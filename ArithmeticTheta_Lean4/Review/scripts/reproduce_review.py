#!/usr/bin/env python3
"""Build and check the additive review layer using a verified original build.

The original 1,199-module build is never started implicitly. Use
--rebuild-original for a fresh environment, or supply an existing original build
whose objects match the committed record or a local record produced here.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import time

REVIEW = Path(__file__).resolve().parents[1]
ORIGINAL = REVIEW.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def is_relative_to(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def write_json(path: Path, value: object) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    temporary.replace(path)


def module_path(module: str, suffix: str) -> Path:
    if not NAME.fullmatch(module):
        raise RuntimeError("Unsupported Lean module name: " + module)
    return Path(*module.split(".")).with_suffix(suffix)


def checksum_entries(root: Path) -> dict[str, str]:
    entries = {}
    for line in (root / "SHA256SUMS").read_text().splitlines():
        expected, rel = line.split("  ", 1)
        if not re.fullmatch(r"[0-9a-f]{64}", expected):
            raise RuntimeError("Malformed checksum: " + rel)
        if Path(rel).is_absolute() or ".." in Path(rel).parts or rel in entries:
            raise RuntimeError("Invalid or duplicate checksum path: " + rel)
        entries[rel] = expected
    return entries


def check_files(root: Path, expected: dict[str, str]) -> None:
    for rel, digest in expected.items():
        path = root / rel
        if not path.is_file() or sha256(path) != digest:
            raise RuntimeError("Missing or changed input: " + str(path))


def resolve_lean(value: str | None, root: Path) -> tuple[str, Path, dict, dict]:
    found = value or shutil.which("lean")
    if not found:
        raise RuntimeError("Install Lean 4.33.1 or supply --lean /path/to/bin/lean")
    # Do not resolve an elan shim: its executable name selects the tool.
    executable = str(Path(found).absolute())
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("LEAN", "LAKE"))
           and k not in {"LD_LIBRARY_PATH", "LD_PRELOAD", "DYLD_LIBRARY_PATH"}}
    version = subprocess.check_output([executable, "--version"], cwd=root,
                                      env=env, text=True).strip()
    if not re.search(r"\bversion 4\.33\.1(?:,|\s|\))", version):
        raise RuntimeError("Expected Lean 4.33.1; got " + version)
    prefix = Path(subprocess.check_output([executable, "--print-prefix"],
                                        cwd=root, env=env, text=True).strip())
    if not (prefix / "lib/lean/Init.olean").is_file():
        raise RuntimeError("Missing Lean standard library under " + str(prefix))
    identity = {"lean_version": version,
                "compiler_sha256": sha256(prefix / "bin/lean"),
                "standard_init_sha256": sha256(prefix / "lib/lean/Init.olean")}
    return executable, prefix, identity, env


def module_inventory(root: Path) -> dict[str, Path]:
    result = {}
    for source in sorted(root.rglob("*.lean")):
        if not is_relative_to(source.resolve(), root.resolve()):
            raise RuntimeError("Source symlink escapes its root: " + str(source))
        module = ".".join(source.relative_to(root).with_suffix("").parts)
        module_path(module, ".lean")
        result[module] = source
    return result


def imports(source: Path) -> set[str]:
    """Remove nested Lean comments before reading ordinary import commands."""
    text = source.read_text()
    clean, index, depth, string = [], 0, 0, False
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                clean.append("\n" if char == "\n" else " ")
                index += 1
        elif string:
            if char == "\\":
                clean.extend("  ")
                index += 2
            else:
                clean.append("\n" if char == "\n" else " ")
                string = char != '"'
                index += 1
        elif pair == "/-":
            depth = 1
            clean.append(" ")
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif char == '"':
            string = True
            clean.append(" ")
            index += 1
        else:
            clean.append(char)
            index += 1
    if depth or string:
        raise RuntimeError("Unterminated comment or string: " + str(source))
    result = set()
    for line in "".join(clean).splitlines():
        match = re.match(r"\s*(?:(?:public|private)\s+)?import\s+(.*?)\s*$", line)
        if match:
            if not match.group(1).strip():
                raise RuntimeError("Put each import command on one line: " + str(source))
            for module in match.group(1).split():
                module_path(module, ".lean")
                result.add(module)
        elif re.match(r"\s*(?:(?:public|private)\s+)?import\b", line):
            raise RuntimeError("Unsupported import command: " + str(source))
    return result


def validate_original_records(records: list[dict], sources: dict[str, Path],
                              objects: Path) -> dict[str, dict[str, str]]:
    by_module = {item["module"]: item for item in records}
    if len(by_module) != len(records) or set(by_module) != set(sources):
        raise RuntimeError("Original source/object binding inventory does not match")
    actual = {}
    for module, source in sources.items():
        record = by_module[module]
        target = objects / module_path(module, ".olean")
        if record.get("exit_code") != 0 or not target.is_file():
            raise RuntimeError("Missing or unsuccessful original module: " + module)
        pair = {"source_sha256": sha256(source), "object_sha256": sha256(target)}
        if any(pair[key] != record.get(key) for key in pair):
            raise RuntimeError("Original source/object binding mismatch: " + module)
        actual[module] = pair
    return actual


def snapshot(sources: dict[str, Path], objects: Path) -> list[dict]:
    return [{"module": module, "source_sha256": sha256(source),
             "object_sha256": sha256(objects / module_path(module, ".olean")),
             "exit_code": 0} for module, source in sorted(sources.items())]


def command_run(command: list[str], cwd: Path, env: dict, log: Path,
                timeout: int | None) -> dict:
    start = time.monotonic()
    with log.open("w") as output:
        try:
            completed = subprocess.run(command, cwd=cwd, env=env, stdout=output,
                                       stderr=subprocess.STDOUT, timeout=timeout)
            code = completed.returncode
        except subprocess.TimeoutExpired:
            output.write("\nCompiler invocation exceeded its time budget.\n")
            code = 124
    return {"command": command, "returncode": code,
            "seconds": round(time.monotonic() - start, 3),
            "log": str(log), "log_sha256": sha256(log)}


def exact_probe(item: dict) -> str:
    declaration = item["declaration"]
    module = ".".join(Path(item["file"]).relative_to("Lean").with_suffix("").parts)
    if not NAME.fullmatch(declaration):
        raise RuntimeError("Invalid declaration name: " + declaration)
    module_path(module, ".lean")
    universes = item.get("universes", [])
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", u) for u in universes):
        raise RuntimeError("Invalid universe binder")
    universe_line = "universe " + " ".join(universes) if universes else ""
    return f'''import Lean
import {module}
{universe_line}
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
set_option hygiene false in
run_cmd Lean.Elab.Command.liftTermElabM do
  let actual ← Lean.Meta.inferType (← Lean.Meta.mkConstWithFreshMVarLevels ``{declaration})
  let expected ← Lean.Elab.Term.elabType (← `(term| {item["type"]}))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← Lean.instantiateMVars expected
  if expected.hasMVar then
    throwError "frozen theorem type contains unresolved metavariables"
  unless ← Lean.Meta.isDefEq actual expected do
    throwError "frozen theorem type mismatch"
#print axioms {declaration}
'''


def axiom_result(output: str, declaration: str, returncode: int) -> tuple[bool, list[str]]:
    pattern = re.escape("'" + declaration + "'")
    match = re.search(pattern + r"\s+depends on axioms:\s*\[([^]]*)\]", output)
    none = re.search(pattern + r"\s+does not depend on any axioms", output)
    used = {x.strip() for x in match.group(1).split(",") if x.strip()} if match else set()
    return returncode == 0 and bool(match or none) and used <= ALLOWED_AXIOMS, sorted(used)


def compile_modules(sources: dict[str, Path], graph: dict[str, set[str]], objects: Path,
                    run, jobs: int) -> list[dict]:
    pending, done, running, records = set(sources), set(), {}, []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            ready = sorted(m for m in pending if graph[m] & sources.keys() <= done)
            for module in ready[:jobs - len(running)]:
                pending.remove(module)
                target = objects / module_path(module, ".olean")
                target.parent.mkdir(parents=True, exist_ok=True)
                running[pool.submit(run, module, sources[module], target)] = module
            if not running:
                raise RuntimeError("Cyclic review import graph: " + ", ".join(sorted(pending)))
            finished, _ = concurrent.futures.wait(
                running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                module = running.pop(future)
                result = future.result()
                records.append(dict(module=module, **result))
                if result["returncode"]:
                    raise RuntimeError("Compilation failed; see " + result["log"])
                done.add(module)
                print(f"Compiled review module {len(done)}/{len(sources)}: {module}", flush=True)
    return records


def original_report_ok(path: Path, manifest: str, version: str, fresh: bool) -> dict:
    report = json.loads(path.read_text())
    modules = report.get("fresh_modules" if fresh else "verified_existing_modules")
    if (report.get("passed") is not True or modules != 1199
            or report.get("exact_type_checks") != 103
            or report.get("input_manifest_sha256") != manifest
            or report.get("lean_version") != version
            or len(report.get("obligations", [])) != 103
            or not all(x.get("passed") for x in report["obligations"])):
        raise RuntimeError("Invalid or stale original reproduction report: " + str(path))
    if fresh and (len(report.get("compiles", [])) != 1199
                  or len({x.get("module") for x in report["compiles"]}) != 1199
                  or any(x.get("returncode") != 0 for x in report["compiles"])):
        raise RuntimeError("Original report does not record all 1199 successful compilations")
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--original-build-dir", default="build-fresh",
                        help="Original build with lib/lean; relative to ArithmeticTheta_Lean4")
    parser.add_argument("--original-bindings", type=Path,
                        help="Committed original build report or a generated OriginalBuildBindings.json")
    parser.add_argument("--build-dir", default=".build",
                        help="Review output; relative to Review (default: .build)")
    parser.add_argument("--lean", help="Lean 4.33.1 executable")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--lean-threads", type=int, default=1)
    parser.add_argument("--timeout", type=int, default=3600,
                        help="Seconds per Lean invocation, including the original runner")
    parser.add_argument("--verify-only", action="store_true",
                        help="Require bound existing review objects; rerun all original and new probes")
    parser.add_argument("--rebuild-original", action="store_true",
                        help="Explicitly build all original modules into a nonexistent directory first")
    args = parser.parse_args(argv)
    if min(args.jobs, args.lean_threads, args.timeout) < 1:
        parser.error("jobs, lean-threads and timeout must be positive")
    if args.verify_only and args.rebuild_original:
        parser.error("--verify-only and --rebuild-original are mutually exclusive")
    original_build = Path(args.original_build_dir)
    original_build = (original_build if original_build.is_absolute()
                      else ORIGINAL / original_build).resolve()
    out = Path(args.build_dir)
    out = (out if out.is_absolute() else REVIEW / out).resolve()
    if out == original_build or is_relative_to(original_build, out) or is_relative_to(out, original_build):
        parser.error("Original and review build directories must be separate")
    for destination in (out, original_build):
        for protected in (ORIGINAL / "Lean", ORIGINAL / "dependencies", REVIEW / "Lean", REVIEW / "scripts"):
            if is_relative_to(protected, destination) or is_relative_to(destination, protected):
                parser.error("Build directory overlaps protected sources: " + str(protected))
    out.mkdir(parents=True, exist_ok=True)
    lock = (out / ".reproduce.lock").open("a+")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise RuntimeError("Another reproduction is using " + str(out)) from None
    started = time.monotonic()
    attempt = out / "attempts" / str(time.time_ns())
    attempt.mkdir(parents=True)
    report = {"schema_version": 1, "passed": False, "original_modules": 1199,
              "allowed_axioms": sorted(ALLOWED_AXIOMS), "verify_only": args.verify_only,
              "provenance_note": "Local compiler and hash records, not an independent semantic review."}
    try:
        if args.verify_only and not (out / "ReviewBuildBindings.json").is_file():
            raise RuntimeError("No bound review build found; first run without --verify-only")
        manifest_path = ORIGINAL / "SHA256SUMS"
        manifest = sha256(manifest_path)
        expected_inputs = checksum_entries(ORIGINAL)
        # Check the pinned executable script before invoking it.
        for rel in ("scripts/reproduce.py", "metadata/dependencies.json", "metadata/original-contract.json"):
            check_files(ORIGINAL, {rel: expected_inputs[rel]})
        lean, prefix, identity, env = resolve_lean(args.lean, ORIGINAL)
        report.update(identity)
        script_hash = sha256(Path(__file__))
        original_script = ORIGINAL / "scripts/reproduce.py"
        pins = {"original_manifest_sha256": manifest,
                "original_runner_sha256": sha256(original_script), **identity}
        old_sources = module_inventory(ORIGINAL / "Lean")
        old_meta = json.loads((ORIGINAL / "metadata/dependencies.json").read_text())
        if set(old_sources) != set(old_meta["local_modules"]) or len(old_sources) != 1199:
            raise RuntimeError("Original source inventory must be exactly the pinned 1199 modules")
        old_objects = original_build / "lib/lean"
        original_command = [sys.executable, str(original_script), "--lean", lean,
                            "--build-dir", str(original_build), "--jobs", str(args.jobs),
                            "--lean-threads", str(args.lean_threads), "--timeout", str(args.timeout)]
        if args.rebuild_original:
            if original_build.exists():
                raise RuntimeError("--rebuild-original requires a nonexistent original build directory")
            before_sources = {m: sha256(p) for m, p in old_sources.items()}
            print("Explicit original rebuild: " + shlex.join(original_command), flush=True)
            result = command_run(original_command, ORIGINAL, env, attempt / "original-build.log", None)
            if result["returncode"]:
                raise RuntimeError("Original rebuild failed; see " + result["log"])
            original_report_ok(original_build / "VerificationReport.json", manifest,
                               identity["lean_version"], True)
            records = snapshot(old_sources, old_objects)
            if any(r["source_sha256"] != before_sources[r["module"]] for r in records):
                raise RuntimeError("Original sources changed during their rebuild")
            binding = {"schema_version": 1, "kind": "review-runner-original-build",
                       "pins": pins, "producer_sha256": script_hash,
                       "original_command": original_command,
                       "verification_report_sha256": sha256(original_build / "VerificationReport.json"),
                       "records": records, "build_log_sha256": result["log_sha256"]}
            write_json(original_build / "OriginalBuildBindings.json", binding)
            binding_path = original_build / "OriginalBuildBindings.json"
        else:
            binding_path = args.original_bindings
            if binding_path is None:
                local = original_build / "OriginalBuildBindings.json"
                binding_path = local if local.is_file() else ORIGINAL / "verification/StatementReadabilityBuildReport.json"
            binding_path = binding_path.resolve()
            try:
                binding = json.loads(binding_path.read_text())
                if binding.get("kind") == "review-runner-original-build":
                    if binding.get("pins") != pins or binding.get("producer_sha256") != script_hash:
                        raise RuntimeError("Local original-build provenance pins have changed")
                    if binding.get("verification_report_sha256") != sha256(original_build / "VerificationReport.json"):
                        raise RuntimeError("Local original compiler report has changed")
                    original_report_ok(original_build / "VerificationReport.json", manifest,
                                       identity["lean_version"], True)
                    recorded_command = binding.get("original_command", [])
                    if len(recorded_command) != 12 or Path(recorded_command[1]).name != "reproduce.py":
                        raise RuntimeError("Local record lacks the original compiler command")
                    if recorded_command[2::2] != ["--lean", "--build-dir", "--jobs", "--lean-threads", "--timeout"]:
                        raise RuntimeError("Local record was not generated by an original source build")
                    if any(not str(recorded_command[i]).isdigit() or int(recorded_command[i]) < 1
                           for i in (7, 9, 11)):
                        raise RuntimeError("Local record contains invalid original compiler arguments")
                else:
                    canonical = ORIGINAL / "verification/StatementReadabilityBuildReport.json"
                    if sha256(binding_path) != sha256(canonical):
                        raise RuntimeError("Only the committed original object record is accepted in this format")
                    if binding.get("status") != "complete" or binding.get("lean_version") != identity["lean_version"]:
                        raise RuntimeError("Original recorded compiler or completion status differs")
                validate_original_records(binding["records"], old_sources, old_objects)
            except (OSError, KeyError, ValueError, RuntimeError) as error:
                next_command = [sys.executable, str(Path(__file__)), "--rebuild-original",
                                "--original-build-dir", str(original_build) + "-fresh",
                                "--build-dir", str(out), "--lean", lean, "--jobs", str(args.jobs)]
                raise RuntimeError(str(error) + "\nBuild a fresh original environment explicitly:\n  "
                                   + shlex.join(next_command)) from error
        original_bindings = validate_original_records(binding["records"], old_sources, old_objects)
        report["original_bindings"] = {"path": str(binding_path), "sha256": sha256(binding_path),
                                       "verified_modules": len(original_bindings)}
        # A fresh original run has just checked all 103 endpoints. For reused
        # objects, rerun the unmodified runner's verify-only path instead.
        if args.rebuild_original:
            old_report = original_build / "VerificationReport.json"
        else:
            print("Rechecking the original 103 exact types and axiom closures", flush=True)
            result = command_run(original_command + ["--verify-only"], ORIGINAL, env,
                                 attempt / "original-verification.log", None)
            if result["returncode"]:
                raise RuntimeError("Original verification failed; see " + result["log"])
            old_report = original_build / "ReverificationReport.json"
            original_report_ok(old_report, manifest, identity["lean_version"], False)
        report["original_verification"] = {**result, "report_sha256": sha256(old_report),
                                           "exact_type_checks": 103}
        sources = module_inventory(REVIEW / "Lean")
        if not sources or "ReviewRoot" not in sources or set(sources) & set(old_sources):
            raise RuntimeError("Expected a separate ReviewRoot and nonoverlapping review modules")
        source_hashes = {m: sha256(p) for m, p in sources.items()}
        graph = {m: imports(p) for m, p in sources.items()}
        reachable, frontier = set(), {"ReviewRoot"}
        while frontier:
            module = frontier.pop()
            if module in reachable:
                continue
            reachable.add(module)
            frontier |= graph[module] & sources.keys() - reachable
        if reachable != set(sources) or "GoalRoot" not in graph["ReviewRoot"]:
            raise RuntimeError("ReviewRoot must import original GoalRoot and reach every review module")
        objects = out / "lib/lean"
        objects.mkdir(parents=True, exist_ok=True)
        extras = {".".join(p.relative_to(objects).with_suffix("").parts)
                  for p in objects.rglob("*.olean")} - set(sources)
        if extras:
            raise RuntimeError("Unexpected objects could shadow original imports: " + ", ".join(sorted(extras)))
        for module in sources:
            if any((root / module_path(module, ".olean")).exists()
                   for root in (old_objects, ORIGINAL / "dependencies/lib/lean", prefix / "lib/lean")):
                raise RuntimeError("Review module shadows an existing module: " + module)
        obligations_path = REVIEW / "metadata/obligations.json"
        data = json.loads(obligations_path.read_text())
        obligations = data if isinstance(data, list) else data["obligations"]
        if not obligations or len({o["id"] for o in obligations}) != len(obligations):
            raise RuntimeError("Expected nonempty uniquely identified review obligations")
        if len({o["declaration"] for o in obligations}) != len(obligations):
            raise RuntimeError("Duplicate review declarations in metadata")
        for item in obligations:
            target_module = ".".join(Path(item["file"]).relative_to("Lean").with_suffix("").parts)
            if target_module not in sources:
                raise RuntimeError("Obligation file is not in the review module inventory")
        current_pins = {**pins, "original_binding_sha256": sha256(binding_path),
                        "obligations_sha256": sha256(obligations_path),
                        "review_runner_sha256": script_hash}
        if any(sha256(source) != source_hashes[module] for module, source in sources.items()):
            raise RuntimeError("Review sources changed while preparing their dependency graph")
        env.update(LEAN_PATH=os.pathsep.join(map(str, [objects, old_objects,
                   ORIGINAL / "dependencies/lib/lean", prefix / "lib/lean"])),
                   LEAN_SYSROOT=str(prefix), LEAN_NUM_THREADS=str(args.lean_threads))
        def run(module, source, target):
            return command_run([lean, "-j" + str(args.lean_threads), "-o", str(target), str(source)],
                               REVIEW / "Lean", env, attempt / (module + ".log"), args.timeout)
        if args.verify_only:
            prior = json.loads((out / "ReviewBuildBindings.json").read_text())
            if prior.get("pins") != current_pins:
                raise RuntimeError("Review build inputs changed; run without --verify-only")
            validate_original_records(prior["records"], sources, objects)
            report["compiles"] = []
        else:
            report["compiles"] = compile_modules(sources, graph, objects, run, args.jobs)
        records = snapshot(sources, objects)
        if any(r["source_sha256"] != source_hashes[r["module"]] for r in records):
            raise RuntimeError("Review sources changed during their build")
        def check_one(pair):
            index, item = pair
            probe = attempt / (f"exact-{index:03d}.lean")
            probe.write_text(exact_probe(item))
            result = command_run([lean, "-j" + str(args.lean_threads), str(probe)],
                                 REVIEW / "Lean", env, probe.with_suffix(".log"), args.timeout)
            passed, axioms = axiom_result(probe.with_suffix(".log").read_text(),
                                         item["declaration"], result["returncode"])
            return {"id": item["id"], "declaration": item["declaration"],
                    "passed": passed, "axioms": axioms, "probe_sha256": sha256(probe), **result}
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
            checks = list(pool.map(check_one, enumerate(obligations)))
        report["obligations"] = checks
        if not all(item["passed"] for item in checks):
            raise RuntimeError("Review exact-type or axiom check failed; see " + str(attempt))
        if sha256(manifest_path) != manifest or sha256(obligations_path) != current_pins["obligations_sha256"]:
            raise RuntimeError("Input manifests changed during verification")
        check_files(ORIGINAL, expected_inputs)
        validate_original_records(binding["records"], old_sources, old_objects)
        validate_original_records(records, sources, objects)
        if sha256(Path(__file__)) != script_hash or sha256(prefix / "bin/lean") != identity["compiler_sha256"]:
            raise RuntimeError("Runner or compiler changed during verification")
        if set(module_inventory(ORIGINAL / "Lean")) != set(old_sources):
            raise RuntimeError("Original source inventory changed during verification")
        if set(module_inventory(REVIEW / "Lean")) != set(sources):
            raise RuntimeError("Review source inventory changed during verification")
        write_json(out / "ReviewBuildBindings.json", {"schema_version": 1, "pins": current_pins,
                                                     "records": records, "imports": {m: sorted(v) for m, v in graph.items()}})
        report.update(passed=True, review_modules=len(sources), exact_type_checks=len(checks),
                      original_exact_type_checks=103, input_pins=current_pins,
                      bindings_sha256=sha256(out / "ReviewBuildBindings.json"))
    except Exception as error:
        report["error"] = str(error)
        print(str(error), file=sys.stderr)
    finally:
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        write_json(attempt / "ReviewVerificationReport.json", report)
        write_json(out / "ReviewVerificationReport.json", report)
        lock.close()
    print(json.dumps({k: v for k, v in report.items()
                      if k in {"passed", "review_modules", "exact_type_checks", "original_exact_type_checks", "error", "elapsed_seconds"}},
                     indent=2, ensure_ascii=False))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
