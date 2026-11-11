#!/usr/bin/env python3
"""Measure elaborated statement definitions using a compiled Lean environment.

The Lean companion performs the semantic traversal. This driver discovers the
source inventory, binds source and object hashes, and invokes the pinned Lean
compiler. It neither builds proofs nor changes any source or existing report.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


DEFAULT_TARGETS = [
    "ArithmeticThetaFullSourceR0268.conservative_image_consumer",
    "ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel",
    "ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity",
]


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def inventory(root: Path) -> dict[str, Path]:
    return {
        ".".join(p.relative_to(root).with_suffix("").parts): p
        for p in sorted(root.rglob("*.lean"))
    }


def stamp(path: Path):
    value = path.stat()
    return (value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns)


def main() -> None:
    bundle = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--objects", required=True, action="append", type=Path,
                        help="Proof object search paths, highest priority first")
    parser.add_argument("--dependencies", type=Path,
                        default=bundle / "dependencies/lib/lean")
    parser.add_argument("--source-root", type=Path, default=bundle / "Lean")
    parser.add_argument("--review-root", type=Path, default=bundle / "Review/Lean")
    parser.add_argument("--import", dest="imports", action="append",
                        help="Joint roots to import; default: GoalRoot")
    parser.add_argument("--target", action="append", help="Fully qualified theorem name")
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--affinity-python", type=Path)
    parser.add_argument("--affinity-wrapper", type=Path)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    if bool(args.affinity_python) != bool(args.affinity_wrapper):
        parser.error("Supply both affinity options or neither")
    output = args.output.resolve()
    if output.exists():
        parser.error("Output already exists; choose a fresh report path")
    source = inventory(args.source_root.resolve())
    review = inventory(args.review_root.resolve())
    duplicate = source.keys() & review.keys()
    if duplicate:
        parser.error(f"Duplicate original/review module names: {sorted(duplicate)}")
    objects = [p.resolve() for p in args.objects]
    dependencies = args.dependencies.resolve()
    all_sources = {**source, **review}
    source_snapshot = {module: digest(path) for module, path in all_sources.items()}
    object_snapshot = {}
    for module in all_sources:
        relative = Path(*module.split(".")).with_suffix(".olean")
        path = next((root / relative for root in objects if (root / relative).is_file()), None)
        if path is not None:
            object_snapshot[module] = (path, stamp(path))
    config = {
        "search_path": [str(p) for p in objects] + [str(dependencies)],
        "imports": args.imports or ["GoalRoot"],
        "local_modules": sorted(all_sources),
        "review_modules": sorted(review),
        "targets": args.target or DEFAULT_TARGETS,
    }
    script = Path(__file__).resolve().with_suffix(".lean")
    tool_snapshot = {"lean": digest(script), "python": digest(Path(__file__))}
    prefix = ([str(args.affinity_python), str(args.affinity_wrapper)]
              if args.affinity_wrapper else [])
    with tempfile.TemporaryDirectory(prefix="theta-definition-closure-") as scratch:
        config_path = Path(scratch) / "configuration.json"
        result_path = Path(scratch) / "result.json"
        config_path.write_text(json.dumps(config, indent=2) + "\n")
        command = prefix + [str(args.lean.resolve()), "--run", str(script),
                            str(config_path), str(result_path)]
        env = dict(os.environ)
        env["LEAN_PATH"] = os.pathsep.join(config["search_path"])
        env["PATH"] = str(args.lean.resolve().parent) + os.pathsep + env.get("PATH", "")
        subprocess.run(command, env=env, check=True, timeout=args.timeout)
        report = json.loads(result_path.read_text())
    modules = sorted({node["module"] for item in report["reports"] for node in item["nodes"]}
                     | {item["target_module"] for item in report["reports"]})
    bindings = []
    for module in modules:
        if module not in object_snapshot:
            raise FileNotFoundError(f"No object for measured module {module}")
        object_file, before = object_snapshot[module]
        src = all_sources[module]
        if stamp(object_file) != before or digest(src) != source_snapshot[module]:
            raise RuntimeError(f"Measured source or object changed during the run: {module}")
        object_digest = digest(object_file)
        if stamp(object_file) != before:
            raise RuntimeError(f"Measured object changed while hashing: {module}")
        bindings.append({"module": module, "source": str(src),
                         "source_sha256": source_snapshot[module],
                         "object": str(object_file), "object_sha256": object_digest})
    if tool_snapshot != {"lean": digest(script), "python": digest(Path(__file__))}:
        raise RuntimeError("Metric implementation changed during the run")
    report.update({
        "configuration": config,
        "lean_version": subprocess.check_output([str(args.lean.resolve()), "--version"], text=True).strip(),
        "lean_binary_sha256": digest(args.lean.resolve()),
        "source_inventory": {"original_modules": len(source), "review_modules": len(review)},
        "tool_sha256": tool_snapshot,
        "bindings": bindings,
        "source_object_binding_note": (
            "Hashes record the objects inspected and the corresponding current sources. "
            "Their compilation correspondence is established by the separate build/audit; "
            "this metric is not a replacement for that audit."
        ),
        "counting_convention": {
            "include": ["elaborated target types", "project definition types and non-proof bodies",
                        "all project structure/inductive constructor field types",
                        "opaque non-proof definition bodies", "private named definitions"],
            "traverse_but_do_not_count": ["projections", "constructors", "recursors",
                                          "compiler-internal names", "proof declaration types"],
            "exclude": ["theorem proof bodies", "proof subterms", "external library bodies"],
            "interpretation": (
                "Counts semantic declaration dependencies under one fixed, explicit convention; "
                "it does not estimate human difficulty, count proof dependencies, or establish "
                "equivalence with the manuscript. Aliases and wrapper records are expanded."
            ),
        },
    })
    dependency_manifest = bundle / "metadata/dependencies.json"
    if dependency_manifest.is_file():
        report["dependency_manifest"] = {
            "path": str(dependency_manifest), "sha256": digest(dependency_manifest)
        }
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(f"Report: {output}")


if __name__ == "__main__":
    main()
