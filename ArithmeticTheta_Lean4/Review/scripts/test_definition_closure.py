#!/usr/bin/env python3
"""Exercise the definition metric's resistance to purely cosmetic hiding."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=Path)
    parser.add_argument("--affinity-python", type=Path)
    parser.add_argument("--affinity-wrapper", type=Path)
    args = parser.parse_args()
    if bool(args.affinity_python) != bool(args.affinity_wrapper):
        parser.error("Supply both affinity options or neither")
    scripts = Path(__file__).resolve().parent
    root = scripts / "tests"
    compiler = args.lean.resolve()
    env = dict(os.environ)
    env["PATH"] = str(compiler.parent) + os.pathsep + env.get("PATH", "")
    prefix = ([str(args.affinity_python), str(args.affinity_wrapper)]
              if args.affinity_wrapper else [])
    with tempfile.TemporaryDirectory(prefix="theta-metric-test-") as scratch:
        temp = Path(scratch)
        for module in ("MetricFixture", "MetricEmpty"):
            subprocess.run(prefix + [str(compiler), "-o", str(temp / (module + ".olean")),
                                     str(root / (module + ".lean"))],
                           cwd=root, env=env, check=True, timeout=60)
        command = [sys.executable, str(scripts / "definition_closure.py"),
                   "--lean", str(compiler), "--objects", str(temp),
                   "--source-root", str(root), "--review-root", str(temp / "empty"),
                   "--import", "MetricFixture", "--import", "MetricEmpty",
                   "--output", str(temp / "report.json")]
        targets = {
            "baseStatement": ["base"],
            "aliasStatement": ["alias", "base"],
            "wrappedStatement": ["Holder", "witnessProperty"],
            "chosenStatement": ["chosen", "witnessProperty"],
            "opaqueStatement": ["chosen", "hidden", "witnessProperty"],
            "proofOnlyStatement": ["base"],
            "emptyStatement": [],
        }
        for target in targets:
            command.extend(["--target", "MetricFixture." + target])
        if args.affinity_wrapper:
            command.extend(["--affinity-python", str(args.affinity_python),
                            "--affinity-wrapper", str(args.affinity_wrapper)])
        subprocess.run(command, env=env, check=True, timeout=120)
        report = json.loads((temp / "report.json").read_text())
        reports = report["reports"]
        actual = {item["target"]: item["custom_definitions"] for item in reports}
        expected = {"MetricFixture." + target: ["MetricFixture." + name for name in names]
                    for target, names in targets.items()}
        if actual != expected:
            raise AssertionError({"actual": actual, "expected": expected})
        if "MetricEmpty" not in {r["module"] for r in report["bindings"]}:
            raise AssertionError("Target theorem module missing from source/object bindings")
        print("PASS: aliases expand; structure proof-field predicates are retained; "
              "choice predicates and opaque bodies are retained; "
              "proof-only dependencies are excluded; theorem-only target modules are bound.")


if __name__ == "__main__":
    main()
