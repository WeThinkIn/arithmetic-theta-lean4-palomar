"""Regression tests for stale-object rejection and actual Lean audit failures.

Run with REVIEW_TEST_LEAN=/path/to/lean for the small compiler integration test.
The integration test never imports or recompiles the original proof corpus.
"""

import importlib.util
import os
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("reproduce_review.py")
SPEC = importlib.util.spec_from_file_location("review_reproduction", SCRIPT)
RUNNER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RUNNER)


class ProvenanceTests(unittest.TestCase):
    def test_old_receipt_rejects_changed_source_or_object(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, target = root / "Example.lean", root / "Example.olean"
            source.write_text("def example := 1\n")
            target.write_bytes(b"compiler output")
            sources = {"Example": source}
            records = RUNNER.snapshot(sources, root)
            RUNNER.validate_original_records(records, sources, root)
            source.write_text("def example := 2\n")
            with self.assertRaisesRegex(RuntimeError, "binding mismatch"):
                RUNNER.validate_original_records(records, sources, root)
            source.write_text("def example := 1\n")
            target.write_bytes(b"substituted output")
            with self.assertRaisesRegex(RuntimeError, "binding mismatch"):
                RUNNER.validate_original_records(records, sources, root)

    def test_duplicate_and_missing_records_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "Example.lean"
            source.write_text("def example := 1\n")
            (root / "Example.olean").write_bytes(b"output")
            sources = {"Example": source}
            records = RUNNER.snapshot(sources, root)
            for bad in ([], records + records):
                with self.assertRaisesRegex(RuntimeError, "inventory"):
                    RUNNER.validate_original_records(bad, sources, root)

    def test_comment_imports_do_not_create_dependencies(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Example.lean"
            source.write_text('''/- import Bogus
/- nested comment -/
-/
import First /- comment -/ Second
-- import Third
def doc := "import Fourth"
''')
            self.assertEqual(RUNNER.imports(source), {"First", "Second"})

    def test_cycle_fails_without_starting_a_compiler(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = {"A": root / "A.lean", "B": root / "B.lean"}
            def unexpected(*_):
                self.fail("No member of a cyclic import graph is ready")
            with self.assertRaisesRegex(RuntimeError, "Cyclic review import graph"):
                RUNNER.compile_modules(sources, {"A": {"B"}, "B": {"A"}}, root, unexpected, 2)

    def test_success_exit_without_axiom_evidence_is_rejected(self):
        self.assertFalse(RUNNER.axiom_result("", "Example", 0)[0])
        self.assertFalse(RUNNER.axiom_result(
            "'Another' does not depend on any axioms", "Example", 0)[0])

    @unittest.skipUnless(os.environ.get("REVIEW_TEST_LEAN"), "Set REVIEW_TEST_LEAN for real compiler tests")
    def test_real_build_exact_type_and_unauthorized_axiom(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            old, source, objects, logs = (root / name for name in ("original", "Lean", "objects", "logs"))
            for path in (old, source, objects, logs):
                path.mkdir()
            lean, prefix, _, env = RUNNER.resolve_lean(os.environ["REVIEW_TEST_LEAN"], root)
            (old / "GoalRoot.lean").write_text("def originalSentinel : Nat := 42\n")
            result = RUNNER.command_run(
                [lean, "-o", str(old / "GoalRoot.olean"), str(old / "GoalRoot.lean")],
                old, env, logs / "original.log", 30)
            self.assertEqual(result["returncode"], 0, (logs / "original.log").read_text())
            (source / "ReviewBase.lean").write_text(
                "import GoalRoot\ntheorem Fixture.add (n : Nat) : n + 0 = n := Nat.add_zero n\n")
            (source / "ReviewRoot.lean").write_text(
                "import GoalRoot\nimport ReviewBase\ntheorem Fixture.main (n : Nat) : n + 0 = n := Fixture.add n\n")
            (source / "ReviewUnsafe.lean").write_text("axiom Fixture.unproved : False\n")
            sources = RUNNER.module_inventory(source)
            env.update(LEAN_PATH=os.pathsep.join(map(str, [objects, old, prefix / "lib/lean"])))
            def run(module, input_path, target):
                return RUNNER.command_run([lean, "-o", str(target), str(input_path)],
                                          source, env, logs / (module + ".log"), 30)
            results = RUNNER.compile_modules(sources, {m: RUNNER.imports(p) for m, p in sources.items()},
                                             objects, run, 2)
            self.assertEqual(len(results), 3)
            for name, declaration, file, expected, accepted in (
                ("correct", "Fixture.main", "ReviewRoot", "∀ n : Nat, n + 0 = n", True),
                ("wrong-type", "Fixture.main", "ReviewRoot", "∀ n : Nat, n + 1 = n", False),
                ("axiom", "Fixture.unproved", "ReviewUnsafe", "False", False),
            ):
                probe = root / (name + ".lean")
                probe.write_text(RUNNER.exact_probe({"declaration": declaration,
                                                    "file": "Lean/" + file + ".lean", "type": expected}))
                result = RUNNER.command_run([lean, str(probe)], source, env, logs / (name + ".log"), 30)
                output = (logs / (name + ".log")).read_text()
                self.assertEqual(RUNNER.axiom_result(output, declaration, result["returncode"])[0], accepted, output)
                if name == "wrong-type":
                    self.assertIn("frozen theorem type mismatch", output)
                if name == "axiom":
                    self.assertIn("Fixture.unproved", RUNNER.axiom_result(output, declaration, result["returncode"])[1])


if __name__ == "__main__":
    unittest.main()
