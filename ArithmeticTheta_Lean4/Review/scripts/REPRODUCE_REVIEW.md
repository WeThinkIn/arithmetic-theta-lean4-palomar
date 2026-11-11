# Reproduce the additive review layer

Run these commands from `ArithmeticTheta_Lean4/`. The runner uses Python 3.8 or
later on a Unix system, the pinned Lean 4.33.1 toolchain, and the original fixed
external dependencies. It does not download dependencies or alter the original
reproduction script, source files, theorem inventory or probes.

For a new environment, first follow the original `REPRODUCE.md` to install the
specified toolchain and obtain `dependencies/`. Then use a **nonexistent**
original build directory:

```bash
python3 Review/scripts/reproduce_review.py \
  --lean /path/to/lean-4.33.1/bin/lean \
  --original-build-dir build-review-original \
  --rebuild-original \
  --jobs 4
```

`--rebuild-original` explicitly invokes the unchanged original
`scripts/reproduce.py`. That invocation compiles all 1,199 original modules and
checks their 103 frozen exact types and transitive axiom dependencies. The new
runner immediately records all original source and object hashes, the compiler
identity, the original script and input manifest hashes, its command, and the
successful original report. It then compiles and checks only the additional
review modules. The original 103 checks are not redundantly repeated immediately
after this fresh successful run.

For an existing verified original build, omit `--rebuild-original`:

```bash
python3 Review/scripts/reproduce_review.py \
  --lean /path/to/lean-4.33.1/bin/lean \
  --original-build-dir build-review-original \
  --jobs 4
```

Existing original objects must match either the committed
`verification/StatementReadabilityBuildReport.json`, including every source and
object hash, or `OriginalBuildBindings.json` produced by a preceding explicit
rebuild with this runner. `--original-bindings PATH` selects one of those records
explicitly. The original directory must have the usual `lib/lean/` layout.
A successful historical report without source/object bindings is insufficient
to establish that an arbitrary set of existing objects came from today's
sources. If no valid binding is available, the runner stops and prints an exact
command for an explicit fresh build. It never starts that expensive build by
itself.

When reusing original objects, the runner invokes the original script with
`--verify-only`. This verifies the full original input checksum manifest and
reruns all 103 exact-type and axiom probes. No original proof module is
recompiled. The review modules are compiled in dependency order, with independent
modules running concurrently up to `--jobs`. `ReviewRoot` must import the original
`GoalRoot` and reach every module under `Review/Lean/`.

To recheck an unchanged review build without recompiling it:

```bash
python3 Review/scripts/reproduce_review.py \
  --lean /path/to/lean-4.33.1/bin/lean \
  --original-build-dir build-review-original \
  --verify-only \
  --jobs 4
```

This mode requires every review source, object and input pin to match the
previous successful build. It reruns both the 103 original checks and all new
checks specified by `Review/metadata/obligations.json`. Each new check strictly
elaborates the frozen expected type, synthesizes implicit metavariables, rejects
any remaining metavariable, compares that type with the actual declaration and
inspects its complete axiom closure. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed.

The default review output is the ignored `Review/.build/` directory. Use
`--build-dir PATH` to select another output directory; relative paths are resolved
under `Review/`. Original and review output directories must be separate. The
runner refuses unexpected review objects that could shadow an original import,
source changes during a run, import cycles and overlapping source/output paths.
A lock prevents two invocations from using the same review output directory.

The output contains:

- `lib/lean/`: the newly compiled review objects only;
- `ReviewBuildBindings.json`: input, source, object and import bindings;
- `ReviewVerificationReport.json`: the current result;
- `attempts/<timestamp>/`: the preserved logs, generated exact-type probes and
  report for that attempt.

These records establish the checked local build history under the normal trust
in the checked-out source, installed compiler and local execution. They are not
cryptographic attestations of a remote machine and do not establish the
mathematical correspondence with the paper by themselves. A user-written JSON
file is not proof that a compiler ran: this runner accepts only the committed
object record or its specific generated format, checks the command and pinned
producer/compiler/source/report hashes, validates every current object, and
reruns the theorem checks. If the provenance of a local cache is not trusted,
use `--rebuild-original` to establish a fresh local record. A different platform
or build is allowed to produce different object bytes; the explicit fresh-build
route records its own bytes instead of requiring the author's object hashes.

The runner's small regression suite checks source/object substitution, duplicate
or missing binding records, comment-aware import parsing and cycle rejection.
Its optional real-compiler test builds a tiny separate fixture and verifies that
a wrong expected type and an unauthorized axiom are rejected:

```bash
REVIEW_TEST_LEAN=/path/to/lean-4.33.1/bin/lean \
  python3 Review/scripts/test_reproduce_review.py -v
```

That test does not import or rebuild the original 1,199-module corpus.
