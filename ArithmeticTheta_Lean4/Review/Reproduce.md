# Reproduce the review interfaces

Use the unchanged original toolchain **Lean 4.33.1**, pinned dependency manifest
and dependency artifacts. Follow the original [REPRODUCE.md](../REPRODUCE.md) to
obtain that environment. The new [portable runner instructions](scripts/REPRODUCE_REVIEW.md)
cover both a fresh environment and reuse of a verified original build.

From `ArithmeticTheta_Lean4/`, for an existing original build with `lib/lean/`:

```sh
python3 Review/scripts/reproduce_review.py \
  --lean /path/to/lean-4.33.1/bin/lean \
  --original-build-dir /path/to/verified-original-build \
  --jobs 8 --lean-threads 2
```

For a fresh original build, use a nonexistent original output directory and add
`--rebuild-original`. That explicitly compiles the original 1,199 modules and
checks their 103 endpoints before building the additive layer. Existing object
reuse requires complete source/object bindings; a historical success flag alone
is insufficient. The runner compiles all 13 new modules including ReviewRoot,
which imports the entire original proof, then checks the 18 frozen types and
their transitive axioms. It never edits original sources or probes.

The local authority audit uses Wujie's unchanged `audit_goal_delivery.py`, with a
frozen contract copied in [metadata/combined-contract.json](metadata/combined-contract.json).
Its authority checkout and original support objects are recorded in the report.
On the originating machine its command is:

```sh
LEAN4_LOCAL_LIBRARY_ROOT=/home/Palomar/workspace/arithmetic-theta-review-interface-20261111/audit-libraries \
  /home/miniconda3/envs/lean4/bin/python \
  /home/wujie-ai-lean4-proof-agent-program/tools/codex_goal_affinity_exec.py \
  /home/miniconda3/envs/lean4/bin/python \
  /home/wujie-ai-lean4-proof-agent-program/tools/audit_goal_delivery.py \
  --project-root /home/wujie-ai-lean4-proof-agent-program \
  --contract /home/wujie-ai-lean4-proof-agent-program/workspace/goal-tasks/arithmetic-theta-review-combined-20261111/contract.json \
  --timeout 600 --summary
```

The Wujie checkout is not required by the portable runner. Both paths elaborate
the frozen expected types without residual metavariables, compare the actual
types and allow only `propext`, `Classical.choice` and `Quot.sound`.

Reproduce the statement-definition metric using the command and conventions in
[DEFINITION_METRIC.md](scripts/DEFINITION_METRIC.md). This metric is separate
from source/proof verification. [SHA256SUMS](SHA256SUMS) binds this additive
delivery; the original bundle's checksum manifest is retained unchanged.
