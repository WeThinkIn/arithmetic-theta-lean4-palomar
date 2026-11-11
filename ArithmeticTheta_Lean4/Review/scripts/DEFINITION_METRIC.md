# Recursive statement definitions

`definition_closure.py` reads the **elaborated Lean environment** through
`definition_closure.lean`. Its inputs are compiled objects for the unchanged
original proof, compiled review interfaces, and the pinned external dependencies.
It does not infer dependencies from import lists or text searches.

For each requested theorem the traversal starts at its type and follows:

1. Every referenced custom definition's type and non-proof body, including
   abbreviations, private definitions, and opaque non-proof definitions.
2. Every custom structure or inductive type's constructor types. This includes
   proof-field predicates and dependent fields; wrapping data in a record does
   not hide those fields.
3. References reached through projections, generated declarations, and other
   bookkeeping declarations. Projection functions, constructors and recursors
   are traversed without adding a second count for a field or constructor of
   an already-counted structure.

The displayed count includes named, non-proof custom definitions and custom
structures/inductive types. Compiler-internal names, projection functions,
constructors, recursors, and proof-valued declarations are not counted as
additional definitions. The JSON lists all visited custom declarations, their
classification, direct dependencies, and the counted names, so the convention
can be inspected rather than inferred from one total.

The six **public generated matcher helpers** named `*.match_1` in the current
main-statement closures are included as named non-proof definitions. They are
not `Name.isInternal` declarations, projection functions or recursors. The
definition index labels them as Lean-generated and links to their generating
source definitions; they are not six additional handwritten mathematical
concepts. This distinction is part of the fixed counting convention, and the
headline totals are not adjusted by an additional counting convention.

Theorem proof bodies and proof subterms are excluded. Hypotheses, predicate
definitions, structure proof-field **types**, and the explicit predicates passed
to `Classical.choose` are retained. Binders are opened with Lean local variables
before checking proof status. External Lean/Mathlib/library constants are
recorded as a boundary; their bodies are not recursively counted as definitions
introduced by this project.

This measures the custom definitions needed to interpret a statement under this
explicit convention. It does **not** count the whole proof dependency closure,
estimate minutes of human review, establish correspondence with the paper, or
certify that two statements have identical mathematical strength. Those require
the mathematical mapping, bridge theorems, and the independent build/type/axiom
checks. A lower number for a weaker statement alone would not satisfy the task.

From `ArithmeticTheta_Lean4/`, after compiling the review root:

```sh
python3 Review/scripts/definition_closure.py \
  --lean /path/to/lean-4.33.1/bin/lean \
  --objects /path/to/review-objects \
  --objects /path/to/original-proof-objects \
  --import GoalRoot --import ReviewRoot \
  --target ArithmeticThetaFullSourceR0268.conservative_image_consumer \
  --target ArithmeticThetaSharpKernelR0195.sharp_matrix_kernel \
  --target ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity \
  --target ArithmeticThetaReview.Geometry.conservative_image_review \
  --target ArithmeticThetaReview.Geometry.cyclotomic_modularity_review \
  --output /path/to/fresh-definition-report.json
```

`ReviewRoot` jointly imports the original root and the complete review layer.
With no `--target` options, the three original principal endpoints above are
measured. With no `--import`, `GoalRoot` is used.
Search paths are ordered: the first matching object wins. The report records
source/object hashes for each target theorem's module and the visited custom
definition modules, the exact Lean binary and
version, script hashes, and the dependency-manifest hash. It rejects changes to
a measured source/object or the metric implementation during the run. The
separate build audit establishes the correspondence of those objects with those
sources. The script refuses to overwrite an existing report.

Wujie's dynamic CPU lease can be retained by supplying
`--affinity-python /path/to/conda/python` and
`--affinity-wrapper /path/to/tools/codex_goal_affinity_exec.py`.

Run the small regression fixture with:

```sh
python3 Review/scripts/test_definition_closure.py \
  --lean /path/to/lean-4.33.1/bin/lean
```

The fixture verifies that an alias still includes its target, a record includes
the predicate in its proof field, a chosen value retains its choice predicate,
an opaque value retains its body dependencies, and a definition used only in a
theorem proof is excluded from statement dependencies. It also checks directly
that the auxiliary definition really occurs in that stored theorem proof, and
that a theorem-only target module is bound even when its statement contains no
custom definitions. Fixtures live under `scripts/tests/`, outside the paper's
Lean module inventory.
