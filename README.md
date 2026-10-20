# Arithmetic determination of relations among lattice theta series

Human author and responsible maintainer: **Jue Ding**.

This repository prepares an independent Palomar verification of the full
arithmetic theta formalization accompanying `paper/Paper.pdf`. The
GitHub repository is `WeThinkIn/arithmetic-theta-lean4-palomar`.

**Status: migration in progress. The accepted-050 scoped submission passed official
mechanical verification and has a private semantic review available. Full GoalRoot migration,
full-paper independent verification and registration remain incomplete.** The original Lean 4.33.1 audit and
the new Lean 4.35.0-rc2 verification are distinct evidence.

For a nonempty finite family of positive-definite even integral Gram matrices,
the development constructs finite coefficient bounds that determine all complex
linear relations among the actual lattice theta series. It also constructs
rational relation bases, pivot image bases and unique rational coordinates,
and proves the arithmetic geometric constructions and exact algorithms used to
obtain these conclusions. Rank zero, dependent families, full infinite series,
and the original arithmetic examples remain in scope.

The complete target retains all thirteen source requirements and all 103 frozen
integration endpoints. `docs/SourceObligations.json` preserves their original
types and source accounts. `docs/Coverage.md` tracks their migration separately
from independent Challenge coverage.

Joint partial audit 316 has checked 99/103 original exact endpoint types and standard
axiom closures. The accepted-017 early-certificate subpackage separately passed
local Comparator with con-ron, NanoDa and Lean default kernel using source-bound
exports and a normal sandbox. Its official full mechanical
preflight also passed for commit `12f83ea` and `comparator-early.json`, including
source provenance and all three kernels. This result covers accepted-017 only. See `docs/MigrationStatus.md` and `docs/PalomarPreflight.md`.

## Verification interface

`Challenge.lean` currently states only the pilot finite-determination theorem.
Its definitions use actual integer shell cardinalities and the full formal
power series. It imports Mathlib, not the proof implementation.
Its deliberate `sorry` denotes the statement to be proved, as required by the
Challenge/Solution comparison; it is not accepted as a proof in the Solution.

`Solution.lean` supplies the intended bridge to the original kernel theorem.
Until it compiles and Comparator succeeds, it is an unverified adapter.
`comparator.json` currently selects only that pilot theorem. Successful comparison
of this configuration would not verify all the paper's claims or its complete
geometric proof route. Full-scope configurations and coverage evidence remain
required before claiming complete Palomar verification.

## Mathematical proof route

Integral Gram orthogonalization and actual rational preimage cosets produce
complete unary theta factorizations. Algebraic Tate geometry, Kato units with
proved divisor and norm identities, the discriminant, four-torsion square roots,
and the finite character supply compact geometric sections and exact completed
expansions. Simultaneous roots and common lines give degree and jet bounds.
The coefficient maps then identify the full-series kernel; exact rational
elimination yields the relation basis, pivot series and unique coordinates.
The arithmetic route also retains the sharper bound and the cyclotomic modular
section family. Exact enumeration and stopping certificates are proved correct
with their original hypotheses. A finite sample or a failed rank test alone is
not a certificate of a full-series relation.

The review should check the actual schemes, maps, divisors, line bundles,
structural scalar actions, completed expansions and existence providers in this
route, including all quantifiers, normalization choices and degenerate cases.
The formal statement is the arithmetic modularity claim in the paper; no
additional analytic transformation law or prescribed multiplier is asserted.

## Reproduction

The toolchain is pinned in `lean-toolchain`, and all dependency revisions are
pinned in `lake-manifest.json`.

```sh
lake exe cache get
lake build +GoalRoot
# Independent scoped interfaces:
lake build MainAndComponentsChallenge MainAndComponentsSolution
lake comparator --config comparator-main-and-components.json
lake build FormalCoverChallenge FormalCoverSolution
lake comparator --config comparator-formal-cover.json
```

The four scoped root modules compiled successfully in build 276. The standalone
formal-cover package passed local con-ron, NanoDa and Lean default checking in
537.30 seconds and subsequently passed official preflight and submission verification.
The combined main-and-components and stronger complete-main official checks are pending.
The full GoalRoot source port still has unresolved compatibility issues. Oversized modules have been split;
all required split modules must pass the migrated build before acceptance.
The verification record will identify the exact submitted Git commit and the
configuration checked. Official mechanical preflight is separate from Palomar's
automated semantic/editorial review and from optional permanent registration.

## Provenance and licensing

The proof source includes 1,199 original delivery modules and a dependency
closure of 2,713 modules copied from the local `fermats-last-theorem` library.
Third-party copyright notices and the library's Apache-2.0 license are retained
under `docs/ThirdParty`. The original file hashes and the migration history are
recorded in the separate local verification workspace.

AI-assisted development is disclosed in `formalization.yaml`; AI systems are not listed as human authors.

## License and attribution

Original Lean code is licensed under Apache-2.0 by authorization of the project owner. Human author and responsible maintainer: Jue Ding. Third-party source headers and licenses are retained; see `docs/ThirdParty/fermats-last-theorem-LICENSE.txt`. Mathlib and other dependencies retain their respective licenses.

## Public preflight status

The owner authorized public visibility, official mechanical preflight and subsequent
submission on 2026-10-20. The repository is now public. The manually dispatched
workflow in `.github/workflows/palomar-preflight.yml` calls the official pinned
PalomarSubmission workflow with `mode: full` and `palomar-standard-v1`. The workflow offers the pilot, early certificate, main-and-components, formal-cover
and complete-main configurations; each result applies only to its selected configuration. Formal submission must follow a passing full mechanical report.

The latest joint migrated audit checks **99 of 103** original exact endpoint types and their standard axiom closures. The full GoalRoot build remains pending.

The prepared `comparator-main-and-components.json` compares 43 targets: an explicit conservative full-series kernel bound, 39 complete prior endpoints and supporting results. Its Mathlib-only Challenge is 953 lines / 61,095 bytes. The main interface does not include the extra `FormalIdentity` field of original accepted-037; that original exact type separately passed audit 316. See `challenges/main-and-components/Scope.json`.

`comparator-formal-cover.json` separately compares accepted-050. Both configurations have scope-specific formalization metadata. Formal-cover passed its official full report and completed intake; main-and-components remains in preflight. Geometry interfaces, including the independent scheme discriminant specification, remain unfinished. No full-paper Palomar verification or registration is claimed.

## Stronger complete main interface

`comparator-main-complete.json` selects the separately compiled 969-line Challenge
in `CompleteMainAndComponentsChallenge.lean`. It covers 40 complete prior endpoints
with 43 targets, including the same-U FormalIdentity output of accepted-037.
The stronger Challenge/Solution root pair and the two compatibility repairs passed
actual Lake integration314. This stronger configuration requires its own official
report; the older main-and-components report cannot validate the added output.

The accepted-050 formal-cover entry completed ordinary intake as `86n83vqdajt2`.
Its Palomar verification run39466419289 succeeded and it is at review-ready, with its semantic review held privately. No permanent registration or full-paper pass is claimed.

Current complete-main preflight:
[39469688913](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39469688913),
source commit `35c8d4a1ed4ad19ac879a31a912ab5fcd707f558`.
Formal-cover submission verification:
[39466419289](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39466419289).
The latter is a mechanical pass for accepted-050 only; its semantic review is available privately.
