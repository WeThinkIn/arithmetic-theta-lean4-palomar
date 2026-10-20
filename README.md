# Arithmetic determination of relations among lattice theta series

Human author and responsible maintainer: **Jue Ding**.

This public repository prepares independent Palomar verification of the arithmetic theta formalization accompanying `paper/Paper.pdf`.

**The complete GoalRoot migration build and all103 original exact endpoint type/axiom checks have passed. Full-paper independent Palomar verification and permanent registration remain incomplete.** The original Lean4.33.1 delivery and this Lean4.35.0-rc2 port are distinct artifacts.

For a nonempty finite family of positive-definite even integral Gram matrices, the development constructs finite coefficient bounds that determine all complex linear relations among the actual lattice theta series. It also constructs rational relation bases, pivot image bases and unique rational coordinates, and proves the arithmetic geometric constructions and exact algorithms used to obtain these conclusions. Rank zero, dependent families, full infinite series and the original arithmetic examples remain in scope.

## Migration validation

The original13 requirements and all103 frozen integration endpoints remain in scope. `docs/SourceObligations.json` preserves their original types and source accounts. `docs/Coverage.md` distinguishes their migration from independent Challenge coverage.

Actual `lake build +GoalRoot` passed in build342, including JointSourceIntegrationR0267 and FullSourceIntegrationR0268. Joint audit343 checked all103 original exact endpoint types and their transitive axiom closures in one environment, with only `propext`, `Classical.choice` and `Quot.sound`, no changed inputs and no axiom issues. This is complete endpoint migration evidence, not independent semantic approval of every paper claim. Source bindings, receipts and audit code are under `docs/audit/`.

Read-only baseline344 confirmed all1207 original delivery files remain unchanged. Compatibility adaptations are confined to the separate Palomar workspace and this repository.

## Independent verification interface

The primary prepared configuration is `comparator-main-complete.json`, selecting `CompleteMainAndComponentsChallenge.lean` and `CompleteMainAndComponentsSolution.lean`.

Its Mathlib-only Challenge has969 lines/62283bytes and43 targets covering40 complete original endpoints plus supporting results. The main theorem includes the original accepted-037 `FormalIdentity` for the same witness U, the exact conservative bound for the same B, all larger cutoffs, actual shell finiteness and rank zero. See `challenges/main-and-components-complete/Scope.json`.

The other63 original endpoints remain outside that independent configuration. In particular, full independent geometric interfaces, including scheme-discriminant existence/naturality, remain unfinished. The formal-cover configuration separately selects accepted-050. Source compilation and exact-type migration do not replace these independent statement comparisons.

Challenge `sorry` declarations specify the targets required by Comparator; they are not accepted as Solution proofs. The legacy default `comparator.json` selects only an earlier finite-determination pilot. Use the explicit configuration paths below to reproduce the intended scope.

## Official Palomar status

| Scope | Fixed source | Official status |
| --- | --- | --- |
| accepted-017 early certificate | `12f83ea` | Full mechanical preflight39455278417 passed. |
| accepted-050 formal-cover constancy | `2bd02cf` | Full preflight39461300608 and submission verification39466419289 passed. Submission86n83vqdajt2 has a private semantic review available; not registered. |
| Main and components, older interface | `2bd02cf` | Full preflight39461299032 running;39 complete endpoints plus supporting/main conclusions, omitting the original extra FormalIdentity field. |
| Stronger complete main and components | `35c8d4a` | Full preflight39469688913 running;40 complete endpoints including all accepted-037 outputs. No ordinary intake yet for this configuration. |

The workflow uses the official pinned PalomarSubmission pipeline, `mode: full` and `palomar-standard-v1`. Each report applies only to its exact commit, configuration and metadata path. Later repository changes do not alter running checks. No full-paper Palomar pass is claimed. Private review content and credentials are not published here.

- [Complete-main preflight39469688913](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39469688913)
- [Older main preflight39461299032](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39461299032)
- [Formal-cover submission verification39466419289](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/39466419289)

See `docs/PalomarPreflight.md` for historical reports and exact source bindings.

## Mathematical proof route

Integral Gram orthogonalization and actual rational preimage cosets produce complete unary theta factorizations. Algebraic Tate geometry, Kato units with proved divisor and norm identities, the discriminant, four-torsion square roots and the finite character supply compact geometric sections and exact completed expansions. Simultaneous roots and common lines give degree and jet bounds. The coefficient maps then identify the full-series kernel; exact rational elimination yields the relation basis, pivot series and unique coordinates.

The arithmetic route retains the sharper bound and the cyclotomic modular section family. Exact enumeration and stopping certificates are proved with their original hypotheses. A finite sample or a failed rank test alone is not a certificate of a full-series relation.

Independent review should check the actual schemes, maps, divisors, line bundles, structural scalar actions, completed expansions and existence providers, including quantifiers, normalization and degenerate cases. The formal statement is the paper's arithmetic modularity claim; no additional analytic transformation law or prescribed multiplier is asserted.

## Reproduction

The toolchain and dependency revisions are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
lake build +GoalRoot
lake build CompleteMainAndComponentsChallenge CompleteMainAndComponentsSolution
lake comparator --config comparator-main-complete.json
# Separate scoped supporting lemma:
lake build FormalCoverChallenge FormalCoverSolution
lake comparator --config comparator-formal-cover.json
```

The stronger Challenge/Solution root pair passed actual build314. Formal-cover passed local con-ron, NanoDa and Lean default checking and later its official verification. The larger local main check has accepted con-ron and NanoDa but its bounded default-kernel continuation is still running; no complete local Comparator pass is claimed for that attempt. Official full workflow results remain authoritative for intake eligibility.

## Provenance and licensing

The proof source includes1199 original delivery modules and a dependency closure of2713 modules copied from the local fermats-last-theorem library. Original file hashes and migration evidence are recorded separately. Third-party copyright notices, licenses and attribution are retained under `docs/ThirdParty` and in source headers.

Original Lean code is licensed under **Apache-2.0** by the owner's authorization. Mathlib and other dependencies retain their respective licenses. AI-assisted development is disclosed in the scope-specific `formalization.yaml` metadata; AI systems are not listed as human authors.
