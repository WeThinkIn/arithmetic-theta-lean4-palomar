# Arithmetic determination of relations among lattice theta series

Human author and responsible maintainer: **Jue Ding**.

This public repository prepares independent Palomar verification of the arithmetic theta formalization accompanying `paper/Paper.pdf`.

**The complete GoalRoot migration build and all103 original exact endpoint type/axiom checks have passed. Full-paper independent Palomar verification and permanent registration remain incomplete.** The original Lean4.33.1 delivery and this Lean4.35.0-rc2 port are distinct artifacts.

Current integrated independent interface coverage is **79/103**, with 24 pending; these are local interface checks, not 79 official passes. [Component Hodge power degree](challenges/component-hodge-degree/README.md) adds full original031, retaining the actual canonical boundary Hodge extension and exact residue-weighted degree formula for every original nonzero section and tensor exponent, including zero. [Split-field component cusp bound](challenges/split-cusp/README.md) adds full original072 without an algebraic-closure hypothesis. Both exact original recoveries, target/semantic/standard-axiom audits and actual four-root build498 passed. [Latest coverage](docs/audit/hodge-degree-cusp-integration-498/coverage.json).

For a nonempty finite family of positive-definite even integral Gram matrices, the development constructs finite coefficient bounds that determine all complex linear relations among the actual lattice theta series. It also constructs rational relation bases, pivot image bases and unique rational coordinates, and proves the arithmetic geometric constructions and exact algorithms used to obtain these conclusions. Rank zero, dependent families, full infinite series and the original arithmetic examples remain in scope.

## Migration validation

The original13 requirements and all103 frozen integration endpoints remain in scope. `docs/SourceObligations.json` preserves their original types and source accounts. `docs/Coverage.md` distinguishes their migration from independent Challenge coverage.

Actual `lake build +GoalRoot` passed in build342, including JointSourceIntegrationR0267 and FullSourceIntegrationR0268. Joint audit343 checked all103 original exact endpoint types and their transitive axiom closures in one environment, with only `propext`, `Classical.choice` and `Quot.sound`, no changed inputs and no axiom issues. This is complete endpoint migration evidence, not independent semantic approval of every paper claim. Source bindings, receipts and audit code are under `docs/audit/`.

Read-only baseline344 confirmed all1207 original delivery files remain unchanged. Compatibility adaptations are confined to the separate Palomar workspace and this repository.

## Independent verification interface

The primary prepared configuration is `comparator-main-complete.json`, selecting `CompleteMainAndComponentsChallenge.lean` and `CompleteMainAndComponentsSolution.lean`.

Its Mathlib-only Challenge has969 lines/62283bytes and43 targets covering40 complete original endpoints plus supporting results. The main theorem includes the original accepted-037 `FormalIdentity` for the same witness U, the exact conservative bound for the same B, all larger cutoffs, actual shell finiteness and rank zero. See `challenges/main-and-components-complete/Scope.json`.

The other63 original endpoints remain outside that independent configuration. In particular, full independent geometric interfaces, remain unfinished; complete scheme-discriminant existence/naturality interfaces have now been prepared separately below. The formal-cover configuration separately selects accepted-050. Source compilation and exact-type migration do not replace these independent statement comparisons.

The sharp/adaptive/image configuration `comparator-sharp-adaptive-image.json` adds seven disjoint endpoints: accepted-046/049/064/065/066/067/088. Its Mathlib-only Challenge has485 lines/31089bytes. Local standalone checks and the actual named root-pair build passed; all225 non-internal Solution declarations have standard axiom closures. It preserves the exact distinct-norm cutoff, full kernels for larger prefixes, actual first-stop algorithm, checked integral changes, full null/image/unique-coordinate results and singleton-zero behavior. Scope and evidence are under `challenges/sharp-adaptive-image/` and `docs/audit/sharp-adaptive-image-351/`. This new configuration still requires its own official full preflight before ordinary intake.

Together, complete-main and sharp/adaptive/image specify47 distinct original endpoints; the separate formal-cover package adds accepted-050 for48. These are independent interface coverage counts, not48 official semantic approvals. The roots package adds two further endpoints and the coordinates package adds four, for54 distinct endpoints; the scheme-discriminant package adds080/081, giving56 distinct endpoints; scheme Kato adds083/086 for58/103 prepared interfaces (45 remaining). Original scope remains13 requirements/103 endpoints.

Challenge `sorry` declarations specify the targets required by Comparator; they are not accepted as Solution proofs. The legacy default `comparator.json` selects only an earlier finite-determination pilot. Use the explicit configuration paths below to reproduce the intended scope.

## Official Palomar status

| Scope | Fixed source | Official status |
| --- | --- | --- |
| accepted-017 early certificate | `12f83ea` | Full mechanical preflight39455278417 passed. |
| accepted-050 formal-cover constancy | `2bd02cf` | Full preflight39461300608 and submission verification39466419289 passed. Submission86n83vqdajt2 has a private semantic review available; not registered. |
| Main and components, older interface | `2bd02cf` | Full preflight39461299032 ended with Solution-build memory exhaustion (exit137/oom-kill);39 complete endpoints plus supporting/main conclusions, omitting the original extra FormalIdentity field. |
| Sharp/adaptive/image seven-endpoint package | `088eff2` | Full preflight39479248485 failed at Solution build with exit137/oom-kill; official report453 records resource exhaustion, with no kernel verdict. |
| Sharp and actual ambient roots | `b706aea` | Full preflight39482676946 failed in Solution build with exit137/oom-kill despite per-compiler-j1; official report493 records six OOM kills, with no kernel verdict. |
| Sharp and algebraic coordinates | current sources | Local build/audit384 passed; official dispatch pending. |
| Complete scheme discriminant | current sources | Local exact-type/axiom checks385 and root build392 passed; official preflight pending. |
| Scheme Kato naturality/characterization | current sources | Local exact-type/axiom checks394 and root build400 passed; official preflight pending. |
| Stronger complete main and components | `35c8d4a` | Full preflight39469688913 passed Solution build/export, then exhausted wall-clock budget at comparator; official report500 gives no final kernel verdict.40 complete endpoints including all accepted-037 outputs; no ordinary intake for this configuration. |

The workflow uses the official pinned PalomarSubmission pipeline, `mode: full` and `palomar-standard-v1`. Each report applies only to its exact commit, configuration and metadata path. Later repository changes do not alter running checks. No full-paper Palomar pass is claimed. Private review content and credentials are not published here.

- [Sharp/adaptive/image preflight39479248485](https://github.com/WeThinkIn/arithmetic-theta-lean4-palomar/actions/runs/39479248485)
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
# Sharp cutoff, certified adaptive solver and exact image:
lake build SharpAdaptiveImageChallenge SharpAdaptiveImageSolution
lake comparator --config comparator-sharp-adaptive-image.json
# Separate scoped supporting lemma:
lake build FormalCoverChallenge FormalCoverSolution
lake comparator --config comparator-formal-cover.json
```

The stronger Challenge/Solution root pair passed actual build314. Formal-cover passed local con-ron, NanoDa and Lean default checking and later its official verification. The larger local main check has accepted con-ron and NanoDa but its7200-second bounded default-kernel continuation ended in timeout without acceptance or rejection; no complete local Comparator pass is claimed for that attempt. Official full workflow results remain authoritative for intake eligibility.

## Provenance and licensing

The proof source includes1199 original delivery modules and a dependency closure of2713 modules copied from the local fermats-last-theorem library. Original file hashes and migration evidence are recorded separately. Third-party copyright notices, licenses and attribution are retained under `docs/ThirdParty` and in source headers.

Original Lean code is licensed under **Apache-2.0** by the owner's authorization. Mathlib and other dependencies retain their respective licenses. AI-assisted development is disclosed in the scope-specific `formalization.yaml` metadata; AI systems are not listed as human authors.

The additional `comparator-sharp-and-roots.json` pairs the full accepted-049 principal sharp theta conclusion with complete accepted-056/057 actual ambient/smooth-point root constructions. Its990-line/66941-byte Mathlib-only Challenge retains all original fields and the actual canonical tensor comparison; all local checks and the actual named root build361 passed. It adds two distinct endpoint IDs, bringing prepared independent interface coverage to50/103 (the remaining53 still need interfaces). This is not50 official passes. Official preflight39482676946 failed during Solution cold build with resource exhaustion; see docs/audit/official-sharp-and-roots-result-493/Review.md. It has not been ordinary-submitted or registered.

Official resource report362: older run39461299032 failed during `solution-build`, with15824445440bytes (~14.74GiB) recorded peak memory, `oom_kill:9` and `deadline_fired:false`. Challenge provenance was high/Mathlib-only. This is a failed mechanical attempt due to infrastructure resources, not a proof rejection. Those historical runs are now terminal: complete-main timed out at comparator (report500), and sharp/adaptive/image failed with build OOM (report453). Do not retry unchanged resource conditions. See `docs/audit/official-older-main-362/`.


Resource experiment364 sets package-level `weakLeanArgs = ["-j1"]`, confirmed in actual compiler arguments by isolated Lake probe363. This limits internal Lean threads per compiler, not simultaneous Lake compiler processes; unchanged theorem types, proof bodies, Comparator and kernel checks are retained. The official sharp-and-roots cold build later failed with six OOM kills despite this setting (report493); no claim of sufficient memory reduction is established. Larger Namespace runner availability was not established. See `docs/audit/resource-diagnosis-363/Analysis.md`.

The additional `comparator-sharp-and-coordinates.json` specifies complete accepted019/020/021/022 coordinates, poles, cubic and global normalized differential together with the accepted049 principal sharp theta conclusion. Its670-line/40226-byte Mathlib-only Challenge, Solution,38-declaration standard-axiom audit and actual named root build384 passed. It adds four distinct endpoint IDs, bringing prepared independent interface coverage to54/103, with49 remaining. This is not54 official passes. Official dispatch is deferred pending a measured resource remedy after experiment39482676946 failed with OOM (report493). See challenges/sharp-and-coordinates/ and docs/audit/sharp-and-coordinates-384/coverage.json.

The complete scheme-discriminant configuration `comparator-full-scheme-discriminant.json` adds original accepted080/081 existence and arbitrary-base-change naturality, with eight explicit canonical-construction support targets. Its976-line/54781-byte Mathlib-only Challenge and883-line/50878-byte Solution passed local compilation;115 Solution declarations have only standard axioms,23 independent definitions/imports were audited, and both original full endpoint types were recovered exactly. Actual named root build392 passed. SchemeSpecification retains all affine tests and arbitrary nonreduced rings/nonflat maps, with exact factor5/exponent24 normalization and actual conormal tensor comparisons. Prepared interface coverage is now56/103 (47 remaining), not56 official passes. Official preflight for this configuration is pending. See challenges/full-scheme-discriminant/ and docs/audit/full-scheme-integration-392/.

The `comparator-scheme-kato.json` configuration adds complete original accepted083/086, scheme Kato unit naturality and intrinsic Cartier-divisor/norm characterization. Its827-line/43286-byte independent Challenge and280-line/16121-byte Solution passed local checks;37 Solution declarations have standard axioms,17 independent definitions/imports were audited and both original types recovered. Five targets include three actual existence supports. Norm families are existentially constructed on all opens with exact determinant normalization and restriction compatibility. Actual root build400 passed. Prepared independent interface coverage is58/103, with45 remaining; official full preflight for this package is pending. See challenges/scheme-kato/ and docs/audit/scheme-kato-integration-400/coverage.json.

The period-one and scheme-initial packages add complete original accepted-082 and accepted-085. Both independent specifications retain all original quantified objects and conclusions, have exact original-type recovery and standard-axiom Solution audits, and passed their actual repository root builds (audit412). Their 14 targets each include 13 explicit support obligations. Prepared independent interface coverage is now 60/103, with 43 remaining; this counts locally checked interfaces, not official passes. Official preflight and semantic review for these new configurations remain pending. See docs/audit/new-geometric-interfaces-412/coverage.json.

The two Weierstrass polynomial proofs have been restored to their original ring implementations after stock-kernel benchmarks found substantial performance regressions in the smaller grind proof terms. Both versions passed the pinned Lean kernel: the symmetric YZ theorem took 6.57 seconds / 0.492 GiB with ring versus 79.98 seconds / 12.285 GiB with grind; the third-addition YZ theorem took 5.27 seconds / 0.258 GiB versus 54.37 seconds / 8.575 GiB. Memory figures are sampled process high-water measurements, and concurrent work makes precise timing ratios indicative. Actual GoalRoot and all 13 current Comparator Solution roots passed build430; exact theorem types/universes, every Solution declaration axiom closure, all 103 original endpoints (audit431), and the unchanged original1207-file baseline passed. Independent interface coverage remains61/103. Historical optimized export416 and its ongoing comparator are preserved for their exact bytes; they do not describe the restored source or establish official acceptance. See docs/audit/proof-kernel-regression-repair-430/Review.md.

The complete scheme Kato–Tate unit interface adds original accepted-084: one unique actual unit with full normalization, Cartier divisor, every positive coprime norm and full period-one Tate expansion through the same actual pullback. Its863-line independent Challenge and227-line Solution passed local compilation, all-declaration axiom/import audits and exact original-type recovery; the actual repository root build424 passed. The7 targets include the inherited394 obligations and explicit gamma-limit existence. Prepared independent coverage is61/103,42remaining; this is local interface coverage, not official passes. See docs/audit/scheme-tate-unit-integration-424/coverage.json. Official preflight and semantic review remain pending.

The complete scheme Miller-phase interface adds original accepted-051 at arbitrary universe u: a unique global phase with its unit and square identities, primitive order4 conditional on nontrivial global sections, and actual moved-divisor pairing on every affine test and characteristic-zero field fiber. Its660-line independent Challenge and23-line Solution passed compilation; all341 Challenge and4 Solution declarations were axiom-audited,208 non-proof declarations have original definitionally equal types and available bodies, and the complete original051 type is recovered. The three targets include explicit local-data and arbitrary-ring fiber-basis existence. Actual root build435 passed. Prepared independent coverage is62/103,41remaining; these are local interfaces, not official passes. Original052 remains pending. See docs/audit/scheme-miller-phase-integration-435/coverage.json.

The complete scheme alpha-character interface adds original accepted-052 at arbitrary universe u, retaining the same global phase, actual cotangent and all even-stabilizer matrices. The canonical differential and conormal maps are specified by unique local derivative formulas and proved equal to the originals. Full affine/global RealizesAlpha equivalences and the exact original052 reverse bridge compile. Its732-line independent Challenge and257-line Solution passed all-declaration audits (349 Challenge,85 Solution),199 Challenge/Solution semantic checks and actual root build439. All seven support/main targets are explicit, including global alpha existence. Prepared independent coverage is63/103,40remaining; these are local interfaces, not official passes. See docs/audit/scheme-alpha-character-integration-439/coverage.json.

The complete relative-alpha interface adds full original accepted-038 and accepted-039 at arbitrary universe u and every positive level divisible by4. It retains actual root data, the unique realizing alpha frame and all original base-change/marking conditions. Canonical pointed comparison is uniquely specified on local derivatives and proved equal to the original, including exact alpha pullback. Original reverse bridges and rfl type checks pass, with all-declaration axiom and Challenge/Solution definition audits and actual root build444. Prepared independent coverage is65/103,38remaining; these are local interfaces, not official passes. Inherited052 is not counted twice. See docs/audit/relative-alpha-integration-444/coverage.json.

The complete Tate-alpha interface adds full original accepted-040 for every positive level divisible by4: actual full marking on the actual Tate cubic, original normalized boundary differential, full power-series-unit expansion of exact order0 or L/4 and the exact signed thetaAt squared identity for every primitive root and canonical marking. Literal full series and all nonidentity point coordinates are retained. Boundary predicate/generator rfl bridges, full original theorem recovery, all-declaration axioms,240 semantic-definition comparisons and actual root build447 pass. Prepared independent coverage is66/103,37remaining; these are local interfaces, not official passes. Inherited052 is not counted twice. See docs/audit/tate-alpha-integration-447/coverage.json.

The complete phase-free multiplier interface adds full original accepted-095 and accepted-097 at arbitrary universe u. It retains actual all-scheme marked Cartesian tests, local invertibility and frame generation, all test-map naturality, inverse character for every actual Miller phase and even-stabilizer change, and the exact reversal law. Existence and uniqueness of the multiplier and the full base-change isomorphism are proved with literal canonical pullback compositions. Full original statements/rfl recovery, all-declaration axiom audits,275 semantic-definition comparisons and actual root build452 pass. Prepared independent coverage is68/103,35remaining; these are local interfaces, not official passes. Inherited052 is not counted twice. See docs/audit/phase-free-multiplier-integration-452/coverage.json.

Official preflight39479248485 for historical088eff2 completed with solution-build OOM (exit137), not a kernel verdict. Genuine report and resource analysis: docs/audit/official-sharp-adaptive-image-result-453/Review.md. Complete-main and sharp-and-roots preflights remain active at snapshot448; no whole-paper official acceptance or ordinary submission claimed.

The complete multiplier-fourth interface adds full original accepted-100 at arbitrary universe u: actual fourth tensor power trivialization uniquely normalized to1 on every prescribed multiplier frame. Canonical pullback comparison is uniquely fixed on all local sections and opens and proved equal to the original; unit pullback and full normalization predicate are recovered. Invertibility is extracted from original IsMultiplier, not an extra assumption. Full original statement/rfl recovery, all-declaration axioms,300 semantic-definition comparisons and actual root build457 pass. Prepared independent coverage is69/103,34remaining; these are local interfaces, not official passes. Inherited052095097 not recounted. See docs/audit/multiplier-fourth-integration-457/coverage.json.

The complete phase-free alpha descent interface adds full original accepted-096 at arbitrary universe u: unique section of the actual cotangent tensor multiplier line and frame generation on every subopen. Every marked test retains both nonvacuity existentials and full tensor equality for every compatible cotangent map and realizing alpha. Canonical binary tensor comparison is uniquely fixed on all local pure tensors and proved equal to original. Full Descends/original statement recovery, all-declaration axioms, semantic-definition checks and actual root build461 pass. Prepared independent coverage is70/103,33remaining; these are local interfaces, not official passes. Inherited052095097 not recounted. See docs/audit/phase-free-alpha-descent-integration-461/coverage.json.

Historical optimized export416 full local Comparator reached its3600-second total budget: con-ron and NanoDa accepted; default Lean did not finish, no accept/reject verdict. Genuine receipt: docs/audit/full-comparator-timeout-462/comparator-receipt.json. Inputs stayed unchanged, overall passed=false. This historical export predates the430 proof restoration and gives no verdict on current main. Full official acceptance and ordinary intake remain incomplete.
