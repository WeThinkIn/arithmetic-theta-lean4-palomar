# Main172 semantic crosscheck, attempt 286

Reviewed commit: `2bd02cf8a38d686dc7a56012b1ca0291443816c9`.

This is an independent agent's read-only source/interface review. It is **not** an official Palomar semantic pass, a fresh compilation, a kernel-comparator result, or an exhaustive review of the entire geometric dependency closure. Only this report and receipt were written outside the project. No build was started and no project source was changed by this reviewer. Commit-bound bytes, not a concurrently evolving working tree, identify this review; the receipt records working-copy matches separately.

## Finding

The independently stated `ArithmeticThetaPalomarMain172.explicitFiniteDetermination` preserves the substantive conservative finite-coefficient kernel conclusion: actual finite integer-shell theta series; every finite nonempty valid Gram family; all complex coefficient vectors; one exact conservative cutoff and every larger prefix; the actual distinct unary-pair count; and the rank-zero constant-series case. No newly assumed target conclusion or additional geometric existence premise was found in this endpoint.

It is **not an exact full-type mirror of accepted-037**: the independent endpoint omits the original output `FormalIdentity A U` for the same returned indexing witness. The Solution obtains and discards `_hformal` at line 1279. This is a scope narrowing of the independent challenge, not an error in the kernel statement or evidence that the original declaration lacks its factorization proof. The committed `docs/Coverage.md:47` already discloses this omission. Passing this challenge must not be reported as independent verification of every output of accepted-037 or every conclusion of the paper's main theorem.

## Definition and quantifier checks

1. **Challenge and Solution agree.** Their Main172 definition prefixes (Challenge line 839; Solution line 1000) are textually identical. The complete theorem types (Challenge line 932; Solution line 1249) are also textually identical. This was checked against the committed bytes with a script.

2. **Hypotheses and normalization.** `paper/OriginalTask.tex:47` specifies symmetric positive-definite integral matrices with even diagonal and `Q(x)=x^t A x/2`. Challenge `validGram` at line 841 has precisely symmetry, even diagonal and positive definiteness of the rational half quadratic form. Both theta and coefficient matrix use that same form on all integer vectors, with no bounded-box substitution. The endpoint quantifies arbitrary `n : Nat`, `h : Nat` with `0<h`, and all families of those Gram matrices. No independence or full-rank hypothesis on the theta coefficient matrix is imposed. Positive definiteness of each input Gram matrix is retained; deficient rank of the theta relation matrix must not be confused with a singular input Gram matrix.

3. **Actual Nat.card and finite shells.** The theorem first concludes `Finite` for every actual integer shell of every input matrix and every natural index. Therefore it does not exploit `Nat.card` returning zero on infinite types. Solution line 1113 uses `ArithmeticThetaLattice.exact_shell_finite` from actual positive definiteness. The theta map is the sum of coordinate projections times the full shell-count power series. Its scalars are genuinely complex, with no restriction of coefficient vectors to rationals.

4. **Actual coefficient matrix and inclusive endpoints.** The matrix at Challenge line 924 counts the same shell over Q and has `Fin (B+1)` rows, including 0 and B. The substantive bridge at Solution line 1117 uses `computed_coefficient_matrix` to match the original executable matrix; it does not falsely claim this bridge is reflexivity. The independent theta map is definitionally equal to the original actual theta map (Solution line 1096).

5. **Same B and every larger B'.** One existential B binds its exact value, kernel equality for all `B'>=B`, coefficient-vanishing equivalence for those same prefixes, and rank zero. Solution lines 1268–1293 obtain a single B from the original main theorem and reuse it. The proof does not choose a new cutoff for each vector or each prefix. Its coefficient equivalence is derived from the transported kernel equality, not assumed. B'=B gives the exact source finite-prefix assertion.

6. **Actual pair count.** `Indexed` at Challenge line 905 requires bijective representatives of the actual rational preimage quotient, the actual residue congruence, injectivity of `U.pair`, agreement of every occurring unary factor with its indexed pair, and occurrence of every index. These jointly prevent duplicate or unused padding pairs. `U.count` counts distinct occurring `(m,nu)` pairs, not merely distinct m values. The centered convention represents residue classes modulo m. Fieldwise conversion `fromOriginal` (Solution line 1137) preserves the same representatives, residues, count, pairs and indices; the Indexed equivalences and both roundtrips are provided.

7. **Exact rational cutoff and integrality.** The definitions retain N as the lcm of all computed diagonal norms, L=24*N^2, K=(1+12*N)^2-1, and B=n*K^U.count*card(SL2(Z/LZ))/48. `levelIndex` is the displayed rational product rather than a definition by group cardinality. The endpoint explicitly concludes `(B : Q)=n*K^s*I(L)/48`. Solution `cutoff_rational` at line 1178 uses the proved finite group count `card=2*L*card(signed primitive pairs)` and L=24*N^2 to establish divisibility by 48 before casting natural division. CommonN positivity follows from valid inputs. Thus it neither silently floors a nonintegral rational bound nor substitutes the separate sharper bound involving `/48L` (OriginalTask line 75).

8. **Rank zero.** When n=0 the endpoint requires B=0, and gives the actual equality `thetaMap A c = C(sum_i c_i)` for every complex vector. All-prefix kernel and coefficient equivalences remain in force. The original proof at `Proof/ConservativeMatrixKernelR0189.lean:92` constructs B=0 using its proved rank-zero theta formula, without a positive-rank geometric construction.

## Dependency direction and assumptions

The Solution imports `ConservativeMatrixKernelR0189` at line 43 and invokes its proved `conservative_matrix_kernel` at line 1269. That original declaration (`Proof/ConservativeMatrixKernelR0189.lean:88`) has only the arithmetic input hypotheses. Its proof produces the geometric family using `arithmetic_geometric_family_existence`, then consumes `geometric_family_conservative_cutoff`.

The existence theorem (`Proof/ArithmeticGeometricFamilyExistenceR0189.lean:23`) constructs the indexing, formal identity, level data, compactification, Hodge extension and geometric family from valid arithmetic inputs. The cutoff theorem (`Proof/GeometricFamilyConservativeCutoffR0189.lean:36`) has a geometric-family premise, but the main theorem supplies it from the existence result rather than exposing it as a new assumption. Similarly the conditional helper `coefficients_iff_of_kernel` is used only after the actual kernel equality has been obtained. This review found no newly assumed conclusion at this integration boundary.

This source inspection checks the interface direction. It does not replace compilation, transitive axiom audit or independent kernel comparison, and it does not certify all geometric definitions or providers by itself.

## Hodge weight K/2

OriginalTask lines 410–414 explicitly normalize by `m^(-K/2)` and give a section of `omega^(K/2)` with full expansion `U_(m,nu)^K`. `Proof/CompactUnaryDefinitionsR0183.lean:22` defines `weight N=exponent N/2`; its OpenPower, DiskCoefficient and RealizesUnary use that actual Hodge power. `Proof/OpenHodgeDescentDefinitionsR0180.lean:172` expresses the actual Hodge pullback's local-frame formula with `(m^-1)^(K/2)`. The designated-expansion theorem at `Proof/OpenUnaryDesignatedExpansionR0182.lean:3321` uses the same weight and unary K-th power. These inspected types agree with K/2, not omega^K. Main172 has no sheaf or modularity output, so passing Main172 alone is not independent verification of this geometric assertion.

## Exact omitted output and coverage consequence

`Proof/LatticeGlobalSectionsDefinitionsR0188.lean:58` defines FormalIdentity as a full identity for every complex c: the literal substitution q=t^(24*N^2) in the theta combination equals the sum of unary-factor products using the same U. This is substantive additional evidence, not another name for Indexed or for the kernel conclusion. The source theorem and its proof retain it, but the independent Challenge does not require it. Separate general orthogonal-factorization results do not automatically make this endpoint an exact same-U, same-substitution mirror of accepted-037.

If exact independent coverage of every accepted-037 output is desired, add a separately reviewed target with the actual unary definition and substitution and transport the already-produced hformal. Do not change frozen inputs during an active comparator run. The present omission is already accurately disclosed and does not invalidate the conservative kernel result.

A successful independent comparison of this exact endpoint can support the conservative full complex kernel and finite-coefficient result for all finite nonempty valid Gram families, including rank zero. It cannot alone support independent verification of the original extra FormalIdentity output, rational pivot/image algorithms, the sharper bound, common-level arithmetic modularity, or the entire paper. Those require their corresponding exact obligations and comparisons. The original accepted-037 source statement also explicitly leaves pivot/image and modularity in separate scope.

Recommendation: retain this endpoint and its precise kernel-scope description for the current build. Keep the FormalIdentity omission explicit and treat exact full-output independent coverage as an additional task. No unexpected kernel-statement weakening or newly assumed target conclusion was found in this bounded review.
