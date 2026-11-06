# Same-witness full main statement, attempt 295

Challenge.lean is a 173-line / 8,128-byte Mathlib-only specification. It adds the previously omitted FormalIdentity to the independent main arithmetic interface, INSIDE the same positive-rank existential Indexing witness that supplies the cutoff. Solution.lean is 403 lines / 20,903 bytes. Both compiled successfully using the pinned toolchain and existing validated dependencies with isolated outputs (2.52s / 3.77s). The main theorem and all five new defining bridges have only propext, Classical.choice and Quot.sound. Full logs and receipts are retained.

The theorem is ArithmeticThetaPalomarMainFormal295.explicitFiniteDeterminationWithFormalIdentity. The namespace is deliberately separate from the currently frozen public main Challenge/Solution. Those files, the original package265 and all project sources were left unchanged.

## Same witness, not two existential assertions

The conclusion has the following quantifier structure, retaining all formulas literally in the Lean source:

exists B,
  (if n=0 then B=0 else exists U,
      Indexed A U AND FormalIdentity A U AND B=cutoff A U AND exact rational formula using U.count)
  AND (for every B' >= B, full theta kernel = actual prefix matrix kernel)
  AND (for every B' >= B and coefficient vector, full vanishing iff coefficient vanishing through B')
  AND (the complete rank-zero constant-series formula).

Shell finiteness is also proved. There is one B for all these assertions and one positive-rank U for indexing, the formal identity, the cutoff and its rational expression. The proof calls conservative_matrix_kernel ONCE and destructs its same U, hU, hformal, hcut and kernel proof. fromOriginal copies representatives, residue, count, pair and index fieldwise. No new choice of U is made, and no witness from an unrelated orthogonal-factorization theorem is substituted.

This stronger theorem can serve as the joint source of the earlier kernel interface and its FormalIdentity: forget the FormalIdentity conjunct to recover the earlier interface. It does NOT prove that every existential witness obtained by an unrelated use of the older weaker theorem is the same witness, nor that an unspecified previous existential choice can be retroactively identified. Such uniqueness is unnecessary and is not claimed. Replacing the earlier interface by this jointly witnessed conclusion is the correct composition.

## Literal formal series

commonN is the lcm of the deterministic orthogonal naturalNorms of the actual Gram family. expanded is literally PowerSeries.subst (X^(24*N^2)) applied to the full theta linear combination. The right-hand side uses the same U.representatives domain, U.pair and U.index:

sum_i c_i * sum_a product_j unarySeries N (U.pair (U.index i a j)).1 (U.pair (U.index i a j)).2.

unarySeries is the actual integer series cast to C after substitution X^(N^2/m). Its integer coefficients are the existing finite sum over k in [-a,a+1] of the predicate 12*(m*k+nu)^2=a. This reproduces the original clearedUnaryTheta definition exactly, including its totalized values and natural-number division. No alternative shell normalization, formal variable functional, shifted residue convention or extra divisibility hypothesis is introduced.

## Checked bridges

- clearedUnaryTheta_eq: independent finite coefficient sum equals the actual ArithmeticThetaUnaryProduct definition, by rfl.
- unarySeries_eq: the same cast and substitution equals the actual ArithmeticThetaSimultaneousUnaryR0187.unarySeries C N m nu, by rfl.
- expanded_eq: the precise q=t^(24*N^2) substitution agrees with the original expanded, by rfl.
- fromOriginal_formal: independent FormalIdentity of the fieldwise transported ORIGINAL U iff original FormalIdentity A U, by Iff.rfl.
- toOriginal_formal: original FormalIdentity of the fieldwise transported INDEPENDENT U iff independent FormalIdentity A U, by Iff.rfl.

The inherited bridges prove both Indexing roundtrips, Indexed equivalence, count preservation, exact cutoff transport, computed-matrix/shell-count correspondence and the rational cutoff formula. The main proof retains hformal rather than discarding it as package265 did.

## Coverage and limits

This addresses the missing FormalIdentity conjunction of accepted-037 with the SAME witness used by its cutoff/kernel conclusion. It restores all mathematical conjuncts of that original main statement through explicit independent definitions and retains the earlier extra shell-finiteness/coefficientwise consequences. It is not an identity of raw elaborated types: Indexing is independently declared, and the shell coefficient matrix is connected to the executable one by a checked equality using validGram. The original exact accepted-037 type remains separately audited by the root.

All other task obligations remain required: the original full program has 13 requirements / 103 endpoints. This package does not independently specify or verify all geometric constructions, sharper cutoffs, other algorithms, examples, or arbitrary-scheme discriminant endpoints080/081.

This attempt provides SOURCE COMPILATION and AXIOM/DEFINITION BRIDGE checks only. No 2.7GB export, new local three-kernel Comparator, official preflight, official submission or public source update was performed. The current official package265/joint274 run is unaffected. A later official submission of this stronger scope would require newly named modules actually rebuilt and a matching official full preflight for its own published commit/config.

Reproduce from the main project directory:

```bash
python3 ../tools/run.py lake env python3 ../evidence/formal-identity-main-package-295/compile.py
python3 ../evidence/formal-identity-main-package-295/finalize.py
```

All writes are isolated within this evidence directory. No shared Lake writer was started.
