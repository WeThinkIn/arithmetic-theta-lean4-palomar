# Material for a possible Palomar size-limit review

This note records the facts that would be needed if Palomar later offers an
official review path for a complete Challenge that exceeds the current size
limit. It is documentation only: no exception, quota increase, registration,
or oversized submission is being requested by this repository at present.

## Current limits

The verifier version recorded by this checkout is
`c02bbeaed888df45c4e28c4e99dba540ad21552a`. Under the corresponding policy, a
Challenge must be at most **102,400 bytes (100 KiB)** and **1,000 lines**. The
published snapshots below are complete source interfaces, but are not eligible
under those limits.

| Interface | Original endpoint | Challenge size | Excess over 102,400 bytes | Excess over 1,000 lines |
| --- | --- | ---: | ---: | ---: |
| `accepted-075` | `ArithmeticThetaCyclotomicModularityR0239.cyclotomic_matrix_modularity` | 144,147 bytes / 577 lines | 41,747 bytes | within line cap |
| `accepted-076` | `ArithmeticThetaExtendedMetaplecticR0241.cyclotomic_extended_modularity` | 160,220 bytes / 600 lines | 57,820 bytes | within line cap |
| `conservative-image-consumer` | `ArithmeticThetaFullSourceR0268.conservative_image_consumer` | 147,894 bytes / 581 lines | 45,494 bytes | within line cap |
| `accepted-087` | `ArithmeticThetaGlobalProjectiveRatiosR0266.global_arithmetic_projective_ratios` | 320,833 bytes / 1,311 lines | 218,433 bytes | 311 lines |

The values are also bound by the machine-readable
[`interfaces/size-limited/manifest.json`](../interfaces/size-limited/manifest.json)
and by each interface's audit receipt.

## Why the complete statements are large

The excess is in the independent Challenge interface, not in a repeated copy
of the proof binary. Each interface must expose the original quantified
mathematical statement and the declarations needed to elaborate it under the
canonical dependency rule.

* `accepted-075` and `accepted-076` retain the actual cyclotomic level,
  compactification, Hodge extension, Tate normalization, solver output, and
  complete formal-series expansion. Each has 45 theorem obligations and 5
  constrained definition obligations. Those definitions are not decorative
  aliases: they connect the exported statement to the arithmetic and geometric
  constructions in `Proof/` and are checked by original-endpoint recovery.
* `conservative-image-consumer` retains the complete consumer theorem: the
  conservative cutoff, exact coefficient matrix and elimination output,
  kernel/image conclusions, unique rational reconstruction, and the full
  geometric hypotheses used by the consumer. It likewise has 45 theorem and 5
  constrained definition obligations.
* `accepted-087` retains the global projective-ratio theorem over the full
  arithmetic/geometric construction and complete-series interpretation. Its
  142 theorem obligations include the projective transport, field-extension,
  level/compactification, normalized section, and ratio-compatibility support
  that the endpoint consumes. Removing those dependencies would change the
  quantified theorem into a supplied-witness or narrowed interface.

The exact source-to-endpoint correspondence is frozen in
[`docs/SourceObligations.json`](SourceObligations.json). The complete Lean
implementations remain under [`Proof/`](../Proof/), while the four published
snapshots and their comparator configurations are under
[`interfaces/size-limited/`](../interfaces/size-limited/README.md).

## Local validation already completed

All four snapshots passed the recorded local compilation, shared-declaration
checks, direct obligation accounting, original-endpoint recovery, and the
Comparator `compareAt` check over the full serialized target closure. The
`accepted-087` snapshot additionally passed fresh export structural/axiom
comparison, Verso rendering, and stock Lean, Conron, and NanoDa typechecking;
the NanoDa axiom pretty-printer emitted a separate diagnostic after successful
typechecking. These are local results and do not confer official Palomar
acceptance. The package READMEs and audit receipts state the precise checks for
each snapshot, including the checks that have not been run for `accepted-075`,
`accepted-076`, and `conservative-image-consumer`.

The surrounding complete development has independently passed the pinned local
Lean **4.35.0-rc2** `GoalRoot` build and the exact type/universe/axiom checks for
all 103 original endpoints. The local toolchain and Mathlib revisions are
recorded in the repository README and lock files.

## Possible official accommodation, if Palomar chooses to provide one

Any accommodation would need to be explicitly offered by Palomar and reviewed
under its normal provenance and kernel checks. A useful request would be:

1. a documented, temporary Challenge byte/line allowance (or a staged package
   mechanism) for these named complete interfaces;
2. the same canonical-import, source-binding, export, and independent-kernel
   checks used for ordinary submissions;
3. enough verifier memory, wall-clock, and log/artifact capacity for the
   142-obligation `accepted-087` export and its three-kernel replay; and
4. an explicit result record that distinguishes this larger-interface review
   from ordinary size-compliant endpoint coverage.

This list describes requested review resources, not an available bypass. Until
Palomar publishes such a path, the repository keeps the complete source and
local evidence available, leaves the four interfaces marked as deferred, and
does not submit them over the current limit.
