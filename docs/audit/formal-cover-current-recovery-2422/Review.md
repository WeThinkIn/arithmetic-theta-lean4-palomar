# FormalCover: complete original statement recovery and current-source audit

The independent FormalCover Challenge and its existing Solution are unchanged. The sole configured proposition is retained, with zero definition holes. The Challenge renders all target anchors without elaboration errors under pinned Lean 4.35.0-rc2.

The current Solution builds with 243 source-bound cached project dependencies (212 from the newer cache and 31 from the earlier validated cache). Shared-declaration comparison checks 91 declarations. The complete Challenge and Solution exports pass strict structural comparison and standard-axiom closure.

FormalCoverRecovery2418.lean supplies the previously implicit reverse recovery from the independent interface to the complete original accepted-050 theorem. The checked toRestrictions and fromCover conversions transport the existential restriction system and the arbitrary cover while preserving every original hypothesis. The raw original type expression and ordered universe list are exactly equal; the recovery equality compiles with rfl. Only propext, Classical.choice and Quot.sound occur in the recovery axiom closure. No new premise, axiom, or relaxed statement is introduced.

The recovery is an isolated audit module, not a replacement of the existing Challenge or Solution. The first audit attempt used a private import where the public recovery needed exported Field visibility. That import-visibility failure is retained in prior-audit-error.json. The continuation uses public import FormalCoverSolution and reuses the hash-verified successful Solution build.

These are local checks. A historical official run does not certify this current revision. Fresh exact-revision official verification and ordinary mathematical review remain pending. No new official acceptance, registration or whole-paper completion is claimed.
