# Isogeny alpha expansion and cusp orders: rendering and current-source validation

The complete Challenge renders all **29 target anchors with zero errors**. It contains **89,218 bytes and 944 lines**, within the published Challenge limits. See [the render record](render.json).

All **857 original serialized declarations** match exactly, including types, ordered universes, definition bodies and proof bodies. Two syntax/elaboration definitions are added. The raw whole-module identity result remains failed because the compiler/syntax declarations differ. The [preservation assessment](declaration-preservation.json) and [raw differences](raw-constant-differences.json) retain this distinction. The old and repaired cache-reset expressions are exactly equal after elaboration. See [the expression check](cache-expression-equality.log). No original mathematical obligation is removed.

The current Solution closure contains **2,976 project modules**: **2,958** were reused from a source-bound, rehashed cache, and **18** were freshly compiled. The [build record](current-solution-build.json) binds current sources and objects before and after compilation. A dependency source changed after the historical official result, which is not treated as verification of the current closure.

The [full strict comparison](full-strict.json) passes for all **29 configured targets**, their complete exported dependency closure and the standard permitted axioms. [Fresh export hashes](export-bindings.json) identify the actual Challenge and current Solution inputs. This is separate from an independent-kernel replay and official acceptance.

Original endpoints **043, 044** are recovered with exactly matching theorem types and ordered universe parameters, only standard permitted axioms, and compiled `rfl` recovery equalities. See [the original type audit](original-endpoint-types.json) and [recovery assessment](original-endpoint-recovery.json). Proof irrelevance in the recovery equalities is used only after Lean accepts the full types. [Direct obligation accounting](target-holes.log) confirms 29 proposition holes and zero definition holes in the Challenge; the Solution supplies every proof. No original hypothesis or universe range is removed.

The [combined readiness assessment](publication-readiness.json) binds these checks. The strict worker's per-scope record marks the separate original recovery audit as pending; that audit is completed by the linked recovery assessment.

Historical official run **39908579898** applies to source `4085af9d0f57a23c83e73eba9b550733a8db1c68`. It does not certify this repaired revision. Fresh official verification and ordinary semantic review remain separate. These local results add no official endpoint coverage and do not establish whole-paper semantic acceptance or registration.
