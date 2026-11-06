# Stock kernel regression and exact proof restoration

Both published ring-to-grind replacements were valid proofs with exact unchanged theorem propositions. Smaller expression DAGs and exported files did not predict kernel evaluation cost. Target-specific exports of the entire original and replacement theorem closures, with the same primitive roots and the pinned stock Lean checker, all passed. The results justify restoring the two original ring implementations in the Palomar copy.

| Target | Original ring seconds | Replacement grind seconds | Original sampled high-water GiB | Replacement sampled high-water GiB |
|---|---:|---:|---:|---:|
| kw_lrSym_minor_YZ | 6.57 | 79.98 | 0.492 | 12.284 |
| kw_lrThird_minor_YZ | 5.27 | 54.37 | 0.258 | 8.575 |

Measurements ran with bounded CPU affinity and4 Lean runtime threads. High-water marks were read every2seconds and can miss late peaks; other isolated read-only verification processes ran concurrently, so exact timing ratios are not a controlled repeated benchmark. The order-of-magnitude increases in both elapsed time and memory make the implementation reversal appropriate. This is a performance repair, not a mathematical correction or a rejection by the kernel.

The only proof changes restore the exact two source files from the407 baseline, verified against the pre-optimization Git commit fca0320. The103 frozen endpoints,13 original requirements, theorem universes and all independent interfaces remain. No new endpoint credit. The fresh416 full comparator uses its immutable exported bytes and continues; its results describe that optimized export, not the restored source. Existing official jobs are preserved. No official acceptance is inferred from these local tests.

Actual root rebuild and post-build audit receipts are recorded separately; this review must be published only after they pass. The unused420 XZ candidates remain unapplied: proof-size improvement alone is insufficient to justify them.
