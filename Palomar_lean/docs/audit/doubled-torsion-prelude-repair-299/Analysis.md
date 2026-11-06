# Doubled-torsion prelude visibility repair 299

The complete 8,849-line isolated module passed its second compilation with exit 0 in 150.209 seconds, using the pinned Lean 4.35.0-rc2 compiler, 12 threads and a finite 600-second budget. No shared project source or Lake object was modified by this worker. The original 17 printed axiom closures all contain only propext, Classical.choice and Quot.sound. The direct module-data audit then checked 714 non-internal declarations in 2.968 seconds: all closures are standard, with zero unexpected axioms. This checks both public and privately imported declarations and skips automatic internal proof helpers. It does not scan Mathlib.

## Root cause and scope

The file opens an exposed public section near line 81. Its adapted later support code explicitly marks several mathematical interfaces private, then creates aliases to them with P2M.Util's p2m_export (lines 4454–4458 and subsequent groups) and uses these aliases or field notation in public theorem types. Lean's module elaborator rejects those public references. The root297 failure at line 4470 is the first occurrence, not a missing mathematical construction or 100 independent proof defects. The same original failure log reports CechTrivialisation, IsFibreReading and IsPicDeformationCocycle identifier failures before its maxErrors cutoff.

The initial isolated patch exposed the eight mutually dependent Cech/SmallExtension definitions. It eliminated that entire error family and let compilation reach line 7988. There it exposed the same visibility problem for sortIdx and inter_le_preimage_inter_sortIdx used by public refinement statements. Those two interfaces were then exposed as well; the second complete compilation succeeded.

## Exact patch

Only ten visibility modifiers change from private to public:

- Scheme.OrderedAffineCover.sortIdx and inter_le_preimage_inter_sortIdx.
- Scheme.Modules.unitAutSection, CechTrivialisation, and CechTrivialisation.restrict, transition, comap.
- SmallExtension.IsFibreReading, IsPicObstructionCocycle, IsPicDeformationCocycle.

All names above are within AlgebraicGeometry. Every mathematical type, definition body and proof body remains textually unchanged. Reversing precisely these ten modifiers reproduces the original source byte for byte. Other private implementation helpers and support theorems remain private. No axiom, sorry, dummy certificate, changed structure map or new conclusion premise was introduced. Visibility changes alter the public/private declaration naming interface intentionally; the downstream consumer already imports the prelude and will require the normal root target rebuild.

The stabilized source, exact project-relative diff, original/candidate hashes, direct dependency object hashes and successful compiler evidence are bound in receipt.json. All 154 directly imported public/private object artifacts were recorded and rechecked. Failed first-attempt evidence is retained rather than relabeled successful. The parent owns integration into project and any later target/full-root build; the isolated validation is not an official Palomar preflight or semantic completion claim.

The first broad-environment audit probe reached its 180-second wall-clock budget and was terminated with exit 124; this failed diagnostic is retained. The successful replacement reads only the target module's constant-name table, checks 714 named declarations and finishes in 2.968 seconds. Two earlier audit-probe elaboration errors (private Lean metaprogramming import, then underconstrained counter types) were corrected in the evidence-only probe; neither affected the successful candidate source.
