# Independent arbitrary formal cover constant package, attempt 275

This package specifies exactly accepted050, `arbitrary_formal_cover_constant`, independently over Mathlib. `Challenge.lean` has 176 lines and 9,199 bytes, imports only Mathlib, and has one intentional target sorry. It reproduces the actual geometric and formal definitions instead of assuming an interface that already contains the desired scalar conclusion.

The target ranges over every characteristic-zero field k of universe Type u, every scheme X over Spec(k[[t]]), and the exact original flatness, properness, smooth generic fiber and geometric connectedness hypotheses. The generic fiber is the actual pullback along k[[t]]→k((t)). It constructs one restriction system before quantifying over all finite covers and all compatible rational no-pole families, then proves existence and uniqueness of a Laurent scalar through the actual structural maps.

## Independent definitions

- The parameter is pulled back through f.appTop and the ΓSpec scalar isomorphism; its principal ideal sheaf and all its powers define actual closed thickenings.
- Each StageSections is the actual structure-sheaf section ring on the preimage of the specified open in that thickening.
- Transition maps use the actual morphisms from inclusions of ideal sheaves.
- FormalRing is the subring of sequences compatible over every thickening, including the empty zeroth stage. It is not replaced by completion of the section ring of an arbitrary nonaffine open.
- The scalar map uses the explicit ΓSpec→f.appLE composition. The project-only algebraOfHom helper is reproduced as this concrete Mathlib expression under the independent namespace, so the Challenge does not reference project-owned declarations.
- GenericRing localizes at the actual parameter; Fractions is its actual fraction ring.
- Restrictions records the actual restrictions on every component and the actual localized extension equation. Cover retains the finite index, opens and closed-fiber cover condition, with no added algebraic-affineness or cyclic-presentation hypothesis.
- ChartConditions retains actual domains, noetherian rings, integral closure and nonzero parameter. RationalCompatible retains every original cross-multiplication equation on overlaps. NoPole ranges over all actual height-one primes. FractionConstant retains the common parameter denominator and the scalar equation in Laurent series, including the zero scalar.

## Structure and definition bridges

`Solution.lean` repeats the same independent definitions and imports `ArbitraryFormalCoverConstantR0210`. It explicitly verifies seven definitional bridges: the parameter ideal, structural scalar map, generic-fiber morphism, formal ring, map of algebraic sections into the formal inverse limit, generic scalar map and fraction ring.

Restrictions and Cover are different structures in the two namespaces. The Solution constructs both directions field by field, retaining every map, equation, count, open and covering proof. Four roundtrip lemmas verify that these conversions lose no data. Four iff bridges verify preservation of ChartConditions, RationalCompatible, NoPole and FractionConstant. The main theorem transports the original constructed restriction witness, applies the actual provider to the converted independent cover, and transports scalar existence and uniqueness back. No geometric conclusion or restriction-system existence is introduced as a new assumption.

## Validation records

`input-bindings.json` binds the original source definition closure, actual provider source/object, source obligation ledger, toolchain and manifest. Per-attempt checkpoints bind independent sources and the exact axiom-check list before Solution compilation. Check logs and the final receipt record genuine terminal results; a planned Comparator run is not counted as a pass.

The standard compile budget is 12 threads and 300 seconds per probe. The Solution prints axioms for all 16 bridge/endpoint lemmas. The final comparison configuration has only the one accepted050 endpoint; supporting bridge lemmas are retained in its actual checked dependency closure where used.

Export and Comparator scripts use isolated outputs and recorded source/object/export hashes. Local comparison uses normal bubblewrap 0.12.0 sandboxing, con-ron --jobs=2, NanoDa and Lean default kernel. This does not itself reproduce the official isolated source-provenance preflight or constitute a public Palomar submission.

All work is confined to `evidence/formal-cover-package-275`. No project sources, shared Lake outputs or accepted contracts are modified. The package asserts no result about the main theta cutoff or complete-paper coverage beyond its one exact source endpoint.
