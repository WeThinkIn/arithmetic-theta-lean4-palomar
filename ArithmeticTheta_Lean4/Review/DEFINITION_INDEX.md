# Definition index for the two review main theorems

This index covers **every counted custom definition** in the union of the two
review statements, using the elaborated Lean environment recorded in the
[definition dependency report](verification/DefinitionDependencyReport.json).
It is grouped by mathematical role so that the 12 new interfaces can be read
first, followed by the retained family, normalization, sheaf, series and
arithmetic definitions. Each entry links to its actual source declaration.

**C** means [`conservative_image_review`](Lean/ReviewMainTheorems.lean);
**M** means [`cyclotomic_modularity_review`](Lean/ReviewMainTheorems.lean).
These tags record membership in the respective recursive statement closure.

| Statement | Original definitions | Review definitions | Net reduction |
| --- | ---: | ---: | ---: |
| Conservative kernel/image/modularity | 340 | 224 | 116 (34.12%) |
| Cyclotomic sharp modularity | 317 | 188 | 129 (40.69%) |

The union has **225 definitions**; definitions used by both statements are
listed only once. The original sharp matrix-kernel statement remains at 23
definitions under the same convention.

This is a reduction in dependencies needed to **read the statements**, not a
compression of the proofs or their transitive proof dependencies. The review
theorems are proved projections of the richer original construction theorems.
They do not have identical complete types to those original witness theorems.
The original theorems, construction data, sources and audits remain available.
The adapter preserves the actual curve, structural scalar map, half line, disk,
frame, sections, compact square and normalized Hodge generator. A single family
is still chosen before the universal quantifier over admissible cutoffs.

The count follows definition bodies and all structure fields, including proof-field
predicates. Abbreviations and opaque non-proof definitions therefore do not hide
their dependencies. Theorem proof bodies and external library bodies are outside
this statement-reading metric. See the
[precise convention and regression tests](scripts/DEFINITION_METRIC.md).
The count includes six **public named generated matcher
helpers** (`match_1`), which are explicitly labeled below and linked to the
definitions that generate them. These names are not classified as compiler-internal
by Lean, unlike the internal names excluded from the count. They are not six
additional handwritten concepts; no second adjusted headline count is used.

Quoted descriptions below are the declarations' actual Lean docstrings.
Historical wording in a quoted comment is not a new validation claim. Where a
docstring is absent, the entry says so and quotes the actual declaration header;
no mathematical description has been guessed from its name. “Next definitions”
means the next counted custom declarations after traversing projection and
constructor bookkeeping; the complete direct dependency graph is in the JSON.

## What moved behind the construction bridges

The conservative statement no longer requires 128 of its original definitions
and adds 12 review definitions. The cyclotomic statement removes 141 and adds
the same 12. In both cases the statement no longer unfolds the following
construction-specific records and functions:

- `ArithmeticThetaArithmeticFieldR0231.MatrixData` and `MatrixData.root`;
- `ArithmeticThetaCompactModularityR0209.CompactRoot`;
- `ArithmeticThetaLevelCompactificationR0179.LevelData`;
- `ArithmeticThetaActualLevelR0208.Provider`, `FiniteEtaleLevel`, `UsesFiber`,
  `canonicalMap` and `testRoot`;
- `ArithmeticThetaMetaplecticStackR0207.ActualFamilyFPQCDescentProof.Provider`;
- `ArithmeticThetaSimultaneousUnaryR0187.RootCover`.

These remain part of the original proofs. Their public review replacements
retain actual elliptic families, marked arrows and pullbacks, the metaplectic
stack and its coherence, finite étale representability, compact regular sections,
the specified Tate normalization and the complete `q = t^L` expansion.
The conservative statement still includes the original conservative-cutoff
specification, so its arithmetic decomposition/indexing dependencies remain.

## Navigation

| Group | Definitions | In C | In M |
| --- | ---: | ---: | ---: |
| [The new review interfaces](#review) | 12 | 12 | 12 |
| [Elliptic families, level structures and the actual metaplectic stack](#moduli) | 53 | 53 | 53 |
| [Tate curves, differentials and Hodge normalization](#normalization) | 54 | 54 | 53 |
| [Sheaves, tensor powers and section operations](#sheaves) | 29 | 29 | 29 |
| [Lattice theta series and image statements](#series) | 20 | 20 | 12 |
| [Arithmetic inputs, cutoffs and elimination](#arithmetic) | 57 | 56 | 29 |

<a id="review"></a>

## The new review interfaces

Read these 12 interfaces first. Their source docstrings specify which
actual maps, squares, frames and compatibility conditions they retain.

<a id="d001"></a>

**D001 — [`ArithmeticThetaReview.Geometry.CompactCurve`](Lean/ReviewGeometryDefinitions.lean#L44)**

Used by **C, M** · `structure` · module `ReviewGeometryDefinitions`.

> A compact curve, its half-weight line, and the actual finite level on a dense open. The line on the level is literally the restriction of this line, not an unrelated line with an arbitrarily chosen expansion map.

Next definitions: [D002](#d002), [D013](#d013), [D021](#d021), [D022](#d022), [D039](#d039), [D043](#d043), [D044](#d044), [D046](#d046), [D055](#d055), [D103](#d103), [D143](#d143).

<a id="d002"></a>

**D002 — [`ArithmeticThetaReview.Geometry.FiniteLevel`](Lean/ReviewGeometryDefinitions.lean#L30)**

Used by **C, M** · `definition` · module `ReviewGeometryDefinitions`.

> Every base change to a scheme is represented by a finite étale scheme. The bound concerns the actual projection to that test scheme; zero rank on other components is allowed. Both projections and naturality are retained by `FiberPresentation`. This predicate makes no reference to an atlas/provider.

Next definitions: [D013](#d013), [D014](#d014), [D015](#d015), [D021](#d021), [D038](#d038), [D043](#d043), [D044](#d044), [D049](#d049), [D065](#d065).

<a id="d003"></a>

**D003 — [`ArithmeticThetaReview.Geometry.FramedFamily`](Lean/ReviewGeometryDefinitions.lean#L69)**

Used by **C, M** · `structure` · module `ReviewGeometryDefinitions`.

> A specified dominant formal disk and its genuine line-bundle frame. These are geometric pullbacks and global sections, not abstract linear functionals. The normalization bridge identifies the original Tate frame.

Next definitions: [D001](#d001), [D006](#d006), [D021](#d021), [D039](#d039), [D095](#d095), [D110](#d110), [D111](#d111), [D114](#d114), [D115](#d115), [D145](#d145), [D154](#d154).

<a id="d004"></a>

**D004 — [`ArithmeticThetaReview.Geometry.Realizes`](Lean/ReviewGeometryDefinitions.lean#L84)**

Used by **C, M** · `definition` · module `ReviewGeometryDefinitions`.

> Complete theta expansions in the displayed frame, with the literal substitution `q = t^L` and the scalar action of the actual structure morphism.

Next definitions: [D001](#d001), [D003](#d003), [D021](#d021), [D087](#d087), [D089](#d089), [D110](#d110), [D122](#d122), [D145](#d145), [D147](#d147), [D154](#d154), [D155](#d155), [D158](#d158), [D163](#d163).

<a id="d005"></a>

**D005 — [`ArithmeticThetaReview.Normalization.CanonicalCotangent`](Lean/ReviewNormalizationDefinitions.lean#L50)**

Used by **C, M** · `definition` · module `ReviewNormalizationDefinitions`.

> The affine Hodge-to-cotangent comparison is fixed by the actual conormal map and the identity-ideal inclusion. This is the original classifier equation with only its family and maps as parameters.

Next definitions: [D012](#d012), [D019](#d019), [D021](#d021), [D022](#d022), [D023](#d023), [D086](#d086), [D089](#d089), [D103](#d103), [D105](#d105), [D106](#d106), [D107](#d107).

<a id="d006"></a>

**D006 — [`ArithmeticThetaReview.Normalization.FrameNormalization`](Lean/ReviewNormalizationDefinitions.lean#L172)**

Used by **C, M** · `structure` · module `ReviewNormalizationDefinitions`.

> All Tate normalization data for one framed compact family. The interior root, compact square, and disk frame are linked in the same record.

Next definitions: [D007](#d007), [D008](#d008), [D009](#d009), [D022](#d022), [D039](#d039), [D103](#d103), [D110](#d110), [D143](#d143), [D145](#d145).

<a id="d007"></a>

**D007 — [`ArithmeticThetaReview.Normalization.InteriorLink`](Lean/ReviewNormalizationDefinitions.lean#L131)**

Used by **C, M** · `structure` · module `ReviewNormalizationDefinitions`.

> The metaplectic family's marked curve and root square are the restrictions of this very compact square. The equality of root lines fixes the transport in the final equation; no independent square root or scalar comparison is chosen.

Next definitions: [D005](#d005), [D009](#d009), [D011](#d011), [D012](#d012), [D019](#d019), [D020](#d020), [D022](#d022), [D023](#d023), [D039](#d039), [D056](#d056), [D058](#d058), [D086](#d086), [D089](#d089), [D103](#d103), [D120](#d120), [D143](#d143), [D145](#d145).

<a id="d008"></a>

**D008 — [`ArithmeticThetaReview.Normalization.NormalizedFrame`](Lean/ReviewNormalizationDefinitions.lean#L155)**

Used by **C, M** · `structure` · module `ReviewNormalizationDefinitions`.

> The square of the actual half-weight frame is a regular Hodge generator, whose punctured value is the prescribed normalized Tate differential.

Next definitions: [D009](#d009), [D010](#d010), [D066](#d066), [D068](#d068), [D090](#d090), [D095](#d095), [D097](#d097), [D108](#d108), [D110](#d110), [D111](#d111), [D112](#d112), [D115](#d115), [D145](#d145), [D147](#d147).

<a id="d009"></a>

**D009 — [`ArithmeticThetaReview.Normalization.TateChart`](Lean/ReviewNormalizationDefinitions.lean#L69)**

Used by **C, M** · `structure` · module `ReviewNormalizationDefinitions`.

> A marked Tate test of the actual open Hodge line and its extension to a disk on a compact target. The period is the one in `TateCurve k L`, namely t^L. The prescribed differential satisfies dx = (2y) delta on the fixed Tate chart.

Next definitions: [D018](#d018), [D019](#d019), [D020](#d020), [D066](#d066), [D067](#d067), [D084](#d084), [D086](#d086), [D089](#d089), [D096](#d096), [D098](#d098), [D100](#d100), [D102](#d102), [D110](#d110), [D111](#d111), [D112](#d112), [D113](#d113), [D115](#d115).

<a id="d010"></a>

**D010 — [`ArithmeticThetaReview.Normalization.TateChart.comparison`](Lean/ReviewNormalizationDefinitions.lean#L99)**

Used by **C, M** · `definition` · module `ReviewNormalizationDefinitions`.

> Canonical comparison obtained by composing the actual pullback maps and the pointed differential comparison of the displayed Cartesian Tate test.

Next definitions: [D009](#d009), [D019](#d019), [D084](#d084), [D085](#d085), [D086](#d086), [D089](#d089), [D090](#d090), [D093](#d093), [D096](#d096), [D100](#d100), [D110](#d110), [D111](#d111), [D112](#d112), [D113](#d113), [D115](#d115).

<a id="d011"></a>

**D011 — [`ArithmeticThetaReview.Normalization.restrictedSquare`](Lean/ReviewNormalizationDefinitions.lean#L112)**

Used by **C, M** · `definition` · module `ReviewNormalizationDefinitions`.

> Restriction of a specified compact square map along the actual open triangle, followed by the displayed open Hodge comparison.

Next definitions: [D009](#d009), [D019](#d019), [D086](#d086), [D089](#d089), [D132](#d132), [D145](#d145).

<a id="d012"></a>

**D012 — [`ArithmeticThetaReview.Normalization.schemeFamily`](Lean/ReviewNormalizationDefinitions.lean#L34)**

Used by **C, M** · `definition` · module `ReviewNormalizationDefinitions`.

> The general-scheme view of an affine elliptic family uses precisely the same curve, structure map, group operations and geometric properties.

Next definitions: [D019](#d019), [D022](#d022), [D024](#d024), [D089](#d089).


<a id="moduli"></a>

## Elliptic families, level structures and the actual metaplectic stack

<a id="d013"></a>

**D013 — [`ArithmeticThetaActualLevelR0208.AnchoredMap`](../Lean/ActualLevelDefinitionsR0208.lean#L40)**

Used by **C, M** · `structure` · module `ActualLevelDefinitionsR0208`.

> A classifying map with an actual family isomorphism at its identity test.

Next definitions: [D021](#d021), [D038](#d038), [D043](#d043), [D044](#d044), [D049](#d049), [D062](#d062), [D065](#d065).

<a id="d014"></a>

**D014 — [`ArithmeticThetaActualLevelR0208.FiberPresentation`](../Lean/ActualLevelDefinitionsR0208.lean#L78)**

Used by **C, M** · `structure` · module `ActualLevelDefinitionsR0208`.

> Representability on all field-base tests, with both projections and naturality.

Next definitions: [D016](#d016), [D017](#d017), [D021](#d021), [D043](#d043), [D044](#d044), [D061](#d061), [D062](#d062), [D064](#d064), [D065](#d065).

<a id="d015"></a>

**D015 — [`ArithmeticThetaActualLevelR0208.PullbackComparison`](../Lean/ActualLevelDefinitionsR0208.lean#L53)**

Used by **C, M** · `structure` · module `ActualLevelDefinitionsR0208`.

> Actual family/root comparison, natural in every test morphism and normalized at identity. Its arrows retain the marked curve, cotangent and full square map.

Next definitions: [D013](#d013), [D021](#d021), [D037](#d037), [D038](#d038), [D040](#d040), [D041](#d041), [D043](#d043), [D044](#d044), [D048](#d048), [D049](#d049), [D051](#d051), [D052](#d052), [D062](#d062), [D065](#d065).

<a id="d016"></a>

**D016 — [`ArithmeticThetaActualLevelR0208.TestFiber`](../Lean/ActualLevelDefinitionsR0208.lean#L66)**

Used by **C, M** · `definition` · module `ActualLevelDefinitionsR0208`.

> All arrows in the categorical fiber of actual family maps over Spec k.

Next definitions: [D021](#d021), [D043](#d043), [D044](#d044), [D065](#d065).

<a id="d017"></a>

**D017 — [`ArithmeticThetaActualLevelR0208.fiberPull`](../Lean/ActualLevelDefinitionsR0208.lean#L71)**

Used by **C, M** · `definition` · module `ActualLevelDefinitionsR0208`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def fiberPull {C : Coherence L (Base k)} {Y T S S' : Over (Base k)}
```

Next definitions: [D016](#d016), [D021](#d021), [D043](#d043), [D044](#d044), [D065](#d065).

<a id="d018"></a>

**D018 — [`ArithmeticThetaFullLevelCoverR0175.FullLevel`](../Lean/FullLevelCoverDefinitionsR0175.lean#L21)**

Used by **C, M** · `structure` · module `FullLevelCoverDefinitionsR0175`.

> Two killed sections whose nonzero residue combinations avoid the actual identity subscheme. The test scheme may be nonreduced or disconnected.

Next definitions: [D089](#d089), [D098](#d098), [D100](#d100), [D101](#d101), [D102](#d102).

<a id="d019"></a>

**D019 — [`ArithmeticThetaLegendreAtlasR0176.EllipticFamily`](../Lean/LegendreLevelAtlasDefinitionsR0176.lean#L91)**

Used by **C, M** · `structure` · module `LegendreLevelAtlasDefinitionsR0176`.

> A genuine elliptic family over the quotient ring. The law is on all scheme-valued points, and smoothness/properness concern its actual structure map.

Next definitions: [D089](#d089).

<a id="d020"></a>

**D020 — [`ArithmeticThetaLegendreAtlasR0176.FamilyLevel`](../Lean/LegendreLevelAtlasDefinitionsR0176.lean#L100)**

Used by **C, M** · `structure` · module `LegendreLevelAtlasDefinitionsR0176`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
structure FamilyLevel (S : Type u) [CommRing S] (E : EllipticFamily S) (L : ℕ) where
```

Next definitions: [D019](#d019), [D089](#d089).

<a id="d021"></a>

**D021 — [`ArithmeticThetaLocalWeierstrassR0203.Base`](../Lean/LocalWeierstrassDefinitionsR0203.lean#L12)**

Used by **C, M** · `definition` · module `LocalWeierstrassDefinitionsR0203`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
```

No further counted custom definition is reached before the external-library boundary.

<a id="d022"></a>

**D022 — [`ArithmeticThetaLocalWeierstrassR0203.Family`](../Lean/LocalWeierstrassDefinitionsR0203.lean#L92)**

Used by **C, M** · `structure` · module `LocalWeierstrassDefinitionsR0203`.

> A smooth proper one-dimensional commutative group scheme with connected fibres.

Next definitions: [D024](#d024).

<a id="d023"></a>

**D023 — [`ArithmeticThetaLocalWeierstrassR0203.Family.zero`](../Lean/LocalWeierstrassDefinitionsR0203.lean#L100)**

Used by **C, M** · `definition` · module `LocalWeierstrassDefinitionsR0203`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def Family.zero {S : Scheme.{u}} (E : Family S) : S ⟶ E.curve :=
```

Next definitions: [D022](#d022), [D024](#d024).

<a id="d024"></a>

**D024 — [`ArithmeticThetaLocalWeierstrassR0203.SchemeLaw`](../Lean/LocalWeierstrassDefinitionsR0203.lean#L73)**

Used by **C, M** · `structure` · module `LocalWeierstrassDefinitionsR0203`.

> A natural commutative group law on all scheme-valued points over any base.

No further counted custom definition is reached before the external-library boundary.

<a id="d025"></a>

**D025 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualGroupoidProof.backward`](../Lean/ActualMetaplecticGroupoidR0206.lean#L72)**

Used by **C, M** · `definition` · module `ActualMetaplecticGroupoidR0206`.

> The uniquely inclusion-normalized backward cotangent comparison.

Next definitions: [D022](#d022), [D023](#d023), [D103](#d103), [D105](#d105), [D107](#d107).

<a id="d026"></a>

**D026 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualGroupoidProof.inverse`](../Lean/ActualMetaplecticGroupoidR0206.lean#L221)**

Used by **C, M** · `definition` · module `ActualMetaplecticGroupoidR0206`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def inverse {X Y : Object L S} (f : Arrow X Y) : Arrow Y X where
```

Next definitions: [D022](#d022), [D036](#d036), [D039](#d039), [D056](#d056), [D057](#d057), [D103](#d103), [D104](#d104), [D120](#d120), [D143](#d143), [D145](#d145).

<a id="d027"></a>

**D027 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualPullbackProof.Lift`](../Lean/ActualMetaplecticPullbackR0206.lean#L18)**

Used by **C, M** · `structure` · module `ActualMetaplecticPullbackR0206`.

> A chosen Cartesian family, retaining the actual pullback line.

Next definitions: [D022](#d022), [D039](#d039), [D056](#d056), [D057](#d057), [D103](#d103), [D104](#d104), [D120](#d120), [D143](#d143), [D144](#d144), [D145](#d145).

<a id="d028"></a>

**D028 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualPullbackProof.arrow`](../Lean/ActualMetaplecticPullbackR0206.lean#L229)**

Used by **C, M** · `definition` · module `ActualMetaplecticPullbackR0206`.

> The line arrow is the actual sheaf pullback and obeys the exact square.

Next definitions: [D022](#d022), [D025](#d025), [D027](#d027), [D029](#d029), [D033](#d033), [D036](#d036), [D039](#d039), [D056](#d056), [D057](#d057), [D103](#d103), [D104](#d104), [D120](#d120), [D143](#d143), [D145](#d145).

<a id="d029"></a>

**D029 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualPullbackProof.curveIso`](../Lean/ActualMetaplecticPullbackR0206.lean#L68)**

Used by **C, M** · `definition` · module `ActualMetaplecticPullbackR0206`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def curveIso (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
```

Next definitions: [D022](#d022), [D026](#d026), [D027](#d027), [D030](#d030), [D036](#d036), [D039](#d039).

<a id="d030"></a>

**D030 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualPullbackProof.curveMap`](../Lean/ActualMetaplecticPullbackR0206.lean#L47)**

Used by **C, M** · `definition` · module `ActualMetaplecticPullbackR0206`.

> Universal-property lift of a curve arrow.

Next definitions: [D022](#d022), [D027](#d027), [D036](#d036), [D039](#d039).

<a id="d031"></a>

**D031 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualPullbackProof.lift`](../Lean/ActualMetaplecticPullbackR0206.lean#L28)**

Used by **C, M** · `definition` · module `ActualMetaplecticPullbackR0206`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def lift (X : Object L S) : Lift a X := Classical.choice (by
```

Next definitions: [D027](#d027), [D039](#d039).

<a id="d032"></a>

**D032 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualPullbackProof.lineIso`](../Lean/ActualMetaplecticPullbackR0206.lean#L195)**

Used by **C, M** · `definition` · module `ActualMetaplecticPullbackR0206`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def lineIso (P : Lift a X) : P.obj.root.line ≅ (Scheme.Modules.pullback a).obj X.root.line :=
```

Next definitions: [D022](#d022), [D027](#d027), [D039](#d039), [D103](#d103), [D143](#d143).

<a id="d033"></a>

**D033 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualPullbackProof.lineMap`](../Lean/ActualMetaplecticPullbackR0206.lean#L198)**

Used by **C, M** · `definition` · module `ActualMetaplecticPullbackR0206`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def lineMap (P : Lift a X) (Q : Lift a Y) (f : Arrow X Y) :
```

Next definitions: [D022](#d022), [D027](#d027), [D032](#d032), [D036](#d036), [D039](#d039), [D103](#d103), [D143](#d143).

<a id="d034"></a>

**D034 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualPullbackProof.pullData`](../Lean/ActualMetaplecticPullbackR0206.lean#L286)**

Used by **C, M** · `definition` · module `ActualMetaplecticPullbackR0206`.

> The simultaneous curve, canonical cotangent, and line comparisons.

Next definitions: [D022](#d022), [D027](#d027), [D031](#d031), [D032](#d032), [D035](#d035), [D036](#d036), [D037](#d037), [D038](#d038), [D039](#d039), [D040](#d040), [D041](#d041), [D056](#d056), [D057](#d057), [D103](#d103), [D104](#d104), [D120](#d120), [D143](#d143), [D144](#d144), [D145](#d145).

<a id="d035"></a>

**D035 — [`ArithmeticThetaMetaplecticComparisonR0206.ActualPullbackProof.pullFunctor`](../Lean/ActualMetaplecticPullbackR0206.lean#L261)**

Used by **C, M** · `definition` · module `ActualMetaplecticPullbackR0206`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def pullFunctor : GS.Objects ⥤ GT.Objects where
```

Next definitions: [D027](#d027), [D028](#d028), [D031](#d031), [D036](#d036), [D037](#d037), [D038](#d038), [D039](#d039), [D041](#d041).

<a id="d036"></a>

**D036 — [`ArithmeticThetaMetaplecticComparisonR0206.Arrow`](../Lean/MetaplecticComparisonDefinitionsR0206.lean#L27)**

Used by **C, M** · `structure` · module `MetaplecticComparisonDefinitionsR0206`.

> Actual isomorphisms, including the inclusion-normalized cotangent map. The cotangent map points forward, the inverse of differential pullback.

Next definitions: [D022](#d022), [D039](#d039), [D056](#d056), [D057](#d057), [D103](#d103), [D104](#d104), [D120](#d120), [D143](#d143), [D145](#d145).

<a id="d037"></a>

**D037 — [`ArithmeticThetaMetaplecticComparisonR0206.GroupoidData`](../Lean/MetaplecticComparisonDefinitionsR0206.lean#L39)**

Used by **C, M** · `structure` · module `MetaplecticComparisonDefinitionsR0206`.

> The category must have exactly these arrows, and the actual curve/line composition laws. This is construction output, not an input category of classes.

Next definitions: [D022](#d022), [D036](#d036), [D039](#d039), [D103](#d103), [D143](#d143).

<a id="d038"></a>

**D038 — [`ArithmeticThetaMetaplecticComparisonR0206.GroupoidData.Objects`](../Lean/MetaplecticComparisonDefinitionsR0206.lean#L51)**

Used by **C, M** · `definition` · module `MetaplecticComparisonDefinitionsR0206`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def GroupoidData.Objects {L : ℕ} {S : Scheme.{0}} (_G : GroupoidData L S) := Object L S
```

Next definitions: [D037](#d037), [D039](#d039).

<a id="d039"></a>

**D039 — [`ArithmeticThetaMetaplecticComparisonR0206.Object`](../Lean/MetaplecticComparisonDefinitionsR0206.lean#L20)**

Used by **C, M** · `structure` · module `MetaplecticComparisonDefinitionsR0206`.

> An arbitrary marked elliptic family and a root of its ACTUAL cotangent. There is no chosen classifier, equation, frame or Hodge comparison in this input.

Next definitions: [D022](#d022), [D056](#d056), [D103](#d103), [D143](#d143).

<a id="d040"></a>

**D040 — [`ArithmeticThetaMetaplecticComparisonR0206.PullbackData`](../Lean/MetaplecticComparisonDefinitionsR0206.lean#L63)**

Used by **C, M** · `structure` · module `MetaplecticComparisonDefinitionsR0206`.

> A functorial pullback of the actual families with their actual roots. Both curve and line squares commute for every arrow, not only geometric points.

Next definitions: [D022](#d022), [D036](#d036), [D037](#d037), [D038](#d038), [D039](#d039), [D041](#d041), [D056](#d056), [D057](#d057), [D103](#d103), [D104](#d104), [D120](#d120), [D143](#d143), [D144](#d144), [D145](#d145).

<a id="d041"></a>

**D041 — [`ArithmeticThetaMetaplecticComparisonR0206.instGroupoidObjects`](../Lean/MetaplecticComparisonDefinitionsR0206.lean#L53)**

Used by **C, M** · `definition` · module `MetaplecticComparisonDefinitionsR0206`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
instance {L : ℕ} {S : Scheme.{0}} (G : GroupoidData L S) : Groupoid.{0} G.Objects := G.groupoid
```

Next definitions: [D037](#d037), [D038](#d038), [D039](#d039).

<a id="d042"></a>

**D042 — [`ArithmeticThetaMetaplecticComparisonR0206.lineForget`](../Lean/MetaplecticComparisonDefinitionsR0206.lean#L55)**

Used by **C, M** · `definition` · module `MetaplecticComparisonDefinitionsR0206`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def lineForget {L : ℕ} {S : Scheme.{0}} (G : GroupoidData L S) : G.Objects ⥤ S.Modules where
```

Next definitions: [D022](#d022), [D036](#d036), [D037](#d037), [D038](#d038), [D039](#d039), [D041](#d041), [D103](#d103), [D143](#d143).

<a id="d043"></a>

**D043 — [`ArithmeticThetaMetaplecticStackR0207.Coherence`](../Lean/MetaplecticStackDefinitionsR0207.lean#L56)**

Used by **C, M** · `structure` · module `MetaplecticStackDefinitionsR0207`.

> Actual unit and composition isomorphisms with pentagon and both triangle laws. These are required outputs, not hypotheses of the construction theorem.

Next definitions: [D045](#d045), [D047](#d047), [D048](#d048), [D049](#d049), [D051](#d051), [D052](#d052).

<a id="d044"></a>

**D044 — [`ArithmeticThetaMetaplecticStackR0207.Coherence.functor`](../Lean/MetaplecticStackDefinitionsR0207.lean#L77)**

Used by **C, M** · `definition` · module `MetaplecticStackDefinitionsR0207`.

> Standard categorical packaging of the required coherence laws.

Next definitions: [D043](#d043), [D048](#d048), [D052](#d052).

<a id="d045"></a>

**D045 — [`ArithmeticThetaMetaplecticStackR0207.CompNormalized`](../Lean/MetaplecticStackDefinitionsR0207.lean#L34)**

Used by **C, M** · `definition` · module `MetaplecticStackDefinitionsR0207`.

> Both geometric components of composition are fixed, including the original Cartesion projections and the canonical sheaf pullback associativity map.

Next definitions: [D022](#d022), [D036](#d036), [D037](#d037), [D038](#d038), [D039](#d039), [D040](#d040), [D041](#d041), [D103](#d103), [D143](#d143).

<a id="d046"></a>

**D046 — [`ArithmeticThetaMetaplecticStackR0207.ForgetData`](../Lean/MetaplecticStackDefinitionsR0207.lean#L92)**

Used by **C, M** · `structure` · module `MetaplecticStackDefinitionsR0207`.

> A coherent tautological line, with the specified actual pullback map. HEq only compares the dependent functor hom types after app_eq; it does not weaken either map or permit an arbitrary scalar.

Next definitions: [D037](#d037), [D038](#d038), [D040](#d040), [D041](#d041), [D042](#d042), [D043](#d043), [D044](#d044), [D049](#d049), [D050](#d050), [D051](#d051), [D054](#d054).

<a id="d047"></a>

**D047 — [`ArithmeticThetaMetaplecticStackR0207.UnitNormalized`](../Lean/MetaplecticStackDefinitionsR0207.lean#L26)**

Used by **C, M** · `definition` · module `MetaplecticStackDefinitionsR0207`.

> Both geometric components of the unit comparison are fixed.

Next definitions: [D022](#d022), [D036](#d036), [D037](#d037), [D038](#d038), [D039](#d039), [D040](#d040), [D041](#d041), [D103](#d103), [D143](#d143).

<a id="d048"></a>

**D048 — [`ArithmeticThetaMetaplecticStackR0207.fiber`](../Lean/MetaplecticStackDefinitionsR0207.lean#L49)**

Used by **C, M** · `definition` · module `MetaplecticStackDefinitionsR0207`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def fiber (S : (Over B)ᵒᵖ) : Cat.{0, 1} := Cat.of (group L S.unop.left).Objects
```

Next definitions: [D038](#d038), [D041](#d041), [D049](#d049).

<a id="d049"></a>

**D049 — [`ArithmeticThetaMetaplecticStackR0207.group`](../Lean/MetaplecticStackDefinitionsR0207.lean#L17)**

Used by **C, M** · `definition` · module `MetaplecticStackDefinitionsR0207`.

> Fix already constructed actual groupoids, without changing their objects or arrows.

Next definitions: [D037](#d037).

<a id="d050"></a>

**D050 — [`ArithmeticThetaMetaplecticStackR0207.linePull`](../Lean/MetaplecticStackDefinitionsR0207.lean#L83)**

Used by **C, M** · `definition` · module `MetaplecticStackDefinitionsR0207`.

> The already proved line-naturality equation, presented as a natural iso.

Next definitions: [D022](#d022), [D037](#d037), [D038](#d038), [D039](#d039), [D040](#d040), [D041](#d041), [D042](#d042), [D049](#d049), [D051](#d051), [D103](#d103), [D143](#d143).

<a id="d051"></a>

**D051 — [`ArithmeticThetaMetaplecticStackR0207.pull`](../Lean/MetaplecticStackDefinitionsR0207.lean#L21)**

Used by **C, M** · `definition` · module `MetaplecticStackDefinitionsR0207`.

> Use the accepted geometric pullback and all its curve, cotangent and line equations.

Next definitions: [D034](#d034), [D040](#d040), [D049](#d049).

<a id="d052"></a>

**D052 — [`ArithmeticThetaMetaplecticStackR0207.reindex`](../Lean/MetaplecticStackDefinitionsR0207.lean#L51)**

Used by **C, M** · `definition` · module `MetaplecticStackDefinitionsR0207`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def reindex {S T : (Over B)ᵒᵖ} (f : S ⟶ T) : fiber L B S ⟶ fiber L B T :=
```

Next definitions: [D037](#d037), [D038](#d038), [D040](#d040), [D041](#d041), [D048](#d048), [D049](#d049), [D051](#d051).

<a id="d053"></a>

**D053 — [`ArithmeticThetaRootDescentR0197.moduleFunctor`](../Lean/RootDescentDefinitionsR0197.lean#L24)**

Used by **C, M** · `definition` · module `RootDescentDefinitionsR0197`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev moduleFunctor := (Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁
```

No further counted custom definition is reached before the external-library boundary.

<a id="d054"></a>

**D054 — [`ArithmeticThetaRootStackR0198.modulesOver`](../Lean/RootStackDefinitionsR0198.lean#L21)**

Used by **C, M** · `definition` · module `RootStackDefinitionsR0198`.

> The actual sheaf pullback pseudofunctor on schemes over B.

Next definitions: [D053](#d053).

<a id="d055"></a>

**D055 — [`ArithmeticThetaRootStackR0198.rootTopology`](../Lean/RootStackDefinitionsR0198.lean#L67)**

Used by **C, M** · `definition` · module `RootStackDefinitionsR0198`.

> The standard big fpqc topology on schemes over the specified base.

No further counted custom definition is reached before the external-library boundary.

<a id="d056"></a>

**D056 — [`ArithmeticThetaSchemeLevelR0204.FullLevel`](../Lean/SchemeLevelDefinitionsR0204.lean#L21)**

Used by **C, M** · `structure` · module `SchemeLevelDefinitionsR0204`.

> A full ordered marking, tested on the actual identity subscheme.

Next definitions: [D022](#d022), [D023](#d023), [D024](#d024), [D059](#d059).

<a id="d057"></a>

**D057 — [`ArithmeticThetaSchemeLevelR0204.MarkedCartesian`](../Lean/SchemeLevelDefinitionsR0204.lean#L39)**

Used by **C, M** · `definition` · module `SchemeLevelDefinitionsR0204`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def MarkedCartesian {S T : Scheme.{u}} {L : ℕ} (E : Family S) (F : Family T)
```

Next definitions: [D022](#d022), [D023](#d023), [D056](#d056), [D058](#d058).

<a id="d058"></a>

**D058 — [`ArithmeticThetaSchemeLevelR0204.Multiplicative`](../Lean/SchemeLevelDefinitionsR0204.lean#L32)**

Used by **C, M** · `definition` · module `SchemeLevelDefinitionsR0204`.

> Compatibility with multiplication on every actual scheme-valued point.

Next definitions: [D022](#d022), [D024](#d024).

<a id="d059"></a>

**D059 — [`ArithmeticThetaSchemeLevelR0204.multiple`](../Lean/SchemeLevelDefinitionsR0204.lean#L15)**

Used by **C, M** · `definition` · module `SchemeLevelDefinitionsR0204`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def multiple {S : Scheme.{u}} (E : Family S) {T : Scheme.{u}}
```

Next definitions: [D022](#d022), [D024](#d024), [D060](#d060).

<a id="d060"></a>

**D060 — [`ArithmeticThetaSchemeLevelR0204.multiple.match_1`](../Lean/SchemeLevelDefinitionsR0204.lean#L15)**

Used by **C, M** · `definition` · module `SchemeLevelDefinitionsR0204`.

Lean-generated pattern-matching helper for `ArithmeticThetaSchemeLevelR0204.multiple`. It has no
separate handwritten declaration or docstring; the source link opens
its generating definition. It is included in the technical count.

Next definitions: [D022](#d022).

<a id="d061"></a>

**D061 — [`ArithmeticThetaStackLevelR0199.Points`](../Lean/StackLevelDefinitionsR0199.lean#L18)**

Used by **C, M** · `definition` · module `StackLevelDefinitionsR0199`.

> A universe lift of the discrete functor of points; arrows remain small.

No further counted custom definition is reached before the external-library boundary.

<a id="d062"></a>

**D062 — [`ArithmeticThetaStackLevelR0199.point`](../Lean/StackLevelDefinitionsR0199.lean#L20)**

Used by **C, M** · `definition` · module `StackLevelDefinitionsR0199`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def point {B : Scheme.{0}} {S Y : Over B} (f : S ⟶ Y) : Points S Y := ⟨⟨f⟩⟩
```

Next definitions: [D061](#d061).

<a id="d063"></a>

**D063 — [`ArithmeticThetaStackLevelR0199.pointsFunctor`](../Lean/StackLevelDefinitionsR0199.lean#L27)**

Used by **C, M** · `definition` · module `StackLevelDefinitionsR0199`.

> The representable presheaf as a category-valued functor.

Next definitions: [D061](#d061), [D064](#d064).

<a id="d064"></a>

**D064 — [`ArithmeticThetaStackLevelR0199.precompose`](../Lean/StackLevelDefinitionsR0199.lean#L22)**

Used by **C, M** · `definition` · module `StackLevelDefinitionsR0199`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def precompose {B : Scheme.{0}} {S T : Over B} (Y : Over B) (a : S ⟶ T) :
```

Next definitions: [D061](#d061), [D062](#d062).

<a id="d065"></a>

**D065 — [`ArithmeticThetaStackLevelR0199.representable`](../Lean/StackLevelDefinitionsR0199.lean#L52)**

Used by **C, M** · `definition` · module `StackLevelDefinitionsR0199`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev representable {B : Scheme.{0}} (Y : Over B) := (pointsFunctor Y).toPseudofunctor'
```

Next definitions: [D063](#d063).


<a id="normalization"></a>

## Tate curves, differentials and Hodge normalization

<a id="d066"></a>

**D066 — [`ArithmeticThetaBoundaryHodgeR0182.CurveFrame`](../Lean/BoundaryHodgeDefinitionsR0182.lean#L23)**

Used by **C, M** · `definition` · module `BoundaryHodgeDefinitionsR0182`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev CurveFrame :=
```

Next definitions: [D098](#d098), [D102](#d102), [D112](#d112).

<a id="d067"></a>

**D067 — [`ArithmeticThetaBoundaryHodgeR0182.Normalized`](../Lean/BoundaryHodgeDefinitionsR0182.lean#L30)**

Used by **C, M** · `definition` · module `BoundaryHodgeDefinitionsR0182`.

> The actual differential dx/(2y) on the fixed Tate cubic, normalized on its specified affine chart. The accepted global-frame provider supplies it.

Next definitions: [D066](#d066), [D070](#d070), [D073](#d073), [D074](#d074), [D076](#d076), [D077](#d077), [D078](#d078), [D098](#d098), [D102](#d102), [D112](#d112).

<a id="d068"></a>

**D068 — [`ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator`](../Lean/BoundaryHodgeDefinitionsR0182.lean#L41)**

Used by **C, M** · `definition` · module `BoundaryHodgeDefinitionsR0182`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def hodgeGenerator (δ : CurveFrame k L) :
```

Next definitions: [D066](#d066), [D090](#d090), [D097](#d097), [D098](#d098), [D101](#d101), [D102](#d102), [D112](#d112).

<a id="d069"></a>

**D069 — [`ArithmeticThetaCommonHalfHodgeR0185.along`](../Lean/CommonHalfHodgeDefinitionsR0185.lean#L114)**

Used by **C, M** · `definition` · module `CommonHalfHodgeDefinitionsR0185`.

> Canonical comparison over a specified commuting triangle.

No further counted custom definition is reached before the external-library boundary.

<a id="d070"></a>

**D070 — [`ArithmeticThetaCompactifiedDifferentialR0145.ChartRing`](../Lean/CompactifiedDifferentialDefinitionsR0145.lean#L44)**

Used by **C, M** · `definition` · module `CompactifiedDifferentialDefinitionsR0145`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev ChartRing (r : ℕ) :=
```

Next definitions: [D076](#d076).

<a id="d071"></a>

**D071 — [`ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.chartRingEquiv`](../Lean/GlobalNormalizedDifferentialR0145.lean#L348)**

Used by **C, M** · `definition` · module `GlobalNormalizedDifferentialR0145`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def chartRingEquiv : Γ(C, i ''ᵁ ⊤) ≃+* B :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d072"></a>

**D072 — [`ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zLeg`](../Lean/GlobalNormalizedDifferentialR0145.lean#L896)**

Used by **C, M** · `definition` · module `GlobalNormalizedDifferentialR0145`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev zLeg := chartInclusion k r ≫ E.inv
```

Next definitions: [D070](#d070), [D075](#d075), [D076](#d076), [D077](#d077).

<a id="d073"></a>

**D073 — [`ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zOpen`](../Lean/GlobalNormalizedDifferentialR0145.lean#L904)**

Used by **C, M** · `definition` · module `GlobalNormalizedDifferentialR0145`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev zOpen : C.Opens := zLeg k r E ''ᵁ ⊤
```

Next definitions: [D070](#d070), [D072](#d072), [D076](#d076), [D077](#d077).

<a id="d074"></a>

**D074 — [`ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential.zSection`](../Lean/GlobalNormalizedDifferentialR0145.lean#L946)**

Used by **C, M** · `definition` · module `GlobalNormalizedDifferentialR0145`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev zSection : ChartRing k r ≃+* Γ(C, zOpen k r E) := (chartRingEquiv (zLeg k r E)).symm
```

Next definitions: [D070](#d070), [D071](#d071), [D072](#d072), [D073](#d073), [D076](#d076), [D077](#d077).

<a id="d075"></a>

**D075 — [`ArithmeticThetaCompactifiedDifferentialR0145.chartInclusion`](../Lean/CompactifiedDifferentialDefinitionsR0145.lean#L47)**

Used by **C, M** · `definition` · module `CompactifiedDifferentialDefinitionsR0145`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def chartInclusion (r : ℕ) : Spec (CommRingCat.of (ChartRing k r)) ⟶ projectiveCurve k r :=
```

Next definitions: [D070](#d070), [D076](#d076), [D077](#d077).

<a id="d076"></a>

**D076 — [`ArithmeticThetaCompactifiedDifferentialR0145.curve`](../Lean/CompactifiedDifferentialDefinitionsR0145.lean#L30)**

Used by **C, M** · `definition` · module `CompactifiedDifferentialDefinitionsR0145`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def curve (r : ℕ) : WeierstrassCurve (LaurentSeries k) where
```

Next definitions: [D079](#d079).

<a id="d077"></a>

**D077 — [`ArithmeticThetaCompactifiedDifferentialR0145.projectiveCurve`](../Lean/CompactifiedDifferentialDefinitionsR0145.lean#L37)**

Used by **C, M** · `definition` · module `CompactifiedDifferentialDefinitionsR0145`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev projectiveCurve (r : ℕ) : Scheme.{u} :=
```

Next definitions: [D076](#d076).

<a id="d078"></a>

**D078 — [`ArithmeticThetaCompactifiedDifferentialR0145.relativeD`](../Lean/CompactifiedDifferentialDefinitionsR0145.lean#L102)**

Used by **C, M** · `definition` · module `CompactifiedDifferentialDefinitionsR0145`.

> Universal relative derivation for the particular structural ring map.

No further counted custom definition is reached before the external-library boundary.

<a id="d079"></a>

**D079 — [`ArithmeticThetaCompactifiedDifferentialR0145.root`](../Lean/CompactifiedDifferentialDefinitionsR0145.lean#L27)**

Used by **C, M** · `definition` · module `CompactifiedDifferentialDefinitionsR0145`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def root (r : ℕ) (j : Fin 3) : LaurentSeries k :=
```

Next definitions: [D080](#d080).

<a id="d080"></a>

**D080 — [`ArithmeticThetaCubicModelR0144.rootSeries`](../Lean/CubicModelDefinitionsR0144.lean#L28)**

Used by **C, M** · `definition` · module `CubicModelDefinitionsR0144`.

> The actual three marked coordinate values for Q=t^r and even r.

Next definitions: [D118](#d118).

<a id="d081"></a>

**D081 — [`ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalLocal`](../Lean/RelativeWeierstrassPresentationR0174.lean#L1622)**

Used by **C, M** · `definition` · module `RelativeWeierstrassPresentationR0174`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def conormalLocal (U : X.Opens) :
```

Next definitions: [D078](#d078).

<a id="d082"></a>

**D082 — [`ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalMap`](../Lean/RelativeWeierstrassPresentationR0174.lean#L1661)**

Used by **C, M** · `definition` · module `RelativeWeierstrassPresentationR0174`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def conormalMap : (Scheme.Modules.pullback e).obj e.ker.module ⟶
```

Next definitions: [D083](#d083).

<a id="d083"></a>

**D083 — [`ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.Conormal.conormalToPushforward`](../Lean/RelativeWeierstrassPresentationR0174.lean#L1636)**

Used by **C, M** · `definition` · module `RelativeWeierstrassPresentationR0174`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def conormalToPushforward :
```

Next definitions: [D081](#d081).

<a id="d084"></a>

**D084 — [`ArithmeticThetaOpenHodgeR0180.Test`](../Lean/OpenHodgeDescentDefinitionsR0180.lean#L27)**

Used by **C, M** · `structure` · module `OpenHodgeDescentDefinitionsR0180`.

> A genuine pointed Cartesian Weierstrass comparison, including the actual multiplication maps. No section or expansion equality is an input.

Next definitions: [D019](#d019), [D088](#d088), [D089](#d089), [D096](#d096), [D098](#d098), [D100](#d100), [D101](#d101), [D102](#d102).

<a id="d085"></a>

**D085 — [`ArithmeticThetaOpenHodgeR0180.comparison`](../Lean/OpenHodgeDescentDefinitionsR0180.lean#L59)**

Used by **C, M** · `definition` · module `OpenHodgeDescentDefinitionsR0180`.

> Reuse the accepted general pointed differential comparison.

Next definitions: [D019](#d019), [D084](#d084), [D086](#d086), [D088](#d088), [D089](#d089), [D090](#d090), [D092](#d092), [D096](#d096), [D098](#d098), [D100](#d100), [D101](#d101), [D102](#d102).

<a id="d086"></a>

**D086 — [`ArithmeticThetaOpenHodgeR0180.hodge`](../Lean/OpenHodgeDescentDefinitionsR0180.lean#L20)**

Used by **C, M** · `definition` · module `OpenHodgeDescentDefinitionsR0180`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev hodge {S : Type u} [CommRing S] (E : EllipticFamily S) :=
```

Next definitions: [D019](#d019), [D088](#d088), [D089](#d089).

<a id="d087"></a>

**D087 — [`ArithmeticThetaOpenHodgeR0180.scalar`](../Lean/OpenHodgeDescentDefinitionsR0180.lean#L163)**

Used by **C, M** · `definition` · module `OpenHodgeDescentDefinitionsR0180`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def scalar (S : Type u) [CommRing S] (v : S) : (Base S).presheaf.obj (Opposite.op ⊤) :=
```

Next definitions: [D089](#d089).

<a id="d088"></a>

**D088 — [`ArithmeticThetaOpenHodgeR0180.zero`](../Lean/OpenHodgeDescentDefinitionsR0180.lean#L18)**

Used by **C, M** · `definition` · module `OpenHodgeDescentDefinitionsR0180`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev zero {S : Type u} [CommRing S] (E : EllipticFamily S) : Base S ⟶ E.curve :=
```

Next definitions: [D019](#d019), [D089](#d089).

<a id="d089"></a>

**D089 — [`ArithmeticThetaRelativeDiscriminantR0171.Base`](../Lean/RelativeDiscriminantDefinitionsR0171.lean#L16)**

Used by **C, M** · `definition` · module `RelativeDiscriminantDefinitionsR0171`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
```

No further counted custom definition is reached before the external-library boundary.

<a id="d090"></a>

**D090 — [`ArithmeticThetaRelativeDiscriminantR0171.Hodge`](../Lean/RelativeDiscriminantDefinitionsR0171.lean#L18)**

Used by **C, M** · `definition` · module `RelativeDiscriminantDefinitionsR0171`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Hodge (R : Type u) [CommRing R] (W : WeierstrassCurve R) :=
```

Next definitions: [D098](#d098), [D101](#d101), [D102](#d102).

<a id="d091"></a>

**D091 — [`ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.differentialMap`](../Lean/RelativeHodgePowerBaseChangeR0171.lean#L180)**

Used by **C, M** · `definition` · module `RelativeHodgePowerBaseChangeR0171`.

> The morphism induced by the actual square on relative differential sheaves.

No further counted custom definition is reached before the external-library boundary.

<a id="d092"></a>

**D092 — [`ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pointedDifferentialIso`](../Lean/RelativeHodgePowerBaseChangeR0171.lean#L341)**

Used by **C, M** · `definition` · module `RelativeHodgePowerBaseChangeR0171`.

> Pullback of the actual Cartesian differential comparison to the pointed sections.

Next definitions: [D091](#d091), [D094](#d094).

<a id="d093"></a>

**D093 — [`ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.pullbackEqIso`](../Lean/RelativeHodgePowerBaseChangeR0171.lean#L284)**

Used by **C, M** · `definition` · module `RelativeHodgePowerBaseChangeR0171`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def pullbackEqIso {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
```

No further counted custom definition is reached before the external-library boundary.

<a id="d094"></a>

**D094 — [`ArithmeticThetaRelativeDiscriminantR0171.HodgeBaseChange.squarePullbackIso`](../Lean/RelativeHodgePowerBaseChangeR0171.lean#L304)**

Used by **C, M** · `definition` · module `RelativeHodgePowerBaseChangeR0171`.

> The comparison for pullbacks along the two sides of a commutative square.

Next definitions: [D093](#d093).

<a id="d095"></a>

**D095 — [`ArithmeticThetaRelativeDiscriminantR0171.IsFrame`](../Lean/RelativeDiscriminantDefinitionsR0171.lean#L28)**

Used by **C, M** · `definition` · module `RelativeDiscriminantDefinitionsR0171`.

> A section generates the actual sheaf on every subopen, including empty opens.

Next definitions: [D097](#d097).

<a id="d096"></a>

**D096 — [`ArithmeticThetaRelativeDiscriminantR0171.baseMap`](../Lean/RelativeDiscriminantDefinitionsR0171.lean#L73)**

Used by **C, M** · `definition` · module `RelativeDiscriminantDefinitionsR0171`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def baseMap (ι : R →+* S) : Base S ⟶ Base R := Spec.map (CommRingCat.ofHom ι)
```

Next definitions: [D089](#d089).

<a id="d097"></a>

**D097 — [`ArithmeticThetaRelativeDiscriminantR0171.res`](../Lean/RelativeDiscriminantDefinitionsR0171.lean#L24)**

Used by **C, M** · `definition` · module `RelativeDiscriminantDefinitionsR0171`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def res {X : Scheme.{u}} (F : X.Modules) {U V : X.Opens} (h : V ≤ U)
```

No further counted custom definition is reached before the external-library boundary.

<a id="d098"></a>

**D098 — [`ArithmeticThetaRelativeKatoR0169.Curve`](../Lean/RelativeKatoDefinitionsR0169.lean#L15)**

Used by **C, M** · `definition` · module `RelativeKatoDefinitionsR0169`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Curve (W : WeierstrassCurve R) : Scheme.{u} :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d099"></a>

**D099 — [`ArithmeticThetaRelativeKatoR0169.IsOriginLaw`](../Lean/RelativeKatoDefinitionsR0169.lean#L27)**

Used by **C, M** · `definition` · module `RelativeKatoDefinitionsR0169`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def IsOriginLaw (W : WeierstrassCurve R) (G : Law R W) : Prop :=
```

Next definitions: [D098](#d098), [D100](#d100), [D101](#d101), [D102](#d102).

<a id="d100"></a>

**D100 — [`ArithmeticThetaRelativeKatoR0169.Law`](../Lean/RelativeKatoDefinitionsR0169.lean#L24)**

Used by **C, M** · `definition` · module `RelativeKatoDefinitionsR0169`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Law (W : WeierstrassCurve R) :=
```

Next definitions: [D098](#d098), [D102](#d102).

<a id="d101"></a>

**D101 — [`ArithmeticThetaRelativeKatoR0169.origin`](../Lean/RelativeKatoDefinitionsR0169.lean#L21)**

Used by **C, M** · `definition` · module `RelativeKatoDefinitionsR0169`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def origin (W : WeierstrassCurve R) : Spec (CommRingCat.of R) ⟶ Curve R W :=
```

Next definitions: [D098](#d098).

<a id="d102"></a>

**D102 — [`ArithmeticThetaRelativeKatoR0169.structureMap`](../Lean/RelativeKatoDefinitionsR0169.lean#L18)**

Used by **C, M** · `definition` · module `RelativeKatoDefinitionsR0169`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def structureMap (W : WeierstrassCurve R) : Curve R W ⟶ Spec (CommRingCat.of R) :=
```

Next definitions: [D098](#d098).

<a id="d103"></a>

**D103 — [`ArithmeticThetaSchemeHodgeR0205.Cotangent`](../Lean/SchemeHodgeDefinitionsR0205.lean#L15)**

Used by **C, M** · `definition` · module `SchemeHodgeDefinitionsR0205`.

> The actual conormal I/I² at the identity, expressed as e*I.

Next definitions: [D022](#d022), [D023](#d023).

<a id="d104"></a>

**D104 — [`ArithmeticThetaSchemeHodgeR0205.CotangentCompatible`](../Lean/SchemeHodgeDefinitionsR0205.lean#L37)**

Used by **C, M** · `definition` · module `SchemeHodgeDefinitionsR0205`.

> Canonical cotangent comparison: the witnessing ideal isomorphism preserves its actual ideal inclusion; no arbitrary line is chosen.

Next definitions: [D022](#d022), [D023](#d023), [D103](#d103), [D105](#d105), [D107](#d107).

<a id="d105"></a>

**D105 — [`ArithmeticThetaSchemeHodgeR0205.IdealCompatible`](../Lean/SchemeHodgeDefinitionsR0205.lean#L19)**

Used by **C, M** · `definition` · module `SchemeHodgeDefinitionsR0205`.

> Compatibility with the inclusion of the actual identity ideal in O.

Next definitions: [D022](#d022), [D023](#d023), [D134](#d134).

<a id="d106"></a>

**D106 — [`ArithmeticThetaSchemeHodgeR0205.affineDifferential`](../Lean/SchemeHodgeDefinitionsR0205.lean#L45)**

Used by **C, M** · `definition` · module `SchemeHodgeDefinitionsR0205`.

> On an affine base use the accepted canonical derivative, including its normalization on every ideal section.

Next definitions: [D021](#d021), [D022](#d022), [D023](#d023), [D082](#d082), [D103](#d103).

<a id="d107"></a>

**D107 — [`ArithmeticThetaSchemeHodgeR0205.cotangentComparison`](../Lean/SchemeHodgeDefinitionsR0205.lean#L27)**

Used by **C, M** · `definition` · module `SchemeHodgeDefinitionsR0205`.

> The comparison is induced by the actual ideal comparison and pointed square.

Next definitions: [D022](#d022), [D023](#d023), [D094](#d094), [D103](#d103).

<a id="d108"></a>

**D108 — [`ArithmeticThetaSimultaneousUnaryR0187.squareOnDisk`](../Lean/SimultaneousUnaryRootsDefinitionsR0187.lean#L63)**

Used by **C, M** · `definition` · module `SimultaneousUnaryRootsDefinitionsR0187`.

> Pull back the specific square map and the same commuting triangle.

Next definitions: [D069](#d069), [D110](#d110), [D132](#d132), [D145](#d145).

<a id="d109"></a>

**D109 — [`ArithmeticThetaSimultaneousUnaryR0187.unarySeries`](../Lean/SimultaneousUnaryRootsDefinitionsR0187.lean#L25)**

Used by **C** · `definition` · module `SimultaneousUnaryRootsDefinitionsR0187`.

> The actual integral unary series, before the accepted Laurent inclusion.

Next definitions: [D168](#d168).

<a id="d110"></a>

**D110 — [`ArithmeticThetaTateCuspsR0181.Disk`](../Lean/TateCuspDefinitionsR0181.lean#L22)**

Used by **C, M** · `definition` · module `TateCuspDefinitionsR0181`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Disk := Base (PowerSeries k)
```

Next definitions: [D089](#d089).

<a id="d111"></a>

**D111 — [`ArithmeticThetaTateCuspsR0181.Puncture`](../Lean/TateCuspDefinitionsR0181.lean#L23)**

Used by **C, M** · `definition` · module `TateCuspDefinitionsR0181`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Puncture := Base (LaurentSeries k)
```

Next definitions: [D089](#d089).

<a id="d112"></a>

**D112 — [`ArithmeticThetaTateCuspsR0181.TateCurve`](../Lean/TateCuspDefinitionsR0181.lean#L21)**

Used by **C, M** · `definition` · module `TateCuspDefinitionsR0181`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev TateCurve := ArithmeticThetaCompactifiedDifferentialR0145.curve k L
```

Next definitions: [D076](#d076).

<a id="d113"></a>

**D113 — [`ArithmeticThetaTateCuspsR0181.TateLevel`](../Lean/TateCuspDefinitionsR0181.lean#L31)**

Used by **C, M** · `structure` · module `TateCuspDefinitionsR0181`.

> Full marking on the specific split cubic for period q=t^L.

Next definitions: [D018](#d018), [D099](#d099), [D100](#d100), [D111](#d111), [D112](#d112).

<a id="d114"></a>

**D114 — [`ArithmeticThetaTateCuspsR0181.diskStructure`](../Lean/TateCuspDefinitionsR0181.lean#L26)**

Used by **C, M** · `definition` · module `TateCuspDefinitionsR0181`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def diskStructure : Disk k ⟶ Base k :=
```

Next definitions: [D089](#d089), [D110](#d110).

<a id="d115"></a>

**D115 — [`ArithmeticThetaTateCuspsR0181.genericInclusion`](../Lean/TateCuspDefinitionsR0181.lean#L24)**

Used by **C, M** · `definition` · module `TateCuspDefinitionsR0181`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def genericInclusion : Puncture k ⟶ Disk k :=
```

Next definitions: [D110](#d110), [D111](#d111).

<a id="d116"></a>

**D116 — [`ArithmeticThetaTateSeries.monomial`](../Lean/TateSeriesDefinitions.lean#L15)**

Used by **C, M** · `definition` · module `TateSeriesDefinitions`.

> a*t^n in the actual power series ring.

No further counted custom definition is reached before the external-library boundary.

<a id="d117"></a>

**D117 — [`ArithmeticThetaTateSeries.partialX`](../Lean/TateSeriesDefinitions.lean#L25)**

Used by **C, M** · `definition` · module `TateSeriesDefinitions`.

> r=0 plus the two tails for 1≤r≤N, including the normalization correction.

Next definitions: [D116](#d116), [D119](#d119).

<a id="d118"></a>

**D118 — [`ArithmeticThetaTateSeries.tateX`](../Lean/TateSeriesDefinitions.lean#L42)**

Used by **C, M** · `definition` · module `TateSeriesDefinitions`.

> Stable coefficient candidates; stabilization is a new theorem obligation.

Next definitions: [D117](#d117).

<a id="d119"></a>

**D119 — [`ArithmeticThetaTateSeries.xTerm`](../Lean/TateSeriesDefinitions.lean#L19)**

Used by **C, M** · `definition` · module `TateSeriesDefinitions`.

> v/(1-v)^2, using the formal power-series inverse.

No further counted custom definition is reached before the external-library boundary.


<a id="sheaves"></a>

## Sheaves, tensor powers and section operations

<a id="d120"></a>

**D120 — [`ArithmeticThetaCoverComparison.tensorPowerMap`](../Lean/CoverComparisonDefinitions.lean#L12)**

Used by **C, M** · `definition` · module `CoverComparisonDefinitions`.

> The actual functorial morphism on the established sheaf tensor powers.

Next definitions: [D121](#d121), [D136](#d136), [D145](#d145).

<a id="d121"></a>

**D121 — [`ArithmeticThetaCoverComparison.tensorPowerMap.match_1`](../Lean/CoverComparisonDefinitions.lean#L12)**

Used by **C, M** · `definition` · module `CoverComparisonDefinitions`.

Lean-generated pattern-matching helper for `ArithmeticThetaCoverComparison.tensorPowerMap`. It has no
separate handwritten declaration or docstring; the source link opens
its generating definition. It is included in the technical count.

No further counted custom definition is reached before the external-library boundary.

<a id="d122"></a>

**D122 — [`ArithmeticThetaNormalizedSections.pullbackPowerSection`](../Lean/NormalizedSectionDefinitions.lean#L44)**

Used by **C, M** · `definition` · module `NormalizedSectionDefinitions`.

> Pullback of a power section via the accepted genuine tensor comparison.

Next definitions: [D130](#d130), [D132](#d132), [D145](#d145).

<a id="d123"></a>

**D123 — [`ArithmeticThetaPullback.instMonoidalCategoryPresheafOfModules_pullbackTensor`](../Lean/PullbackTensor.lean#L13)**

Used by **C, M** · `definition` · module `PullbackTensor`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d124"></a>

**D124 — [`ArithmeticThetaPullback.presheafAdjunction`](../Lean/PullbackTensor.lean#L485)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> The actual presheaf pullback/pushforward adjunction, with its scheme types exposed.

Next definitions: [D125](#d125), [D128](#d128).

<a id="d125"></a>

**D125 — [`ArithmeticThetaPullback.presheafPullback`](../Lean/PullbackTensor.lean#L475)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> Presheaf pullback with scheme-specific source and target types exposed.

No further counted custom definition is reached before the external-library boundary.

<a id="d126"></a>

**D126 — [`ArithmeticThetaPullback.presheafPullbackTensorIso`](../Lean/PullbackTensor.lean#L792)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> The canonical tensor comparison for actual module presheaves.

Next definitions: [D123](#d123), [D125](#d125), [D127](#d127).

<a id="d127"></a>

**D127 — [`ArithmeticThetaPullback.presheafPullbackTensorMap`](../Lean/PullbackTensor.lean#L556)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> The tensor comparison of presheaf pullback, adjoint to the pure-section pairing.

Next definitions: [D123](#d123), [D124](#d124), [D125](#d125), [D128](#d128), [D129](#d129).

<a id="d128"></a>

**D128 — [`ArithmeticThetaPullback.presheafPushforward`](../Lean/PullbackTensor.lean#L480)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> Presheaf pushforward with scheme-specific source and target types exposed.

No further counted custom definition is reached before the external-library boundary.

<a id="d129"></a>

**D129 — [`ArithmeticThetaPullback.presheafPushforwardTensorMap`](../Lean/PullbackTensor.lean#L529)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> The ordinary sectionwise tensor pairing for pushforward of module presheaves.

Next definitions: [D123](#d123), [D128](#d128).

<a id="d130"></a>

**D130 — [`ArithmeticThetaPullback.pullbackGlobalSection`](../Lean/PullbackTensorDefinitions.lean#L13)**

Used by **C, M** · `definition` · module `PullbackTensorDefinitions`.

> The global section map induced by the actual pullback/pushforward adjunction. It is only an ordinary definition; the compatibility laws are target obligations.

No further counted custom definition is reached before the external-library boundary.

<a id="d131"></a>

**D131 — [`ArithmeticThetaPullback.pullback_sheafTensor_iso`](../Lean/PullbackTensor.lean#L801)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> Canonical pullback comparison for genuine sheaf tensors. The construction uses commutation of pullback with sheafification, the colimit-preserving presheaf comparison, and descent of tensor pairings through sheafification.

Next definitions: [D123](#d123), [D125](#d125), [D126](#d126), [D135](#d135), [D137](#d137), [D139](#d139), [D140](#d140).

<a id="d132"></a>

**D132 — [`ArithmeticThetaPullback.pullback_tensorPower_iso`](../Lean/PullbackTensor.lean#L814)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> Recursive comparison for every genuine tensor power, including the structure sheaf at exponent zero.

Next definitions: [D131](#d131), [D133](#d133), [D134](#d134), [D135](#d135), [D139](#d139), [D145](#d145).

<a id="d133"></a>

**D133 — [`ArithmeticThetaPullback.pullback_tensorPower_iso.match_1`](../Lean/PullbackTensor.lean#L814)**

Used by **C, M** · `definition` · module `PullbackTensor`.

Lean-generated pattern-matching helper for `ArithmeticThetaPullback.pullback_tensorPower_iso`. It has no
separate handwritten declaration or docstring; the source link opens
its generating definition. It is included in the technical count.

No further counted custom definition is reached before the external-library boundary.

<a id="d134"></a>

**D134 — [`ArithmeticThetaPullback.pullback_unit_iso`](../Lean/PullbackUnit.lean#L13)**

Used by **C, M** · `definition` · module `PullbackUnit`.

> The canonical structure-sheaf comparison for the actual pullback functor. Its forward map is adjoint to the structure-sheaf morphism of `p`.

No further counted custom definition is reached before the external-library boundary.

<a id="d135"></a>

**D135 — [`ArithmeticThetaPullback.sheafTensorCongr`](../Lean/PullbackTensor.lean#L22)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> The genuine sheaf tensor transports isomorphisms in both factors.

Next definitions: [D123](#d123), [D139](#d139), [D140](#d140).

<a id="d136"></a>

**D136 — [`ArithmeticThetaPullback.sheafTensorMap`](../Lean/PullbackTensor.lean#L17)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> Functoriality of the genuine sheaf tensor, induced by sheafification.

Next definitions: [D138](#d138), [D139](#d139), [D140](#d140).

<a id="d137"></a>

**D137 — [`ArithmeticThetaPullback.sheafificationTensorIso`](../Lean/PullbackTensor.lean#L409)**

Used by **C, M** · `definition` · module `PullbackTensor`.

> Sheafification commutes with the genuine sheaf tensor. Both unit maps are inverted using descent into arbitrary target module sheaves.

Next definitions: [D123](#d123), [D139](#d139), [D140](#d140).

<a id="d138"></a>

**D138 — [`ArithmeticThetaSheafTensor.instMonoidalCategoryPresheafOfModules_actualSheafTensor`](../Lean/ActualSheafTensor.lean#L23)**

Used by **C, M** · `definition` · module `ActualSheafTensor`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
local instance : MonoidalCategory X.PresheafOfModules :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d139"></a>

**D139 — [`ArithmeticThetaSheafTensor.sheafTensor`](../Lean/ActualSheafTensor.lean#L29)**

Used by **C, M** · `definition` · module `ActualSheafTensor`.

> The actual sheafification of the actual categorical tensor of module presheaves.

Next definitions: [D140](#d140).

<a id="d140"></a>

**D140 — [`ArithmeticThetaSheafTensor.tensorPresheaf`](../Lean/ActualSheafTensor.lean#L26)**

Used by **C, M** · `definition` · module `ActualSheafTensor`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def tensorPresheaf (H K : X.Modules) : X.PresheafOfModules := H.val ⊗ K.val
```

Next definitions: [D138](#d138).

<a id="d141"></a>

**D141 — [`ArithmeticThetaSheafTensor.tensorSection`](../Lean/ActualSheafTensor.lean#L58)**

Used by **C, M** · `definition` · module `ActualSheafTensor`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def tensorSection (H K : X.Modules) (U : X.Opens) (s : Γ(H, U)) (t : Γ(K, U)) :
```

Next definitions: [D139](#d139), [D140](#d140), [D142](#d142).

<a id="d142"></a>

**D142 — [`ArithmeticThetaSheafTensor.tensorUnitMap`](../Lean/ActualSheafTensor.lean#L32)**

Used by **C, M** · `definition` · module `ActualSheafTensor`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def tensorUnitMap (H K : X.Modules) : tensorPresheaf X H K ⟶ (sheafTensor X H K).val :=
```

Next definitions: [D138](#d138), [D139](#d139), [D140](#d140).

<a id="d143"></a>

**D143 — [`ArithmeticThetaSquareLinesR0192.SquareLine`](../Lean/SquareLineComparisonDefinitionsR0192.lean#L22)**

Used by **C, M** · `structure` · module `SquareLineComparisonDefinitionsR0192`.

> A genuine invertible sheaf with its specified square isomorphism.

Next definitions: [D145](#d145).

<a id="d144"></a>

**D144 — [`ArithmeticThetaSquareLinesR0192.squarePull`](../Lean/SquareLineComparisonDefinitionsR0192.lean#L28)**

Used by **C, M** · `definition` · module `SquareLineComparisonDefinitionsR0192`.

> Pullback retains the supplied square map and the canonical tensor comparison.

Next definitions: [D132](#d132), [D143](#d143), [D145](#d145).

<a id="d145"></a>

**D145 — [`ArithmeticThetaTensorPower.tensorPower`](../Lean/TensorPowerDefinitions.lean#L14)**

Used by **C, M** · `definition` · module `TensorPowerDefinitions`.

> Iterated genuine sheaf tensor, starting with the structure sheaf. The exponent-one identification is the accepted genuine left unit isomorphism.

Next definitions: [D139](#d139), [D146](#d146).

<a id="d146"></a>

**D146 — [`ArithmeticThetaTensorPower.tensorPower.match_1`](../Lean/TensorPowerDefinitions.lean#L14)**

Used by **C, M** · `definition` · module `TensorPowerDefinitions`.

Lean-generated pattern-matching helper for `ArithmeticThetaTensorPower.tensorPower`. It has no
separate handwritten declaration or docstring; the source link opens
its generating definition. It is included in the technical count.

No further counted custom definition is reached before the external-library boundary.

<a id="d147"></a>

**D147 — [`ArithmeticThetaTensorPower.tensorPowerSection`](../Lean/TensorPowerDefinitions.lean#L31)**

Used by **C, M** · `definition` · module `TensorPowerDefinitions`.

> Actual tensor power of a section; it does not refer to a chosen local frame.

Next definitions: [D141](#d141), [D145](#d145), [D148](#d148).

<a id="d148"></a>

**D148 — [`ArithmeticThetaTensorPower.tensorPowerSection.match_1`](../Lean/TensorPowerDefinitions.lean#L31)**

Used by **C, M** · `definition` · module `TensorPowerDefinitions`.

Lean-generated pattern-matching helper for `ArithmeticThetaTensorPower.tensorPowerSection`. It has no
separate handwritten declaration or docstring; the source link opens
its generating definition. It is included in the technical count.

No further counted custom definition is reached before the external-library boundary.


<a id="series"></a>

## Lattice theta series and image statements

<a id="d149"></a>

**D149 — [`ArithmeticThetaArithmeticFieldR0231.integralTheta`](../Lean/ArithmeticFieldDefinitionsR0231.lean#L24)**

Used by **C, M** · `definition` · module `ArithmeticFieldDefinitionsR0231`.

> The integer shell-count series, before any coefficient-field embedding.

No further counted custom definition is reached before the external-library boundary.

<a id="d150"></a>

**D150 — [`ArithmeticThetaArithmeticFieldR0231.theta`](../Lean/ArithmeticFieldDefinitionsR0231.lean#L29)**

Used by **C, M** · `definition` · module `ArithmeticFieldDefinitionsR0231`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def theta (k : Type) [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries k :=
```

Next definitions: [D149](#d149).

<a id="d151"></a>

**D151 — [`ArithmeticThetaCompactUnaryR0183.exponent`](../Lean/CompactUnaryDefinitionsR0183.lean#L17)**

Used by **C** · `definition` · module `CompactUnaryDefinitionsR0183`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev exponent (N : ℕ) : ℕ := (1+12*N)^2-1
```

No further counted custom definition is reached before the external-library boundary.

<a id="d152"></a>

**D152 — [`ArithmeticThetaCompactUnaryR0183.level`](../Lean/CompactUnaryDefinitionsR0183.lean#L16)**

Used by **C, M** · `definition` · module `CompactUnaryDefinitionsR0183`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev level (N : ℕ) : ℕ := 24*N^2
```

No further counted custom definition is reached before the external-library boundary.

<a id="d153"></a>

**D153 — [`ArithmeticThetaFieldImageR0233.SectionImage`](../Lean/FieldImageDefinitionsR0233.lean#L63)**

Used by **C, M** · `definition` · module `FieldImageDefinitionsR0233`.

> Exact relations, independence, spanning and rational coordinates of actual sections. No freely chosen k-module action is used on their carrier.

Next definitions: [D154](#d154), [D155](#d155), [D156](#d156), [D157](#d157), [D158](#d158), [D163](#d163), [D169](#d169), [D190](#d190).

<a id="d154"></a>

**D154 — [`ArithmeticThetaFieldImageR0233.Sections`](../Lean/FieldImageDefinitionsR0233.lean#L49)**

Used by **C, M** · `definition` · module `FieldImageDefinitionsR0233`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Sections {X : Scheme.{0}} (J : X.Modules) := J.presheaf.obj (Opposite.op ⊤)
```

No further counted custom definition is reached before the external-library boundary.

<a id="d155"></a>

**D155 — [`ArithmeticThetaFieldImageR0233.combination`](../Lean/FieldImageDefinitionsR0233.lean#L51)**

Used by **C, M** · `definition` · module `FieldImageDefinitionsR0233`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def combination (k : Type) [Field k] {h : ℕ} {X : Scheme.{0}}
```

Next definitions: [D154](#d154), [D164](#d164).

<a id="d156"></a>

**D156 — [`ArithmeticThetaFieldImageR0233.pivotCombination`](../Lean/FieldImageDefinitionsR0233.lean#L56)**

Used by **C, M** · `definition` · module `FieldImageDefinitionsR0233`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def pivotCombination (k : Type) [Field k] {n h : ℕ} (A : Matrices n h) (B : ℕ)
```

Next definitions: [D154](#d154), [D157](#d157), [D163](#d163), [D164](#d164), [D170](#d170).

<a id="d157"></a>

**D157 — [`ArithmeticThetaFieldImageR0233.pivotCount`](../Lean/FieldImageDefinitionsR0233.lean#L16)**

Used by **C, M** · `definition` · module `FieldImageDefinitionsR0233`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev pivotCount {n h : ℕ} (A : Matrices n h) (B : ℕ) :=
```

Next definitions: [D163](#d163), [D169](#d169), [D189](#d189), [D199](#d199).

<a id="d158"></a>

**D158 — [`ArithmeticThetaFieldImageR0233.seriesCombination`](../Lean/FieldImageDefinitionsR0233.lean#L19)**

Used by **C, M** · `definition` · module `FieldImageDefinitionsR0233`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def seriesCombination (k : Type) [Field k] {n h : ℕ}
```

Next definitions: [D150](#d150), [D163](#d163).

<a id="d159"></a>

**D159 — [`ArithmeticThetaLatticeSectionsR0188.Cosets`](../Lean/LatticeGlobalSectionsDefinitionsR0188.lean#L23)**

Used by **C** · `definition` · module `LatticeGlobalSectionsDefinitionsR0188`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Cosets {n h : ℕ} (A : Matrices n h) (i : Fin h) :=
```

Next definitions: [D163](#d163), [D209](#d209).

<a id="d160"></a>

**D160 — [`ArithmeticThetaLatticeSectionsR0188.FormalIdentity`](../Lean/LatticeGlobalSectionsDefinitionsR0188.lean#L54)**

Used by **C** · `definition` · module `LatticeGlobalSectionsDefinitionsR0188`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def FormalIdentity {n h : ℕ} (A : Matrices n h) (U : Indexing A) : Prop :=
```

Next definitions: [D109](#d109), [D159](#d159), [D162](#d162), [D163](#d163), [D166](#d166), [D167](#d167), [D209](#d209).

<a id="d161"></a>

**D161 — [`ArithmeticThetaLatticeSectionsR0188.Indexed`](../Lean/LatticeGlobalSectionsDefinitionsR0188.lean#L40)**

Used by **C** · `definition` · module `LatticeGlobalSectionsDefinitionsR0188`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def Indexed {n h : ℕ} (A : Matrices n h) (U : Indexing A) : Prop :=
```

Next definitions: [D159](#d159), [D162](#d162), [D163](#d163), [D165](#d165), [D209](#d209), [D210](#d210), [D217](#d217), [D222](#d222).

<a id="d162"></a>

**D162 — [`ArithmeticThetaLatticeSectionsR0188.Indexing`](../Lean/LatticeGlobalSectionsDefinitionsR0188.lean#L33)**

Used by **C** · `structure` · module `LatticeGlobalSectionsDefinitionsR0188`.

> Enumerate the distinct pairs actually used by the chosen preimage cosets.

Next definitions: [D159](#d159), [D163](#d163), [D209](#d209), [D210](#d210), [D222](#d222).

<a id="d163"></a>

**D163 — [`ArithmeticThetaLatticeSectionsR0188.Matrices`](../Lean/LatticeGlobalSectionsDefinitionsR0188.lean#L22)**

Used by **C, M** · `definition` · module `LatticeGlobalSectionsDefinitionsR0188`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ
```

No further counted custom definition is reached before the external-library boundary.

<a id="d164"></a>

**D164 — [`ArithmeticThetaLatticeSectionsR0188.baseScalar`](../Lean/LatticeGlobalSectionsDefinitionsR0188.lean#L92)**

Used by **C, M** · `definition` · module `LatticeGlobalSectionsDefinitionsR0188`.

> Scalars on the actual curve use its displayed structure morphism.

Next definitions: [D087](#d087).

<a id="d165"></a>

**D165 — [`ArithmeticThetaLatticeSectionsR0188.centered`](../Lean/LatticeGlobalSectionsDefinitionsR0188.lean#L29)**

Used by **C** · `definition` · module `LatticeGlobalSectionsDefinitionsR0188`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def centered (m : ℕ) (a : Fin m) : ℤ :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d166"></a>

**D166 — [`ArithmeticThetaLatticeSectionsR0188.commonN`](../Lean/LatticeGlobalSectionsDefinitionsR0188.lean#L26)**

Used by **C, M** · `definition` · module `LatticeGlobalSectionsDefinitionsR0188`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def commonN {n h : ℕ} (A : Matrices n h) : ℕ :=
```

Next definitions: [D163](#d163), [D210](#d210).

<a id="d167"></a>

**D167 — [`ArithmeticThetaLatticeSectionsR0188.expanded`](../Lean/LatticeGlobalSectionsDefinitionsR0188.lean#L51)**

Used by **C** · `definition` · module `LatticeGlobalSectionsDefinitionsR0188`.

> Literal q=t^(24*N^2) substitution; no chosen series functional.

Next definitions: [D152](#d152), [D163](#d163), [D166](#d166), [D172](#d172).

<a id="d168"></a>

**D168 — [`ArithmeticThetaUnaryProduct.clearedUnaryTheta`](../Lean/UnaryThetaProduct.lean#L422)**

Used by **C** · `definition` · module `UnaryThetaProduct`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
noncomputable def clearedUnaryTheta (m : ℕ) (ν : ℤ) : PowerSeries ℤ :=
```

No further counted custom definition is reached before the external-library boundary.


<a id="arithmetic"></a>

## Arithmetic inputs, cutoffs and elimination

<a id="d169"></a>

**D169 — [`ArithmeticThetaComputed.coefficientMatrix`](../Lean/IntegrationDefinitions.lean#L15)**

Used by **C, M** · `definition` · module `IntegrationDefinitions`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def coefficientMatrix {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ)
```

Next definitions: [D203](#d203).

<a id="d170"></a>

**D170 — [`ArithmeticThetaComputed.selectedIndex`](../Lean/IntegrationDefinitions.lean#L26)**

Used by **C, M** · `definition` · module `IntegrationDefinitions`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def selectedIndex {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
```

Next definitions: [D169](#d169), [D189](#d189), [D199](#d199).

<a id="d171"></a>

**D171 — [`ArithmeticThetaComputed.theta`](../Lean/IntegrationDefinitions.lean#L10)**

Used by **C** · `definition` · module `IntegrationDefinitions`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d172"></a>

**D172 — [`ArithmeticThetaComputed.thetaMap`](../Lean/IntegrationDefinitions.lean#L19)**

Used by **C** · `definition` · module `IntegrationDefinitions`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
noncomputable def thetaMap {n h : ℕ} (A : Fin h → Matrix (Fin n) (Fin n) ℤ) :
```

Next definitions: [D171](#d171).

<a id="d173"></a>

**D173 — [`ArithmeticThetaComputed.validGram`](../Lean/IntegrationDefinitions.lean#L6)**

Used by **C, M** · `definition` · module `IntegrationDefinitions`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d174"></a>

**D174 — [`ArithmeticThetaConservativeKernelR0189.CutoffSpecification`](../Lean/ConservativeMatrixKernelR0189.lean#L90)**

Used by **C** · `definition` · module `ConservativeMatrixKernelR0189`.

> The conservative bound, including its rank-zero case and exact rational value. `Indexing`, `Indexed` and `FormalIdentity` retain the actual unary factorization and its complete formal-series identity.

Next definitions: [D151](#d151), [D152](#d152), [D160](#d160), [D161](#d161), [D162](#d162), [D163](#d163), [D166](#d166), [D176](#d176), [D208](#d208).

<a id="d175"></a>

**D175 — [`ArithmeticThetaConservativeKernelR0189.PrefixDeterminesKernel`](../Lean/ConservativeMatrixKernelR0189.lean#L83)**

Used by **C** · `definition` · module `ConservativeMatrixKernelR0189`.

> The coefficient prefix through `B` detects every full-series relation.

Next definitions: [D163](#d163), [D169](#d169), [D172](#d172).

<a id="d176"></a>

**D176 — [`ArithmeticThetaConservativeKernelR0189.cutoff`](../Lean/ConservativeKernelDefinitionsR0189.lean#L25)**

Used by **C** · `definition` · module `ConservativeKernelDefinitionsR0189`.

> Exact integer realization of n*K^s*I(L)/48. The final theorem must prove its equality to the displayed rational source expression.

Next definitions: [D151](#d151), [D152](#d152), [D162](#d162), [D163](#d163), [D166](#d166).

<a id="d177"></a>

**D177 — [`ArithmeticThetaCyclotomicModularityR0239.CoefficientField`](../Lean/CyclotomicMatrixModularityR0239.lean#L21)**

Used by **C, M** · `definition` · module `CyclotomicMatrixModularityR0239`.

> The concrete number field `ℚ(ζ_L)`, with `L = coefficientLevel A`. This abbreviation retains the prescribed field; it does not choose an arbitrary field or discard the dependence on the lattice family.

Next definitions: [D163](#d163), [D178](#d178).

<a id="d178"></a>

**D178 — [`ArithmeticThetaCyclotomicModularityR0239.coefficientLevel`](../Lean/CyclotomicMatrixModularityR0239.lean#L15)**

Used by **C, M** · `definition` · module `CyclotomicMatrixModularityR0239`.

> Prescribed level obtained from the common unary denominator of the family.

Next definitions: [D152](#d152), [D163](#d163), [D166](#d166).

<a id="d179"></a>

**D179 — [`ArithmeticThetaDegreeAssembly.CertifiedImageData`](../Lean/EarlyCertificateAssembly.lean#L72)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> Full kernel basis, full image basis and unique rational reconstruction. This is an abbreviation of three explicit conclusions, with no added assumption.

Next definitions: [D180](#d180), [D181](#d181), [D182](#d182).

<a id="d180"></a>

**D180 — [`ArithmeticThetaDegreeAssembly.ImageBasisCorrect`](../Lean/EarlyCertificateAssembly.lean#L57)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> The selected complete theta series form a basis of the theta image.

Next definitions: [D172](#d172), [D183](#d183), [D185](#d185).

<a id="d181"></a>

**D181 — [`ArithmeticThetaDegreeAssembly.ReconstructionCorrect`](../Lean/EarlyCertificateAssembly.lean#L63)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> Every input series has the computed coordinates, uniquely over `ℚ`.

Next definitions: [D171](#d171), [D184](#d184), [D185](#d185), [D186](#d186).

<a id="d182"></a>

**D182 — [`ArithmeticThetaDegreeAssembly.RelationBasisCorrect`](../Lean/EarlyCertificateAssembly.lean#L51)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> The computed nullspace vectors form a basis of all complex theta relations.

Next definitions: [D172](#d172), [D187](#d187), [D188](#d188).

<a id="d183"></a>

**D183 — [`ArithmeticThetaDegreeAssembly.imageBasis`](../Lean/EarlyCertificateAssembly.lean#L33)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> The original complete theta series selected by the pivot columns.

Next definitions: [D170](#d170), [D171](#d171), [D185](#d185).

<a id="d184"></a>

**D184 — [`ArithmeticThetaDegreeAssembly.imageCombination`](../Lean/EarlyCertificateAssembly.lean#L45)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> A rational linear combination of the selected complete theta series.

Next definitions: [D183](#d183), [D185](#d185).

<a id="d185"></a>

**D185 — [`ArithmeticThetaDegreeAssembly.imageDimension`](../Lean/EarlyCertificateAssembly.lean#L23)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> Number of selected theta series (the number of pivot columns).

Next definitions: [D169](#d169), [D189](#d189), [D199](#d199).

<a id="d186"></a>

**D186 — [`ArithmeticThetaDegreeAssembly.reconstructionCoordinates`](../Lean/EarlyCertificateAssembly.lean#L39)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> Rational reconstruction coordinates supplied by the same elimination.

Next definitions: [D169](#d169), [D185](#d185), [D190](#d190).

<a id="d187"></a>

**D187 — [`ArithmeticThetaDegreeAssembly.relationBasis`](../Lean/EarlyCertificateAssembly.lean#L27)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> The computed rational nullspace basis, viewed as vectors over `ℂ`.

Next definitions: [D169](#d169), [D188](#d188), [D194](#d194).

<a id="d188"></a>

**D188 — [`ArithmeticThetaDegreeAssembly.relationCount`](../Lean/EarlyCertificateAssembly.lean#L18)**

Used by **C** · `definition` · module `EarlyCertificateAssembly`.

> Number of rational nullspace vectors computed from coefficients through `B`.

Next definitions: [D169](#d169), [D192](#d192), [D199](#d199).

<a id="d189"></a>

**D189 — [`ArithmeticThetaElimination.State`](../Lean/EliminationAlgorithm.lean#L21)**

Used by **C, M** · `structure` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
structure State (m h : ℕ) where
```

No further counted custom definition is reached before the external-library boundary.

<a id="d190"></a>

**D190 — [`ArithmeticThetaElimination.columnCoordinates`](../Lean/EliminationAlgorithm.lean#L72)**

Used by **C, M** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def columnCoordinates {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) (j : Fin h) :
```

Next definitions: [D189](#d189), [D199](#d199).

<a id="d191"></a>

**D191 — [`ArithmeticThetaElimination.findPivot`](../Lean/EliminationAlgorithm.lean#L5)**

Used by **C, M** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def findPivot {m h : ℕ} (M : Matrix (Fin m) (Fin h) ℚ) (r : ℕ) (c : Fin h) :
```

No further counted custom definition is reached before the external-library boundary.

<a id="d192"></a>

**D192 — [`ArithmeticThetaElimination.freeColumns`](../Lean/EliminationAlgorithm.lean#L55)**

Used by **C** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def freeColumns {m h : ℕ} (s : State m h) : List (Fin h) :=
```

Next definitions: [D189](#d189), [D196](#d196).

<a id="d193"></a>

**D193 — [`ArithmeticThetaElimination.initial`](../Lean/EliminationAlgorithm.lean#L27)**

Used by **C, M** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def initial {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) : State m h :=
```

Next definitions: [D189](#d189).

<a id="d194"></a>

**D194 — [`ArithmeticThetaElimination.nullBasis`](../Lean/EliminationAlgorithm.lean#L64)**

Used by **C** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def nullBasis {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) :
```

Next definitions: [D192](#d192), [D195](#d195), [D199](#d199).

<a id="d195"></a>

**D195 — [`ArithmeticThetaElimination.nullVector`](../Lean/EliminationAlgorithm.lean#L58)**

Used by **C** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def nullVector {m h : ℕ} (s : State m h) (f : Fin h) (j : Fin h) : ℚ :=
```

Next definitions: [D189](#d189), [D198](#d198), [D201](#d201).

<a id="d196"></a>

**D196 — [`ArithmeticThetaElimination.pivotColumns`](../Lean/EliminationAlgorithm.lean#L52)**

Used by **C** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def pivotColumns {m h : ℕ} (s : State m h) : List (Fin h) :=
```

Next definitions: [D189](#d189).

<a id="d197"></a>

**D197 — [`ArithmeticThetaElimination.pivotOperation`](../Lean/EliminationAlgorithm.lean#L13)**

Used by **C, M** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def pivotOperation {m h k : ℕ} (M : Matrix (Fin m) (Fin h) ℚ)
```

Next definitions: [D202](#d202).

<a id="d198"></a>

**D198 — [`ArithmeticThetaElimination.pivotRow`](../Lean/EliminationAlgorithm.lean#L49)**

Used by **C** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def pivotRow {m h : ℕ} (s : State m h) (j : Fin h) : Option (Fin m) :=
```

Next definitions: [D189](#d189).

<a id="d199"></a>

**D199 — [`ArithmeticThetaElimination.run`](../Lean/EliminationAlgorithm.lean#L41)**

Used by **C, M** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def run {m h : ℕ} (A : Matrix (Fin m) (Fin h) ℚ) : State m h :=
```

Next definitions: [D189](#d189), [D193](#d193), [D200](#d200).

<a id="d200"></a>

**D200 — [`ArithmeticThetaElimination.step`](../Lean/EliminationAlgorithm.lean#L30)**

Used by **C, M** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def step {m h : ℕ} (s : State m h) (c : Fin h) : State m h :=
```

Next definitions: [D189](#d189), [D191](#d191), [D197](#d197), [D201](#d201).

<a id="d201"></a>

**D201 — [`ArithmeticThetaElimination.step.match_1`](../Lean/EliminationAlgorithm.lean#L30)**

Used by **C, M** · `definition` · module `EliminationAlgorithm`.

Lean-generated pattern-matching helper for `ArithmeticThetaElimination.step`. It has no
separate handwritten declaration or docstring; the source link opens
its generating definition. It is included in the technical count.

No further counted custom definition is reached before the external-library boundary.

<a id="d202"></a>

**D202 — [`ArithmeticThetaElimination.swapRows`](../Lean/EliminationAlgorithm.lean#L9)**

Used by **C, M** · `definition` · module `EliminationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def swapRows {m k : ℕ} (M : Matrix (Fin m) (Fin k) ℚ) (r s : Fin m) :
```

No further counted custom definition is reached before the external-library boundary.

<a id="d203"></a>

**D203 — [`ArithmeticThetaEnumeration.coefficientsUpTo`](../Lean/EnumerationAlgorithm.lean#L23)**

Used by **C, M** · `definition` · module `EnumerationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def coefficientsUpTo {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ) : List ℕ :=
```

Next definitions: [D206](#d206), [D207](#d207).

<a id="d204"></a>

**D204 — [`ArithmeticThetaEnumeration.coordinateRadius`](../Lean/EnumerationAlgorithm.lean#L8)**

Used by **C, M** · `definition` · module `EnumerationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def coordinateRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) (j : Fin n) : ℕ :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d205"></a>

**D205 — [`ArithmeticThetaEnumeration.integerInterval`](../Lean/EnumerationAlgorithm.lean#L11)**

Used by **C, M** · `definition` · module `EnumerationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def integerInterval (R : ℕ) : Finset ℤ :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d206"></a>

**D206 — [`ArithmeticThetaEnumeration.normNumerator`](../Lean/EnumerationAlgorithm.lean#L5)**

Used by **C, M** · `definition` · module `EnumerationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def normNumerator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℤ) : ℤ :=
```

No further counted custom definition is reached before the external-library boundary.

<a id="d207"></a>

**D207 — [`ArithmeticThetaEnumeration.searchBox`](../Lean/EnumerationAlgorithm.lean#L14)**

Used by **C, M** · `definition` · module `EnumerationAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def searchBox {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) : Finset (Fin n → ℤ) :=
```

Next definitions: [D204](#d204), [D205](#d205).

<a id="d208"></a>

**D208 — [`ArithmeticThetaLevelCount.levelIndex`](../Lean/GlobalizationDefinitions.lean#L67)**

Used by **C** · `definition` · module `GlobalizationDefinitions`.

> The rational product occurring in the manuscript, with no cardinality assumption.

No further counted custom definition is reached before the external-library boundary.

<a id="d209"></a>

**D209 — [`ArithmeticThetaOrthogonalAlgorithm.basisMatrix`](../Lean/OrthogonalAlgorithm.lean#L22)**

Used by **C, M** · `definition` · module `OrthogonalAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def basisMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
```

Next definitions: [D214](#d214).

<a id="d210"></a>

**D210 — [`ArithmeticThetaOrthogonalAlgorithm.naturalNorms`](../Lean/OrthogonalAlgorithm.lean#L28)**

Used by **C, M** · `definition` · module `OrthogonalAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def naturalNorms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℕ :=
```

Next definitions: [D211](#d211).

<a id="d211"></a>

**D211 — [`ArithmeticThetaOrthogonalAlgorithm.norms`](../Lean/OrthogonalAlgorithm.lean#L25)**

Used by **C, M** · `definition` · module `OrthogonalAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def norms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℤ :=
```

Next definitions: [D209](#d209), [D212](#d212).

<a id="d212"></a>

**D212 — [`ArithmeticThetaOrthogonalAlgorithm.pairing`](../Lean/OrthogonalAlgorithm.lean#L5)**

Used by **C, M** · `definition` · module `OrthogonalAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def pairing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
```

No further counted custom definition is reached before the external-library boundary.

<a id="d213"></a>

**D213 — [`ArithmeticThetaOrthogonalAlgorithm.project`](../Lean/OrthogonalAlgorithm.lean#L9)**

Used by **C, M** · `definition` · module `OrthogonalAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def project {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
```

Next definitions: [D212](#d212).

<a id="d214"></a>

**D214 — [`ArithmeticThetaOrthogonalAlgorithm.runPrefix`](../Lean/OrthogonalAlgorithm.lean#L18)**

Used by **C, M** · `definition` · module `OrthogonalAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def runPrefix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
```

Next definitions: [D215](#d215).

<a id="d215"></a>

**D215 — [`ArithmeticThetaOrthogonalAlgorithm.step`](../Lean/OrthogonalAlgorithm.lean#L13)**

Used by **C, M** · `definition` · module `OrthogonalAlgorithm`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def step {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) :
```

Next definitions: [D213](#d213).

<a id="d216"></a>

**D216 — [`ArithmeticThetaOrthogonalConsumerR0127.RationalCosets`](../Lean/OrthogonalConsumerDefinitionsR0127.lean#L28)**

Used by **C** · `definition` · module `OrthogonalConsumerDefinitionsR0127`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
abbrev RationalCosets {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :=
```

Next definitions: [D221](#d221), [D222](#d222).

<a id="d217"></a>

**D217 — [`ArithmeticThetaOrthogonalConsumerR0127.Representatives`](../Lean/OrthogonalConsumerDefinitionsR0127.lean#L34)**

Used by **C** · `definition` · module `OrthogonalConsumerDefinitionsR0127`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def Representatives {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
```

Next definitions: [D216](#d216), [D219](#d219), [D222](#d222).

<a id="d218"></a>

**D218 — [`ArithmeticThetaOrthogonalConsumerR0127.castVec`](../Lean/OrthogonalConsumerDefinitionsR0127.lean#L13)**

Used by **C** · `definition` · module `OrthogonalConsumerDefinitionsR0127`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def castVec (n : ℕ) : (Fin n → ℤ) →+ (Fin n → ℚ) where
```

No further counted custom definition is reached before the external-library boundary.

<a id="d219"></a>

**D219 — [`ArithmeticThetaOrthogonalConsumerR0127.cosetClass`](../Lean/OrthogonalConsumerDefinitionsR0127.lean#L31)**

Used by **C** · `definition` · module `OrthogonalConsumerDefinitionsR0127`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def cosetClass {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
```

Next definitions: [D216](#d216), [D221](#d221), [D222](#d222).

<a id="d220"></a>

**D220 — [`ArithmeticThetaOrthogonalConsumerR0127.integerVectors`](../Lean/OrthogonalConsumerDefinitionsR0127.lean#L18)**

Used by **C** · `definition` · module `OrthogonalConsumerDefinitionsR0127`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def integerVectors (n : ℕ) : AddSubgroup (Fin n → ℚ) := (castVec n).range
```

Next definitions: [D218](#d218).

<a id="d221"></a>

**D221 — [`ArithmeticThetaOrthogonalConsumerR0127.periods`](../Lean/OrthogonalConsumerDefinitionsR0127.lean#L24)**

Used by **C** · `definition` · module `OrthogonalConsumerDefinitionsR0127`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def periods {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
```

Next definitions: [D220](#d220), [D222](#d222).

<a id="d222"></a>

**D222 — [`ArithmeticThetaOrthogonalConsumerR0127.preimageLattice`](../Lean/OrthogonalConsumerDefinitionsR0127.lean#L20)**

Used by **C** · `definition` · module `OrthogonalConsumerDefinitionsR0127`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def preimageLattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
```

Next definitions: [D220](#d220).

<a id="d223"></a>

**D223 — [`ArithmeticThetaSharpKernelR0195.cutoff`](../Lean/SharpKernelDefinitionsR0195.lean#L39)**

Used by **M** · `definition` · module `SharpKernelDefinitionsR0195`.

> Natural division is the exact nonnegative floor, with no enlarged cutoff.

Next definitions: [D152](#d152), [D163](#d163), [D166](#d166), [D224](#d224).

<a id="d224"></a>

**D224 — [`ArithmeticThetaSharpKernelR0195.normCount`](../Lean/SharpKernelDefinitionsR0195.lean#L28)**

Used by **C, M** · `definition` · module `SharpKernelDefinitionsR0195`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def normCount {n h : ℕ} (A : Matrices n h) : ℕ := (norms A).card
```

Next definitions: [D163](#d163), [D225](#d225).

<a id="d225"></a>

**D225 — [`ArithmeticThetaSharpKernelR0195.norms`](../Lean/SharpKernelDefinitionsR0195.lean#L23)**

Used by **C, M** · `definition` · module `SharpKernelDefinitionsR0195`.

No declaration docstring is recorded in Lean.

Actual source header:

```lean
def norms {n h : ℕ} (A : Matrices n h) : Finset ℕ := by
```

Next definitions: [D163](#d163), [D210](#d210).

## Generation record

- Measured report SHA-256: `408a66f25fa8242030a0908ff481e92d1810a6571a0c6d31df0d12bf8e7c2c7d`.
- Lean declaration metadata SHA-256: `41e5fa4e8bc8fa51d98469537bb611096f6b80bf3e5fe74f46d0ce9b641d2fad`.
- Generated with `scripts/generate_definition_index.py`; declaration metadata
  is read from the compiled environment by `scripts/definition_index_metadata.lean`.
- Every indexed source hash was checked against the measured report before generation.
- These documentation tools do not build or alter proof declarations.
