module

public import MetaplecticComparisonDefinitionsR0206

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticComparisonR0206
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLocalWeierstrassR0203 ArithmeticThetaSchemeLevelR0204
open ArithmeticThetaSchemeHodgeR0205 ArithmeticThetaTensorPower ArithmeticThetaCoverComparison

namespace ActualGroupoidProof
variable {L : ℕ} {S : Scheme.{0}}

lemma mult_id (E : Family S) : Multiplicative E E (𝟙 S) (𝟙 E.curve) := by
  intro U t x y x' y' hx hy
  simp only [Category.comp_id] at *
  have hx' : x' = x := Subtype.ext hx
  have hy' : y' = y := Subtype.ext hy
  subst x'; subst y'
  rfl

lemma mult_comp {E F G : Family S} {f : F.curve ⟶ E.curve} {g : G.curve ⟶ F.curve}
    (_hf : f ≫ E.p = F.p) (hg : g ≫ F.p = G.p)
    (mf : Multiplicative E F (𝟙 S) f) (mg : Multiplicative F G (𝟙 S) g) :
    Multiplicative E G (𝟙 S) (g ≫ f) := by
  intro U t x y x' y' hx hy
  let xx : SchemeHomOver t F.p := ⟨x.val ≫ g, by rw [Category.assoc, hg]; exact x.property⟩
  let yy : SchemeHomOver t F.p := ⟨y.val ≫ g, by rw [Category.assoc, hg]; exact y.property⟩
  rw [mf U t xx yy x' y' (by simpa [xx, Category.assoc] using hx)
    (by simpa [yy, Category.assoc] using hy)]
  have hm := mg U t x y xx yy rfl rfl
  exact (congrArg (fun q ↦ q ≫ f) hm).trans (Category.assoc _ _ _)

lemma mult_inv {E F : Family S} (f : F.curve ≅ E.curve)
    (_hf : f.hom ≫ E.p = F.p) (mf : Multiplicative E F (𝟙 S) f.hom) :
    Multiplicative F E (𝟙 S) f.inv := by
  intro U t x y x' y' hx hy
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, f.inv_hom_id, Category.comp_id]
  exact (mf U t x' y' x y (by simp [hx]) (by simp [hy])).symm

lemma marked_id (X : Object L S) :
    MarkedCartesian X.family X.family X.marking X.marking (𝟙 S) (𝟙 X.family.curve) := by
  exact ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, by simp, mult_id _, by simp, by simp⟩

lemma marked_comp {X Y Z : Object L S} (f : Arrow X Y) (g : Arrow Y Z) :
    MarkedCartesian Z.family X.family Z.marking X.marking (𝟙 S) (f.curve.hom ≫ g.curve.hom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using f.marked.1.paste_horiz g.marked.1
  · rw [← Category.assoc, f.marked.2.1]; simpa using g.marked.2.1
  · exact mult_comp (by simpa using g.marked.1.w) (by simpa using f.marked.1.w)
      g.marked.2.2.1 f.marked.2.2.1
  · rw [← Category.assoc, f.marked.2.2.2.1]; simpa using g.marked.2.2.2.1
  · rw [← Category.assoc, f.marked.2.2.2.2]; simpa using g.marked.2.2.2.2

lemma marked_inv {X Y : Object L S} (f : Arrow X Y) :
    MarkedCartesian X.family Y.family X.marking Y.marking (𝟙 S) f.curve.inv := by
  have hp : f.curve.inv ≫ X.family.p = Y.family.p := by
    rw [← show f.curve.hom ≫ Y.family.p = X.family.p from by simpa using f.marked.1.w]
    simp
  refine ⟨IsPullback.of_horiz_isIso ⟨by simpa using hp⟩, ?_,
    mult_inv f.curve (by simpa using f.marked.1.w) f.marked.2.2.1, ?_, ?_⟩
  all_goals apply (cancel_mono f.curve.hom).mp
  all_goals simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · simpa using f.marked.2.1.symm
  · simpa using f.marked.2.2.2.1.symm
  · simpa using f.marked.2.2.2.2.symm

/-- The uniquely inclusion-normalized backward cotangent comparison. -/
def backward {E F : Family S} (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p (𝟙 S))
    (hz : F.zero ≫ f = 𝟙 S ≫ E.zero) : Cotangent E ≅ Cotangent F :=
  (Scheme.Modules.pullbackId S).symm.app (Cotangent E) ≪≫
    cotangentComparison E F (𝟙 S) f hz
      (Classical.choose (cartesian_identity_ideal S S E F (𝟙 S) f hc hz))

lemma backward_canonical {E F : Family S} (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p (𝟙 S)) (hz : F.zero ≫ f = 𝟙 S ≫ E.zero) :
    CotangentCompatible E F (𝟙 S) f hz
      ((Scheme.Modules.pullbackId S).app (Cotangent E) ≪≫ backward f hc hz) := by
  refine ⟨_, (Classical.choose_spec (cartesian_identity_ideal S S E F (𝟙 S) f hc hz)).1, ?_⟩
  apply Iso.ext
  simp [backward]

lemma backward_unique {E F : Family S} (f : F.curve ⟶ E.curve)
    (hc : IsPullback f F.p E.p (𝟙 S)) (hz : F.zero ≫ f = 𝟙 S ≫ E.zero)
    (e : Cotangent E ≅ Cotangent F)
    (he : CotangentCompatible E F (𝟙 S) f hz
      ((Scheme.Modules.pullbackId S).app (Cotangent E) ≪≫ e)) :
    e = backward f hc hz := by
  obtain ⟨i, hi, he⟩ := he
  have hu := (Classical.choose_spec (cartesian_identity_ideal S S E F (𝟙 S) f hc hz)).2 i hi
  apply Iso.ext
  apply (cancel_epi ((Scheme.Modules.pullbackId S).app (Cotangent E)).hom).mp
  have he' := congrArg Iso.hom he
  simpa only [hu, backward, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Iso.hom_inv_id_app_assoc] using he'

lemma backward_id (E : Family S)
    (hc : IsPullback (𝟙 E.curve) E.p E.p (𝟙 S))
    (hz : E.zero ≫ 𝟙 E.curve = 𝟙 S ≫ E.zero) :
    backward (𝟙 E.curve) hc hz = Iso.refl _ := by
  apply Iso.ext
  have h := scheme_cotangent_coherence.1 S E hz _ (backward_canonical _ hc hz)
  change (Scheme.Modules.pullbackId S).hom.app _ ≫ _ = _ at h
  apply (cancel_epi ((Scheme.Modules.pullbackId S).hom.app (Cotangent E))).mp
  simpa using h

lemma coherence_comp {E F G : Family S}
    (a b c : S ⟶ S) (hab : a ≫ b = c)
    (f : F.curve ⟶ E.curve) (g : G.curve ⟶ F.curve)
    (zf : F.zero ≫ f = b ≫ E.zero) (zg : G.zero ≫ g = a ≫ F.zero)
    (zgf : G.zero ≫ (g ≫ f) = c ≫ E.zero)
    (ef : (Scheme.Modules.pullback b).obj (Cotangent E) ≅ Cotangent F)
    (eg : (Scheme.Modules.pullback a).obj (Cotangent F) ≅ Cotangent G)
    (egf : (Scheme.Modules.pullback c).obj (Cotangent E) ≅ Cotangent G)
    (hf : CotangentCompatible E F b f zf ef)
    (hg : CotangentCompatible F G a g zg eg)
    (hgf : CotangentCompatible E G c (g ≫ f) zgf egf) :
    (Scheme.Modules.pullback a).map ef.hom ≫ eg.hom =
      (Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr hab).hom.app
        (Cotangent E) ≫ egf.hom := by
  subst c
  simpa [Scheme.Modules.pullbackCongr] using
    scheme_cotangent_coherence.2 S S S E F G b a f g zf zg zgf ef eg egf hf hg hgf

lemma pullback_id_comp (M : S.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 S) (𝟙 S) ≪≫
      Scheme.Modules.pullbackCongr (Category.id_comp (𝟙 S))).hom.app M =
      (Scheme.Modules.pullbackId S).hom.app ((Scheme.Modules.pullback (𝟙 S)).obj M) := by
  have h := congrArg (fun q ↦ q.app M) (Scheme.Modules.pseudofunctor_right_unitality (𝟙 S))
  dsimp at h
  apply (cancel_epi ((Scheme.Modules.pullbackComp (𝟙 S) (𝟙 S)).inv.app M)).mp
  simpa [Scheme.Modules.pullbackCongr] using h.symm

lemma backward_comp {E F G : Family S}
    (f : F.curve ⟶ E.curve) (g : G.curve ⟶ F.curve)
    (hf : IsPullback f F.p E.p (𝟙 S)) (hg : IsPullback g G.p F.p (𝟙 S))
    (hgf : IsPullback (g ≫ f) G.p E.p (𝟙 S))
    (zf : F.zero ≫ f = 𝟙 S ≫ E.zero) (zg : G.zero ≫ g = 𝟙 S ≫ F.zero)
    (zgf : G.zero ≫ (g ≫ f) = 𝟙 S ≫ E.zero) :
    backward (g ≫ f) hgf zgf = backward f hf zf ≪≫ backward g hg zg := by
  let ef := (Scheme.Modules.pullbackId S).app (Cotangent E) ≪≫ backward f hf zf
  let eg := (Scheme.Modules.pullbackId S).app (Cotangent F) ≪≫ backward g hg zg
  let egf := (Scheme.Modules.pullbackId S).app (Cotangent E) ≪≫ backward (g ≫ f) hgf zgf
  have h := coherence_comp (𝟙 S) (𝟙 S) (𝟙 S) (Category.id_comp _) f g
    zf zg zgf ef eg egf (backward_canonical f hf zf) (backward_canonical g hg zg)
    (backward_canonical (g ≫ f) hgf zgf)
  rw [pullback_id_comp] at h
  dsimp only [ef, eg, egf, Iso.trans_hom, Iso.app_hom] at h
  rw [← Category.assoc, (Scheme.Modules.pullbackId S).hom.naturality] at h
  simp only [Functor.id_map, Category.assoc] at h
  apply Iso.ext
  exact ((cancel_epi ((Scheme.Modules.pullbackId S).hom.app
    ((Scheme.Modules.pullback (𝟙 S)).obj (Cotangent E)))).mp
      h).symm |> (cancel_epi ((Scheme.Modules.pullbackId S).hom.app (Cotangent E))).mp

lemma arrow_backward {X Y : Object L S} (f : Arrow X Y) :
    f.cotangent.symm = backward f.curve.hom f.marked.1 f.marked.2.1 :=
  backward_unique _ _ _ _ f.canonical

/-- The specified square equation determines the cotangent map from the line map. -/
lemma arrow_ext {X Y : Object L S} (f g : Arrow X Y)
    (hc : f.curve.hom = g.curve.hom) (hl : f.line.hom = g.line.hom) : f = g := by
  have ht : f.cotangent.hom = g.cotangent.hom := by
    apply (cancel_epi X.root.square.hom).mp
    rw [← f.square, ← g.square, hl]
  have hc' := Iso.ext hc
  have hl' := Iso.ext hl
  have ht' := Iso.ext ht
  cases f; cases g
  dsimp at hc' hl' ht'
  cases hc'; cases hl'; cases ht'
  rfl

def identity (X : Object L S) : Arrow X X where
  curve := Iso.refl _
  marked := marked_id X
  cotangent := Iso.refl _
  canonical := by
    have h := backward_canonical (𝟙 X.family.curve) (marked_id X).1 (marked_id X).2.1
    rw [backward_id] at h
    simpa using h
  line := Iso.refl _
  square := by simp

def compose {X Y Z : Object L S} (f : Arrow X Y) (g : Arrow Y Z) : Arrow X Z where
  curve := f.curve ≪≫ g.curve
  marked := marked_comp f g
  cotangent := f.cotangent ≪≫ g.cotangent
  canonical := by
    have he : (f.cotangent ≪≫ g.cotangent).symm =
        backward (f.curve.hom ≫ g.curve.hom) (marked_comp f g).1 (marked_comp f g).2.1 := by
      change g.cotangent.symm ≪≫ f.cotangent.symm = _
      rw [arrow_backward f, arrow_backward g]
      exact (backward_comp _ _ _ _ _ _ _ _).symm
    rw [he]
    exact backward_canonical _ _ _
  line := f.line ≪≫ g.line
  square := by
    simp only [Iso.trans_hom, tensorPowerMap_comp, Category.assoc]
    rw [g.square, ← Category.assoc, f.square, Category.assoc]

lemma inverse_backward {X Y : Object L S} (f : Arrow X Y) :
    backward f.curve.inv (marked_inv f).1 (marked_inv f).2.1 = f.cotangent := by
  have hp : IsPullback (f.curve.inv ≫ f.curve.hom) Y.family.p Y.family.p (𝟙 S) := by
    simpa using (marked_id Y).1
  have hz : Y.family.zero ≫ (f.curve.inv ≫ f.curve.hom) = 𝟙 S ≫ Y.family.zero := by simp
  have h := backward_comp f.curve.hom f.curve.inv f.marked.1 (marked_inv f).1 hp
    f.marked.2.1 (marked_inv f).2.1 hz
  have hid : backward (f.curve.inv ≫ f.curve.hom) hp hz = Iso.refl _ := by
    generalize_proofs at *
    simpa only [f.curve.inv_hom_id] using backward_id Y.family (marked_id Y).1 (marked_id Y).2.1
  rw [hid, ← arrow_backward f] at h
  apply Iso.ext
  apply (cancel_epi f.cotangent.inv).mp
  simpa using (congrArg Iso.hom h).symm

def inverse {X Y : Object L S} (f : Arrow X Y) : Arrow Y X where
  curve := f.curve.symm
  marked := marked_inv f
  cotangent := f.cotangent.symm
  canonical := by
    have h := backward_canonical f.curve.inv (marked_inv f).1 (marked_inv f).2.1
    rw [inverse_backward] at h
    exact h
  line := f.line.symm
  square := by
    apply (cancel_mono f.cotangent.hom).mp
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← f.square, ← Category.assoc, ← tensorPowerMap_comp,
      Iso.inv_hom_id, tensorPowerMap_id, Category.id_comp]

/-- All homs are precisely the frozen actual arrows. -/
@[instance_reducible] def groupoid (L : ℕ) (S : Scheme.{0}) : Groupoid.{0} (Object L S) where
  Hom := Arrow
  id := identity
  comp := compose
  id_comp f := by apply arrow_ext <;> simp [identity, compose]
  comp_id f := by apply arrow_ext <;> simp [identity, compose]
  assoc f g h := by apply arrow_ext <;> simp [compose]
  inv := inverse
  inv_comp f := by apply arrow_ext <;> simp [inverse, compose, identity]
  comp_inv f := by apply arrow_ext <;> simp [inverse, compose, identity]

end ActualGroupoidProof

/-- Every actual marked family with its specified cotangent square root belongs
    to the groupoid with exactly the specified geometric arrows. -/
theorem actual_metaplectic_groupoid :
    ∀ (L : ℕ) (S : AlgebraicGeometry.Scheme.{0}), Nonempty (GroupoidData L S) := by
  intro L S
  exact ⟨{
    groupoid := ActualGroupoidProof.groupoid L S
    arrow := fun _ _ ↦ Equiv.refl _
    curve_id := fun _ ↦ rfl
    line_id := fun _ ↦ rfl
    curve_comp := fun _ _ _ _ _ ↦ rfl
    line_comp := fun _ _ _ _ _ ↦ rfl
  }⟩

#print axioms actual_metaplectic_groupoid
end ArithmeticThetaMetaplecticComparisonR0206
