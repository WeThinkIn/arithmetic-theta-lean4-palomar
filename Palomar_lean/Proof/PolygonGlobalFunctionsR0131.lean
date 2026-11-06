module

public import PolygonCechKernelR0131

@[expose] public section

/-! Global functions on every realization of the finite cyclic atlas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaPolygonCohomologyR0131
namespace PolygonGlobalFunctionsR0131
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129

variable (k : Type u) [Field k] [CharZero k]
variable (r n : ℕ) (hr : 0 < r) {E : B k n false ≃+* B k n true}
variable (D : Atlas k r n hr E)

/-- Restrict an actual global section to the affine node charts. -/
def chartSections (s : D.X.presheaf.obj (Opposite.op ⊤)) : Fin r → A k n :=
  fun i => (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom ((D.chart i).appTop s)

lemma affine_pullback {S T : CommRingCat.{u}} (f : S ⟶ T)
    (s : (Spec S).presheaf.obj (Opposite.op ⊤)) :
    (Scheme.ΓSpecIso T).hom ((Spec.map f).appTop s) =
      f ((Scheme.ΓSpecIso S).hom s) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality f) s

omit [CharZero k] in
lemma chartSections_compatible (s : D.X.presheaf.obj (Opposite.op ⊤)) :
    difference k r n hr E (chartSections k r n hr D s) = 0 := by
  funext i
  apply sub_eq_zero.mpr
  have h := congrArg (fun f : specB k n true ⟶ D.X => f.appTop) (D.adjacent i).w
  have hs := ConcreteCategory.congr_hom h s
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hs
  have he := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).hom z) hs
  change (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).hom
    ((Spec.map (CommRingCat.ofHom (E.toRingHom.comp (restriction k n false)))).appTop
      ((D.chart i).appTop s)) =
    (Scheme.ΓSpecIso (CommRingCat.of (B k n true))).hom
    ((Spec.map (CommRingCat.ofHom (restriction k n true))).appTop
      ((D.chart (next r hr i)).appTop s)) at he
  rw [affine_pullback, affine_pullback] at he
  exact he

omit [CharZero k] in
lemma chartSections_base (c : R k n) :
    chartSections k r n hr D (globalBase k r n hr D c) = constants k r n c := by
  funext i
  have h := congrArg (fun f : specA k n ⟶ specR k n => f.appTop) (D.chart_over i)
  have hs := ConcreteCategory.congr_hom h
    ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv c)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hs
  change (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom
    ((D.chart i).appTop (D.p.appTop ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv c))) = _
  rw [hs]
  change (Scheme.ΓSpecIso (CommRingCat.of (A k n))).hom
    ((Spec.map (CommRingCat.ofHom (base k n))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv c)) = _
  rw [affine_pullback]
  simpa [constants] using congrArg (base k n)
    ((Scheme.ΓSpecIso (CommRingCat.of (R k n))).commRingCatIsoToRingEquiv.apply_symm_apply c)

omit [CharZero k] in
lemma chartSections_injective : Function.Injective (chartSections k r n hr D) := by
  intro s t h
  apply (D.openCover).ext_elem s t
  intro i
  have hi := congrFun h i
  have he := (Scheme.ΓSpecIso (CommRingCat.of (A k n))).commRingCatIsoToRingEquiv.injective hi
  exact he

end PolygonGlobalFunctionsR0131
open ArithmeticThetaInfinitesimalPolygonR0129 PolygonGlobalFunctionsR0131

/-- The actual structural pullback to global sections is bijective. -/
theorem polygon_global_functions :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r n : ℕ) (hr : 0 < r), 3 ≤ r →
      ∀ (E : B k n false ≃+* B k n true), IsAdjacent k n E →
      ∀ D : Atlas k r n hr E, Function.Bijective (globalBase k r n hr D) := by
  intro k _ _ r n hr h3 E hE D
  constructor
  · intro c d h
    obtain ⟨z, hz, hu⟩ := (polygon_cech_kernel k r n hr h3 E hE
      (chartSections k r n hr D (globalBase k r n hr D c))).mp
      (chartSections_compatible k r n hr D _)
    have hc := hu c (chartSections_base k r n hr D c).symm
    have hd := hu d (by rw [h]; exact (chartSections_base k r n hr D d).symm)
    exact hc.trans hd.symm
  · intro s
    obtain ⟨c, hc, _⟩ := (polygon_cech_kernel k r n hr h3 E hE
      (chartSections k r n hr D s)).mp (chartSections_compatible k r n hr D s)
    refine ⟨c, chartSections_injective k r n hr D ?_⟩
    rw [chartSections_base, hc]

end ArithmeticThetaPolygonCohomologyR0131
