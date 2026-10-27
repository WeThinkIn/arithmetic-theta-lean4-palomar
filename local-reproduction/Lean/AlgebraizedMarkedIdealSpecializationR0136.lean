import AlgebraizedSplitMarkedDivisorR0136

/-! Scheme-theoretic specialization of the disjoint algebraized marked union. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaAlgebraizedMarkedLineR0136
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaProjectiveEffectivityR0135

namespace AlgebraizedMarkedIdealSpecializationR0136
lemma ker_sigma {ι : Type*} [Small.{u} ι] {X : ι → Scheme.{u}} {Y : Scheme.{u}}
    (s : ∀ i, X i ⟶ Y) [QuasiCompact (Sigma.desc s)] : (Sigma.desc s).ker = ⨅ i, (s i).ker := by
  rw [← (Sigma.desc s).iInf_ker_openCover_map_comp (sigmaOpenCover X)]
  congr 1
  funext i
  congr 1
  exact Sigma.ι_desc s i

lemma ker_baseChange {A B X Y : Scheme.{u}} {a : A ⟶ X} {b : A ⟶ B}
    {f : X ⟶ Y} {g : B ⟶ Y} [IsClosedImmersion g]
    (h : IsPullback a b f g) : g.ker.comap f = a.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom, h.isoPullback_hom_fst]

lemma section_square (k : Type u) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (hM : IsModel k T M) (a : Fin r → kˣ)
    (s : Fin r → (baseScheme k ⟶ M.X)) (hs : LiftFamily k M a s)
    (n : ℕ) (i : Fin r) :
    IsPullback (markedSection k r n hr (T.atlas n) i (a i))
      (baseInclusion k n) (M.inclusion n) (s i) := by
  have outer : IsPullback (markedSection k r n hr (T.atlas n) i (a i) ≫
      (T.atlas n).p) (baseInclusion k n) (baseInclusion k n) (s i ≫ M.p) := by
    rw [SmoothMarkedSections.section_over, (hs i).1]
    exact IsPullback.id_horiz (baseInclusion k n)
  exact outer.of_right ((hs i).2 n).symm (hM.2.2.1 n).flip
end AlgebraizedMarkedIdealSpecializationR0136

/-- Equality of actual ideal sheaves on every infinitesimal stage. -/
theorem algebraized_marked_ideal_specialization :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : Tower k r hr) (M : Model k T), IsModel k T M →
    ∀ (a : Fin r → kˣ) (s : Fin r → (baseScheme k ⟶ M.X)),
      LiftFamily k M a s → ∀ n : ℕ,
      (markedIdeal k M s).comap (M.inclusion n) =
        ArithmeticThetaPolygonCartierR0133.markedIdeal k r n hr (T.atlas n) a := by
  intro k _ _ r hr _h3 T M hM a s hs n
  let sn := fun i : Fin r => markedSection k r n hr (T.atlas n) i (a i)
  have hsc (i : Fin r) : IsClosedImmersion (s i) :=
    AlgebraizedSplitMarkedDivisorR0136.section_closed k M hM (s i) (hs i).1
  have : IsClosedImmersion (Sigma.desc s) :=
    ArithmeticThetaPolygonCartierR0133.SplitFiniteMarkedDivisorR0133.closed_sigma s
      (AlgebraizedSplitMarkedDivisorR0136.sections_disjoint k M hM a s hs)
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct (fun _ : Fin r => baseScheme k))
  have hp := hu.isPullback_of_isColimit_left s (Sigma.desc s) (M.inclusion n)
    sn (fun _ => baseInclusion k n)
    (AlgebraizedMarkedIdealSpecializationR0136.section_square k M hM a s hs n)
    (coproductIsCoproduct (fun _ : Fin r => specR k n))
  have he : Cofan.IsColimit.desc
      (coproductIsCoproduct (fun _ : Fin r => specR k n)) sn = Sigma.desc sn := by
    apply Sigma.hom_ext
    intro i
    exact (Cofan.IsColimit.fac _ _ i).trans (Sigma.ι_desc sn i).symm
  rw [he] at hp
  have : IsClosedImmersion (Sigma.desc sn) :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  have hker := AlgebraizedMarkedIdealSpecializationR0136.ker_baseChange hp
  simpa only [
    AlgebraizedMarkedIdealSpecializationR0136.ker_sigma, markedIdeal,
    ArithmeticThetaPolygonCartierR0133.markedIdeal, sn] using hker

end ArithmeticThetaAlgebraizedMarkedLineR0136
