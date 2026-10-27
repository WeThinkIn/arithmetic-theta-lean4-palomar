import SimultaneousDiskRootSectionsR0187
import UnaryPowersInCommonSquareLineR0187
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
noncomputable section

namespace ArithmeticThetaSimultaneousUnaryR0187.SimultaneousUnaryCommonCoverR0187
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaCommonHalfHodgeR0185 CommonHalfHodgeCoverR0185
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCompactUnaryR0183

/-- The actual punctured disk dominates any integral smooth curve through which
its compact Tate disk factors. Its generic and closed images differ because
one lies in the open modular curve and the other in its boundary. -/
lemma disk_dominant (k : Type) [Field k] [CharZero k] (L : ℕ)
    (D : LevelData k L) (X : Compactification k L D) (V : DiskTest k L D X)
    {Z : Scheme.{0}} [IsIntegral Z] (b : Z ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 b] (p : Z ⟶ X.space)
    (g : Disk k ⟶ Z) (hg : g ≫ p = V.disk) :
    IsDominant (genericInclusion k ≫ g) := by
  classical
  let z := _root_.genericPoint (Puncture k)
  have he : (genericInclusion k ≫ g) z = _root_.genericPoint Z := by
    by_contra hn
    have hc := AlgebraicCurve.isClosed_singleton_of_ne_genericPoint b _ hn
    have hs : (genericInclusion k ≫ g) z ⤳ g (closedPoint k) :=
      (IsLocalRing.specializes_closedPoint ((genericInclusion k) z)).map g.continuous
    have heq : (genericInclusion k ≫ g) z = g (closedPoint k) := by
      exact (hc.closure_subset (specializes_iff_mem_closure.mp hs)).symm
    have hpoint : (V.base ≫ X.inclusion) z = V.disk (closedPoint k) := by
      rw [← V.extends_eq.2.1, ← hg]
      exact congrArg p heq
    have hb := V.extends_eq.2.2
    change V.disk (closedPoint k) ∉ Set.range X.inclusion at hb
    exact hb ⟨V.base z, hpoint⟩
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff, ← (_root_.genericPoint_spec Z).def]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr ⟨z, he⟩

/-- Finite flat rank constancy multiplies the actual two degrees. -/
lemma composite_degree {B Z Y : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z]
    (r : Y ⟶ Z) (p : Z ⟶ B) [IsFinite r] [Flat r] [IsFinite p] [Flat p]
    (a c : ℕ) (hr : ∀ z, 0 < r.finrank z ∧ r.finrank z ≤ a)
    (hp : ∀ x, 0 < p.finrank x ∧ p.finrank x ≤ c) (x : B) :
    0 < (r ≫ p).finrank x ∧ (r ≫ p).finrank x ≤ c * a := by
  letI : LocallyOfFinitePresentation r :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr inferInstance
  let z := _root_.genericPoint Z
  have hc : ∀ y, r.finrank y = r.finrank z := fun y =>
    (Scheme.Hom.isLocallyConstant_finrank r).apply_eq_of_isPreconnected
      PreconnectedSpace.isPreconnected_univ trivial trivial
  rw [Scheme.Hom.finrank_comp_of_finrank_eq_const r p (r.finrank z) hc]
  refine ⟨Nat.mul_pos (hr z).1 (hp x).1, ?_⟩
  simpa only [Nat.mul_comm c a] using Nat.mul_le_mul (hr z).2 (hp x).2

open HodgeBaseChange

/-- Coherence of the square comparison uses the actual three composable maps. -/
lemma half_square_disk (k : Type) [Field k] [CharZero k] (L : ℕ)
    {D : LevelData k L} {X : Compactification k L D} {x : X.space}
    {A : DivisorLine (Component k L D X x)} {H : Extension k L D X}
    {d2 : Sections X.space (tensorPower X.space H.line 24)}
    (C : HalfCover k L D X x A H d2) (V : DiskTest k L D X)
    (f : Disk k ⟶ Component k L D X x) (hf : f ≫ inclusion k L D X x = V.disk)
    (g : Disk k ⟶ C.space) (hg : g ≫ C.map = f)
    (hgp : g ≫ (C.map ≫ inclusion k L D X x) = V.disk)
    (h : Sections (Disk k) ((Scheme.Modules.pullback g).obj
      ((Scheme.Modules.pullback C.map).obj A.line))) :
    (squareOnDisk k (C.map ≫ inclusion k L D X x)
      ((Scheme.Modules.pullback C.map).obj A.line) H.line (halfSquare k L C)
      g V.disk hgp).hom.app ⊤ (tensorPowerSection (Disk k) _ 2 ⊤ h) =
    (diskHodgeIso k L D X x H V f hf).hom.app ⊤
      ((pullSquare g C.map f hg A.line (hodge k L D X x H) C.square).hom.app ⊤
        (tensorPowerSection (Disk k) _ 2 ⊤ ((along g C.map f hg A.line).hom.app ⊤ h))) := by
  have hc := ArithmeticThetaGenericEvaluationR0140.NormalizedIdentityFrameR0140.compIso_assoc
    g C.map (inclusion k L D X x) f (C.map ≫ inclusion k L D X x) V.disk
    hg rfl hf hgp H.line
  change (Scheme.Modules.pullback g).map (along C.map (inclusion k L D X x)
      (C.map ≫ inclusion k L D X x) rfl H.line).hom ≫
      (along g (C.map ≫ inclusion k L D X x) V.disk hgp H.line).hom =
    (along g C.map f hg (hodge k L D X x H)).hom ≫
      (diskHodgeIso k L D X x H V f hf).hom at hc
  have hm : (squareOnDisk k (C.map ≫ inclusion k L D X x)
      ((Scheme.Modules.pullback C.map).obj A.line) H.line (halfSquare k L C)
      g V.disk hgp).hom =
      (powerCongr (Disk k) (along g C.map f hg A.line) 2).hom ≫
        (pullSquare g C.map f hg A.line (hodge k L D X x H) C.square).hom ≫
          (diskHodgeIso k L D X x H V f hf).hom := by
    simp only [squareOnDisk, halfSquare, pullSquare, tensorComparison, Iso.trans_hom,
      Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_assoc]
    congr 2
  rw [hm]
  change _ = _
  rw [← powerCongr_section (Disk k) (along g C.map f hg A.line) 2 ⊤ h]
  rfl

#print axioms half_square_disk

#print axioms disk_dominant
#print axioms composite_degree

end ArithmeticThetaSimultaneousUnaryR0187.SimultaneousUnaryCommonCoverR0187

namespace ArithmeticThetaSimultaneousUnaryR0187
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaNormalizedSections ArithmeticThetaPullback
open ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaCommonHalfHodgeR0185 CommonHalfHodgeCoverR0185
open ArithmeticThetaBoundaryHodgeR0182 ArithmeticThetaLevelCompactificationR0179
open ArithmeticThetaComponentDegreeR0184 ArithmeticThetaTateCuspsR0181
open ArithmeticThetaCompactUnaryR0183 SimultaneousUnaryCommonCoverR0187
open ArithmeticThetaOpenHodgeR0180.GlobalFamilyDiscriminantR0180

/-- The common half-Hodge cover and all prescribed unary roots on one finite
smooth proper curve, with the positive composite degree bounded by 24*K^s. -/
theorem simultaneous_unary_common_cover :
∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (N s : ℕ), 0 < N → Even N → ∀ (m : Fin s → ℕ) (ν : Fin s → ℤ), (∀ j, 0 < m j ∧ Even (m j) ∧ m j ∣ N ∧ (-(m j : ℤ) ≤ 2*ν j ∧ 2*ν j < (m j : ℤ))) → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ∀ (d2 : ArithmeticThetaSimultaneousUnaryR0187.Sections X.space (ArithmeticThetaTensorPower.tensorPower X.space (H.line) (24))), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k (ArithmeticThetaCompactUnaryR0183.level N) D X H d2 → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k (ArithmeticThetaCompactUnaryR0183.level N) D X) (ζ : k), IsPrimitiveRoot ζ (ArithmeticThetaCompactUnaryR0183.level N) → ArithmeticThetaTateCuspsR0181.CanonicalMarking k (ArithmeticThetaCompactUnaryR0183.level N) ζ V.level → ArithmeticThetaSimultaneousUnaryR0187.SimultaneousUnary k N s m ν H d2 V := by
  intro k _ _ _ N s hN hNeven m ν hm D X H hH d2 hd2 V ζ hζ hmark
  have hL : 0 < level N := by dsimp [level]; positivity
  have h24 : 24 ∣ level N := dvd_mul_right 24 (N^2)
  obtain ⟨f, hf, A, hA, C, hC⟩ := common_half_hodge_cover k (level N) hL h24
    D X H hH d2 hd2 V
  let x := V.disk (closedPoint k)
  letI := C.integral
  letI := C.finite
  letI := C.etale
  letI := C.proper
  letI := C.smooth
  have hJ : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback C.map).obj A.line) :=
    (hA.choose_spec.1.1).pullback C.map
  obtain ⟨g, hg, hbranch⟩ := hC
  have hgp : g ≫ (C.map ≫ inclusion k (level N) D X x) = V.disk := by
    rw [← Category.assoc, hg, hf]
  obtain ⟨η, hη, _⟩ := hH V
  obtain ⟨h₀, hh₀, hcanonical, hsquare₀⟩ := hbranch η hη
  let e := along g C.map f hg A.line
  let h := e.inv.app ⊤ h₀
  have he : e.hom.app ⊤ h = h₀ := ArithmeticThetaCommonHalfHodgeR0185.DiscriminantTateRootR0185.iso_inv_hom_apply e.symm ⊤ h₀
  have hh : IsFrame ((Scheme.Modules.pullback g).obj
      ((Scheme.Modules.pullback C.map).obj A.line)) ⊤ h := frame_iso e.symm h₀ hh₀
  have hsquare : (squareOnDisk k (C.map ≫ inclusion k (level N) D X x)
      ((Scheme.Modules.pullback C.map).obj A.line) H.line (halfSquare k (level N) C)
      g V.disk hgp).hom.app ⊤ (tensorPowerSection (Disk k) _ 2 ⊤ h) = η := by
    rw [half_square_disk k (level N) C V f hf g hg hgp h]
    change _ = η
    rw [show (along g C.map f hg A.line).hom.app ⊤ h = h₀ from he]
    exact hsquare₀
  obtain ⟨F, hF, hFd⟩ := unary_powers_in_common_square_line k N s hN hNeven m ν hm
    D X H hH V ζ hζ hmark C.space (C.map ≫ inclusion k (level N) D X x)
    ((Scheme.Modules.pullback C.map).obj A.line) hJ (halfSquare k (level N) C)
    g hgp η hη h hh hsquare
  have hFne : ∀ j, F j ≠ 0 := fun j => hF.choose_spec.2 j |>.1
  have hK : 0 < exponent N := by
    dsimp [exponent]
    have : 2 ≤ 1 + 12*N := by omega
    have : 1 < (1+12*N)^2 := by nlinarith
    omega
  have hgb : g ≫ (C.map ≫ projection k (level N) D X x) = diskStructure k := by
    change g ≫ (C.map ≫ (inclusion k (level N) D X x ≫ X.projection)) = _
    rw [← Category.assoc C.map, ← Category.assoc g, hgp]
    exact V.extends_eq.1
  have hdom := disk_dominant k (level N) D X V
    (C.map ≫ projection k (level N) D X x)
    (C.map ≫ inclusion k (level N) D X x) g hgp
  obtain ⟨R, hR⟩ := simultaneous_disk_root_sections k C.space
    (C.map ≫ projection k (level N) D X x)
    ((Scheme.Modules.pullback C.map).obj A.line) hJ (exponent N) s hK F hFne
    g hgb hdom h hh (fun j => unarySeries k N (m j) (ν j)) hFd
  refine ⟨f, hf, A, hA, C, ⟨g, hg, hbranch⟩, g, hg, hgp, η, hη,
    h, hh, ?_, hsquare, F, hF, R, hR, ?_⟩
  · rw [show (along g C.map f hg A.line).hom.app ⊤ h = h₀ from he]
    exact hcanonical
  · letI := R.finite
    letI := R.flat
    letI : IsLocallyNoetherian C.space :=
      LocallyOfFiniteType.isLocallyNoetherian (C.map ≫ projection k (level N) D X x)
    exact composite_degree R.map C.map ((exponent N)^s) 24 R.degree C.rank

#print axioms simultaneous_unary_common_cover
end ArithmeticThetaSimultaneousUnaryR0187
