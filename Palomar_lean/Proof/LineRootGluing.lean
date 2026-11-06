module

public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.ENatToNat

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u v

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ArithmeticThetaLineRoot

/-- Actual rank-one local trivializations, natural on every subopen. -/
structure LocalFrame (X : Scheme.{u}) (H : X.Modules) (U : X.Opens) where
  equiv (V : X.Opens) (hVU : V ≤ U) : Γ(X, V) ≃ₗ[Γ(X, V)] Γ(H, V)
  naturality (V W : X.Opens) (hWV : W ≤ V) (hVU : V ≤ U) (a : Γ(X, V)) :
    H.presheaf.map (homOfLE hWV).op (equiv V hVU a) =
      equiv W (hWV.trans hVU) (X.presheaf.map (homOfLE hWV).op a)

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

def transition (e f : R ≃ₗ[R] M) : R := e.symm (f 1)

theorem transition_apply (e f : R ≃ₗ[R] M) (a : R) :
    f a = e (transition e f * a) := by
  rw [mul_comm]
  calc
    f a = a • f 1 := by simpa using f.map_smul a (1 : R)
    _ = e (a * transition e f) := by
      change a • f 1 = e (a • e.symm (f 1))
      rw [e.map_smul, e.apply_symm_apply]

theorem transition_cocycle (e f g : R ≃ₗ[R] M) :
    transition e g = transition e f * transition f g := by
  apply e.injective
  simp only [transition, LinearEquiv.apply_symm_apply]
  simpa [transition] using transition_apply e f (f.symm (g 1))

theorem transition_self (e : R ≃ₗ[R] M) : transition e e = 1 := by
  simp [transition]

def transitionUnit (e f : R ≃ₗ[R] M) : Rˣ where
  val := transition e f
  inv := transition f e
  val_inv := by rw [← transition_cocycle, transition_self]
  inv_val := by rw [← transition_cocycle, transition_self]

theorem transitionUnit_cocycle (e f g : R ≃ₗ[R] M) :
    transitionUnit e g = transitionUnit e f * transitionUnit f g := by
  apply Units.ext
  exact transition_cocycle e f g

variable (X : Scheme.{u}) [IsIntegral X]

theorem germ_restrict (U V : X.Opens) [Nonempty U] [Nonempty V]
    (hVU : V ≤ U) (a : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE hVU).op a) =
      X.germToFunctionField U a := by
  exact X.presheaf.germ_res_apply (homOfLE hVU) (genericPoint X) _ a

theorem overlap_nonempty (U V : X.Opens) [Nonempty U] [Nonempty V] :
    Nonempty (U ⊓ V : X.Opens) := by
  refine ⟨⟨genericPoint X, ?_, ?_⟩⟩
  · exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  · exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)

theorem affine_root_regular (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIntegrallyClosed Γ(X, U)] (N : ℕ) (hN : 0 < N)
    (r : X.functionField) (a : Γ(X, U))
    (hr : r ^ N = X.germToFunctionField U a) :
    ∃! b : Γ(X, U), X.germToFunctionField U b = r ∧ b ^ N = a := by
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hN
    (IsIntegrallyClosed.isIntegral_iff.mpr ⟨a, hr.symm⟩)
  refine ⟨b, ⟨hb, ?_⟩, ?_⟩
  · apply X.germToFunctionField_injective U
    change algebraMap Γ(X, U) X.functionField (b ^ N) = _
    rw [map_pow, hb, hr]
  · intro c hc
    exact X.germToFunctionField_injective U (hc.1.trans hb.symm)

/-- A genuine affine cover carrying natural trivializations of an actual module sheaf. -/
structure NormalFrameCover (H : X.Modules) (ι : Type v) where
  opens : ι → X.Opens
  covers : (⊤ : X.Opens) ≤ iSup opens
  nonempty : ∀ i, Nonempty (opens i)
  affine : ∀ i, IsAffineOpen (opens i)
  normal : ∀ i, IsIntegrallyClosed Γ(X, opens i)
  frame : ∀ i, LocalFrame X H (opens i)

variable {X} {H : X.Modules} {ι : Type v}

instance (C : NormalFrameCover X H ι) (i : ι) : Nonempty (C.opens i) := C.nonempty i
instance (C : NormalFrameCover X H ι) (i : ι) : IsIntegrallyClosed Γ(X, C.opens i) :=
  C.normal i
instance (C : NormalFrameCover X H ι) (i j : ι) :
    Nonempty (C.opens i ⊓ C.opens j : X.Opens) := overlap_nonempty X _ _

def overlapUnit (C : NormalFrameCover X H ι) (i j : ι) :
    Γ(X, C.opens i ⊓ C.opens j)ˣ :=
  transitionUnit ((C.frame i).equiv _ inf_le_left) ((C.frame j).equiv _ inf_le_right)

omit [IsIntegral X] in
theorem transition_restrict {U V W Z : X.Opens}
    (e : LocalFrame X H U) (f : LocalFrame X H V)
    (hWU : W ≤ U) (hWV : W ≤ V) (hZW : Z ≤ W) :
    X.presheaf.map (homOfLE hZW).op (transition (e.equiv W hWU) (f.equiv W hWV)) =
      transition (e.equiv Z (hZW.trans hWU)) (f.equiv Z (hZW.trans hWV)) := by
  apply (e.equiv Z (hZW.trans hWU)).injective
  rw [← e.naturality W Z hZW hWU]
  simp only [transition, LinearEquiv.apply_symm_apply]
  rw [f.naturality, map_one]

omit [IsIntegral X] in
theorem overlapUnit_cocycle (C : NormalFrameCover X H ι) (i j k : ι)
    (W : X.Opens) (hi : W ≤ C.opens i) (hj : W ≤ C.opens j) (hk : W ≤ C.opens k) :
    X.presheaf.map (homOfLE (le_inf hi hk)).op (overlapUnit C i k) =
      X.presheaf.map (homOfLE (le_inf hi hj)).op (overlapUnit C i j) *
      X.presheaf.map (homOfLE (le_inf hj hk)).op (overlapUnit C j k) := by
  change X.presheaf.map (homOfLE (le_inf hi hk)).op
      (transition ((C.frame i).equiv _ inf_le_left) ((C.frame k).equiv _ inf_le_right)) =
    X.presheaf.map (homOfLE (le_inf hi hj)).op
      (transition ((C.frame i).equiv _ inf_le_left) ((C.frame j).equiv _ inf_le_right)) *
    X.presheaf.map (homOfLE (le_inf hj hk)).op
      (transition ((C.frame j).equiv _ inf_le_left) ((C.frame k).equiv _ inf_le_right))
  rw [transition_restrict, transition_restrict, transition_restrict]
  exact transition_cocycle _ _ _

/-- Coefficients of the actual local frames relative to one rational frame. -/
structure RationalFrame (C : NormalFrameCover X H ι) where
  coeff : ι → X.functionField
  nonzero : ∀ i, coeff i ≠ 0
  transition_eq : ∀ i j, coeff j =
    X.germToFunctionField (C.opens i ⊓ C.opens j) (overlapUnit C i j) * coeff i

/-- A frame on any one nonempty chart gives a rational frame on all charts. -/
def rationalFrameFromChart (C : NormalFrameCover X H ι) (i₀ : ι) : RationalFrame C where
  coeff i := X.germToFunctionField (C.opens i₀ ⊓ C.opens i) (overlapUnit C i₀ i)
  nonzero i := ((overlapUnit C i₀ i).isUnit.map
    (X.germToFunctionField (C.opens i₀ ⊓ C.opens i)).hom).ne_zero
  transition_eq i j := by
    let W := (C.opens i₀ ⊓ C.opens i) ⊓ C.opens j
    let : Nonempty W := overlap_nonempty X (C.opens i₀ ⊓ C.opens i) (C.opens j)
    have h := congrArg (X.germToFunctionField W)
      (overlapUnit_cocycle C i₀ i j W (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right) inf_le_right)
    rw [map_mul, germ_restrict, germ_restrict, germ_restrict] at h
    exact h.trans (mul_comm _ _)

theorem exists_rationalFrame (C : NormalFrameCover X H ι) : Nonempty (RationalFrame C) := by
  have h : genericPoint X ∈ iSup C.opens := C.covers (by trivial)
  obtain ⟨i₀, _⟩ := Opens.mem_iSup.mp h
  exact ⟨rationalFrameFromChart C i₀⟩

theorem rational_coefficient_transition (C : NormalFrameCover X H ι)
    (T : RationalFrame C) (r : X.functionField) (i j : ι) :
    r / T.coeff i = X.germToFunctionField (C.opens i ⊓ C.opens j)
      (overlapUnit C i j) * (r / T.coeff j) := by
  field_simp [T.nonzero i, T.nonzero j]
  rw [T.transition_eq i j]
  ring

theorem regular_sections_compatible (C : NormalFrameCover X H ι)
    (b : ∀ i, Γ(X, C.opens i)) (r : ι → X.functionField)
    (hb : ∀ i, X.germToFunctionField (C.opens i) (b i) = r i)
    (hr : ∀ i j, r i = X.germToFunctionField (C.opens i ⊓ C.opens j)
      (overlapUnit C i j) * r j) :
    TopCat.Presheaf.IsCompatible H.presheaf C.opens
      (fun i ↦ (C.frame i).equiv _ le_rfl (b i)) := by
  intro i j
  change H.presheaf.map (homOfLE (inf_le_left : C.opens i ⊓ C.opens j ≤ C.opens i)).op
      ((C.frame i).equiv _ le_rfl (b i)) =
    H.presheaf.map (homOfLE (inf_le_right : C.opens i ⊓ C.opens j ≤ C.opens j)).op
      ((C.frame j).equiv _ le_rfl (b j))
  rw [(C.frame i).naturality _ _ inf_le_left le_rfl,
    (C.frame j).naturality _ _ inf_le_right le_rfl]
  rw [transition_apply ((C.frame i).equiv _ inf_le_left)
    ((C.frame j).equiv _ inf_le_right)]
  apply congrArg ((C.frame i).equiv _ inf_le_left)
  apply X.germToFunctionField_injective (C.opens i ⊓ C.opens j)
  rw [map_mul, germ_restrict, germ_restrict, hb, hb]
  exact hr i j

theorem regular_sections_glue (C : NormalFrameCover X H ι)
    (b : ∀ i, Γ(X, C.opens i)) (r : ι → X.functionField)
    (hb : ∀ i, X.germToFunctionField (C.opens i) (b i) = r i)
    (hr : ∀ i j, r i = X.germToFunctionField (C.opens i ⊓ C.opens j)
      (overlapUnit C i j) * r j) :
    ∃! s : Γ(H, ⊤), ∀ i, H.presheaf.map (homOfLE le_top).op s =
      (C.frame i).equiv _ le_rfl (b i) := by
  exact TopCat.Sheaf.existsUnique_gluing' ⟨H.presheaf, H.isSheaf⟩ C.opens ⊤
    (fun _ ↦ homOfLE le_top) C.covers _ (regular_sections_compatible C b r hb hr)

def coordinate (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) (i : ι) :
    Γ(X, C.opens i) :=
  ((C.frame i).equiv _ le_rfl).symm (H.presheaf.map (homOfLE le_top).op s)

theorem existsUnique_regular_root (C : NormalFrameCover X H ι)
    (T : RationalFrame C) (N : ℕ) (hN : 0 < N) (r : X.functionField)
    (a : ∀ i, Γ(X, C.opens i))
    (hpow : ∀ i, (r / T.coeff i) ^ N = X.germToFunctionField (C.opens i) (a i)) :
    ∃! s : Γ(H, ⊤), ∀ i,
      X.germToFunctionField (C.opens i) (coordinate C s i) = r / T.coeff i ∧
      coordinate C s i ^ N = a i := by
  have hex i := affine_root_regular X (C.opens i) (C.affine i) N hN
    (r / T.coeff i) (a i) (hpow i)
  choose b hb using fun i ↦ (hex i).exists
  obtain ⟨s, hs, huniq⟩ := regular_sections_glue C b (fun i ↦ r / T.coeff i)
    (fun i ↦ (hb i).1) (rational_coefficient_transition C T r)
  have hscoord i : coordinate C s i = b i := by
    simp only [coordinate, hs i, LinearEquiv.symm_apply_apply]
  refine ⟨s, fun i ↦ ?_, ?_⟩
  · rw [hscoord]
    exact hb i
  · intro s' hs'
    apply huniq s'
    intro i
    apply ((C.frame i).equiv _ le_rfl).symm.injective
    change coordinate C s' i = _
    rw [LinearEquiv.symm_apply_apply]
    exact (hex i).unique (hs' i) (hb i)

/-- A second actual module sheaf with the Nth-power transition law. -/
structure PowerFrames (C : NormalFrameCover X H ι) (P : X.Modules) (N : ℕ) where
  frame : ∀ i, LocalFrame X P (C.opens i)
  transition_eq : ∀ i j,
    transition ((frame i).equiv _ inf_le_left) ((frame j).equiv _ inf_le_right) =
      (overlapUnit C i j : Γ(X, C.opens i ⊓ C.opens j)) ^ N

omit [IsIntegral X] in
theorem global_sections_compatible (C : NormalFrameCover X H ι) (s : Γ(H, ⊤)) :
    TopCat.Presheaf.IsCompatible H.presheaf C.opens
      (fun i ↦ (C.frame i).equiv _ le_rfl (coordinate C s i)) := by
  intro i j
  simp only [coordinate, LinearEquiv.apply_symm_apply]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

omit [IsIntegral X] in
theorem power_sections_compatible (C : NormalFrameCover X H ι)
    (P : X.Modules) (N : ℕ) (E : PowerFrames C P N) (s : Γ(H, ⊤)) :
    TopCat.Presheaf.IsCompatible P.presheaf C.opens
      (fun i ↦ (E.frame i).equiv _ le_rfl (coordinate C s i ^ N)) := by
  intro i j
  have h := global_sections_compatible C s i j
  change H.presheaf.map (homOfLE inf_le_left).op
      ((C.frame i).equiv _ le_rfl (coordinate C s i)) =
    H.presheaf.map (homOfLE inf_le_right).op
      ((C.frame j).equiv _ le_rfl (coordinate C s j)) at h
  rw [(C.frame i).naturality, (C.frame j).naturality,
    transition_apply ((C.frame i).equiv _ inf_le_left)
      ((C.frame j).equiv _ inf_le_right)] at h
  have hc := ((C.frame i).equiv _ inf_le_left).injective h
  change P.presheaf.map (homOfLE inf_le_left).op
      ((E.frame i).equiv _ le_rfl (coordinate C s i ^ N)) =
    P.presheaf.map (homOfLE inf_le_right).op
      ((E.frame j).equiv _ le_rfl (coordinate C s j ^ N))
  rw [(E.frame i).naturality, (E.frame j).naturality,
    transition_apply ((E.frame i).equiv _ inf_le_left)
      ((E.frame j).equiv _ inf_le_right)]
  apply congrArg ((E.frame i).equiv _ inf_le_left)
  rw [map_pow, map_pow, hc, mul_pow, E.transition_eq]
  rfl

omit [IsIntegral X] in
theorem existsUnique_power_section (C : NormalFrameCover X H ι)
    (P : X.Modules) (N : ℕ) (E : PowerFrames C P N) (s : Γ(H, ⊤)) :
    ∃! t : Γ(P, ⊤), ∀ i, P.presheaf.map (homOfLE le_top).op t =
      (E.frame i).equiv _ le_rfl (coordinate C s i ^ N) := by
  exact TopCat.Sheaf.existsUnique_gluing' ⟨P.presheaf, P.isSheaf⟩ C.opens ⊤
    (fun _ ↦ homOfLE le_top) C.covers _ (power_sections_compatible C P N E s)

def powerSection (C : NormalFrameCover X H ι) (P : X.Modules)
    (N : ℕ) (E : PowerFrames C P N) (s : Γ(H, ⊤)) : Γ(P, ⊤) :=
  (existsUnique_power_section C P N E s).choose

omit [IsIntegral X] in
theorem powerSection_restrict (C : NormalFrameCover X H ι) (P : X.Modules)
    (N : ℕ) (E : PowerFrames C P N) (s : Γ(H, ⊤)) (i : ι) :
    P.presheaf.map (homOfLE le_top).op (powerSection C P N E s) =
      (E.frame i).equiv _ le_rfl (coordinate C s i ^ N) :=
  (existsUnique_power_section C P N E s).choose_spec.1 i

theorem exists_regular_root_of_section (C : NormalFrameCover X H ι)
    (T : RationalFrame C) (P : X.Modules) (N : ℕ) (hN : 0 < N)
    (E : PowerFrames C P N) (r : X.functionField) (F : Γ(P, ⊤))
    (hpow : ∀ i, (r / T.coeff i) ^ N = X.germToFunctionField (C.opens i)
      (((E.frame i).equiv _ le_rfl).symm (P.presheaf.map (homOfLE le_top).op F))) :
    ∃ s : Γ(H, ⊤), (∀ i,
      X.germToFunctionField (C.opens i) (coordinate C s i) = r / T.coeff i) ∧
      powerSection C P N E s = F := by
  obtain ⟨s, hs, _⟩ := existsUnique_regular_root C T N hN r
    (fun i ↦ ((E.frame i).equiv _ le_rfl).symm
      (P.presheaf.map (homOfLE le_top).op F)) hpow
  refine ⟨s, fun i ↦ (hs i).1, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨P.presheaf, P.isSheaf⟩ C.opens ⊤
    (fun _ ↦ homOfLE le_top) C.covers
  intro i
  rw [powerSection_restrict, (hs i).2, LinearEquiv.apply_symm_apply]

end ArithmeticThetaLineRoot
