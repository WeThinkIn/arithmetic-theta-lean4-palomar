import HodgeInitialDefinitionsR0163

/-! Compatibility of the actual finite-chart logarithmic derivation with
Taylor expansion. All implementation declarations belong to this module. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaAlgebraicCoordinatesR0143
open ArithmeticThetaCubicModelR0144.LogarithmicCoordinateDerivativeR0144

section Algebra
variable {F B S : Type} [CommRing F] [CommRing B] [CommRing S] [Algebra F B]
local instance : Module Sᵐᵒᵖ S := Semiring.toOppositeModule

/-- A derivation followed by a ring map, encoded without any implicit choice
of scalar action on the target. -/
def mappedLift (f : B →+* S) (D : Derivation F B B) :
    B →+* TrivSqZeroExt S S where
  toFun a := ⟨f a, f (D a)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [D.leibniz, smul_eq_mul, mul_comm]

/-- The logarithmic derivative in the parameter u=z-1. -/
def logDerivative (S : Type) [CommRing S] :
    Derivation S (PowerSeries S) (PowerSeries S) :=
  (1 + PowerSeries.X : PowerSeries S) • PowerSeries.derivative S

lemma logDerivative_apply (f : PowerSeries S) :
    logDerivative S f = (1 + PowerSeries.X) * PowerSeries.derivative S f := rfl

@[simp] lemma logDerivative_C (a : S) : logDerivative S (PowerSeries.C a) = 0 := by
  simp [logDerivative_apply]

@[simp] lemma logDerivative_z :
    logDerivative S (1 + PowerSeries.X) = (1 + PowerSeries.X : PowerSeries S) := by
  simp [logDerivative_apply]

lemma logDerivative_inverse (w : PowerSeries S)
    (hw : (1 + PowerSeries.X) * w = 1) : logDerivative S w = -w := by
  have hd := congrArg (logDerivative S) hw
  rw [Derivation.leibniz, logDerivative_z, Derivation.map_one_eq_zero] at hd
  change (1 + PowerSeries.X) * logDerivative S w + w * (1 + PowerSeries.X) = 0 at hd
  calc
    logDerivative S w = w * ((1 + PowerSeries.X) * logDerivative S w) := by
      rw [← mul_assoc, mul_comm w, hw, one_mul]
    _ = w * (-(w * (1 + PowerSeries.X))) := by
      rw [eq_neg_of_add_eq_zero_left hd]
    _ = -w := by rw [mul_comm w (1 + PowerSeries.X), hw]; simp
end Algebra

variable (k : Type) [Field k] [CharZero k] (n : ℕ)

/-- Naturality on the actual truncated nodal algebra is forced by the base
and its two specified coordinates. -/
lemma finite_deriv_naturality {F S : Type} [CommRing F] [CommRing S] [Algebra F S]
    (f : A k n →+* S) (D : Derivation F S S)
    (hb : ∀ c, D (f (base k n c)) = 0)
    (hx : D (f (coordX k n)) = f (coordX k n))
    (hy : D (f (coordY k n)) = -f (coordY k n)) (a : A k n) :
    D (f a) = f (deriv k n a) := by
  letI : Module Sᵐᵒᵖ S := Semiring.toOppositeModule
  have h : (mappedLift (RingHom.id S) D).comp f = mappedLift f (deriv k n) := by
    apply point_ext
    · ext c <;> simp [mappedLift, hb]
    · ext <;> simp [mappedLift, hx]
    · ext <;> simp [mappedLift, hy]
  exact congrArg TrivSqZeroExt.snd (RingHom.congr_fun h a)

def stageInverse : PowerSeries (R k n) :=
  PowerSeries.invOfUnit (1 + PowerSeries.X) 1

lemma stageInverse_mul :
    (1 + PowerSeries.X) * stageInverse k n = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simp)

/-- The literal substitution z=1+u and y=t/z, with base coefficients
reduced modulo t^(n+1). -/
def stageTaylor : A k n →+* PowerSeries (R k n) :=
  mkPoint PowerSeries.C (1 + PowerSeries.X)
    (PowerSeries.C (parameter k n) * stageInverse k n) (by
      rw [mul_left_comm, stageInverse_mul, mul_one])

lemma stageTaylor_base (c : R k n) :
    stageTaylor k n (base k n c) = PowerSeries.C c :=
by
  unfold stageTaylor
  exact RingHom.congr_fun (mkPoint_base _ _ _ (by
    rw [mul_left_comm, stageInverse_mul, mul_one])) c

lemma stageTaylor_x : stageTaylor k n (coordX k n) = 1 + PowerSeries.X :=
  mkPoint_x _ _ _ _

lemma stageTaylor_y : stageTaylor k n (coordY k n) =
    PowerSeries.C (parameter k n) * stageInverse k n := mkPoint_y _ _ _ _

lemma stageTaylor_deriv (a : A k n) :
    logDerivative (R k n) (stageTaylor k n a) = stageTaylor k n (deriv k n a) := by
  refine finite_deriv_naturality k n (stageTaylor k n) (logDerivative (R k n)) ?_ ?_ ?_ a
  · intro c
    rw [stageTaylor_base, logDerivative_C]
  · rw [stageTaylor_x, logDerivative_z]
  · rw [stageTaylor_y, Derivation.leibniz, logDerivative_C,
      logDerivative_inverse _ (stageInverse_mul k n)]
    simp [smul_eq_mul]

/-- The accepted cleared coordinate identity holds as a complete formal
power-series identity at every base thickness, not just to first order in u. -/
lemma stageTaylor_numerator (r : ℕ) (h3 : 3 ≤ r) (i : Fin r) :
    stageTaylor k n (equation k r n i) *
        logDerivative (R k n) (stageTaylor k n (numerator k false r n i)) -
      2 * stageTaylor k n (numerator k false r n i) *
        logDerivative (R k n) (stageTaylor k n (equation k r n i)) =
      2 * stageTaylor k n (numerator k true r n i) := by
  rw [stageTaylor_deriv, stageTaylor_deriv]
  simpa only [map_sub, map_mul, map_ofNat] using
    congrArg (stageTaylor k n) (numerator_derivative k n r h3 i)

open ArithmeticThetaOriginInitialR0161
open ArithmeticThetaKatoAnnularR0152 hiding Chart ChartField
open ArithmeticThetaKatoAnnularR0152.CompletedMarkedChartIdealR0152

/-- A nilpotent base target sees a completed chart entirely through a finite
quotient. The assertion uses all polynomial approximations from the accepted
completion, without assuming continuity as an extra hypothesis. -/
lemma completed_ext_nilpotent {S : Type} [CommRing S]
    (f g : Chart k →+* S)
    (hb : ∀ b, f (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.base k b))
    (hx : f (ArithmeticThetaAnnularTorsionPrereqR0053.cx k) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.cx k))
    (hy : f (ArithmeticThetaAnnularTorsionPrereqR0053.cy k) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.cy k))
    (ht : f (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ (n+1) = 0) :
    f = g := by
  have hfg : f.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) =
      g.comp (ArithmeticThetaAnnularTorsionPrereqR0053.complete k) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · exact hb
    · intro i
      fin_cases i
      · exact hx
      · exact hy
  have hparam : ArithmeticThetaScaledTateBridgeR0046.completedParameter k 1 =
      ArithmeticThetaAnnularTorsionPrereqR0053.tau k := by
    simp [ArithmeticThetaScaledTateBridgeR0046.completedParameter,
      ArithmeticThetaScaledTateBridgeR0046.t, ArithmeticThetaScaledTateBridgeR0046.parameter,
      ArithmeticThetaAnnularTorsionPrereqR0053.tau, ArithmeticThetaScaledAnnularR0050.tau,
      ArithmeticThetaScaledTateBridgeR0046.completedBaseMap]
  have hkill (q : Chart k →+* S)
      (hq : q (ArithmeticThetaAnnularTorsionPrereqR0053.tau k) ^ (n+1) = 0)
      (z : Chart k) (hz : z ∈ ArithmeticThetaScaledTateBridgeR0046.completedPower k 1 (n+1)) :
      q z = 0 := by
    have hm := Ideal.mem_map_of_mem q hz
    rw [ArithmeticThetaScaledTateBridgeR0046.completedPower, hparam,
      Ideal.map_pow, Ideal.map_span, Set.image_singleton] at hm
    simpa only [Ideal.span_singleton_pow, hq, Ideal.span_singleton_zero, Ideal.mem_bot] using hm
  apply RingHom.ext
  intro z
  obtain ⟨b, hb'⟩ := (ArithmeticThetaScaledTateBridgeR0046.completion_reductions
    k 1 (by decide)).2.2.2.2.2.2 (n+1) z
  have hf := hkill f ht _ hb'
  have hg := hkill g (by
    change g (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X) ^ (n+1) = 0
    rw [← hb]
    exact ht) _ hb'
  rw [map_sub, sub_eq_zero] at hf hg
  exact hf.trans ((RingHom.congr_fun hfg _).trans hg.symm)

/-- Every accepted completed Taylor map agrees, at every base thickness,
with the literal finite nodal Taylor substitution. -/
lemma taylor_reduction (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    (PowerSeries.map (trunc (PowerSeries k) PowerSeries.X n)).comp σ =
      (stageTaylor k n).comp (reduction k n) := by
  let f := (PowerSeries.map (trunc (PowerSeries k) PowerSeries.X n)).comp σ
  let g := (stageTaylor k n).comp (reduction k n)
  have hb (b : PowerSeries k) : f (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) =
      g (ArithmeticThetaAnnularTorsionPrereqR0053.base k b) := by
    simp only [f, g, RingHom.comp_apply, hσ.1, PowerSeries.map_C,
      reduction_base, stageTaylor_base]
  have hzi : PowerSeries.map (trunc (PowerSeries k) PowerSeries.X n) (zInverse k) =
      stageInverse k n := by
    have h1 : (1 + PowerSeries.X) * zInverse k = 1 :=
      PowerSeries.mul_invOfUnit _ _ (by simp)
    have h2 := congrArg (PowerSeries.map (trunc (PowerSeries k) PowerSeries.X n)) h1
    simp only [map_mul, map_add, map_one, PowerSeries.map_X] at h2
    calc
      PowerSeries.map (trunc (PowerSeries k) PowerSeries.X n) (zInverse k) =
          PowerSeries.map (trunc (PowerSeries k) PowerSeries.X n) (zInverse k) *
            ((1 + PowerSeries.X) * stageInverse k n) := by rw [stageInverse_mul, mul_one]
      _ = stageInverse k n := by
        rw [← mul_assoc, mul_comm _ (1 + PowerSeries.X), h2, one_mul]
  apply completed_ext_nilpotent k n f g hb
  · simp only [f, g, RingHom.comp_apply, hσ.2.1, map_add, map_one,
      PowerSeries.map_X, reduction_x, stageTaylor_x]
  · simp only [f, g, RingHom.comp_apply, hσ.2.2.1, map_mul,
      PowerSeries.map_C, hzi, reduction_y, stageTaylor_y]
    rfl
  · change (PowerSeries.map (trunc (PowerSeries k) PowerSeries.X n)
      (σ (ArithmeticThetaAnnularTorsionPrereqR0053.base k PowerSeries.X))) ^ (n+1) = 0
    rw [hσ.1, PowerSeries.map_C, ← map_pow]
    change PowerSeries.C (parameter k n ^ (n+1)) = 0
    rw [parameter_pow, map_zero]

section CoefficientMaps
variable {S S' : Type} [CommRing S] [CommRing S']

lemma derivative_map (f : S →+* S') (a : PowerSeries S) :
    PowerSeries.map f (PowerSeries.derivative S a) =
      PowerSeries.derivative S' (PowerSeries.map f a) := by
  ext i
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_derivative, map_mul,
    map_add, map_natCast, map_one]

lemma logDerivative_map (f : S →+* S') (a : PowerSeries S) :
    PowerSeries.map f (logDerivative S a) =
      logDerivative S' (PowerSeries.map f a) := by
  simp only [logDerivative_apply, map_mul, map_add, map_one,
    PowerSeries.map_X, derivative_map]
end CoefficientMaps

lemma bivariate_ext (a b : Bivariate k)
    (h : ∀ n, PowerSeries.map (trunc (PowerSeries k) PowerSeries.X n) a =
      PowerSeries.map (trunc (PowerSeries k) PowerSeries.X n) b) : a = b := by
  apply PowerSeries.ext
  intro i
  apply AlgebraizedThetaSaturationR0138.powerSeries_ext k
  intro n
  exact congrArg (PowerSeries.coeff i) (h n)

/-- Passing through all base reductions proves the entire completed cleared
coordinate identity. No truncation in the Taylor variable occurs. -/
lemma completed_numerator_identity (r : ℕ) (h3 : 3 ≤ r) (i : Fin r)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (h a b : Chart k)
    (hh : ∀ n, reduction k n h = equation k r n i)
    (ha : ∀ n, reduction k n a = numerator k false r n i)
    (hb : ∀ n, reduction k n b = numerator k true r n i) :
    σ h * logDerivative (PowerSeries k) (σ a) -
      2 * σ a * logDerivative (PowerSeries k) (σ h) = 2 * σ b := by
  apply bivariate_ext k
  intro n
  have ht (z : Chart k) := RingHom.congr_fun (taylor_reduction k n σ hσ) z
  simp only [RingHom.comp_apply] at ht
  simp only [map_sub, map_mul, map_ofNat, logDerivative_map, ht, hh, ha, hb]
  exact stageTaylor_numerator k n r h3 i

section LaurentExtension
variable (K : Type) [Field K]
local instance : Module (LaurentSeries K)ᵐᵒᵖ (LaurentSeries K) := Semiring.toOppositeModule

def powerSeriesLogLift : PowerSeries K →+* TrivSqZeroExt (LaurentSeries K) (LaurentSeries K) :=
  mappedLift (algebraMap (PowerSeries K) (LaurentSeries K)) (logDerivative K)

lemma powerSeriesLogLift_unit (a : nonZeroDivisors (PowerSeries K)) :
    IsUnit (powerSeriesLogLift K a) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  change IsUnit (algebraMap (PowerSeries K) (LaurentSeries K) a)
  exact IsLocalization.map_units (LaurentSeries K) a

def laurentLogLift : LaurentSeries K →+* TrivSqZeroExt (LaurentSeries K) (LaurentSeries K) :=
  IsLocalization.lift (powerSeriesLogLift_unit K)

lemma laurentLogLift_powerSeries (a : PowerSeries K) :
    laurentLogLift K (algebraMap (PowerSeries K) (LaurentSeries K) a) =
      powerSeriesLogLift K a := IsLocalization.lift_eq _ a

lemma laurentLogLift_fst (a : LaurentSeries K) : (laurentLogLift K a).fst = a := by
  have h : (TrivSqZeroExt.fstHom (LaurentSeries K) (LaurentSeries K) (LaurentSeries K)).toRingHom.comp
      (laurentLogLift K) = RingHom.id (LaurentSeries K) := by
    apply IsFractionRing.ringHom_ext (A := PowerSeries K)
    intro b
    change (laurentLogLift K (algebraMap (PowerSeries K) (LaurentSeries K) b)).fst = _
    rw [laurentLogLift_powerSeries]
    rfl
  exact RingHom.congr_fun h a

/-- Extension of the full logarithmic power-series derivation to the actual
Laurent field by localization. -/
def laurentLogDerivative : Derivation ℤ (LaurentSeries K) (LaurentSeries K) :=
  secondDeriv (laurentLogLift K) (laurentLogLift_fst K)

lemma laurentLogDerivative_powerSeries (a : PowerSeries K) :
    laurentLogDerivative K (algebraMap (PowerSeries K) (LaurentSeries K) a) =
      algebraMap (PowerSeries K) (LaurentSeries K) (logDerivative K a) := by
  change (laurentLogLift K (algebraMap (PowerSeries K) (LaurentSeries K) a)).snd = _
  rw [laurentLogLift_powerSeries]
  rfl

lemma laurentLogDerivative_C (a : K) :
    laurentLogDerivative K (HahnSeries.C a) = 0 := by
  rw [← HahnSeries.ofPowerSeries_C (Γ := ℤ) a]
  change laurentLogDerivative K
    (algebraMap (PowerSeries K) (LaurentSeries K) (PowerSeries.C a)) = 0
  rw [laurentLogDerivative_powerSeries, logDerivative_C, map_zero]
/-- The additive presentation keeps the same map when coefficient fields are
iterated Laurent fields, without rebuilding integer scalar instances. -/
def laurentLogAdd : LaurentSeries K →+ LaurentSeries K where
  toFun := laurentLogDerivative K
  map_zero' := map_zero _
  map_add' := map_add _

lemma laurentLogAdd_mul (a b : LaurentSeries K) :
    laurentLogAdd K (a*b) = a * laurentLogAdd K b + b * laurentLogAdd K a :=
  (laurentLogDerivative K).leibniz a b

lemma laurentLogAdd_powerSeries (a : PowerSeries K) :
    laurentLogAdd K (algebraMap (PowerSeries K) (LaurentSeries K) a) =
      algebraMap (PowerSeries K) (LaurentSeries K) (logDerivative K a) :=
  laurentLogDerivative_powerSeries K a
end LaurentExtension

section QuotientRule
variable {F L : Type} [CommRing F] [Field L] [Algebra F L]

lemma cleared_identity_div (D : Derivation F L L) (h a b : L) (hh : h ≠ 0)
    (he : h * D a - 2 * a * D h = 2 * b) :
    D (a / h^2) = 2 * (b / h^3) := by
  rw [Derivation.leibniz_div, Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  norm_num only [show 2-1=1 by decide, pow_one]
  field_simp
  linear_combination he
end QuotientRule

section DifferentialTransport
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaHodgeFourTorsionR0147.InverseDifferentialSign
variable {F L : Type} [CommRing F] [Field L]
variable {C : Scheme} [IsIntegral C]
variable (p : C ⟶ Spec (CommRingCat.of F))
variable (e : (SheafOfModules.unit C.ringCatSheaf : C.Modules) ≅ p.kaehler)
variable (E : C.functionField →+* L) (D : L →+ L)

def sectionExpansion (U : C.Opens) [Nonempty U] : Γ(C,U) →+* L :=
  E.comp (C.germToFunctionField U).hom

lemma sectionExpansion_restrict (U V : C.Opens) [Nonempty U] [Nonempty V]
    (h : V ≤ U) (a : Γ(C,U)) :
    sectionExpansion E V (C.presheaf.map (homOfLE h).op a) = sectionExpansion E U a := by
  simp only [sectionExpansion, RingHom.comp_apply, Scheme.germToFunctionField,
    C.presheaf.germ_res_apply]

def expansionDefect (U : C.Opens) [Nonempty U] : Γ(C,U) →+ L where
  toFun a := sectionExpansion E U (coefficient p e U a) - D (sectionExpansion E U a)
  map_zero' := by simp only [map_zero, coefficient_zero, sub_self]
  map_add' a b := by
    simp only [map_add, coefficient_add]
    abel

lemma expansionDefect_mul (hD : ∀ a b, D (a*b) = a * D b + b * D a) (U : C.Opens) [Nonempty U] (a b : Γ(C,U)) :
    expansionDefect p e E D U (a*b) =
      sectionExpansion E U a * expansionDefect p e E D U b +
        sectionExpansion E U b * expansionDefect p e E D U a := by
  simp only [expansionDefect, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    coefficient_mul, map_mul, map_add, hD]
  ring

lemma expansionDefect_restrict (U V : C.Opens) [Nonempty U] [Nonempty V]
    (h : V ≤ U) (a : Γ(C,U)) :
    expansionDefect p e E D V (C.presheaf.map (homOfLE h).op a) =
      expansionDefect p e E D U a := by
  change sectionExpansion E V (coefficient p e V _) - D (sectionExpansion E V _) = _
  rw [← coefficient_restrict, sectionExpansion_restrict, sectionExpansion_restrict]
  rfl

/-- A derivation comparison on one nonempty affine open controls all regular
functions on all nonempty opens of the same integral scheme. -/
lemma expansionDefect_zero_of_affine (hD : ∀ a b, D (a*b) = a * D b + b * D a) (W : C.Opens) (hW : IsAffineOpen W) [Nonempty W]
    (hzero : ∀ a, expansionDefect p e E D W a = 0)
    (U : C.Opens) [Nonempty U] (a : Γ(C,U)) :
    expansionDefect p e E D U a = 0 := by
  let V := U ⊓ W
  letI : Nonempty V := nonempty_inter U W
  let ρ := C.presheaf.map (homOfLE (show V ≤ W from inf_le_right)).op
  obtain ⟨b,c,hc,heq⟩ := section_fraction W hW U a
  have hz (z : Γ(C,W)) : expansionDefect p e E D V (ρ z) = 0 := by
    rw [expansionDefect_restrict]
    exact hzero z
  have hd := congrArg (expansionDefect p e E D V) heq
  rw [expansionDefect_mul p e E D hD, hz b, hz c, mul_zero, zero_add] at hd
  have hn : sectionExpansion E V (ρ c) ≠ 0 := by
    rw [sectionExpansion_restrict]
    intro H
    apply hc
    apply C.germToFunctionField_injective W
    apply E.injective
    simpa only [sectionExpansion, RingHom.comp_apply, map_zero] using H
  have hz' := (mul_eq_zero.mp hd).resolve_left hn
  rw [expansionDefect_restrict] at hz'
  exact hz'
end DifferentialTransport

section OriginTransport
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaCompactifiedDifferentialR0145 ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaHodgeFourTorsionR0147.InverseDifferentialSign
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

/-- The geometric stalk-to-field square transports a field derivation identity
back to an identity of entire regular Taylor series. -/
lemma origin_chainRule_of_affine (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 _) [IsIntegral (genericScheme k M)] (δ : Frame k M)
    (E : (genericScheme k M).functionField →+* Iterated k)
    (κ : OriginStalk k M s hs →+* PowerSeries (LaurentSeries k))
    (hκ : IsOriginTaylor k M s hs E κ)
    (W : (genericScheme k M).Opens) (hW : IsAffineOpen W) [Nonempty W]
    (hzero : ∀ a, expansionDefect (C := genericScheme k M) (genericStructure k M) δ E
      (laurentLogAdd (LaurentSeries k)) W a = 0)
    (U : (genericScheme k M).Opens)
    (hx : Origin k M s hs (IsLocalRing.closedPoint (LaurentSeries k)) ∈ U)
    (a : (genericScheme k M).presheaf.obj (Opposite.op U)) :
    κ ((genericScheme k M).presheaf.germ U _ hx (frameDerivative k M δ U a)) =
      (1 + PowerSeries.X) * PowerSeries.derivative (LaurentSeries k)
        (κ ((genericScheme k M).presheaf.germ U _ hx a)) := by
  letI : Nonempty U := ⟨⟨_,hx⟩⟩
  have hh := expansionDefect_zero_of_affine (C := genericScheme k M) (genericStructure k M) δ E
    (laurentLogAdd (LaurentSeries k))
    (laurentLogAdd_mul (LaurentSeries k)) W hW hzero U a
  change sectionExpansion E U (frameDerivative k M δ U a) -
    laurentLogAdd (LaurentSeries k) (sectionExpansion E U a) = 0 at hh
  rw [sub_eq_zero] at hh
  have ht (b : (genericScheme k M).presheaf.obj (Opposite.op U)) :
      algebraMap (PowerSeries (LaurentSeries k)) (Iterated k)
        (κ ((genericScheme k M).presheaf.germ U _ hx b)) = sectionExpansion E U b := by
    have h := hκ.1 ((genericScheme k M).presheaf.germ U _ hx b)
    rw [Scheme.algebraMap_germ_eq_germToFunctionField] at h
    exact h
  apply IsFractionRing.injective (PowerSeries (LaurentSeries k)) (Iterated k)
  rw [ht, ← logDerivative_apply, ← laurentLogAdd_powerSeries, ht]
  exact hh
/-- The chart-field Taylor map fixes the entire Laurent coefficient field,
through the accepted structural inclusion. -/
lemma taylor_laurent_scalar (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ) :
    Ψ.comp (CompletedChartFieldMaps.laurentInclusion k) = HahnSeries.C := by
  apply IsFractionRing.ringHom_ext (A := PowerSeries k)
  intro b
  change Ψ (CompletedChartFieldMaps.laurentInclusion k
    (algebraMap (PowerSeries k) (LaurentSeries k) b)) = _
  rw [CompletedChartFieldMaps.laurentInclusion_base]
  rw [show Ψ (chartToField k (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)) =
      toIterated k (σ (ArithmeticThetaAnnularTorsionPrereqR0053.base k b)) from
    RingHom.congr_fun hΨ _]
  rw [hσ.1]
  simp only [toIterated, RingHom.comp_apply, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
  rfl

lemma taylor_field_scalar (M : Model k T) [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : χ ≫ M.p = chartBase k)
    (φ : (genericScheme k M).functionField →+* ChartField k)
    (hφ : IsChartFieldMap k M χ φ)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ)
    (c : LaurentSeries k) :
    (Ψ.comp φ) (ArithmeticThetaGeometricNormR0150.baseScalar
      (X := genericScheme k M) (LaurentSeries k) (genericStructure k M) c) = HahnSeries.C c := by
  change Ψ (φ _) = _
  rw [CompletedChartFieldMaps.fieldMap_scalar k M χ hχ φ hφ]
  exact RingHom.congr_fun (taylor_laurent_scalar k σ hσ Ψ hΨ) c
end OriginTransport

section CompletedGeometricNumerators
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaPolygonCartierR0133
open GlobalCartierIdealLineR0133 CanonicalCartierLineReductionR0133
open ArithmeticThetaAlgebraizedMarkedLineR0136.AlgebraizedPositiveFormalSectionsR0136
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144

lemma principal_pullback_witness {X Y : Scheme} [IsAffine X] (f : X ⟶ Y)
    (I : Y.IdealSheafData) (hI : I.IsInvertible) (h : Γ(X,⊤))
    (hreg : IsRegular h)
    (hJ : (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {h}) :
    ∃ z : Γ((Scheme.Modules.pullback f).obj I.module, ⊤),
      (pulledInclusion f I.moduleι).app ⊤ z = h := by
  have hinv : (I.comap f).IsInvertible := effective_invertible _ (by
    intro x
    exact ⟨⟨⊤, isAffineOpen_top X⟩, trivial, h, hreg, hJ⟩)
  let e := idealPullbackIso f I (I.comap f) hI hinv rfl
  have hmem : h ∈ (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [hJ]
    exact Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨z,hz⟩ : ∃ z : Γ((I.comap f).module,⊤), (I.comap f).moduleι.app ⊤ z = h := by
    have he := (ideal_realization (I.comap f)).2 ⟨⊤, isAffineOpen_top X⟩
    exact (Set.ext_iff.mp he h).mpr hmem
  refine ⟨e.inv.app ⊤ z, ?_⟩
  have he : e.inv ≫ pulledInclusion f I.moduleι = (I.comap f).moduleι := by
    change e.inv ≫ ((Scheme.Modules.pullback f).map I.moduleι ≫ unitPullback f) = _
    rw [← idealPullbackIso_inclusion f I (I.comap f) hI hinv rfl]
    exact e.inv_hom_id_assoc _
  change (e.inv ≫ pulledInclusion f I.moduleι).app ⊤ z = h
  rw [he]
  exact hz

def completedIdentityEquation : Chart k := 1 - ArithmeticThetaAnnularTorsionPrereqR0053.cx k

lemma completedIdentityEquation_reduction (n : ℕ) {r : ℕ} {hr : 0 < r} (h3 : 3 ≤ r) :
    reduction k n (completedIdentityEquation k) = equation k r n (zeroIndex r hr) := by
  simp [completedIdentityEquation, reduction_x, equation, zeroIndex, show 1 ≠ r by omega]

variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

local instance chartScheme_affine : IsAffine (chartScheme k) :=
  inferInstanceAs (IsAffine (Spec (.of (Chart k))))

lemma completed_identity_principal (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ) :
    IsRegular ((Scheme.ΓSpecIso (.of (Chart k))).inv (completedIdentityEquation k)) ∧
    (s.ker.comap χ).ideal ⟨⊤, isAffineOpen_top (chartScheme k)⟩ =
      Ideal.span {(Scheme.ΓSpecIso (.of (Chart k))).inv (completedIdentityEquation k)} := by
  obtain ⟨hI, hreg⟩ := completed_marked_chart_ideal k r hr h3 T M hM
    (zeroIndex r hr) (zeroIndex r hr) 1 s hs χ hχ
  have heq : markedEquation k (hr := hr) (zeroIndex r hr) (zeroIndex r hr) 1 =
      -(completedIdentityEquation k) := by
    simp only [markedEquation, ite_true,
      if_neg (CompletedMarkedChartIdealR0152.next_ne hr h3 (zeroIndex r hr)),
      Units.val_one, map_one, mul_one, completedIdentityEquation]
    ring
  rw [heq] at hI hreg
  rw [Ideal.span_singleton_neg] at hI
  let e := (Scheme.ΓSpecIso (.of (Chart k))).commRingCatIsoToRingEquiv
  have hreg' : IsRegular (completedIdentityEquation k) := by
    simpa only [neg_one_mul, neg_neg] using isUnit_neg_one.isRegular.mul hreg
  refine ⟨regular_equiv e.symm hreg', ?_⟩
  have hh := congrArg (Ideal.map e.symm.toRingHom) hI
  change Ideal.map e.symm.toRingHom
    (Ideal.map e.toRingHom ((s.ker.comap χ).ideal ⟨⊤, isAffineOpen_top (chartScheme k)⟩)) = _ at hh
  simpa only [Ideal.map_map, RingEquiv.symm_toRingHom_comp_toRingHom,
    Ideal.map_id, Ideal.map_span, Set.image_singleton] using! hh

lemma completed_identity_power_witness (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ) (d : ℕ) :
    ∃ z : Γ((Scheme.Modules.pullback χ).obj (powerModule k M s d), ⊤),
      (pulledInclusion χ (idealInclusion (s.ker^d))).app ⊤ z =
        (Scheme.ΓSpecIso (.of (Chart k))).inv (completedIdentityEquation k ^ d) := by
  obtain ⟨hreg,hI⟩ := completed_identity_principal k h3 M hM s hs χ hχ
  apply principal_pullback_witness χ (s.ker^d)
    (AlgebraizedThetaSectionsR0138.power_invertible k h3 M hM s hs d)
  · simpa only [map_pow] using hreg.pow d
  · rw [comap_power, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, hI,
      Ideal.span_singleton_pow, map_pow]
    rfl
lemma comp_pull_witness {A B C : Scheme} (f : A ⟶ B) (g : B ⟶ C)
    (c : A ⟶ C) (hc : f ≫ g = c) (L : C.Modules)
    (j q : L ⟶ (SheafOfModules.unit C.ringCatSheaf : C.Modules))
    (a b : Γ(B,⊤))
    (hz : ∃ z : Γ((Scheme.Modules.pullback g).obj L,⊤),
      (pulledInclusion g j).app ⊤ z = a ∧ (pulledInclusion g q).app ⊤ z = b) :
    ∃ z : Γ((Scheme.Modules.pullback c).obj L,⊤),
      (pulledInclusion c j).app ⊤ z = f.appTop a ∧
        (pulledInclusion c q).app ⊤ z = f.appTop b := by
  apply (witness_iso (compIso f g c hc L)
    (pulledInclusion f (pulledInclusion g j)) (pulledInclusion f (pulledInclusion g q))
    (pulledInclusion c j) (pulledInclusion c q)
    (compIso_inclusion f g c hc L j) (compIso_inclusion f g c hc L q) _ _).mp
  exact pull_witness f _ _ _ a b hz

lemma spec_map_section {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom f)).appTop ((Scheme.ΓSpecIso (.of A)).inv a) =
      (Scheme.ΓSpecIso (.of B)).inv (f a) :=
  (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)) a).symm

lemma completed_coordinate_reduction (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (odd : Bool) (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ)
    (z : Γ((Scheme.Modules.pullback χ).obj (powerModule k M s (degree odd)),⊤))
    (hz : (pulledInclusion χ (idealInclusion (s.ker^degree odd))).app ⊤ z =
      (Scheme.ΓSpecIso (.of (Chart k))).inv (completedIdentityEquation k ^ degree odd))
    (n : ℕ) :
    reduction k n ((Scheme.ΓSpecIso (.of (Chart k))).hom ((pulledInclusion χ φ).app ⊤ z)) =
      numerator k odd r n (zeroIndex r hr) := by
  let a : Chart k := (Scheme.ΓSpecIso (.of (Chart k))).hom ((pulledInclusion χ φ).app ⊤ z)
  have ha : (pulledInclusion χ φ).app ⊤ z = (Scheme.ΓSpecIso (.of (Chart k))).inv a :=
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (Chart k))).hom_inv_id _).symm
  obtain ⟨w,hw,hv⟩ := comp_pull_witness (Spec.map (CommRingCat.ofHom (reduction k n))) χ
    ((T.atlas n).chart (zeroIndex r hr) ≫ M.inclusion n) (hχ.2 n)
    (powerModule k M s (degree odd)) (idealInclusion (s.ker^degree odd)) φ _ _ ⟨z,hz,ha⟩
  rw [spec_map_section, map_pow, completedIdentityEquation_reduction k n (hr := hr) h3] at hw
  rw [spec_map_section] at hv
  obtain ⟨w',hw',hv'⟩ := hφ n (zeroIndex r hr)
  letI : Mono (pulledInclusion ((T.atlas n).chart (zeroIndex r hr) ≫ M.inclusion n)
      (idealInclusion (s.ker^degree odd))) :=
    CoordinateMarkedEvaluationR0143.chart_mono k h3 M hM s hs (degree odd) n (zeroIndex r hr)
  have he : w = w' := mono_app_injective
    (pulledInclusion ((T.atlas n).chart (zeroIndex r hr) ≫ M.inclusion n)
      (idealInclusion (s.ker^degree odd))) ⊤ (hw.trans hw'.symm)
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A k n))).inv).1
  exact hv.symm.trans (by rw [he]; exact hv')

lemma completed_coordinate_numerator (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (odd : Bool) (φ : Dual k M s (degree odd)) (hφ : RealizesCoordinate k odd M s φ) :
    ∃ (a : Chart k) (z : Γ((Scheme.Modules.pullback χ).obj (powerModule k M s (degree odd)),⊤)),
      (pulledInclusion χ (idealInclusion (s.ker^degree odd))).app ⊤ z =
        (Scheme.ΓSpecIso (.of (Chart k))).inv (completedIdentityEquation k ^ degree odd) ∧
      (pulledInclusion χ φ).app ⊤ z = (Scheme.ΓSpecIso (.of (Chart k))).inv a ∧
      ∀ n, reduction k n a = numerator k odd r n (zeroIndex r hr) := by
  obtain ⟨z,hz⟩ := completed_identity_power_witness k h3 M hM s hs χ hχ (degree odd)
  refine ⟨(Scheme.ΓSpecIso (.of (Chart k))).hom ((pulledInclusion χ φ).app ⊤ z), z, hz, ?_, ?_⟩
  · exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (Chart k))).hom_inv_id _).symm
  · exact completed_coordinate_reduction k h3 M hM s hs χ hχ odd φ hφ z hz
lemma stalk_open_appTop {X : Scheme} (U : X.Opens) (x : X) (hx : x ∈ U) :
    (U.fromSpecStalkOfMem x hx).appTop =
      U.topIso.hom ≫ X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  have hh := congrArg (fun f => f.appTop) (U.fromSpecStalkOfMem_toSpecΓ x hx)
  rw [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop] at hh
  have hn : (Spec.map (X.presheaf.germ U x hx)).appTop =
      (Scheme.ΓSpecIso Γ(X,U)).hom ≫ X.presheaf.germ U x hx ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  rw [hn] at hh
  apply (cancel_epi U.topIso.inv).mp
  apply (cancel_epi (Scheme.ΓSpecIso Γ(X,U)).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Iso.hom_inv_id_assoc] using hh

lemma pullback_scalar_equation {A B C D : Scheme} (f : A ⟶ B) (a : D ⟶ A)
    (g : C ⟶ B) (c : D ⟶ C) (h : a ≫ f = c ≫ g) (L : B.Modules)
    (j q : L ⟶ (SheafOfModules.unit B.ringCatSheaf : B.Modules)) (b : Γ(A,⊤))
    (hq : pulledInclusion f q = dualScale b (pulledInclusion f j)) :
    pulledInclusion (c ≫ g) q = dualScale (a.appTop b) (pulledInclusion (c ≫ g) j) := by
  apply (cancel_epi (compIso a f (c ≫ g) h L).hom).mp
  rw [compIso_inclusion, hq, pulled_dualScale]
  change pulledInclusion a (pulledInclusion f j) ≫ fromSection (SheafOfModules.unit D.ringCatSheaf : D.Modules) (a.appTop b) = _
  change _ = (compIso a f (c ≫ g) h L).hom ≫
    (pulledInclusion (c ≫ g) j ≫ fromSection (SheafOfModules.unit D.ringCatSheaf : D.Modules) (a.appTop b))
  rw [← Category.assoc, compIso_inclusion]

open ArithmeticThetaGenericEvaluationR0140

lemma completed_coordinate_field_equation (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (φ : (genericScheme k M).functionField →+* ChartField k) (hφ : IsChartFieldMap k M χ φ)
    (d : ℕ) (q : Dual k M s d) (a : Chart k)
    (z : Γ((Scheme.Modules.pullback χ).obj (powerModule k M s d),⊤))
    (hz : (pulledInclusion χ (idealInclusion (s.ker^d))).app ⊤ z =
      (Scheme.ΓSpecIso (.of (Chart k))).inv (completedIdentityEquation k ^ d))
    (ha : (pulledInclusion χ q).app ⊤ z = (Scheme.ΓSpecIso (.of (Chart k))).inv a) :
    letI : Nonempty (complement k M s) := complement_nonempty k h3 M hM s hs
    chartToField k a =
      φ ((genericScheme k M).germToFunctionField (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s d q))) *
        chartToField k (completedIdentityEquation k) ^ d := by
  let W := complement k M s
  let C := genericScheme k M
  letI : Nonempty W := complement_nonempty k h3 M hM s hs
  have hη : _root_.genericPoint C ∈ W :=
    ((genericPoint_spec C).mem_open_set_iff W.isOpen).mpr (by
      simpa only [Set.univ_inter] using (Set.nonempty_coe_sort.mp (inferInstance : Nonempty W)))
  let f : Spec (.of (ChartField k)) ⟶ W.toScheme :=
    Spec.map (CommRingCat.ofHom φ) ≫ W.fromSpecStalkOfMem (_root_.genericPoint C) hη
  let g : Spec (.of (ChartField k)) ⟶ chartScheme k := Spec.map (CommRingCat.ofHom (chartToField k))
  have hsq : f ≫ complementInclusion k M s = g ≫ χ := by
    change (Spec.map (CommRingCat.ofHom φ) ≫ W.fromSpecStalkOfMem _ hη) ≫
      (W.ι ≫ genericInclusion k M) = _
    rw [Category.assoc, ← Category.assoc (W.fromSpecStalkOfMem _ hη),
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact hφ
  have hq : pulledInclusion (complementInclusion k M s) q =
      dualScale (complementCoordinate k M s d q)
        (pulledInclusion (complementInclusion k M s) (idealInclusion (s.ker^d))) := by
    apply Scheme.Modules.hom_ext
    intro U
    ext v
    exact (complementCoordinate_spec k M s d q U v).trans (dualScale_app _ _ U v).symm
  have hqs := pullback_scalar_equation (complementInclusion k M s) f χ g hsq
    (powerModule k M s d) (idealInclusion (s.ker^d)) q _ hq
  obtain ⟨w,hw,hv⟩ := comp_pull_witness g χ (g ≫ χ) rfl (powerModule k M s d)
    (idealInclusion (s.ker^d)) q _ _ ⟨z,hz,ha⟩
  have hv' := dualScale_app (f.appTop (complementCoordinate k M s d q))
    (pulledInclusion (g ≫ χ) (idealInclusion (s.ker^d))) ⊤ w
  erw [← hqs] at hv'
  simp only [homOfLE_refl, op_id] at hv'
  have hid : (Spec (.of (ChartField k))).presheaf.map (𝟙 (Opposite.op ⊤)) = 𝟙 _ :=
    (Spec (.of (ChartField k))).presheaf.map_id _
  rw [hid] at hv'
  erw [hw, hv] at hv'
  have hf : f.appTop (complementCoordinate k M s d q) =
      (Scheme.ΓSpecIso (.of (ChartField k))).inv
        (φ (C.germToFunctionField W (W.topIso.hom (complementCoordinate k M s d q)))) := by
    simp only [f, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply,
      stalk_open_appTop]
    exact spec_map_section φ _
  rw [hf] at hv'
  change g.appTop ((Scheme.ΓSpecIso (.of (Chart k))).inv a) = _ at hv'
  erw [spec_map_section, spec_map_section] at hv'
  change (Scheme.ΓSpecIso (.of (ChartField k))).inv (chartToField k a) =
    (Scheme.ΓSpecIso (.of (ChartField k))).inv
      (φ (C.germToFunctionField W (W.topIso.hom (complementCoordinate k M s d q)))) *
    (Scheme.ΓSpecIso (.of (ChartField k))).inv (chartToField k (completedIdentityEquation k ^ d)) at hv'
  erw [map_pow, ← map_mul] at hv' 
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (ChartField k))).inv).1 hv'
end CompletedGeometricNumerators

section ExpandedCoordinates
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma toIterated_injective : Function.Injective (toIterated k) :=
by
  intro a b h
  apply PowerSeries.map_injective (HahnSeries.ofPowerSeries ℤ k)
    (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := k))
  exact HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := LaurentSeries k) h

lemma laurentLogAdd_toIterated (a : Bivariate k) :
    laurentLogAdd (LaurentSeries k) (toIterated k a) =
      toIterated k (logDerivative (PowerSeries k) a) := by
  change laurentLogAdd (LaurentSeries k)
    (algebraMap (PowerSeries (LaurentSeries k)) (Iterated k)
      (PowerSeries.map (HahnSeries.ofPowerSeries ℤ k) a)) = _
  rw [laurentLogAdd_powerSeries, ← logDerivative_map]
  rfl

lemma laurentLogAdd_cleared (K : Type) [Field K] (h a b : LaurentSeries K) (hh : h ≠ 0)
    (he : h * laurentLogAdd K a - 2*a*laurentLogAdd K h = 2*b) :
    laurentLogAdd K (a/h^2) = 2*(b/h^3) := by
  have hmul : a = (a / h^2) * (h*h) := by field_simp
  have hd := congrArg (laurentLogAdd K) hmul
  rw [laurentLogAdd_mul, laurentLogAdd_mul] at hd
  apply (mul_right_cancel₀ (pow_ne_zero 3 hh))
  field_simp
  field_simp at hd
  linear_combination he - hd

lemma completed_equation_expansion (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    σ (completedIdentityEquation k) = -PowerSeries.X := by
  rw [completedIdentityEquation, map_sub, map_one, hσ.2.1]
  ring

lemma completed_equation_expansion_ne (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ) :
    toIterated k (σ (completedIdentityEquation k)) ≠ 0 := by
  rw [completed_equation_expansion k σ hσ]
  intro H
  have hh := toIterated_injective k (H.trans (map_zero _).symm)
  exact PowerSeries.X_ne_zero (neg_eq_zero.mp hh)

lemma expanded_x_derivative (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (φ : (genericScheme k M).functionField →+* ChartField k) (hφ : IsChartFieldMap k M χ φ)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y) :
    letI : Nonempty (complement k M s) := complement_nonempty k h3 M hM s hs
    laurentLogAdd (LaurentSeries k) (sectionExpansion (Ψ.comp φ) (complement k M s)
      ((complement k M s).topIso.hom (complementCoordinate k M s 2 X))) =
      2 * sectionExpansion (Ψ.comp φ) (complement k M s)
        ((complement k M s).topIso.hom (complementCoordinate k M s 3 Y)) := by
  letI : Nonempty (complement k M s) := complement_nonempty k h3 M hM s hs
  obtain ⟨a,z,hz,ha,har⟩ := completed_coordinate_numerator k h3 M hM s hs χ hχ false X hX
  obtain ⟨b,w,hw,hb,hbr⟩ := completed_coordinate_numerator k h3 M hM s hs χ hχ true Y hY
  have he := completed_numerator_identity k r h3 (zeroIndex r hr) σ hσ
    (completedIdentityEquation k) a b
    (fun n => completedIdentityEquation_reduction k n (hr := hr) h3) har hbr
  have hd := congrArg (toIterated k) he
  simp only [map_sub, map_mul, map_ofNat, ← laurentLogAdd_toIterated] at hd
  have hh := completed_equation_expansion_ne k σ hσ
  have hquot := laurentLogAdd_cleared (LaurentSeries k) _ _ _ hh hd
  have hx := congrArg Ψ (completed_coordinate_field_equation k h3 M hM s hs χ hχ φ hφ 2 X a z hz ha)
  have hy := congrArg Ψ (completed_coordinate_field_equation k h3 M hM s hs χ hχ φ hφ 3 Y b w hw hb)
  have ht (v : Chart k) : Ψ (chartToField k v) = toIterated k (σ v) := RingHom.congr_fun hΨ v
  simp only [map_mul, map_pow, ht] at hx hy
  have hx' : sectionExpansion (Ψ.comp φ) (complement k M s)
      ((complement k M s).topIso.hom (complementCoordinate k M s 2 X)) =
      toIterated k (σ a) / toIterated k (σ (completedIdentityEquation k))^2 :=
    (eq_div_iff (pow_ne_zero 2 hh)).mpr hx.symm
  have hy' : sectionExpansion (Ψ.comp φ) (complement k M s)
      ((complement k M s).topIso.hom (complementCoordinate k M s 3 Y)) =
      toIterated k (σ b) / toIterated k (σ (completedIdentityEquation k))^3 :=
    (eq_div_iff (pow_ne_zero 3 hh)).mpr hy.symm
  rw [hx',hy']
  exact hquot
end ExpandedCoordinates

section AffineComparison
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaOriginInitialR0161
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaCompactifiedDifferentialR0145
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open ArithmeticThetaHodgeFourTorsionR0147
open ArithmeticThetaHodgeFourTorsionR0147.InverseDifferentialSign
open ArithmeticThetaGeometricNormR0150
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

lemma germ_scalar {F : Type} [Field F] {C : Scheme} [IsIntegral C]
    (p : C ⟶ Spec (.of F)) (U : C.Opens) [Nonempty U] (c : F) :
    C.germToFunctionField U ((p.constToPresheaf.app (Opposite.op U)).hom c) =
      baseScalar F p c := by
  letI : Nonempty (⊤ : C.Opens) := ⟨⟨_root_.genericPoint C, trivial⟩⟩
  have hr : C.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      ((p.constToPresheaf.app (Opposite.op ⊤)).hom c) =
      (p.constToPresheaf.app (Opposite.op U)).hom c :=
    (ConcreteCategory.congr_hom (p.constToPresheaf.naturality (homOfLE le_top).op) c).symm
  rw [← hr]
  simp only [Scheme.germToFunctionField, C.presheaf.germ_res_apply, ArithmeticThetaGeometricNormR0150.baseScalar]
  congr 1
  change p.appLE ⊤ ⊤ le_top ((Scheme.ΓSpecIso (.of F)).inv c) =
    p.appTop ((Scheme.ΓSpecIso (.of F)).inv c)
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]

lemma expanded_affine_defect_zero (h3 : 3 ≤ r) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    [IsIntegral (genericScheme k M)]
    (χ : chartScheme k ⟶ M.X) (hχ : IsChartMap k M (zeroIndex r hr) χ)
    (φ : (genericScheme k M).functionField →+* ChartField k) (hφ : IsChartFieldMap k M χ φ)
    (σ : Chart k →+* Bivariate k) (hσ : IsChartTaylor k σ)
    (Ψ : ChartField k →+* Iterated k) (hΨ : ExtendsTaylor k σ Ψ)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y)
    (e : Frame k M) (heN : IsGlobalDifferentialFrame k M s X Y e) :
    letI : Nonempty (complement k M s) := complement_nonempty k h3 M hM s hs
    ∀ a, expansionDefect (C := genericScheme k M) (genericStructure k M) e (Ψ.comp φ)
      (laurentLogAdd (LaurentSeries k)) (complement k M s) a = 0 := by
  let C := genericScheme k M
  let p : C ⟶ Spec (.of (LaurentSeries k)) := genericStructure k M
  let W := complement k M s
  letI : Nonempty W := complement_nonempty k h3 M hM s hs
  let E := Ψ.comp φ
  let D := laurentLogAdd (LaurentSeries k)
  obtain ⟨a,ha',_⟩ := generic_affine_cubic_isomorphism k r hr h3 T he M hM s hs X Y hX hY
  let q : CubicRing k r →+* Γ(C,W) := W.topIso.hom.hom.comp
    (a.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of (CubicRing k r))).inv.hom)
  have hq (odd : Bool) : q (cubicCoordinate k r odd) =
      W.topIso.hom (complementCoordinate k M s (degree odd) (match odd with | true => Y | false => X)) :=
    congrArg W.topIso.hom (ArithmeticThetaMarkedGroupLawR0146.ActualInverseComparison.coordinateIso_values k M s X Y a ha' odd)
  have hqc (c : LaurentSeries k) : q (algebraMap _ _ c) =
      (p.constToPresheaf.app (Opposite.op W)).hom c := by
    change W.topIso.hom (a.hom.appTop ((Scheme.ΓSpecIso (.of (CubicRing k r))).inv
      (algebraMap _ _ c))) = _
    rw [← spec_constant]
    have ht : a.hom.appTop = a.hom.appLE ⊤ ⊤ le_top := by
      simp [Scheme.Hom.appTop, Scheme.Hom.appLE]
    rw [ht]
    erw [appLE_constant]
    change W.topIso.hom (((a.hom ≫ cubicStructure k r).constToPresheaf.app (Opposite.op ⊤)).hom c) = _
    rw [ha'.1]
    exact topIso_constant p W c
  have hc (c : LaurentSeries k) :
      expansionDefect p e E D W ((p.constToPresheaf.app (Opposite.op W)).hom c) = 0 := by
    change sectionExpansion E W (coefficient p e W _) - D (sectionExpansion E W _) = 0
    rw [coefficient_constant, map_zero]
    have hv : sectionExpansion E W ((p.constToPresheaf.app (Opposite.op W)).hom c) = HahnSeries.C c := by
      change E (C.germToFunctionField W _) = _
      rw [germ_scalar]
      exact taylor_field_scalar k M χ hχ.1 φ hφ σ hσ Ψ hΨ c
    rw [hv]
    change 0 - laurentLogDerivative (LaurentSeries k) (HahnSeries.C c) = 0
    rw [laurentLogDerivative_C, sub_self]
  have hx : coefficient p e W (q (cubicCoordinate k r false)) = 2*q (cubicCoordinate k r true) := by
    rw [hq false, hq true]
    exact coefficient_normalization p e W _ _ (normalization_from_predicate k M s X Y e heN)
  have hex : expansionDefect p e E D W (q (cubicCoordinate k r false)) = 0 := by
    change sectionExpansion E W (coefficient p e W _) - D (sectionExpansion E W _) = 0
    rw [hx, map_mul, map_ofNat, hq false, hq true]
    exact sub_eq_zero.mpr (expanded_x_derivative k h3 M hM s hs χ hχ φ hφ σ hσ Ψ hΨ X Y hX hY).symm
  let f := (sectionExpansion E W).comp q
  have hy : f (2*cubicCoordinate k r true) ≠ 0 := by
    have hy0 : q (cubicCoordinate k r true) ≠ 0 := by
      rw [hq true]
      exact complement_y_nonzero k h3 he M hM s hs X Y hX hY
    have h2 : (2 : Γ(C,W)) ≠ 0 := by
      letI : CharZero (LaurentSeries k) := LaurentSeries.XAdic.charZero k
      have hu : IsUnit (2 : Γ(C,W)) := by
        simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (by norm_num : (2 : LaurentSeries k) ≠ 0)).map
          ((p.constToPresheaf.app (Opposite.op W)).hom)
      exact hu.ne_zero
    intro H
    have HH : q (2*cubicCoordinate k r true) = 0 := by
      apply C.germToFunctionField_injective W
      apply E.injective
      change E (C.germToFunctionField W (q (2*cubicCoordinate k r true))) = 0 at H
      simpa only [map_zero] using H
    rw [map_mul, map_ofNat] at HH
    exact (mul_ne_zero h2 hy0) HH
  have hall := cubic_twisted_ext k r f ((expansionDefect p e E D W).comp q.toAddMonoidHom)
    (fun b c => by
      change expansionDefect p e E D W (q (b*c)) = _
      rw [map_mul]
      exact expansionDefect_mul p e E D (laurentLogAdd_mul (LaurentSeries k)) W (q b) (q c))
    (fun c => by
      change expansionDefect p e E D W (q (algebraMap _ _ c)) = 0
      rw [hqc]
      exact hc c) hex hy
  intro z
  have hsurj : Function.Surjective q :=
    (ConcreteCategory.bijective_of_isIso W.topIso.hom).2.comp
      ((ConcreteCategory.bijective_of_isIso a.hom.appTop).2.comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (CubicRing k r))).inv).2)
  obtain ⟨b,rfl⟩ := hsurj z
  exact hall b
end AffineComparison

end ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163

#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.finite_deriv_naturality
#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.taylor_reduction
#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.completed_numerator_identity

#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.laurentLogDerivative_powerSeries

#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.expansionDefect_zero_of_affine

#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.origin_chainRule_of_affine

#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.taylor_field_scalar

#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.completed_coordinate_numerator

#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.completed_coordinate_field_equation

#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.expanded_x_derivative

#print axioms ArithmeticThetaHodgeInitialR0163.OriginLogarithmicTaylorR0163.expanded_affine_defect_zero

namespace ArithmeticThetaHodgeInitialR0163
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaOriginInitialR0161
open ArithmeticThetaCubicModelR0144
open ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaCompactifiedDifferentialR0145.GlobalNormalizedDifferential
open OriginLogarithmicTaylorR0163

/-- The normalized geometric frame acts on every actual regular Taylor
expansion as (1+u)d/du, as an identity of entire power series. -/
theorem origin_logarithmic_taylor :
∀ (k : Type) [Field k] [CharZero k] (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) [AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] [AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)], ∀ (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∀ (δ : ArithmeticThetaHodgeFourTorsionR0147.Frame k M), ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y δ → ArithmeticThetaHodgeInitialR0163.LogarithmicTaylor k M s hs.1 δ := by
  intro k _ _ r hr h3 he T M hM s hs G hG _ _ X Y hX hY δ hδ
  intro ε κ hκ U hx a
  obtain ⟨_, χ, φ, σ, Ψ, hχ, hφ, hσ, hΨ, hκ⟩ := hκ
  let j := ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr
  letI : Nonempty (complement k M s) := complement_nonempty k h3 M hM s hs
  exact origin_chainRule_of_affine k M s hs.1 δ (Ψ.comp (φ j)) κ hκ
    (complement k M s) (complement_isAffineOpen k h3 M hM s hs X hX)
    (expanded_affine_defect_zero k h3 he M hM s hs (χ j) (hχ j) (φ j) (hφ j)
      σ hσ Ψ hΨ X Y hX hY δ hδ) U hx a
end ArithmeticThetaHodgeInitialR0163

#print axioms ArithmeticThetaHodgeInitialR0163.origin_logarithmic_taylor
