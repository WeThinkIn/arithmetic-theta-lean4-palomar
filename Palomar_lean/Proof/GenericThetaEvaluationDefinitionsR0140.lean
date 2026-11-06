module

public import AlgebraizedThetaSaturationR0138
public import AlgebraizedThetaFaithfulnessR0138

@[expose] public section

/-! Actual generic-fiber dual sections and evaluation at the marked identity.
The scalar maps come from the specified structure morphisms. A frame is an
isomorphism of actual pulled-back sheaves; its normalization is tested at every
finite thickness on the actual extracted section numerators. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGenericEvaluationR0140
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaPolygonCartierR0133
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138

def thetaChartBound (m : ℕ) (hm : 0 < m) (he : Even m) : 3 ≤ 2*m := by
  obtain ⟨a, ha⟩ := he
  omega

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def genericScheme (M : Model k T) : Scheme.{u} := pullback M.p (genericBase k)

def genericInclusion (M : Model k T) : genericScheme k M ⟶ M.X :=
  pullback.fst M.p (genericBase k)

def genericPower (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ) :
    (genericScheme k M).Modules :=
  (Scheme.Modules.pullback (genericInclusion k M)).obj (powerModule k M s d)

def GenericDual (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ) :=
  genericPower k M s d ⟶
    (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules)

def restrictDual (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (φ : Dual k M s d) : GenericDual k M s d :=
  (Scheme.Modules.pullback (genericInclusion k M)).map φ ≫
    unitPullback (genericInclusion k M)

/-- The Laurent-series action is induced by the actual generic structure map. -/
def scalarAt (M : Model k T) (U : (genericScheme k M).Opens)
    (c : LaurentSeries k) : (genericScheme k M).presheaf.obj (Opposite.op U) :=
  (genericScheme k M).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    ((genericStructure k M).appTop ((Scheme.ΓSpecIso
      (CommRingCat.of (LaurentSeries k))).inv c))

def ScaledEq (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (c : LaurentSeries k) (φ ψ : GenericDual k M s d) : Prop :=
  ∀ (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)),
    scalarAt k M U c * (show (genericScheme k M).presheaf.obj (Opposite.op U) from φ.app U x) = ψ.app U x

def Combines (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) (c : Fin m → LaurentSeries k)
    (φ : GenericDual k M s d) : Prop :=
  ∀ (U : (genericScheme k M).Opens) (x : Γ(genericPower k M s d, U)),
    φ.app U x = ∑ ν : Fin m, scalarAt k M U (c ν) * (show (genericScheme k M).presheaf.obj (Opposite.op U) from (b ν).app U x)

def IdentityFrame (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ) :=
  (Scheme.Modules.pullback s).obj (powerModule k M s d) ≅
    (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules)

def frameValue (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (e : IdentityFrame k M s d) (φ : Dual k M s d) : PowerSeries k :=
  (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
    ((e.inv ≫ (Scheme.Modules.pullback s).map φ ≫ unitPullback s).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv 1))

def NormalizedFrame (h3 : 3 ≤ r) (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (d : ℕ) (e : IdentityFrame k M s d) : Prop :=
  ∀ (φ : Dual k M s d) (n : ℕ),
    trunc (PowerSeries k) PowerSeries.X n (frameValue k M s d e φ) =
      ArithmeticThetaPolygonCohomologyR0131.markedPoint k n 1
        (((AlgebraizedThetaSaturationR0138.algebraicFormal k h3 M hM s hs d φ).val n).val
          (zeroIndex r hr))

def commonUnit (m : ℕ) (hm : 0 < m) : (PowerSeries k)ˣ :=
  Units.map (ArithmeticThetaAnnularThetaR0128.specialize k 1)
    ((gammaTail k (2*m) (Nat.mul_pos (by decide) hm)
      (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)))⁻¹)^m

def thetaVector (m : ℕ) (ν : Fin m) : Fin m → PowerSeries k :=
  fun μ => if μ = ν then 1 else 0

def thetaSection (m : ℕ) (hm : 0 < m) (he : Even m)
    {T : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
    (M : Model k T) (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s)
    (ν : Fin m) : Dual k M s m :=
  Classical.choose (algebraized_theta_sections k m hm he T M hM s hs (thetaVector k m ν))

def genericTheta (m : ℕ) (hm : 0 < m) (he : Even m)
    {T : Tower k (2*m) (Nat.mul_pos (by decide) hm)}
    (M : Model k T) (hM : IsModel k T M) (s : baseScheme k ⟶ M.X)
    (hs : MarkedLift k M (zeroIndex (2*m) (Nat.mul_pos (by decide) hm)) 1 s)
    (ν : Fin m) : GenericDual k M s m :=
  restrictDual k M s m (thetaSection k m hm he M hM s hs ν)

def genericPoint (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) :
    Spec (CommRingCat.of (LaurentSeries k)) ⟶ genericScheme k M :=
  pullback.lift (genericBase k ≫ s) (𝟙 _) (by
    dsimp only [baseScheme] at hs ⊢
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

def GenericFrame (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (d : ℕ) :=
  (Scheme.Modules.pullback (genericPoint k M s hs)).obj (genericPower k M s d) ≅
    (SheafOfModules.unit (Spec (CommRingCat.of (LaurentSeries k))).ringCatSheaf :
      (Spec (CommRingCat.of (LaurentSeries k))).Modules)

def genericValue (M : Model k T) (s : baseScheme k ⟶ M.X)
    (hs : s ≫ M.p = 𝟙 (baseScheme k)) (d : ℕ)
    (e : GenericFrame k M s hs d) (φ : GenericDual k M s d) : LaurentSeries k :=
  (Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).hom
    ((e.inv ≫ (Scheme.Modules.pullback (genericPoint k M s hs)).map φ ≫
      unitPullback (genericPoint k M s hs)).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (LaurentSeries k))).inv 1))

end ArithmeticThetaGenericEvaluationR0140
