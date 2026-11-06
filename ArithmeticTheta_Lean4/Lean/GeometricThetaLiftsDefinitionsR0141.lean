import GenericProjectiveEvaluationR0140
import SchrodingerCommonScalarR0119
import AlgebraizedActionLawsR0137
import AlgebraizedMarkedTransportR0137

/-! Lifts are isomorphisms of the actual ideal-power sheaf, above the
specified generic-fiber maps. No lift or theta action is assumed to exist. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaGeometricLiftsR0141
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
open ArithmeticThetaIdentitySectionsR0138
open ArithmeticThetaGenericEvaluationR0140
open ArithmeticThetaModelSymmetriesR0137

variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}

def genericMap (M : Model k T) (f : M.X ⟶ M.X) (hf : f ≫ M.p = M.p) :
    genericScheme k M ⟶ genericScheme k M :=
  pullback.lift (genericInclusion k M ≫ f) (genericStructure k M) (by
    rw [Category.assoc, hf]
    exact pullback.condition)

def modelOver (M : Model k T) (perm : Fin r → Fin r) (a : kˣ) (flip : Bool)
    (f : M.X ≅ M.X) (h : ModelAction k M perm a flip f) : f.hom ≫ M.p = M.p :=
  h.choose_spec.2.1

def scalarMap (M : Model k T) (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X))
    (inv : M.X ≅ M.X) (ha : Actions k M rot scal inv) (ζ : kˣ) :
    genericScheme k M ⟶ genericScheme k M :=
  genericMap k M (scal ζ).hom (modelOver k M id ζ false (scal ζ) (ha.2.1 ζ))

def shiftMap (M : Model k T) (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X))
    (inv : M.X ≅ M.X) (ha : Actions k M rot scal inv) :
    genericScheme k M ⟶ genericScheme k M :=
  let g := genericMap k M rot.hom (modelOver k M (next r hr) 1 false rot ha.1)
  g ≫ g

def inversionMap (M : Model k T) (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X))
    (inv : M.X ≅ M.X) (ha : Actions k M rot scal inv) :
    genericScheme k M ⟶ genericScheme k M :=
  genericMap k M inv.hom (modelOver k M Fin.rev 1 true inv ha.2.2)

def Lift (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (f : genericScheme k M ⟶ genericScheme k M) :=
  genericPower k M s d ≅ (Scheme.Modules.pullback f).obj (genericPower k M s d)

def act (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (f : genericScheme k M ⟶ genericScheme k M) (e : Lift k M s d f)
    (φ : GenericDual k M s d) : GenericDual k M s d :=
  e.hom ≫ (Scheme.Modules.pullback f).map φ ≫
    ArithmeticThetaPolygonCartierR0133.unitPullback f

def phase (ζ : kˣ) (ν : ℕ) : LaurentSeries k :=
  algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C ((ζ : k)^ν))

def HasBasis (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (b : Fin m → GenericDual k M s d) : Prop :=
  ∀ φ : GenericDual k M s d, ∃! c : Fin m → LaurentSeries k,
    Combines k M s d m b c φ

def Eigen (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ)
    (ζ : kˣ) (f : genericScheme k M ⟶ genericScheme k M)
    (e : Lift k M s d f) (b : Fin m → GenericDual k M s d) : Prop :=
  ∀ ν : Fin m, ScaledEq k M s d (phase k ζ ν.val) (b ν) (act k M s d f e (b ν))

def Cyclic (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ) (hm : 0 < m)
    (f : genericScheme k M ⟶ genericScheme k M) (e : Lift k M s d f)
    (b : Fin m → GenericDual k M s d) : Prop :=
  ∀ ν : Fin m, act k M s d f e (b ν) = b (next m hm ν)

def Reverses (M : Model k T) (s : baseScheme k ⟶ M.X) (d m : ℕ) (hm : 0 < m)
    (f : genericScheme k M ⟶ genericScheme k M) (e : Lift k M s d f)
    (b : Fin m → GenericDual k M s d) : Prop :=
  ∀ ν : Fin m, act k M s d f e (b ν) = b (negIndex m hm ν)

def Relations (M : Model k T) (s : baseScheme k ⟶ M.X) (m : ℕ) (ζ : kˣ)
    (A B S : GenericDual k M s m → GenericDual k M s m) : Prop :=
  (∀ φ, (A^[m]) φ = φ) ∧ (∀ φ, (B^[m]) φ = φ) ∧
  (∀ φ, ScaledEq k M s m (phase k ζ 1) (B (A φ)) (A (B φ))) ∧
  (∀ φ, S (S φ) = φ) ∧ (∀ φ, S (A (S (A φ))) = φ) ∧
  (∀ φ, S (B (S (B φ))) = φ)

end ArithmeticThetaGeometricLiftsR0141
