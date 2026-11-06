module

public import RelativeWeierstrassPresentationR0174

@[expose] public section

/-! Actual elliptic families and local presentations for arbitrary rational bases.
Only semantic definitions are introduced; all existence assertions are targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLocalWeierstrassR0203
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open scoped TensorProduct
abbrev Base (R : Type u) [CommRing R] := Spec (CommRingCat.of R)
abbrev FramedCurve (R : Type u) [CommRing R] :=
  ArithmeticThetaCyclicPresentationR0174.RelativeWeierstrassPresentationR0174.FramedCurve R

/-- Cohomology of the actual inverse identity ideal, with its structural scalar action. -/
def PositiveCohomology (R : Type u) [CommRing R] (Q : FramedCurve R) : Prop :=
  ∀ (m : ℕ), 0 < m →
    let f := Q.structureMap
    let M := (Q.zero.ker ^ m).invModule
    (letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
     Module.Finite R Γ(M, ⊤) ∧ Module.Projective R Γ(M, ⊤)) ∧
    (∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
        ((pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤)
      ∃ e : A ⊗[R] Γ(M, ⊤) ≃ₗ[A]
          Γ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A))).obj M,
            (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ ⊤),
        ∀ (a : A) (x : Γ(M, ⊤)),
          e (a ⊗ₜ[R] x) = a • Scheme.Modules.pullbackLocalSection
            (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R A)) x) ∧
    (∀ (𝒰 : Q.target.OrderedAffineCover) (i : ℕ),
      Subsingleton ((OModulePresheaf.ofModules f M).HSucc 𝒰 i)) ∧
    (∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
      FiniteDimensional K (K ⊗[R] Γ(M, ⊤)) ∧
      Module.finrank K (K ⊗[R] Γ(M, ⊤)) = m)

/-- Bases and the actual restriction to the identity, including degree one. -/
def PositiveFiltration (R : Type u) [CommRing R] (Q : FramedCurve R) : Prop :=
  ∀ (m : ℕ), 0 < m →
    (let M := (Q.zero.ker ^ m).invModule
     letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom Q.structureMap M ⊤
     Nonempty (Module.Basis (Fin m) R Γ(M, ⊤))) ∧
    Function.Surjective (Scheme.Modules.pullbackLocalSection Q.zero
      (L := (Q.zero.ker ^ (m+1)).invModule) (U := ⊤))

/-- Finite-type descent of the actual framed group curve, not a chosen equation. -/
structure FramedApproximation (R : Type u) [CommRing R] [Algebra ℚ R]
    (Q : FramedCurve R) where
  ring : Type u
  [commRing : CommRing ring]
  [rational : Algebra ℚ ring]
  finiteType : Algebra.FiniteType ℚ ring
  scalar : ring →ₐ[ℚ] R
  model : FramedCurve ring
  comparison : Q.target ⟶ model.target
  cartesian : IsPullback comparison Q.structureMap model.structureMap
    (Spec.map (CommRingCat.ofHom scalar.toRingHom))
  zero_eq : Q.zero ≫ comparison =
    Spec.map (CommRingCat.ofHom scalar.toRingHom) ≫ model.zero
  mul_eq : ∀ (T : Scheme.{u}) (t : T ⟶ Base R)
    (x y : SchemeHomOver t Q.structureMap)
    (x' y' : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom scalar.toRingHom))
      model.structureMap),
    x'.val = x.val ≫ comparison → y'.val = y.val ≫ comparison →
    (model.law.mul _ x' y').val = (Q.law.mul t x y).val ≫ comparison

/-- A natural commutative group law on all scheme-valued points over any base. -/
structure SchemeLaw {S X : Scheme.{u}} (p : X ⟶ S) where
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ S),
    SchemeHomOver t p → SchemeHomOver t p → SchemeHomOver t p
  one : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t p
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ S), SchemeHomOver t p → SchemeHomOver t p
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y z : SchemeHomOver t p),
    mul t (mul t x y) z = mul t x (mul t y z)
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p), mul t (one t) x = x
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p), mul t x (one t) = x
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x : SchemeHomOver t p),
    mul t (inv t x) x = one t
  mul_comm : ∀ {T : Scheme.{u}} (t : T ⟶ S) (x y : SchemeHomOver t p), mul t x y = mul t y x
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ S) (t' : T' ⟶ S)
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x y : SchemeHomOver t p),
    GoodReductionJacobian.schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ y)

/-- A smooth proper one-dimensional commutative group scheme with connected fibres. -/
structure Family (S : Scheme.{u}) where
  curve : Scheme.{u}
  p : curve ⟶ S
  law : SchemeLaw p
  proper : IsProper p
  dimension : SmoothOfRelativeDimension 1 p
  connected : GeometricallyConnected p

def Family.zero {S : Scheme.{u}} (E : Family S) : S ⟶ E.curve :=
  (E.law.one (𝟙 S)).val

/-- An actual open affine presentation, with all test-point multiplication preserved. -/
structure LocalPresentation (k : Type u) [Field k] (S : Scheme.{u})
    (σ : S ⟶ Base k) (E : Family S) where
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra k ring]
  equation : WeierstrassCurve ring
  elliptic : equation.IsElliptic
  base : Base ring ⟶ S
  openImmersion : IsOpenImmersion base
  base_eq : base ≫ σ = Spec.map (CommRingCat.ofHom (algebraMap k ring))
  comparison : ArithmeticThetaRelativeKatoR0169.Curve ring equation ⟶ E.curve
  cartesian : IsPullback comparison (ArithmeticThetaRelativeKatoR0169.structureMap ring equation)
    E.p base
  zero_eq : ArithmeticThetaRelativeKatoR0169.origin ring equation ≫ comparison = base ≫ E.zero
  law : ArithmeticThetaRelativeKatoR0169.Law ring equation
  originLaw : ArithmeticThetaRelativeKatoR0169.IsOriginLaw ring equation law
  mul_eq : ∀ (T : Scheme.{u}) (t : T ⟶ Base ring)
    (x y : SchemeHomOver t (ArithmeticThetaRelativeKatoR0169.structureMap ring equation))
    (x' y' : SchemeHomOver (t ≫ base) E.p),
    x'.val = x.val ≫ comparison → y'.val = y.val ≫ comparison →
    (E.law.mul _ x' y').val = (law.mul t x y).val ≫ comparison

end ArithmeticThetaLocalWeierstrassR0203
