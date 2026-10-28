module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section elab "mX" : term => return Lean.mkConst (((((Lean.Name.num `_private.Lean.Meta.Match.Match 0).str "Lean").str "Meta").str "Match").str "matcherExt")
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace ArithmeticThetaNodeCharts
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
variable (k : Type u) [Field k]
abbrev Base := PowerSeries k
def parameter : Base k := PowerSeries.X
abbrev PolynomialChart := MvPolynomial (Fin 2) (Base k)
def relation : PolynomialChart k :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C (parameter k)
def relationIdeal : Ideal (PolynomialChart k) := Ideal.span {relation k}
abbrev Node := PolynomialChart k ⧸ relationIdeal k
instance (priority := 2000) nodeCommRing : CommRing (Node k) :=
  Ideal.Quotient.commRing (relationIdeal k)
def quotientMap : PolynomialChart k →+* Node k := Ideal.Quotient.mk (relationIdeal k)
def x : Node k := quotientMap k (MvPolynomial.X 0)
def y : Node k := quotientMap k (MvPolynomial.X 1)
def t : Node k := algebraMap (Base k) (Node k) (parameter k)
abbrev Torus := LaurentPolynomial (Base k)
def torusMap : PolynomialChart k →+* Torus k :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C
    (fun i => if i = (0 : Fin 2) then LaurentPolynomial.T 1
      else LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1))
def oppositeTorusMap : PolynomialChart k →+* Torus k :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C
    (fun i => if i = (0 : Fin 2) then
      LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)
      else LaurentPolynomial.T 1)
abbrev XChart := Localization.Away (x k)
abbrev YChart := Localization.Away (y k)
def toXChart : Node k →+* XChart k := algebraMap (Node k) (XChart k)
def toYChart : Node k →+* YChart k := algebraMap (Node k) (YChart k)
end ArithmeticThetaNodeCharts
namespace ArithmeticThetaNodeCharts
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
private theorem laurent_hom_ext {R S : Type*} [CommRing R] [CommRing S] {f g : LaurentPolynomial R →+* S} (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a)) (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT
variable (k : Type u) [Field k]
set_option backward.isDefEq.respectTransparency true in
private theorem coordinate_product (i j : Fin 2) (h : i ≠ j) : quotientMap k (MvPolynomial.X i) * quotientMap k (MvPolynomial.X j) = quotientMap k (MvPolynomial.C (parameter k)) := by
  have hr : quotientMap k (relation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hxy := sub_eq_zero.mp (show
    quotientMap k (MvPolynomial.X 0) * quotientMap k (MvPolynomial.X 1) -
      quotientMap k (MvPolynomial.C (parameter k)) = 0 by
        simpa [relation, map_sub, map_mul] using hr)
  fin_cases i <;> fin_cases j <;> simp_all [mul_comm]
set_option backward.isDefEq.respectTransparency true in
private theorem coordinate_chart (i : Fin 2) (f : PolynomialChart k →+* Torus k) (hC : ∀ a, f (MvPolynomial.C a) = LaurentPolynomial.C a) (hX : ∀ j, f (MvPolynomial.X j) = if j = i then LaurentPolynomial.T 1 else LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)) : ∃! e : Localization.Away (quotientMap k (MvPolynomial.X i)) ≃+* Torus k, e.toRingHom.comp ((algebraMap (Node k) _).comp (quotientMap k)) = f := by
  let v := quotientMap k (MvPolynomial.X i)
  let S := Localization.Away v
  let a : Node k →+* S := algebraMap _ _
  let p : PolynomialChart k →+* S := a.comp (quotientMap k)
  have hfrel : f (relation k) = 0 := by
    simp only [relation, map_sub, map_mul, hC, hX]
    fin_cases i
    · change LaurentPolynomial.T 1 *
        (LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)) -
          LaurentPolynomial.C (parameter k) = 0
      rw [mul_left_comm, ← LaurentPolynomial.T_add]
      norm_num
    · change (LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)) *
        LaurentPolynomial.T 1 - LaurentPolynomial.C (parameter k) = 0
      rw [mul_assoc, ← LaurentPolynomial.T_add]
      norm_num
  have hkill : relationIdeal k ≤ RingHom.ker f := by
    rw [relationIdeal, Ideal.span_singleton_le_iff_mem]
    exact hfrel
  let g : Node k →+* Torus k := Ideal.Quotient.lift _ f (fun z hz => hkill hz)
  have hg (z) : g (quotientMap k z) = f z := rfl
  have hgv : g v = LaurentPolynomial.T 1 := by simp [v, hg, hX]
  let F : S →+* Torus k := IsLocalization.Away.lift v
    (show IsUnit (g v) by rw [hgv]; exact LaurentPolynomial.isUnit_T 1)
  have hF (z) : F (a z) = g z := IsLocalization.Away.lift_eq _ _ z
  have hFp (z) : F (p z) = f z := by change F (a (quotientMap k z)) = _; rw [hF, hg]
  let U : Sˣ := (IsLocalization.Away.algebraMap_isUnit v (S := S)).unit
  have hU : (U : S) = p (MvPolynomial.X i) := IsUnit.unit_spec _
  let G : Torus k →+* S := LaurentPolynomial.eval₂ (p.comp MvPolynomial.C) U
  have hGC (z) : G (LaurentPolynomial.C z) = p (MvPolynomial.C z) :=
    LaurentPolynomial.eval₂_C _ _ _
  have hGT : G (LaurentPolynomial.T 1) = p (MvPolynomial.X i) := by
    simpa [G] using hU
  have hGX (j : Fin 2) : G (f (MvPolynomial.X j)) = p (MvPolynomial.X j) := by
    rw [hX]
    split_ifs with h
    · subst j; exact hGT
    · have hprod : p (MvPolynomial.X i) * p (MvPolynomial.X j) =
          p (MvPolynomial.C (parameter k)) := by
        change a (quotientMap k (MvPolynomial.X i)) * a (quotientMap k (MvPolynomial.X j)) = _
        rw [← map_mul, coordinate_product k i j (Ne.symm h)]
        rfl
      change G (LaurentPolynomial.C (parameter k) * LaurentPolynomial.T (-1)) = _
      rw [map_mul, hGC]
      have hneg : G (LaurentPolynomial.T (-1)) = ↑(U⁻¹) := by simp [G]
      rw [hneg, ← hprod, ← hU]
      rw [mul_right_comm, Units.mul_inv, one_mul]
  have hGFp : G.comp f = p := MvPolynomial.ringHom_ext
    (fun z => by simp only [RingHom.comp_apply, hC, hGC]) hGX
  have hGF : G.comp F = RingHom.id S := by
    apply IsLocalization.ringHom_ext (Submonoid.powers v)
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro z
    change G (F (p z)) = p z
    rw [hFp]
    exact RingHom.congr_fun hGFp z
  have hFG : F.comp G = RingHom.id (Torus k) := by
    apply laurent_hom_ext
    · intro z
      change F (G (LaurentPolynomial.C z)) = LaurentPolynomial.C z
      rw [hGC, hFp, hC]
    · change F (G (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1
      rw [hGT, hFp, hX]; simp
  let e : S ≃+* Torus k :=
    { F with
      invFun := G
      left_inv := fun z => RingHom.congr_fun hGF z
      right_inv := fun z => RingHom.congr_fun hFG z }
  have he : e.toRingHom.comp p = f := RingHom.ext hFp
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers v)
  apply Ideal.Quotient.ringHom_ext
  exact he'.trans he.symm
set_option backward.isDefEq.respectTransparency true in
theorem node_torus_chart_equivalences : ∀ (k : Type u) [Field k] [CharZero k], (∃! e : XChart k ≃+* Torus k, e.toRingHom.comp ((toXChart k).comp (quotientMap k)) = torusMap k) ∧ (∃! e : YChart k ≃+* Torus k, e.toRingHom.comp ((toYChart k).comp (quotientMap k)) = oppositeTorusMap k) := by sorry
end ArithmeticThetaNodeCharts
namespace ArithmeticThetaIndexedOverlapsR0058
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
variable (k : Type u) [Field k] [CharZero k]
abbrev Node (_j : ℕ) := ArithmeticThetaNodeCharts.Node k
def next (r j : ℕ) : ℕ := (j + 1) % r
def nodeCoord (side : Bool) : Node k 0 :=
  if side then ArithmeticThetaNodeCharts.x k else ArithmeticThetaNodeCharts.y k
abbrev Open (_j : ℕ) (side : Bool) := Localization.Away (nodeCoord k side)
set_option backward.isDefEq.respectTransparency true in
def torusEquiv (j : ℕ) (side : Bool) : Open k j side ≃+* ArithmeticThetaNodeCharts.Torus k := by
  cases side with
  | false => exact Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).2
  | true => exact Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1
set_option backward.isDefEq.respectTransparency true in
def adjacent (r j : ℕ) : Open k j false ≃+* Open k (next r j) true :=
  ((torusEquiv k j false).trans LaurentPolynomial.invert.toRingEquiv).trans
    (torusEquiv k (next r j) true).symm
end ArithmeticThetaIndexedOverlapsR0058
namespace ArithmeticThetaInfinitesimalPolygonR0129
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev Trunc (R : Type u) [CommRing R] (t : R) (n : ℕ) :=
  R ⧸ (Ideal.span {t}) ^ (n+1)
def trunc (R : Type u) [CommRing R] (t : R) (n : ℕ) : R →+* Trunc R t n :=
  Ideal.Quotient.mk _
def truncMap {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (t : R) (s : S) (h : f t = s) (n : ℕ) : Trunc R t n →+* Trunc S s n :=
  Ideal.quotientMap _ f (by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, h])
def truncReduce (R : Type u) [CommRing R] (t : R) (n N : ℕ) (h : n ≤ N) : Trunc R t N →+* Trunc R t n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
variable (k : Type u) [Field k] [CharZero k]
abbrev R (n : ℕ) := Trunc (PowerSeries k) PowerSeries.X n
abbrev A (n : ℕ) := Trunc (ArithmeticThetaNodeCharts.Node k)
  (ArithmeticThetaNodeCharts.t k) n
abbrev RawOpen (side : Bool) := ArithmeticThetaIndexedOverlapsR0058.Open k 0 side
def openParameter (side : Bool) : RawOpen k side :=
  algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k side)
    (ArithmeticThetaNodeCharts.t k)
abbrev B (n : ℕ) (side : Bool) := Trunc (RawOpen k side) (openParameter k side) n
def base (n : ℕ) : R k n →+* A k n :=
  truncMap (algebraMap (PowerSeries k) (ArithmeticThetaNodeCharts.Node k))
    PowerSeries.X (ArithmeticThetaNodeCharts.t k) rfl n
def restriction (n : ℕ) (side : Bool) : A k n →+* B k n side :=
  truncMap (algebraMap (ArithmeticThetaNodeCharts.Node k) (RawOpen k side))
    (ArithmeticThetaNodeCharts.t k) (openParameter k side) rfl n
set_option backward.isDefEq.respectTransparency true in
def rawAdjacent : RawOpen k false ≃+* RawOpen k true :=
  ArithmeticThetaIndexedOverlapsR0058.adjacent k 1 0
def IsAdjacent (n : ℕ) (E : B k n false ≃+* B k n true) : Prop :=
  E.toRingHom.comp (trunc (RawOpen k false) (openParameter k false) n) =
    (trunc (RawOpen k true) (openParameter k true) n).comp (rawAdjacent k).toRingHom
theorem _root_.ArithmeticThetaInfinitesimalPolygonR0129.CompletionComparison._proof_2.{u_1} : ∀ (k : Type u_1) [inst : Field.{u_1} k], @IsScalarTower.{u_1, u_1, u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@Algebra.toSMul.{u_1, u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)) (@CommSemiring.toSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@Algebra.id.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)))) (@instSMulOfMul.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@Distrib.toMul.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@instDistribOfSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@CommSemiring.toSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)))))) (@Algebra.toSMul.{u_1, u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)) (@CommSemiring.toSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@Algebra.id.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaNodeCharts.Node.{u_1} k inst) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)))) := by sorry
theorem _root_.ArithmeticThetaInfinitesimalPolygonR0129.CompletionComparison._proof_4.{u_1} : ∀ (k : Type u_1) [inst : Field.{u_1} k] (side : Bool), @IsScalarTower.{u_1, u_1, u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@Algebra.toSMul.{u_1, u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@OreLocalization.instCommRing.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side)) (@OreLocalization.oreSetComm.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side))))) (@CommSemiring.toSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@OreLocalization.instCommRing.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side)) (@OreLocalization.oreSetComm.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side)))))) (@Algebra.id.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@OreLocalization.instCommRing.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side)) (@OreLocalization.oreSetComm.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side))))))) (@instSMulOfMul.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@Distrib.toMul.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@instDistribOfSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@CommSemiring.toSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@OreLocalization.instCommRing.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side)) (@OreLocalization.oreSetComm.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side))))))))) (@Algebra.toSMul.{u_1, u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@OreLocalization.instCommRing.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side)) (@OreLocalization.oreSetComm.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side))))) (@CommSemiring.toSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@OreLocalization.instCommRing.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side)) (@OreLocalization.oreSetComm.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side)))))) (@Algebra.id.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@CommRing.toCommSemiring.{u_1} (@ArithmeticThetaInfinitesimalPolygonR0129.RawOpen.{u_1} k inst side) (@OreLocalization.instCommRing.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side)) (@OreLocalization.oreSetComm.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst)) (@Submonoid.powers.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommMonoid.toMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@CommRing.toCommMonoid.{u_1} (@ArithmeticThetaIndexedOverlapsR0058.Node.{u_1} k inst (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) (@ArithmeticThetaNodeCharts.nodeCommRing.{u_1} k inst))) (@ArithmeticThetaIndexedOverlapsR0058.nodeCoord.{u_1} k inst side))))))) := by sorry
run_cmd do
  for n in [`ArithmeticThetaInfinitesimalPolygonR0129.CompletionComparison._proof_2, `ArithmeticThetaInfinitesimalPolygonR0129.CompletionComparison._proof_4] do
    let some ci := (← Lean.getEnv).find? n | throwError "Missing original completion helper"
    let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
    Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s => { s with lemmas := s.lemmas.insert key (ci.name, ci.levelParams) }
def specR (n : ℕ) : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (R k n))
def specA (n : ℕ) : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (A k n))
def specB (n : ℕ) (side : Bool) : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of (B k n side))
def structureMap (n : ℕ) : specA k n ⟶ specR k n :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (base k n))
def rightLeg (n : ℕ) : specB k n true ⟶ specA k n :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (restriction k n true))
def leftLeg (n : ℕ) (E : B k n false ≃+* B k n true) : specB k n true ⟶ specA k n :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (E.toRingHom.comp (restriction k n false)))
def next (r : ℕ) (hr : 0 < r) (i : Fin r) : Fin r :=
  ⟨(i.val+1)%r, Nat.mod_lt _ hr⟩
structure Atlas (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true) where
  X : AlgebraicGeometry.Scheme.{u}
  p : X ⟶ specR k n
  chart : Fin r → (specA k n ⟶ X)
  chart_open : ∀ i, AlgebraicGeometry.IsOpenImmersion (chart i)
  covers : ∀ x : X, ∃ (i : Fin r) (a : specA k n), chart i a = x
  chart_over : ∀ i, chart i ≫ p = structureMap k n
  adjacent : ∀ i, CategoryTheory.IsPullback (leftLeg k n E) (rightLeg k n)
    (chart i) (chart (next r hr i))
  disjoint : ∀ i j, i ≠ j → next r hr i ≠ j → next r hr j ≠ i →
    Disjoint (Set.range (chart i)) (Set.range (chart j))
def baseReduction (n N : ℕ) (h : n ≤ N) : specR k n ⟶ specR k N :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (truncReduce (PowerSeries k) PowerSeries.X n N h))
def chartReduction (n N : ℕ) (h : n ≤ N) : specA k n ⟶ specA k N :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom
    (truncReduce (ArithmeticThetaNodeCharts.Node k) (ArithmeticThetaNodeCharts.t k) n N h))
def IsReduction (r n N : ℕ) (hr : 0 < r) (h : n ≤ N) {E : B k n false ≃+* B k n true} {F : B k N false ≃+* B k N true} (D : Atlas k r n hr E) (T : Atlas k r N hr F) (i : D.X ⟶ T.X) : Prop :=
  i ≫ T.p = D.p ≫ baseReduction k n N h ∧
    ∀ j : Fin r, D.chart j ≫ i = chartReduction k n N h ≫ T.chart j
structure Tower (r : ℕ) (hr : 0 < r) where
  overlap : ∀ n, B k n false ≃+* B k n true
  overlap_spec : ∀ n, IsAdjacent k n (overlap n)
  atlas : ∀ n, Atlas k r n hr (overlap n)
  transition : ∀ n N (h : n ≤ N), (atlas n).X ⟶ (atlas N).X
  transition_spec : ∀ n N h, IsReduction k r n N hr h (atlas n) (atlas N) (transition n N h)
  identity : ∀ n, transition n n (le_refl n) = 𝟙 (atlas n).X
  composition : ∀ n N P (h : n ≤ N) (h' : N ≤ P),
    transition n N h ≫ transition N P h' = transition n P (le_trans h h')
end ArithmeticThetaInfinitesimalPolygonR0129
namespace ArithmeticThetaInfinitesimalPolygonR0129
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
variable (k : Type u) [Field k] [CharZero k]
variable (n : ℕ)
def coordX : A k n := trunc _ (ArithmeticThetaNodeCharts.t k) n
  (ArithmeticThetaNodeCharts.x k)
def coordY : A k n := trunc _ (ArithmeticThetaNodeCharts.t k) n
  (ArithmeticThetaNodeCharts.y k)
def parameter : R k n := trunc _ PowerSeries.X n PowerSeries.X
lemma parameter_pow : parameter k n ^ (n+1) = 0 := by
  rw [parameter, ← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.pow_mem_pow (Ideal.subset_span (by simp)) _
variable {k n}
def mkPoint {S : Type u} [CommRing S] (b : R k n →+* S) (x y : S) (hxy : x * y = b (parameter k n)) : A k n →+* S := by
  let f : ArithmeticThetaNodeCharts.PolynomialChart k →+* S :=
    MvPolynomial.eval₂Hom (b.comp (trunc _ PowerSeries.X n))
      (fun j => if j = 0 then x else y)
  have hf : ArithmeticThetaNodeCharts.relationIdeal k ≤ RingHom.ker f := by
    rw [ArithmeticThetaNodeCharts.relationIdeal, Ideal.span_singleton_le_iff_mem]
    change f (ArithmeticThetaNodeCharts.relation k) = 0
    simpa [f, ArithmeticThetaNodeCharts.relation, ArithmeticThetaNodeCharts.parameter,
      parameter] using sub_eq_zero.mpr hxy
  let g : ArithmeticThetaNodeCharts.Node k →+* S :=
    Ideal.Quotient.lift _ f (fun a ha => hf ha)
  have hg : (Ideal.span {ArithmeticThetaNodeCharts.t k}) ^ (n+1) ≤ RingHom.ker g := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    change g (ArithmeticThetaNodeCharts.t k ^ (n+1)) = 0
    rw [map_pow]
    have ht : g (ArithmeticThetaNodeCharts.t k) = b (parameter k n) := by
      change f (MvPolynomial.C PowerSeries.X) = _
      simp [f, parameter]
    rw [ht, ← map_pow, parameter_pow, map_zero]
  exact Ideal.Quotient.lift _ g (fun a ha => hg ha)
end ArithmeticThetaInfinitesimalPolygonR0129
namespace ArithmeticThetaPolygonCohomologyR0131
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129
variable (k : Type u) [Field k] [CharZero k]
def LaurentPresentation (n : ℕ)
    (L : B k n true ≃+* LaurentPolynomial (R k n)) : Prop :=
  L.toRingHom.comp ((restriction k n true).comp (base k n)) =
    LaurentPolynomial.C ∧
  L (restriction k n true (coordX k n)) = LaurentPolynomial.T 1

def difference (r n : ℕ) (hr : 0 < r) (E : B k n false ≃+* B k n true)
    (a : Fin r → A k n) : Fin r → B k n true :=
  fun i => E (restriction k n false (a i)) -
    restriction k n true (a (next r hr i))

def constants (r n : ℕ) (c : R k n) : Fin r → A k n :=
  fun _ => base k n c

def residue (r n : ℕ) (L : B k n true ≃+* LaurentPolynomial (R k n))
    (b : Fin r → B k n true) : R k n :=
  ∑ i : Fin r, (L (b i)).coeff 0

def globalBase (r n : ℕ) (hr : 0 < r)
    {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E) :
    R k n →+* D.X.presheaf.obj (Opposite.op ⊤) :=
  D.p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (R k n))).inv.hom

def markedUnit (n : ℕ) (a : kˣ) : (R k n)ˣ :=
  Units.map ((trunc (PowerSeries k) PowerSeries.X n).comp PowerSeries.C) a
def markedPoint (n : ℕ) (a : kˣ) : A k n →+* R k n :=
  mkPoint (RingHom.id (R k n)) (markedUnit k n a : R k n)
    (parameter k n * ↑((markedUnit k n a)⁻¹)) (by
      simp [mul_left_comm])
def markedSection (r n : ℕ) (hr : 0 < r) {E : B k n false ≃+* B k n true} (D : Atlas k r n hr E) (i : Fin r) (a : kˣ) : specR k n ⟶ D.X :=
  Spec.map (CommRingCat.ofHom (markedPoint k n a)) ≫ D.chart i
end ArithmeticThetaPolygonCohomologyR0131
namespace ArithmeticThetaProjectiveEffectivityR0135
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129
variable (k : Type u) [Field k] [CharZero k]
def baseInclusion (n : ℕ) : specR k n ⟶ Spec (CommRingCat.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (trunc (PowerSeries k) PowerSeries.X n))
structure Model {r : ℕ} {hr : 0 < r} (T : Tower k r hr) where
  X : Scheme.{u}
  p : X ⟶ Spec (CommRingCat.of (PowerSeries k))
  inclusion : ∀ n, (T.atlas n).X ⟶ X
def IsModel {r : ℕ} {hr : 0 < r} (T : Tower k r hr) (M : Model k T) : Prop :=
  IsProper M.p ∧ Flat M.p ∧
  (∀ n, IsPullback (M.inclusion n) (T.atlas n).p M.p (baseInclusion k n)) ∧
  (∀ n N (h : n ≤ N), T.transition n N h ≫ M.inclusion N = M.inclusion n)
end ArithmeticThetaProjectiveEffectivityR0135
namespace ArithmeticThetaAlgebraizedMarkedLineR0136
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaPolygonCohomologyR0131
variable (k : Type u) [Field k] [CharZero k]
def baseScheme : Scheme.{u} := Spec (CommRingCat.of (PowerSeries k))
def MarkedLift {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T) (i : Fin r) (a : kˣ) (s : baseScheme k ⟶ M.X) : Prop :=
  s ≫ M.p = 𝟙 (baseScheme k) ∧ ∀ n : ℕ,
    baseInclusion k n ≫ s = markedSection k r n hr (T.atlas n) i a ≫ M.inclusion n
end ArithmeticThetaAlgebraizedMarkedLineR0136
namespace ArithmeticThetaIdentitySectionsR0138
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
def zeroIndex (r : ℕ) (hr : 0 < r) : Fin r := ⟨0, hr⟩
end ArithmeticThetaIdentitySectionsR0138
namespace ArithmeticThetaProjectiveEffectivityR0135
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129
variable (k : Type u) [Field k] [CharZero k]
def genericBase : Spec (CommRingCat.of (LaurentSeries k)) ⟶ Spec (CommRingCat.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
def genericStructure {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T) :=
  CategoryTheory.Limits.pullback.snd M.p (genericBase k)
end ArithmeticThetaProjectiveEffectivityR0135
namespace ArithmeticThetaGenericEvaluationR0140
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
def genericScheme (M : Model k T) : Scheme.{u} := pullback M.p (genericBase k)
def genericPoint (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k)) : Spec (CommRingCat.of (LaurentSeries k)) ⟶ genericScheme k M :=
  pullback.lift (genericBase k ≫ s) (𝟙 _) (by
    dsimp only [baseScheme] at hs ⊢
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
end ArithmeticThetaGenericEvaluationR0140
namespace NeronModelInfra
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) := {φ : Y ⟶ X // φ ≫ f = g}
end NeronModelInfra
namespace WeierstrassProjModel
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open NeronModelInfra
def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩
@[simp]
theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl
structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) where
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f
  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f
  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)
  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t (one t) x = x
  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t x (one t) = x
  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f), mul t (inv t x) x = one t
  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f),
    schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)
end WeierstrassProjModel
namespace WeierstrassProjModel.RelativeGroupLaw
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open NeronModelInfra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n
end WeierstrassProjModel.RelativeGroupLaw
namespace ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaGenericEvaluationR0140
variable (k : Type u) [Field k] [CharZero k] (r : ℕ)
lemma genericPoint_structure {hr : 0 < r} {T : Tower k r hr} (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 _) : genericPoint k M s hs ≫ genericStructure k M = 𝟙 _ := by sorry
end ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144
namespace ArithmeticThetaMarkedGroupLawR0146
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaGenericEvaluationR0140 NeronModelInfra
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
abbrev Law (M : Model k T) :=
  WeierstrassProjModel.RelativeGroupLaw (LaurentSeries k) (genericStructure k M)
def pointOver (M : Model k T) {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k))) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k)) : SchemeHomOver t (genericStructure k M) :=
  ⟨t ≫ genericPoint k M s hs, by rw [Category.assoc, ArithmeticThetaCubicModelR0144.GenericAffineCubicIsomorphismR0144.genericPoint_structure, Category.comp_id]⟩
def IsOriginLaw (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k)) (G : Law k M) : Prop :=
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k))),
    G.one t = pointOver k M t s hs) ∧
  (∀ {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of (LaurentSeries k)))
    (x y : SchemeHomOver t (genericStructure k M)), G.mul t x y = G.mul t y x)
end ArithmeticThetaMarkedGroupLawR0146
namespace ArithmeticThetaHodgeFourTorsionR0147
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaGenericEvaluationR0140 NeronModelInfra ArithmeticThetaMarkedGroupLawR0146
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
abbrev Point (M : Model k T) := SchemeHomOver (𝟙 (Spec (CommRingCat.of (LaurentSeries k)))) (genericStructure k M)
def universalPoint (M : Model k T) : SchemeHomOver (genericStructure k M) (genericStructure k M) :=
  ⟨𝟙 _, Category.id_comp _⟩
def multiplication (M : Model k T) (G : Law k M) (n : ℕ) : genericScheme k M ⟶ genericScheme k M :=
  (G.nsmul (genericStructure k M) n (universalPoint k M)).val
end ArithmeticThetaHodgeFourTorsionR0147
namespace ArithmeticThetaGeometricNormR0150
attribute [local instance 2000] HenselianLocalRing.toIsLocalRing
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaHodgeFourTorsionR0147
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
def IsFieldMap (f : X ⟶ Y) (φ : Y.functionField →+* X.functionField) : Prop :=
  X.fromSpecStalk (genericPoint X) ≫ f =
    Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y)
def fieldNorm (φ : Y.functionField →+* X.functionField) (g : X.functionField) : Y.functionField :=
  letI := φ.toAlgebra
  Algebra.norm Y.functionField g
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
def identityPoint (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k)) : genericScheme k M :=
  genericPoint k M s hs (IsLocalRing.closedPoint (LaurentSeries k))
def katoOrder (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k)) (G : Law k M) (c : ℕ) (x : genericScheme k M) : ℤ := by
  classical
  exact (if x = identityPoint k M s hs then (c : ℤ)^2 else 0) -
    (if multiplication k M G c x = identityPoint k M s hs then 1 else 0)
end ArithmeticThetaGeometricNormR0150
namespace ArithmeticThetaKatoExistenceR0151
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaMarkedGroupLawR0146 ArithmeticThetaHodgeFourTorsionR0147 ArithmeticThetaGeometricNormR0150
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
def HasKatoDivisor (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k)) (G : Law k M) (c : ℕ) [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)] (g : (genericScheme k M).functionField) : Prop :=
  g ≠ 0 ∧ ∀ x : genericScheme k M, Scheme.ord g x = katoOrder k M s hs G c x
def IsKatoFunction (M : Model k T) (s : baseScheme k ⟶ M.X) (hs : s ≫ M.p = 𝟙 (baseScheme k)) (G : Law k M) (c : ℕ) [IsIntegral (genericScheme k M)] [IsLocallyNoetherian (genericScheme k M)] (g : (genericScheme k M).functionField) : Prop :=
  HasKatoDivisor k M s hs G c g ∧
    ∀ (d : ℕ), 0 < d → Nat.Coprime c d →
      ∀ (φ : (genericScheme k M).functionField →+* (genericScheme k M).functionField),
        IsFieldMap (multiplication k M G d) φ → fieldNorm φ g = g
end ArithmeticThetaKatoExistenceR0151
namespace ArithmeticThetaMarkedKatoValuesR0159
attribute [local instance 2000] HenselianLocalRing.toIsLocalRing
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
def HasValue (F : Type u) [Field F] (X : Scheme.{u}) [IsIntegral X] (p : Spec (CommRingCat.of F) ⟶ X) (g : X.functionField) (v : F) : Prop :=
  ∃ b : X.presheaf.stalk (p (IsLocalRing.closedPoint F)),
    algebraMap (X.presheaf.stalk (p (IsLocalRing.closedPoint F))) X.functionField b = g ∧
    Scheme.stalkClosedPointTo p b = v
end ArithmeticThetaMarkedKatoValuesR0159
namespace ArithmeticThetaUnaryProduct
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
noncomputable def unaryA (m : ℕ) (ν : ℤ) : ℕ :=
  (12*(m : ℤ)^2+24*(m : ℤ)*ν).toNat
noncomputable def clearedUnaryTheta (m : ℕ) (ν : ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => ∑ k ∈ Finset.Icc (-(n : ℤ)) ((n : ℤ)+1),
    if 12*((m : ℤ)*k+ν)^2=(n : ℤ) then (1 : ℤ) else 0)
end ArithmeticThetaUnaryProduct
namespace ArithmeticThetaDiscriminant
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
noncomputable def partialEuler {R : Type*} [CommRing R] (a : R) (N : ℕ) : PowerSeries R := ∏ j ∈ Finset.range N, (1 - PowerSeries.C a * PowerSeries.X ^ (j + 1))
noncomputable def euler {R : Type*} [CommRing R] (a : R) : PowerSeries R :=
  PowerSeries.mk (fun d => PowerSeries.coeff d (partialEuler a d))
noncomputable def P : PowerSeries ℚ := euler 1
end ArithmeticThetaDiscriminant
namespace ArithmeticThetaUnaryKatoPowerR0160
run_cmd Lean.modifyEnv fun env => Lean.EnvExtension.setState mX (Lean.Meta.auxLemmasExt.setState env {}) {}
open CategoryTheory AlgebraicGeometry
def integerSeries (k : Type) [Field k] : PowerSeries ℤ →+* LaurentSeries k :=
  (HahnSeries.ofPowerSeries ℤ k).comp (PowerSeries.map (Int.castRingHom k))
def unary (k : Type) [Field k] (d m : ℕ) (ν : ℤ) : LaurentSeries k :=
  integerSeries k (PowerSeries.subst (PowerSeries.X^d)
    (ArithmeticThetaUnaryProduct.clearedUnaryTheta m ν))
def discriminant (k : Type) [Field k] [CharZero k] (r : ℕ) : LaurentSeries k :=
  (HahnSeries.ofPowerSeries ℤ k) (PowerSeries.subst (PowerSeries.X^r)
    (PowerSeries.map (algebraMap ℚ k)
      (PowerSeries.X^2 * ArithmeticThetaDiscriminant.P^48)))
def PowerValues (k : Type) [Field k] [CharZero k] {r : ℕ} {hr : 0 < r} {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr} (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) [IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)] (d m N : ℕ) (g : (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).functionField) : Prop :=
  ∀ ν : ℤ, (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) →
    ∃ (j : Fin r) (p : ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k ⟶ M.X)
      (hp : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M j (-1) p),
      j.val = d * ArithmeticThetaUnaryProduct.unaryA m ν ∧
      ArithmeticThetaMarkedKatoValuesR0159.HasValue (LaurentSeries k)
        (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)
        (ArithmeticThetaGenericEvaluationR0140.genericPoint k M p hp.1) g
        (unary k d m ν ^ ((1+12*N)^2-1) /
          discriminant k r ^ (((1+12*N)^2-1)/48))
def GeometricRealization (k : Type) [Field k] [CharZero k] (d m N : ℕ) : Prop :=
  ∃ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (he : Even r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (G : ArithmeticThetaMarkedGroupLawR0146.Law k M) (hG : ArithmeticThetaMarkedGroupLawR0146.IsOriginLaw k M s hs.1 G) (hI : AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)) (hNoeth : AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), letI : AlgebraicGeometry.IsIntegral (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) := hI
  letI : AlgebraicGeometry.IsLocallyNoetherian (ArithmeticThetaGenericEvaluationR0140.genericScheme k M) := hNoeth
  r = 24*d*m^2 ∧ ∃! g : (AlgebraicGeometry.Scheme.functionField (ArithmeticThetaGenericEvaluationR0140.genericScheme k M)), ArithmeticThetaKatoExistenceR0151.IsKatoFunction k M s hs.1 G (1+12*N) g ∧ ArithmeticThetaUnaryKatoPowerR0160.PowerValues k M d m N g
end ArithmeticThetaUnaryKatoPowerR0160
theorem ArithmeticThetaPalomarUnary489.unaryPowerGeometricRealization :
∀ (k : Type) [Field k] [CharZero k] (d m N : ℕ), 0 < d → 0 < m → Even m → 0 < N → Even N → m ∣ N → ArithmeticThetaUnaryKatoPowerR0160.GeometricRealization k d m N := by
  sorry
