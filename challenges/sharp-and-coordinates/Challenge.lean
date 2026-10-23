module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section
section Package00
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
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
private theorem laurent_hom_ext {R S : Type*} [CommRing R] [CommRing S] {f g : LaurentPolynomial R →+* S} (hC : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a)) (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro a
    simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hC a
  · simpa [LaurentPolynomial.algebraMap_eq_toLaurent] using hT
variable (k : Type u) [Field k]
private theorem coordinate_product (i j : Fin 2) (h : i ≠ j) : quotientMap k (MvPolynomial.X i) * quotientMap k (MvPolynomial.X j) = quotientMap k (MvPolynomial.C (parameter k)) := by
  have hr : quotientMap k (relation k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hxy := sub_eq_zero.mp (show
    quotientMap k (MvPolynomial.X 0) * quotientMap k (MvPolynomial.X 1) -
      quotientMap k (MvPolynomial.C (parameter k)) = 0 by
        simpa [relation, map_sub, map_mul] using hr)
  fin_cases i <;> fin_cases j <;> simp_all [mul_comm]
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
theorem node_torus_chart_equivalences : ∀ (k : Type u) [Field k] [CharZero k], (∃! e : XChart k ≃+* Torus k, e.toRingHom.comp ((toXChart k).comp (quotientMap k)) = torusMap k) ∧ (∃! e : YChart k ≃+* Torus k, e.toRingHom.comp ((toYChart k).comp (quotientMap k)) = oppositeTorusMap k) := by sorry
end ArithmeticThetaNodeCharts
namespace ArithmeticThetaIndexedOverlapsR0058
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
variable (k : Type u) [Field k] [CharZero k]
abbrev Node (_j : ℕ) := ArithmeticThetaNodeCharts.Node k
def next (r j : ℕ) : ℕ := (j + 1) % r
def nodeCoord (side : Bool) : Node k 0 :=
  if side then ArithmeticThetaNodeCharts.x k else ArithmeticThetaNodeCharts.y k
abbrev Open (_j : ℕ) (side : Bool) := Localization.Away (nodeCoord k side)
def torusEquiv (j : ℕ) (side : Bool) : Open k j side ≃+* ArithmeticThetaNodeCharts.Torus k := by
  cases side with
  | false => exact Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).2
  | true => exact Classical.choose (ArithmeticThetaNodeCharts.node_torus_chart_equivalences k).1
def adjacent (r j : ℕ) : Open k j false ≃+* Open k (next r j) true :=
  ((torusEquiv k j false).trans LaurentPolynomial.invert.toRingEquiv).trans
    (torusEquiv k (next r j) true).symm
end ArithmeticThetaIndexedOverlapsR0058
namespace ArithmeticThetaInfinitesimalPolygonR0129
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
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
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaPolygonCohomologyR0131
variable (k : Type u) [Field k] [CharZero k]
def baseScheme : Scheme.{u} := Spec (CommRingCat.of (PowerSeries k))
def MarkedLift {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T) (i : Fin r) (a : kˣ) (s : baseScheme k ⟶ M.X) : Prop :=
  s ≫ M.p = 𝟙 (baseScheme k) ∧ ∀ n : ℕ,
    baseInclusion k n ≫ s = markedSection k r n hr (T.atlas n) i a ≫ M.inclusion n
end ArithmeticThetaAlgebraizedMarkedLineR0136
namespace ArithmeticThetaPolygonCartierR0133
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def unitPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj
      (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
end ArithmeticThetaPolygonCartierR0133
namespace ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def quotientMap {X : Scheme.{u}} (I : X.IdealSheafData) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit I.subschemeι.toRingCatSheafHom
def idealModule {X : Scheme.{u}} (I : X.IdealSheafData) : X.Modules :=
  kernel (quotientMap I)
def idealInclusion {X : Scheme.{u}} (I : X.IdealSheafData) :
    idealModule I ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  kernel.ι (quotientMap I)
end ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133
namespace ArithmeticThetaIdentitySectionsR0138
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaPolygonCartierR0133
variable (k : Type u) [Field k] [CharZero k]
def zeroIndex (r : ℕ) (hr : 0 < r) : Fin r := ⟨0, hr⟩
def equation (r n : ℕ) (i : Fin r) : A k n :=
  (if i.val = 0 then 1 - ArithmeticThetaInfinitesimalPolygonR0129.coordX k n else 1) *
  (if i.val + 1 = r then 1 - ArithmeticThetaInfinitesimalPolygonR0129.coordY k n else 1)
def powerModule {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ) : M.X.Modules :=
  GlobalCartierIdealLineR0133.idealModule (s.ker^d)
def Dual {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T)
    (s : baseScheme k ⟶ M.X) (d : ℕ) :=
  powerModule k M s d ⟶ (SheafOfModules.unit M.X.ringCatSheaf : M.X.Modules)
end ArithmeticThetaIdentitySectionsR0138
namespace ArithmeticThetaAlgebraicCoordinatesR0143
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaPolygonCartierR0133
variable (k : Type u) [Field k] [CharZero k]
def degree (odd : Bool) : ℕ := if odd then 3 else 2
def tau (n : ℕ) : A k n := base k n (parameter k n)
def geometric (n : ℕ) (v : A k n) : A k n :=
  ∑ a ∈ Finset.range (n+1), v^a
def term (odd : Bool) (n : ℕ) (v : A k n) : A k n :=
  v * (if odd then 1+v else 1) * geometric k n v ^ degree odd
def numerator (odd : Bool) (r n : ℕ) (i : Fin r) : A k n :=
  let h := equation k r n i ^ degree odd
  let first := if i.val = 0 then
      coordX k n * (if odd then 1+coordX k n else 1)
    else h * term k odd n (tau k n ^ i.val * coordX k n)
  let positive := h * ∑ a ∈ Finset.range (n+1),
    term k odd n (tau k n ^ (r*(a+1)+i.val) * coordX k n)
  let negative := ∑ a ∈ Finset.range (n+1),
    if a = 0 ∧ i.val+1 = r then
      coordY k n * (if odd then 1+coordY k n else 1)
    else h * term k odd n (tau k n ^ (r*(a+1)-i.val-1) * coordY k n)
  if odd then
    base k n (trunc (PowerSeries k) PowerSeries.X n (PowerSeries.C (2 : k)⁻¹)) *
      (first + positive - negative)
  else
    first + positive + negative - 2 * h * ∑ a ∈ Finset.range (n+1),
      (a+1 : ℕ) * tau k n ^ (r*(a+1)) * geometric k n (tau k n ^ (r*(a+1)))
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
def RealizesCoordinate (odd : Bool) (M : Model k T)
    (s : baseScheme k ⟶ M.X) (φ : Dual k M s (degree odd)) : Prop :=
  ∀ n (i : Fin r),
    let f := (T.atlas n).chart i ≫ M.inclusion n
    let P := (Scheme.Modules.pullback f).obj (powerModule k M s (degree odd))
    let j := (Scheme.Modules.pullback f).map
      (GlobalCartierIdealLineR0133.idealInclusion (s.ker ^ degree odd)) ≫ unitPullback f
    let q := (Scheme.Modules.pullback f).map φ ≫ unitPullback f
    ∃ z : Γ(P, ⊤),
      j.app ⊤ z = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (equation k r n i ^ degree odd) ∧
      q.app ⊤ z = (Scheme.ΓSpecIso (CommRingCat.of (A k n))).inv
        (numerator k odd r n i)
def pulled (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (p : baseScheme k ⟶ M.X) (φ : Dual k M s d) :=
  (Scheme.Modules.pullback p).map φ ≫ unitPullback p
end ArithmeticThetaAlgebraicCoordinatesR0143
namespace ArithmeticThetaProjectiveEffectivityR0135
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129
variable (k : Type u) [Field k] [CharZero k]
def genericBase : Spec (CommRingCat.of (LaurentSeries k)) ⟶
    Spec (CommRingCat.of (PowerSeries k)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))
def genericStructure {r : ℕ} {hr : 0 < r} {T : Tower k r hr} (M : Model k T) :=
  CategoryTheory.Limits.pullback.snd M.p (genericBase k)
end ArithmeticThetaProjectiveEffectivityR0135
namespace ArithmeticThetaGenericEvaluationR0140
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaPolygonCartierR0133
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
def IdentityFrame (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ) :=
  (Scheme.Modules.pullback s).obj (powerModule k M s d) ≅
    (SheafOfModules.unit (baseScheme k).ringCatSheaf : (baseScheme k).Modules)
def frameValue (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ)
    (e : IdentityFrame k M s d) (φ : Dual k M s d) : PowerSeries k :=
  (Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).hom
    ((e.inv ≫ (Scheme.Modules.pullback s).map φ ≫ unitPullback s).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv 1))
end ArithmeticThetaGenericEvaluationR0140
namespace ArithmeticThetaTateSeries
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
variable {k : Type u} [Field k]
def monomial (a : k) (n : ℕ) : PowerSeries k :=
  PowerSeries.C a * PowerSeries.X ^ n
def xTerm (v : PowerSeries k) : PowerSeries k := v * ((1-v)⁻¹)^2
def partialX (d i : ℕ) (a : k) (N : ℕ) : PowerSeries k :=
  xTerm (monomial a i) +
  (∑ j ∈ Finset.range N,
    (xTerm (monomial a (d*(j+1)+i)) +
     xTerm (monomial a⁻¹ (d*(j+1)-i)))) -
  2 * ∑ j ∈ Finset.range N,
    PowerSeries.C ((j+1 : ℕ) : k) * monomial 1 (d*(j+1)) *
      (1 - monomial 1 (d*(j+1)))⁻¹
def tateX (d i : ℕ) (a : k) : PowerSeries k :=
  PowerSeries.mk fun n => PowerSeries.coeff n (partialX d i a (n+1))
end ArithmeticThetaTateSeries
namespace ArithmeticThetaCubicModelR0144
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaPolygonCartierR0133 ArithmeticThetaAlgebraicCoordinatesR0143
variable (k : Type u) [Field k] [CharZero k]
def rootSeries (r : ℕ) (j : Fin 3) : PowerSeries k :=
  if j.val = 0 then ArithmeticThetaTateSeries.tateX r 0 (-1)
  else ArithmeticThetaTateSeries.tateX r (r/2) (if j.val = 1 then 1 else -1)
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
def modelScalar (M : Model k T) (U : M.X.Opens) (g : PowerSeries k) :
    M.X.presheaf.obj (Opposite.op U) :=
  M.X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
    (M.p.appTop ((Scheme.ΓSpecIso (CommRingCat.of (PowerSeries k))).inv g))
def ModelCubic (M : Model k T) (s : baseScheme k ⟶ M.X)
    (X : Dual k M s 2) (Y : Dual k M s 3) : Prop :=
  ∀ (U : M.X.Opens) (a : Γ(powerModule k M s 2, U))
    (b : Γ(powerModule k M s 3, U)),
    let ja : M.X.presheaf.obj (Opposite.op U) :=
      (GlobalCartierIdealLineR0133.idealInclusion (s.ker^2)).app U a
    let jb : M.X.presheaf.obj (Opposite.op U) :=
      (GlobalCartierIdealLineR0133.idealInclusion (s.ker^3)).app U b
    (show M.X.presheaf.obj (Opposite.op U) from Y.app U b)^2 * ja^3 =
      (∏ j : Fin 3, ((show M.X.presheaf.obj (Opposite.op U) from X.app U a) -
        modelScalar k M U (rootSeries k r j) * ja)) * jb^2
end ArithmeticThetaCubicModelR0144
namespace AlgebraicGeometry.Scheme.Hom
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of A) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]
@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra A Γ(X, U) :=
  (f.constToPresheaf.app (op U)).hom.toAlgebra
def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' f.constToPresheaf
def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj f.kaehlerPresheaf
def kaehlerToSections (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U) : Type u) → (Γ(f.kaehler, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom s
end AlgebraicGeometry.Scheme.Hom
namespace ArithmeticThetaCompactifiedDifferentialR0145
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaPolygonCartierR0133 ArithmeticThetaGenericEvaluationR0140
variable (k : Type u) [Field k] [CharZero k]
variable {r : ℕ} {hr : 0 < r} {T : Tower k r hr}
def genericIdealInclusion (M : Model k T) (s : baseScheme k ⟶ M.X) (d : ℕ) :
    genericPower k M s d ⟶
      (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) :=
  (Scheme.Modules.pullback (genericInclusion k M)).map
    (GlobalCartierIdealLineR0133.idealInclusion (s.ker ^ d)) ≫
      unitPullback (genericInclusion k M)
def relativeD {F : Type u} [CommRing F] {C : Scheme.{u}}
    (f : C ⟶ Spec (CommRingCat.of F)) (U : C.Opens)
    (a : C.presheaf.obj (Opposite.op U)) : Γ(f.kaehler, U) :=
  letI : Algebra F (C.presheaf.obj (Opposite.op U)) := f.sectionsAlgebra U
  f.kaehlerToSections U (KaehlerDifferential.D F
    (C.presheaf.obj (Opposite.op U)) a)
def differentialAt (M : Model k T) (U : (genericScheme k M).Opens)
    (a : (genericScheme k M).presheaf.obj (Opposite.op U)) :
    Γ((genericStructure k M).kaehler, U) :=
  relativeD (genericStructure k M) U a
theorem _root_.ArithmeticThetaCompactifiedDifferentialR0145.cubicDerivative._proof_2 : Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := by sorry
run_cmd do
  let n := `ArithmeticThetaCompactifiedDifferentialR0145.cubicDerivative._proof_2
  let some ci := (← Lean.getEnv).find? n | throwError "Missing original numeric helper"
  let key : Lean.Meta.AuxLemmaKey := { type := ci.type, isPrivate := false, defeq := false }
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.modifyState env fun s => { s with lemmas := s.lemmas.insert key (ci.name, ci.levelParams) }
def IsGlobalDifferentialFrame (M : Model k T) (s : baseScheme k ⟶ M.X)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
      (genericStructure k M).kaehler) : Prop :=
  ∀ (U : (genericScheme k M).Opens) (a : Γ(genericPower k M s 2, U))
    (b : Γ(genericPower k M s 3, U)),
    let ja : (genericScheme k M).presheaf.obj (Opposite.op U) :=
      (genericIdealInclusion k M s 2).app U a
    let jb : (genericScheme k M).presheaf.obj (Opposite.op U) :=
      (genericIdealInclusion k M s 3).app U b
    let xa : (genericScheme k M).presheaf.obj (Opposite.op U) :=
      (restrictDual k M s 2 X).app U a
    let yb : (genericScheme k M).presheaf.obj (Opposite.op U) :=
      (restrictDual k M s 3 Y).app U b
    jb • (ja • differentialAt k M U xa - xa • differentialAt k M U ja) =
      (2 * yb * ja^2) • Scheme.Modules.Hom.app e.hom U
        (1 : (genericScheme k M).presheaf.obj (Opposite.op U))
end ArithmeticThetaCompactifiedDifferentialR0145
namespace ArithmeticThetaPalomarCoordinates377
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def NormalizedFrame (k : Type u) [Field k] [CharZero k]
    {r : ℕ} {hr : 0 < r} {T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr}
    (h3 : 3 ≤ r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
    (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
    (s : ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k ⟶ M.X)
    (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M
      (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s)
    (d : ℕ) (e : ArithmeticThetaGenericEvaluationR0140.IdentityFrame k M s d) : Prop :=
  ∀ (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s d) (n : ℕ),
    let i := ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr
    let f := (T.atlas n).chart i ≫ M.inclusion n
    let P := (Scheme.Modules.pullback f).obj
      (ArithmeticThetaIdentitySectionsR0138.powerModule k M s d)
    let j := (Scheme.Modules.pullback f).map
      (ArithmeticThetaPolygonCartierR0133.GlobalCartierIdealLineR0133.idealInclusion (s.ker^d)) ≫
        ArithmeticThetaPolygonCartierR0133.unitPullback f
    let q := (Scheme.Modules.pullback f).map φ ≫ ArithmeticThetaPolygonCartierR0133.unitPullback f
    ∃ z : Γ(P, ⊤),
      j.app ⊤ z = (Scheme.ΓSpecIso
        (CommRingCat.of (ArithmeticThetaInfinitesimalPolygonR0129.A k n))).inv
          (ArithmeticThetaIdentitySectionsR0138.equation k r n i ^ d) ∧
      ArithmeticThetaInfinitesimalPolygonR0129.trunc (PowerSeries k) PowerSeries.X n
        (ArithmeticThetaGenericEvaluationR0140.frameValue k M s d e φ) =
        ArithmeticThetaPolygonCohomologyR0131.markedPoint k n 1
          ((Scheme.ΓSpecIso (CommRingCat.of
            (ArithmeticThetaInfinitesimalPolygonR0129.A k n))).hom (q.app ⊤ z))
end ArithmeticThetaPalomarCoordinates377
namespace ArithmeticThetaPalomarCoordinates377
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaPolygonCartierR0133 ArithmeticThetaAlgebraicCoordinatesR0143 ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaCompactifiedDifferentialR0145
theorem algebraic_tate_coordinates :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r)
      (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr)
      (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T)
      (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M)
      (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X)
      (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M
        (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s),
      ∀ odd : Bool, ∃! φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s
        (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd),
        ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ
 := by sorry
end ArithmeticThetaPalomarCoordinates377
namespace ArithmeticThetaPalomarCoordinates377
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaPolygonCartierR0133 ArithmeticThetaAlgebraicCoordinatesR0143 ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaCompactifiedDifferentialR0145
theorem coordinate_exact_poles :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (odd : Bool) (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd)), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ → CategoryTheory.IsIso (ArithmeticThetaAlgebraicCoordinatesR0143.pulled k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) s φ) ∧ ∀ e : ArithmeticThetaGenericEvaluationR0140.IdentityFrame k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd), ArithmeticThetaPalomarCoordinates377.NormalizedFrame k h3 M hM s hs (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e → ArithmeticThetaGenericEvaluationR0140.frameValue k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e φ = 1
 := by sorry
end ArithmeticThetaPalomarCoordinates377
namespace ArithmeticThetaPalomarCoordinates377
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaPolygonCartierR0133 ArithmeticThetaAlgebraicCoordinatesR0143 ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaCompactifiedDifferentialR0145
theorem algebraic_model_cubic :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ArithmeticThetaCubicModelR0144.ModelCubic k M s X Y
 := by sorry
end ArithmeticThetaPalomarCoordinates377
namespace ArithmeticThetaPalomarCoordinates377
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
open ArithmeticThetaInfinitesimalPolygonR0129 ArithmeticThetaProjectiveEffectivityR0135 ArithmeticThetaAlgebraizedMarkedLineR0136 ArithmeticThetaIdentitySectionsR0138 ArithmeticThetaPolygonCartierR0133 ArithmeticThetaAlgebraicCoordinatesR0143 ArithmeticThetaGenericEvaluationR0140 ArithmeticThetaCompactifiedDifferentialR0145
theorem global_normalized_differential (k : Type u) [Field k] [CharZero k]
    (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : Tower k r hr) (he : Even r)
    (M : Model k T) (hM : IsModel k T M)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M (zeroIndex r hr) 1 s)
    (X : Dual k M s 2) (Y : Dual k M s 3)
    (hX : RealizesCoordinate k false M s X) (hY : RealizesCoordinate k true M s Y) :
    ∃! e : (SheafOfModules.unit (genericScheme k M).ringCatSheaf : (genericScheme k M).Modules) ≅
      (genericStructure k M).kaehler, IsGlobalDifferentialFrame k M s X Y e
 := by sorry
end ArithmeticThetaPalomarCoordinates377
end
end Package00
section Package01
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarSharp360
run_cmd Lean.modifyEnv fun env => Lean.Meta.Match.matcherExt.setState (Lean.Meta.auxLemmasExt.setState env {}) {}
def validGram {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  A.IsSymm ∧ (∀ i, Even (A i i)) ∧
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef
noncomputable def theta {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : PowerSeries ℂ :=
  PowerSeries.mk (fun m => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun i => (x i : ℚ)) = (m : ℚ)} : ℂ))
noncomputable def thetaMap {n h : ℕ}
    (A : Fin h → Matrix (Fin n) (Fin n) ℤ) :
    (Fin h → ℂ) →ₗ[ℂ] PowerSeries ℂ :=
  ∑ i, (LinearMap.proj i : (Fin h → ℂ) →ₗ[ℂ] ℂ).smulRight (theta (A i))
def pairing {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x y : Fin n → ℤ) : ℤ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * A i j * y j
def project {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (b v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => pairing A b b * v i - pairing A b v * b i
def step {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℤ) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of (fun i j => if k < j then project A (fun a => C a k) (fun a => C a j) i
    else C i j)
def runPrefix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  ((List.finRange n).take k).foldl (step A) 1
def basisMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    Matrix (Fin n) (Fin n) ℤ := runPrefix A n
def norms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℤ :=
  pairing A (fun i => basisMatrix A i j) (fun i => basisMatrix A i j)
def naturalNorms {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : ℕ :=
  (norms A j).toNat
abbrev Matrices (n h : ℕ) := Fin h → Matrix (Fin n) (Fin n) ℤ
def commonN {n h : ℕ} (A : Matrices n h) : ℕ :=
  Finset.univ.lcm (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def distinctNorms {n h : ℕ} (A : Matrices n h) : Finset ℕ := by
  classical
  exact Finset.univ.image (fun ij : Fin h × Fin n => naturalNorms (A ij.1) ij.2)
def normCount {n h : ℕ} (A : Matrices n h) : ℕ := (distinctNorms A).card
def level (N : ℕ) : ℕ := 24 * N^2
def cutoff {n h : ℕ} (A : Matrices n h) : ℕ :=
  n * 2^(normCount A - 1) *
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (level (commonN A)))) /
      (48 * level (commonN A))
def coefficientMatrix {n h : ℕ} (A : Matrices n h) (B : ℕ) :
    Matrix (Fin (B+1)) (Fin h) ℚ :=
  fun a i => (Nat.card {x : Fin n → ℤ //
    ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
      (fun j => (x j : ℚ)) = (a.val : ℚ)} : ℚ)
/-- Full original sharp kernel conclusion plus actual shell finiteness. -/
theorem sharpFiniteDetermination (n h : ℕ) (hh : 0 < h)
    (A : Matrices n h) (hA : ∀ i, validGram (A i)) :
    (∀ (i : Fin h) (a : ℕ), Finite {x : Fin n → ℤ //
      ((1 / 2 : ℚ) • ((A i).map (Int.castRingHom ℚ)).toQuadraticForm')
        (fun j => (x j : ℚ)) = (a : ℚ)}) ∧
    (∀ B : ℕ, cutoff A ≤ B → LinearMap.ker (thetaMap A) =
      LinearMap.ker (((coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) ∧
    (n = 0 → cutoff A = 0 ∧ ∀ c : Fin h → ℂ,
      thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by
  sorry
end ArithmeticThetaPalomarSharp360
end
end Package01
