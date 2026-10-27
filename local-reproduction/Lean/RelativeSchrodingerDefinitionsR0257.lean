import RelativeCyclicThetaSplittingR0256
import RelativePrimitiveThetaCommutatorR0256
import RelativeSymmetricLiftSignsR0256

/-! Relative sections and the orbit comparison for the actual rigidified theta line.
These predicates specify new proof obligations; they contain no chosen basis or frame. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace ArithmeticThetaRelativeSchrodingerR0257
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaRelationsR0256
open scoped TensorProduct

/-- Finite projectivity and geometric rank, with the given scalar action. -/
def FiniteProjectiveRank (R : Type u) [CommRing R] (V : Type v)
    [AddCommGroup V] [Module R V] (d : ℕ) : Prop :=
  Module.Finite R V ∧ Module.Projective R V ∧
    ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Module.Finite K (K ⊗[R] V) ∧ Module.finrank K (K ⊗[R] V) = d

/-- The invariant line is the actual eigenspace, not an unrelated rank-one type. -/
abbrev Fixed (R : Type u) [CommRing R] (V : Type v)
    [AddCommGroup V] [Module R V] (A : Module.End R V) := A.eigenspace 1

/-- Canonical orbit sum, together with the two standard operator equations.
The common line need not have a global generator. -/
def OrbitComparison (R : Type u) [CommRing R] (V : Type v)
    [AddCommGroup V] [Module R V] (m : ℕ)
    (A B : Module.End R V) (c : Rˣ) : Prop :=
  FiniteProjectiveRank R (Fixed R V A) 1 ∧
    ∃ e : (Fin m → Fixed R V A) ≃ₗ[R] V,
      (∀ w, e w = ∑ i : Fin m, (B ^ i.val) ((w i).val)) ∧
      (∀ w, A (e w) = e (fun i => (c : R) ^ i.val • w i)) ∧
      (∀ (i : Fin m) (w : Fixed R V A),
        B (e (Pi.single i w)) = (B ^ ((i.val + 1) % m)) w.val)

/-- The canonical eigenspace inclusion after arbitrary scalar extension. -/
def FixedBaseChange (R : Type u) [CommRing R] (V : Type v)
    [AddCommGroup V] [Module R V] (A : Module.End R V) : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra R S],
    ∃ e : S ⊗[R] (Fixed R V A) ≃ₗ[S]
        Fixed S (S ⊗[R] V) (A.baseChange S),
      ∀ (s : S) (w : Fixed R V A),
        (e (s ⊗ₜ[R] w)).val = s ⊗ₜ[R] w.val

variable {R : Type u} [CommRing R] (E : EllipticFamily R)

abbrev sections (m : ℕ) := Γ(thetaLine E m, ⊤)

/-- Actual structural scalar action, retained explicitly in every predicate. -/
abbrev sectionModule (m : ℕ) : Module R (sections E m) :=
  Scheme.TwoAffineOpenCover.moduleSectionsOfHom E.projection (thetaLine E m) ⊤

def SectionFacts (m : ℕ) : Prop :=
  letI := sectionModule E m
  FiniteProjectiveRank R (sections E m) m ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S],
      let f := E.projection
      let t := Scheme.TwoAffineOpenCover.specMap R S
      let M := thetaLine E m
      letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
        (Limits.pullback.snd f t)
        ((Scheme.Modules.pullback (Limits.pullback.fst f t)).obj M)
        ((Limits.pullback.fst f t) ⁻¹ᵁ ⊤)
      ∃ e : S ⊗[R] sections E m ≃ₗ[S]
          Γ((Scheme.Modules.pullback (Limits.pullback.fst f t)).obj M,
            (Limits.pullback.fst f t) ⁻¹ᵁ ⊤),
        ∀ (s : S) (w : sections E m),
          e (s ⊗ₜ[R] w) = s • Scheme.Modules.pullbackLocalSection
            (Limits.pullback.fst f t) w

/-- The actual geometric operators, with no supplied representation or order laws. -/
def GeometricComparison (m : ℕ) (M : FamilyLevel R E (2*m)) : Prop :=
  ∃ (ι : Lift E m (inverse E))
    (α : Lift E m (translation E M.x)) (β : Lift E m (translation E M.y)) (c : Rˣ),
    NormalizedInversion E m ι ∧
    MidpointNormalized E m M.x ι α ∧ Symmetric E m M.x ι α ∧
    MidpointNormalized E m M.y ι β ∧ Symmetric E m M.y ι β ∧
    Commutator E m M.x M.y α β c ∧ PrimitiveUnit m c ∧
    (letI := sectionModule E m
     let A := RelativePrimitiveThetaCommutator.thetaAct E m M.x α
     let B := RelativePrimitiveThetaCommutator.thetaAct E m M.y β
     A ^ m = 1 ∧ B ^ m = 1 ∧
       OrbitComparison R (sections E m) m A B c ∧
       FixedBaseChange R (sections E m) A)

end ArithmeticThetaRelativeSchrodingerR0257
