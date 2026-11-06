module

public import FormalSchrodingerDefinitionsR0119
public import UnaryThetaProducts
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Tactic.ENatToNat

@[expose] public section

/-! Bilateral theta convergence in the native Laurent-series valuation topology. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaSchrodingerR0119
open Filter Topology

/-- The linear annular shift is absorbed into the accepted quadratic shell bound. -/
lemma annular_residue_local_finite (m : ℕ) (ν j N : ℤ) :
    Set.Finite {r : ℤ | Int.ModEq (m : ℤ) r ν ∧ r^2+j*r ≤ N} := by
  let C : ℕ := (2*N+j^2).toNat
  have h := ArithmeticThetaCosets.weighted_residue_local_finite 1
    (fun _ => m) (fun _ => 1) (fun _ => ν) (by intro i; decide) C
  apply (h.image (fun r => r 0)).subset
  intro r hr
  refine ⟨fun _ => r, ⟨fun _ => hr.1, ?_⟩, rfl⟩
  have hC : 2*N+j^2 ≤ (C : ℤ) := by dsimp [C]; omega
  have hb : r^2 ≤ (C : ℤ) := by nlinarith [sq_nonneg (r+j), hr.2]
  simpa using hb

/-- Literal multiplication of the two monomials after the annular substitution. -/
lemma theta_annular_term (k : Type u) [Field k] (m : ℕ) (ν : Fin m)
    (j : ℤ) (x : kˣ) (r : ℤ) :
    annularTerms k (theta k m ν) j x r =
      if Int.ModEq (m : ℤ) r (ν.val : ℤ) then
        HahnSeries.single (r^2+j*r) ((x : k)^r) else 0 := by
  classical
  simp only [annularTerms, theta, monomial]
  split_ifs <;> simp [HahnSeries.single_mul_single]

/-- A monomial with large exponent belongs to the corresponding valuation ball. -/
lemma annular_term_valuation_le (k : Type u) [Field k] (m : ℕ) (ν : Fin m)
    (j : ℤ) (x : kˣ) (D r : ℤ)
    (hr : ¬ (Int.ModEq (m : ℤ) r (ν.val : ℤ) ∧ r^2+j*r ≤ D)) :
    Valued.v (annularTerms k (theta k m ν) j x r) ≤ WithZero.exp (-D) := by
  rw [LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]
  intro n hn
  rw [theta_annular_term]
  by_cases hres : Int.ModEq (m : ℤ) r (ν.val : ℤ)
  · rw [if_pos hres]
    have hlarge : D < r^2+j*r := lt_of_not_ge (fun hle => hr ⟨hres, hle⟩)
    simp [ne_of_lt (hn.trans hlarge)]
  · rw [if_neg hres]
    simp

/-- Both tails tend to zero on the cofinite filter, in the actual valued field. -/
lemma theta_annular_tendsto_zero (k : Type u) [Field k] (m : ℕ) (ν : Fin m)
    (j : ℤ) (x : kˣ) :
    Tendsto (annularTerms k (theta k m ν) j x) cofinite (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero (K k) (WithZero (Multiplicative ℤ))).tendsto_right_iff]
  intro γ _
  let γ' : (WithZero (Multiplicative ℤ))ˣ := Units.map MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom γ
  let D : ℤ := -WithZero.log (γ' : WithZero (Multiplicative ℤ)) + 1
  have hevent : ∀ᶠ r : ℤ in cofinite,
      ¬ (Int.ModEq (m : ℤ) r (ν.val : ℤ) ∧ r^2+j*r ≤ D) := by
    simpa only [eventually_cofinite, not_not] using
      annular_residue_local_finite m (ν.val : ℤ) j D
  filter_upwards [hevent] with r hr
  change Valued.v.restrict (annularTerms k (theta k m ν) j x r) < γ.val
  rw [Valued.v.restrict_lt_iff_lt_embedding]
  change Valued.v (annularTerms k (theta k m ν) j x r) < (γ' : WithZero (Multiplicative ℤ))
  apply lt_of_le_of_lt (annular_term_valuation_le k m ν j x D r hr)
  rw [← WithZero.exp_log γ'.ne_zero, WithZero.exp_lt_exp]
  dsimp [D]
  omega

/-- The exact assigned convergence theorem, for all bilateral indices and annular shifts. -/
theorem theta_annular_convergence :
    ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m], Even m →
      ∀ (ν : Fin m) (j : ℤ) (x : kˣ),
      (∀ N : ℤ, Set.Finite {r : ℤ |
        Int.ModEq (m : ℤ) r (ν.val : ℤ) ∧ r^2+j*r ≤ N}) ∧
      Summable (annularTerms k (theta k m ν) j x) := by
  intro k _ _ m _ _ ν j x
  refine ⟨annular_residue_local_finite m (ν.val : ℤ) j, ?_⟩
  let : NonarchimedeanRing (K k) :=
    (Valued.v (R := K k)).subgroups_basis.nonarchimedean
  exact NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (theta_annular_tendsto_zero k m ν j x)

end ArithmeticThetaSchrodingerR0119
