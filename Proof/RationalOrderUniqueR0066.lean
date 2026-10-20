module

public import LocalOrderDefinitionsR0066

@[expose] public section

/-! Presentation independence for the finite rational orders on the generic chart. -/
set_option autoImplicit false
noncomputable section
universe u
namespace ArithmeticThetaLocalOrdersR0066

/-- The ideal-power definition of a finite order gives the DVR's additive valuation. -/
lemma exactOrder_addVal (k : Type u) [Field k] [CharZero k]
    (P : Ideal (GenericChart k)) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (a : GenericChart k) (n : ℕ) (h : ExactOrder k P a n) :
    IsDiscreteValuationRing.addVal (Localization.AtPrime P)
      (algebraMap (GenericChart k) (Localization.AtPrime P) a) = n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  unfold ExactOrder at h
  rw [Localization.AtPrime.map_eq_maximalIdeal] at h
  simp only [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow] at h
  apply le_antisymm ?_ h.1
  exact (ENat.lt_natCast_add_one_iff).mp (lt_of_not_ge (by simpa using h.2))

/-- The difference of finite numerator and denominator orders is independent of presentation. -/
theorem rational_order_unique (k : Type u) [Field k] [CharZero k]
    (P : Ideal (GenericChart k)) [P.IsPrime]
    [IsDiscreteValuationRing (Localization.AtPrime P)]
    (f : FunctionField k) (m n : ℤ) :
    HasOrder k P f m → HasOrder k P f n → m = n := by
  rintro ⟨a, b, na, nb, hb, hab, ha, hbo, hm⟩
    ⟨c, d, nc, nd, hd, hcd, hc, hdo, hn⟩
  have hcross : a * d = c * b := by
    apply IsFractionRing.injective (GenericChart k) (FunctionField k)
    change toFunctionField k (a * d) = toFunctionField k (c * b)
    rw [map_mul, map_mul, ← hab, ← hcd]
    ring
  have hlocal := congrArg
    (fun x => IsDiscreteValuationRing.addVal (Localization.AtPrime P)
      (algebraMap (GenericChart k) (Localization.AtPrime P) x)) hcross
  simp only [map_mul, IsDiscreteValuationRing.addVal_mul,
    exactOrder_addVal k P a na ha, exactOrder_addVal k P b nb hbo,
    exactOrder_addVal k P c nc hc, exactOrder_addVal k P d nd hdo] at hlocal
  have hnat : na + nd = nc + nb := by exact_mod_cast hlocal
  omega

end ArithmeticThetaLocalOrdersR0066
