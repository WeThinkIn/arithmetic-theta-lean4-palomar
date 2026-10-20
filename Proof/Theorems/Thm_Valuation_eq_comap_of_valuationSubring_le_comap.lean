module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_Valuation_eq_comap_of_valuationSubring_le_comap

@[expose] public section

theorem Valuation.eq_comap_of_valuationSubring_le_comap {L L' : Type*} [Field L] [Field L'] {v : Valuation L' (WithZero (Multiplicative ℤ))} {w : Valuation L (WithZero (Multiplicative ℤ))} (hv : Function.Surjective v) (hw : Function.Surjective w) (σ : L ≃+* L') (hle : w.valuationSubring ≤ v.valuationSubring.comap σ.toRingHom) : w = v.comap σ.toRingHom := by p2m_exact_reverting @_root_.P2MW.S_Valuation_eq_comap_of_valuationSubring_le_comap.solution
