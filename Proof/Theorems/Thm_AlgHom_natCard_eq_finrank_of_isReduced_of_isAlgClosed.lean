module

public import P2M.Util
public import P2M.Sol.S_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed

@[expose] public section

theorem AlgHom.natCard_eq_finrank_of_isReduced_of_isAlgClosed (K B : Type*) [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B] : Nat.card (B →ₐ[K] K) = Module.finrank K B := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_natCard_eq_finrank_of_isReduced_of_isAlgClosed.solution
