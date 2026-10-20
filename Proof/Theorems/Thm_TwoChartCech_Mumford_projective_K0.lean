module

public import Definitions.Def_AlgebraicGeometry_MumfordTruncation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Module.Projective
public import P2M.Util
public import P2M.Sol.S_TwoChartCech_Mumford_projective_K0

@[expose] public section

universe u v w

open scoped TensorProduct

theorem TwoChartCech.Mumford.projective_K0
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {C0 : Type v} {C1 : Type w} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    [Module.Flat R C0] [Module.Flat R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (LinearMap.ker d)] [Module.Finite R (C1 ⧸ LinearMap.range d)] :
    Module.Projective R (TwoChartCech.Mumford.K0 d) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Mumford_projective_K0.solution
