module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot

@[expose] public section

open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] [IsLocallyNoetherian V] (K : V.OrderedAffineCover) (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) (hStep : ∀ k, (OModulePresheaf.idealPowQuot π (Scheme.IdealSheafData.vanishingIdeal Y) F k).CechFinite K) : F.CechFinite K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot.solution
