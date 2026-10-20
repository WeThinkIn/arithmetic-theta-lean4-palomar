module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import P2M.Util
public import P2M.Sol.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed

@[expose] public section

universe u

theorem AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IrreducibleSpace X] :
    GeometricallyIrreducible f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.solution
