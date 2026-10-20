module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import P2M.Util
public import P2M.Sol.S_Module_Flat_of_flat_of_faithfullyFlat_right

@[expose] public section

set_option autoImplicit false

open TensorProduct

theorem Module.Flat.of_flat_of_faithfullyFlat_right (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_of_flat_of_faithfullyFlat_right.solution
