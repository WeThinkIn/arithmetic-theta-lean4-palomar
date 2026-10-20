module

public import Mathlib
public import Definitions.Def_PresheafOfModules_InternalHom
public import P2M.Util
public import P2M.Sol.S_PresheafOfModules_isSheaf_ihomObj

@[expose] public section

universe u

open CategoryTheory
theorem PresheafOfModules.isSheaf_ihomObj {C : Type u} [Category.{u} C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}} (F N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {J : GrothendieckTopology C} (hN : Presheaf.IsSheaf J N.presheaf) :
    Presheaf.IsSheaf J (PresheafOfModules.ihomObj F N).presheaf := by p2m_exact_reverting @_root_.P2MW.S_PresheafOfModules_isSheaf_ihomObj.solution
