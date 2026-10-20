module

public import CoherentMetaplecticPullbackR0207

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaMetaplecticStackR0207
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open ArithmeticThetaMetaplecticComparisonR0206

namespace CoherentTautologicalLineProof

variable (L : ℕ) (B : Scheme.{0}) (C : Coherence L B)

/-- Forget the family but retain its specified root line and the actual
geometric pullback comparison. Normalization supplies both coherence laws. -/
def transformation : Pseudofunctor.StrongTrans C.functor
    (ArithmeticThetaRootStackR0198.modulesOver B) where
  app S := (lineForget (group L S.as.unop.left)).toCatHom
  naturality f := Cat.Hom.isoMk (linePull L B f.as.unop)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 _ := Subsingleton.elim _ _
    subst η
    simp
  naturality_id S := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change ((pull L (𝟙 S.as.unop.left)).line X).hom ≫
      (Scheme.Modules.pullbackId S.as.unop.left).hom.app X.root.line =
      ((group L S.as.unop.left).arrow _ _ ((C.unit S.as).hom.toNatTrans.app X)).line.hom ≫
        𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
    exact (C.unit_normalized S.as.unop X).2.symm
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext X
    change ((pull L (g.as.unop.left ≫ f.as.unop.left)).line X).hom ≫
      (Scheme.Modules.pullbackComp g.as.unop.left f.as.unop.left).inv.app X.root.line =
      ((group L _).arrow _ _ ((C.comp f.as g.as).hom.toNatTrans.app X)).line.hom ≫
        𝟙 _ ≫ ((pull L g.as.unop.left).line ((pull L f.as.unop.left).functor.obj X)).hom ≫
        𝟙 _ ≫ (Scheme.Modules.pullback g.as.unop.left).map
          ((pull L f.as.unop.left).line X).hom ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact (C.comp_normalized _ _ _ f.as.unop g.as.unop X).2.symm

def forgetData : ForgetData L B C where
  transformation := transformation L B C
  app_eq _ := rfl
  naturality_eq _ _ _ := HEq.rfl

end CoherentTautologicalLineProof

/-- The actual specified cotangent-root line is coherent under all base changes,
with precisely the accepted line-forgetful and geometric pullback maps. -/
theorem coherent_tautological_line :
    ∀ (L : ℕ) (B : AlgebraicGeometry.Scheme.{0})
      (C : ArithmeticThetaMetaplecticStackR0207.Coherence L B),
      Nonempty (ArithmeticThetaMetaplecticStackR0207.ForgetData L B C) := by
  intro L B C
  exact ⟨CoherentTautologicalLineProof.forgetData L B C⟩

#print axioms coherent_tautological_line
end ArithmeticThetaMetaplecticStackR0207
