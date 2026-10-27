import SquareLineComparisonDefinitionsR0192

/-! Adapt the accepted square-isomorphism torsor without changing its cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace ArithmeticThetaSquareLinesR0192
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaTensorPower ArithmeticThetaLineRoot ArithmeticThetaNormalizedSections
open ArithmeticThetaPullback ArithmeticThetaCoverComparison

namespace SquareIsometryInterfaceAdapterR0192

/-- Invertibility gives the actual natural local rank-one trivializations. -/
lemma line_of_invertible {Z : Scheme.{0}} (M : Z.Modules)
    (hM : Scheme.Modules.IsInvertible M) : IsLineBundle Z M := by
  intro z
  obtain ⟨U, s, hz, hs⟩ :=
    ArithmeticThetaBoundaryHodgeR0182.CompactHodgeLatticeExtensionR0182.local_frame_exists hM z
  exact ⟨U, hz, ⟨localFrameIso Z M U
    (ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.frame M s hs)⟩⟩

/-- The specified square isomorphism supplies the line structure on W. -/
lemma target_line {Z : Scheme.{0}} {W : Z.Modules} (A : SquareLine Z W) :
    IsLineBundle Z W := by
  intro z
  obtain ⟨U, hz, ⟨e⟩⟩ := line_of_invertible A.line A.invertible z
  let F := tensorPowerFrame Z A.line U (localFrameOfIso Z A.line U e) 2
  exact ⟨U, hz, ⟨localFrameIso Z W U
    (ArithmeticThetaDegreeAssembly.inverseImageFrame A.square.symm F)⟩⟩

/-- On a line, pure squares of local frames determine a tensor-square map. -/
lemma pure_square_ext {Y : Scheme.{0}} {M N : Y.Modules}
    (hM : IsLineBundle Y M) (hN : IsLineBundle Y N)
    {a b : tensorPower Y M 2 ⟶ N}
    (h : ∀ (U : Y.Opens) (s : Γ(M,U)),
      a.app U (tensorPowerSection Y M 2 U s) =
        b.app U (tensorPowerSection Y M 2 U s)) : a = b := by
  let C := HomLine.pairFrames hM hN
  apply HomLine.frameHomCoordinate_ext_top C.opens C.covers
    (fun i => tensorPowerFrame Y M (C.opens i) (C.left i) 2) C.right
  intro i
  unfold frameHomCoordinate
  have hf : (tensorPowerFrame Y M (C.opens i) (C.left i) 2).equiv (C.opens i) le_rfl 1 =
      tensorPowerSection Y M 2 (C.opens i) ((C.left i).equiv (C.opens i) le_rfl 1) := by
    simpa only [one_pow] using
      (tensorPowerSection_frame Y M (C.opens i) (C.left i) 2 (C.opens i) le_rfl 1).symm
  rw [hf, h]

/-- The all-open interface is exactly the accepted tensor-map equation. -/
lemma isometry_iff {Z Y : Scheme.{0}} {W : Z.Modules} (f : Y ⟶ Z)
    (A B : SquareLine Z W)
    (e : (Scheme.Modules.pullback f).obj A.line ≅ (Scheme.Modules.pullback f).obj B.line) :
    IsSquareIsometry f A B e ↔
      tensorPowerMap e.hom 2 ≫ (pullbackPowerIso f B.square).hom =
        (pullbackPowerIso f A.square).hom := by
  constructor
  · intro h
    apply pure_square_ext
      (pullback_isLineBundle Y Z f A.line (line_of_invertible A.line A.invertible))
      (pullback_isLineBundle Y Z f W (target_line A))
    intro U s
    change (squarePull f B).hom.app U
      ((tensorPowerMap e.hom 2).app U (tensorPowerSection Y _ 2 U s)) = _
    rw [tensorPowerMap_section]
    exact (h U s).symm
  · intro h U s
    have he := ConcreteCategory.congr_hom
      (congrArg (fun a => Scheme.Modules.Hom.app a U) h)
      (tensorPowerSection Y _ 2 U s)
    change (squarePull f B).hom.app U
      ((tensorPowerMap e.hom 2).app U (tensorPowerSection Y _ 2 U s)) = _ at he
    rw [tensorPowerMap_section] at he
    exact he.symm

/-- Both interfaces use the same composition and equality pullback comparisons. -/
lemma transport_eq {Z Y S : Scheme.{0}} {W : Z.Modules} (p : Y ⟶ Z)
    (A B : SquareLine Z W)
    (e : (Scheme.Modules.pullback p).obj A.line ≅ (Scheme.Modules.pullback p).obj B.line)
    (f : S ⟶ Z) (g : S ⟶ Y) (hg : g ≫ p = f) :
    transportIsometry p A B e f g hg = pullbackIsoOver p f A.line B.line ⟨g,hg⟩ e := rfl

end SquareIsometryInterfaceAdapterR0192

open SquareIsometryInterfaceAdapterR0192

/-- The accepted rank-two torsor, expressed in the invertible-sheaf interface. -/
theorem square_isometry_interface_adapter
    (Z : Scheme.{0}) (W : Z.Modules) (A B : SquareLine Z W)
    (h2 : IsUnit (2 : Z.presheaf.obj (Opposite.op ⊤))) :
    ∃ (T : Scheme.{0}) (p : T ⟶ Z)
      (e : (Scheme.Modules.pullback p).obj A.line ≅ (Scheme.Modules.pullback p).obj B.line),
      IsFinite p ∧ Etale p ∧ Surjective p ∧ (∀ z : Z, Scheme.Hom.finrank p z = 2) ∧
      IsSquareIsometry p A B e ∧
      ∀ (S : Scheme.{0}) (f : S ⟶ Z)
        (w : (Scheme.Modules.pullback f).obj A.line ≅ (Scheme.Modules.pullback f).obj B.line),
        IsSquareIsometry f A B w →
        ∃! g : {g : S ⟶ T // g ≫ p = f},
          transportIsometry p A B e f g.val g.property = w := by
  obtain ⟨T, p, e, hfin, het, hsur, hdeg, huniv⟩ :=
    square_isomorphism_torsor Z h2 A.line B.line W
      (line_of_invertible A.line A.invertible) (line_of_invertible B.line B.invertible)
      (target_line A) A.square B.square
  refine ⟨T, p, e.val, hfin, het, hsur, hdeg, (isometry_iff p A B e.val).mpr e.property, ?_⟩
  intro S f w hw
  simpa only [transport_eq] using huniv S f ⟨w, (isometry_iff f A B w).mp hw⟩

end ArithmeticThetaSquareLinesR0192

#print axioms ArithmeticThetaSquareLinesR0192.square_isometry_interface_adapter
