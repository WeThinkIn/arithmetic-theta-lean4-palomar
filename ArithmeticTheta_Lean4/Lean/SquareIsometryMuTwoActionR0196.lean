import MetaplecticTestDefinitionsR0196

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace ArithmeticThetaMetaplecticTestsR0196
open CategoryTheory AlgebraicGeometry Opposite
open ArithmeticThetaLineRoot ArithmeticThetaTensorPower ArithmeticThetaCoverComparison
open ArithmeticThetaSquareLinesR0192
open ArithmeticThetaSquareLinesR0192.SquareIsometryInterfaceAdapterR0192
open ArithmeticThetaGeometricLiftsR0141.GeometricShiftLiftR0141.RawAction

namespace SquareIsometryMuTwoActionR0196

variable {Z : Scheme.{0}} {M : Z.Modules}

lemma scale_coordinate {U : Z.Opens} (F : LocalFrame Z M U)
    (a : Γ(Z, ⊤)) (V : Z.Opens) (hV : V ≤ U) :
    frameHomCoordinate F F (scaleHom a (𝟙 M)) V hV =
      Z.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op a := by
  unfold frameHomCoordinate
  rw [scaleHom_app]
  change (F.equiv V hV).symm (_ • F.equiv V hV 1) = _
  rw [← map_smul, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_one]

/-- Endomorphism coordinates in the same source and target frame are independent
of the choice of frame, including on overlaps with zero section ring. -/
lemma end_coordinate_change {U V T : Z.Opens}
    (F : LocalFrame Z M U) (G : LocalFrame Z M V) (f : M ⟶ M)
    (hU : T ≤ U) (hV : T ≤ V) :
    frameHomCoordinate F F f T hU = frameHomCoordinate G G f T hV := by
  apply (transitionUnit (F.equiv T hU) (G.equiv T hV)).isUnit.mul_left_cancel
  exact (frameHomCoordinate_change F F G G f T hU hV).symm

/-- Every endomorphism of an invertible sheaf is multiplication by one uniquely
specified global section of the actual structure sheaf. -/
lemma end_scalar (hM : ArithmeticThetaNormalizedSections.IsLineBundle Z M)
    (f : M ⟶ M) : ∃! a : Γ(Z, ⊤), f = scaleHom a (𝟙 M) := by
  let C := HomLine.pairFrames hM hM
  let c := fun i => frameHomCoordinate (C.left i) (C.left i) f (C.opens i) le_rfl
  have hc : TopCat.Presheaf.IsCompatible Z.presheaf C.opens c := by
    intro i j
    change Z.presheaf.map (homOfLE inf_le_left).op (c i) =
      Z.presheaf.map (homOfLE inf_le_right).op (c j)
    dsimp [c]
    rw [← frameHomCoordinate_restrict, ← frameHomCoordinate_restrict]
    exact end_coordinate_change _ _ f _ _
  obtain ⟨a, ha, hu⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf C.opens ⊤
    (fun _ => homOfLE le_top) C.covers c hc
  refine ⟨a, ?_, ?_⟩
  · apply HomLine.frameHomCoordinate_ext_top C.opens C.covers C.left C.left
    intro i
    rw [scale_coordinate]
    exact (ha i).symm
  · intro b hb
    apply hu b
    intro i
    dsimp [c]
    rw [hb, scale_coordinate]
    rfl

lemma scale_injective (hM : ArithmeticThetaNormalizedSections.IsLineBundle Z M)
    {a b : Γ(Z, ⊤)} (h : scaleHom a (𝟙 M) = scaleHom b (𝟙 M)) : a = b := by
  obtain ⟨c, hc, hu⟩ := end_scalar hM (scaleHom a (𝟙 M))
  exact (hu a rfl).trans (hu b h).symm

lemma scale_comp {N P : Z.Modules} (a b : Γ(Z, ⊤)) (f : M ⟶ N) (g : N ⟶ P) :
    scaleHom a f ≫ scaleHom b g = scaleHom (a * b) (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, scaleHom_app,
    Scheme.Modules.Hom.app_smul, map_mul, mul_smul]

/-- Multiplication by a global unit is an actual sheaf isomorphism. -/
def scaleIso {N : Z.Modules} (a : Γ(Z, ⊤)ˣ) (e : M ≅ N) : M ≅ N where
  hom := scaleHom (a : Γ(Z, ⊤)) e.hom
  inv := scaleHom ((a⁻¹ : Γ(Z, ⊤)ˣ) : Γ(Z, ⊤)) e.inv
  hom_inv_id := by rw [scale_comp, e.hom_inv_id, Units.mul_inv, scaleHom_one]
  inv_hom_id := by rw [scale_comp, e.inv_hom_id, Units.inv_mul, scaleHom_one]

/-- A scalar endomorphism whose tensor square is the identity has square one
as a global section; separatedness checks this on every frame chart. -/
lemma scalar_square (hM : ArithmeticThetaNormalizedSections.IsLineBundle Z M)
    (a : Γ(Z, ⊤))
    (h : tensorPowerMap (scaleHom a (𝟙 M)) 2 = 𝟙 (tensorPower Z M 2)) : a ^ 2 = 1 := by
  let C := HomLine.pairFrames hM hM
  apply TopCat.Sheaf.eq_of_locally_eq' Z.sheaf C.opens ⊤
    (fun _ => homOfLE le_top) C.covers
  intro i
  have hc := congrArg (fun f => frameHomCoordinate
    (tensorPowerFrame Z M (C.opens i) (C.left i) 2)
    (tensorPowerFrame Z M (C.opens i) (C.left i) 2) f (C.opens i) le_rfl) h
  rw [frameHomCoordinate_tensorPowerMap, scale_coordinate, frameHomCoordinate_id] at hc
  change Z.presheaf.map (homOfLE le_top).op (a ^ 2) =
    Z.presheaf.map (homOfLE le_top).op 1
  simpa only [map_pow, map_one] using hc

variable {W : Z.Modules} {A B : SquareLine Z W}

lemma scaled_compatible (u : MuTwo Z) (e : SquareIso A B) :
    tensorPowerMap (scaleIso u.val e.val).hom 2 ≫ B.square.hom = A.square.hom := by
  apply pure_square_ext (line_of_invertible A.line A.invertible) (target_line A)
  intro U s
  have he := ConcreteCategory.congr_hom
    (congrArg (fun f => Scheme.Modules.Hom.app f U) e.property)
    (tensorPowerSection Z A.line 2 U s)
  change B.square.hom.app U ((tensorPowerMap e.val.hom 2).app U _) = _ at he
  rw [tensorPowerMap_section] at he
  change B.square.hom.app U ((tensorPowerMap (scaleIso u.val e.val).hom 2).app U _) = _
  rw [tensorPowerMap_section]
  change B.square.hom.app U (tensorPowerSection Z B.line 2 U
    ((scaleHom (u.val : Γ(Z, ⊤)) e.val.hom).app U s)) = _
  rw [scaleHom_app, ArithmeticThetaRelativeDiscriminantR0171.InitialHodgeSection.tensor_smul]
  have hu : (u.val : Γ(Z, ⊤)) ^ 2 = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun x : Γ(Z, ⊤)ˣ => (x : Γ(Z, ⊤))) u.property
  rw [← map_pow, hu, map_one, one_smul]
  exact he

lemma squareIso_ext {e e' : SquareIso A B}
    (h : ∀ (U : Z.Opens) (v : Γ(A.line,U)), e.val.hom.app U v = e'.val.hom.app U v) :
    e = e' := by
  apply Subtype.ext
  apply Iso.ext
  apply Scheme.Modules.hom_ext
  intro U
  ext v
  exact h U v

lemma comparison_square (e e' : SquareIso A B) :
    tensorPowerMap (e'.val.hom ≫ e.val.inv) 2 = 𝟙 (tensorPower Z A.line 2) := by
  have hinv : tensorPowerMap e.val.inv 2 ≫ A.square.hom = B.square.hom := by
    calc
      tensorPowerMap e.val.inv 2 ≫ A.square.hom =
          tensorPowerMap e.val.inv 2 ≫ (tensorPowerMap e.val.hom 2 ≫ B.square.hom) :=
        congrArg (fun f => tensorPowerMap e.val.inv 2 ≫ f) e.property.symm
      _ = B.square.hom := by
        rw [← Category.assoc, ← tensorPowerMap_comp,
          e.val.inv_hom_id, tensorPowerMap_id, Category.id_comp]
  apply (cancel_mono A.square.hom).mp
  rw [tensorPowerMap_comp, Category.assoc, hinv, e'.property, Category.id_comp]

/-- Compare two existing square isomorphisms using the unique global scalar of
 their quotient automorphism, without choosing a global trivialization. -/
lemma comparison_exists (e e' : SquareIso A B) : ∃ u : MuTwo Z, Scales u e e' := by
  obtain ⟨a, ha, _⟩ := end_scalar (line_of_invertible A.line A.invertible)
    (e'.val.hom ≫ e.val.inv)
  have ha2 : a ^ 2 = 1 := scalar_square (line_of_invertible A.line A.invertible) a
    (by rw [← ha]; exact comparison_square e e')
  let v : Γ(Z, ⊤)ˣ := ⟨a, a, by simpa only [pow_two] using ha2,
    by simpa only [pow_two] using ha2⟩
  have hv : v ^ 2 = 1 := by apply Units.ext; exact ha2
  refine ⟨⟨v, hv⟩, ?_⟩
  have hh : e'.val.hom = scaleHom a e.val.hom := by
    have hh := congrArg (fun f => f ≫ e.val.hom) ha
    simpa only [Category.assoc, e.val.inv_hom_id, Category.comp_id,
      scaleHom_comp, Category.id_comp] using hh
  intro U s
  change e'.val.hom.app U s = Z.presheaf.map (homOfLE le_top).op a • e.val.hom.app U s
  rw [hh, scaleHom_app]

lemma comparison_unique (e e' : SquareIso A B) (u v : MuTwo Z)
    (hu : Scales u e e') (hv : Scales v e e') : u = v := by
  have h : scaleHom (u.val : Γ(Z, ⊤)) e.val.hom = scaleHom (v.val : Γ(Z, ⊤)) e.val.hom := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    simpa only [scaleHom_app] using (hu U s).symm.trans (hv U s)
  have hh := congrArg (fun f => f ≫ e.val.inv) h
  rw [scaleHom_comp, scaleHom_comp, e.val.hom_inv_id] at hh
  apply Subtype.ext
  apply Units.ext
  exact scale_injective (line_of_invertible A.line A.invertible) hh

end SquareIsometryMuTwoActionR0196

open SquareIsometryMuTwoActionR0196

/-- The actual global mu_2 units act uniquely on square isomorphisms, and any
 two such isomorphisms differ by a unique unit, on arbitrary test schemes. -/
theorem square_isometry_mu2_action
    (Z : Scheme.{0}) (W : Z.Modules) (A B : SquareLine Z W)
    (_h2 : IsUnit (2 : Z.presheaf.obj (Opposite.op ⊤))) :
    (∀ (u : MuTwo Z) (e : SquareIso A B), ∃! e' : SquareIso A B, Scales u e e') ∧
    (∀ e e' : SquareIso A B, ∃! u : MuTwo Z, Scales u e e') := by
  constructor
  · intro u e
    refine ⟨⟨scaleIso u.val e.val, scaled_compatible u e⟩, ?_, ?_⟩
    · intro U s
      exact scaleHom_app _ _ U s
    · intro e' he'
      apply squareIso_ext
      intro U s
      exact (he' U s).trans (scaleHom_app _ _ U s).symm
  · intro e e'
    obtain ⟨u, hu⟩ := comparison_exists e e'
    exact ⟨u, hu, fun v hv => comparison_unique e e' v u hv hu⟩

end ArithmeticThetaMetaplecticTestsR0196

#print axioms ArithmeticThetaMetaplecticTestsR0196.square_isometry_mu2_action

