module

public import SchemeSchrodingerDefinitionsR0261

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaSchemeSchrodingerR0261
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ArithmeticThetaSchemeThetaMarkingR0259
namespace SchemeSchrodingerOrbit
open ArithmeticThetaRelativeSchrodingerR0257
open RelativeSchrodingerModule

local instance (S : Scheme.{u}) : HasFiniteBiproducts S.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {S : Scheme.{u}} {W : S.Modules}

abbrev sections (U : S.Opens) : S.Modules ⥤ ModuleCat.{u} Γ(S,U) := SheafOfModules.evaluation S.ringCatSheaf (Opposite.op U)

instance (U : S.Opens) : (sections U).Additive where
  map_add := rfl

instance (U : S.Opens) : PreservesFiniteLimits (sections U) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation S.ringCatSheaf (Opposite.op U)))

abbrev act (A : End W) (U : S.Opens) : Module.End Γ(S, U) Γ(W, U) :=
  ((sections U).map A).hom

def actHom (U : S.Opens) : End W →+* Module.End Γ(S, U) Γ(W, U) where
  toFun A := act A U
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] lemma act_pow (A : End W) (U : S.Opens) (n : ℕ) :
    act (A ^ n) U = (act A U) ^ n := map_pow (actHom U) A n

abbrev res (U : S.Opens) : Γ(S, ⊤) →+* Γ(S, U) :=
  (S.presheaf.map (homOfLE le_top).op).hom

@[simp] lemma unitAction_apply (c : Γ(S, ⊤)ˣ) (U : S.Opens) (x : Γ(W, U)) :
    (unitAction W c).app U x = res U c • x := rfl

lemma local_relations (m : ℕ) (A B : End W) (c : Γ(S, ⊤)ˣ)
    (h : Relations m A B c) (U : S.Opens) :
    act A U ^ m = 1 ∧ act B U ^ m = 1 ∧
      act A U * act B U = (res U c) • (act B U * act A U) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← act_pow]
    change (actHom U) (A ^ m) = (actHom U) 1
    exact congrArg (actHom U) h.1
  · rw [← act_pow]
    change (actHom U) (B ^ m) = (actHom U) 1
    exact congrArg (actHom U) h.2.1
  · exact congrArg (actHom U) h.2.2

lemma local_primitive (m : ℕ) (c : Γ(S, ⊤)ˣ) (hc : PrimitiveUnit (S := S) m c)
    (U : S.Opens) : ArithmeticThetaRelativeThetaRelationsR0256.PrimitiveUnit m
      (Units.map (res U).toMonoidHom c) := by
  refine ⟨by simp only [← map_pow, hc.1, map_one], ?_⟩
  intro i hi
  simpa using (hc.2 i hi).map (res U)

/-- Evaluation identifies the actual sheaf kernel with the linear kernel. -/
def kernelSections (A : End W) (U : S.Opens) :
    (sections U).obj (fixed A) ≅ ModuleCat.of Γ(S,U) (((sections U).map (A - 1)).hom.ker) :=
  PreservesKernel.iso (sections U) (A - 1) ≪≫ ModuleCat.kernelIsoKer _

lemma kernelSections_inv_ι (A : End W) (U : S.Opens) :
    (kernelSections A U).inv ≫ (sections U).map (fixedι A) =
      ModuleCat.ofHom (((sections U).map (A - 1)).hom.ker.subtype) := by
  simp [kernelSections, Category.assoc, PreservesKernel.iso_inv_ι]

lemma fixed_mem (A : End W) (U : S.Opens) (x : Γ(fixed A,U)) :
    act A U ((fixedι A).app U x) = (fixedι A).app U x := by
  have h := congrArg (fun f : fixed A ⟶ W => f.app U x) (kernel.condition (A - 1))
  change act A U ((fixedι A).app U x) - (fixedι A).app U x = 0 at h
  exact sub_eq_zero.mp h

def fixedSections (A : End W) (U : S.Opens) :
    Γ(fixed A,U) →ₗ[Γ(S,U)] Fixed Γ(S,U) Γ(W,U) (act A U) :=
  (((sections U).map (fixedι A)).hom).codRestrict _ (fun x => by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact fixed_mem A U x)

lemma fixedSections_bijective (A : End W) (U : S.Opens) :
    Function.Bijective (fixedSections A U) := by
  constructor
  · intro x y h
    have : Mono ((sections U).map (fixedι A)) := inferInstance
    apply (ModuleCat.mono_iff_injective ((sections U).map (fixedι A))).mp inferInstance
    exact congrArg Subtype.val h
  · intro x
    have hx : x.val ∈ (((sections U).map (A - 1)).hom.ker) := by
      change act A U x.val - x.val = 0
      exact sub_eq_zero.mpr (by simpa only [Module.End.mem_eigenspace_iff, one_smul] using x.property)
    refine ⟨(kernelSections A U).inv ⟨x.val,hx⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun f => f ⟨x.val,hx⟩) (kernelSections_inv_ι A U)

lemma sum_app {X Y : S.Modules} {I : Type*} (s : Finset I) (f : I → (X ⟶ Y))
    (U : S.Opens) (x : Γ(X,U)) :
    (∑ i ∈ s, f i).app U x = ∑ i ∈ s, (f i).app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, Scheme.Modules.Hom.add_app, ih]

lemma copies_total (X : S.Modules) (m : ℕ) (U : S.Opens) (x : Γ(copies X m,U)) :
    ∑ i : Fin m, (biproduct.ι (fun _ : Fin m => X) i).app U
      ((biproduct.π (fun _ : Fin m => X) i).app U x) = x := by
  have h := congrArg (fun f : End (copies X m) => f.app U x)
    (biproduct.total (f := fun _ : Fin m => X))
  simpa only [sum_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    AddCommGrpCat.comp_apply, AddCommGrpCat.id_apply] using h

lemma copies_π_ι (X : S.Modules) (m : ℕ) (U : S.Opens) (i j : Fin m) (x : Γ(X,U)) :
    (biproduct.π (fun _ : Fin m => X) i).app U
      ((biproduct.ι (fun _ : Fin m => X) j).app U x) = if j = i then x else 0 := by
  classical
  change ((biproduct.ι (fun _ : Fin m => X) j ≫
    biproduct.π (fun _ : Fin m => X) i).app U x) = _
  rw [biproduct.ι_π]
  split_ifs <;> rfl

def coordinates (A : End W) (m : ℕ) (U : S.Opens) :
    Γ(copies (fixed A) m,U) → (Fin m → Fixed Γ(S,U) Γ(W,U) (act A U)) :=
  fun x i => fixedSections A U ((biproduct.π (fun _ : Fin m => fixed A) i).app U x)

lemma coordinates_bijective (A : End W) (m : ℕ) (U : S.Opens) :
    Function.Bijective (coordinates A m U) := by
  classical
  constructor
  · intro x y h
    have hp : ∀ i : Fin m, (biproduct.π (fun _ : Fin m => fixed A) i).app U x =
        (biproduct.π (fun _ : Fin m => fixed A) i).app U y := by
      intro i
      exact (fixedSections_bijective A U).1 (congrFun h i)
    rw [← copies_total (fixed A) m U x, ← copies_total (fixed A) m U y]
    simp only [hp]
  · intro y
    choose z hz using fun i => (fixedSections_bijective A U).2 (y i)
    refine ⟨∑ i : Fin m, (biproduct.ι (fun _ : Fin m => fixed A) i).app U (z i), ?_⟩
    funext i
    simp [coordinates, map_sum, copies_π_ι, hz]

/-- The global orbit map is defined categorically, hence commutes with all restrictions. -/
def orbitMap (m : ℕ) (A B : End W) : copies (fixed A) m ⟶ W :=
  biproduct.desc (fun i : Fin m => fixedι A ≫ (B ^ i.val))

lemma orbitMap_app (m : ℕ) (A B : End W) (U : S.Opens)
    (x : Γ(copies (fixed A) m,U)) :
    (orbitMap m A B).app U x = orbitSum m (act A U) (act B U) (coordinates A m U x) := by
  simp only [orbitMap, biproduct.desc_eq, sum_app, Scheme.Modules.Hom.comp_app,
    AddCommGrpCat.comp_apply]
  change (∑ i : Fin m, act (B ^ i.val) U
    ((fixedι A).app U ((biproduct.π (fun _ : Fin m => fixed A) i).app U x))) = _
  simp only [act_pow]
  rfl

lemma orbitMap_bijective (m : ℕ) (hm : 0 < m) (A B : End W) (c : Γ(S,⊤)ˣ)
    (h : Relations m A B c) (hc : PrimitiveUnit (S := S) m c)
    (U : S.Opens) [Algebra ℚ Γ(S,U)] : Function.Bijective ((orbitMap m A B).app U) := by
  have hr := local_relations m A B c h U
  have ho := orbitSum_bijective m hm (act A U) (act B U) (Units.map (res U).toMonoidHom c)
    hr.1 hr.2.1 hr.2.2 (local_primitive m c hc U)
  have hb := ho.comp (coordinates_bijective A m U)
  have he : (fun x => (orbitMap m A B).app U x) =
      (fun x => orbitSum m (act A U) (act B U) (coordinates A m U x)) :=
    funext (orbitMap_app m A B U)
  change Function.Bijective (fun x => (orbitMap m A B).app U x)
  rw [he]
  exact hb

lemma orbit_eigen_sheaf (m : ℕ) (A B : End W) (c : Γ(S,⊤)ˣ)
    (h : Relations m A B c) (i : Fin m) :
    fixedι A ≫ (B ^ i.val) ≫ A = fixedι A ≫ (B ^ i.val) ≫ unitAction W (c ^ i.val) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  have he := orbit_eigen (act A U) (act B U) (Units.map (res U).toMonoidHom c)
    (local_relations m A B c h U).2.2 i.val (fixedSections A U x)
  change act A U (act (B ^ i.val) U ((fixedι A).app U x)) =
    (unitAction W (c ^ i.val)).app U (act (B ^ i.val) U ((fixedι A).app U x))
  simp only [act_pow, unitAction_apply, Units.val_pow_eq_pow_val, map_pow]
  exact he

lemma orbit_shift_sheaf (m : ℕ) (A B : End W) (hB : B ^ m = 1) (i : Fin m) :
    fixedι A ≫ (B ^ i.val) ≫ B = fixedι A ≫ (B ^ ((i.val + 1) % m)) := by
  change fixedι A ≫ (B * B ^ i.val) = _
  rw [← pow_succ', pow_eq_pow_mod (i.val + 1) hB]

end SchemeSchrodingerOrbit

/-- The canonical orbit decomposition of an arbitrary module sheaf, from its actual invariant kernel. -/
theorem scheme_schrodinger_orbit :
    ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u})
      (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)),
      ∀ (W : S.Modules) (m : ℕ), 0 < m → ∀ (A B : CategoryTheory.End W)
      (c : (S.presheaf.obj (Opposite.op ⊤))ˣ), Relations m A B c →
      ArithmeticThetaSchemeThetaMarkingR0259.PrimitiveUnit (S := S) m c → Orbit m A B c := by
  intro k _ _ S σ W m hm A B c h hc
  letI : HasFiniteBiproducts S.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let f := SchemeSchrodingerOrbit.orbitMap m A B
  have hf : IsIso f := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    let scalar : k →+* Γ(S,U) := (SchemeSchrodingerOrbit.res U).comp
      (σ.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
    letI : Algebra k Γ(S,U) := scalar.toAlgebra
    letI : Algebra ℚ Γ(S,U) := Algebra.compHom Γ(S,U) (algebraMap ℚ k)
    exact (ConcreteCategory.isIso_iff_bijective (f.app U)).mpr
      (SchemeSchrodingerOrbit.orbitMap_bijective m hm A B c h hc U)
  refine ⟨asIso f, ?_, ?_, ?_⟩
  · intro i
    exact biproduct.ι_desc (fun i : Fin m => fixedι A ≫ (B ^ i.val)) i
  · exact SchemeSchrodingerOrbit.orbit_eigen_sheaf m A B c h
  · exact SchemeSchrodingerOrbit.orbit_shift_sheaf m A B h.2.1

end ArithmeticThetaSchemeSchrodingerR0261

#print axioms ArithmeticThetaSchemeSchrodingerR0261.scheme_schrodinger_orbit
