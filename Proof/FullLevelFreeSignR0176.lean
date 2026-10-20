module

public import LegendreLevelAtlasDefinitionsR0176

@[expose] public section

/-! Simultaneous inversion of the actual full marking and its empty fixed scheme. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaLegendreAtlasR0176
namespace FullLevelFreeSignR0176
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaFullLevelCoverR0175
open WeierstrassProjModel ArithmeticThetaRelativeKatoNaturalityR0170

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} (G : Law R W)

lemma inverse_natural {T U : Scheme.{u}} (t : T ⟶ Base R) (s : U ⟶ Base R)
    (q : U ⟶ T) (hq : q ≫ t = s) (x : SchemeHomOver t (structureMap R W)) :
    schemeHomOverComp q hq (G.inv t x) = G.inv s (schemeHomOverComp q hq x) := by
  letI := G.pointGroup s
  apply eq_inv_of_mul_eq_one_left
  change G.mul s _ _ = G.one s
  rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]

lemma inverse_twice {T : Scheme.{u}} (t : T ⟶ Base R)
    (x : SchemeHomOver t (structureMap R W)) : G.inv t (G.inv t x) = x := by
  letI := G.pointGroup t
  exact inv_inv x

lemma inverse_power {H : Type*} [Group H] {L : ℕ} (_hL : 0 < L)
    (x : H) (hx : x ^ L = 1) (i : Fin L) :
    x⁻¹ ^ i.val = x ^ ((L - i.val) % L) := by
  have hp : x ^ (L - i.val) * x ^ i.val = 1 := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt i.isLt), hx]
  rw [inv_pow, ← eq_inv_of_mul_eq_one_left hp]
  exact (pow_eq_pow_of_modEq (by simp [Nat.ModEq]) hx).symm

/-- Both inverse sections form a full marking: complement the two residue indices. -/
def negative {T : Scheme.{u}} {t : T ⟶ Base R} {L : ℕ} (hL : 0 < L)
    (A : FullLevel R W G L t) : FullLevel R W G L t where
  x := G.inv t A.x
  y := G.inv t A.y
  killed_x := by
    letI := G.pointGroup t
    have hx : A.x ^ L = 1 := (RelativeKatoFiberSpecialization.nsmul_pow G t L A.x).symm.trans A.killed_x
    rw [RelativeKatoFiberSpecialization.nsmul_pow]
    change A.x⁻¹ ^ L = 1
    rw [inv_pow, hx, inv_one]
  killed_y := by
    letI := G.pointGroup t
    have hy : A.y ^ L = 1 := (RelativeKatoFiberSpecialization.nsmul_pow G t L A.y).symm.trans A.killed_y
    rw [RelativeKatoFiberSpecialization.nsmul_pow]
    change A.y⁻¹ ^ L = 1
    rw [inv_pow, hy, inv_one]
  avoids := by
    intro i j hij
    letI := G.pointGroup t
    have hx : A.x ^ L = 1 := (RelativeKatoFiberSpecialization.nsmul_pow G t L A.x).symm.trans A.killed_x
    have hy : A.y ^ L = 1 := (RelativeKatoFiberSpecialization.nsmul_pow G t L A.y).symm.trans A.killed_y
    have hn : (L-i.val) % L ≠ 0 ∨ (L-j.val) % L ≠ 0 := by
      have hh (k : Fin L) (hk : k.val ≠ 0) : (L-k.val) % L ≠ 0 := by
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      exact hij.imp (hh i) (hh j)
    have ha := A.avoids ⟨(L-i.val)%L, Nat.mod_lt _ hL⟩
      ⟨(L-j.val)%L, Nat.mod_lt _ hL⟩ hn
    simp only [RelativeKatoFiberSpecialization.nsmul_pow] at ha ⊢
    change Disjoint (Set.range (G.mul t (A.x⁻¹ ^ i.val) (A.y⁻¹ ^ j.val)).val) _
    rw [inverse_power hL A.x hx i, inverse_power hL A.y hy j]
    exact ha

lemma double_comp {T : Scheme.{u}} (t : T ⟶ Base R) (σ : T ⟶ T)
    (hσ : σ ≫ t = t) (x : SchemeHomOver t (structureMap R W))
    (hx : σ ≫ x.val = (G.inv t x).val) : σ ≫ σ ≫ x.val = x.val := by
  have he : schemeHomOverComp σ hσ x = G.inv t x := Subtype.ext hx
  rw [hx]
  exact (congrArg Subtype.val (inverse_natural G t t σ hσ x)).trans
    (by rw [he, inverse_twice])

/-- On a fixed test scheme the first marking is killed by two, so its
nonzero residue (2,0) meets the origin. Thus the entire test scheme is empty. -/
lemma fixed_empty (hG : IsOriginLaw R W G) {L : ℕ} (hL : 3 ≤ L)
    (Z : LevelScheme R W G L) (σ : Z.space ⟶ Z.space)
    (hx : σ ≫ Z.level.x.val = (G.inv Z.projection Z.level.x).val) :
    IsEmpty (equalizer σ (𝟙 Z.space) : Scheme.{u}) := by
  let E : Scheme.{u} := equalizer σ (𝟙 Z.space)
  let e : E ⟶ Z.space := equalizer.ι σ (𝟙 Z.space)
  let t := e ≫ Z.projection
  let A := BaseChange.restrict Z.level e (show e ≫ Z.projection = t from rfl)
  have he : e ≫ σ = e := by simpa only [Category.comp_id] using equalizer.condition σ (𝟙 Z.space)
  have ha : G.inv t A.x = A.x := by
    apply Subtype.ext
    have hn := congrArg Subtype.val (inverse_natural G Z.projection t e rfl Z.level.x)
    change e ≫ (G.inv Z.projection Z.level.x).val = (G.inv t A.x).val at hn
    rw [← hn, ← hx, ← Category.assoc, he]
    rfl
  have htwo : G.nsmul t 2 A.x = G.one t := by
    rw [G.nsmul_succ, G.nsmul_one_apply]
    calc G.mul t A.x A.x = G.mul t (G.inv t A.x) A.x := by rw [ha]
         _ = G.one t := G.inv_mul_cancel t A.x
  have hd := A.avoids ⟨2, by omega⟩ ⟨0, by omega⟩ (Or.inl (by change (2 : ℕ) ≠ 0; omega))
  simp only [G.nsmul_zero, G.mul_one, htwo] at hd
  refine ⟨fun z => ?_⟩
  apply Set.disjoint_left.mp hd (Set.mem_range_self z)
  rw [hG.1]
  exact ⟨t z, rfl⟩

end FullLevelFreeSignR0176
open CategoryTheory AlgebraicGeometry ArithmeticThetaRelativeKatoR0169
open ArithmeticThetaFullLevelCoverR0175 FullLevelFreeSignR0176

/-- The representing scheme carries the free simultaneous sign involution. -/
theorem full_level_free_sign :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic]
    (G : Law R W) (hG : IsOriginLaw R W G) (L : ℕ) (hL : 3 ≤ L)
    (Z : LevelScheme R W G L) (hZ : Represents R W G Z),
    Nonempty (SignAction R W G Z) := by
  intro R _ _ _ _ _ W _ G hG L hL Z hZ
  obtain ⟨σ, hσ, _⟩ := hZ Z.space Z.projection (negative G (by omega) Z.level)
  have hx : σ.val ≫ Z.level.x.val = (G.inv Z.projection Z.level.x).val := hσ.1
  have hy : σ.val ≫ Z.level.y.val = (G.inv Z.projection Z.level.y).val := hσ.2
  refine ⟨{ map := σ.val
            over_eq := σ.property
            x_eq := hx
            y_eq := hy
            square := ?_
            free := fixed_empty G hG hL Z σ.val hx }⟩
  apply BaseChange.represents_ext hZ _ _ (t := Z.projection)
  · rw [Category.assoc, σ.property, σ.property]
  · exact Category.id_comp _
  · simpa only [Category.assoc, Category.id_comp] using double_comp G Z.projection σ.val σ.property Z.level.x hx
  · simpa only [Category.assoc, Category.id_comp] using double_comp G Z.projection σ.val σ.property Z.level.y hy

#print axioms full_level_free_sign
end ArithmeticThetaLegendreAtlasR0176
