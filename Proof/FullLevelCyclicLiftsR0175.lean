module

public import FullLevelCoverDefinitionsR0175

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaFullLevelCoverR0175
open CategoryTheory AlgebraicGeometry NeronModelInfra
open ArithmeticThetaRelativeKatoR0169 ArithmeticThetaRelativeDiscriminantR0171
open ArithmeticThetaRelativeCyclicQuotientR0173

namespace FullLevelCyclicLiftsR0175
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}
  (G : Law R W) (hG : IsOriginLaw R W G)

abbrev sections := SchemeHomOver (𝟙 (Base R)) (structureMap R W)

/-- The commutative group is precisely the given group law on actual sections. -/
abbrev sectionGroup : CommGroup (sections (R := R) (W := W)) :=
  { G.pointGroup (𝟙 (Base R)) with mul_comm := hG.2 (𝟙 (Base R)) }

lemma pow_mod {H : Type*} [Monoid H] {x : H} {L : ℕ}
    (hx : x ^ L = 1) (n : ℕ) : x ^ (n % L) = x ^ n := by
  exact pow_eq_pow_of_modEq (by simp [Nat.ModEq]) hx

def translate (t : sections (R := R) (W := W)) : Curve R W ⟶ Curve R W :=
  (G.mul (structureMap R W) ⟨𝟙 _, Category.id_comp _⟩
    ⟨structureMap R W ≫ t.val, by rw [Category.assoc, t.property, Category.comp_id]⟩).val

lemma translate_section (z t : sections (R := R) (W := W)) :
    z.val ≫ translate G t = (G.mul (𝟙 (Base R)) z t).val := by
  have h := G.mul_natural (structureMap R W) (𝟙 (Base R)) z.val z.property
    ⟨𝟙 _, Category.id_comp _⟩
    ⟨structureMap R W ≫ t.val, by rw [Category.assoc, t.property, Category.comp_id]⟩
  have h₁ : WeierstrassProjModel.schemeHomOverComp z.val z.property
      (⟨𝟙 _, Category.id_comp _⟩ : SchemeHomOver (structureMap R W) (structureMap R W)) = z :=
    Subtype.ext (Category.comp_id _)
  have h₂ : WeierstrassProjModel.schemeHomOverComp z.val z.property
      (⟨structureMap R W ≫ t.val, by rw [Category.assoc, t.property, Category.comp_id]⟩ :
        SchemeHomOver (structureMap R W) (structureMap R W)) = t := by
    apply Subtype.ext
    dsimp [WeierstrassProjModel.schemeHomOverComp]
    rw [← Category.assoc, z.property, Category.id_comp]
  exact (congrArg Subtype.val h).trans (by rw [h₁, h₂])

include hG in
lemma disjoint_of_product (s t d : sections (R := R) (W := W))
    (ht : G.mul (𝟙 (Base R)) t d = G.one (𝟙 (Base R)))
    (hs : Disjoint (Set.range (G.mul (𝟙 (Base R)) s d).val)
      (Set.range (origin R W))) :
    Disjoint (Set.range s.val) (Set.range t.val) := by
  apply Set.disjoint_iff_forall_ne.mpr
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  have he := congrArg (fun q => (translate G d) q) hab
  change (s.val ≫ translate G d) a = (t.val ≫ translate G d) b at he
  rw [translate_section, translate_section, ht, hG.1, Category.id_comp] at he
  exact (Set.disjoint_iff_forall_ne.mp hs) ⟨a, rfl⟩ ⟨b, rfl⟩ he

include hG in
/-- Distinct reduced coordinate pairs have disjoint images over the entire base. -/
lemma coordinate_disjoint {L : ℕ} (hL : 0 < L)
    (A : FullLevel R W G L (𝟙 (Base R)))
    (i j k l : ℕ) (hi : i < L) (hj : j < L) (hk : k < L) (hl : l < L)
    (hne : i ≠ k ∨ j ≠ l) :
    Disjoint
      (Set.range (G.mul (𝟙 (Base R)) (G.nsmul (𝟙 (Base R)) i A.x)
        (G.nsmul (𝟙 (Base R)) j A.y)).val)
      (Set.range (G.mul (𝟙 (Base R)) (G.nsmul (𝟙 (Base R)) k A.x)
        (G.nsmul (𝟙 (Base R)) l A.y)).val) := by
  letI := sectionGroup G hG
  have hx : A.x ^ L = 1 := by
    have h := A.killed_x
    rw [RelativeKatoFiberSpecialization.nsmul_pow] at h
    exact h
  have hy : A.y ^ L = 1 := by
    have h := A.killed_y
    rw [RelativeKatoFiberSpecialization.nsmul_pow] at h
    exact h
  let d := A.x ^ (L-k) * A.y ^ (L-l)
  have prod (a b : ℕ) : (A.x ^ a * A.y ^ b) * d =
      A.x ^ (a+(L-k)) * A.y ^ (b+(L-l)) := by
    simp only [pow_add]
    dsimp [d]
    ac_rfl
  apply disjoint_of_product G hG _ _ d
  · simp only [RelativeKatoFiberSpecialization.nsmul_pow]
    change (A.x ^ k * A.y ^ l) * d = 1
    rw [prod, Nat.add_sub_of_le (Nat.le_of_lt hk), Nat.add_sub_of_le (Nat.le_of_lt hl), hx, hy, one_mul]
  · have hn : (i+(L-k)) % L ≠ 0 ∨ (j+(L-l)) % L ≠ 0 := by
      have hi' : i + (L-k) < 2*L := by omega
      have hj' : j + (L-l) < 2*L := by omega
      have aux (a : ℕ) (ha : a < 2*L) : a % L = 0 → a = 0 ∨ a = L := by
        intro h
        have hd := Nat.mod_add_div a L
        have hq : a / L < 2 := (Nat.div_lt_iff_lt_mul hL).mpr (by omega)
        interval_cases h : a / L <;> simp_all
      have hh₁ := aux _ hi'
      have hh₂ := aux _ hj'
      omega
    have ha := A.avoids ⟨(i+(L-k)) % L, Nat.mod_lt _ hL⟩
      ⟨(j+(L-l)) % L, Nat.mod_lt _ hL⟩ hn
    simp only [RelativeKatoFiberSpecialization.nsmul_pow] at ha ⊢
    change Disjoint (Set.range ((A.x ^ i * A.y ^ j) * d).val) _
    rw [prod]
    rw [pow_mod hx, pow_mod hy] at ha
    exact ha

lemma nsmul_comp (z : sections (R := R) (W := W)) (a b : ℕ) :
    (G.nsmul (𝟙 (Base R)) a z).val ≫ G.schemeNsmul b =
      (G.nsmul (𝟙 (Base R)) (a*b) z).val := by
  rw [comp_schemeNsmul]
  apply congrArg Subtype.val
  letI := G.pointGroup (𝟙 (Base R))
  simp only [RelativeKatoFiberSpecialization.nsmul_pow, pow_mul]

end FullLevelCyclicLiftsR0175

open FullLevelCyclicLiftsR0175
open ArithmeticThetaRelativeKatoNaturalityR0170
open ArithmeticThetaHodgeFourTorsionR0147.MultiplicationDifferential

/-- The full marking supplies the actual cyclic kernel and all nonzero lifts. -/
theorem full_level_cyclic_lifts :

∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ) (hL : 0 < L) (m N : ℕ) (hm : 0 < m) (hN : 0 < N) (hdiv : m*N ∣ L) (A : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))) , ∃ P : ArithmeticThetaRelativeCyclicQuotientR0173.CyclicSection R W G m, P.point = ArithmeticThetaFullLevelCoverR0175.kernelPoint R W G m A ∧ ∀ a b : Fin N, a.val ≠ 0 ∨ b.val ≠ 0 → ArithmeticThetaRelativeCyclicQuotientR0173.LiftConditions R W G P N (ArithmeticThetaFullLevelCoverR0175.liftPoint R W G m N a.val b.val A) := by
  intro R _ _ _ _ _ W _ G hG L hL m N hm hN hdiv A
  letI := sectionGroup G hG
  have hx : A.x ^ L = 1 := by
    have h := A.killed_x
    rw [RelativeKatoFiberSpecialization.nsmul_pow] at h
    exact h
  have hy : A.y ^ L = 1 := by
    have h := A.killed_y
    rw [RelativeKatoFiberSpecialization.nsmul_pow] at h
    exact h
  have hmL : m ∣ L := dvd_trans (dvd_mul_right m N) hdiv
  have hNL : N ∣ L := dvd_trans (dvd_mul_left N m) hdiv
  have hc : L / m * m = L := Nat.div_mul_cancel hmL
  have hd : L / N * N = L := Nat.div_mul_cancel hNL
  have hq : L / (m*N) * (m*N) = L := Nat.div_mul_cancel hdiv
  have hcpos : 0 < L / m := Nat.div_pos (Nat.le_of_dvd hL hmL) hm
  have hdpos : 0 < L / N := Nat.div_pos (Nat.le_of_dvd hL hNL) hN
  have hqpos : 0 < L / (m*N) := Nat.div_pos (Nat.le_of_dvd hL hdiv) (Nat.mul_pos hm hN)
  have hqc : L / (m*N) * N = L / m := by nlinarith [hc, hq]
  have hc_lt (i : Fin m) : L / m * i.val < L := by
    have := Nat.mul_lt_mul_of_pos_left i.isLt hcpos
    omega
  let P : CyclicSection R W G m :=
    { point := kernelPoint R W G m A
      over_eq := (G.nsmul (𝟙 (Base R)) (L/m) A.x).property
      killed := by
        change (G.nsmul (𝟙 (Base R)) (L/m) A.x).val ≫ G.schemeNsmul m = _
        rw [nsmul_comp, hc, A.killed_x, hG.1, Category.id_comp]
      disjoint := by
        intro i j hij
        change Disjoint (Set.range ((G.nsmul (𝟙 (Base R)) (L/m) A.x).val ≫ G.schemeNsmul i.val))
          (Set.range ((G.nsmul (𝟙 (Base R)) (L/m) A.x).val ≫ G.schemeNsmul j.val))
        rw [nsmul_comp, nsmul_comp]
        have hne : L/m * i.val ≠ L/m * j.val := by
          intro h
          apply hij
          apply Fin.ext
          exact Nat.eq_of_mul_eq_mul_left hcpos h
        simpa only [G.nsmul_zero, G.mul_one] using
          coordinate_disjoint G hG hL A (L/m*i.val) 0 (L/m*j.val) 0
            (hc_lt i) hL (hc_lt j) hL (Or.inl hne) }
  refine ⟨P, rfl, ?_⟩
  intro a b hab
  have hax : L/N * a.val < L := by
    have := Nat.mul_lt_mul_of_pos_left a.isLt hdpos
    omega
  have hbx : L/(m*N) * b.val < L := by
    have hh := Nat.mul_lt_mul_of_pos_left b.isLt hqpos
    have hh' : L/m ≤ L := Nat.div_le_self L m
    omega
  refine ⟨(G.mul (𝟙 (Base R))
    (G.nsmul (𝟙 (Base R)) (L/(m*N)*b.val) A.x)
    (G.nsmul (𝟙 (Base R)) (L/N*a.val) A.y)).property, ?_, ?_⟩
  · refine ⟨⟨b.val % m, Nat.mod_lt _ hm⟩, ?_⟩
    change (G.mul (𝟙 (Base R))
      (G.nsmul (𝟙 (Base R)) (L/(m*N)*b.val) A.x)
      (G.nsmul (𝟙 (Base R)) (L/N*a.val) A.y)).val ≫ G.schemeNsmul N =
        (G.nsmul (𝟙 (Base R)) (L/m) A.x).val ≫ G.schemeNsmul (b.val % m)
    rw [comp_schemeNsmul, nsmul_comp]
    apply congrArg Subtype.val
    simp only [RelativeKatoFiberSpecialization.nsmul_pow]
    change (A.x ^ (L/(m*N)*b.val) * A.y ^ (L/N*a.val)) ^ N = A.x ^ (L/m*(b.val%m))
    rw [mul_pow, ← pow_mul, ← pow_mul]
    have e₁ : L/(m*N)*b.val*N = L/m*b.val := by nlinarith [hqc]
    have e₂ : L/N*a.val*N = L*a.val := by nlinarith [hd]
    rw [e₁, e₂, pow_mul A.y, hy, one_pow, mul_one]
    have hp : (A.x ^ (L/m)) ^ m = 1 := by rw [← pow_mul, hc, hx]
    simpa only [← pow_mul] using (pow_mod hp b.val).symm
  · intro i
    change Disjoint (Set.range (G.mul (𝟙 (Base R))
      (G.nsmul (𝟙 (Base R)) (L/(m*N)*b.val) A.x)
      (G.nsmul (𝟙 (Base R)) (L/N*a.val) A.y)).val)
      (Set.range ((G.nsmul (𝟙 (Base R)) (L/m) A.x).val ≫ G.schemeNsmul i.val))
    rw [nsmul_comp]
    have hne : L/(m*N)*b.val ≠ L/m*i.val ∨ L/N*a.val ≠ 0 := by
      by_contra h
      push Not at h
      have ha : a.val = 0 := (Nat.mul_eq_zero.mp h.2).resolve_left (Nat.ne_of_gt hdpos)
      have hb : b.val ≠ 0 := hab.resolve_left (not_not_intro ha)
      have hb' : b.val = N*i.val := by
        apply Nat.eq_of_mul_eq_mul_left hqpos
        nlinarith [h.1, hqc]
      have hi : 0 < i.val := by
        apply Nat.pos_of_ne_zero
        intro hi
        apply hb
        simpa [hi] using hb'
      have := b.isLt
      nlinarith
    simpa only [G.nsmul_zero, G.mul_one] using
      coordinate_disjoint G hG hL A (L/(m*N)*b.val) (L/N*a.val) (L/m*i.val) 0
        hbx hax (hc_lt i) hL hne

end ArithmeticThetaFullLevelCoverR0175
