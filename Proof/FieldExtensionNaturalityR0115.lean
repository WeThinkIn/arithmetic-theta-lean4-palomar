module

public import BasisCoordinateGeometryR0115

@[expose] public section

/-! Field-extension naturality on the actual nonsingular point groups. -/
noncomputable section
universe u v
namespace ArithmeticThetaMarkingR0115
open WeierstrassCurve.Affine ArithmeticThetaFourTorsion

variable {k : Type u} [Field k] [DecidableEq k]
  {K : Type v} [Field K] [DecidableEq K]

omit [DecidableEq k] [DecidableEq K] in
lemma curve_map (e : Fin 3 → k) (f : k →+* K) :
    (Curve k e).map f = Curve K (f ∘ e) := by
  ext <;> simp [Curve, ArithmeticThetaMillerR0114.Curve, splitCurve,
    WeierstrassCurve.map]

omit [DecidableEq k] [DecidableEq K] in
lemma mapped_nonsingular (e : Fin 3 → k) (f : k →+* K)
    {x y : k} (h : (Curve k e).Nonsingular x y) :
    (Curve K (f ∘ e)).Nonsingular (f x) (f y) := by
  rw [← curve_map]
  exact ((Curve k e).map_nonsingular f.injective x y).mpr h

/-- The coordinate map, defined on every nonsingular point, including infinity. -/
def fieldMap (e : Fin 3 → k) (f : k →+* K) :
    (Curve k e).Point →+ (Curve K (f ∘ e)).Point where
  toFun P := match P with
    | .zero => .zero
    | .some x y h => .some (f x) (f y) (mapped_nonsingular e f h)
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    have hn : ∀ x y, (Curve K (f ∘ e)).negY (f x) (f y) =
        f ((Curve k e).negY x y) := by
      intro x y; rw [← curve_map]; exact (Curve k e).map_negY f x y
    have hx : ∀ x₁ x₂ ℓ, (Curve K (f ∘ e)).addX (f x₁) (f x₂) (f ℓ) =
        f ((Curve k e).addX x₁ x₂ ℓ) := by
      intro x₁ x₂ ℓ; rw [← curve_map]; exact (Curve k e).map_addX f x₁ x₂ ℓ
    have hy : ∀ x₁ x₂ y₁ ℓ, (Curve K (f ∘ e)).addY (f x₁) (f x₂) (f y₁) (f ℓ) =
        f ((Curve k e).addY x₁ x₂ y₁ ℓ) := by
      intro x₁ x₂ y₁ ℓ; rw [← curve_map]; exact (Curve k e).map_addY f x₁ y₁ x₂ ℓ
    have hs : ∀ x₁ x₂ y₁ y₂, (Curve K (f ∘ e)).slope (f x₁) (f x₂) (f y₁) (f y₂) =
        f ((Curve k e).slope x₁ x₂ y₁ y₂) := by
      intro x₁ x₂ y₁ y₂; rw [← curve_map]; exact (Curve k e).map_slope f x₁ x₂ y₁ y₂
    by_cases hxy : x₁ = x₂ ∧ y₁ = (Curve k e).negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2,
        Point.add_of_Y_eq (congrArg f hxy.1) (by rw [hn, hxy.2])]
      rfl
    · simpa only [Point.add_some hxy, ← hx, ← hy, ← hs] using!
        (Point.add_some (h₁ := mapped_nonsingular e f h₁)
          (h₂ := mapped_nonsingular e f h₂)
          (fun h => hxy ⟨f.injective h.1, f.injective ((hn x₂ y₂) ▸ h.2)⟩)).symm

@[simp] lemma fieldMap_some (e : Fin 3 → k) (f : k →+* K)
    {x y : k} (h : (Curve k e).Nonsingular x y) :
    fieldMap e f (Point.some x y h) = Point.some (f x) (f y) (mapped_nonsingular e f h) := rfl

lemma fieldMap_injective (e : Fin 3 → k) (f : k →+* K) :
    Function.Injective (fieldMap e f) := by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · rw [Point.some.injEq]
    exact ⟨f.injective (Point.some.inj h).1,
      f.injective (Point.some.inj h).2⟩

@[simp] lemma pointX_fieldMap (e : Fin 3 → k) (f : k →+* K) (P : (Curve k e).Point) :
    pointX K (f ∘ e) (fieldMap e f P) = f (pointX k e P) := by
  cases P <;> simp [fieldMap, pointX]

@[simp] lemma pointY_fieldMap (e : Fin 3 → k) (f : k →+* K) (P : (Curve k e).Point) :
    pointY K (f ∘ e) (fieldMap e f P) = f (pointY k e P) := by
  cases P <;> simp [fieldMap, pointY]

lemma fieldMap_coordinates (e : Fin 3 → k) (f : k →+* K) (b : Marking k e)
    (z : Fin 2 → ZMod 4) :
    coordinates K (f ∘ e) (fieldMap e f ∘ b) z = fieldMap e f (coordinates k e b z) := by
  simp [coordinates]

lemma fieldMap_labels (e : Fin 3 → k) (f : k →+* K) (b : Marking k e) :
    labels K (f ∘ e) (fieldMap e f ∘ b) = f ∘ labels k e b := by
  funext i
  fin_cases i <;> simp [labels, ← map_nsmul, ← map_add]

lemma fieldMap_root (e : Fin 3 → k) (f : k →+* K) (b : Marking k e) :
    root K (f ∘ e) (fieldMap e f ∘ b) = f (root k e b) := by
  simp [root, fieldMap_labels, rootExpression, map_ofNat]

lemma fieldMap_tangent (e : Fin 3 → k) (f : k →+* K) (P Q : (Curve k e).Point) :
    tangent K (f ∘ e) (fieldMap e f P) (fieldMap e f Q) = f (tangent k e P Q) := by
  simp only [tangent, ArithmeticThetaMillerR0114.tangentValue,
    ArithmeticThetaMillerR0114.tangentSlope, pointX_fieldMap, pointY_fieldMap]
  have hs := (Curve k e).map_slope f (pointX k e P) (pointX k e P)
    (pointY k e P) (pointY k e P)
  rw [curve_map] at hs
  change (ArithmeticThetaMillerR0114.Curve K (f ∘ e)).slope _ _ _ _ = _ at hs
  rw [hs]
  simp

lemma fieldMap_phase (e : Fin 3 → k) (f : k →+* K) (b : Marking k e) :
    phase K (f ∘ e) (fieldMap e f ∘ b) = f (phase k e b) := by
  simp [phase, fieldMap_labels, fieldMap_tangent]

private lemma halves_span_equal_curve [CharZero K]
    (W : WeierstrassCurve.Affine K) (d : Fin 3 → K)
    (hW : W = Curve K d) (hd : Function.Injective d)
    (P Q : W.Point)
    (hP : ∃ h : W.Nonsingular (d 0) 0, 2 • P = Point.some (d 0) 0 h)
    (hQ : ∃ h : W.Nonsingular (d 1) 0, 2 • Q = Point.some (d 1) 0 h)
    (T : W.Point) (hT : 4 • T = 0) :
    ∃ z : Fin 2 → ZMod 4, (z 0).val • P + (z 1).val • Q = T := by
  subst W
  exact ((ArithmeticThetaMillerR0114.independent_halves_four_basis
    K d hd P Q hP hQ T).mp hT).exists

/-- Even over the larger field, the transported marking spans every point killed by four. -/
lemma fieldMap_basis [CharZero k] [CharZero K]
    (e : Fin 3 → k) (he : Function.Injective e) (f : k →+* K)
    (b : Marking k e) (hb : IsBasis k e b) :
    IsBasis K (f ∘ e) (fieldMap e f ∘ b) := by
  obtain ⟨_, ⟨σ, hlabels⟩, hcurve, hhalf, _, _⟩ := basis_coordinate_geometry k e he b hb
  have hlabelsInj : Function.Injective (labels k e b) := by
    rw [hlabels]
    exact he.comp σ.injective
  have hcurveK : Curve K (f ∘ e) = Curve K (f ∘ labels k e b) := by
    rw [← curve_map e f, ← curve_map (labels k e b) f, hcurve]
  have hhalfK : ∀ i : Fin 2,
      ∃ h : (Curve K (f ∘ e)).Nonsingular (f (labels k e b i.castSucc)) 0,
        2 • fieldMap e f (b i) = Point.some (f (labels k e b i.castSucc)) 0 h := by
    intro i
    obtain ⟨h, hh⟩ := hhalf i
    have hm := congrArg (fieldMap e f) hh
    simp only [map_nsmul, fieldMap_some] at hm
    have h0 := mapped_nonsingular e f h
    rw [map_zero] at h0
    refine ⟨h0, ?_⟩
    simpa only [map_zero] using hm
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change 4 • fieldMap e f (b i) = 0
    rw [← map_nsmul, hb.1 i, map_zero]
  · intro z w hzw
    apply hb.2.1
    apply fieldMap_injective e f
    simpa only [← fieldMap_coordinates] using hzw
  · intro T hT
    exact halves_span_equal_curve (Curve K (f ∘ e)) (f ∘ labels k e b)
      hcurveK (f.injective.comp hlabelsInj) (fieldMap e f (b 0)) (fieldMap e f (b 1))
      (hhalfK 0) (hhalfK 1) T hT

lemma fieldMap_isCoordinateMap (e : Fin 3 → k) (f : k →+* K) :
    IsCoordinateMap k K e f (fieldMap e f) := by
  intro P hP
  refine ⟨?_, pointX_fieldMap e f P, pointY_fieldMap e f P⟩
  intro h
  apply hP
  apply fieldMap_injective e f
  simpa using h

lemma coordinateMap_unique (e : Fin 3 → k) (f : k →+* K)
    (G : (Curve k e).Point →+ (Curve K (f ∘ e)).Point)
    (hG : IsCoordinateMap k K e f G) : G = fieldMap e f := by
  ext P
  cases P with
  | zero => exact G.map_zero
  | some x y h =>
    obtain ⟨hn, hx, hy⟩ := hG (Point.some x y h) (Point.some_ne_zero h)
    cases hGP : G (Point.some x y h) with
    | zero => exact False.elim (hn hGP)
    | some a b hab =>
      rw [fieldMap_some, Point.some.injEq]
      simpa only [hGP, pointX, pointY] using And.intro hx hy

/-- Unique coordinate-preserving extension, including full four-torsion and literal formulas. -/
theorem field_extension_naturality :
    ∀ (k : Type u) [Field k] [CharZero k] [DecidableEq k] (e : Fin 3 → k),
      Function.Injective e →
      ∀ (K : Type v) [Field K] [CharZero K] [DecidableEq K] (f : k →+* K),
      ∃! F : (Curve k e).Point →+ (Curve K (f ∘ e)).Point,
        IsCoordinateMap k K e f F ∧ Function.Injective F ∧
        (∀ b : Marking k e, IsBasis k e b →
          IsBasis K (f ∘ e) (F ∘ b) ∧
          root K (f ∘ e) (F ∘ b) = f (root k e b) ∧
          phase K (f ∘ e) (F ∘ b) = f (phase k e b)) := by
  intro k _ _ _ e he K _ _ _ f
  refine ⟨fieldMap e f, ⟨fieldMap_isCoordinateMap e f, fieldMap_injective e f, ?_⟩, ?_⟩
  · intro b hb
    exact ⟨fieldMap_basis e he f b hb, fieldMap_root e f b, fieldMap_phase e f b⟩
  · intro G hG
    exact coordinateMap_unique e f G hG.1

end ArithmeticThetaMarkingR0115
