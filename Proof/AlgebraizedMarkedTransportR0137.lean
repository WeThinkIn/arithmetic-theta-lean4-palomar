module

public import AlgebraizedAnnularActionsR0137
public import TowerInversionR0137
public import TowerScalarTranslationR0137
public import TowerPeriodRotationR0137

@[expose] public section

/-! Transport of the actual marked sections under the three model actions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace ArithmeticThetaModelSymmetriesR0137
namespace AlgebraizedMarkedTransportR0137
open CategoryTheory AlgebraicGeometry
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaPolygonCohomologyR0131
open ArithmeticThetaProjectiveEffectivityR0135
open ArithmeticThetaAlgebraizedMarkedLineR0136
variable (k : Type u) [Field k] [CharZero k]

@[simp] lemma point_base (n : ℕ) (b : kˣ) :
    (markedPoint k n b).comp (base k n) = RingHom.id _ := mkPoint_base ..
@[simp] lemma point_base_apply (n : ℕ) (b : kˣ) (z : R k n) :
    markedPoint k n b (base k n z) = z := RingHom.congr_fun (point_base k n b) z
@[simp] lemma point_x (n : ℕ) (b : kˣ) :
    markedPoint k n b (coordX k n) = markedUnit k n b := mkPoint_x ..
@[simp] lemma point_y (n : ℕ) (b : kˣ) :
    markedPoint k n b (coordY k n) = parameter k n * ↑((markedUnit k n b)⁻¹) :=
  mkPoint_y ..

lemma point_scalar (n : ℕ) (a b : kˣ) :
    (markedPoint k n b).comp (TowerScalarTranslation.ringMap k n a) =
      markedPoint k n (a*b) := by
  apply point_ext
  · ext z; simp
  · simp [RingHom.comp_apply, scalar, markedUnit]
  · simp [RingHom.comp_apply, scalar, markedUnit, mul_comm, mul_left_comm]

variable {k} {r n : ℕ} {hr : 0 < r} {E : B k n false ≃+* B k n true}
lemma stage_rotation (D : Atlas k r n hr E) (g : D.X ≅ D.X)
    (hg : StageAction k D (next r hr) 1 false g) (i : Fin r) (b : kˣ) :
    markedSection k r n hr D i b ≫ g.hom =
      markedSection k r n hr D (next r hr i) b := by
  obtain ⟨_, f, hf, hc⟩ := hg
  rw [TowerPeriodRotationR0137.coordinate_unique k n f hf] at hc
  simp only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at hc
  simp only [markedSection, Category.assoc, hc]

lemma stage_scalar (D : Atlas k r n hr E) (g : D.X ≅ D.X) (a : kˣ)
    (hg : StageAction k D id a false g) (i : Fin r) (b : kˣ) :
    markedSection k r n hr D i b ≫ g.hom = markedSection k r n hr D i (a*b) := by
  obtain ⟨_, f, hf, hc⟩ := hg
  rw [TowerScalarTranslation.coordinates_unique k n a f hf] at hc
  rw [markedSection, Category.assoc, hc, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((markedPoint k n b).comp
    (TowerScalarTranslation.ringMap k n a))) ≫ _ = _
  rw [point_scalar]; rfl

/-- Evaluate the adjacent overlap at the reciprocal unit. This identity holds
in every nonreduced quotient, without reducing the parameter to zero. -/
lemma inversion_overlap (hE : IsAdjacent k n E) (b : kˣ) :
    ∃ q : B k n true →+* R k n,
      q.comp (restriction k n true) = markedPoint k n b⁻¹ ∧
      q.comp (E.toRingHom.comp (restriction k n false)) =
        (markedPoint k n b).comp (TowerInversionR0137.swap k n) := by
  have hu : IsUnit (markedPoint k n b⁻¹ (if true then coordX k n else coordY k n)) := by
    simp only [↓reduceIte, point_x]; exact Units.isUnit _
  let q := openPoint (markedPoint k n b⁻¹) true hu
  have hq : q.comp (restriction k n true) = markedPoint k n b⁻¹ := openPoint_restriction ..
  have hqb (z : R k n) : q (E (restriction k n false (base k n z))) = z := by
    rw [show E (restriction k n false (base k n z)) =
      restriction k n true (base k n z) from RingHom.congr_fun (adjacent_base hE) z]
    exact (RingHom.congr_fun hq (base k n z)).trans (point_base_apply k n b⁻¹ z)
  have hqy : q (E (restriction k n false (coordY k n))) = markedUnit k n b := by
    have hh := congrArg q (adjacent_y_mul_x hE)
    have hx : q (restriction k n true (coordX k n)) = markedUnit k n b⁻¹ :=
      (RingHom.congr_fun hq (coordX k n)).trans (point_x k n b⁻¹)
    rw [map_mul, map_one, hx] at hh
    have hm : markedUnit k n b⁻¹ = (markedUnit k n b)⁻¹ := by simp [markedUnit]
    rw [hm] at hh
    calc
      _ = (q (E (restriction k n false (coordY k n))) * ↑((markedUnit k n b)⁻¹)) *
          ↑(markedUnit k n b) := by simp [mul_assoc]
      _ = _ := by rw [hh, one_mul]
  have hqx : q (E (restriction k n false (coordX k n))) =
      parameter k n * ↑((markedUnit k n b)⁻¹) := by
    have hh := congrArg (fun z => q (E (restriction k n false z))) (coordX_mul_coordY k n)
    simp only [map_mul, hqy, hqb] at hh
    calc
      _ = (q (E (restriction k n false (coordX k n))) * ↑(markedUnit k n b)) *
          ↑((markedUnit k n b)⁻¹) := by simp [mul_assoc]
      _ = _ := by rw [hh]
  refine ⟨q, hq, ?_⟩
  apply point_ext
  · ext z; simpa using hqb z
  · simpa using hqx
  · simpa using hqy

lemma next_rev (i : Fin r) : next r hr (Fin.rev i) = negIndex r hr i := by
  apply Fin.ext
  simp only [next, Fin.rev, negIndex, Fin.val_mk]
  congr 1
  have hi := i.isLt
  omega

lemma stage_inversion (D : Atlas k r n hr E) (hE : IsAdjacent k n E)
    (g : D.X ≅ D.X) (hg : StageAction k D Fin.rev 1 true g) (i : Fin r) (b : kˣ) :
    markedSection k r n hr D i b ≫ g.hom =
      markedSection k r n hr D (negIndex r hr i) b⁻¹ := by
  obtain ⟨_, f, hf, hc⟩ := hg
  rw [TowerInversionR0137.swap_unique k n f hf] at hc
  obtain ⟨q, hqr, hql⟩ := inversion_overlap hE b
  have hl : Spec.map (CommRingCat.ofHom q) ≫ leftLeg k n E =
      Spec.map (CommRingCat.ofHom (markedPoint k n b)) ≫
        Spec.map (CommRingCat.ofHom (TowerInversionR0137.swap k n)) := by
    simp only [leftLeg, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hql
  have hr' : Spec.map (CommRingCat.ofHom q) ≫ rightLeg k n =
      Spec.map (CommRingCat.ofHom (markedPoint k n b⁻¹)) := by
    simp only [rightLeg, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hqr
  rw [markedSection, Category.assoc, hc, ← Category.assoc, ← hl,
    Category.assoc, (D.adjacent (Fin.rev i)).w, ← Category.assoc, hr', next_rev]
  rfl

lemma lift_transport {T : Tower k r hr} (M : Model k T)
    (g : ∀ n, (T.atlas n).X ≅ (T.atlas n).X) (f : M.X ≅ M.X)
    (hf : Algebraizes k M g f) (i j : Fin r) (b c : kˣ)
    (hstage : ∀ n, markedSection k r n hr (T.atlas n) i b ≫ (g n).hom =
      markedSection k r n hr (T.atlas n) j c)
    (s : baseScheme k ⟶ M.X) (hs : MarkedLift k M i b s) :
    MarkedLift k M j c (s ≫ f.hom) := by
  constructor
  · rw [Category.assoc, hf.1]; exact hs.1
  · intro n
    rw [← Category.assoc, hs.2, Category.assoc, hf.2, ← Category.assoc, hstage]

end AlgebraizedMarkedTransportR0137
open CategoryTheory
open ArithmeticThetaInfinitesimalPolygonR0129
open ArithmeticThetaProjectiveEffectivityR0135
open AlgebraizedMarkedTransportR0137

/-- Every actual marked lift has the prescribed images under all three actions. -/
theorem algebraized_marked_transport :
    ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r), 3 ≤ r →
    ∀ (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr),
    ∀ (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T),
    ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M →
    ∀ (rot : M.X ≅ M.X) (scal : kˣ → (M.X ≅ M.X)) (inv : M.X ≅ M.X),
    ArithmeticThetaModelSymmetriesR0137.Actions k M rot scal inv →
    ArithmeticThetaModelSymmetriesR0137.MarkedTransport k M rot scal inv := by
  intro k _ _ r hr _ T M _ rot scal inv h i b s hs
  obtain ⟨grot, hgrot, hrot⟩ := h.1
  obtain ⟨ginv, hginv, hinv⟩ := h.2.2
  refine ⟨lift_transport M grot rot hrot i (next r hr i) b b
    (fun n => stage_rotation (T.atlas n) (grot n) (hgrot.2 n) i b) s hs, ?_,
    lift_transport M ginv inv hinv i (negIndex r hr i) b b⁻¹
      (fun n => stage_inversion (T.atlas n) (T.overlap_spec n) (ginv n)
        (hginv.2 n) i b) s hs⟩
  intro a
  obtain ⟨g, hg, hf⟩ := h.2.1 a
  exact lift_transport M g (scal a) hf i i b (a*b)
    (fun n => stage_scalar (T.atlas n) (g n) a (hg.2 n) i b) s hs

end ArithmeticThetaModelSymmetriesR0137
#print axioms ArithmeticThetaModelSymmetriesR0137.algebraized_marked_transport
