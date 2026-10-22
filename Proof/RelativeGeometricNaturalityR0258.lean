module

public import RelativeMidpointNaturalityR0258
public import RelativeSectionIntertwiningR0258
public import RelativeGeometricSchrodingerR0257

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
noncomputable section
universe u v w
namespace ArithmeticThetaRelativeThetaNaturalityR0258
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ArithmeticThetaLegendreAtlasR0176 ArithmeticThetaRelativeThetaLiftsR0255
open ArithmeticThetaRelativeThetaRelationsR0256 ArithmeticThetaRelativeSchrodingerR0257
open scoped TensorProduct
namespace GeometricNaturalityProof
open RelativePrimitiveThetaCommutator
open P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2

lemma conjugate_change {X : Scheme.{u}} {f g : X ⟶ X} (h : f = g)
    {L N : X.Modules} (e : L ≅ N) (α : (Scheme.Modules.pullback g).obj L ≅ L) :
    (Scheme.Modules.pullback f).mapIso e.symm ≪≫
        ((Scheme.Modules.pullbackCongr h).app L ≪≫ α) ≪≫ e =
      (Scheme.Modules.pullbackCongr h).app N ≪≫
        ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ α ≪≫ e) := by
  subst g
  rfl

lemma scalar_natural {X : Scheme.{u}} {L N : X.Modules} (e : L ≅ N)
    (a : Γ(X, ⊤)ˣ) : smulIso a L ≪≫ e = e ≪≫ smulIso a N := by
  apply Iso.ext
  ext U x
  exact Scheme.Modules.Hom.app_smul e.hom _ x

lemma conjugate_scaled {X : Scheme.{u}} (f : X ⟶ X)
    {L N : X.Modules} (e : L ≅ N) (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (a : Γ(X, ⊤)ˣ) :
    (Scheme.Modules.pullback f).mapIso e.symm ≪≫ (α ≪≫ smulIso a L) ≪≫ e =
      ((Scheme.Modules.pullback f).mapIso e.symm ≪≫ α ≪≫ e) ≪≫ smulIso a N := by
  simp only [Iso.trans_assoc, scalar_natural]

lemma conjugate_commutation {X : Scheme.{u}} (f g : X ⟶ X)
    (h : f ≫ g = g ≫ f) {L N : X.Modules} (e : L ≅ N)
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L) (a : Γ(X, ⊤)ˣ)
    (hab : PullbackLifts.compLift f g α β =
      (Scheme.Modules.pullbackCongr h).app L ≪≫
        PullbackLifts.compLift g f β α ≪≫ smulIso a L) :
    PullbackLifts.compLift f g
      ((Scheme.Modules.pullback f).mapIso e.symm ≪≫ α ≪≫ e)
      ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ β ≪≫ e) =
      (Scheme.Modules.pullbackCongr h).app N ≪≫
        PullbackLifts.compLift g f
          ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ β ≪≫ e)
          ((Scheme.Modules.pullback f).mapIso e.symm ≪≫ α ≪≫ e) ≪≫ smulIso a N := by
  rw [← MidpointNaturalityProof.conjugate_comp, hab]
  calc
    _ = ((Scheme.Modules.pullback (f ≫ g)).mapIso e.symm ≪≫
        ((Scheme.Modules.pullbackCongr h).app L ≪≫ PullbackLifts.compLift g f β α) ≪≫ e) ≪≫
        smulIso a N := by simp only [Iso.trans_assoc, scalar_natural]
    _ = _ := by rw [conjugate_change, MidpointNaturalityProof.conjugate_comp, Iso.trans_assoc]

lemma transport_commutation {X Y : Scheme.{u}} (c : Y ⟶ X)
    {L : X.Modules} {N : Y.Modules} (e : (Scheme.Modules.pullback c).obj L ≅ N)
    (f g : X ⟶ X) (f' g' : Y ⟶ Y)
    (hf : c ≫ f = f' ≫ c) (hg : c ≫ g = g' ≫ c)
    (h : f ≫ g = g ≫ f) (h' : f' ≫ g' = g' ≫ f')
    (α : (Scheme.Modules.pullback f).obj L ≅ L)
    (β : (Scheme.Modules.pullback g).obj L ≅ L)
    (α' : (Scheme.Modules.pullback f').obj N ≅ N)
    (β' : (Scheme.Modules.pullback g').obj N ≅ N)
    (hα : MidpointNaturalityProof.transport c e f f' hf α = α')
    (hβ : MidpointNaturalityProof.transport c e g g' hg β = β')
    (a : Γ(X, ⊤)ˣ) (b : Γ(Y, ⊤)ˣ)
    (hs : Units.map c.appTop.hom.toMonoidHom a = b)
    (hab : PullbackLifts.compLift f g α β =
      (Scheme.Modules.pullbackCongr h).app L ≪≫ PullbackLifts.compLift g f β α ≪≫ smulIso a L) :
    PullbackLifts.compLift f' g' α' β' =
      (Scheme.Modules.pullbackCongr h').app N ≪≫ PullbackLifts.compLift g' f' β' α' ≪≫ smulIso b N := by
  subst α'
  subst β'
  have hp := PullbackLifts.lift_commutation c f g f' g' hf hg h h' α β a hab
  rw [hs] at hp
  exact conjugate_commutation f' g' h' e _ _ b hp

variable {R : Type u} [CommRing R] (E : EllipticFamily R)
variable (S : Type u) [CommRing S] [Algebra R S]

lemma commutator_transport (m : ℕ) (P Q : point E)
    (α : Lift E m (translation E P)) (β : Lift E m (translation E Q))
    (αS : Lift (family E S) m (translation (family E S) (pointBaseChange E S P)))
    (βS : Lift (family E S) m (translation (family E S) (pointBaseChange E S Q)))
    (hα : LiftCorresponds E S m _ _ α αS) (hβ : LiftCorresponds E S m _ _ β βS)
    (c : Rˣ) (hc : Commutator E m P Q α β c) :
    Commutator (family E S) m (pointBaseChange E S P) (pointBaseChange E S Q)
      αS βS (Units.map (algebraMap R S).toMonoidHom c) := by
  obtain ⟨hf, hα⟩ := hα
  obtain ⟨hg, hβ⟩ := hβ
  obtain ⟨h, hh⟩ := hc
  let hS := translations_commute (family E S) (pointBaseChange E S P) (pointBaseChange E S Q)
  have hab : PullbackLifts.compLift (translation E P) (translation E Q) α β =
      (Scheme.Modules.pullbackCongr h).app (thetaLine E m) ≪≫
        PullbackLifts.compLift (translation E Q) (translation E P) β α ≪≫
          smulIso (scalar E c) (thetaLine E m) := by
    simpa only [compose, scaled, changeMap, PullbackLifts.compLift, Iso.trans_assoc] using hh
  refine ⟨hS, ?_⟩
  simpa only [compose, scaled, changeMap, PullbackLifts.compLift, Iso.trans_assoc] using
    (transport_commutation (curveMap E S) (thetaComparison E S m)
      _ _ _ _ hf hg h hS α β αS βS hα hβ (scalar E c) _
      (fibre_scalar E (algebraMap R S) c) hab)

#print axioms commutator_transport

lemma primitive_map (m : ℕ) (c : Rˣ) (hc : PrimitiveUnit m c) :
    PrimitiveUnit m (Units.map (algebraMap R S).toMonoidHom c) := by
  constructor
  · rw [← map_pow, hc.1, map_one]
  · intro i hi
    change IsUnit ((algebraMap R S) (c : R) ^ i.val - 1)
    rw [← map_pow, ← map_one (algebraMap R S), ← map_sub]
    exact (hc.2 i hi).map (algebraMap R S)

lemma point_killed (P : point E) (n : ℕ)
    (hP : P.val ≫ E.law.schemeNsmul n = zero E) :
    (pointBaseChange E S P).val ≫ (family E S).law.schemeNsmul n = zero (family E S) := by
  apply (RelativeDoubledTorsionThetaLiftR0255.killed_iff (family E S) _ _).mpr
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [MidpointNaturalityProof.nsmul_square]
    rw [(RelativeDoubledTorsionThetaLiftR0255.killed_iff E P n).mp hP]
    exact (baseChanged_zero E (baseMap (R := R) S)).symm
  · exact (Subtype.property ((family E S).law.nsmul (𝟙 _) n (pointBaseChange E S P))).trans
      (Subtype.property ((family E S).law.one (𝟙 _))).symm

section Linear
variable {K : Type u} [CommRing K] {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def fixedCongr (A : Module.End K V) (B : Module.End K W) (e : V ≃ₗ[K] W)
    (he : ∀ x, e (A x) = B (e x)) : Fixed K V A ≃ₗ[K] Fixed K W B where
  toFun x := ⟨e x.val, by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    rw [← he]
    congr 1
    simpa only [Module.End.mem_eigenspace_iff, one_smul] using x.property⟩
  invFun y := ⟨e.symm y.val, by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    apply e.injective
    rw [he, e.apply_symm_apply]
    simpa only [Module.End.mem_eigenspace_iff, one_smul] using y.property⟩
  left_inv x := by ext; exact e.symm_apply_apply x.val
  right_inv y := by ext; exact e.apply_symm_apply y.val
  map_add' x y := by ext; exact map_add e x.val y.val
  map_smul' a x := by ext; exact map_smul e a x.val

lemma intertwine_pow (A : Module.End K V) (B : Module.End K W) (e : V ≃ₗ[K] W)
    (he : ∀ x, e (A x) = B (e x)) (n : ℕ) (x : V) :
    e ((A ^ n) x) = (B ^ n) (e x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, he, ih]
end Linear

lemma tensor_fixed_orbit {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    {V : Type v} [AddCommGroup V] [Module R V] {W : Type w} [AddCommGroup W] [Module S W]
    (m : ℕ) (A B : Module.End R V) (AS BS : Module.End S W)
    (hfixed : FixedBaseChange R V A) (e : S ⊗[R] V ≃ₗ[S] W)
    (hA : ∀ x, e (A.baseChange S x) = AS (e x))
    (hB : ∀ x, e (B.baseChange S x) = BS (e x)) :
    ∃ eL : S ⊗[R] Fixed R V A ≃ₗ[S] Fixed S W AS,
      (∀ (s : S) (w : Fixed R V A), (eL (s ⊗ₜ[R] w)).val = e (s ⊗ₜ[R] w.val)) ∧
      (∀ (s : S) (w : Fin m → Fixed R V A),
        e (s ⊗ₜ[R] (∑ i : Fin m, (B ^ i.val) (w i).val)) =
          ∑ i : Fin m, (BS ^ i.val) (eL (s ⊗ₜ[R] w i)).val) := by
  obtain ⟨e₀, he₀⟩ := hfixed S
  let eL := e₀.trans (fixedCongr (A.baseChange S) AS e hA)
  have heL (s : S) (w : Fixed R V A) :
      (eL (s ⊗ₜ[R] w)).val = e (s ⊗ₜ[R] w.val) := by
    change e (e₀ (s ⊗ₜ[R] w)).val = _
    rw [he₀]
  refine ⟨eL, heL, ?_⟩
  intro s w
  simp only [TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [heL]
  have hp := intertwine_pow (B.baseChange S) BS e hB i.val (s ⊗ₜ[R] (w i).val)
  have hpow : (B ^ i.val).baseChange S = (B.baseChange S) ^ i.val :=
    map_pow (Module.End.baseChangeHom R S V) B i.val
  rw [← hpow] at hp
  exact hp

end GeometricNaturalityProof

/-- Geometric scalar-extension compatibility on actual theta sections and their fixed line. -/
theorem relative_geometric_naturality :
    ∀ (R : Type u) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
      (E : EllipticFamily R) (S : Type u) [CommRing S] [Algebra R S]
      [Algebra ℚ S] [IsScalarTower ℚ R S] [IsNoetherianRing S] (m : ℕ),
      0 < m → Even m → ∀ M : FamilyLevel R E (2*m), GeometricNaturality E S m M := by
  intro R _ _ _ E S _ _ _ _ _ m hm he M
  obtain ⟨ι, α, β, c, hι, hα, hsα, hβ, hsβ, hc, hp, hA, hB, hO, hF⟩ :=
    relative_geometric_schrodinger R E m hm he M
  obtain ⟨ιS, hιS, _⟩ := (relative_normalized_theta_inversion S (family E S) m).2
  obtain ⟨αS, hαS, hsαS, hAS⟩ := RelativeGeometricSchrodinger.normalized_order
    (family E S) m hm he (pointBaseChange E S M.x)
    (GeometricNaturalityProof.point_killed E S M.x (2*m) M.killed_x) ιS hιS
  obtain ⟨βS, hβS, hsβS, hBS⟩ := RelativeGeometricSchrodinger.normalized_order
    (family E S) m hm he (pointBaseChange E S M.y)
    (GeometricNaturalityProof.point_killed E S M.y (2*m) M.killed_y) ιS hιS
  have hci := relative_inversion_naturality R E S m ι ιS hι hιS
  have hca := relative_midpoint_naturality R E S m hm he M.x M.killed_x
    ι ιS α αS hι hιS hα hαS
  have hcb := relative_midpoint_naturality R E S m hm he M.y M.killed_y
    ι ιS β βS hι hιS hβ hβS
  have hcS := GeometricNaturalityProof.commutator_transport E S m M.x M.y α β αS βS hca hcb c hc
  refine ⟨ι, ιS, α, β, αS, βS, c, hι, hιS, hα, hsα, hβ, hsβ,
    hαS, hsαS, hβS, hsβS, hci, hca, hcb, hc, hp, hcS, ?_⟩
  letI := sectionModule E m
  letI := sectionModule (family E S) m
  refine ⟨hA, hB, hAS, hBS, hO, ?_, ?_⟩
  · exact (relative_schrodinger_module S (sections (family E S) m) m hm
      (relative_theta_sections_cohomology S (family E S) m hm).1 _ _ _ hAS hBS
      (RelativePrimitiveThetaCommutator.thetaAct_relation (family E S) m
        (pointBaseChange E S M.x) (pointBaseChange E S M.y) αS βS _ hcS)
      (GeometricNaturalityProof.primitive_map (R := R) S m c hp)).1
  · obtain ⟨e, he, hinter⟩ := relative_section_intertwining R E S m hm
    have heA := hinter M.x α αS hca
    have heB := hinter M.y β βS hcb
    obtain ⟨eL, heL, horbit⟩ := GeometricNaturalityProof.tensor_fixed_orbit m _ _ _ _ hF e heA heB
    exact ⟨e, eL, he, heA, heB, heL, horbit⟩

#print axioms relative_geometric_naturality
end ArithmeticThetaRelativeThetaNaturalityR0258
