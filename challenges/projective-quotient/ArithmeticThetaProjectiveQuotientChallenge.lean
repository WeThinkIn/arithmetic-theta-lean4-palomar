module
public import Mathlib
import all Lean.Meta.Match.Match
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.privateInPublic true
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open _root_ renaming CommRing → z0, Field → z1, Nonempty → z29, CommRingCat → z9, SheafOfModules → z8
namespace AlgebraicGeometry
structure Scheme.Modules.IsInvertible {X: Scheme.{u}} (M: X.Modules): Prop where (exists_trivialization: ∀ x: X, ∃ (U: X.Opens), x ∈ U ∧ z29 ((Scheme.Modules.pullback U.ι).obj M ≅ z8.unit U.toScheme.ringCatSheaf))
end AlgebraicGeometry
namespace ArithmeticThetaLocalWeierstrassR0203
abbrev Base (R: Type u) [z0 R]:= Spec (z9.of R)
end ArithmeticThetaLocalWeierstrassR0203
namespace P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2
variable {X Y : Scheme.{u}}
noncomputable abbrev resTop (s: Γ(X, ⊤)) (U: X.Opens): Γ(X, U):= X.presheaf.map (homOfLE le_top: U ⟶ ⊤).op s
lemma smul_res_comm (s: Γ(X, ⊤)) (M: X.Modules) (U: X.Opens) (r: Γ(X, U)) (m: Γ(M, U)): resTop s U • r • m = r • resTop s U • m:= by sorry
lemma map_resTop_smul (s: Γ(X, ⊤)) (M: X.Modules) {U V: X.Opens} (i: U ⟶ V) (x: Γ(M, V)): M.presheaf.map i.op (resTop s V • x) = resTop s U • M.presheaf.map i.op x:= by sorry
noncomputable def smulHom (s : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom Γ(M, U.unop) (resTop s U.unop))
      naturality := fun {U V} i => by
        ext x
        exact (map_resTop_smul s M i.unop (x : Γ(M, U.unop))).symm }
    (fun U r m => smul_res_comm s M U.unop r m)⟩
end P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2
namespace ArithmeticThetaInvariantRatiosR0265
open ArithmeticThetaLocalWeierstrassR0203
def scalarEnd {F: Type u} [z1 F] (M: (Base F).Modules) (a: F): End M:= P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.smulHom ((Scheme.ΓSpecIso (z9.of F)).inv.hom a) M
end ArithmeticThetaInvariantRatiosR0265
namespace ArithmeticThetaGlobalProjectiveRatiosR0266
open ArithmeticThetaInvariantRatiosR0265
structure GenericChart (Z S: Scheme.{u}) [IsIntegral Z] (g: Spec (z9.of Z.functionField) ⟶ S) where (domain: Z.Opens) (nonempty: z29 domain) (map: domain.toScheme ⟶ S) (generic: Spec (z9.of Z.functionField) ⟶ domain.toScheme) (generic_eq: generic ≫ domain.ι = Z.fromSpecStalk (genericPoint Z)) (map_eq: generic ≫ map = g)
variable {Z S : Scheme.{u}} [IsIntegral Z]
  (g : Spec (CommRingCat.of Z.functionField) ⟶ S)
  (M N : S.Modules) (d : M ⟶ N) {n : ℕ} (v : Fin n → (M ⟶ N))
def GenericRatios (r: Fin n → Z.functionField): Prop:= IsIso ((Scheme.Modules.pullback g).map d) ∧ ∀ i, (Scheme.Modules.pullback g).map (v i) = (Scheme.Modules.pullback g).map d ≫ scalarEnd ((Scheme.Modules.pullback g).obj N) (r i)
def RegularRatios (C: GenericChart Z S g) (r: Fin n → Z.functionField): Prop:= IsIso ((Scheme.Modules.pullback C.map).map d) ∧ ∃ a: Fin n → Γ(C.domain.toScheme, ⊤), ∀ i, (Scheme.Modules.pullback C.map).map (v i) = (Scheme.Modules.pullback C.map).map d ≫ P2MW.S_AlgebraicGeometry_Polarisation_subsingleton_rigidifiedIso.AlgebraicGeometry.Scheme.Modules.P2K2.smulHom (a i) ((Scheme.Modules.pullback C.map).obj N) ∧ (Scheme.ΓSpecIso (z9.of Z.functionField)).hom (C.generic.appTop (a i)) = r i
end ArithmeticThetaGlobalProjectiveRatiosR0266
@[expose] public section
noncomputable section
namespace ArithmeticThetaGlobalProjectiveRatiosR0266
open CategoryTheory AlgebraicGeometry
variable {Z S : Scheme.{u}} [IsIntegral Z]
  (g : Spec (CommRingCat.of Z.functionField) ⟶ S)

def Refines (C C' : GenericChart Z S g) : Prop :=
  ∃ j : C'.domain.toScheme ⟶ C.domain.toScheme,
    IsOpenImmersion j ∧ j ≫ C.domain.ι = C'.domain.ι ∧
      j ≫ C.map = C'.map ∧ C'.generic ≫ j = C.generic

end ArithmeticThetaGlobalProjectiveRatiosR0266
end

namespace PalomarProjective954
open CategoryTheory AlgebraicGeometry ArithmeticThetaGlobalProjectiveRatiosR0266
open ArithmeticThetaInvariantRatiosR0265 ArithmeticThetaLocalWeierstrassR0203
def QuotientTransfer : Prop :=
 ∀ (Z S : Scheme.{0}) [IsIntegral Z]
   (g : Spec (CommRingCat.of Z.functionField) ⟶ S)
   (C : GenericChart Z S g)
   (K : Type) [Field K] (θ : Z.functionField →+* K) (t : Base K ⟶ S),
   Spec.map (CommRingCat.ofHom θ) ≫ g = t →
   ∀ (M N : S.Modules), Scheme.Modules.IsInvertible M → Scheme.Modules.IsInvertible N →
   ∀ (d : M ⟶ N) (n : ℕ) (v : Fin n → (M ⟶ N)) (s : Fin n → K),
   IsIso ((Scheme.Modules.pullback t).map d) →
   (∀ j, (Scheme.Modules.pullback t).map (v j) =
     (Scheme.Modules.pullback t).map d ≫ scalarEnd ((Scheme.Modules.pullback t).obj N) (s j)) →
   ∃ (r : Fin n → Z.functionField) (C' : GenericChart Z S g),
     GenericRatios g M N d v r ∧ Refines g C C' ∧ RegularRatios g M N d v C' r ∧
     ∀ j, θ (r j) = s j

theorem quotient_transfer : QuotientTransfer := by sorry
end PalomarProjective954
