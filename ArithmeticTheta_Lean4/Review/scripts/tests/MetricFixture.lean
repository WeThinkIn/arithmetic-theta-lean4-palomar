import Lean

/-! Regression fixture for the reading-dependency metric, not a paper theorem. -/
namespace MetricFixture

def base (n : Nat) := n + 1
abbrev alias := base
def witnessProperty (n : Nat) : Prop := n = 0
noncomputable def chosen : Nat :=
  Classical.choose (show ∃ n, witnessProperty n from ⟨0, rfl⟩)
noncomputable opaque hidden : Nat := chosen
structure Holder where
  value : Nat
  proof : witnessProperty value
def auxiliary (n : Nat) := n * 2

theorem baseStatement : base 0 = 1 := rfl
theorem aliasStatement : alias 0 = 1 := rfl
theorem wrappedStatement : ∃ w : Holder, w.value = 0 := ⟨⟨0, rfl⟩, rfl⟩
theorem chosenStatement : chosen = chosen := rfl
theorem opaqueStatement : hidden = hidden := rfl
theorem proofOnlyStatement : base 0 = 1 :=
  (fun (_ : auxiliary 0 = 0) => (rfl : base 0 = 1)) rfl

open Lean in
run_meta do
  let .thmInfo proof ← getConstInfo ``proofOnlyStatement
    | throwError "Fixture theorem was not elaborated"
  unless proof.value.getUsedConstants.contains ``auxiliary do
    throwError "Fixture no longer contains the proof-only auxiliary definition"

end MetricFixture
