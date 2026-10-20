module
public import MainIndependentDefinitions198
public import OriginalArithmeticPrefix198
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace ArithmeticThetaPalomarMain172.Bridges198
open ArithmeticThetaPalomarMain172
variable {n h : ℕ} (A : Matrices n h)
lemma commonN_eq : commonN A = ArithmeticThetaLatticeSectionsR0188.commonN A := rfl
lemma centered_eq (m : ℕ) (a : Fin m) :
    centered m a = ArithmeticThetaLatticeSectionsR0188.centered m a := rfl
/-- Copy the actual fields; no new choice of representatives, pairs or count. -/
def fromOriginal (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) : Indexing A where
  representatives := U.representatives
  residue := U.residue
  count := U.count
  pair := U.pair
  index := U.index
/-- Reverse fieldwise conversion, useful for checking that no data were omitted. -/
def toOriginal (U : Indexing A) : ArithmeticThetaLatticeSectionsR0188.Indexing A where
  representatives := U.representatives
  residue := U.residue
  count := U.count
  pair := U.pair
  index := U.index
lemma fromOriginal_count (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) :
    (fromOriginal A U).count = U.count := rfl
lemma fromOriginal_indexed (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) :
    Indexed A (fromOriginal A U) ↔ ArithmeticThetaLatticeSectionsR0188.Indexed A U := Iff.rfl
lemma toOriginal_indexed (U : Indexing A) :
    ArithmeticThetaLatticeSectionsR0188.Indexed A (toOriginal A U) ↔ Indexed A U := Iff.rfl
lemma to_fromOriginal (U : ArithmeticThetaLatticeSectionsR0188.Indexing A) :
    toOriginal A (fromOriginal A U) = U := by cases U; rfl
lemma from_toOriginal (U : Indexing A) :
    fromOriginal A (toOriginal A U) = U := by cases U; rfl
end ArithmeticThetaPalomarMain172.Bridges198
#print axioms ArithmeticThetaPalomarMain172.Bridges198.fromOriginal_indexed
#print axioms ArithmeticThetaPalomarMain172.Bridges198.to_fromOriginal
