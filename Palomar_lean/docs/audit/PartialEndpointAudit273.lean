module
public import ActualEarlierCertificate
public import AlgebraicModelCubicR0144
public import AlgebraicTateCoordinatesR0143
public import ArbitraryFormalCoverConstantR0210
public import ArithmeticGeometricFamilyExistenceR0189
public import BinaryOrthogonalExampleR0268
public import CommonHalfHodgeCoverR0185
public import CompactUnaryHodgeRealizationR0183
public import ComponentDiscriminantDivisorR0184
public import ComponentHodgePowerDegreeR0184
public import ComputedFamilyFormalUnaryConsumerR0127
public import ComputedOrthogonalization
public import ComputedRationalLDLR0229
public import ConservativeMatrixKernelR0189
public import CoordinateExactPolesR0143
public import Det80CoefficientMinor
public import Det80CompleteClassification
public import Det80LocalRealization
public import Det80OrderClassification
public import Det80Similarity
public import Det80ThetaIndependence
public import DiscriminantTateRootR0185
public import DiscriminantTwistUnitR0185
public import EarlyCertificateAssembly
public import FiniteEtaleNormFamilyR0251
public import FormalJacobiTripleProduct
public import FourTorsionTateBehaviorR0190
public import GeneralDPlusDualR0242
public import GeneralDPlusEvenUnimodularR0242
public import GeneralDPlusThetaRealizationR0242
public import GeometricComponentCuspBoundR0184
public import GeometricFamilyConservativeCutoffR0189
public import GlobalNormalizedDifferentialR0145
public import HadamardJacobi
public import IndividualCosetIntegralProductR0127
public import IntegralGramOrthogonalization
public import LDLThetaPrefixR0229
public import LaurentPoweredNormR0064
public import NormExponentAlgebra
public import Rank16Nonisometry
public import Rank16Theta
public import RankZero
public import RationalPreimageCosetsR0127
public import RationalSchurCompletionR0229
public import RecursiveEllipsoidEnumerationR0229
public import RelativeFourTorsionRootR0190
public import SchemeDiscriminantExistenceR0244
public import SchemeDiscriminantNaturalityR0244
public import SchemeKatoIntrinsicCharacterizationR0254
public import SchemeKatoUnitNaturalityR0250
public import ShiftedIntegerIntervalR0229
public import SourceOrthogonalFactorizationR0127
public import TateBasicFourthIdentity
public import TateGeneralAddition
public import UnaryParameterIdentificationR0127
public import UnaryPowerGeometricRealizationR0160

@[expose] public section
set_option autoImplicit false
universe u v w u_1 u_2 u_3 u_4
set_option maxHeartbeats 4000000

-- binary-orthogonal-example
example : ArithmeticThetaComputed.validGram ArithmeticThetaFullSourceR0268.binaryGram ∧ ArithmeticThetaFullSourceR0268.binaryBasis.det = 2 ∧ ArithmeticThetaOrthogonalConsumerR0127.OrthogonalData ArithmeticThetaFullSourceR0268.binaryGram ArithmeticThetaFullSourceR0268.binaryBasis ArithmeticThetaFullSourceR0268.binaryNorms ∧ ∃ t : Fin 2 → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice ArithmeticThetaFullSourceR0268.binaryBasis, (∀ i, (t i).val = ArithmeticThetaFullSourceR0268.binaryRepresentatives i) ∧ Function.Bijective (fun i => ArithmeticThetaOrthogonalConsumerR0127.cosetClass ArithmeticThetaFullSourceR0268.binaryBasis (t i)) ∧ (∀ i j, ((ArithmeticThetaFullSourceR0268.binaryResidues i j : ℤ) : ℚ) = (ArithmeticThetaFullSourceR0268.binaryNorms j : ℚ) * (t i).val j) ∧ ArithmeticThetaOrthogonalConsumerR0127.thetaZ ArithmeticThetaFullSourceR0268.binaryGram = ArithmeticThetaOrthogonalConsumerR0127.cosetSeries ArithmeticThetaFullSourceR0268.binaryNorms (ArithmeticThetaFullSourceR0268.binaryRepresentatives 0) + ArithmeticThetaOrthogonalConsumerR0127.cosetSeries ArithmeticThetaFullSourceR0268.binaryNorms (ArithmeticThetaFullSourceR0268.binaryRepresentatives 1) ∧ (∀ (D : ℕ) (hD : D ≠ 0), 92 ∣ D → PowerSeries.expand D hD (ArithmeticThetaOrthogonalConsumerR0127.thetaZ ArithmeticThetaFullSourceR0268.binaryGram) = ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 2 (D / 4) 0 * ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 46 (D / 92) 0 + ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 2 (D / 4) 1 * ArithmeticThetaOrthogonalConsumerR0127.scaledUnary 46 (D / 92) 23) := by exact ArithmeticThetaFullSourceR0268.binary_orthogonal_example
#print axioms ArithmeticThetaFullSourceR0268.binary_orthogonal_example

-- accepted-000
example : ∀ (Q : (Fin 0 → ℤ) → ℕ), Q 0 = 0 → ∀ n : ℕ, Nat.card {x : Fin 0 → ℤ // Q x = n} = if n = 0 then 1 else 0 := by exact ArithmeticThetaElementary.rank_zero_coefficients
#print axioms ArithmeticThetaElementary.rank_zero_coefficients

-- accepted-001
example : ∀ (h : ℕ) (c : Fin h → ℂ), (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = 0 ↔ (∑ i : Fin h, c i) = 0 := by exact ArithmeticThetaElementary.rank_zero_kernel
#print axioms ArithmeticThetaElementary.rank_zero_kernel

-- accepted-002
example : ∀ (h : ℕ), 0 < h → ∀ f : PowerSeries ℂ, (∃ c : Fin h → ℂ, (∑ i : Fin h, c i • (1 : PowerSeries ℂ)) = f) ↔ ∃ z : ℂ, f = PowerSeries.C z := by exact ArithmeticThetaElementary.rank_zero_image
#print axioms ArithmeticThetaElementary.rank_zero_image

-- accepted-003
example : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → ∃ (B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℤ), B.det ≠ 0 ∧ (∀ i, 0 < m i ∧ Even (m i)) ∧ B.transpose * A * B = Matrix.diagonal m := by exact ArithmeticThetaLattice.even_integral_gram_orthogonalization
#print axioms ArithmeticThetaLattice.even_integral_gram_orthogonalization

-- accepted-004
example : ((fun i j : Fin 3 => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (![0, 1, 3] : Fin 3 → ℤ) i} : ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = ![![1, 1, 1], ![2, 0, 0], ![0, 2, 0]] := by exact ArithmeticThetaDet80.actual_coefficient_matrix
#print axioms ArithmeticThetaDet80.actual_coefficient_matrix

-- accepted-005
example : Matrix.det ((fun i j : Fin 3 => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (![0, 1, 3] : Fin 3 → ℤ) i} : ℤ)) : Matrix (Fin 3) (Fin 3) ℤ) = 4 := by exact ArithmeticThetaDet80.actual_minor_determinant
#print axioms ArithmeticThetaDet80.actual_minor_determinant

-- accepted-006
example : LinearMap.ker (∑ j : Fin 3, (LinearMap.proj j : (Fin 3 → ℂ) →ₗ[ℂ] ℂ).smulRight (PowerSeries.mk (fun m : ℕ => (Nat.card {v : ℤ × ℤ // (![v.1 ^ 2 + 20 * v.2 ^ 2, 3 * v.1 ^ 2 + 2 * v.1 * v.2 + 7 * v.2 ^ 2, 4 * v.1 ^ 2 + 5 * v.2 ^ 2] : Fin 3 → ℤ) j = (m : ℤ)} : ℂ)) : PowerSeries ℂ)) = ⊥ := by exact ArithmeticThetaDet80.actual_theta_kernel_zero
#print axioms ArithmeticThetaDet80.actual_theta_kernel_zero

-- accepted-007
example : (PowerSeries.mk (fun e => PowerSeries.coeff e ((1 + PowerSeries.C (LaurentPolynomial.T 1)) * ∏ j ∈ Finset.range e, (1 - PowerSeries.X ^ (j + 1)) * (1 + PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X ^ (j + 1)) * (1 + PowerSeries.C (LaurentPolynomial.T (-1)) * PowerSeries.X ^ (j + 1)) : PowerSeries (LaurentPolynomial ℤ)))) = PowerSeries.mk (fun d => ∑ k ∈ Finset.Icc (-(d : ℤ)) ((d : ℤ) + 1), if k * (k - 1) = 2 * (d : ℤ) then (LaurentPolynomial.T k : LaurentPolynomial ℤ) else 0) := by exact ArithmeticThetaDurfee.formal_jacobi_triple_product
#print axioms ArithmeticThetaDurfee.formal_jacobi_triple_product

-- accepted-008
example : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), A.IsSymm → (∀ i, Even (A i i)) → ((1 / 2 : ℚ) • (A.map (Int.castRingHom ℚ)).toQuadraticForm').PosDef → (∀ i, 0 < (ArithmeticThetaOrthogonalAlgorithm.naturalNorms A) i ∧ Even ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms A) i) ∧ ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms A) i : ℤ) = (ArithmeticThetaOrthogonalAlgorithm.norms A) i) ∧ ArithmeticThetaOrthogonalAlgorithm.indexValue A = ∏ i : Fin n, ((ArithmeticThetaOrthogonalAlgorithm.basisMatrix A) i i).toNat ∧ 0 < ArithmeticThetaOrthogonalAlgorithm.indexValue A := by exact ArithmeticThetaOrthogonalAlgorithm.computed_natural_data
#print axioms ArithmeticThetaOrthogonalAlgorithm.computed_natural_data

-- accepted-009
example : ArithmeticThetaHadamard.a ^ 4 = ArithmeticThetaHadamard.b ^ 4 + ArithmeticThetaHadamard.c ^ 4 := by exact ArithmeticThetaHadamard.jacobi_formal
#print axioms ArithmeticThetaHadamard.jacobi_formal

-- accepted-010
example : ∀ a b c : ℤ, 0 < a → 4*a*c-b^2 = 80 → ArithmeticThetaBinary.gramContent a b c = 2 → ∃ (j : Fin 3) (U : Matrix (Fin 2) (Fin 2) ℤ), IsUnit U.det ∧ U.transpose * ArithmeticThetaBinary.gram a b c * U = ArithmeticThetaBinary.forms j := by exact ArithmeticThetaBinary.all_positive_classes
#print axioms ArithmeticThetaBinary.all_positive_classes

-- accepted-011
example : ∀ (i j : Fin 3), i ≠ j → ¬ ∃ (s : ℚ) (U : Matrix (Fin 2) (Fin 2) ℤ), 0 < s ∧ IsUnit U.det ∧ (U.map (Int.castRingHom ℚ)).transpose * (ArithmeticThetaBinary.forms i).map (Int.castRingHom ℚ) * U.map (Int.castRingHom ℚ) = s • (ArithmeticThetaBinary.forms j).map (Int.castRingHom ℚ) := by exact ArithmeticThetaBinary.similarity_distinct
#print axioms ArithmeticThetaBinary.similarity_distinct

-- accepted-012
example : ∀ j : Fin 3, (ArithmeticThetaBinary.embeddings j).det ≠ 0 ∧ (ArithmeticThetaBinary.embeddings j).transpose * (ArithmeticThetaBinary.forms 0).map (Int.castRingHom ℚ) * ArithmeticThetaBinary.embeddings j = (![1,3,1] : Fin 3 → ℚ) j • (ArithmeticThetaBinary.forms j).map (Int.castRingHom ℚ) := by exact ArithmeticThetaBinary.ambient_realization
#print axioms ArithmeticThetaBinary.ambient_realization

-- accepted-013
example : ∀ a b c : ℤ, 0 < a → 0 < 4*a*c-b^2 → ArithmeticThetaBinary.sameLocalSmith a b c → ∃! j : Fin 3, ∃ U : Matrix (Fin 2) (Fin 2) ℤ, IsUnit U.det ∧ U.transpose * ArithmeticThetaBinary.gram a b c * U = ArithmeticThetaBinary.forms j := by exact ArithmeticThetaBinary.same_order_classes
#print axioms ArithmeticThetaBinary.same_order_classes

-- accepted-014
example : ¬ ∃ (s : ℚ) (U : Matrix (Fin 16) (Fin 16) ℤ), 0 < s ∧ IsUnit U.det ∧ (U.map (Int.castRingHom ℚ)).transpose * (ArithmeticThetaRank16.sumGram).map (Int.castRingHom ℚ) * U.map (Int.castRingHom ℚ) = s • (ArithmeticThetaRank16.latticeGram 16).map (Int.castRingHom ℚ) := by exact ArithmeticThetaRank16.no_similarity
#print axioms ArithmeticThetaRank16.no_similarity

-- accepted-015
example : ArithmeticThetaRank16.sumTheta = ArithmeticThetaRank16.theta 16 := by exact ArithmeticThetaRank16.integral_identity
#print axioms ArithmeticThetaRank16.integral_identity

-- accepted-016
example : ∀ v : Fin 2 → ℂ, (∑ i, v i • ArithmeticThetaRank16.columns i) = 0 ↔ ∃ t : ℂ, v = ![t, -t] := by exact ArithmeticThetaRank16.two_column_kernel
#print axioms ArithmeticThetaRank16.two_column_kernel

-- accepted-017
example : ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) ≤ LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin) ∧ ((ArithmeticThetaComputed.coefficientMatrix A B).rank = h → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = ⊥) ∧ (∀ W : Submodule ℂ (Fin h → ℂ), (∀ c ∈ W, ArithmeticThetaComputed.thetaMap A c = 0) → Module.finrank ℂ W = h - (ArithmeticThetaComputed.coefficientMatrix A B).rank → W = LinearMap.ker (ArithmeticThetaComputed.thetaMap A) ∧ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin)) := by exact ArithmeticThetaEarlyAssembly.actual_earlier_certificate
#print axioms ArithmeticThetaEarlyAssembly.actual_earlier_certificate

-- accepted-018
example : ∀ {k : Type u} [Field k] [CharZero k], ArithmeticThetaTateSeries.theta k ^ 4 = 4 * (ArithmeticThetaTateSeries.tateX 2 1 (1:k) - ArithmeticThetaTateSeries.tateX 2 0 (-1:k)) := by exact ArithmeticThetaTateSeries.basic_fourth
#print axioms ArithmeticThetaTateSeries.basic_fourth

-- accepted-023
example : ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ), B.det ≠ 0 → ∃ E : ArithmeticThetaOrthogonalConsumerR0127.RationalCosets B ≃+ ((Fin n → ℤ) ⧸ LinearMap.range (Matrix.mulVecLin B)), (∀ (t : ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B) (x : Fin n → ℤ), (B.map (Int.castRingHom ℚ)).mulVec t.val = ArithmeticThetaOrthogonalConsumerR0127.castVec n x → E (ArithmeticThetaOrthogonalConsumerR0127.cosetClass B t) = (LinearMap.range (Matrix.mulVecLin B)).mkQ x) ∧ Finite (ArithmeticThetaOrthogonalConsumerR0127.RationalCosets B) ∧ Nat.card (ArithmeticThetaOrthogonalConsumerR0127.RationalCosets B) = B.det.natAbs ∧ ∃ t : Fin B.det.natAbs → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B, ArithmeticThetaOrthogonalConsumerR0127.Representatives B t := by exact ArithmeticThetaOrthogonalConsumerR0127.rational_preimage_cosets
#print axioms ArithmeticThetaOrthogonalConsumerR0127.rational_preimage_cosets

-- accepted-024
example : ∀ (k : Type u) [Field k] [CharZero k] (m : ℕ) [NeZero m] (w : ℕ) (hw : w ≠ 0) (ν : ℤ) (a : Fin m), Int.ModEq (m : ℤ) ν (a.val : ℤ) → PowerSeries.map (Int.castRingHom k) (ArithmeticThetaOrthogonalConsumerR0127.scaledUnary m w ν) = PowerSeries.expand w hw (ArithmeticThetaSchrodingerR0119.unary k m a) := by exact ArithmeticThetaOrthogonalConsumerR0127.unary_parameter_identification
#print axioms ArithmeticThetaOrthogonalConsumerR0127.unary_parameter_identification

-- accepted-025
example : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), ArithmeticThetaComputed.validGram A → ArithmeticThetaOrthogonalConsumerR0127.OrthogonalData A B m → ∀ (t : ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B) (ν : Fin n → ℤ), (∀ j, (ν j : ℚ) = (m j : ℚ) * t.val j) → (∀ r : Fin n → ℤ, (∀ j, Int.ModEq (m j : ℤ) (r j) (ν j)) → ∃ a : ℕ, (∑ j : Fin n, (r j : ℚ)^2 / (2 * (m j : ℚ))) = (a : ℚ)) ∧ (∀ (D : ℕ) (hD : D ≠ 0), (∀ j, 2 * m j ∣ D) → PowerSeries.expand D hD (ArithmeticThetaOrthogonalConsumerR0127.cosetSeries m t.val) = ∏ j : Fin n, ArithmeticThetaOrthogonalConsumerR0127.scaledUnary (m j) (D / (2 * m j)) (ν j)) := by exact ArithmeticThetaOrthogonalConsumerR0127.individual_coset_integral_product
#print axioms ArithmeticThetaOrthogonalConsumerR0127.individual_coset_integral_product

-- accepted-026
example : ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℤ) (m : Fin n → ℕ), ArithmeticThetaComputed.validGram A → ArithmeticThetaOrthogonalConsumerR0127.OrthogonalData A B m → ∀ t : Fin B.det.natAbs → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice B, ArithmeticThetaOrthogonalConsumerR0127.Representatives B t → ∃ ν : Fin B.det.natAbs → Fin n → ℤ, (∀ i j, (ν i j : ℚ) = (m j : ℚ) * (t i).val j) ∧ ArithmeticThetaOrthogonalConsumerR0127.thetaZ A = ∑ i : Fin B.det.natAbs, ArithmeticThetaOrthogonalConsumerR0127.cosetSeries m (t i).val ∧ (∀ (D : ℕ) (hD : D ≠ 0), (∀ j, 2 * m j ∣ D) → PowerSeries.expand D hD (ArithmeticThetaOrthogonalConsumerR0127.thetaZ A) = ∑ i : Fin B.det.natAbs, ∏ j : Fin n, ArithmeticThetaOrthogonalConsumerR0127.scaledUnary (m j) (D / (2 * m j)) (ν i j)) := by exact ArithmeticThetaOrthogonalConsumerR0127.source_orthogonal_factorization
#print axioms ArithmeticThetaOrthogonalConsumerR0127.source_orthogonal_factorization

-- accepted-027
example : ∀ (n h : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (D : ℕ) (hD : D ≠ 0), (∀ (i : Fin h) (j : Fin n), 2 * (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) ∣ D) → ∃ (t : (i : Fin h) → Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs → ArithmeticThetaOrthogonalConsumerR0127.preimageLattice (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i))) (ν : (i : Fin h) → Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs → (j : Fin n) → Fin (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j)) (hw : ∀ (i : Fin h) (j : Fin n), D / (2 * (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j)) ≠ 0), (∀ i, ArithmeticThetaOrthogonalConsumerR0127.Representatives (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)) (t i)) ∧ (∀ (i : Fin h) (a : Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs) (j : Fin n), ∃ z : ℤ, ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) : ℚ) * (t i a).val j = ((ν i a j).val : ℚ) + ((ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) : ℚ) * (z : ℚ)) ∧ (∀ c : Fin h → ℂ, PowerSeries.expand D hD (ArithmeticThetaComputed.thetaMap A c) = ∑ i : Fin h, c i • (∑ a : Fin (ArithmeticThetaOrthogonalAlgorithm.basisMatrix (A i)).det.natAbs, ∏ j : Fin n, PowerSeries.expand (D / (2 * (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j))) (hw i j) (ArithmeticThetaSchrodingerR0119.unary ℂ (ArithmeticThetaOrthogonalAlgorithm.naturalNorms (A i) j) (ν i a j)))) := by exact ArithmeticThetaOrthogonalConsumerR0127.computed_family_formal_unary_consumer
#print axioms ArithmeticThetaOrthogonalConsumerR0127.computed_family_formal_unary_consumer

-- accepted-058
example : ∀ (c R : ℚ) (z : ℤ), z ∈ ArithmeticThetaLDLEnumerationR0229.shiftedInterval c R ↔ ((z : ℚ) - c)^2 ≤ R := by exact ArithmeticThetaLDLEnumerationR0229.shifted_integer_interval
#print axioms ArithmeticThetaLDLEnumerationR0229.shifted_integer_interval

-- accepted-059
example : ∀ (n : ℕ) (A : ArithmeticThetaLDLEnumerationR0229.QMatrix (n+1)), A.IsSymm → A.toQuadraticForm'.PosDef → 0 < A 0 0 ∧ (ArithmeticThetaLDLEnumerationR0229.schur A).IsSymm ∧ (ArithmeticThetaLDLEnumerationR0229.schur A).toQuadraticForm'.PosDef ∧ ∀ (z : ℚ) (y : Fin n → ℚ), ArithmeticThetaLDLEnumerationR0229.energy A (Fin.cons z y) = A 0 0 * (z + (∑ j : Fin n, A 0 j.succ * y j) / A 0 0)^2 + ArithmeticThetaLDLEnumerationR0229.energy (ArithmeticThetaLDLEnumerationR0229.schur A) y := by exact ArithmeticThetaLDLEnumerationR0229.rational_schur_completion
#print axioms ArithmeticThetaLDLEnumerationR0229.rational_schur_completion

-- accepted-060
example : ∀ (n : ℕ) (A : ArithmeticThetaLDLEnumerationR0229.QMatrix n), A.IsSymm → A.toQuadraticForm'.PosDef → (∀ i : Fin n, 0 < (ArithmeticThetaLDLEnumerationR0229.ldl n A).1 i) ∧ (∀ i : Fin n, (ArithmeticThetaLDLEnumerationR0229.ldl n A).2 i i = 1) ∧ (∀ i j : Fin n, j < i → (ArithmeticThetaLDLEnumerationR0229.ldl n A).2 i j = 0) ∧ A = (ArithmeticThetaLDLEnumerationR0229.ldl n A).2.transpose * Matrix.diagonal (ArithmeticThetaLDLEnumerationR0229.ldl n A).1 * (ArithmeticThetaLDLEnumerationR0229.ldl n A).2 := by exact ArithmeticThetaLDLEnumerationR0229.computed_rational_ldl
#print axioms ArithmeticThetaLDLEnumerationR0229.computed_rational_ldl

-- accepted-061
example : ∀ (n : ℕ) (A : ArithmeticThetaLDLEnumerationR0229.QMatrix n), A.IsSymm → A.toQuadraticForm'.PosDef → ∀ (B : ℚ) (x : Fin n → ℤ), x ∈ ArithmeticThetaLDLEnumerationR0229.enumerate n A B ↔ ArithmeticThetaLDLEnumerationR0229.energy A (fun i => (x i : ℚ)) ≤ B := by exact ArithmeticThetaLDLEnumerationR0229.recursive_ellipsoid_enumeration
#print axioms ArithmeticThetaLDLEnumerationR0229.recursive_ellipsoid_enumeration

-- accepted-062
example : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), ArithmeticThetaComputed.validGram A → (∀ m : ℕ, ArithmeticThetaLDLEnumerationR0229.shell A m = ArithmeticThetaEnumeration.shellVectors A m) ∧ ∀ B : ℕ, ArithmeticThetaLDLEnumerationR0229.coefficients A B = ArithmeticThetaEnumeration.coefficientsUpTo A B ∧ (ArithmeticThetaLDLEnumerationR0229.coefficients A B).length = B + 1 ∧ ∀ a : Fin (B+1), ((ArithmeticThetaLDLEnumerationR0229.coefficients A B).getD a.val 0 : ℂ) = PowerSeries.coeff a.val (ArithmeticThetaComputed.theta A) := by exact ArithmeticThetaLDLEnumerationR0229.ldl_theta_prefix
#print axioms ArithmeticThetaLDLEnumerationR0229.ldl_theta_prefix

-- accepted-063
example : ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B = ArithmeticThetaComputed.coefficientMatrix A B ∧ ArithmeticThetaElimination.run (ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B) = ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B) ∧ (ArithmeticThetaComputed.prefixMap B).comp (ArithmeticThetaComputed.thetaMap A) = ((ArithmeticThetaLDLEnumerationR0229.coefficientMatrix A B).map (algebraMap ℚ ℂ)).mulVecLin := by exact ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix
#print axioms ArithmeticThetaLDLEnumerationR0229.ldl_coefficient_matrix

-- accepted-077
example : ∀ n : ℕ, 8 ∣ n → ArithmeticThetaComputed.validGram (ArithmeticThetaRank16.latticeGram n) ∧ (ArithmeticThetaRank16.latticeGram n).det = 1 ∧ (∀ v : Fin n → ℚ, v ∈ ArithmeticThetaGeneralDPlusR0242.lattice n ↔ ArithmeticThetaRank16.originalDPlus n v) ∧ (∃ b : Module.Basis (Fin n) ℤ (ArithmeticThetaGeneralDPlusR0242.lattice n), ∀ (j i : Fin n), (b j).val i = ArithmeticThetaRank16.latticeBasis n i j) ∧ (∀ v : Fin n → ℚ, ArithmeticThetaRank16.originalDPlus n v → ∃ z : ℤ, (∑ i, v i ^ 2) / 2 = (z : ℚ)) := by exact ArithmeticThetaGeneralDPlusR0242.general_dplus_even_unimodular
#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_even_unimodular

-- accepted-078
example : ∀ n : ℕ, 8 ∣ n → ∀ v : Fin n → ℚ, ArithmeticThetaGeneralDPlusR0242.dualMember n v ↔ v ∈ ArithmeticThetaGeneralDPlusR0242.lattice n := by exact ArithmeticThetaGeneralDPlusR0242.general_dplus_dual
#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_dual

-- accepted-079
example : ∀ n : ℕ, 8 ∣ n → (∀ m : ℕ, ∃ e : ArithmeticThetaGeneralDPlusR0242.OriginalShell n m ≃ ArithmeticThetaRank16.NormShell n (8 * m), ∀ v, ArithmeticThetaRank16.doubledRealization n (e v).val = v.val) ∧ ArithmeticThetaGeneralDPlusR0242.originalTheta n = ArithmeticThetaRank16.theta n ∧ ArithmeticThetaComputed.theta (ArithmeticThetaRank16.latticeGram n) = PowerSeries.map (Int.castRingHom ℂ) (ArithmeticThetaGeneralDPlusR0242.originalTheta n) ∧ (0 < n → (2 : PowerSeries ℤ) * PowerSeries.expand 8 (by decide) (ArithmeticThetaGeneralDPlusR0242.originalTheta n) = ArithmeticThetaHadamard.a ^ n + ArithmeticThetaHadamard.b ^ n + ArithmeticThetaHadamard.c ^ n) := by exact ArithmeticThetaGeneralDPlusR0242.general_dplus_theta_realization
#print axioms ArithmeticThetaGeneralDPlusR0242.general_dplus_theta_realization

-- accepted-088
example : ∀ (n h B : ℕ) (A : Fin h → Matrix (Fin n) (Fin n) ℤ), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ W : Submodule ℂ (Fin h → ℂ), W ≤ LinearMap.ker (ArithmeticThetaComputed.thetaMap A) → Module.finrank ℂ W = h - (ArithmeticThetaComputed.coefficientMatrix A B).rank → (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ)) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.freeColumns (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B))).length => fun j => ((ArithmeticThetaElimination.nullBasis (ArithmeticThetaComputed.coefficientMatrix A B) t j : ℚ) : ℂ))) = LinearMap.ker (ArithmeticThetaComputed.thetaMap A)) ∧ (LinearIndependent ℂ (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t))) ∧ Submodule.span ℂ (Set.range (fun t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length => ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)))) = LinearMap.range (ArithmeticThetaComputed.thetaMap A)) ∧ ∀ j : Fin h, ArithmeticThetaComputed.theta (A j) = ∑ t : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length, ((ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) ∧ ∀ c : Fin (ArithmeticThetaElimination.run (ArithmeticThetaComputed.coefficientMatrix A B)).pivots.length → ℚ, ArithmeticThetaComputed.theta (A j) = ∑ t, ((c t : ℚ) : ℂ) • ArithmeticThetaComputed.theta (A (ArithmeticThetaComputed.selectedIndex A B t)) → c = ArithmeticThetaElimination.columnCoordinates (ArithmeticThetaComputed.coefficientMatrix A B) j := by exact ArithmeticThetaDegreeAssembly.certified_theta_image_data
#print axioms ArithmeticThetaDegreeAssembly.certified_theta_image_data

-- accepted-089
example : ∀ {k : Type u} [Field k] [CharZero k], ∀ (d i j : ℕ) (a b : k), ArithmeticThetaTateSeries.Admissible d i a → ArithmeticThetaTateSeries.Admissible d j b → (ArithmeticThetaTateSeries.toLaurent k (ArithmeticThetaTateSeries.tateX d i (a : k)) - ArithmeticThetaTateSeries.toLaurent k (ArithmeticThetaTateSeries.tateX d j (b : k))) * (ArithmeticThetaTateIdentities.gammaLaurent d (i:ℤ) a)^2 * (ArithmeticThetaTateIdentities.gammaLaurent d (j:ℤ) b)^2 = -HahnSeries.single (j:ℤ) b * (ArithmeticThetaTateSeries.toLaurent k (PowerSeries.map (Int.castRingHom k) (ArithmeticThetaUnaryProduct.etaProduct d)))^4 * ArithmeticThetaTateIdentities.gammaLaurent d ((i:ℤ)-(j:ℤ)) (a/b) * ArithmeticThetaTateIdentities.gammaLaurent d ((i:ℤ)+(j:ℤ)) (a*b) := by exact ArithmeticThetaTateIdentities.general_annular_addition
#print axioms ArithmeticThetaTateIdentities.general_annular_addition

-- accepted-090
example : ∀ (c d : ℚ), (d - 1) * (-c * (c - 1) / 2) + c * ((c - 1) * (d - 1) / 2) = 0 ∧ (d ^ 2 - 1) * (c ^ 2 - 1) / 12 + (-c * (c - 1) / 2) * d * (d - 1) / 2 + ((c ^ 2 - 1) * (d - 1) * (2 * d - 1) / 12 - d * (c - 1) * (d - 1) / 4) = 0 ∧ (d ^ 2 - 1) * (-c * (c - 1) / 2) + (c - 1) * (d - 1) / 2 = (c - 1) * (d - 1) * (1 - c * (d + 1)) / 2 := by exact ArithmeticThetaElementary.norm_exponent_identities
#print axioms ArithmeticThetaElementary.norm_exponent_identities

-- accepted-091
example : ∀ (c d : ℤ), Odd c → Even ((c - 1) * (d - 1) * (1 - c * (d + 1)) / 2) := by exact ArithmeticThetaElementary.norm_sign_exponent_even
#print axioms ArithmeticThetaElementary.norm_sign_exponent_even

-- accepted-092
example : ∀ (K : Type) [Field K] [CharZero K] (c d : ℕ) (ζ : K), 1 < c → 0 < d → Nat.Coprime c d → IsPrimitiveRoot ζ d → ∀ (H : Fin d → Fin d → ArithmeticThetaLaurentNormR0064.Series K) (b : ArithmeticThetaLaurentNormR0064.Series K), (∀ i j : Fin d, ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff K) d (c * i.val) (ArithmeticThetaLaurentNormR0064.a K ζ j.val c) (H i j)) → ArithmeticThetaLaurentNormR0064.IsGamma (ArithmeticThetaLaurentNormR0064.Coeff K) d 0 (ArithmeticThetaLaurentNormR0064.w K ^ (c * d)) b → (∏ i : Fin d, ∏ j : Fin d, H i j) = (-1 : ArithmeticThetaLaurentNormR0064.Series K) ^ (-ArithmeticThetaNormFiniteR0063.S c d) * ArithmeticThetaLaurentNormR0064.z K d ^ (-(c : ℤ) * ArithmeticThetaNormFiniteR0063.S c d) * ArithmeticThetaLaurentNormR0064.Q K d ^ (-ArithmeticThetaNormFiniteR0063.E c d) * b := by exact ArithmeticThetaLaurentNormR0064.powered_gamma_norm
#print axioms ArithmeticThetaLaurentNormR0064.powered_gamma_norm

-- accepted-050
example : ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of (PowerSeries k))) [CharZero k] [AlgebraicGeometry.Flat f] [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.Smooth (ArithmeticThetaFormalConstants.genericStructure k X f)] [AlgebraicGeometry.GeometricallyConnected (ArithmeticThetaFormalConstants.genericStructure k X f)], ∃ ρ : ArithmeticThetaFormalCoverR0210.Restrictions k X f, ∀ C : ArithmeticThetaFormalCoverR0210.Cover k X f, ArithmeticThetaFormalCoverR0210.ChartConditions k X f C → ∀ v : (∀ i, ArithmeticThetaFormalCoverR0210.Fractions k X f (C.opens i)), ArithmeticThetaFormalCoverR0210.RationalCompatible k X f ρ C v → ArithmeticThetaFormalCoverR0210.NoPole k X f C v → ∃! c : LaurentSeries k, ArithmeticThetaFormalCoverR0210.FractionConstant k X f C v c := by exact ArithmeticThetaFormalCoverR0210.arbitrary_formal_cover_constant
#print axioms ArithmeticThetaFormalCoverR0210.arbitrary_formal_cover_constant

-- accepted-019
example : ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ odd : Bool, ∃! φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ := by exact ArithmeticThetaAlgebraicCoordinatesR0143.algebraic_tate_coordinates
#print axioms ArithmeticThetaAlgebraicCoordinatesR0143.algebraic_tate_coordinates

-- accepted-020
example : ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s), ∀ (odd : Bool) (φ : ArithmeticThetaIdentitySectionsR0138.Dual k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd)), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k odd M s φ → CategoryTheory.IsIso (ArithmeticThetaAlgebraicCoordinatesR0143.pulled k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) s φ) ∧ ∀ e : ArithmeticThetaGenericEvaluationR0140.IdentityFrame k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd), ArithmeticThetaGenericEvaluationR0140.NormalizedFrame k h3 M hM s hs (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e → ArithmeticThetaGenericEvaluationR0140.frameValue k M s (ArithmeticThetaAlgebraicCoordinatesR0143.degree odd) e φ = 1 := by exact ArithmeticThetaAlgebraicCoordinatesR0143.coordinate_exact_poles
#print axioms ArithmeticThetaAlgebraicCoordinatesR0143.coordinate_exact_poles

-- accepted-021
example : ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ArithmeticThetaCubicModelR0144.ModelCubic k M s X Y := by exact ArithmeticThetaCubicModelR0144.algebraic_model_cubic
#print axioms ArithmeticThetaCubicModelR0144.algebraic_model_cubic

-- accepted-022
example : ∀ (k : Type u) [Field k] [CharZero k], ∀ (r : ℕ) (hr : 0 < r) (h3 : 3 ≤ r) (T : ArithmeticThetaInfinitesimalPolygonR0129.Tower k r hr) (he : Even r) (M : ArithmeticThetaProjectiveEffectivityR0135.Model k T) (hM : ArithmeticThetaProjectiveEffectivityR0135.IsModel k T M) (s : Quiver.Hom (ArithmeticThetaAlgebraizedMarkedLineR0136.baseScheme k) M.X) (hs : ArithmeticThetaAlgebraizedMarkedLineR0136.MarkedLift k M (ArithmeticThetaIdentitySectionsR0138.zeroIndex r hr) 1 s) (X : ArithmeticThetaIdentitySectionsR0138.Dual k M s 2) (Y : ArithmeticThetaIdentitySectionsR0138.Dual k M s 3), ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k false M s X → ArithmeticThetaAlgebraicCoordinatesR0143.RealizesCoordinate k true M s Y → ∃! e : CategoryTheory.Iso (SheafOfModules.unit (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).ringCatSheaf : (ArithmeticThetaGenericEvaluationR0140.genericScheme k M).Modules) (AlgebraicGeometry.Scheme.Hom.kaehler (ArithmeticThetaProjectiveEffectivityR0135.genericStructure k M)), ArithmeticThetaCompactifiedDifferentialR0145.IsGlobalDifferentialFrame k M s X Y e := by exact ArithmeticThetaCompactifiedDifferentialR0145.global_normalized_differential
#print axioms ArithmeticThetaCompactifiedDifferentialR0145.global_normalized_differential

-- accepted-080
example : ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∃ d : ArithmeticThetaSchemeDiscriminantR0244.Sections E, ArithmeticThetaSchemeDiscriminantR0244.IsD2 k σ E d := by exact ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_existence
#print axioms ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_existence

-- accepted-081
example : ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (T : AlgebraicGeometry.Scheme.{u}) (τ : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base k)) (F : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S), CategoryTheory.CategoryStruct.comp b σ = τ → ∀ (C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E F b) (d : ArithmeticThetaSchemeDiscriminantR0244.Sections E) (e : ArithmeticThetaSchemeDiscriminantR0244.Sections F), ArithmeticThetaSchemeDiscriminantR0244.IsD2 k σ E d → ArithmeticThetaSchemeDiscriminantR0244.IsD2 k τ F e → ArithmeticThetaSchemeDiscriminantR0244.pull C d = e := by exact ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_naturality
#print axioms ArithmeticThetaSchemeDiscriminantR0244.scheme_discriminant_naturality

-- accepted-083
example : ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ (T : AlgebraicGeometry.Scheme.{u}) (τ : Quiver.Hom T (ArithmeticThetaLocalWeierstrassR0203.Base k)) (H : ArithmeticThetaLocalWeierstrassR0203.Family T) (b : Quiver.Hom T S), CategoryTheory.CategoryStruct.comp b σ = τ → ∀ C : ArithmeticThetaSchemeDiscriminantR0244.Comparison E H b, ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ (v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c) (w : ArithmeticThetaSchemeKatoUnitR0250.UnitSection H c), ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v → ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit H k τ c w → ∃ e : ArithmeticThetaSchemeKatoUnitR0250.complement H c ≤ (TopologicalSpace.Opens.map C.map.base).obj (ArithmeticThetaSchemeKatoUnitR0250.complement E c), (w : H.curve.presheaf.obj (Opposite.op (ArithmeticThetaSchemeKatoUnitR0250.complement H c))) = C.map.appLE _ _ e (v : _) := by exact ArithmeticThetaSchemeKatoUnitR0250.scheme_kato_unit_naturality
#print axioms ArithmeticThetaSchemeKatoUnitR0250.scheme_kato_unit_naturality

-- accepted-086
example : ∀ (k : Type u) [Field k] [CharZero k] (S : AlgebraicGeometry.Scheme.{u}) (σ : Quiver.Hom S (ArithmeticThetaLocalWeierstrassR0203.Base k)) (E : ArithmeticThetaLocalWeierstrassR0203.Family S), ∀ c : ℕ, 1 < c → Nat.Coprime c 6 → ∀ v : ArithmeticThetaSchemeKatoUnitR0250.UnitSection E c, ArithmeticThetaSchemeKatoUnitR0250.IsKatoUnit E k σ c v ↔ ArithmeticThetaSchemeKatoUnitR0250.HasCartierDivisor E c v ∧ ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E 2) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _) ∧ ArithmeticThetaSchemeKatoNormR0251.NormInvariant (ArithmeticThetaSchemeKatoUnitR0250.multiplication E 3) (ArithmeticThetaSchemeKatoUnitR0250.complement E c) (v : _) := by exact ArithmeticThetaKatoCharacterizationR0254.scheme_kato_intrinsic_characterization
#print axioms ArithmeticThetaKatoCharacterizationR0254.scheme_kato_intrinsic_characterization

-- accepted-098
example : ∀ (X Y : AlgebraicGeometry.Scheme.{u}) (f : Quiver.Hom X Y) [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.Etale f], ∃! N : ArithmeticThetaSchemeKatoNormR0251.NormFamily f, ArithmeticThetaSchemeKatoNormR0251.IsNormFamily f N := by exact ArithmeticThetaSchemeKatoNormR0251.finite_etale_norm_family
#print axioms ArithmeticThetaSchemeKatoNormR0251.finite_etale_norm_family

-- accepted-093
example : ∀ (k : Type) [Field k] [CharZero k] (d m N : ℕ), 0 < d → 0 < m → Even m → 0 < N → Even N → m ∣ N → ArithmeticThetaUnaryKatoPowerR0160.GeometricRealization k d m N := by exact ArithmeticThetaUnaryKatoPowerR0160.unary_power_geometric_realization
#print axioms ArithmeticThetaUnaryKatoPowerR0160.unary_power_geometric_realization

-- accepted-028
example : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (m N : ℕ) (hm : 0 < m) (hmeven : Even m) (hN : 0 < N) (hNeven : Even N) (hmN : m ∣ N) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k (ArithmeticThetaCompactUnaryR0183.level N)) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k (ArithmeticThetaCompactUnaryR0183.level N) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k (ArithmeticThetaCompactUnaryR0183.level N) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k (ArithmeticThetaCompactUnaryR0183.level N) H → ∀ ν : ℤ, (-(m : ℤ) ≤ 2*ν ∧ 2*ν < (m : ℤ)) → ∃ (a b : Fin N), a.val = ArithmeticThetaBoundaryHodgeR0182.unaryResidue m N ν ∧ b.val = N/2 ∧ ∃ A : ArithmeticThetaCompactUnaryR0183.OpenPower k m N D a b, ∃! s : (ArithmeticThetaTensorPower.tensorPower X.space H.line (ArithmeticThetaCompactUnaryR0183.weight N)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaCompactUnaryR0183.RealizesUnary k m N H ν A s := by exact ArithmeticThetaCompactUnaryR0183.compact_unary_hodge_realization
#print axioms ArithmeticThetaCompactUnaryR0183.compact_unary_hodge_realization

-- accepted-029
example : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), Finite (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ Nonempty (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ∧ Nonempty ((ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ↪ ArithmeticThetaLevelCount.SignedPrimitivePair L) ∧ 2 * L * Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) := by exact ArithmeticThetaComponentDegreeR0184.geometric_component_cusp_bound
#print axioms ArithmeticThetaComponentDegreeR0184.geometric_component_cusp_bound

-- accepted-030
example : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s → (ArithmeticThetaComponentDegreeR0184.restrict k L D X x H 24 s) ≠ 0 ∧ ∀ (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) ι), ∃ E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ, ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H 24) C (ArithmeticThetaComponentDegreeR0184.restrict k L D X x H 24 s) E ∧ ∀ y : ArithmeticThetaComponentDegreeR0184.Component k L D X x, (y ∈ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = (2*L : ℕ)) ∧ (y ∉ ArithmeticThetaComponentDegreeR0184.cuspSet k L D X x → E y = 0) := by exact ArithmeticThetaComponentDegreeR0184.component_discriminant_divisor
#print axioms ArithmeticThetaComponentDegreeR0184.component_discriminant_divisor

-- accepted-031
example : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ) (hL : 3 ≤ L) (heven : Even L) (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space), ∀ (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (n : ℕ) (ι : Type) (C : ArithmeticThetaLineRoot.NormalFrameCover (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) ι) (t : (ArithmeticThetaComponentDegreeR0184.power k L D X x H n).presheaf.obj (Opposite.op ⊤)) (E : (ArithmeticThetaComponentDegreeR0184.Component k L D X x) →₀ ℤ), t ≠ 0 → ArithmeticThetaSectionOrder.MatchesSectionOrder (ArithmeticThetaComponentDegreeR0184.Component k L D X x) (ArithmeticThetaComponentDegreeR0184.power k L D X x H n) C t E → 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) = (n : ℤ) * (2*L : ℕ) * (Nat.card (ArithmeticThetaComponentDegreeR0184.Cusps k L D X x) : ℤ) ∧ 24 * (ArithmeticThetaCurveDegree.weightedDegree k (ArithmeticThetaComponentDegreeR0184.projection k L D X x) E) ≤ (n : ℤ) * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod L)) : ℤ) := by exact ArithmeticThetaComponentDegreeR0184.component_hodge_power_degree
#print axioms ArithmeticThetaComponentDegreeR0184.component_hodge_power_degree

-- accepted-032
example : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s → ∀ (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaCommonHalfHodgeR0185.IsCuspHalfLine k L D X x A → ∃ W : ArithmeticThetaCommonHalfHodgeR0185.Twist k L D X x A H, ArithmeticThetaCommonHalfHodgeR0185.IsTwist k L D X x s W := by exact ArithmeticThetaCommonHalfHodgeR0185.discriminant_twist_unit
#print axioms ArithmeticThetaCommonHalfHodgeR0185.discriminant_twist_unit

-- accepted-033
example : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (x : X.space) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s → ∀ (A : ArithmeticThetaCommonHalfHodgeR0185.DivisorLine (ArithmeticThetaComponentDegreeR0184.Component k L D X x)), ArithmeticThetaCommonHalfHodgeR0185.IsCuspHalfLine k L D X x A → ∀ (W : ArithmeticThetaCommonHalfHodgeR0185.Twist k L D X x A H), ArithmeticThetaCommonHalfHodgeR0185.IsTwist k L D X x s W → ∀ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X) (f : Quiver.Hom (ArithmeticThetaTateCuspsR0181.Disk k) (ArithmeticThetaComponentDegreeR0184.Component k L D X x)) (hf : CategoryTheory.CategoryStruct.comp f (ArithmeticThetaComponentDegreeR0184.inclusion k L D X x) = V.disk), ∃! v : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj W.line).presheaf.obj (Opposite.op ⊤), ArithmeticThetaCommonHalfHodgeR0185.IsTateRoot k L D X x W V f hf v := by exact ArithmeticThetaCommonHalfHodgeR0185.discriminant_tate_root
#print axioms ArithmeticThetaCommonHalfHodgeR0185.discriminant_tate_root

-- accepted-034
example : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (L : ℕ), 0 < L → 24 ∣ L → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData k L) (X : ArithmeticThetaLevelCompactificationR0179.Compactification k L D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension k L D X), ArithmeticThetaBoundaryHodgeR0182.Canonical k L H → ∀ (s : (ArithmeticThetaTensorPower.tensorPower X.space H.line 24).presheaf.obj (Opposite.op ⊤)), ArithmeticThetaComponentDegreeR0184.IsCompactD2 k L D X H s → ∀ V : ArithmeticThetaBoundaryHodgeR0182.DiskTest k L D X, ArithmeticThetaCommonHalfHodgeR0185.CommonHalfHodge k L D X H s V := by exact ArithmeticThetaCommonHalfHodgeR0185.common_half_hodge_cover
#print axioms ArithmeticThetaCommonHalfHodgeR0185.common_half_hodge_cover

-- accepted-035
example : ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ ∃ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaBoundaryHodgeR0182.Canonical ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) H ∧ ∃ (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaLatticeSectionsR0188.GeometricFamily A U H V := by exact ArithmeticThetaConservativeKernelR0189.arithmetic_geometric_family_existence
#print axioms ArithmeticThetaConservativeKernelR0189.arithmetic_geometric_family_existence

-- accepted-036
example : ∀ (n h : ℕ), 0 < n → 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∀ (U : ArithmeticThetaLatticeSectionsR0188.Indexing A), ArithmeticThetaLatticeSectionsR0188.Indexed A U → ∀ (D : ArithmeticThetaLevelCompactificationR0179.LevelData ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A))) (X : ArithmeticThetaLevelCompactificationR0179.Compactification ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D) (H : ArithmeticThetaBoundaryHodgeR0182.Extension ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X) (V : ArithmeticThetaBoundaryHodgeR0182.DiskTest ℂ (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) D X), ArithmeticThetaLatticeSectionsR0188.GeometricFamily A U H V → ∀ c : Fin h → ℂ, ArithmeticThetaSectionOrder.VanishesThrough (ArithmeticThetaComputed.thetaMap A c) (ArithmeticThetaConservativeKernelR0189.cutoff A U) → ArithmeticThetaComputed.thetaMap A c = 0 := by exact ArithmeticThetaConservativeKernelR0189.geometric_family_conservative_cutoff
#print axioms ArithmeticThetaConservativeKernelR0189.geometric_family_conservative_cutoff

-- accepted-037
example : ∀ (n h : ℕ), 0 < h → ∀ (A : ArithmeticThetaLatticeSectionsR0188.Matrices n h), (∀ i, ArithmeticThetaComputed.validGram (A i)) → ∃ B : ℕ, (if n = 0 then B = 0 else ∃ U : ArithmeticThetaLatticeSectionsR0188.Indexing A, ArithmeticThetaLatticeSectionsR0188.Indexed A U ∧ ArithmeticThetaLatticeSectionsR0188.FormalIdentity A U ∧ B = ArithmeticThetaConservativeKernelR0189.cutoff A U ∧ (B : ℚ) = (n : ℚ) * ((ArithmeticThetaCompactUnaryR0183.exponent (ArithmeticThetaLatticeSectionsR0188.commonN A) : ℕ) : ℚ)^U.count * ArithmeticThetaLevelCount.levelIndex (ArithmeticThetaCompactUnaryR0183.level (ArithmeticThetaLatticeSectionsR0188.commonN A)) / 48) ∧ (∀ B' : ℕ, B ≤ B' → LinearMap.ker (ArithmeticThetaComputed.thetaMap A) = LinearMap.ker (((ArithmeticThetaComputed.coefficientMatrix A B').map (algebraMap ℚ ℂ)).mulVecLin)) ∧ (n = 0 → ∀ c : Fin h → ℂ, ArithmeticThetaComputed.thetaMap A c = PowerSeries.C (∑ i : Fin h, c i)) := by exact ArithmeticThetaConservativeKernelR0189.conservative_matrix_kernel
#print axioms ArithmeticThetaConservativeKernelR0189.conservative_matrix_kernel

-- accepted-038
example : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [Algebra ℚ R] (W : WeierstrassCurve R) [W.IsElliptic] (G : ArithmeticThetaRelativeKatoR0169.Law R W) (hG : ArithmeticThetaRelativeKatoR0169.IsOriginLaw R W G) (L : ℕ), 0 < L → 4 ∣ L → ∀ (M : ArithmeticThetaFullLevelCoverR0175.FullLevel R W G L (CategoryTheory.CategoryStruct.id (ArithmeticThetaRelativeDiscriminantR0171.Base R))), ∃ (e : Fin 3 → R) (x y g : R), ArithmeticThetaGlobalFourTorsionR0190.RootData R W G L M e x y g := by exact ArithmeticThetaGlobalFourTorsionR0190.relative_four_torsion_root
#print axioms ArithmeticThetaGlobalFourTorsionR0190.relative_four_torsion_root

-- accepted-040
example : ∀ (k : Type) [Field k] [CharZero k] (L : ℕ), 0 < L → 4 ∣ L → ∀ (E : ArithmeticThetaTateCuspsR0181.TateLevel k L) (δ : ArithmeticThetaBoundaryHodgeR0182.CurveFrame k L), ArithmeticThetaBoundaryHodgeR0182.Normalized k L δ → ∀ a : (ArithmeticThetaRelativeDiscriminantR0171.Hodge (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k L)).presheaf.obj (Opposite.op ⊤), ArithmeticThetaGlobalFourTorsionR0190.RealizesAlpha (LaurentSeries k) (ArithmeticThetaTateCuspsR0181.TateCurve k L) E.law L E.marking a → (∃ (v : (PowerSeries k)ˣ) (j : ℕ), (j = 0 ∨ j = L/4) ∧ a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.X^j * (v : PowerSeries k))) • (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L δ)) ∧ (∀ ζ : k, IsPrimitiveRoot ζ L → ArithmeticThetaTateCuspsR0181.CanonicalMarking k L ζ E → a = ArithmeticThetaOpenHodgeR0180.scalar (LaurentSeries k) (algebraMap (PowerSeries k) (LaurentSeries k) (ArithmeticThetaGlobalFourTorsionR0190.thetaAt k L ^ 2)) • (ArithmeticThetaBoundaryHodgeR0182.hodgeGenerator k L δ)) := by exact ArithmeticThetaGlobalFourTorsionR0190.four_torsion_tate_behavior
#print axioms ArithmeticThetaGlobalFourTorsionR0190.four_torsion_tate_behavior
