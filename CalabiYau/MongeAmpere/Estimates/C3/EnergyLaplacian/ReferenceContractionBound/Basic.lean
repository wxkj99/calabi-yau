module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound
public import CalabiYau.Mathlib.LinearAlgebra.Matrix.PullbackInverse

/-!
# Basic for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

noncomputable def referenceContractionTensorFrameTransform {n : ℕ}
    (B P : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ) :
    Fin n → Fin n → Fin n → ℂ := fun i j k ↦
      ∑ a, ∑ b, ∑ c, B i a * P b j * P c k * T a b c

def referenceContractionFourSlotTransform {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (p q j k : Fin n) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    P a p * star (P b q) * P c j * star (P d k) * R a b c d

def referenceContractionFiveSlotTransform {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ)
    (X : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (s p q j k : Fin n) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    P a s * P b p * star (P c q) * P d j * star (P e k) * X a b c d e

noncomputable def referenceContractionDiagonalDrift {n : ℕ}
    (d : Fin n → ℝ) (B : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) : Fin n → Fin n → Fin n → ℂ :=
  fun i j k ↦ ∑ p, ((d p)⁻¹ : ℂ) *
    (B p j p k i +
      ∑ r, T i p r * R j p k r -
      ∑ r, T r p j * R r p k i -
      ∑ r, T r p k * R j p r i)

noncomputable def c3PullbackMetric {n : ℕ}
    (P G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  P.transpose * G * P.map star

theorem c3_pullback_inverse_entry {n : ℕ}
    (P Q G : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (q p : Fin n) :
    (c3PullbackMetric P G)⁻¹ q p =
      ∑ a, ∑ b, star (Q q a) * G⁻¹ a b * Q p b := by
  rw [c3PullbackMetric, Matrix.inv_transpose_mul_mul_map_star P Q G hQP]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Coordinate pullback of a Hermitian matrix. -/
noncomputable def linearPullbackMetric {n : ℕ} (P G : Matrix (Fin n) (Fin n) ℂ) :=
  P.transpose * G * P.map star

/-- The tensor transformation law for an upper index and two lower indices. -/
noncomputable def linearPullbackThreeTensor {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (i j k : Fin n) : ℂ :=
  ∑ a, ∑ b, ∑ c, Q i a * P b j * P c k * T a b c

/-- The five covariant slots transform by the five prescribed Jacobian factors. -/
noncomputable def linearPullbackFiveTensor {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (D : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (s p q j k : Fin n) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    P a s * P b p * star (P c q) * P d j * star (P e k) * D a b c d e

/-- Contract the perturbed and reference inverse metrics into a five-slot tensor. -/
noncomputable def linearReferenceDrift {n : ℕ} (G₀ G : Matrix (Fin n) (Fin n) ℂ)
    (D : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (i j k : Fin n) : ℂ :=
  ∑ p, ∑ q, ∑ l, G⁻¹ q p * G₀⁻¹ l i * D p j q k l

def referenceAction_tauT {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) : Fin n → Fin n → Fin n → ℂ :=
  fun i j k ↦ ∑ a, ∑ b, ∑ c, Q i a * P b j * P c k * T a b c

def referenceAction_tauU {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ)
    (U : Fin n → Fin n → Fin n → Fin n → ℂ) :
    Fin n → Fin n → Fin n → Fin n → ℂ :=
  fun i j k q ↦ ∑ a, ∑ b, ∑ c, ∑ e,
    Q i a * P b j * P c k * star (P e q) * U a b c e

def referenceAction_contract {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (U : Fin n → Fin n → Fin n → Fin n → ℂ) :
    Fin n → Fin n → Fin n → ℂ :=
  fun i j k ↦ ∑ p, ∑ q, g q p *
    ((∑ r, T i p r * U r j k q) -
     (∑ r, T r p j * U i r k q) -
     (∑ r, T r p k * U i j r q))

def referenceAction_minusJPart {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (U : Fin n → Fin n → Fin n → Fin n → ℂ) :
    Fin n → Fin n → Fin n → ℂ :=
  fun i j k ↦ ∑ p, ∑ q, g q p * ∑ r, T r p j * U i r k q

def referenceAction_minusKPart {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (U : Fin n → Fin n → Fin n → Fin n → ℂ) :
    Fin n → Fin n → Fin n → ℂ :=
  fun i j k ↦ ∑ p, ∑ q, g q p * ∑ r, T r p k * U i j r q

def referenceAction_plusPart {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (U : Fin n → Fin n → Fin n → Fin n → ℂ) :
    Fin n → Fin n → Fin n → ℂ :=
  fun i j k ↦ ∑ p, ∑ q, g q p * ∑ r, T i p r * U r j k q

end KahlerForm
