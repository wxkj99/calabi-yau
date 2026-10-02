module

public import CalabiYau.Geometry.Complex.Schauder
public import CalabiYau.Geometry.Complex.Schauder.RealCoordinateEquiv
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Fixed-radius local mollification

The scale in each row is independent of the point. Coefficients and solutions use the same
normalized kernel. Zero extension is used only inside a compact collar contained in the domain;
no global regularity or measurability of the supplied functions is required outside that domain.
-/

@[expose] public section

open Filter Set Matrix MeasureTheory
open scoped ContDiff NNReal Topology

namespace CalabiYau.Schauder

noncomputable section

/-- A fixed scale for each row of the local approximation. -/
def localKernelRadius (η : ℝ) (m : ℕ) : ℝ := η / (4 * ((m : ℝ) + 1))

theorem localKernelRadius_pos {η : ℝ} (hη : 0 < η) (m : ℕ) :
    0 < localKernelRadius η m := by
  unfold localKernelRadius
  positivity

/-- The canonical radial bump on the real isometric coordinate model. -/
def localKernelBump {n : ℕ} {η : ℝ} (hη : 0 < η) (m : ℕ) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin n × Fin 2)) where
  rIn := localKernelRadius η m / 2
  rOut := localKernelRadius η m
  rIn_pos := half_pos (localKernelRadius_pos hη m)
  rIn_lt_rOut := half_lt_self (localKernelRadius_pos hη m)

/-- The same nonnegative unit-mass kernel is used for every entry and every jet. -/
def localFixedKernel {n : ℕ} {η : ℝ} (hη : 0 < η) (m : ℕ) :
    EuclideanSpace ℝ (Fin n × Fin 2) → ℝ :=
  (localKernelBump hη m).normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))

theorem localFixedKernel_nonneg {n : ℕ} {η : ℝ} (hη : 0 < η) (m : ℕ)
    (w : EuclideanSpace ℝ (Fin n × Fin 2)) : 0 ≤ localFixedKernel hη m w :=
  (localKernelBump hη m).nonneg_normed w

theorem localFixedKernel_integral {n : ℕ} {η : ℝ} (hη : 0 < η) (m : ℕ) :
    (∫ w : EuclideanSpace ℝ (Fin n × Fin 2), localFixedKernel hη m w) = 1 :=
  (localKernelBump hη m).integral_normed

theorem localFixedKernel_neg {n : ℕ} {η : ℝ} (hη : 0 < η) (m : ℕ)
    (w : EuclideanSpace ℝ (Fin n × Fin 2)) :
    localFixedKernel hη m (-w) = localFixedKernel hη m w :=
  (localKernelBump hη m).normed_neg w

/-- Convolution after zero extension, evaluated in real isometric coordinates. -/
def localFixedMollify {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Set (EuclideanSpace ℂ (Fin n))) {η : ℝ} (hη : 0 < η) (m : ℕ)
    (f : EuclideanSpace ℂ (Fin n) → F) (z : EuclideanSpace ℂ (Fin n)) : F := by
  classical
  exact ∫ w : EuclideanSpace ℝ (Fin n × Fin 2), localFixedKernel hη m w •
    (if complexToRealCoordinateEquiv.symm
        (complexToRealCoordinateEquiv z - w) ∈ U then
      f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0)

/-- Entrywise coefficient mollification, with exactly the solution's kernel. -/
def localFixedCoefficientSeq {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) {η : ℝ}
    (hη : 0 < η) (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ) :
    ℕ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
  fun m z j l ↦ localFixedMollify U hη m (fun y ↦ A y j l) z

/-- The product covariance, with sign `(κf)(κg) - κ(fg)`. -/
def localMollificationCovariance {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n)))
    {η : ℝ} (hη : 0 < η) (m : ℕ)
    (f g : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n)) : ℂ :=
  localFixedMollify U hη m f z * localFixedMollify U hη m g z -
    localFixedMollify U hη m (fun y ↦ f y * g y) z

/-- Local data on nested balls. This is not the old all-open-domain approximation predicate.
There is no cap on early-row errors; only their limit is zero. -/
def LocalSchauderApproximationData {n : ℕ} (α lam K K₀ K₁ : ℝ≥0)
    (c : EuclideanSpace ℂ (Fin n)) (R S : ℝ)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ) : Prop :=
  ∃ (ε : ℕ → ℝ≥0)
    (Aseq : ℕ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (useq : ℕ → EuclideanSpace ℂ (Fin n) → ℝ),
    Tendsto ε atTop (𝓝 0) ∧
    (∀ m j l, ContDiffOn ℝ ∞ (fun z ↦ Aseq m z j l) (Metric.ball c S)) ∧
    (∀ m, ContDiffOn ℝ ∞ (useq m) (Metric.ball c S)) ∧
    (∀ m, IsUniformlyEllipticOn (Aseq m) (lam / 2) (Metric.ball c S)) ∧
    (∀ m j l, HolderBoundOn 0 α (K + 1) (Metric.ball c S) fun z ↦ Aseq m z j l) ∧
    (∀ m, HolderBoundOn 0 α (K₁ + ε m) (Metric.ball c S)
      (complexEllipticOp (Aseq m) (useq m))) ∧
    (∀ m z, z ∈ Metric.ball c S → |useq m z| ≤ K₀ + ε m) ∧
    (∀ j l, TendstoLocallyUniformlyOn (fun m z ↦ Aseq m z j l)
      (fun z ↦ A z j l) atTop (Metric.ball c R)) ∧
    (∀ j ≤ 2, TendstoLocallyUniformlyOn
      (fun m z ↦ iteratedFDeriv ℝ j (useq m) z)
      (iteratedFDeriv ℝ j u) atTop (Metric.ball c R))

end

end CalabiYau.Schauder
