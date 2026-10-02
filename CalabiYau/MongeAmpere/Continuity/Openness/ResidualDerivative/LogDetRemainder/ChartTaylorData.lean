module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetMatrixRemainder

/-!
Independent low-source artifact. This file deliberately imports neither
ResidualNormalization, ChartJets, nor ChartwiseTransfer. Public definitions
are actual evaluated objects, not aliases for private declarations.
All matrix-valued norms and HolderBoundOn use Matrix.Norms.Frobenius.
-/

@[expose] public section

set_option maxHeartbeats 800000

open scoped Manifold ContDiff NNReal Topology ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Set

namespace KahlerForm

def chartFixedEstimate (n : ℕ) : Prop :=
  ∀ (A X Y : Matrix (Fin n) (Fin n) ℂ) (μ : ℝ),
    0 < μ → A.PosDef →
    ‖A⁻¹‖ ≤ Real.sqrt (Fintype.card (Fin n) : ℝ) / μ →
    (∀ s ∈ Icc (0 : ℝ) 1, (A + (1 - s) • Y + s • X).PosDef) →
    (∀ s ∈ Icc (0 : ℝ) 1,
      ‖(A + (1 - s) • Y + s • X)⁻¹‖ ≤
        Real.sqrt (Fintype.card (Fin n) : ℝ) / μ) →
    |Matrix.logDetTaylorRemainder A X - Matrix.logDetTaylorRemainder A Y| ≤
      ((Fintype.card (Fin n) : ℝ) / μ ^ 2) * max ‖X‖ ‖Y‖ * ‖X - Y‖

def chartBaseEstimate (n : ℕ) : Prop :=
  ∀ (Mbound : ℝ≥0), 0 < Mbound →
    ∃ C : ℝ≥0, ∀ A B H : Matrix (Fin n) (Fin n) ℂ,
      (∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        (A + (1 - s) • (B - A) + t • H).PosDef) →
      (∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        ‖(A + (1 - s) • (B - A) + t • H)⁻¹‖ ≤ Mbound) →
      |Matrix.logDetTaylorRemainder A H - Matrix.logDetTaylorRemainder B H| ≤
        C * ‖A - B‖ * ‖H‖ ^ 2

structure ChartTaylorControl {n : ℕ} {U E κ : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ≥0) (S : κ → Set E)
    (A : κ → E → Matrix (Fin n) (Fin n) ℂ)
    (H : U → κ → E → Matrix (Fin n) (Fin n) ℂ) where
  baseConstant : ℝ≥0
  jetConstant : ℝ≥0
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  inverseBound : ℝ≥0
  inverseBound_pos : 0 < inverseBound
  baseHolder : ∀ i,
    @HolderBoundOn E _ _ (Matrix (Fin n) (Fin n) ℂ)
      Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
      0 α baseConstant (S i) (A i)
  jetHolder : ∀ u i,
    @HolderBoundOn E _ _ (Matrix (Fin n) (Fin n) ℂ)
      Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
      0 α (jetConstant * ‖u‖₊) (S i) (H u i)
  jet_sub : ∀ u v i z, z ∈ S i → H (u - v) i z = H u i z - H v i z
  jet_hermitian : ∀ u i z, z ∈ S i → (H u i z).IsHermitian
  smallHermitian : ∀ i x y, x ∈ S i → y ∈ S i →
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ J : Matrix (Fin n) (Fin n) ℂ,
      J.IsHermitian → ‖J‖ < epsilon →
      ((1 - s) • A i x + s • A i y + J).PosDef ∧
      ‖((1 - s) • A i x + s • A i y + J)⁻¹‖ ≤ inverseBound

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

noncomputable def actualPairwiseTaylor
    (ω₀ : KahlerForm n M) (φ : M → ℝ) {ω₁ : KahlerForm n M} {α : ℝ≥0}
    [P : ContinuityHolderPair ω₁ α] (L : P.C2 ≃L[ℝ] P.C0) (u v : P.C2) : M → ℝ :=
  fun x ↦ Real.log (ω₀.mongeAmpere (φ + P.evalC2 u) x / ω₀.mongeAmpere φ x) -
    Real.log (ω₀.mongeAmpere (φ + P.evalC2 v) x / ω₀.mongeAmpere φ x) -
    P.evalC0 (L (u - v)) x

noncomputable def chartTaylorH {ω₁ : KahlerForm n M} {α : ℝ≥0}
    (P : ContinuityHolderPair ω₁ α) (u : P.C2) (i : P.finiteChartCover.ι)
    (z : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  complexHessian ((P.evalC2 u) ∘
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm) z

end KahlerForm
