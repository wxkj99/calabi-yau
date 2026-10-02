module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.Basic
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.MatrixIncrement

/-!
# Finite-atlas gauge control of logarithmic matrix differences

The order-zero gauge is sup PLUS Hölder seminorm. Its coefficient is (3K+K²H)C, not a
maximum of the two estimates. The estimate is first finite in ENNReal, before taking toReal.
This estimate uses the checked matrix functional calculus, not a new Nemytskii-continuity oracle.
-/

public section

open scoped Manifold ContDiff NNReal ENNReal Topology ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory

namespace KahlerForm

variable {n : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

variable [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem holderOnWith_iteratedFDeriv_zero
    {s : Set E} {f : E → ℝ} {K α : ℝ≥0} (hf : HolderOnWith K α f s) :
    HolderOnWith K α (iteratedFDeriv ℝ 0 f) s := by
  let L := (continuousMultilinearCurryFin0 ℝ E ℝ).symm
  have hjet (x : E) : iteratedFDeriv ℝ 0 f x = L (f x) := by
    simp [L, iteratedFDeriv_zero_eq_comp]
  intro x hx y hy
  rw [hjet x, hjet y, L.edist_map]
  exact hf x hx y hy

/-- Finite ENNReal gauge bound from the scalar sup and Hölder estimates on every chart piece.
The two constants are added, as required by the actual gauge definition. -/
private theorem smoothCore_zeroGauge_le_sup_add_holder
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (f : SmoothChartHolderCore cover 0 α) (Csup Cholder : ℝ≥0)
    (hsup : ∀ i z, z ∈ cover.piece i →
      ‖f ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm z)‖ ≤ Csup)
    (hholder : ∀ i, HolderOnWith Cholder α
      (fun z => f ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm z)) (cover.piece i)) :
    smoothChartHolderGauge cover 0 α f ≤ (Csup : ℝ≥0∞) + Cholder := by
  change finiteChartHolderGauge cover 0 α f.smoothMap ≤ _
  unfold finiteChartHolderGauge
  apply iSup_le
  intro i
  calc
    CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α (cover.piece i)
        (f.smoothMap ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm) ≤
        (∑ _j ∈ Finset.range (0 + 1), (Csup : ℝ≥0∞)) + Cholder :=
      CalabiYau.Schauder.eContDiffHolderGaugeOn_le (fun _ => Csup) Cholder
        (fun j hj z hz => by
          have hj0 : j = 0 := by omega
          subst j
          simpa [iteratedFDeriv_zero_eq_comp] using hsup i z hz)
        (HolderWith.restrict_iff.mpr (holderOnWith_iteratedFDeriv_zero (hholder i)))
    _ = (Csup : ℝ≥0∞) + Cholder := by simp

/-- The complete order-zero gauge estimate, including both terms and an explicitly finite
upper bound. All matrix norms used by the functional-calculus wrapper are Frobenius. -/
theorem smoothCore_residual_finiteGauge_bound_of_chartMatrix_control
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (f : SmoothChartHolderCore cover 0 α)
    (A B : cover.ι → E → Matrix (Fin n) (Fin n) ℂ) (K H ε : ℝ≥0)
    (hchart : ∀ i z, z ∈ cover.piece i →
      f ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm z) =
        Real.log (RCLike.re (B i z).det) - Real.log (RCLike.re (A i z).det))
    (hsup : ∀ i z, z ∈ cover.piece i → ‖B i z - A i z‖ ≤ (ε : ℝ))
    (hdiffHolder : ∀ i, HolderOnWith (2 * ε) α
      (fun z => B i z - A i z) (cover.piece i))
    (hsegment : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∀ z ∈ cover.piece i,
        (A i z + t • (B i z - A i z)).PosDef ∧
        ‖(A i z + t • (B i z - A i z))⁻¹‖ ≤ (K : ℝ)) ∧
      HolderOnWith H α (fun z => A i z + t • (B i z - A i z)) (cover.piece i)) :
    smoothChartHolderGauge cover 0 α f ≤
      (((3 * K + K ^ 2 * H) * ε : ℝ≥0) : ℝ≥0∞) := by
  have hcontrol (i : cover.ι) := Matrix.logdet_difference_c0alpha_control
    (A i) (B i) (fun z hz t ht => (hsegment i t ht).1 z hz)
    (fun t ht => (hsegment i t ht).2) (hsup i) (hdiffHolder i)
  have hb := smoothCore_zeroGauge_le_sup_add_holder cover α f
    (K * ε) ((2 * K + K ^ 2 * H) * ε)
    (fun i z hz => by rw [hchart i z hz]; exact (hcontrol i).1 z hz)
    (fun i => by
      intro z hz w hw
      change edist (f _) (f _) ≤ _
      rw [hchart i z hz, hchart i w hw]
      exact (hcontrol i).2 z hz w hw)
  calc
    _ ≤ ((K * ε : ℝ≥0) : ℝ≥0∞) + ((2 * K + K ^ 2 * H) * ε : ℝ≥0) := hb
    _ = (((3 * K + K ^ 2 * H) * ε : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_add]
      congr 1
      ring

/-- Input norm Cauchy plus the common tail matrix controls gives Cauchy in the actual output
gauge. The finite ENNReal bound above is the intended bridge before taking toReal. -/
theorem smoothCore_residual_finiteGaugeCauchy_of_chartMatrix_control
    (cover : CompactChartCover E M) (α : ℝ≥0)
    (N₂ : SmoothChartHolderNormedData cover 2 α)
    (N₀ : SmoothChartHolderNormedData cover 0 α)
    (v : ℕ → LittleHolder cover 2 α N₂) (hv : CauchySeq v)
    (g : ℕ → SmoothChartHolderCore cover 0 α)
    (A : ℕ → cover.ι → E → Matrix (Fin n) (Fin n) ℂ)
    (N : ℕ) (K H C : ℝ≥0)
    (hchart : ∀ j k i z, z ∈ cover.piece i →
      (-g j + g k) ((extChartAt 𝓘(ℝ, E) (cover.base i)).symm z) =
        Real.log (RCLike.re (A k i z).det) - Real.log (RCLike.re (A j i z).det))
    (hsup : ∀ j k i z, z ∈ cover.piece i →
      ‖A k i z - A j i z‖ ≤ (C : ℝ) * ‖v k - v j‖)
    (hdiffHolder : ∀ j k i, HolderOnWith (2 * C * ‖v k - v j‖₊) α
      (fun z => A k i z - A j i z) (cover.piece i))
    (htail : ∀ j k, N ≤ j → N ≤ k → ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∀ z ∈ cover.piece i,
        (A j i z + t • (A k i z - A j i z)).PosDef ∧
        ‖(A j i z + t • (A k i z - A j i z))⁻¹‖ ≤ (K : ℝ)) ∧
      HolderOnWith H α
        (fun z => A j i z + t • (A k i z - A j i z)) (cover.piece i)) :
    ∀ ε : ℝ, 0 < ε → ∃ Nε : ℕ, ∀ j k,
      Nε ≤ j → Nε ≤ k →
      (smoothChartHolderGauge cover 0 α (-g j + g k)).toReal < ε := by
  let D : ℝ≥0 := (3 * K + K ^ 2 * H) * C
  have hbound (j k : ℕ) (hj : N ≤ j) (hk : N ≤ k) :
      smoothChartHolderGauge cover 0 α (-g j + g k) ≤
        ((D * ‖v k - v j‖₊ : ℝ≥0) : ℝ≥0∞) := by
    have hb := smoothCore_residual_finiteGauge_bound_of_chartMatrix_control
      cover α (-g j + g k) (A j) (A k) K H (C * ‖v k - v j‖₊)
      (hchart j k) (by simpa only [NNReal.coe_mul, coe_nnnorm] using hsup j k)
      (by simpa only [mul_assoc] using hdiffHolder j k) (htail j k hj hk)
    simpa only [D, mul_assoc] using hb
  intro ε hε
  have hD : 0 < (D : ℝ) + 1 := by positivity
  obtain ⟨Nε, hNε⟩ := Metric.cauchySeq_iff.mp hv (ε / ((D : ℝ) + 1))
    (div_pos hε hD)
  refine ⟨max Nε N, ?_⟩
  intro j k hj hk
  have hsmall : ‖v k - v j‖ < ε / ((D : ℝ) + 1) := by
    simpa only [dist_eq_norm] using hNε k (le_trans (le_max_left _ _) hk)
      j (le_trans (le_max_left _ _) hj)
  have hreal := (ENNReal.toReal_le_toReal (N₀.finiteGauge (-g j + g k)).ne
    (show ((D * ‖v k - v j‖₊ : ℝ≥0) : ℝ≥0∞) ≠ ⊤ from ENNReal.coe_ne_top)).2
    (hbound j k (le_trans (le_max_right _ _) hj) (le_trans (le_max_right _ _) hk))
  have hreal' : (smoothChartHolderGauge cover 0 α (-g j + g k)).toReal ≤
      (D : ℝ) * ‖v k - v j‖ := by
    simpa only [smoothChartHolderGauge, ENNReal.coe_toReal, NNReal.coe_mul, coe_nnnorm] using hreal
  apply lt_of_le_of_lt hreal'
  have hscaled := (lt_div_iff₀ hD).mp hsmall
  nlinarith [norm_nonneg (v k - v j)]

end KahlerForm
