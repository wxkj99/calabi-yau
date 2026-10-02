module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.GlobalSchauder.MeanZeroC0ControlBasic

/-!
# Normalized counterexamples to a mean-zero estimate

Failure of a uniform finite constant yields smooth mean-zero counterexamples normalized by their
attained supremum. The order-zero Laplacian gauges of these normalized functions tend to zero.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

private theorem eSupNormOn_smul_local {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Set X) (g : X → F) (c : ℝ) :
    CalabiYau.Schauder.eSupNormOn s (c • g) =
      (‖c‖₊ : ℝ≥0∞) * CalabiYau.Schauder.eSupNormOn s g := by
  unfold CalabiYau.Schauder.eSupNormOn
  simp_rw [Pi.smul_apply, norm_smul, ENNReal.ofReal_mul (norm_nonneg c),
    ofReal_norm, enorm_eq_nnnorm]
  rw [ENNReal.mul_iSup]

private theorem eHolderSeminormOn_smul_local {X F : Type*} [MetricSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : ℝ≥0) (s : Set X) (g : X → F) (c : ℝ) :
    CalabiYau.Schauder.eHolderSeminormOn α s (c • g) =
      (‖c‖₊ : ℝ≥0∞) * CalabiYau.Schauder.eHolderSeminormOn α s g := by
  unfold CalabiYau.Schauder.eHolderSeminormOn
  change eHolderNorm α (c • s.domRestrict g) = _
  exact eHolderNorm_smul c

private theorem eContDiffHolderGaugeOn_smul_local
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (α : ℝ≥0) (s : Set V) (g : V → F) (c : ℝ)
    (hg : ∀ x ∈ s, ContDiffAt ℝ k g x) :
    CalabiYau.Schauder.eContDiffHolderGaugeOn k α s (c • g) =
      (‖c‖₊ : ℝ≥0∞) * CalabiYau.Schauder.eContDiffHolderGaugeOn k α s g := by
  have hjet : ∀ j ≤ k, Set.EqOn
      (iteratedFDeriv ℝ j (c • g)) (c • iteratedFDeriv ℝ j g) s := by
    intro j hj x hx
    exact iteratedFDeriv_const_smul_apply ((hg x hx).of_le (by exact_mod_cast hj))
  unfold CalabiYau.Schauder.eContDiffHolderGaugeOn
  calc
    (∑ j ∈ Finset.range (k + 1),
        CalabiYau.Schauder.eSupNormOn s (iteratedFDeriv ℝ j (c • g))) +
        CalabiYau.Schauder.eHolderSeminormOn α s (iteratedFDeriv ℝ k (c • g)) =
      (∑ j ∈ Finset.range (k + 1),
        CalabiYau.Schauder.eSupNormOn s (c • iteratedFDeriv ℝ j g)) +
        CalabiYau.Schauder.eHolderSeminormOn α s (c • iteratedFDeriv ℝ k g) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        exact CalabiYau.Schauder.eSupNormOn_congr
          (hjet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      · exact CalabiYau.Schauder.eHolderSeminormOn_congr (hjet k le_rfl) α
    _ = (‖c‖₊ : ℝ≥0∞) *
        ((∑ j ∈ Finset.range (k + 1),
          CalabiYau.Schauder.eSupNormOn s (iteratedFDeriv ℝ j g)) +
          CalabiYau.Schauder.eHolderSeminormOn α s (iteratedFDeriv ℝ k g)) := by
      simp_rw [eSupNormOn_smul_local, eHolderSeminormOn_smul_local]
      rw [← Finset.mul_sum, ← mul_add]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem finiteChartHolderGauge_smul_smooth
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (f : M → ℝ) (c : ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) :
    finiteChartHolderGauge cover 0 α (c • f) =
      (‖c‖₊ : ℝ≥0∞) * finiteChartHolderGauge cover 0 α f := by
  unfold finiteChartHolderGauge
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro i
  have hfun : ((c • f) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      (cover.base i)).symm) = c •
        (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base i)).symm) := by
    funext x
    rfl
  rw [hfun, eContDiffHolderGaugeOn_smul_local]
  · intro x hx
    let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
    have hMD : ContMDiffOn I 𝓘(ℝ) ∞
        (f ∘ (extChartAt I (cover.base i)).symm) (extChartAt I (cover.base i)).target := by
      exact (contMDiffOn_univ.mpr hf).comp (contMDiffOn_extChartAt_symm (I := I) _)
        (by intro z hz; simp)
    have hCD : ContDiffOn ℝ ∞
        (f ∘ (extChartAt I (cover.base i)).symm) (extChartAt I (cover.base i)).target :=
      hMD.contDiffOn
    exact (hCD.contDiffAt
      ((isOpen_extChartAt_target (I := I) (cover.base i)).mem_nhds
        (cover.piece_in_target i hx))).of_le (by norm_num)

omit [BorelSpace M] [ConnectedSpace M] in
/-- Contradiction-sequence extraction by division by the strictly positive attained `C⁰` norm.
Finiteness of each gauge is retained before using its `toReal`. -/
theorem exists_normalized_counterexample_of_no_meanZero_laplacian_C0_control [Nonempty M]
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hNoControl : ¬ HasMeanZeroLaplacianC0Control ω₁ cover α) :
    ∃ u : ℕ → M → ℝ,
      (∀ j, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (u j)) ∧
      (∀ j, ∫ x, u j x ∂ω₁.volume = 0) ∧
      (∀ j x, |u j x| ≤ 1) ∧
      (∀ j, ∃ x, |u j x| = 1) ∧
      (∀ j, finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j)) < ⊤) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j →
        (finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j))).toReal < ε) := by
  classical
  have hbad (C : ℝ≥0) :
      ∃ f : M → ℝ,
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f ∧
        (∫ x, f x ∂ω₁.volume = 0) ∧
        finiteChartHolderGauge cover 0 α (ω₁.laplacian f) < ⊤ ∧
        ∃ x, (C : ℝ) * (finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal < |f x| := by
    have hnot : ¬ ∀ f : M → ℝ,
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
        (∫ x, f x ∂ω₁.volume = 0) →
        finiteChartHolderGauge cover 0 α (ω₁.laplacian f) < ⊤ →
        ∀ x, |f x| ≤ (C : ℝ) *
          (finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal := by
      intro h
      exact hNoControl ⟨C, h⟩
    push Not at hnot
    obtain ⟨f, hf, hm, hfin, x, hx⟩ := hnot
    exact ⟨f, hf, hm, hfin, x, hx⟩
  have hdata : ∀ j : ℕ,
      ∃ f : M → ℝ,
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f ∧
        (∫ x, f x ∂ω₁.volume = 0) ∧
        finiteChartHolderGauge cover 0 α (ω₁.laplacian f) < ⊤ ∧
        ∃ x, ((j + 1 : ℝ≥0) : ℝ) *
          (finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal < |f x| :=
    fun j ↦ hbad (j + 1)
  choose f hf hm hfin xbad hbadx using hdata
  have hmax_exists (j : ℕ) : ∃ x : M, ∀ y : M, |f j y| ≤ |f j x| := by
    obtain ⟨x, hx, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      ((continuous_abs.comp (hf j).continuous).continuousOn)
    exact ⟨x, fun y ↦ hmax (Set.mem_univ y)⟩
  choose xmax hxmax using hmax_exists
  let A (j : ℕ) : ℝ := |f j (xmax j)|
  have hA (j : ℕ) : 0 < A j := by
    have hstrict := hbadx j
    have hmaxbad := hxmax j (xbad j)
    dsimp [A]
    exact lt_of_le_of_lt (by positivity : 0 ≤ ((j + 1 : ℝ≥0) : ℝ) *
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian (f j))).toReal)
      (lt_of_lt_of_le hstrict hmaxbad)
  let u : ℕ → M → ℝ := fun j ↦ (A j)⁻¹ • f j
  have huSmooth (j : ℕ) :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (u j) := by
    dsimp [u]
    have hmul : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 * p.2) :=
      contDiff_fst.mul contDiff_snd
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun y ↦ (A j)⁻¹ * f j y)
    simpa [Function.comp_def, smul_eq_mul] using
      hmul.comp_contMDiff (contMDiff_const.prodMk_space (hf j))
  have huMean (j : ℕ) : ∫ y, u j y ∂ω₁.volume = 0 := by
    dsimp [u]
    rw [MeasureTheory.integral_const_mul]
    simp [hm j]
  have huBound (j : ℕ) (y : M) : |u j y| ≤ 1 := by
    have hAi : 0 ≤ (A j)⁻¹ := inv_nonneg.mpr (hA j).le
    change |(A j)⁻¹ * f j y| ≤ 1
    rw [abs_mul, abs_of_nonneg hAi]
    calc
      (A j)⁻¹ * |f j y| ≤ (A j)⁻¹ * A j :=
        mul_le_mul_of_nonneg_left (hxmax j y) hAi
      _ = 1 := by field_simp [ne_of_gt (hA j)]
  have huUnit (j : ℕ) : ∃ y : M, |u j y| = 1 := by
    refine ⟨xmax j, ?_⟩
    have hAi : 0 ≤ (A j)⁻¹ := inv_nonneg.mpr (hA j).le
    change |(A j)⁻¹ * f j (xmax j)| = 1
    rw [abs_mul, abs_of_nonneg hAi]
    change (A j)⁻¹ * A j = 1
    exact inv_mul_cancel₀ (ne_of_gt (hA j))
  have hLap (j : ℕ) : ω₁.laplacian (u j) =
      (A j)⁻¹ • ω₁.laplacian (f j) := by
    dsimp [u]
    exact ω₁.laplacian_smul (hf j) ((A j)⁻¹)
  have huFinite (j : ℕ) : finiteChartHolderGauge cover 0 α
      (ω₁.laplacian (u j)) < ⊤ := by
    rw [hLap j, finiteChartHolderGauge_smul_smooth cover α
      (ω₁.laplacian (f j)) ((A j)⁻¹) (ω₁.contMDiff_laplacian (hf j))]
    exact ENNReal.mul_lt_top (by simp) (hfin j)
  have hGaugeReal (j : ℕ) :
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j))).toReal =
        (A j)⁻¹ * (finiteChartHolderGauge cover 0 α
          (ω₁.laplacian (f j))).toReal := by
    rw [hLap j, finiteChartHolderGauge_smul_smooth cover α
      (ω₁.laplacian (f j)) ((A j)⁻¹) (ω₁.contMDiff_laplacian (hf j))]
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, coe_nnnorm]
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hA j).le)]
  have hsmall (j : ℕ) :
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j))).toReal <
        1 / ((j + 1 : ℝ≥0) : ℝ) := by
    rw [hGaugeReal j]
    have hstrict := hbadx j
    have hmaxbad := hxmax j (xbad j)
    have hCA : ((j + 1 : ℝ≥0) : ℝ) *
        (finiteChartHolderGauge cover 0 α (ω₁.laplacian (f j))).toReal < A j :=
      lt_of_lt_of_le hstrict hmaxbad
    have hCpos : 0 < ((j + 1 : ℝ≥0) : ℝ) := by positivity
    have hGnonneg : 0 ≤
        (finiteChartHolderGauge cover 0 α (ω₁.laplacian (f j))).toReal := by positivity
    have hdiv : (A j)⁻¹ *
        (finiteChartHolderGauge cover 0 α (ω₁.laplacian (f j))).toReal =
        (finiteChartHolderGauge cover 0 α (ω₁.laplacian (f j))).toReal / A j := by
      rw [div_eq_mul_inv]
      ring
    rw [hdiv, div_lt_iff₀ (hA j)]
    rw [show (1 / ((j + 1 : ℝ≥0) : ℝ)) * A j =
      A j / ((j + 1 : ℝ≥0) : ℝ) by ring]
    rw [lt_div_iff₀ hCpos]
    nlinarith [hCA]
  refine ⟨u, huSmooth, huMean, ?_, huUnit, huFinite, ?_⟩
  · intro j y
    exact huBound j y
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, ?_⟩
    intro j hNj
    calc
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian (u j))).toReal <
          1 / ((j + 1 : ℝ≥0) : ℝ) := hsmall j
      _ ≤ 1 / ((N + 1 : ℝ≥0) : ℝ) := by gcongr
      _ < ε := by
        have hN' : (1 / ε : ℝ) < (N : ℝ) + 1 := by
          exact lt_trans hN (by linarith)
        have hInv := (one_div_lt_one_div
          (by positivity : (0 : ℝ) < (N : ℝ) + 1)
          (one_div_pos.mpr hε)).2 hN'
        calc
          1 / ((N : ℝ) + 1) < 1 / (1 / ε) := hInv
          _ = ε := by field_simp [ne_of_gt hε]

end KahlerForm
