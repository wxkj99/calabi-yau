module

public import CalabiYau.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBound

/-!
# Identification of the limit of the smooth base forcing residuals

Port target: DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Analysis/Elliptic/Regularity/Iterated/BaseFChart/PolymorphicRegularity.lean`,
`smoothApproxSeqWkpM_smoothFChartResidual_limit_eq_fChartResidual_wkpM` (lines 240–1018), stated
for any sequence of smooth approximants at rate `1/(n+1)`. The order-one template is
`SmoothApproxSeq/Identification.lean` with `SmoothApproxSeq/H1ComplTendsto.lean`: chart
`H^(m+1)` closeness gives `H1Compl` convergence of `smoothToH1Compl (v n)` to `u_h`, hence weighted
`L²` convergence of the residuals to `fChartResidual u_h` and an a.e. subsequence.
-/

@[expose] public section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.Riemannian CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian Sobolev.Chart Sobolev.Euclidean
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open CalabiYau.Analysis.Laplacian.SmoothFChartResidualBilinearBound
open CalabiYau.Laplacian.MetricExtension hiding chartTargetEuclid chartTargetEuclid_isOpen
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private lemma eLpNorm_le_wkpNorm_of_any_order
    {m : ℕ} (u : EuclN → ℝ) (Ω : Set EuclN) :
    eLpNorm u 2 ((volume : Measure EuclN).restrict Ω) ≤
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2 u Ω := by
  classical
  have h_iter_eq := _root_.Sobolev.Euclidean.iterWeakPartial_zero
    (d := Module.finrank ℝ E) (p := 2) (fun i : Fin 0 => i.elim0) u Ω
  have h_zero_le := _root_.Sobolev.Euclidean.eLpNorm_iterWeakPartial_le_wkpNorm
    (d := Module.finrank ℝ E) (k := m) (p := 2) u Ω 0 (by omega)
    (fun i : Fin 0 => i.elim0)
  rw [h_iter_eq] at h_zero_le
  exact h_zero_le

private lemma eLpNorm_tendsto_zero_of_wkpNorm_tendsto_zero
    {m : ℕ} {u : ℕ → EuclN → ℝ} {F_lim : EuclN → ℝ} {Ω : Set EuclN}
    (h_tendsto : Tendsto (fun n =>
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2 (fun y => u n y - F_lim y) Ω)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun y => u n y - F_lim y) 2
      ((volume : Measure EuclN).restrict Ω)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ => (0 : ℝ≥0∞)) (h := fun n =>
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2 (fun y => u n y - F_lim y) Ω)
    tendsto_const_nhds h_tendsto (fun _ => zero_le) ?_
  intro n
  exact eLpNorm_le_wkpNorm_of_any_order (fun y => u n y - F_lim y) Ω

private lemma volume_restrict_target_absolutelyContinuous_weighted
    (g : SmoothRiemannianMetric I M) (α : M) :
    (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  intro A hA
  have hT : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  unfold chartPulledWeightedMeasure at hA
  rw [show ((volume : Measure EuclN).withDensity
      (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
      (chartTargetEuclid (I := I) (M := M) α) =
    ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    from MeasureTheory.restrict_withDensity hT _] at hA
  rw [MeasureTheory.withDensity_apply_eq_zero'
    (μ := (volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α))
    (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable hT))] at hA
  rw [Measure.restrict_apply' hT]
  rw [Measure.restrict_apply' hT] at hA
  refine MeasureTheory.measure_mono_null ?_ hA
  intro y ⟨hy_A, hy_target⟩
  refine ⟨⟨?_, hy_A⟩, hy_target⟩
  have hpos : 0 < densityOnEuclid (I := I) g α y :=
    densityOnEuclid_pos (I := I) g α hy_target
  exact (ENNReal.ofReal_pos.mpr hpos).ne'

private lemma residual_aestronglyMeasurable_volume
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (μ : Measure EuclN) :
    AEStronglyMeasurable
      (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
        (I := I) (M := M) g α v) μ := by
  unfold CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
    fChartResidual
  exact (Lp.stronglyMeasurable _).aestronglyMeasurable.mono_measure (le_refl _)

private lemma fChartResidual_aestronglyMeasurable_weighted
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl (I := I) (M := M) g)
    (μ : Measure EuclN) :
    AEStronglyMeasurable
      (fChartResidual (I := I) (M := M) g α u_h) μ := by
  unfold fChartResidual
  exact (Lp.stronglyMeasurable _).aestronglyMeasurable.mono_measure (le_refl _)

private lemma wkpNorm_succ_ge
    (d : ℕ) (k : ℕ) (p : ℝ≥0∞)
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) :
    _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) k p u Ω ≤
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) (k + 1) p u Ω := by
  classical
  unfold _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro _ _ _; exact zero_le

private lemma wkpNormChart_le_succ
    (m : ℕ) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) 1 2 u ≤
      wkpNormChart (I := I) (M := M) (m + 1) 2 u := by
  classical
  induction m with
  | zero => exact le_refl _
  | succ k ih =>
      have hstep : wkpNormChart (I := I) (M := M) (k + 1) 2 u ≤
          wkpNormChart (I := I) (M := M) (k + 1 + 1) 2 u := by
        classical
        unfold wkpNormChart
        refine ENNReal.tsum_le_tsum (fun α => ?_)
        exact wkpNorm_succ_ge (d := Module.finrank ℝ E) (k + 1) 2 _ _
      exact ih.trans hstep

private lemma eLpNorm_smoothScalar_le_const_mul_wkpNormChart_one
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SmoothScalar g,
      eLpNorm f.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C * wkpNormChart (I := I) (M := M) 1 2 f.toFun := by
  obtain ⟨C, hC_nn, hbound⟩ :=
    _root_.Sobolev.Equivalence.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g (p := 2) (by norm_num) (by norm_num)
  exact ⟨C, hC_nn, fun f => hbound f.smooth.continuous.measurable⟩

private lemma eLpNorm_gNormGrad_smoothScalar_le_const_mul_wkpNormChart_one
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SmoothScalar g,
      eLpNorm (fun x : M => Real.sqrt
        (g.inner x (gradFun (I := I) g f.toFun x)
          (gradFun (I := I) g f.toFun x))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C * wkpNormChart (I := I) (M := M) 1 2 f.toFun := by
  obtain ⟨C, hC_nn, hbound⟩ :=
    _root_.Sobolev.Equivalence.eLpNorm_g_norm_gradFun_le_const_mul_wkpNormChart_smooth_uniform
      (I := I) (M := M) g (p := 2) (by norm_num) (by norm_num)
  exact ⟨C, hC_nn, fun f => hbound f.smooth⟩

private lemma eLpNorm_sq_toReal_eq_integral_sq
    (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    (eLpNorm f.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ^ 2 =
      ∫ x, f.toFun x * f.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h := f.norm_smoothToLp_sq
  have h_norm : ‖smoothToLpLin (I := I) (M := M) g f‖ =
      (eLpNorm f.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g)).toReal := by
    change ‖f.memLp_two.toLp f.toFun‖ = _
    exact MeasureTheory.Lp.norm_toLp _ _
  rw [← h_norm]
  exact h

private lemma eLpNorm_gNormGrad_sq_toReal_eq_integral_inner_grad
    (g : SmoothRiemannianMetric I M) (f : SmoothScalar g) :
    (eLpNorm (fun x : M => Real.sqrt
      (g.inner x (gradFun (I := I) g f.toFun x) (gradFun (I := I) g f.toFun x))) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ^ 2 =
      ∫ x, g.inner x
        ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have hfinite : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set fMap : C^∞⟮I, M; ℝ⟯ := ⟨f.toFun, f.smooth⟩ with hfMap
  set ψ : M → ℝ := fun x : M => Real.sqrt
    (g.inner x (gradFun (I := I) g f.toFun x)
      (gradFun (I := I) g f.toFun x)) with hψ_def
  have hψ_sq : ∀ x, ψ x ^ 2 = g.inner x
      ((gradG (I := I) g fMap : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g fMap : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    dsimp [ψ]
    rw [sq]
    rw [Real.mul_self_sqrt (SmoothRiemannianMetric_inner_self_nonneg g x _)]
    congr 1
  have hψ_cont : Continuous ψ := by
    have h_inner_cont : Continuous (fun x : M =>
        g.inner x (gradFun (I := I) g f.toFun x)
          (gradFun (I := I) g f.toFun x)) := by
      have h1 : (fun x : M =>
          g.inner x (gradFun (I := I) g f.toFun x)
            (gradFun (I := I) g f.toFun x)) = (fun x : M =>
          g.inner x ((gradG (I := I) g fMap :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g fMap :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) := by
        funext x
        rw [grad_g_apply]
        congr 1
      rw [h1]
      exact f.continuous_inner_grad f
    simpa only [ψ] using h_inner_cont.sqrt
  have hψ_mem : MemLp ψ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hψ_cont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let ψLp := hψ_mem.toLp ψ
  have hinner := real_inner_self_eq_norm_sq ψLp
  rw [L2.inner_def (𝕜 := ℝ)] at hinner
  have hnorm : ‖ψLp‖ = (eLpNorm ψ 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal :=
    MeasureTheory.Lp.norm_toLp _ _
  rw [hnorm] at hinner
  have hae : (fun x : M => @inner ℝ _ _ (ψLp x) (ψLp x)) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g] (fun x => ψ x * ψ x) := by
    filter_upwards [MemLp.coeFn_toLp hψ_mem] with x hx
    rw [hx]
    rfl
  rw [integral_congr_ae hae] at hinner
  have heq : (fun x : M => ψ x * ψ x) = (fun x => g.inner x
      ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g ⟨f.toFun, f.smooth⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) := by
    funext x
    rw [← sq]
    exact hψ_sq x
  rw [heq] at hinner
  exact hinner.symm

private lemma norm_smoothScalar_le_const_mul_wkpNormChart_one
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SmoothScalar g,
      wkpNormChart (I := I) (M := M) 1 2 f.toFun ≠ ⊤ →
      ‖f‖ ≤ C * (wkpNormChart (I := I) (M := M) 1 2 f.toFun).toReal := by
  obtain ⟨C₀, hC₀_nn, hC₀_bnd⟩ :=
    eLpNorm_smoothScalar_le_const_mul_wkpNormChart_one (I := I) (M := M) g
  obtain ⟨C₁, hC₁_nn, hC₁_bnd⟩ :=
    eLpNorm_gNormGrad_smoothScalar_le_const_mul_wkpNormChart_one (I := I) (M := M) g
  refine ⟨C₀ + C₁, add_nonneg hC₀_nn hC₁_nn, ?_⟩
  intro f hfinite
  have hsq := f.norm_sq_eq_inner_self
  let L := (eLpNorm f.toFun 2 (riemannianVolumeMeasure (I := I) (M := M) g)).toReal
  let G := (eLpNorm (fun x : M => Real.sqrt
    (g.inner x (gradFun (I := I) g f.toFun x) (gradFun (I := I) g f.toFun x))) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal
  have hLnn : 0 ≤ L := ENNReal.toReal_nonneg
  have hGnn : 0 ≤ G := ENNReal.toReal_nonneg
  have hnormsq : ‖f‖ ^ 2 = L ^ 2 + G ^ 2 := by
    rw [hsq]
    unfold smoothScalarH1Inner
    rw [← eLpNorm_sq_toReal_eq_integral_sq, ← eLpNorm_gNormGrad_sq_toReal_eq_integral_inner_grad]
  have hnormle : ‖f‖ ≤ L + G := by
    apply abs_le_of_sq_le_sq' _ (add_nonneg hLnn hGnn) |>.2
    rw [hnormsq]
    nlinarith
  let N := (wkpNormChart (I := I) (M := M) 1 2 f.toFun).toReal
  have hNnn : 0 ≤ N := ENNReal.toReal_nonneg
  have hLle : L ≤ C₀ * N := by
    have h := hC₀_bnd f
    have h' : L ≤ (ENNReal.ofReal C₀ * wkpNormChart (I := I) (M := M) 1 2 f.toFun).toReal := by
      dsimp [L]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₀_nn] at h'
    exact h'
  have hGle : G ≤ C₁ * N := by
    have h := hC₁_bnd f
    have h' : G ≤ (ENNReal.ofReal C₁ * wkpNormChart (I := I) (M := M) 1 2 f.toFun).toReal := by
      dsimp [G]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₁_nn] at h'
    exact h'
  calc ‖f‖ ≤ L + G := hnormle
    _ ≤ C₀ * N + C₁ * N := add_le_add hLle hGle
    _ = (C₀ + C₁) * N := by dsimp [N]; ring

private theorem eLpNorm_approx_error_tendsto_zero
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (v : ℕ → SmoothScalar g)
    (hv : ∀ n, wkpNormChart (I := I) (M := M) (m + 1) 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (v n).toFun x) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => eLpNorm
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (v n).toFun x) 2 (riemannianVolumeMeasure (I := I) (M := M) g))
      atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC, hCbound⟩ :=
    _root_.Sobolev.Equivalence.eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g (p := 2) (by norm_num) (by norm_num)
  let u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
  have hu_meas : Measurable u := by
    exact (Lp.stronglyMeasurable _).measurable
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp hnat using 1 <;> ext n <;> simp
  have hreal : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hinv
  have hofreal : Tendsto (fun n : ℕ => ENNReal.ofReal
      (C * (1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
    convert (ENNReal.continuous_ofReal.tendsto 0).comp hreal using 1 <;>
      ext n <;> simp
  have hbound : ∀ n, eLpNorm (fun x => u x - (v n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal (C * ((1 : ℝ) / ((n : ℝ) + 1))) := by
    intro n
    have hchart :=
      (wkpNormChart_le_succ (I := I) (M := M)
        m (fun x => u x - (v n).toFun x)).trans
        (by simpa only [u] using hv n)
    have hle := hCbound (hu_meas.sub (v n).smooth.continuous.measurable)
    calc
      eLpNorm (fun x => u x - (v n).toFun x) 2
          (riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ENNReal.ofReal C * wkpNormChart (I := I) (M := M) 1 2
            (fun x => u x - (v n).toFun x) := hle
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
        gcongr
      _ = ENNReal.ofReal (C * (1 / ((n : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_mul hC]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hofreal
    (fun n => (zero_le : (0 : ℝ≥0∞) ≤ eLpNorm
      (fun x => u x - (v n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g))) (fun n => hbound n)

private theorem smoothToLp_approx_tendsto
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (v : ℕ → SmoothScalar g)
    (hv : ∀ n, wkpNormChart (I := I) (M := M) (m + 1) 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
        (v n).toFun x) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => smoothToLp (I := I) (M := M) g (v n)) atTop
      (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) := by
  classical
  have h_eLpNorm_tendsto := eLpNorm_approx_error_tendsto_zero (I := I) (M := M)
    g m v hv
  rw [ENNReal.tendsto_atTop_zero] at h_eLpNorm_tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε_pos
  have hε_half_pos : 0 < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := h_eLpNorm_tendsto (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.mpr hε_half_pos)
  refine ⟨N, ?_⟩
  intro n hn
  set u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
  have h_eLpNorm_le := hN n hn
  rw [dist_eq_norm]
  have h_norm_sub_comm :
      ‖smoothToLp (I := I) (M := M) g (v n) -
        H1ComplToLp (I := I) (M := M) g u_h‖ =
      ‖H1ComplToLp (I := I) (M := M) g u_h -
        smoothToLp (I := I) (M := M) g (v n)‖ := norm_sub_rev _ _
  rw [h_norm_sub_comm]
  set Δ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    H1ComplToLp (I := I) (M := M) g u_h - smoothToLp (I := I) (M := M) g (v n)
  have h_Δ_coe_ae : (Δ : M → ℝ) =ᵐ[
      riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x => u x - (v n).toFun x) := by
    have h_sub := MeasureTheory.Lp.coeFn_sub
      (H1ComplToLp (I := I) (M := M) g u_h)
      (smoothToLp (I := I) (M := M) g (v n))
    have h_smoothToLp_coe :
        (smoothToLp (I := I) (M := M) g (v n) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
            riemannianVolumeMeasure (I := I) (M := M) g] (v n).toFun :=
      MemLp.coeFn_toLp (v n).memLp_two
    filter_upwards [h_sub, h_smoothToLp_coe] with x hx_sub hx_smoothToLp
    rw [hx_sub, Pi.sub_apply, hx_smoothToLp]
  have h_norm_Δ : ‖Δ‖ = (eLpNorm (fun x => u x - (v n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal := by
    rw [Lp.norm_def]
    rw [eLpNorm_congr_ae h_Δ_coe_ae]
  rw [h_norm_Δ]
  have h_eLpNorm_finite : eLpNorm (fun x => u x - (v n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) ≠ ⊤ := by
    refine ne_of_lt ?_
    exact lt_of_le_of_lt h_eLpNorm_le ENNReal.ofReal_lt_top
  have h_toReal_le : (eLpNorm (fun x => u x - (v n).toFun x) 2
      (riemannianVolumeMeasure (I := I) (M := M) g)).toReal ≤ ε / 2 := by
    have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_eLpNorm_le
    rw [ENNReal.toReal_ofReal hε_half_pos.le] at hmono
    exact hmono
  linarith

private lemma wkpNormChart_one_two_smoothScalar_diff_ne_top
    (g : SmoothRiemannianMetric I M)
    (v w : SmoothScalar g) :
    wkpNormChart (I := I) (M := M) 1 2
        (fun x : M => v.toFun x - w.toFun x) ≠ ⊤ := by
  classical
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hv_mem : MemWkpChart (I := I) (M := M) 1 2 v.toFun :=
    _root_.CalabiYau.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) hp_one 1 v.smooth
  have hw_mem : MemWkpChart (I := I) (M := M) 1 2 w.toFun :=
    _root_.CalabiYau.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) hp_one 1 w.smooth
  have h_diff_mem : MemWkpChart (I := I) (M := M) 1 2
      (fun x : M => v.toFun x - w.toFun x) :=
    _root_.Sobolev.Chart.MemWkpChart_sub
      (I := I) (M := M) hp_one hv_mem hw_mem
  exact (wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp_one h_diff_mem).ne

private theorem smoothToH1Compl_arbitrary_approx_cauchy
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) (m + 1) 2 u)
    (v : ℕ → SmoothScalar g)
    (hv : ∀ n, wkpNormChart (I := I) (M := M) (m + 1) 2
      (fun x => u x - (v n).toFun x) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    CauchySeq (fun n => smoothToH1Compl (I := I) (M := M) g (v n)) := by
  classical
  obtain ⟨C, hC_nn, hC_bnd⟩ :=
    norm_smoothScalar_le_const_mul_wkpNormChart_one (I := I) (M := M) g
  rw [Metric.cauchySeq_iff]
  intro ε hε_pos
  let Cp1 : ℝ := C + 1
  have hCp1_pos : 0 < Cp1 := by dsimp [Cp1]; linarith
  let ε' : ℝ := ε / (2 * Cp1)
  have hε'_pos : 0 < ε' := by dsimp [ε']; positivity
  obtain ⟨N0, hN0_real⟩ := exists_nat_gt (1 / ε' - 1)
  have hN1_pos : (0 : ℝ) < (N0 : ℝ) + 1 := by
    have hpos : 0 < 1 / ε' := by positivity
    linarith
  have hN0_inv_le : (1 : ℝ) / ((N0 : ℝ) + 1) ≤ ε' := by
    rw [div_le_iff₀ hN1_pos]
    have h1 : (1 : ℝ) = ε' * (1 / ε') := by
      rw [mul_one_div, div_self hε'_pos.ne']
    rw [h1]
    apply mul_le_mul_of_nonneg_left _ hε'_pos.le
    linarith
  refine ⟨N0, ?_⟩
  intro a ha b hb
  rw [dist_eq_norm]
  let va : SmoothScalar g := v a
  let vb : SmoothScalar g := v b
  let vdiff : SmoothScalar g := va - vb
  have hvdiff_toFun : vdiff.toFun = fun x => va.toFun x - vb.toFun x := rfl
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h_smooth_va : MemWkpChart (I := I) (M := M) (m + 1) 2 va.toFun :=
    CalabiYau.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) hp_one (m + 1) va.smooth
  have h_smooth_vb : MemWkpChart (I := I) (M := M) (m + 1) 2 vb.toFun :=
    CalabiYau.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) hp_one (m + 1) vb.smooth
  have h_err_va : MemWkpChart (I := I) (M := M) (m + 1) 2
      (fun x => u x - va.toFun x) :=
    _root_.Sobolev.Chart.MemWkpChart_sub (I := I) hp_one hu h_smooth_va
  have h_err_vb : MemWkpChart (I := I) (M := M) (m + 1) 2
      (fun x => u x - vb.toFun x) :=
    _root_.Sobolev.Chart.MemWkpChart_sub (I := I) hp_one hu h_smooth_vb
  have h_decomp : (fun x => va.toFun x - vb.toFun x) =
      (fun x => (u x - vb.toFun x) + (-1 : ℝ) * (u x - va.toFun x)) := by
    funext x; ring
  have h_neg_norm : wkpNormChart (I := I) (M := M) (m + 1) 2
      (fun x => (-1 : ℝ) * (u x - va.toFun x)) =
      wkpNormChart (I := I) (M := M) (m + 1) 2 (fun x => u x - va.toFun x) := by
    rw [_root_.Sobolev.Chart.wkpNormChart_const_smul (I := I) hp_one (-1 : ℝ) h_err_va]
    simp [enorm]
  have h_neg_mem : MemWkpChart (I := I) (M := M) (m + 1) 2
      (fun x => (-1 : ℝ) * (u x - va.toFun x)) := by
    have heq : (fun x : M => (-1 : ℝ) * (u x - va.toFun x)) =
        (fun x => -(u x - va.toFun x)) := by funext x; ring
    rw [heq]
    exact _root_.Sobolev.Chart.MemWkpChart_neg (I := I) hp_one h_err_va
  have hadd := _root_.Sobolev.Chart.wkpNormChart_add_le (I := I)
    (k := m + 1) (p := 2) hp_one h_err_vb h_neg_mem
  have hdiff_bound : wkpNormChart (I := I) (M := M) (m + 1) 2 vdiff.toFun ≤
      ENNReal.ofReal (1 / ((a : ℝ) + 1)) + ENNReal.ofReal (1 / ((b : ℝ) + 1)) := by
    rw [hvdiff_toFun]
    change wkpNormChart (I := I) (M := M) (m + 1) 2
      (fun x => va.toFun x - vb.toFun x) ≤ _
    rw [h_decomp]
    calc
      wkpNormChart (I := I) (M := M) (m + 1) 2
          (fun x => (u x - vb.toFun x) + (-1 : ℝ) * (u x - va.toFun x))
        ≤ wkpNormChart (I := I) (M := M) (m + 1) 2 (fun x => u x - vb.toFun x) +
            wkpNormChart (I := I) (M := M) (m + 1) 2 (fun x => (-1 : ℝ) * (u x - va.toFun x)) := hadd
      _ = _ := by rw [h_neg_norm]
      _ ≤ _ := by simpa [add_comm] using add_le_add (hv b) (hv a)
  have hdiff_finite : wkpNormChart (I := I) (M := M) 1 2 vdiff.toFun ≠ ⊤ := by
    rw [hvdiff_toFun]
    exact wkpNormChart_one_two_smoothScalar_diff_ne_top (I := I) (M := M) g va vb
  have h_norm_bd : ‖vdiff‖ ≤ C *
      (wkpNormChart (I := I) (M := M) 1 2 vdiff.toFun).toReal := hC_bnd vdiff hdiff_finite
  have hdiff1_bound : wkpNormChart (I := I) (M := M) 1 2 vdiff.toFun ≤
      ENNReal.ofReal (1 / ((a : ℝ) + 1)) + ENNReal.ofReal (1 / ((b : ℝ) + 1)) :=
    (wkpNormChart_le_succ (I := I) (M := M) m vdiff.toFun).trans hdiff_bound
  have hsum_finite : ENNReal.ofReal (1 / ((a : ℝ) + 1)) +
      ENNReal.ofReal (1 / ((b : ℝ) + 1)) ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have ha_nn : 0 ≤ (1 : ℝ) / ((a : ℝ) + 1) := by positivity
  have hb_nn : 0 ≤ (1 : ℝ) / ((b : ℝ) + 1) := by positivity
  have hsum_toReal : (ENNReal.ofReal (1 / ((a : ℝ) + 1)) +
      ENNReal.ofReal (1 / ((b : ℝ) + 1))).toReal =
      1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) := by
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal ha_nn, ENNReal.toReal_ofReal hb_nn]
  have hdiff_toReal : (wkpNormChart (I := I) (M := M) 1 2 vdiff.toFun).toReal ≤
      1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) := by
    have h := ENNReal.toReal_mono hsum_finite hdiff1_bound
    rwa [hsum_toReal] at h
  have hN0a : (N0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hN0b : (N0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hN0inv_a : (1 : ℝ) / ((a : ℝ) + 1) ≤ 1 / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos; linarith
  have hN0inv_b : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((N0 : ℝ) + 1) := by
    apply div_le_div_of_nonneg_left zero_le_one hN1_pos; linarith
  have hsum_le : 1 / ((a : ℝ) + 1) + 1 / ((b : ℝ) + 1) ≤
      2 * (1 / ((N0 : ℝ) + 1)) := by linarith
  have hdiff2 : (wkpNormChart (I := I) (M := M) 1 2 vdiff.toFun).toReal ≤
      2 * (1 / ((N0 : ℝ) + 1)) := hdiff_toReal.trans hsum_le
  have hmult : C * (wkpNormChart (I := I) (M := M) 1 2 vdiff.toFun).toReal ≤
      C * (2 * (1 / ((N0 : ℝ) + 1))) := mul_le_mul_of_nonneg_left hdiff2 hC_nn
  have hN0_eps : 2 * (1 / ((N0 : ℝ) + 1)) ≤ 2 * ε' :=
    mul_le_mul_of_nonneg_left hN0_inv_le (by norm_num)
  have hmult_eps : C * (wkpNormChart (I := I) (M := M) 1 2 vdiff.toFun).toReal ≤
      C * (2 * ε') := hmult.trans (mul_le_mul_of_nonneg_left hN0_eps hC_nn)
  have hfinal_le : C * (2 * ε') < ε := by
    dsimp [ε', Cp1]
    have hcalc : C * (2 * (ε / (2 * (C + 1)))) = C * ε / (C + 1) := by field_simp
    rw [hcalc, div_lt_iff₀ (by linarith : 0 < C + 1)]
    nlinarith [hC_nn]
  have hdist : dist (smoothToH1Compl (I := I) (M := M) g (v a))
      (smoothToH1Compl (I := I) (M := M) g (v b)) < ε := by
    rw [dist_eq_norm]
    change ‖smoothToH1Compl (I := I) (M := M) g (v a) -
      smoothToH1Compl (I := I) (M := M) g (v b)‖ < ε
    calc
      ‖smoothToH1Compl (I := I) (M := M) g (v a) -
          smoothToH1Compl (I := I) (M := M) g (v b)‖ =
          ‖smoothToH1Compl (I := I) (M := M) g vdiff‖ := by
        congr 1
        change smoothToH1Compl (I := I) (M := M) g (v a) -
          smoothToH1Compl (I := I) (M := M) g (v b) =
          smoothToH1Compl (I := I) (M := M) g (v a - v b)
        exact (map_sub (smoothToH1Compl (I := I) (M := M) g) (v a) (v b)).symm
      _ = ‖vdiff‖ := by
        simp [smoothToH1Compl_apply]
      _ ≤ C * (wkpNormChart (I := I) (M := M) 1 2 vdiff.toFun).toReal := h_norm_bd
      _ < ε := lt_of_le_of_lt hmult_eps hfinal_le
  simpa only [dist_eq_norm] using hdist

private lemma smoothScalarH1Inner_eq_lpInner_oneSubLap_right
    (g : SmoothRiemannianMetric I M) (v f : SmoothScalar g) :
    smoothScalarH1Inner (I := I) v f =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        smoothToLp (I := I) (M := M) g v⟫_ℝ := by
  rw [smoothScalarH1Inner_symm]
  exact smoothScalarH1Inner_eq_lpInner_oneSubLap f v

private lemma inner_h1Compl_smoothToH1Compl_eq_lpInner
    (g : SmoothRiemannianMetric I M)
    (u_h : H1Compl (I := I) (M := M) g) (f : SmoothScalar g) :
    ⟪u_h, smoothToH1Compl (I := I) (M := M) g f⟫_ℝ =
      ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
        H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ := by
  rw [real_inner_comm]
  have h_bilin :
      H1ComplBilin (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g f) u_h =
        lpFunctionalCLM (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g f.oneSubLapClassical) u_h :=
    smoothToH1Compl_bilin_eq_lpFunctional f u_h
  have h_lhs : ⟪smoothToH1Compl (I := I) (M := M) g f, u_h⟫_ℝ =
      H1ComplBilin (I := I) (M := M) g
        (smoothToH1Compl (I := I) (M := M) g f) u_h := rfl
  rw [h_lhs, h_bilin, lpFunctionalCLM_apply]
  exact real_inner_comm _ _

private theorem bridge
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu : MemWkpChart (I := I) (M := M) (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h : Lp ℝ 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (v : ℕ → SmoothScalar g)
    (hv : ∀ n, wkpNormChart (I := I) (M := M) (m + 1) 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h : Lp ℝ 2
        (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x - (v n).toFun x) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n)) atTop (𝓝 u_h) := by
  classical
  let u : M → ℝ := ((H1ComplToLp (I := I) (M := M) g u_h :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)
  have hu_chart : MemWkpChart (I := I) (M := M) (m + 1) 2 u := by
    simpa only [u] using hu
  have hv' : ∀ n, wkpNormChart (I := I) (M := M) (m + 1) 2
      (fun x => u x - (v n).toFun x) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    simpa only [u] using hv n
  have h_cauchy := smoothToH1Compl_arbitrary_approx_cauchy
    (I := I) (M := M) g m hu_chart v hv'
  obtain ⟨u_star, h_tendsto_star⟩ := cauchySeq_tendsto_of_complete h_cauchy
  have h_lp_tendsto := smoothToLp_approx_tendsto (I := I) (M := M) g m v hv'
  suffices h_eq : u_star = u_h by
    simpa only [h_eq] using h_tendsto_star
  apply ext_inner_left ℝ
  intro w
  have h_left_cont : Continuous (fun z : H1Compl (I := I) (M := M) g =>
      ⟪z, u_star⟫_ℝ) := ((innerSL ℝ (E := H1Compl g)).flip u_star).continuous
  have h_right_cont : Continuous (fun z : H1Compl (I := I) (M := M) g =>
      ⟪z, u_h⟫_ℝ) := ((innerSL ℝ (E := H1Compl g)).flip u_h).continuous
  have h_pairings :
      (fun z => ⟪z, u_star⟫_ℝ) ∘ smoothToH1Compl (I := I) (M := M) g =
      (fun z => ⟪z, u_h⟫_ℝ) ∘ smoothToH1Compl (I := I) (M := M) g := by
    funext f
    have h_seq_star : Tendsto (fun j =>
        ⟪smoothToH1Compl (I := I) (M := M) g f,
          smoothToH1Compl (I := I) (M := M) g (v j)⟫_ℝ) atTop
        (𝓝 ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ) :=
      Tendsto.inner tendsto_const_nhds h_tendsto_star
    have h_seq_lp : Tendsto (fun j =>
        ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          smoothToLp (I := I) (M := M) g (v j)⟫_ℝ) atTop
        (𝓝 ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ) :=
      Tendsto.inner tendsto_const_nhds h_lp_tendsto
    have h_seq_eq : ∀ j,
        ⟪smoothToH1Compl (I := I) (M := M) g f,
          smoothToH1Compl (I := I) (M := M) g (v j)⟫_ℝ =
        ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          smoothToLp (I := I) (M := M) g (v j)⟫_ℝ := by
      intro j
      rw [inner_smoothToH1Compl_smoothToH1Compl, smoothScalarH1Inner_symm]
      exact smoothScalarH1Inner_eq_lpInner_oneSubLap_right (I := I) (M := M) g
        (v j) f
    have h_target :
        ⟪smoothToH1Compl (I := I) (M := M) g f, u_h⟫_ℝ =
        ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
          H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ := by
      rw [real_inner_comm]
      exact inner_h1Compl_smoothToH1Compl_eq_lpInner (I := I) (M := M) g u_h f
    have h_lp_target := h_seq_lp.congr'
      (Filter.Eventually.of_forall fun j => (h_seq_eq j).symm)
    calc
      ⟪smoothToH1Compl (I := I) (M := M) g f, u_star⟫_ℝ =
          ⟪smoothToLp (I := I) (M := M) g f.oneSubLapClassical,
            H1ComplToLp (I := I) (M := M) g u_h⟫_ℝ :=
        tendsto_nhds_unique h_seq_star h_lp_target
      _ = ⟪smoothToH1Compl (I := I) (M := M) g f, u_h⟫_ℝ := h_target.symm
  exact congrFun ((denseRange_smoothToH1Compl (I := I) (M := M) g).equalizer
    h_left_cont h_right_cont h_pairings) w

set_option maxHeartbeats 600000 in
private theorem limit_identification_of_h1_tendsto
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu : MemWkpChart (I := I) (M := M) (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h : M → ℝ)))
    (v : ℕ → SmoothScalar g)
    (hv : ∀ n, wkpNormChart (I := I) (M := M) (m + 1) 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h : M → ℝ) x - (v n).toFun x)) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)))
    (hH1 : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h))
    (F_lim : EuclN → ℝ)
    (hF : MemWkp (d := Module.finrank ℝ E) m 2 F_lim
      (chartTargetEuclid (I := I) (M := M) α))
    (hF_lim : Tendsto (fun n =>
      _root_.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) m 2
        (fun y =>
          CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
            (I := I) (M := M) g α (v n) y - F_lim y)
        (chartTargetEuclid (I := I) (M := M) α)) atTop (𝓝 0)) :
    F_lim =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)]
      fChartResidual (I := I) (M := M) g α u_h := by
  classical
  let Ω := chartTargetEuclid (I := I) (M := M) α
  let F : ℕ → EuclN → ℝ := fun n =>
    CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
      (I := I) (M := M) g α (v n)
  have h_eLp_volume : Tendsto (fun n => eLpNorm (fun y => F n y - F_lim y) 2
      ((volume : Measure EuclN).restrict Ω)) atTop (𝓝 0) :=
    eLpNorm_tendsto_zero_of_wkpNorm_tendsto_zero (m := m) (u := F)
      (F_lim := F_lim) (Ω := Ω) (by simpa [F, Ω] using hF_lim)
  have hF_lim_aesm : AEStronglyMeasurable F_lim
      ((volume : Measure EuclN).restrict Ω) := hF.memLp.aestronglyMeasurable
  have hF_seq_aesm : ∀ n, AEStronglyMeasurable (F n)
      ((volume : Measure EuclN).restrict Ω) := by
    intro n
    exact residual_aestronglyMeasurable_volume (I := I) (M := M) g α (v n) _
  have h_vol_measure : TendstoInMeasure ((volume : Measure EuclN).restrict Ω)
      F atTop F_lim :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (μ := (volume : Measure EuclN).restrict Ω) (p := 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) hF_seq_aesm hF_lim_aesm h_eLp_volume
  obtain ⟨σ, hσ_strict, hσ_ae⟩ := h_vol_measure.exists_seq_tendsto_ae
  have h_weighted : Tendsto (fun n => eLpNorm
      (fun y => F n y - fChartResidual (I := I) (M := M) g α u_h y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict Ω)) atTop (𝓝 0) :=
    CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual_tendsto_fChartResidual_lp_weighted
      (I := I) (M := M) g α v hH1
  have h_f_ae : AEStronglyMeasurable
      (fChartResidual (I := I) (M := M) g α u_h)
      ((chartPulledWeightedMeasure (I := I) g α).restrict Ω) :=
    fChartResidual_aestronglyMeasurable_weighted (I := I) (M := M) g α u_h _
  have hF_weighted_aesm : ∀ n, AEStronglyMeasurable (F n)
      ((chartPulledWeightedMeasure (I := I) g α).restrict Ω) := by
    intro n
    exact residual_aestronglyMeasurable_volume (I := I) (M := M) g α (v n) _
  have h_weighted_sigma : Tendsto (fun n => eLpNorm
      (fun y => F (σ n) y - fChartResidual (I := I) (M := M) g α u_h y) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict Ω)) atTop (𝓝 0) :=
    h_weighted.comp hσ_strict.tendsto_atTop
  have hF_weighted_sigma_aesm : ∀ n, AEStronglyMeasurable (F (σ n))
      ((chartPulledWeightedMeasure (I := I) g α).restrict Ω) :=
    fun n => hF_weighted_aesm (σ n)
  have h_weighted_measure : TendstoInMeasure
      ((chartPulledWeightedMeasure (I := I) g α).restrict Ω)
      (fun n => F (σ n)) atTop (fChartResidual (I := I) (M := M) g α u_h) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm
      (μ := (chartPulledWeightedMeasure (I := I) g α).restrict Ω) (p := 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) hF_weighted_sigma_aesm h_f_ae h_weighted_sigma
  obtain ⟨τ, hτ_strict, hτ_ae⟩ := h_weighted_measure.exists_seq_tendsto_ae
  have h_vol_ac : (volume : Measure EuclN).restrict Ω ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict Ω :=
    volume_restrict_target_absolutelyContinuous_weighted (I := I) (M := M) g α
  have h_lim_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      Tendsto (fun n => F (σ (τ n)) y) atTop (𝓝 (F_lim y)) := by
    filter_upwards [hσ_ae] with y hy
    exact hy.comp hτ_strict.tendsto_atTop
  have h_res_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      Tendsto (fun n => F (σ (τ n)) y) atTop
        (𝓝 (fChartResidual (I := I) (M := M) g α u_h y)) :=
    h_vol_ac.ae_le hτ_ae
  filter_upwards [h_lim_ae, h_res_ae] with y h₁ h₂
  exact tendsto_nhds_unique h₁ h₂

/-- If the smooth `v n` approximate `u_h` in chart `H^(m+1)` at rate `1/(n+1)`, any `H^m` limit
of their residuals is a.e. the residual of `u_h` on the chart target. -/
theorem smoothFChartResidual_limit_eq_fChartResidual_of_approx
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu : MemWkpChart (I := I) (M := M) (m + 1) 2
      ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
    (v : ℕ → SmoothScalar g)
    (hv : ∀ n, wkpNormChart (I := I) (M := M) (m + 1) 2
      (fun x => ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) x - (v n).toFun x) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)))
    (F_lim : EuclN → ℝ)
    (hF : MemWkp (d := Module.finrank ℝ E) m 2 F_lim (chartTargetEuclid (I := I) (M := M) α))
    (hF_lim : Tendsto (fun n =>
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) m 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
        (chartTargetEuclid (I := I) (M := M) α)) atTop (𝓝 0)) :
    F_lim =ᵐ[(volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)]
      fChartResidual (I := I) (M := M) g α u_h := by
  have hH1 : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h) :=
    bridge (I := I) (M := M) g m hu v hv
  exact limit_identification_of_h1_tendsto (I := I) (M := M) g α m hu v hv hH1
    F_lim hF hF_lim

end CalabiYau.PoissonDomainRegularity
