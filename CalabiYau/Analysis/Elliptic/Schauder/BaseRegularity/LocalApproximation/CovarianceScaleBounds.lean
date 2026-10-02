module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.Basic
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.CommonModulus
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.IncrementCancellation

/-! # Scale bounds for the mixed mollification covariance

This is the increment-cancellation step of the Constantin--E--Titi commutator argument,
adapted to a Hölder coefficient and a merely continuous second factor on a compact collar.
The two scale bounds share one vanishing modulus; near/far interpolation is proved separately.
-/

@[expose] public section

open Set Filter Matrix MeasureTheory Classical
open scoped ContDiff NNReal Topology Convolution

namespace CalabiYau.Schauder

/-- A continuous function on a compact set has an integrable zero extension. -/
private theorem compact_indicator_integrable {n : ℕ}
    {K : Set (EuclideanSpace ℂ (Fin n))} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    Integrable (K.indicator f) (volume : Measure (EuclideanSpace ℂ (Fin n))) := by
  have hOn : IntegrableOn f K (volume : Measure (EuclideanSpace ℂ (Fin n))) :=
    hf.integrableOn_compact hK
  exact hOn.integrable_indicator hK.measurableSet

/-- A zero-mass signed kernel only sees the oscillation of the factor it weights. -/
private lemma abs_integral_zero_mass_weighted_oscillation
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {q F : Ω → ℝ}
    {F₀ δ : ℝ}
    (hq : Integrable q μ)
    (hqF : Integrable (fun x => q x * F x) μ)
    (hqmean : ∫ x, q x ∂μ = 0)
    (_hδ : 0 ≤ δ)
    (hclose : ∀ᵐ x ∂μ, q x ≠ 0 → |F x - F₀| ≤ δ) :
    |∫ x, q x * F x ∂μ| ≤ δ * ∫ x, |q x| ∂μ := by
  have hscaled : Integrable (fun x => F₀ * q x) μ := hq.const_mul F₀
  have hcentered : Integrable (fun x => q x * (F x - F₀)) μ := by
    convert hqF.sub hscaled using 1
    funext x
    change q x * (F x - F₀) = q x * F x - F₀ * q x
    ring
  have hcenter_eq :
      (∫ x, q x * (F x - F₀) ∂μ) = ∫ x, q x * F x ∂μ := by
    calc
      (∫ x, q x * (F x - F₀) ∂μ) =
          (∫ x, q x * F x ∂μ) - ∫ x, F₀ * q x ∂μ := by
            rw [show (fun x => q x * (F x - F₀)) =
                fun x => q x * F x - F₀ * q x by funext x; ring]
            exact integral_sub hqF hscaled
      _ = (∫ x, q x * F x ∂μ) - F₀ * ∫ x, q x ∂μ := by
            rw [integral_const_mul]
      _ = ∫ x, q x * F x ∂μ := by rw [hqmean]; ring
  have hbound : ∀ᵐ x ∂μ,
      ‖q x * (F x - F₀)‖ ≤ δ * |q x| := by
    filter_upwards [hclose] with x hx
    by_cases hqx : q x = 0
    · simp [hqx]
    · rw [Real.norm_eq_abs, abs_mul]
      calc
        |q x| * |F x - F₀| ≤ |q x| * δ :=
          mul_le_mul_of_nonneg_left (hx hqx) (abs_nonneg _)
        _ = δ * |q x| := by ring
  have hmajorant : Integrable (fun x => δ * |q x|) μ := by
    convert hq.norm.const_mul δ using 1
    funext x
    simp only [Real.norm_eq_abs]
  have hnorm := norm_integral_le_of_norm_le hmajorant hbound
  rw [hcenter_eq] at hnorm
  simpa only [Real.norm_eq_abs, integral_const_mul] using hnorm

private theorem holderOnWith_zero_complex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α C : ℝ≥0} {s : Set E} {f : E → ℂ}
    (h : HolderBoundOn 0 α C s f) : HolderOnWith C α f s := by
  let curry := continuousMultilinearCurryFin0 ℝ E ℂ
  have hcomp : HolderOnWith C α (fun x => curry.symm (f x)) s := by
    intro x hx y hy
    have hh := h.2 x hx y hy
    have hh' : edist (curry.symm (f x)) (curry.symm (f y)) ≤
        (C : ENNReal) * edist x y ^ (α : ℝ) := by
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply] using hh
    exact hh'
  intro x hx y hy
  rw [← curry.symm.isometry.edist_eq (f x) (f y)]
  exact hcomp x hx y hy

private lemma norm_covariance_le_of_centered_bounds
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {A H : X → ℂ} {a b : ℂ} {εA εH : ℝ}
    (hA : Integrable A μ) (hH : Integrable H μ)
    (hAH : Integrable (fun x => A x * H x) μ)
    (hεA : 0 ≤ εA) (_hεH : 0 ≤ εH)
    (hAdev : ∀ᵐ x ∂μ, ‖A x - a‖ ≤ εA)
    (hHdev : ∀ᵐ x ∂μ, ‖H x - b‖ ≤ εH) :
    ‖(∫ x, A x * H x ∂μ) - (∫ x, A x ∂μ) * (∫ x, H x ∂μ)‖ ≤
      2 * εA * εH := by
  let U : X → ℂ := fun x => A x - a
  let V : X → ℂ := fun x => H x - b
  have hU : Integrable U μ := hA.sub (integrable_const _)
  have hV : Integrable V μ := hH.sub (integrable_const _)
  have hUV : Integrable (fun x => U x * V x) μ := by
    have heq : (fun x => U x * V x) =
        fun x => A x * H x - b * A x - a * H x + a * b := by
      funext x
      dsimp [U, V]
      ring
    rw [heq]
    exact ((hAH.sub (hA.const_mul b)).sub (hH.const_mul a)).add (integrable_const _)
  have hUbound : ‖∫ x, U x ∂μ‖ ≤ εA := by
    calc
      ‖∫ x, U x ∂μ‖ ≤ ∫ x, ‖U x‖ ∂μ := norm_integral_le_integral_norm U
      _ ≤ ∫ _x, εA ∂μ := integral_mono_ae hU.norm (integrable_const _) (by
        filter_upwards [hAdev] with x hx
        simpa [U] using hx)
      _ = εA := by simp [probReal_univ]
  have hVbound : ‖∫ x, V x ∂μ‖ ≤ εH := by
    calc
      ‖∫ x, V x ∂μ‖ ≤ ∫ x, ‖V x‖ ∂μ := norm_integral_le_integral_norm V
      _ ≤ ∫ _x, εH ∂μ := integral_mono_ae hV.norm (integrable_const _) (by
        filter_upwards [hHdev] with x hx
        simpa [V] using hx)
      _ = εH := by simp [probReal_univ]
  have hUVbound : ‖∫ x, U x * V x ∂μ‖ ≤ εA * εH := by
    calc
      ‖∫ x, U x * V x ∂μ‖ ≤ ∫ x, ‖U x * V x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _x, εA * εH ∂μ := integral_mono_ae hUV.norm (integrable_const _) (by
        filter_upwards [hAdev, hHdev] with x hx hy
        calc
          ‖U x * V x‖ = ‖U x‖ * ‖V x‖ := norm_mul _ _
          _ ≤ εA * εH := mul_le_mul hx hy (norm_nonneg _) hεA)
      _ = εA * εH := by simp [probReal_univ]
  have hmeanU : ∫ x, U x ∂μ = (∫ x, A x ∂μ) - a := by
    dsimp [U]
    rw [integral_sub hA (integrable_const a), integral_const]
    simp [probReal_univ]
  have hmeanV : ∫ x, V x ∂μ = (∫ x, H x ∂μ) - b := by
    dsimp [V]
    rw [integral_sub hH (integrable_const b), integral_const]
    simp [probReal_univ]
  have hUVmean : ∫ x, U x * V x ∂μ =
      (∫ x, A x * H x ∂μ) - b * (∫ x, A x ∂μ) -
        a * (∫ x, H x ∂μ) + a * b := by
    have heq : (fun x => U x * V x) =
        fun x => (A x * H x - b * A x - a * H x) + a * b := by
      funext x
      dsimp [U, V]
      ring
    rw [heq]
    have h1 : Integrable (fun x => A x * H x - b * A x) μ := hAH.sub (hA.const_mul b)
    have h2 : Integrable (fun x => a * H x) μ := hH.const_mul a
    calc
      _ = (∫ x, A x * H x - b * A x - a * H x ∂μ) + ∫ x, a * b ∂μ :=
        integral_add (h1.sub h2) (integrable_const _)
      _ = (∫ x, A x * H x ∂μ) - (∫ x, b * A x ∂μ) -
          (∫ x, a * H x ∂μ) + ∫ x, a * b ∂μ := by
        rw [integral_sub h1 h2, integral_sub hAH (hA.const_mul b)]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_const]
        simp [probReal_univ]
  have hcov :
      (∫ x, A x * H x ∂μ) - (∫ x, A x ∂μ) * (∫ x, H x ∂μ) =
        (∫ x, U x * V x ∂μ) - (∫ x, U x ∂μ) * (∫ x, V x ∂μ) := by
    rw [hUVmean, hmeanU, hmeanV]
    ring
  rw [hcov]
  calc
    ‖(∫ x, U x * V x ∂μ) - (∫ x, U x ∂μ) * (∫ x, V x ∂μ)‖ ≤
        ‖∫ x, U x * V x ∂μ‖ + ‖(∫ x, U x ∂μ) * (∫ x, V x ∂μ)‖ := norm_sub_le _ _
    _ = ‖∫ x, U x * V x ∂μ‖ + ‖∫ x, U x ∂μ‖ * ‖∫ x, V x ∂μ‖ := by rw [norm_mul]
    _ ≤ εA * εH + εA * εH := add_le_add hUVbound (mul_le_mul hUbound hVbound (norm_nonneg _) hεA)
    _ = 2 * εA * εH := by ring

open Classical in
private theorem weighted_cutoff_coefficient_integrable {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
    [TopologicalSpace Y]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (K : Set X) (U : Set Y) (kernel : X → ℝ) (sample : X → Y) (f : Y → ℂ)
    (hK : IsCompact K)
    (hKernel : ContinuousOn kernel K) (hSample : ContinuousOn sample K)
    (hIn : ∀ x ∈ K, sample x ∈ U) (hZero : ∀ x, x ∉ K → kernel x = 0)
    (hf : ContinuousOn f U) :
    Integrable (fun x ↦ kernel x • (if sample x ∈ U then f (sample x) else 0)) μ := by
  classical
  have hComp : ContinuousOn (fun x ↦ f (sample x)) K := hf.comp hSample hIn
  have hCut : ContinuousOn (fun x ↦ if sample x ∈ U then f (sample x) else 0) K := by
    apply hComp.congr
    intro x hx
    simp [hIn x hx]
  have hProd : ContinuousOn
      (fun x ↦ kernel x • (if sample x ∈ U then f (sample x) else 0)) K :=
    hKernel.smul hCut
  have hOn := hProd.integrableOn_compact (μ := μ) hK
  exact hOn.integrable_of_forall_notMem_eq_zero fun x hx ↦ by
    simp [hZero x hx]

open Classical in
private theorem localFixedMollify_integrand_integrable {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (m : ℕ) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ Metric.ball c S) :
    Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
      localFixedKernel hη m w •
        (if (complexToRealCoordinateEquiv.symm
          (complexToRealCoordinateEquiv z - w)) ∈ U then
          f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w))
        else 0)) := by
  classical
  let K : Set (EuclideanSpace ℝ (Fin n × Fin 2)) :=
    Metric.closedBall 0 (localKernelRadius η m)
  let sample : EuclideanSpace ℝ (Fin n × Fin 2) → EuclideanSpace ℂ (Fin n) :=
    fun w => complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  have hK : IsCompact K := by
    simpa [K] using (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n × Fin 2))
      (localKernelRadius η m))
  have hKernel : ContinuousOn (localFixedKernel hη m) K := by
    exact (localKernelBump hη m).continuous_normed.continuousOn
  have hSample : ContinuousOn sample K := by
    apply Continuous.continuousOn
    dsimp [sample]
    fun_prop
  have hIn : ∀ w ∈ K, sample w ∈ U := by
    intro w hw
    have hw_norm : ‖w‖ ≤ localKernelRadius η m := by
      simpa [K, dist_eq_norm] using hw
    have hr : localKernelRadius η m < η := by
      unfold localKernelRadius
      rw [div_lt_iff₀ (by positivity : 0 < 4 * ((m : ℝ) + 1))]
      nlinarith [hη]
    have hzs : z = complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z) :=
      (complexToRealCoordinateEquiv.symm_apply_apply z).symm
    have hdist : dist (sample w) z = ‖w‖ := by
      calc
        dist (sample w) z =
            dist (sample w)
              (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z)) := by
          exact congrArg (fun q => dist (sample w) q) hzs
        _ = dist (complexToRealCoordinateEquiv z - w) (complexToRealCoordinateEquiv z) := by
          dsimp [sample]
          exact complexToRealCoordinateEquiv.symm.isometry.dist_eq _ _
        _ = ‖w‖ := by
          rw [dist_eq_norm]
          have hsub :
              (complexToRealCoordinateEquiv z - w) - complexToRealCoordinateEquiv z = -w := by
            abel
          rw [hsub, norm_neg]
    have hthick : sample w ∈ Metric.thickening η (Metric.closedBall c S) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
      calc
        dist (sample w) z = ‖w‖ := hdist
        _ ≤ localKernelRadius η m := hw_norm
        _ < η := hr
    exact hCollar hthick
  have hZero : ∀ w, w ∉ K → localFixedKernel hη m w = 0 := by
    intro w hw
    by_contra hk
    have hsupport : w ∈ Function.support (localFixedKernel hη m) :=
      Function.mem_support.mpr hk
    have htsupport : w ∈ tsupport (localFixedKernel hη m) := subset_closure hsupport
    change w ∈ tsupport ((localKernelBump hη m).normed volume) at htsupport
    rw [(localKernelBump hη m).tsupport_normed_eq] at htsupport
    have htsupport' : ‖w‖ ≤ localKernelRadius η m := by
      simpa [localKernelBump, localKernelRadius] using htsupport
    exact hw (by simpa [K, dist_eq_norm] using htsupport')
  exact weighted_cutoff_coefficient_integrable K U (localFixedKernel hη m) sample f
    hK hKernel hSample hIn hZero hf

private theorem compact_collar_sum {n : ℕ} (c : EuclideanSpace ℂ (Fin n)
    ) {S η : ℝ} (hη : 0 < η) :
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    IsCompact K ∧ K ⊆ Metric.thickening η (Metric.closedBall c S) := by
  dsimp
  let C := EuclideanSpace ℂ (Fin n)
  have h1 : IsCompact (Metric.closedBall c S : Set C) := isCompact_closedBall c S
  have h2 : IsCompact (Metric.closedBall (0 : C) (η / 2)) := isCompact_closedBall 0 (η / 2)
  have hsum : IsCompact
      ((Metric.closedBall c S ×ˢ Metric.closedBall (0 : C) (η / 2)).image
        (fun p : C × C => p.1 + p.2)) := by
    apply (h1.prod h2).image
    fun_prop
  refine ⟨hsum, ?_⟩
  rintro y ⟨⟨x, v⟩, ⟨hx, hv⟩, rfl⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨x, hx, ?_⟩
  calc
    dist (x + v) x = dist v 0 := by
      rw [dist_eq_norm, dist_eq_norm]
      simp
    _ ≤ η / 2 := hv
    _ < η := by linarith

private theorem localKernelRadius_le_div_four {η : ℝ} (hη : 0 < η) (m : ℕ) :
    localKernelRadius η m ≤ η / 4 := by
  unfold localKernelRadius
  have hm : 0 ≤ (m : ℝ) := by positivity
  have hden : (4 : ℝ) ≤ 4 * ((m : ℝ) + 1) := by nlinarith
  exact div_le_div_of_nonneg_left hη.le (by norm_num : (0 : ℝ) < 4) hden

/-- On a small neighborhood of the compact collar, the local zero extension is a compactly
supported convolution with an integrable cutoff extension of the data. -/
private theorem localFixedMollify_eq_cutoffConvolution_near {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (m : ℕ)
    (x z : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S)
    (hnear : dist x z < η / 8) :
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
    localFixedMollify U hη m f z =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        localFixedKernel hη m w • Kr.indicator
          (fun y => f (complexToRealCoordinateEquiv.symm y))
          (complexToRealCoordinateEquiv z - w) := by
  dsimp
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
  have hKU : K ⊆ U := (compact_collar_sum c hη).2.trans hCollar
  have hradius := localKernelRadius_le_div_four hη m
  have hsampleK (w : EuclideanSpace ℝ (Fin n × Fin 2))
      (hw : localFixedKernel hη m w ≠ 0) :
      complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w) ∈ K := by
    have htsupport : w ∈ tsupport (localFixedKernel hη m) :=
      subset_closure (Function.mem_support.mpr hw)
    change w ∈ tsupport ((localKernelBump hη m).normed
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) at htsupport
    rw [(localKernelBump hη m).tsupport_normed_eq] at htsupport
    have hw' : ‖w‖ ≤ localKernelRadius η m := by
      simpa [localKernelBump, localKernelRadius, dist_eq_norm] using htsupport
    let rw := complexToRealCoordinateEquiv.symm w
    let v := z - x - rw
    have hv : dist v 0 ≤ η / 2 := by
      simp only [dist_eq_norm, sub_zero]
      dsimp [v]
      calc
        ‖z - x - rw‖ ≤ ‖z - x‖ + ‖rw‖ := norm_sub_le _ _
        _ = ‖z - x‖ + ‖w‖ := by
          rw [show ‖rw‖ = ‖w‖ by dsimp [rw]; exact complexToRealCoordinateEquiv.symm.norm_map w]
        _ = dist x z + ‖w‖ := by rw [dist_eq_norm, norm_sub_rev]
        _ ≤ η / 8 + η / 4 := add_le_add hnear.le (hw'.trans hradius)
        _ ≤ η / 2 := by linarith
    refine ⟨(x, v), ⟨Metric.ball_subset_closedBall hx, hv⟩, ?_⟩
    apply complexToRealCoordinateEquiv.injective
    rw [complexToRealCoordinateEquiv.apply_symm_apply]
    change complexToRealCoordinateEquiv
      (x + (z - x - complexToRealCoordinateEquiv.symm w)) =
        complexToRealCoordinateEquiv z - w
    simp only [map_add, map_sub, complexToRealCoordinateEquiv.apply_symm_apply]
    abel
  have hsampleU (w : EuclideanSpace ℝ (Fin n × Fin 2))
      (hw : localFixedKernel hη m w ≠ 0) :
      complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w) ∈ U :=
    hKU (hsampleK w hw)
  have hsampleKr (w : EuclideanSpace ℝ (Fin n × Fin 2))
      (hw : localFixedKernel hη m w ≠ 0) :
      complexToRealCoordinateEquiv z - w ∈ Kr := by
    refine ⟨complexToRealCoordinateEquiv.symm
      (complexToRealCoordinateEquiv z - w), hsampleK w hw, ?_⟩
    simp
  rw [localFixedMollify]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : localFixedKernel hη m w = 0
  · simp [hw]
  · rw [if_pos (hsampleU w hw), Set.indicator_of_mem (hsampleKr w hw)]
    exact Complex.real_smul

private theorem localFixedMollify_cutoff_integrable {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContinuousOn f U) :
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
    Integrable (Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y)))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  dsimp
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  have hKcompact : IsCompact K := (compact_collar_sum c hη).1
  have hKU : K ⊆ U := (compact_collar_sum c hη).2.trans hCollar
  let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
  have hKr : IsCompact Kr := by
    apply hKcompact.image
    exact complexToRealCoordinateEquiv.continuous
  have hmaps : ∀ y ∈ Kr, complexToRealCoordinateEquiv.symm y ∈ U := by
    rintro y ⟨z, hz, rfl⟩
    simpa using hKU hz
  have hcont : ContinuousOn (fun y => f (complexToRealCoordinateEquiv.symm y)) Kr :=
    hf.comp complexToRealCoordinateEquiv.symm.continuous.continuousOn hmaps
  have hOn : IntegrableOn
      (fun y => f (complexToRealCoordinateEquiv.symm y)) Kr
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
    hcont.integrableOn_compact hKr
  exact hOn.integrable_indicator hKr.measurableSet

private theorem hasFDerivAt_localFixedKernel_convolution_left_locallyIntegrable {n : ℕ}
    {η : ℝ} (hη : 0 < η) (m : ℕ) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (H : EuclideanSpace ℝ (Fin n × Fin 2) → F)
    (hH : LocallyIntegrable H (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    (letI : AddCommGroup (EuclideanSpace ℝ (Fin n × Fin 2)) :=
      (PiLp.normedAddCommGroup 2 (fun _ : Fin n × Fin 2 => ℝ)).toAddCommGroup
     HasFDerivAt
       (fun z => ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
         localFixedKernel hη m w • H (z - w))
       ((fderiv ℝ (localFixedKernel hη m) ⋆[
         (ContinuousLinearMap.lsmul ℝ ℝ).precompL
           (EuclideanSpace ℝ (Fin n × Fin 2)),
         (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] H) x) x) := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := localFixedKernel hη m
  let L : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  have hκ : ContDiff ℝ 1 κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).contDiff_normed
  have hcompact : HasCompactSupport κ := by
    dsimp [κ, localFixedKernel]
    exact (localKernelBump hη m).hasCompactSupport_normed
  have hderiv := hcompact.hasFDerivAt_convolution_left L hκ hH x
  have hconv :
      (fun z => ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        κ w • H (z - w)) =
        κ ⋆[L, (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] H := by
    funext z
    rw [← MeasureTheory.convolution_flip]
    rw [MeasureTheory.convolution_eq_swap]
    simp [L]
  rw [hconv]
  simpa [κ, L, ContinuousLinearMap.lsmul_apply] using hderiv

private theorem hasFDerivAt_localFixedMollify_real {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContinuousOn f U) (m : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S) :
    let K : Set (EuclideanSpace ℂ (Fin n)) :=
      (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
    let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
    HasFDerivAt
      (fun y => localFixedMollify U hη m f (complexToRealCoordinateEquiv.symm y))
      ((fderiv ℝ (localFixedKernel hη m) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)),
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))]
        (Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))))
        (complexToRealCoordinateEquiv x)) (complexToRealCoordinateEquiv x) := by
  dsimp
  let K : Set (EuclideanSpace ℂ (Fin n)) :=
    (Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2)
  let Kr : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := complexToRealCoordinateEquiv '' K
  let H : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ :=
    Kr.indicator (fun y => f (complexToRealCoordinateEquiv.symm y))
  have hH : Integrable H (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
    exact localFixedMollify_cutoff_integrable U hη hCollar f hf
  have hderiv := hasFDerivAt_localFixedKernel_convolution_left_locallyIntegrable
    (F := ℂ) hη m H hH.locallyIntegrable (complexToRealCoordinateEquiv x)
  have hEq : (fun y => localFixedMollify U hη m f (complexToRealCoordinateEquiv.symm y)) =ᶠ[
      𝓝 (complexToRealCoordinateEquiv x)]
      (fun y => ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        localFixedKernel hη m w • H (y - w)) := by
    filter_upwards [Metric.ball_mem_nhds _ (by positivity : (0 : ℝ) < η / 8)] with y hy
    have hy' : dist x (complexToRealCoordinateEquiv.symm y) < η / 8 := by
      calc
        dist x (complexToRealCoordinateEquiv.symm y) =
            dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x))
              (complexToRealCoordinateEquiv.symm y) := by
                rw [complexToRealCoordinateEquiv.symm_apply_apply]
        _ = dist (complexToRealCoordinateEquiv x) y :=
          complexToRealCoordinateEquiv.symm.isometry.dist_eq _ _
        _ < η / 8 := by simpa [Metric.mem_ball, dist_comm] using hy
    have hlocal := localFixedMollify_eq_cutoffConvolution_near
      U hη hCollar f m x (complexToRealCoordinateEquiv.symm y) hx hy'
    simpa [H, Kr, K, complexToRealCoordinateEquiv.apply_symm_apply] using hlocal
  exact hderiv.congr_of_eventuallyEq hEq

private theorem localMollificationCovariance_differentiableAt_of_continuous {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} (hη : 0 < η) {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U) (m : ℕ)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S) :
    DifferentiableAt ℝ
      (fun z => (localMollificationCovariance U hη m f g z).re) x := by
  let fg : EuclideanSpace ℂ (Fin n) → ℂ := fun y => f y * g y
  have hfg : ContinuousOn fg U := hf.mul hg
  have hF : HasFDerivAt
      (fun y => localFixedMollify U hη m f (complexToRealCoordinateEquiv.symm y))
      ((fderiv ℝ (localFixedKernel hη m) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n × Fin 2)),
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))]
        ((complexToRealCoordinateEquiv ''
          ((Metric.closedBall c S ×ˢ Metric.closedBall 0 (η / 2)).image
            (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.1 + p.2))).indicator
          (fun y => f (complexToRealCoordinateEquiv.symm y))))
        (complexToRealCoordinateEquiv x)) (complexToRealCoordinateEquiv x) :=
    hasFDerivAt_localFixedMollify_real U hη hCollar f hf m x hx
  have hF' : DifferentiableAt ℝ (fun z => localFixedMollify U hη m f z) x := by
    have hcomp := hF.comp x complexToRealCoordinateEquiv.hasFDerivAt
    simpa [Function.comp_def, complexToRealCoordinateEquiv.symm_apply_apply] using
      hcomp.differentiableAt
  have hG : DifferentiableAt ℝ (fun z => localFixedMollify U hη m g z) x := by
    have hderiv := hasFDerivAt_localFixedMollify_real U hη hCollar g hg m x hx
    have hcomp := hderiv.comp x complexToRealCoordinateEquiv.hasFDerivAt
    simpa [Function.comp_def, complexToRealCoordinateEquiv.symm_apply_apply] using
      hcomp.differentiableAt
  have hFG : DifferentiableAt ℝ (fun z => localFixedMollify U hη m fg z) x := by
    have hderiv := hasFDerivAt_localFixedMollify_real U hη hCollar fg hfg m x hx
    have hcomp := hderiv.comp x complexToRealCoordinateEquiv.hasFDerivAt
    simpa [Function.comp_def, complexToRealCoordinateEquiv.symm_apply_apply] using
      hcomp.differentiableAt
  have hcov : DifferentiableAt ℝ
      (fun z => localFixedMollify U hη m f z * localFixedMollify U hη m g z -
        localFixedMollify U hη m fg z) x :=
    (hF'.mul hG).sub hFG
  have hre : DifferentiableAt ℝ
      (fun z => Complex.reCLM (localFixedMollify U hη m f z *
        localFixedMollify U hη m g z - localFixedMollify U hη m fg z)) x := by
    exact (Complex.reCLM.hasFDerivAt.comp x hcov.hasFDerivAt).differentiableAt
  simpa [localMollificationCovariance, fg, Complex.reCLM] using hre

private noncomputable def localKernelProbabilityMeasure {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) : Measure (EuclideanSpace ℝ (Fin n × Fin 2)) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).withDensity
    (fun w => ENNReal.ofNNReal
      (⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩ : ℝ≥0))

private theorem localKernelProbabilityMeasure_isProbability {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    IsProbabilityMeasure (localKernelProbabilityMeasure (n := n) hη m) := by
  constructor
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ≥0 :=
    fun w => ⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩
  have hκ : Integrable (fun w => (κ w : ℝ)) := by
    exact (localKernelBump hη m).integrable_normed
  change ((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).withDensity
    (fun w => ENNReal.ofNNReal (κ w))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [lintegral_coe_eq_integral κ hκ]
  have hfun : (fun w => (κ w : ℝ)) = localFixedKernel hη m := by
    funext w
    rfl
  rw [hfun, localFixedKernel_integral]
  norm_num

private theorem localKernelProbability_integral {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (G : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ) :
    (∫ w, G w ∂localKernelProbabilityMeasure (n := n) hη m) =
      ∫ w, localFixedKernel hη m w • G w := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ≥0 :=
    fun w => ⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩
  change (∫ w, G w ∂(volume.withDensity fun w => ENNReal.ofNNReal (κ w))) = _
  have hKernel : Measurable (localFixedKernel (n := n) hη m) := by
    exact (localKernelBump (n := n) hη m).continuous_normed.measurable
  have hκ : Measurable κ := by
    change Measurable (fun w =>
      (⟨localFixedKernel (n := n) hη m w,
        localFixedKernel_nonneg (n := n) hη m w⟩ : ℝ≥0))
    exact hKernel.subtype_mk
  rw [integral_withDensity_eq_integral_smul hκ G]
  change (∫ w, (κ w : ℝ) • G w) = _
  congr 1

private theorem localFixedMollify_eq_kernelProbability_integral {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) {η : ℝ} (hη : 0 < η) (m : ℕ)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n)) :
    localFixedMollify U hη m f z =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (if complexToRealCoordinateEquiv.symm
            (complexToRealCoordinateEquiv z - w) ∈ U then
          f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0)
        ∂localKernelProbabilityMeasure hη m := by
  rw [localFixedMollify]
  symm
  rw [localKernelProbability_integral]

private theorem localKernelProbability_integrable {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (G : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ)
    (hG : Integrable (fun w => localFixedKernel hη m w • G w)) :
    Integrable G (localKernelProbabilityMeasure (n := n) hη m) := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ≥0 :=
    fun w => ⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩
  have hKernel : Measurable (localFixedKernel (n := n) hη m) := by
    exact (localKernelBump (n := n) hη m).continuous_normed.measurable
  have hκ : Measurable κ := by
    change Measurable (fun w =>
      (⟨localFixedKernel (n := n) hη m w,
        localFixedKernel_nonneg (n := n) hη m w⟩ : ℝ≥0))
    exact hKernel.subtype_mk
  change Integrable G ((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).withDensity
    fun w => ENNReal.ofNNReal (κ w))
  apply (integrable_withDensity_iff_integrable_smul
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) hκ).2
  convert hG using 1
  funext w
  rfl

private theorem localKernelProbability_support {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    ∀ᵐ w ∂localKernelProbabilityMeasure (n := n) hη m,
      ‖w‖ ≤ localKernelRadius η m := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ≥0 :=
    fun w => ⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩
  have hKernel : Measurable (localFixedKernel (n := n) hη m) := by
    exact (localKernelBump (n := n) hη m).continuous_normed.measurable
  have hκ : Measurable κ := by
    change Measurable (fun w =>
      (⟨localFixedKernel (n := n) hη m w,
        localFixedKernel_nonneg (n := n) hη m w⟩ : ℝ≥0))
    exact hKernel.subtype_mk
  have hbound : ∀ w, ENNReal.ofNNReal (κ w) ≠ 0 →
      ‖w‖ ≤ localKernelRadius η m := by
    intro w hden
    have hk : localFixedKernel hη m w ≠ 0 := by
      intro hk
      have hκzero : κ w = 0 := by
        apply Subtype.ext
        exact hk
      apply hden
      rw [hκzero]
      rfl
    have hsupport : w ∈ tsupport (localFixedKernel hη m) :=
      subset_closure (Function.mem_support.mpr hk)
    change w ∈ tsupport ((localKernelBump hη m).normed volume) at hsupport
    rw [(localKernelBump hη m).tsupport_normed_eq] at hsupport
    simpa [localKernelBump, localKernelRadius, dist_eq_norm] using hsupport
  change ∀ᵐ w ∂((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).withDensity
    fun w => ENNReal.ofNNReal (κ w)), ‖w‖ ≤ localKernelRadius η m
  rw [ae_withDensity_iff' (hκ.coe_nnreal_ennreal).aemeasurable]
  filter_upwards [] with w hden
  exact hbound w hden

private theorem localKernelProbability_sample_in_U {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (m : ℕ) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S) :
    ∀ᵐ w ∂localKernelProbabilityMeasure hη m,
      complexToRealCoordinateEquiv.symm
        (complexToRealCoordinateEquiv z - w) ∈ U := by
  have hr : localKernelRadius η m < η := by
    unfold localKernelRadius
    rw [div_lt_iff₀ (by positivity : 0 < 4 * ((m : ℝ) + 1))]
    nlinarith [hη]
  filter_upwards [localKernelProbability_support (n := n) hη m] with w hw
  have hzs : z = complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z) :=
    (complexToRealCoordinateEquiv.symm_apply_apply z).symm
  have hdist : dist
      (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) z = ‖w‖ := by
    calc
      dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) z =
          dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w))
            (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z)) := by
        exact congrArg (fun q => dist
          (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) q) hzs
      _ = dist (complexToRealCoordinateEquiv z - w) (complexToRealCoordinateEquiv z) := by
        exact complexToRealCoordinateEquiv.symm.isometry.dist_eq _ _
      _ = ‖w‖ := by
        rw [dist_eq_norm]
        have hsub : (complexToRealCoordinateEquiv z - w) - complexToRealCoordinateEquiv z = -w := by
          abel
        rw [hsub, norm_neg]
  have hthick : complexToRealCoordinateEquiv.symm
      (complexToRealCoordinateEquiv z - w) ∈ Metric.thickening η (Metric.closedBall c S) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
    calc
      dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) z = ‖w‖ := hdist
      _ ≤ localKernelRadius η m := hw
      _ < η := hr
  exact hCollar hthick

private theorem localKernelProbability_holder_deviation {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {α K : ℝ≥0} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hH : HolderBoundOn 0 α K U f) (m : ℕ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S) :
    ∀ᵐ w ∂localKernelProbabilityMeasure hη m,
      ‖(if complexToRealCoordinateEquiv.symm
            (complexToRealCoordinateEquiv z - w) ∈ U then
          f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0) - f z‖ ≤
        (K : ℝ) * localKernelRadius η m ^ (α : ℝ) := by
  have hzU : z ∈ U := hCollar (by
    rw [Metric.mem_thickening_iff]
    exact ⟨z, Metric.ball_subset_closedBall hz, by simpa using hη⟩)
  have hSampleU := localKernelProbability_sample_in_U hη hCollar m z hz
  have hSupport := localKernelProbability_support (n := n) hη m
  filter_upwards [hSampleU, hSupport] with w hwU hw
  let y := complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  have hy : y ∈ U := by simpa [y] using hwU
  have hpoint : ‖f y - f z‖ ≤
      (K : ℝ) * dist y z ^ (α : ℝ) := by
    have hpair' := (holderOnWith_zero_complex hH) y hy z hzU
    have hrhs : (K : ENNReal) * edist y z ^ (α : ℝ) =
        ENNReal.ofReal ((K : ℝ) * dist y z ^ (α : ℝ)) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg
        (NNReal.coe_nonneg α)]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg K)]
    have hpair'' : edist (f y) (f z) ≤
        ENNReal.ofReal ((K : ℝ) * dist y z ^ (α : ℝ)) := by
      rw [← hrhs]
      exact hpair'
    have hdist : dist (f y) (f z) ≤
        (K : ℝ) * dist y z ^ (α : ℝ) :=
      (edist_le_ofReal (by positivity)).mp hpair''
    simpa [dist_eq_norm] using hdist
  have hdist_eq : dist y z = ‖w‖ := by
    simp [y]
  have hdist : dist y z ≤ localKernelRadius η m := by
    rw [hdist_eq]
    exact hw
  have hpow : dist y z ^ (α : ℝ) ≤ localKernelRadius η m ^ (α : ℝ) :=
    Real.rpow_le_rpow (dist_nonneg) hdist (NNReal.coe_nonneg _)
  have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg _
  calc
    ‖(if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w) ∈ U then
        f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0) - f z‖ =
        ‖f y - f z‖ := by
      change ‖(if y ∈ U then f y else 0) - f z‖ = _
      simp [hy]
    _ ≤ (K : ℝ) * dist y z ^ (α : ℝ) := hpoint
    _ ≤ (K : ℝ) * localKernelRadius η m ^ (α : ℝ) :=
      mul_le_mul_of_nonneg_left hpow hK

private theorem localKernelProbability_sample_integrable {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (m : ℕ) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ Metric.ball c S) :
    Integrable
      (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
        if complexToRealCoordinateEquiv.symm
            (complexToRealCoordinateEquiv z - w) ∈ U then
          f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0)
      (localKernelProbabilityMeasure hη m) := by
  apply localKernelProbability_integrable hη m
  exact localFixedMollify_integrand_integrable hη hCollar hf m z hz

private theorem localMollificationCovariance_norm_le_of_sample_deviations {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {α K : ℝ≥0} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hHolder : HolderBoundOn 0 α K U f) (m : ℕ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S)
    {εg : ℝ} (hεg : 0 ≤ εg)
    (hDevG : ∀ᵐ w ∂localKernelProbabilityMeasure hη m,
      ‖(if complexToRealCoordinateEquiv.symm
          (complexToRealCoordinateEquiv z - w) ∈ U then
        g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0) -
          g z‖ ≤ εg) :
    ‖localMollificationCovariance U hη m f g z‖ ≤
      2 * ((K : ℝ) * localKernelRadius η m ^ (α : ℝ)) * εg := by
  let sample : EuclideanSpace ℝ (Fin n × Fin 2) → EuclideanSpace ℂ (Fin n) :=
    fun w => complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  let A : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ := fun w =>
    if sample w ∈ U then f (sample w) else 0
  let H : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ := fun w =>
    if sample w ∈ U then g (sample w) else 0
  have hfprod : ContinuousOn (fun y => f y * g y) U := hf.mul hg
  have hA : Integrable A (localKernelProbabilityMeasure hη m) := by
    simpa [A, sample] using localKernelProbability_sample_integrable hη hCollar hf m z hz
  have hH : Integrable H (localKernelProbabilityMeasure hη m) := by
    simpa [H, sample] using localKernelProbability_sample_integrable hη hCollar hg m z hz
  have hprod : Integrable (fun w => if sample w ∈ U then (f * g) (sample w) else 0)
      (localKernelProbabilityMeasure hη m) := by
    simpa [sample] using localKernelProbability_sample_integrable hη hCollar hfprod m z hz
  have hSampleU : ∀ᵐ w ∂localKernelProbabilityMeasure hη m, sample w ∈ U := by
    simpa [sample] using localKernelProbability_sample_in_U hη hCollar m z hz
  have hAH : Integrable (fun w => A w * H w) (localKernelProbabilityMeasure hη m) := by
    apply hprod.congr
    filter_upwards [hSampleU] with w hw
    simp [A, H, hw]
  have hDevA : ∀ᵐ w ∂localKernelProbabilityMeasure hη m,
      ‖A w - f z‖ ≤ (K : ℝ) * localKernelRadius η m ^ (α : ℝ) := by
    simpa [A, sample] using localKernelProbability_holder_deviation hη hCollar hHolder m z hz
  have hmf : localFixedMollify U hη m f z =
      ∫ w, A w ∂localKernelProbabilityMeasure hη m := by
    rw [localFixedMollify_eq_kernelProbability_integral]
  have hmg : localFixedMollify U hη m g z =
      ∫ w, H w ∂localKernelProbabilityMeasure hη m := by
    rw [localFixedMollify_eq_kernelProbability_integral]
  have hmfg : localFixedMollify U hη m (fun y => f y * g y) z =
      ∫ w, A w * H w ∂localKernelProbabilityMeasure hη m := by
    rw [localFixedMollify_eq_kernelProbability_integral]
    apply integral_congr_ae
    filter_upwards [localKernelProbability_sample_in_U hη hCollar m z hz] with w hwOriginal
    have hw : sample w ∈ U := by simpa [sample] using hwOriginal
    have hs : sample w = z - complexToRealCoordinateEquiv.symm w := by
      simp [sample]
    have hw' : z - complexToRealCoordinateEquiv.symm w ∈ U := by
      rw [← hs]
      exact hw
    rw [if_pos hwOriginal]
    simp [A, H, hw', hs]
  have hεf : 0 ≤ (K : ℝ) * localKernelRadius η m ^ (α : ℝ) :=
    mul_nonneg (NNReal.coe_nonneg K)
      (Real.rpow_nonneg (le_of_lt (localKernelRadius_pos hη m)) _)
  let : IsProbabilityMeasure (localKernelProbabilityMeasure (n := n) hη m) :=
    localKernelProbabilityMeasure_isProbability (n := n) hη m
  have hcov := norm_covariance_le_of_centered_bounds hA hH hAH hεf hεg hDevA
    (by simpa [H, sample] using hDevG)
  rw [localMollificationCovariance, hmf, hmg, hmfg]
  exact (norm_sub_rev _ _).trans_le hcov

private theorem localMollificationCovariance_spatialLip_of_derivative_bound {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η C : ℝ} (hη : 0 < η) (m : ℕ)
    {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hDiff : ∀ x ∈ Metric.ball c S,
      DifferentiableAt ℝ (fun z => (localMollificationCovariance U hη m f g z).re) x)
    (hbound : ∀ x ∈ Metric.ball c S,
      ‖fderiv ℝ (fun z => (localMollificationCovariance U hη m f g z).re) x‖ ≤ C)
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ Metric.ball c S) :
    |(localMollificationCovariance U hη m f g x).re -
        (localMollificationCovariance U hη m f g y).re| ≤ C * dist x y := by
  have hmv := (convex_ball c S).norm_image_sub_le_of_norm_fderiv_le hDiff hbound hx hy
  calc
    |(localMollificationCovariance U hη m f g x).re -
        (localMollificationCovariance U hη m f g y).re| =
        ‖(localMollificationCovariance U hη m f g y).re -
          (localMollificationCovariance U hη m f g x).re‖ := by
            rw [Real.norm_eq_abs, abs_sub_comm]
    _ ≤ C * ‖y - x‖ := hmv
    _ = C * dist x y := by rw [dist_eq_norm, norm_sub_rev]

private theorem actualCovariance_continuous_increment_modulus {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hS : 0 < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hg : ContinuousOn g U) :
    ∃ modulus : ℕ → ℝ, Filter.Tendsto modulus Filter.atTop (𝓝 0) ∧
      (∀ m, 0 ≤ modulus m) ∧
      ∀ (m : ℕ) (x : EuclideanSpace ℂ (Fin n)), x ∈ Metric.ball c S →
        ∀ h : EuclideanSpace ℂ (Fin n),
          ‖h‖ ≤ 2 * (η / (4 * ((m : ℝ) + 1))) →
            ‖g (x + h) - g x‖ ≤ modulus m := by
  let K : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall c S
  let C : Set (EuclideanSpace ℂ (Fin n)) := Metric.cthickening (η / 2) K
  let r : ℕ → ℝ := fun m => η / (4 * ((m : ℝ) + 1))
  let A : ℕ → Set ℝ := fun m => {a | ∃ x h, x ∈ Metric.ball c S ∧
    ‖h‖ ≤ 2 * r m ∧ a = ‖g (x + h) - g x‖}
  let modulus : ℕ → ℝ := fun m => sSup (A m)
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_closedBall c S
  have hCcompact : IsCompact C := by
    dsimp [C]
    exact hKcompact.cthickening
  have hCsubU : C ⊆ U := by
    dsimp [C, K]
    exact (Metric.cthickening_subset_thickening' hη (by linarith) _).trans hCollar
  have hgC : ContinuousOn g C := hg.mono hCsubU
  have hUC : UniformContinuousOn g C := hCcompact.uniformContinuousOn_of_continuous hgC
  have hradius_nonneg (m : ℕ) : 0 ≤ r m := by
    dsimp [r]
    positivity
  have htwor_le (m : ℕ) : 2 * r m ≤ η / 2 := by
    dsimp [r]
    have hm : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hden : 0 < 4 * ((m : ℝ) + 1) := by positivity
    calc
      2 * (η / (4 * ((m : ℝ) + 1))) = η / (2 * ((m : ℝ) + 1)) := by
        field_simp; norm_num
      _ ≤ η / 2 := div_le_div_of_nonneg_left hη.le (by norm_num)
        (by nlinarith [hm])
  have hxC (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball c S) : x ∈ C := by
    have hxK : x ∈ K := Metric.ball_subset_closedBall hx
    apply (Metric.closedBall_subset_cthickening hxK (η / 2))
    rw [Metric.mem_closedBall, dist_self]
    positivity
  have hxaddC (m : ℕ) (x h : EuclideanSpace ℂ (Fin n))
      (hx : x ∈ Metric.ball c S) (hh : ‖h‖ ≤ 2 * r m) : x + h ∈ C := by
    have hxK : x ∈ K := Metric.ball_subset_closedBall hx
    apply (Metric.closedBall_subset_cthickening hxK (η / 2))
    rw [Metric.mem_closedBall]
    have hdist : dist (x + h) x = ‖h‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    rw [hdist]
    exact hh.trans (htwor_le m)
  have himageCompact : IsCompact (g '' C) := hCcompact.image_of_continuousOn hgC
  have himageBounded := himageCompact.isBounded
  obtain ⟨R, hR⟩ := himageBounded.subset_closedBall (0 : ℂ)
  have hcC : c ∈ C := by
    apply hxC c
    simpa [Metric.mem_ball] using hS
  have hRnonneg : 0 ≤ R := by
    have hmem : g c ∈ g '' C := ⟨c, hcC, rfl⟩
    have hball := hR hmem
    exact le_trans (norm_nonneg (g c)) (by simpa [Metric.mem_closedBall] using hball)
  have hnormg (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ C) : ‖g x‖ ≤ R := by
    have hmem : g x ∈ g '' C := ⟨x, hx, rfl⟩
    have hball := hR hmem
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball
  have hAzero (m : ℕ) : 0 ∈ A m := by
    dsimp [A]
    refine ⟨c, 0, ?_, ?_, ?_⟩
    · simpa [Metric.mem_ball] using hS
    · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hradius_nonneg m)
    · simp
  have hAnonempty (m : ℕ) : (A m).Nonempty := ⟨0, hAzero m⟩
  have hAbdd (m : ℕ) : BddAbove (A m) := by
    refine ⟨2 * R, ?_⟩
    intro a ha
    rcases ha with ⟨x, h, hx, hh, rfl⟩
    have hx' : x ∈ C := hxC x hx
    have hx'h : x + h ∈ C := hxaddC m x h hx hh
    calc
      ‖g (x + h) - g x‖ ≤ ‖g (x + h)‖ + ‖g x‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hnormg _ hx'h) (hnormg _ hx')
      _ = 2 * R := by ring
  have hmodulusnonneg (m : ℕ) : 0 ≤ modulus m :=
    le_csSup (hAbdd m) (hAzero m)
  have hbound (m : ℕ) (x : EuclideanSpace ℂ (Fin n))
      (hx : x ∈ Metric.ball c S) (h : EuclideanSpace ℂ (Fin n))
      (hh : ‖h‖ ≤ 2 * r m) : ‖g (x + h) - g x‖ ≤ modulus m := by
    apply le_csSup (hAbdd m)
    exact ⟨x, h, hx, hh, rfl⟩
  have hrho : Filter.Tendsto (fun m : ℕ => 2 * r m) Filter.atTop (𝓝 0) := by
    have hrec := tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (η / 2)
    have heq : (fun m : ℕ => 2 * r m) =
        fun (m : ℕ) => (1 / ((m : ℝ) + 1)) * (η / 2) := by
      funext m
      dsimp [r]
      field_simp
      ring
    rw [heq]
    simpa using hrec
  have hmodulustendsto : Filter.Tendsto modulus Filter.atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ :=
      (Metric.uniformContinuousOn_iff_le.mp hUC) (ε / 2) (by linarith)
    have hsmall : ∀ᶠ m : ℕ in Filter.atTop, 2 * r m < δ :=
      hrho.eventually (Iio_mem_nhds hδ)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
    refine ⟨N, ?_⟩
    intro m hmN
    have hm := hN m hmN
    have hmodulusle : modulus m ≤ ε / 2 := by
      apply csSup_le (hAnonempty m)
      intro a ha
      rcases ha with ⟨x, h, hx, hh, rfl⟩
      have hxC' : x ∈ C := hxC x hx
      have hxaddC' : x + h ∈ C := hxaddC m x h hx hh
      have hdist : dist (x + h) x ≤ δ := by
        rw [dist_eq_norm]
        exact le_of_lt <| calc
          ‖x + h - x‖ = ‖h‖ := by congr 1; abel
          _ ≤ 2 * r m := hh
          _ < δ := hm
      have hmod' := hmod (x + h) hxaddC' x hxC' hdist
      simpa [dist_eq_norm] using hmod'
    have hboundε : modulus m < ε := lt_of_le_of_lt hmodulusle (by linarith)
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (hmodulusnonneg m)] using hboundε
  have hcball : c ∈ Metric.ball c S := by
    simpa [Metric.mem_ball] using hS
  have hmod_nonneg (m : ℕ) : 0 ≤ modulus m := by
    have hzero := hbound m c hcball 0 (by
      have hr := hradius_nonneg m
      simpa [r] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)
    exact le_trans (norm_nonneg _) hzero
  refine ⟨modulus, hmodulustendsto, hmod_nonneg, ?_⟩
  intro m x hx h hh
  exact hbound m x hx h (by simpa [r] using hh)

private theorem actualCovariance_common_modulus_data {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {α K : ℝ≥0} {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hS : 0 < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hHolder : HolderBoundOn 0 α K U f) :
    ∃ modulus : ℕ → ℝ, Filter.Tendsto modulus Filter.atTop (𝓝 0) ∧
      (∀ m, 0 ≤ modulus m) ∧
      (∀ m x, x ∈ Metric.ball c S → ∀ h : EuclideanSpace ℂ (Fin n),
        ‖h‖ ≤ 2 * localKernelRadius η m →
          ‖g (x + h) - g x‖ ≤ modulus m) ∧
      (∀ m x, x ∈ Metric.ball c S →
        |(localMollificationCovariance U hη m f g x).re| ≤
          2 * (K : ℝ) * modulus m * localKernelRadius η m ^ (α : ℝ)) := by
  obtain ⟨modulus, hmoduluszero, hmodulusnonneg, hmodulusbound⟩ :=
    actualCovariance_continuous_increment_modulus hS hη hCollar hg
  have hmodulusbound' : ∀ m x, x ∈ Metric.ball c S →
      ∀ h : EuclideanSpace ℂ (Fin n),
        ‖h‖ ≤ 2 * localKernelRadius η m → ‖g (x + h) - g x‖ ≤ modulus m := by
    intro m x hx h hh
    exact hmodulusbound m x hx h (by simpa [localKernelRadius] using hh)
  refine ⟨modulus, hmoduluszero, hmodulusnonneg, hmodulusbound', ?_⟩
  intro m x hx
  have hSampleU := localKernelProbability_sample_in_U hη hCollar m x hx
  have hSupport := localKernelProbability_support (n := n) hη m
  have hDevG : ∀ᵐ w ∂localKernelProbabilityMeasure hη m,
      ‖(if complexToRealCoordinateEquiv.symm
          (complexToRealCoordinateEquiv x - w) ∈ U then
        g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) else 0) -
          g x‖ ≤ modulus m := by
    filter_upwards [hSampleU, hSupport] with w hwU hw
    let y := complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)
    have hyU : y ∈ U := by simpa [y] using hwU
    have hdist : dist y x = ‖w‖ := by
      dsimp [y]
      have hxs : x = complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x) :=
        (complexToRealCoordinateEquiv.symm_apply_apply x).symm
      calc
        dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w)) x =
            dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x - w))
              (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv x)) :=
                congrArg _ hxs
        _ = dist (complexToRealCoordinateEquiv x - w) (complexToRealCoordinateEquiv x) :=
          complexToRealCoordinateEquiv.symm.isometry.dist_eq _ _
        _ = ‖w‖ := by
          rw [dist_eq_norm]
          have hs : (complexToRealCoordinateEquiv x - w) - complexToRealCoordinateEquiv x = -w := by
            abel
          rw [hs, norm_neg]
    have hshift : ‖y - x‖ ≤ 2 * localKernelRadius η m := by
      rw [← dist_eq_norm, hdist]
      calc
        ‖w‖ ≤ localKernelRadius η m := hw
        _ ≤ 2 * localKernelRadius η m := by nlinarith [localKernelRadius_pos hη m]
    have hinc := hmodulusbound' m x hx (y - x) hshift
    have hxy : x + (y - x) = y := by abel
    rw [hxy] at hinc
    change ‖(if y ∈ U then g y else 0) - g x‖ ≤ modulus m
    rw [if_pos hyU]
    exact hinc
  have hcov := localMollificationCovariance_norm_le_of_sample_deviations hη hCollar
    hf hg hHolder m x hx (hmodulusnonneg m) hDevG
  calc
    |(localMollificationCovariance U hη m f g x).re| ≤
        ‖localMollificationCovariance U hη m f g x‖ := Complex.abs_re_le_norm _
    _ ≤ 2 * ((K : ℝ) * localKernelRadius η m ^ (α : ℝ)) * modulus m := hcov
    _ = 2 * (K : ℝ) * modulus m * localKernelRadius η m ^ (α : ℝ) := by ring

/-- Cancellation gains the coefficient's Hölder power and the continuous factor's vanishing
local oscillation. The slope bound costs precisely one power of the fixed convolution radius.
No derivative or Hölder hypothesis on `g` is assumed. -/
theorem localMollificationCovariance_scaleBounds {n : ℕ}
    {α K : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hS : 0 < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hH : HolderBoundOn 0 α K U f) :
    ∃ δ : ℕ → ℝ≥0, Tendsto δ atTop (𝓝 0) ∧
      (∀ m x, x ∈ Metric.ball c S →
        |(localMollificationCovariance U hη m f g x).re| ≤
          (δ m : ℝ) * localKernelRadius η m ^ (α : ℝ)) ∧
      (∀ m x, x ∈ Metric.ball c S → ∀ y, y ∈ Metric.ball c S →
        |(localMollificationCovariance U hη m f g x).re -
          (localMollificationCovariance U hη m f g y).re| ≤
          (δ m : ℝ) * dist x y / localKernelRadius η m ^ (1 - (α : ℝ))) := by
  obtain ⟨modulus, hmoduluszero, hmodulusnonneg, hIncrement, hValue⟩ :=
    actualCovariance_common_modulus_data hS hη hCollar hf hg hH
  have hJ : 0 ≤ covarianceA2_J n := covarianceA2_J_nonneg n
  have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
  have hSlope : ∀ m x, x ∈ Metric.ball c S →
      ‖fderiv ℝ (fun z => (localMollificationCovariance U hη m f g z).re) x‖ ≤
        4 * (K : ℝ) * covarianceA2_J n * modulus m /
          (localKernelRadius η m) ^ (1 - (α : ℝ)) := by
    intro m x hx
    have hdir := incrementCancellation_real_directional_bound hη hCollar hf hg hH
      (hmodulusnonneg m) m x hx (by
        intro h hh
        exact hIncrement m x hx h hh)
    have hcoef : 0 ≤ 4 * (K : ℝ) * covarianceA2_J n * modulus m :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hK) hJ)
        (hmodulusnonneg m)
    have hB : 0 ≤ 4 * (K : ℝ) * covarianceA2_J n * modulus m /
        (localKernelRadius η m) ^ (1 - (α : ℝ)) := by
      apply div_nonneg hcoef
      exact (Real.rpow_pos_of_pos (localKernelRadius_pos hη m) _).le
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    exact hdir v
  obtain ⟨δ, hδ, hδformula, hCommonValue, hCommonSlope⟩ :=
    covarianceCommonModulusLeaf_commonModulus_uniform (Metric.ball c S) hJ hK
      modulus (fun m => localKernelRadius η m)
      (fun m x => (localMollificationCovariance U hη m f g x).re)
      (fun m x => ‖fderiv ℝ
        (fun z => (localMollificationCovariance U hη m f g z).re) x‖)
      hmodulusnonneg hmoduluszero (fun m => localKernelRadius_pos hη m)
      hValue hSlope
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro m x hx
    exact hCommonValue m x hx
  · intro m x hx y hy
    let C : ℝ := (δ m : ℝ) / localKernelRadius η m ^ (1 - (α : ℝ))
    have hDiff : ∀ z ∈ Metric.ball c S,
        DifferentiableAt ℝ
          (fun w => (localMollificationCovariance U hη m f g w).re) z := by
      intro z hz
      exact localMollificationCovariance_differentiableAt_of_continuous
        hη hf hg hCollar m z hz
    have hBound : ∀ z ∈ Metric.ball c S,
        ‖fderiv ℝ
          (fun w => (localMollificationCovariance U hη m f g w).re) z‖ ≤ C := by
      intro z hz
      exact hCommonSlope m z hz
    have hLip := localMollificationCovariance_spatialLip_of_derivative_bound
      hη m hDiff hBound x hx y hy
    calc
      |(localMollificationCovariance U hη m f g x).re -
          (localMollificationCovariance U hη m f g y).re| ≤ C * dist x y := hLip
      _ = (δ m : ℝ) * dist x y /
          localKernelRadius η m ^ (1 - (α : ℝ)) := by
        dsimp [C]
        ring

end CalabiYau.Schauder
