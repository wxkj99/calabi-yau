module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.Basic
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.CovarianceScaleBounds.KernelDerivativeBounds

open Set Filter MeasureTheory Classical
open scoped ContDiff NNReal Topology

@[expose] public section

namespace CalabiYau.Schauder

noncomputable def holderLeafKernelMeasure {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) : Measure (EuclideanSpace ℝ (Fin n × Fin 2)) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).withDensity
    (fun w => ENNReal.ofNNReal
      (⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩ : ℝ≥0))

theorem holderLeafKernelMeasure_probability {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    IsProbabilityMeasure (holderLeafKernelMeasure (n := n) hη m) := by
  constructor
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ≥0 :=
    fun w => ⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩
  have hκ : Integrable (fun w => (κ w : ℝ)) :=
    (localKernelBump hη m).integrable_normed
  change ((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).withDensity
    (fun w => ENNReal.ofNNReal (κ w))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [lintegral_coe_eq_integral κ hκ]
  have hfun : (fun w => (κ w : ℝ)) = localFixedKernel hη m := by
    funext w
    rfl
  rw [hfun, localFixedKernel_integral]
  norm_num

theorem holderLeafKernelMeasure_integral {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (G : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ) :
    (∫ w, G w ∂holderLeafKernelMeasure (n := n) hη m) =
      ∫ w, localFixedKernel hη m w • G w := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ≥0 :=
    fun w => ⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩
  change (∫ w, G w ∂(volume.withDensity fun w => ENNReal.ofNNReal (κ w))) = _
  have hKernel : Measurable (localFixedKernel (n := n) hη m) :=
    (localKernelBump (n := n) hη m).continuous_normed.measurable
  have hκ : Measurable κ := by
    change Measurable (fun w =>
      (⟨localFixedKernel (n := n) hη m w,
        localFixedKernel_nonneg hη m w⟩ : ℝ≥0))
    exact hKernel.subtype_mk
  rw [integral_withDensity_eq_integral_smul hκ G]
  change (∫ w, (κ w : ℝ) • G w) = _
  congr 1

theorem holderLeafKernelMeasure_integrable {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (G : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ)
    (hG : Integrable (fun w => localFixedKernel hη m w • G w)) :
    Integrable G (holderLeafKernelMeasure (n := n) hη m) := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ≥0 :=
    fun w => ⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩
  have hKernel : Measurable (localFixedKernel (n := n) hη m) :=
    (localKernelBump (n := n) hη m).continuous_normed.measurable
  have hκ : Measurable κ := by
    change Measurable (fun w =>
      (⟨localFixedKernel (n := n) hη m w,
        localFixedKernel_nonneg hη m w⟩ : ℝ≥0))
    exact hKernel.subtype_mk
  change Integrable G ((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).withDensity
    fun w => ENNReal.ofNNReal (κ w))
  apply (integrable_withDensity_iff_integrable_smul
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) hκ).2
  convert hG using 1
  funext w
  rfl

theorem holderLeafKernel_support_bound {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) (w : EuclideanSpace ℝ (Fin n × Fin 2))
    (hw : localFixedKernel hη m w ≠ 0) :
    ‖w‖ ≤ localKernelRadius η m := by
  have hsupp : w ∈ tsupport (localFixedKernel hη m) :=
    subset_closure (Function.mem_support.mpr hw)
  change w ∈ tsupport ((localKernelBump hη m).normed
    (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) at hsupp
  rw [(localKernelBump hη m).tsupport_normed_eq] at hsupp
  simpa [localKernelBump, localKernelRadius, dist_eq_norm] using hsupp

theorem holderLeafKernel_support {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    ∀ᵐ w ∂holderLeafKernelMeasure (n := n) hη m,
      ‖w‖ ≤ localKernelRadius η m := by
  let κ : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ≥0 :=
    fun w => ⟨localFixedKernel hη m w, localFixedKernel_nonneg hη m w⟩
  have hKernel : Measurable (localFixedKernel (n := n) hη m) :=
    (localKernelBump (n := n) hη m).continuous_normed.measurable
  have hκ : Measurable κ := by
    change Measurable (fun w =>
      (⟨localFixedKernel (n := n) hη m w,
        localFixedKernel_nonneg hη m w⟩ : ℝ≥0))
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
    exact holderLeafKernel_support_bound hη m w hk
  change ∀ᵐ w ∂((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).withDensity
    fun w => ENNReal.ofNNReal (κ w)), ‖w‖ ≤ localKernelRadius η m
  rw [ae_withDensity_iff' (hκ.coe_nnreal_ennreal).aemeasurable]
  filter_upwards [] with w hden
  exact hbound w hden

theorem holderLeaf_shifted_sample_dist {n : ℕ}
    (z : EuclideanSpace ℂ (Fin n)) (w : EuclideanSpace ℝ (Fin n × Fin 2)) :
    dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) z = ‖w‖ := by
  have hzs : z = complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z) :=
    (complexToRealCoordinateEquiv.symm_apply_apply z).symm
  calc
    dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) z =
        dist (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w))
          (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z)) := by
      exact congrArg (fun q => dist
        (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) q) hzs
    _ = dist (complexToRealCoordinateEquiv z - w) (complexToRealCoordinateEquiv z) :=
      complexToRealCoordinateEquiv.symm.isometry.dist_eq _ _
    _ = ‖w‖ := by
      rw [dist_eq_norm]
      have hsub : (complexToRealCoordinateEquiv z - w) - complexToRealCoordinateEquiv z = -w := by
        abel
      rw [hsub, norm_neg]

theorem holderLeaf_holderOnWith_zero_complex
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

theorem holderLeaf_sample_deviation {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {α K : ℝ≥0} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hHolder : HolderBoundOn 0 α K U f) (m : ℕ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S) :
    ∀ᵐ w ∂holderLeafKernelMeasure (n := n) hη m,
      ‖(if complexToRealCoordinateEquiv.symm
          (complexToRealCoordinateEquiv z - w) ∈ U then
        f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0) - f z‖ ≤
        (K : ℝ) * localKernelRadius η m ^ (α : ℝ) := by
  have hsupp := holderLeafKernel_support (n := n) hη m
  have hr : localKernelRadius η m < η := by
    unfold localKernelRadius
    rw [div_lt_iff₀ (by positivity : 0 < 4 * ((m : ℝ) + 1))]
    nlinarith [hη]
  filter_upwards [hsupp] with w hw
  let y := complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  have hdist : dist y z = ‖w‖ := by
    dsimp [y]
    exact holderLeaf_shifted_sample_dist z w
  have hyU : y ∈ U := hCollar (by
    rw [Metric.mem_thickening_iff]
    refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
    rw [hdist]
    exact hw.trans_lt hr)
  have hzU : z ∈ U := hCollar (by
    rw [Metric.mem_thickening_iff]
    exact ⟨z, Metric.ball_subset_closedBall hz, by simpa using hη⟩)
  have hpair := holderLeaf_holderOnWith_zero_complex hHolder y hyU z hzU
  have hpair' : edist (f y) (f z) ≤
      ENNReal.ofReal ((K : ℝ) * dist y z ^ (α : ℝ)) := by
    have hrhs : (K : ENNReal) * edist y z ^ (α : ℝ) =
        ENNReal.ofReal ((K : ℝ) * dist y z ^ (α : ℝ)) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg
        (NNReal.coe_nonneg α)]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg K)]
    rw [← hrhs]
    exact hpair
  have hreal : dist (f y) (f z) ≤ (K : ℝ) * dist y z ^ (α : ℝ) :=
    (edist_le_ofReal (by positivity)).mp hpair'
  have hnorm : ‖f y - f z‖ ≤ (K : ℝ) * dist y z ^ (α : ℝ) := by
    simpa [dist_eq_norm] using hreal
  have hpow : dist y z ^ (α : ℝ) ≤ localKernelRadius η m ^ (α : ℝ) :=
    Real.rpow_le_rpow (dist_nonneg) (by rw [hdist]; exact hw) (NNReal.coe_nonneg α)
  change ‖(if y ∈ U then f y else 0) - f z‖ ≤ _
  rw [if_pos hyU]
  calc
    ‖f y - f z‖ ≤ (K : ℝ) * dist y z ^ (α : ℝ) := hnorm
    _ ≤ (K : ℝ) * localKernelRadius η m ^ (α : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (NNReal.coe_nonneg K)

theorem holderLeaf_deriv_kernel_sample_deviation {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (m : ℕ) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S)
    (v : EuclideanSpace ℝ (Fin n × Fin 2))
    {g : EuclideanSpace ℂ (Fin n) → ℂ}
    {M : ℝ}
    (hIncrement : ∀ h : EuclideanSpace ℂ (Fin n),
      ‖h‖ ≤ localKernelRadius η m → ‖g (z + h) - g z‖ ≤ M)
    (w : EuclideanSpace ℝ (Fin n × Fin 2))
    (hw : fderiv ℝ (localFixedKernel hη m) w v ≠ 0) :
    ‖(if complexToRealCoordinateEquiv.symm
        (complexToRealCoordinateEquiv z - w) ∈ U then
      g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0) -
      g z‖ ≤ M := by
  have hBundle := covarianceA2_complexDirection_q_bundle hη m
    (complexToRealCoordinateEquiv.symm v)
  have hq : ((fderiv ℝ (localFixedKernel hη m) w)
      (complexToRealCoordinateEquiv (complexToRealCoordinateEquiv.symm v)) : ℂ) ≠ 0 := by
    simpa using hw
  have hwNorm : ‖w‖ ≤ localKernelRadius η m := hBundle.2.2 w hq
  let y := complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  have hdist : dist y z = ‖w‖ := by
    dsimp [y]
    exact holderLeaf_shifted_sample_dist z w
  have hsample : y ∈ U := hCollar (by
    rw [Metric.mem_thickening_iff]
    refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
    rw [hdist]
    exact hwNorm.trans_lt (by
      unfold localKernelRadius
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))]
      nlinarith [hη]))
  have hshift : ‖y - z‖ ≤ localKernelRadius η m := by
    rw [← dist_eq_norm, hdist]
    exact hwNorm
  have hinc := hIncrement (y - z) hshift
  have hzy : z + (y - z) = y := by abel
  rw [hzy] at hinc
  change ‖(if y ∈ U then g y else 0) - g z‖ ≤ M
  rw [if_pos hsample]
  exact hinc

theorem holderLeaf_holder_increment_of_norm_le_radius {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {α K : ℝ≥0} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hHolder : HolderBoundOn 0 α K U f) (m : ℕ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S)
    (h : EuclideanSpace ℂ (Fin n)) (hh : ‖h‖ ≤ localKernelRadius η m) :
    ‖f (z + h) - f z‖ ≤ (K : ℝ) * localKernelRadius η m ^ (α : ℝ) := by
  have hr : localKernelRadius η m < η := by
    unfold localKernelRadius
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))]
    nlinarith [hη]
  have hzU : z ∈ U := hCollar (by
    rw [Metric.mem_thickening_iff]
    exact ⟨z, Metric.ball_subset_closedBall hz, by simpa using hη⟩)
  have hyU : z + h ∈ U := hCollar (by
    rw [Metric.mem_thickening_iff]
    refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
    rw [dist_eq_norm]
    have hsub : z + h - z = h := by abel
    rw [hsub]
    exact hh.trans_lt hr)
  have hpair := holderLeaf_holderOnWith_zero_complex hHolder (z + h) hyU z hzU
  have hdist : dist (z + h) z = ‖h‖ := by
    rw [dist_eq_norm]
    have hsub : z + h - z = h := by abel
    rw [hsub]
  have hpair' : edist (f (z + h)) (f z) ≤
      ENNReal.ofReal ((K : ℝ) * dist (z + h) z ^ (α : ℝ)) := by
    have hrhs : (K : ENNReal) * edist (z + h) z ^ (α : ℝ) =
        ENNReal.ofReal ((K : ℝ) * dist (z + h) z ^ (α : ℝ)) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg
        (NNReal.coe_nonneg α)]
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg K)]
    rw [← hrhs]
    exact hpair
  have hreal : dist (f (z + h)) (f z) ≤
      (K : ℝ) * dist (z + h) z ^ (α : ℝ) :=
    (edist_le_ofReal (by positivity)).mp hpair'
  have hnorm : ‖f (z + h) - f z‖ ≤
      (K : ℝ) * dist (z + h) z ^ (α : ℝ) := by
    simpa [dist_eq_norm] using hreal
  have hpow : dist (z + h) z ^ (α : ℝ) ≤
      localKernelRadius η m ^ (α : ℝ) :=
    Real.rpow_le_rpow dist_nonneg (by rw [hdist]; exact hh) (NNReal.coe_nonneg α)
  exact hnorm.trans (mul_le_mul_of_nonneg_left hpow (NNReal.coe_nonneg K))

theorem holderLeaf_deriv_kernel_holder_deviation {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {α K : ℝ≥0} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hHolder : HolderBoundOn 0 α K U f) (m : ℕ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S)
    (v : EuclideanSpace ℝ (Fin n × Fin 2))
    (w : EuclideanSpace ℝ (Fin n × Fin 2))
    (hw : fderiv ℝ (localFixedKernel hη m) w v ≠ 0) :
    ‖(if complexToRealCoordinateEquiv.symm
        (complexToRealCoordinateEquiv z - w) ∈ U then
      f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0) - f z‖ ≤
      (K : ℝ) * localKernelRadius η m ^ (α : ℝ) := by
  have hBundle := covarianceA2_complexDirection_q_bundle hη m
    (complexToRealCoordinateEquiv.symm v)
  have hq : ((fderiv ℝ (localFixedKernel hη m) w)
      (complexToRealCoordinateEquiv (complexToRealCoordinateEquiv.symm v)) : ℂ) ≠ 0 := by
    simpa using hw
  have hwNorm : ‖w‖ ≤ localKernelRadius η m := hBundle.2.2 w hq
  have hr : localKernelRadius η m < η := by
    unfold localKernelRadius
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))]
    nlinarith [hη]
  let y := complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  have hdist : dist y z = ‖w‖ := by
    dsimp [y]
    exact holderLeaf_shifted_sample_dist z w
  have hyU : y ∈ U := hCollar (by
    rw [Metric.mem_thickening_iff]
    refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
    rw [hdist]
    exact hwNorm.trans_lt hr)
  have hshift : ‖y - z‖ ≤ localKernelRadius η m := by
    rw [← dist_eq_norm, hdist]
    exact hwNorm
  have hinc := holderLeaf_holder_increment_of_norm_le_radius
    hη hCollar hHolder m z hz (y - z) hshift
  have hzy : z + (y - z) = y := by abel
  rw [hzy] at hinc
  change ‖(if y ∈ U then f y else 0) - f z‖ ≤ _
  rw [if_pos hyU]
  exact hinc

theorem holderLeaf_integrand_integrable {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (m : ℕ) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ Metric.ball c S) :
    Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
      localFixedKernel hη m w •
        (if complexToRealCoordinateEquiv.symm
          (complexToRealCoordinateEquiv z - w) ∈ U then
          f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0)) := by
  let K : Set (EuclideanSpace ℝ (Fin n × Fin 2)) :=
    Metric.closedBall 0 (localKernelRadius η m)
  let sample : EuclideanSpace ℝ (Fin n × Fin 2) → EuclideanSpace ℂ (Fin n) :=
    fun w => complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  have hK : IsCompact K := by
    simpa [K] using isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin n × Fin 2)) (localKernelRadius η m)
  have hKernel : ContinuousOn (localFixedKernel hη m) K :=
    (localKernelBump hη m).continuous_normed.continuousOn
  have hSample : ContinuousOn sample K := by
    apply Continuous.continuousOn
    dsimp [sample]
    fun_prop
  have hr : localKernelRadius η m < η := by
    unfold localKernelRadius
    rw [div_lt_iff₀ (by positivity : 0 < 4 * ((m : ℝ) + 1))]
    nlinarith [hη]
  have hIn : ∀ w ∈ K, sample w ∈ U := by
    intro w hw
    have hwNorm : ‖w‖ ≤ localKernelRadius η m := by
      simpa [K, dist_eq_norm] using hw
    have hthick : sample w ∈ Metric.thickening η (Metric.closedBall c S) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
      rw [holderLeaf_shifted_sample_dist]
      exact hwNorm.trans_lt hr
    exact hCollar hthick
  have hComp : ContinuousOn (fun w => f (sample w)) K := hf.comp hSample hIn
  have hCut : ContinuousOn (fun w => if sample w ∈ U then f (sample w) else 0) K := by
    apply hComp.congr
    intro w hw
    simp [hIn w hw]
  have hProd : ContinuousOn
      (fun w => localFixedKernel hη m w • (if sample w ∈ U then f (sample w) else 0)) K :=
    hKernel.smul hCut
  have hOn : IntegrableOn
      (fun w : EuclideanSpace ℝ (Fin n × Fin 2) => localFixedKernel hη m w •
        (if sample w ∈ U then f (sample w) else 0)) K
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
    hProd.integrableOn_compact (μ := volume) hK
  have hZero : ∀ w, w ∉ K → localFixedKernel hη m w = 0 := by
    intro w hw
    by_contra hne
    have hwNorm := holderLeafKernel_support_bound hη m w hne
    exact hw (by simpa [K, dist_eq_norm] using hwNorm)
  exact hOn.integrable_of_forall_notMem_eq_zero fun w hw => by
    simp [hZero w hw]

theorem holderLeaf_localFixedMollify_mean_deviation_of_center_increment {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η M : ℝ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hg : ContinuousOn g U) (_hM : 0 ≤ M) (m : ℕ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S)
    (hIncrement : ∀ h : EuclideanSpace ℂ (Fin n),
      ‖h‖ ≤ localKernelRadius η m → ‖g (z + h) - g z‖ ≤ M) :
    ‖localFixedMollify U hη m g z - g z‖ ≤ M := by
  let μ := holderLeafKernelMeasure (n := n) hη m
  let G : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ := fun w =>
    if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w) ∈ U then
      g (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0
  have : IsProbabilityMeasure μ := holderLeafKernelMeasure_probability (n := n) hη m
  have hGvol : Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
      localFixedKernel hη m w • G w) := by
    simpa [G] using holderLeaf_integrand_integrable hη hCollar hg m z hz
  have hG : Integrable G μ := by
    change Integrable G (holderLeafKernelMeasure (n := n) hη m)
    exact holderLeafKernelMeasure_integrable hη m G hGvol
  have hrep : localFixedMollify U hη m g z = ∫ w, G w ∂μ := by
    rw [localFixedMollify]
    symm
    rw [holderLeafKernelMeasure_integral]
  have hdev : ∀ᵐ w ∂μ, ‖G w - g z‖ ≤ M := by
    filter_upwards [holderLeafKernel_support (n := n) hη m] with w hw
    let y := complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
    have hyU : y ∈ U := hCollar (by
      rw [Metric.mem_thickening_iff]
      refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
      rw [holderLeaf_shifted_sample_dist]
      exact hw.trans_lt (by
        unfold localKernelRadius
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))]
        nlinarith [hη]))
    have hshift : ‖y - z‖ ≤ localKernelRadius η m := by
      rw [← dist_eq_norm, holderLeaf_shifted_sample_dist]
      exact hw
    have hinc := hIncrement (y - z) hshift
    have hzy : z + (y - z) = y := by abel
    rw [hzy] at hinc
    change ‖(if y ∈ U then g y else 0) - g z‖ ≤ M
    rw [if_pos hyU]
    exact hinc
  have hdiff : Integrable (fun w => G w - g z) μ := hG.sub (integrable_const _)
  have hmean : (∫ w, G w - g z ∂μ) = (∫ w, G w ∂μ) - g z := by
    rw [integral_sub hG (integrable_const _), integral_const]
    simp [probReal_univ]
  have hbound : ‖(∫ w, G w ∂μ) - g z‖ ≤ M := by
    rw [← hmean]
    calc
      ‖∫ w, G w - g z ∂μ‖ ≤ ∫ w, ‖G w - g z‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _w, M ∂μ := integral_mono_ae hdiff.norm (integrable_const _) hdev
      _ = M := by simp [probReal_univ]
  rw [hrep]
  exact hbound

theorem holderLeaf_localFixedMollify_mean_deviation_of_holder {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} {α K : ℝ≥0} {f : EuclideanSpace ℂ (Fin n) → ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (hHolder : HolderBoundOn 0 α K U f) (m : ℕ)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S) :
    ‖localFixedMollify U hη m f z - f z‖ ≤
      (K : ℝ) * localKernelRadius η m ^ (α : ℝ) := by
  let μ := holderLeafKernelMeasure (n := n) hη m
  let G : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ := fun w =>
    if complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w) ∈ U then
      f (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) else 0
  have : IsProbabilityMeasure μ := holderLeafKernelMeasure_probability (n := n) hη m
  have hGvol : Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
      localFixedKernel hη m w • G w) := by
    simpa [G] using holderLeaf_integrand_integrable hη hCollar hf m z hz
  have hG : Integrable G μ := by
    change Integrable G (holderLeafKernelMeasure (n := n) hη m)
    exact holderLeafKernelMeasure_integrable hη m G hGvol
  have hrep : localFixedMollify U hη m f z = ∫ w, G w ∂μ := by
    rw [localFixedMollify]
    symm
    rw [holderLeafKernelMeasure_integral]
  have hdev : ∀ᵐ w ∂μ,
      ‖G w - f z‖ ≤ (K : ℝ) * localKernelRadius η m ^ (α : ℝ) := by
    simpa [G, μ] using holderLeaf_sample_deviation hη hCollar hHolder m z hz
  have hdiff : Integrable (fun w => G w - f z) μ := hG.sub (integrable_const _)
  have hmean : (∫ w, G w - f z ∂μ) = (∫ w, G w ∂μ) - f z := by
    rw [integral_sub hG (integrable_const _), integral_const]
    simp [probReal_univ]
  have hbound : ‖(∫ w, G w ∂μ) - f z‖ ≤
      (K : ℝ) * localKernelRadius η m ^ (α : ℝ) := by
    rw [← hmean]
    calc
      ‖∫ w, G w - f z ∂μ‖ ≤ ∫ w, ‖G w - f z‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _w, (K : ℝ) * localKernelRadius η m ^ (α : ℝ) ∂μ :=
        integral_mono_ae hdiff.norm (integrable_const _) hdev
      _ = (K : ℝ) * localKernelRadius η m ^ (α : ℝ) := by simp [probReal_univ]
  rw [hrep]
  exact hbound

end CalabiYau.Schauder
