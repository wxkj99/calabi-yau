module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.Basic

/-!
# Coefficient smoothing on a compact collar

This is source-free: positivity of the same fixed kernel preserves the Hermitian cone and
ellipticity. Coefficient Hölder control is supplied separately by positive averaging.
-/

@[expose] public section

open Set Filter Matrix
open scoped ContDiff NNReal Topology

namespace CalabiYau.Schauder

open MeasureTheory
open scoped ComplexConjugate

private theorem localFixedKernel_sample_mem_collar {n : ℕ}
    {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ} {U : Set (EuclideanSpace ℂ (Fin n))}
    (m : ℕ) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S)
    (w : EuclideanSpace ℝ (Fin n × Fin 2))
    (hw : w ∈ Metric.closedBall 0 (localKernelRadius η m)) :
    complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w) ∈ U := by
  apply hCollar
  rw [Metric.mem_thickening_iff]
  refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
  let e := complexToRealCoordinateEquiv (n := n)
  calc
    dist (e.symm (e z - w)) z = dist (e.symm (e z - w)) (e.symm (e z)) := by
      rw [e.symm_apply_apply]
    _ = dist (e z - w) (e z) := e.symm.isometry.dist_eq _ _
    _ = dist w 0 := by
      simp [dist_eq_norm]
    _ ≤ localKernelRadius η m := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    _ < η := by
      unfold localKernelRadius
      have hden : 1 < 4 * ((m : ℝ) + 1) := by
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith
      exact div_lt_self hη hden

private theorem localFixedCoefficientEntry_integrable {n : ℕ}
    {η : ℝ} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {S : ℝ}
    (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hA₀ : ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U)
    (m : ℕ) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S)
    (j l : Fin n) :
    Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) ↦
      (localFixedKernel hη m w : ℂ) *
        A (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)) j l)
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  classical
  let K : Set (EuclideanSpace ℝ (Fin n × Fin 2)) :=
    Metric.closedBall 0 (localKernelRadius η m)
  let sample : EuclideanSpace ℝ (Fin n × Fin 2) → EuclideanSpace ℂ (Fin n) :=
    fun w ↦ complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  let kernel : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := localFixedKernel hη m
  have hK : IsCompact K := by
    simpa [K] using (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n × Fin 2))
      (localKernelRadius η m))
  have hKernel : ContinuousOn kernel K := by
    have hsmooth : ContDiff ℝ ∞ kernel := by
      simpa [kernel, localFixedKernel] using (localKernelBump hη m).contDiff_normed
    exact hsmooth.continuous.continuousOn
  have hSample : ContinuousOn sample K := by
    fun_prop
  have hIn : ∀ w ∈ K, sample w ∈ U := by
    intro w hw
    exact localFixedKernel_sample_mem_collar m hη hCollar z hz w (by simpa [K] using hw)
  have hSupport : ∀ w, kernel w ≠ 0 → sample w ∈ U := by
    intro w hw
    have hmem : w ∈ Function.support kernel := hw
    have hball : w ∈ Metric.ball 0 (localKernelRadius η m) := by
      change w ∈ Function.support ((localKernelBump hη m).normed volume) at hmem
      rw [(localKernelBump hη m).support_normed_eq] at hmem
      exact hmem
    exact hIn w (Metric.ball_subset_closedBall hball)
  have hZero : ∀ w, w ∉ K → kernel w = 0 := by
    intro w hw
    by_contra hne
    have hmem : w ∈ Function.support kernel := hne
    change w ∈ Function.support ((localKernelBump hη m).normed volume) at hmem
    rw [(localKernelBump hη m).support_normed_eq] at hmem
    exact hw (Metric.ball_subset_closedBall hmem)
  have hComp : ContinuousOn (fun w ↦ A (sample w) j l) K := by
    exact (hA₀ j l).continuousOn.comp hSample hIn
  have hCut : ContinuousOn
      (fun w ↦ if sample w ∈ U then A (sample w) j l else 0) K := by
    apply hComp.congr
    intro w hw
    simp [hIn w hw]
  have hProd : ContinuousOn
      (fun w ↦ kernel w • (if sample w ∈ U then A (sample w) j l else 0)) K :=
    hKernel.smul hCut
  have hCutInt : Integrable
      (fun w ↦ kernel w • (if sample w ∈ U then A (sample w) j l else 0))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
    have hOn : IntegrableOn
        (fun w ↦ kernel w • (if sample w ∈ U then A (sample w) j l else 0)) K
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
      hProd.integrableOn_compact (μ := volume) hK
    exact hOn.integrable_of_forall_notMem_eq_zero fun w hw ↦ by
      simp [hZero w (by simpa [K] using hw)]
  have hUncut : Integrable
      (fun w ↦ (kernel w : ℂ) * A (sample w) j l)
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
    apply hCutInt.congr
    filter_upwards [] with w
    have heq : kernel w • (if sample w ∈ U then A (sample w) j l else 0) =
        kernel w • A (sample w) j l := by
      by_cases hw : kernel w = 0
      · simp [hw]
      · simp [hSupport w hw]
    simpa only [Complex.real_smul] using heq
  simpa [kernel, sample] using hUncut

private theorem star_dotProduct_weightedMatrixIntegral {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    (w : α → ℝ) (A : α → Matrix ι ι ℂ) (v : ι → ℂ)
    (B : Matrix ι ι ℂ)
    (hentry : ∀ i j, Integrable (fun x ↦ (w x : ℂ) * A x i j) μ)
    (hB : ∀ i j, B i j = ∫ x, (w x : ℂ) * A x i j ∂μ) :
    dotProduct (star v) (Matrix.mulVec B v) =
      ∫ x, (w x : ℂ) * dotProduct (star v) (Matrix.mulVec (A x) v) ∂μ := by
  classical
  have hterm (i j : ι) :
      Integrable (fun x ↦ (w x : ℂ) * (star (v i) * A x i j * v j)) μ := by
    have h := (hentry i j).const_mul (star (v i))
    have h' := h.mul_const (v j)
    apply h'.congr
    filter_upwards [] with x
    ring
  have hrow (j : ι) :
      Integrable (fun x ↦ ∑ i, (w x : ℂ) * (star (v i) * A x i j * v j)) μ := by
    exact integrable_finsetSum Finset.univ (by intro i hi; exact hterm i j)
  have hsummand (i j : ι) :
      star (v i) * B i j * v j =
        ∫ x, (w x : ℂ) * (star (v i) * A x i j * v j) ∂μ := by
    rw [hB i j]
    calc
      star (v i) * (∫ x, (w x : ℂ) * A x i j ∂μ) * v j =
          star (v i) * ((∫ x, (w x : ℂ) * A x i j ∂μ) * v j) := by ring
      _ = star (v i) * (∫ x, ((w x : ℂ) * A x i j) * v j ∂μ) := by
        rw [← integral_mul_const]
      _ = ∫ x, star (v i) * (((w x : ℂ) * A x i j) * v j) ∂μ := by
        rw [← integral_const_mul]
      _ = ∫ x, (w x : ℂ) * (star (v i) * A x i j * v j) ∂μ := by
        congr 1
        funext x
        ring
  have hExpand :
      (∫ x, (w x : ℂ) * (∑ j, ∑ i, star (v i) * A x i j * v j) ∂μ) =
        ∑ j, ∑ i, ∫ x, (w x : ℂ) * (star (v i) * A x i j * v j) ∂μ := by
    calc
      _ = ∫ x, ∑ j, ∑ i, (w x : ℂ) * (star (v i) * A x i j * v j) ∂μ := by
        congr 1
        funext x
        simp only [Finset.mul_sum]
      _ = ∑ j, ∫ x, ∑ i, (w x : ℂ) * (star (v i) * A x i j * v j) ∂μ := by
        rw [integral_finsetSum Finset.univ (fun j hj ↦ hrow j)]
      _ = ∑ j, ∑ i, ∫ x, (w x : ℂ) * (star (v i) * A x i j * v j) ∂μ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_finsetSum Finset.univ (fun i hi ↦ hterm i j)]
  rw [Matrix.dot_mulVec_eq_sum_sum]
  calc
    _ = ∑ j, ∑ i, ∫ x, (w x : ℂ) * (star (v i) * A x i j * v j) ∂μ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      exact hsummand i j
    _ = ∫ x, (w x : ℂ) * (∑ j, ∑ i, star (v i) * A x i j * v j) ∂μ := hExpand.symm
    _ = ∫ x, (w x : ℂ) * dotProduct (star v) (Matrix.mulVec (A x) v) ∂μ := by
      congr 1
      funext x
      rw [Matrix.dot_mulVec_eq_sum_sum]
      simp

private theorem weightedMatrixQuadraticForm_integrable {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    (w : α → ℝ) (A : α → Matrix ι ι ℂ) (v : ι → ℂ)
    (hentry : ∀ i j, Integrable (fun x ↦ (w x : ℂ) * A x i j) μ) :
    Integrable (fun x ↦ (w x : ℂ) * dotProduct (star v) (Matrix.mulVec (A x) v)) μ := by
  classical
  have hterm (i j : ι) :
      Integrable (fun x ↦ (w x : ℂ) * (star (v i) * A x i j * v j)) μ := by
    have h := (hentry i j).const_mul (star (v i))
    have h' := h.mul_const (v j)
    apply h'.congr
    filter_upwards [] with x
    ring
  have hrow (j : ι) :
      Integrable (fun x ↦ ∑ i, (w x : ℂ) * (star (v i) * A x i j * v j)) μ :=
    integrable_finsetSum Finset.univ (by intro i hi; exact hterm i j)
  have hdouble : Integrable
      (fun x ↦ ∑ j, ∑ i, (w x : ℂ) * (star (v i) * A x i j * v j)) μ :=
    integrable_finsetSum Finset.univ (by intro j hj; exact hrow j)
  apply hdouble.congr
  filter_upwards [] with x
  rw [Matrix.dot_mulVec_eq_sum_sum]
  simp only [Finset.mul_sum]
  simp

private theorem re_star_dotProduct_weightedMatrixIntegral {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    (w : α → ℝ) (A : α → Matrix ι ι ℂ) (v : ι → ℂ)
    (B : Matrix ι ι ℂ)
    (hentry : ∀ i j, Integrable (fun x ↦ (w x : ℂ) * A x i j) μ)
    (hB : ∀ i j, B i j = ∫ x, (w x : ℂ) * A x i j ∂μ) :
    (dotProduct (star v) (Matrix.mulVec B v)).re =
      ∫ x, w x * (dotProduct (star v) (Matrix.mulVec (A x) v)).re ∂μ := by
  rw [star_dotProduct_weightedMatrixIntegral w A v B hentry hB]
  change RCLike.re
    (∫ x, (w x : ℂ) * dotProduct (star v) (Matrix.mulVec (A x) v) ∂μ) = _
  rw [← integral_re (weightedMatrixQuadraticForm_integrable w A v hentry)]
  simp

private theorem weightedAverage_elliptic_lower {n : ℕ} {lam : NNReal}
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (w : α → ℝ) (φ : α → EuclideanSpace ℂ (Fin n))
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (v : Fin n → ℂ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hEll : IsUniformlyEllipticOn A lam U)
    (hSupport : ∀ᵐ x ∂μ, w x ≠ 0 → φ x ∈ U)
    (hentry : ∀ i j, Integrable (fun x ↦ (w x : ℂ) * A (φ x) i j) μ)
    (hB : ∀ i j, B i j = ∫ x, (w x : ℂ) * A (φ x) i j ∂μ)
    (hw : Integrable w μ) (hweight : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hmass : ∫ x, w x ∂μ = 1) :
    (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤
      RCLike.re (dotProduct (star v) (Matrix.mulVec B v)) := by
  let q : α → ℂ := fun x ↦ dotProduct (star v) (Matrix.mulVec (A (φ x)) v)
  have hqComplex : Integrable (fun x ↦ (w x : ℂ) * q x) μ := by
    exact weightedMatrixQuadraticForm_integrable w (fun x ↦ A (φ x)) v hentry
  have hqReal : Integrable (fun x ↦ w x * RCLike.re (q x)) μ := by
    have h := hqComplex.re
    apply h.congr
    filter_upwards [] with x
    simp [q]
  have hbound : ∀ᵐ x ∂μ,
      w x ≠ 0 → (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ RCLike.re (q x) := by
    filter_upwards [hSupport] with x hx
    exact fun hwx ↦ (hEll (φ x) (hx hwx)).2 v
  have hmul : ∀ᵐ x ∂μ,
      w x * ((lam : ℝ) * ∑ i, ‖v i‖ ^ 2) ≤ w x * RCLike.re (q x) := by
    filter_upwards [hweight, hbound] with x hwx hbx
    by_cases hz : w x = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (hbx hz) hwx
  have hmono := integral_mono_ae
    (hw.mul_const ((lam : ℝ) * ∑ i, ‖v i‖ ^ 2)) hqReal hmul
  calc
    (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 =
        ∫ x, w x * ((lam : ℝ) * ∑ i, ‖v i‖ ^ 2) ∂μ := by
      rw [integral_mul_const, hmass]
      simp
    _ ≤ ∫ x, w x * RCLike.re (q x) ∂μ := hmono
    _ = RCLike.re (dotProduct (star v) (Matrix.mulVec B v)) := by
      simpa [q] using
        (re_star_dotProduct_weightedMatrixIntegral w (fun x ↦ A (φ x)) v B hentry hB).symm

private theorem localFixedCoefficientSeq_ellipticOn {n : ℕ}
    {lam : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (hη : 0 < η) (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hA₀ : ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U)
    (hEll : IsUniformlyEllipticOn A lam U) :
    ∀ m, IsUniformlyEllipticOn (localFixedCoefficientSeq U hη A m) (lam / 2)
      (Metric.ball c S) := by
  classical
  intro m z hz
  let sample : EuclideanSpace ℝ (Fin n × Fin 2) → EuclideanSpace ℂ (Fin n) :=
    fun w ↦ complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - w)
  let kernel : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := localFixedKernel hη m
  let B : Matrix (Fin n) (Fin n) ℂ := localFixedCoefficientSeq U hη A m z
  have hSupport : ∀ᵐ w : EuclideanSpace ℝ (Fin n × Fin 2) ∂volume,
      kernel w ≠ 0 → sample w ∈ U := by
    filter_upwards [] with w hw
    have hmem : w ∈ Function.support kernel := hw
    change w ∈ Function.support ((localKernelBump hη m).normed volume) at hmem
    rw [(localKernelBump hη m).support_normed_eq] at hmem
    have hw' : w ∈ Metric.closedBall 0 (localKernelRadius η m) :=
      Metric.ball_subset_closedBall hmem
    exact localFixedKernel_sample_mem_collar m hη hCollar z hz w hw'
  have hentry : ∀ i j,
      Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) ↦
        (kernel w : ℂ) * A (sample w) i j) volume := by
    intro i j
    simpa [kernel, sample] using
      localFixedCoefficientEntry_integrable hη hCollar A hA₀ m z hz i j
  have hB : ∀ i j, B i j =
      ∫ w : EuclideanSpace ℝ (Fin n × Fin 2),
        (kernel w : ℂ) * A (sample w) i j ∂volume := by
    intro i j
    change localFixedMollify U hη m (fun y ↦ A y i j) z = _
    unfold localFixedMollify
    rw [integral_congr_ae]
    filter_upwards [hSupport] with w hw
    have heq : kernel w • (if sample w ∈ U then A (sample w) i j else 0) =
        kernel w • A (sample w) i j := by
      by_cases hzero : kernel w = 0
      · simp [hzero]
      · simp [hw hzero]
    simpa [kernel, sample, Complex.real_smul] using heq
  have hMatrixHerm : B.IsHermitian := by
    change Matrix.conjTranspose B = B
    ext i j
    rw [Matrix.conjTranspose_apply, hB i j, hB j i]
    change conj (∫ w, (kernel w : ℂ) * A (sample w) j i ∂volume) = _
    rw [← integral_conj]
    have hpoint : ∀ᵐ w : EuclideanSpace ℝ (Fin n × Fin 2) ∂volume,
        star ((kernel w : ℂ) * A (sample w) j i) =
          (kernel w : ℂ) * A (sample w) i j := by
      filter_upwards [hSupport] with w hw
      by_cases hzero : kernel w = 0
      · simp [hzero]
      · have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ M i j)
          (hEll (sample w) (hw hzero)).1
        have h' : star (A (sample w) j i) = A (sample w) i j := by
          simpa only [Matrix.conjTranspose_apply] using h
        simp [h']
    exact integral_congr_ae hpoint
  have hLower : ∀ v : Fin n → ℂ,
      (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤
        RCLike.re (dotProduct (star v) (Matrix.mulVec B v)) := by
    intro v
    apply weightedAverage_elliptic_lower kernel sample A U v B hEll hSupport hentry hB
      (by
        simpa [kernel, localFixedKernel] using (localKernelBump hη m).integrable_normed)
      (by filter_upwards [] with w; exact localFixedKernel_nonneg hη m w)
      (by simpa [kernel] using localFixedKernel_integral hη m)
  refine ⟨?_, ?_⟩
  · simpa [B] using hMatrixHerm
  · intro v
    have h := hLower v
    have hLam : ((lam / 2 : ℝ≥0) : ℝ) ≤ (lam : ℝ) := by
      have hpos : (0 : ℝ) ≤ (lam : ℝ) := NNReal.coe_nonneg _
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith
    have hnorm : 0 ≤ ∑ i, ‖v i‖ ^ 2 := by positivity
    calc
      ((lam / 2 : ℝ≥0) : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤
          (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 := mul_le_mul_of_nonneg_right hLam hnorm
      _ ≤ RCLike.re (dotProduct (star v) (Matrix.mulVec B v)) := h

set_option maxHeartbeats 1000000 in
private theorem localFixedCoefficientEntry_contDiffOn {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {S η : ℝ} (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hA₀ : ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U)
    (m : ℕ) (j l : Fin n) :
    ContDiffOn ℝ ∞ (fun z ↦ localFixedMollify U hη m (fun y ↦ A y j l) z)
      (Metric.ball c S) := by
  classical
  let e := complexToRealCoordinateEquiv (n := n)
  let r := localKernelRadius η m
  let K₁ : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall c S
  let K₂ : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := Metric.closedBall 0 r
  let K : Set (EuclideanSpace ℝ (Fin n × Fin 2)) :=
    (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℝ (Fin n × Fin 2) ↦ e p.1 - p.2) '' (K₁ ×ˢ K₂)
  let g : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ := fun x ↦
    if x ∈ K then A (e.symm x) j l else 0
  let k : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ := localFixedKernel hη m
  have hr : r < η := by
    dsimp [r, localKernelRadius]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hd : 1 < 4 * ((m : ℝ) + 1) := by nlinarith
    exact div_lt_self hη hd
  have hK₁ : IsCompact K₁ := by simpa [K₁] using isCompact_closedBall c S
  have hK₂ : IsCompact K₂ := by simpa [K₂] using isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n × Fin 2)) r
  have hmap : Continuous (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℝ (Fin n × Fin 2) ↦ e p.1 - p.2) := by fun_prop
  have hK : IsCompact K := by
    simpa [K] using (hK₁.prod hK₂).image hmap
  have hKsample : ∀ x ∈ K, e.symm x ∈ U := by
    intro x hx
    rcases hx with ⟨⟨z, w⟩, ⟨hz, hw⟩, rfl⟩
    apply hCollar
    rw [Metric.mem_thickening_iff]
    refine ⟨z, hz, ?_⟩
    calc
      dist (e.symm (e z - w)) z = dist (e.symm (e z - w)) (e.symm (e z)) := by
        rw [e.symm_apply_apply]
      _ = dist (e z - w) (e z) := e.symm.isometry.dist_eq _ _
      _ = dist w 0 := by simp [dist_eq_norm]
      _ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm, K₂] using hw
      _ < η := hr
  have hgCont : ContinuousOn g K := by
    apply ((hA₀ j l).continuousOn.comp e.symm.continuous.continuousOn hKsample).congr
    intro x hx
    simp [g, hx]
  have hgOn : IntegrableOn g K (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
    hgCont.integrableOn_compact (μ := volume) hK
  have hg : Integrable g (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
    hgOn.integrable_of_forall_notMem_eq_zero fun x hx ↦ by simp [g, hx]
  have hkSupport : HasCompactSupport k := by
    change HasCompactSupport ((localKernelBump hη m).normed volume)
    exact (localKernelBump hη m).hasCompactSupport_normed
  have hkSmooth : ContDiff ℝ ∞ k := by
    change ContDiff ℝ ∞ ((localKernelBump hη m).normed volume)
    exact (localKernelBump hη m).contDiff_normed
  let L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  have hconv : ContDiff ℝ ∞ (MeasureTheory.convolution k g L volume) :=
    hkSupport.contDiff_convolution_left L hkSmooth hg.locallyIntegrable
  have hcomp : ContDiff ℝ ∞ (fun z ↦ MeasureTheory.convolution k g L volume (e z)) := by
    exact hconv.comp e.contDiff
  apply hcomp.contDiffOn.congr
  intro z hz
  unfold localFixedMollify MeasureTheory.convolution
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hzero : k w = 0
  · simp [k, hzero]
  · have hmem : w ∈ Function.support k := hzero
    change w ∈ Function.support ((localKernelBump hη m).normed volume) at hmem
    rw [(localKernelBump hη m).support_normed_eq] at hmem
    have hxK : e z - w ∈ K := by
      refine ⟨(z, w), ⟨Metric.ball_subset_closedBall hz, ?_⟩, rfl⟩
      have hball : w ∈ Metric.ball 0 (localKernelRadius η m) := by
        simpa [localKernelBump] using hmem
      simpa [K₂, r] using Metric.ball_subset_closedBall hball
    have hxU : e.symm (e z - w) ∈ U :=
      localFixedKernel_sample_mem_collar m hη hCollar z hz w (by
        have hball : w ∈ Metric.ball 0 (localKernelRadius η m) := by
          simpa [localKernelBump] using hmem
        exact Metric.ball_subset_closedBall hball)
    have hgEq : g (e z - w) = A (e.symm (e z - w)) j l := by simp [g, hxK]
    have hsample : e.symm (e z - w) = z - e.symm w := by simp
    have hxU' : z - e.symm w ∈ U := by rw [← hsample]; exact hxU
    change k w • (if e.symm (e z - w) ∈ U then A (e.symm (e z - w)) j l else 0) =
      k w • g (e z - w)
    rw [hgEq]
    simp [hxU']

private theorem localFixedCoefficientSeq_regular_smooth_and_tendsto {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {R S η : ℝ} {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (_hR : 0 < R) (hRS : R < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hA₀ : ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U) :
    (∀ m j l, ContDiffOn ℝ ∞ (fun z ↦ localFixedCoefficientSeq U hη A m z j l)
      (Metric.ball c S)) ∧
    (∀ j l, TendstoLocallyUniformlyOn (fun m z ↦ localFixedCoefficientSeq U hη A m z j l)
      (fun z ↦ A z j l) atTop (Metric.ball c R)) := by
  refine ⟨?_, ?_⟩
  · intro m j l
    exact localFixedCoefficientEntry_contDiffOn hη hCollar A hA₀ m j l
  · intro j l
    classical
    let e := complexToRealCoordinateEquiv (n := n)
    let X := EuclideanSpace ℝ (Fin n × Fin 2)
    let g : X → ℂ := fun x ↦
      if e.symm x ∈ U then A (e.symm x) j l else 0
    have hden : Tendsto (fun m : ℕ ↦ 4 * ((m : ℝ) + 1)) atTop atTop := by
      refine tendsto_atTop_mono' atTop (Eventually.of_forall fun m ↦ ?_)
        tendsto_natCast_atTop_atTop
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    have hr : Tendsto (fun m : ℕ ↦ localKernelRadius η m) atTop (𝓝 0) := by
      change Tendsto (fun m : ℕ ↦ η / (4 * ((m : ℝ) + 1))) atTop (𝓝 0)
      exact tendsto_const_nhds.div_atTop hden
    have hs : IsOpen (e.symm ⁻¹' U) := by
      exact hU.preimage e.symm.continuous
    have hcoeff_cont : ContinuousOn (fun z ↦ A z j l) U :=
      (hA₀ j l).continuousOn
    have hmeas : Measurable g := by
      have hc : ContinuousOn (fun x : X ↦ A (e.symm x) j l) (e.symm ⁻¹' U) :=
        hcoeff_cont.comp e.symm.continuous.continuousOn (by intro x hx; exact hx)
      have heq : g = (e.symm ⁻¹' U).piecewise (fun x ↦ A (e.symm x) j l) (fun _ ↦ 0) := by
        funext x
        by_cases hx : e.symm x ∈ U <;> simp [g, hx]
      rw [heq]
      exact hc.measurable_piecewise continuousOn_const hs.measurableSet
    have hA_cont (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
        ContinuousAt (fun y ↦ A y j l) z :=
      hcoeff_cont.continuousAt (hU.mem_nhds hz)
    have hconv_local : ∀ z ∈ Metric.ball c R,
        Tendsto (fun p : ℕ × EuclideanSpace ℂ (Fin n) ↦
          localFixedCoefficientSeq U hη A p.1 p.2 j l)
          (atTop ×ˢ 𝓝 z) (𝓝 (A z j l)) := by
      intro z hz
      have hzS : z ∈ Metric.ball c S := Metric.ball_subset_ball hRS.le hz
      have hzC : z ∈ Metric.closedBall c S := Metric.ball_subset_closedBall hzS
      have hzU : z ∈ U := hCollar (Metric.mem_thickening_iff.mpr
        ⟨z, hzC, by simp [hη]⟩)
      let x₀ : X := e z
      have hx₀ : e.symm x₀ ∈ U := by simpa [x₀] using hzU
      have hgEq : g =ᶠ[𝓝 x₀] (fun x : X ↦ A (e.symm x) j l) := by
        filter_upwards [hs.mem_nhds hx₀] with x hx
        have hx' : e.symm x ∈ U := by simpa using hx
        simp [g, hx']
      have hgAt : Tendsto g (𝓝 x₀) (𝓝 (A z j l)) := by
        have hcont : Tendsto (fun x : X ↦ A (e.symm x) j l) (𝓝 x₀) (𝓝 (A z j l)) := by
          have he : Tendsto e.symm (𝓝 (e z)) (𝓝 z) := by
            simpa only [e.symm_apply_apply] using
              (e.symm.continuous.continuousAt (x := e z)).tendsto
          have h := (hA_cont z hzU).tendsto.comp he
          simpa [x₀, Function.comp_def] using h
        exact hcont.congr' hgEq.symm
      let φ : (ℕ × EuclideanSpace ℂ (Fin n)) → ContDiffBump (0 : X) :=
        fun p ↦ localKernelBump hη p.1
      let k : (ℕ × EuclideanSpace ℂ (Fin n)) → X := fun p ↦ e p.2
      have hφ : Tendsto (fun p ↦ (φ p).rOut) (atTop ×ˢ 𝓝 z) (𝓝 0) := by
        have hfst : Tendsto (fun p : ℕ × EuclideanSpace ℂ (Fin n) ↦ p.1)
            (atTop ×ˢ 𝓝 z) atTop := tendsto_fst
        change Tendsto (fun p : ℕ × EuclideanSpace ℂ (Fin n) ↦
          localKernelRadius η p.1) (atTop ×ˢ 𝓝 z) (𝓝 0)
        exact hr.comp hfst
      have hk : Tendsto k (atTop ×ˢ 𝓝 z) (𝓝 x₀) := by
        have hsnd : Tendsto (fun p : ℕ × EuclideanSpace ℂ (Fin n) ↦ p.2)
            (atTop ×ˢ 𝓝 z) (𝓝 z) := tendsto_snd (f := atTop) (g := 𝓝 z)
        have h := (e.continuous.tendsto z).comp hsnd
        simpa [k, x₀, Function.comp_def] using h
      have hcg : Tendsto (fun p : (ℕ × EuclideanSpace ℂ (Fin n)) × X ↦ g p.2)
          ((atTop ×ˢ 𝓝 z) ×ˢ 𝓝 x₀) (𝓝 (A z j l)) := by
        exact hgAt.comp tendsto_snd
      have hmeas' : AEStronglyMeasurable g
          (volume : Measure X) := hmeas.aestronglyMeasurable
      let L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
      have hcv := ContDiffBump.convolution_tendsto_right
        (μ := (volume : Measure X)) hφ
        (Eventually.of_forall fun _ ↦ hmeas') hcg hk
      have hconvEq (p : ℕ × EuclideanSpace ℂ (Fin n)) :
          localFixedCoefficientSeq U hη A p.1 p.2 j l =
            MeasureTheory.convolution ((φ p).normed (volume : Measure X)) g L
              (volume : Measure X) (k p) := by
        change localFixedMollify U hη p.1 (fun y ↦ A y j l) p.2 = _
        rw [MeasureTheory.convolution_def]
        rfl
      exact hcv.congr' (Filter.Eventually.of_forall hconvEq)
    rw [(Metric.isOpen_ball : IsOpen (Metric.ball c R)).tendstoLocallyUniformlyOn_iff_forall_tendsto]
    intro z hz
    have hzS : z ∈ Metric.ball c S := Metric.ball_subset_ball hRS.le hz
    have hzC : z ∈ Metric.closedBall c S := Metric.ball_subset_closedBall hzS
    have hzU : z ∈ U := hCollar (Metric.mem_thickening_iff.mpr
      ⟨z, hzC, by simp [hη]⟩)
    have hA : Tendsto (fun p : ℕ × EuclideanSpace ℂ (Fin n) ↦ A p.2 j l)
        (atTop ×ˢ 𝓝 z) (𝓝 (A z j l)) := by
      exact (hA_cont z hzU).tendsto.comp tendsto_snd
    have hseq : Tendsto (fun p : ℕ × EuclideanSpace ℂ (Fin n) ↦
        localFixedCoefficientSeq U hη A p.1 p.2 j l)
        (atTop ×ˢ 𝓝 z) (𝓝 (A z j l)) := hconv_local z hz
    exact (hA.prodMk_nhds hseq).mono_right (nhds_le_uniformity (A z j l))

/-- Canonical coefficient rows are smooth and elliptic, and converge locally to the input. -/
theorem localFixedCoefficientSeq_regular {n : ℕ}
    {lam : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {R S η : ℝ}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hR : 0 < R) (hRS : R < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hA₀ : ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U)
    (hEll : IsUniformlyEllipticOn A lam U) :
    (∀ m j l, ContDiffOn ℝ ∞ (fun z ↦ localFixedCoefficientSeq U hη A m z j l)
      (Metric.ball c S)) ∧
    (∀ m, IsUniformlyEllipticOn (localFixedCoefficientSeq U hη A m) (lam / 2)
      (Metric.ball c S)) ∧
    (∀ j l, TendstoLocallyUniformlyOn (fun m z ↦ localFixedCoefficientSeq U hη A m z j l)
      (fun z ↦ A z j l) atTop (Metric.ball c R)) := by
  have hRest := localFixedCoefficientSeq_regular_smooth_and_tendsto
    hU hR hRS hη hCollar hA₀
  exact ⟨hRest.1, localFixedCoefficientSeq_ellipticOn hη hCollar hA₀ hEll, hRest.2⟩

end CalabiYau.Schauder
