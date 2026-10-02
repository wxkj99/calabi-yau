module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.Basic

/-!
# Hölder bounds under fixed positive averaging

The kernel has mass one, and every shifted point lies in the source collar. In particular this
statement controls both the value part and the seminorm part of `HolderBoundOn 0`.
-/

@[expose] public section

open Set Filter
open MeasureTheory ContinuousLinearMap
open scoped ContDiff NNReal Topology Convolution

namespace CalabiYau.Schauder

private theorem holderBoundOn_zero_iff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α B : ℝ≥0} {s : Set E} {f : E → F} :
    HolderBoundOn 0 α B s f ↔ (∀ z ∈ s, ‖f z‖ ≤ B) ∧ HolderOnWith B α f s := by
  constructor
  · intro hf
    refine ⟨fun z hz ↦ ?_, ?_⟩
    · simpa only [norm_iteratedFDeriv_zero] using hf.1 0 le_rfl z hz
    · intro x hx y hy
      have h := hf.2 x hx y hy
      rw [iteratedFDeriv_zero_eq_comp] at h
      exact ((continuousMultilinearCurryFin0 ℝ E F).symm.edist_map (f x) (f y)) ▸ h
  · rintro ⟨hNorm, hHolder⟩
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have : j = 0 := by omega
      subst j
      simpa only [norm_iteratedFDeriv_zero] using hNorm z hz
    · rw [iteratedFDeriv_zero_eq_comp]
      intro x hx y hy
      change edist ((continuousMultilinearCurryFin0 ℝ E F).symm (f x))
        ((continuousMultilinearCurryFin0 ℝ E F).symm (f y)) ≤ _
      rw [(continuousMultilinearCurryFin0 ℝ E F).symm.edist_map]
      exact hHolder x hx y hy

private theorem localHolderSampleMem {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ} (_hS : 0 < S) (_hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S)
    (w : EuclideanSpace ℝ (Fin n × Fin 2)) (hw : ‖w‖ < η) :
    (complexToRealCoordinateEquiv).symm
      (complexToRealCoordinateEquiv z - w) ∈ U := by
  apply hCollar
  rw [Metric.mem_thickening_iff]
  refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
  rw [dist_eq_norm]
  calc
    ‖(complexToRealCoordinateEquiv).symm
        (complexToRealCoordinateEquiv z - w) - z‖ =
      ‖complexToRealCoordinateEquiv
        ((complexToRealCoordinateEquiv).symm (complexToRealCoordinateEquiv z - w) - z)‖ := by
          rw [complexToRealCoordinateEquiv.norm_map]
    _ = ‖w‖ := by simp
    _ < η := hw

private theorem integrable_smul_translate_of_norm_bound
    {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure E} {φ : E → ℝ} {g : E → F} {x : E} {K : ℝ}
    (hφ : Integrable φ μ) (hg : AEStronglyMeasurable g μ)
    (hbound : ∀ y, ‖g y‖ ≤ K)
    (htranslate : MeasurePreserving (fun t : E => x - t) μ μ) :
    Integrable (fun t => φ t • g (x - t)) μ := by
  have hweight : Integrable (fun t => ‖φ t‖ * K) μ := by
    simpa only [mul_comm] using hφ.norm.const_mul K
  apply hweight.mono'
  · exact hφ.aestronglyMeasurable.smul (hg.comp_measurePreserving htranslate)
  · filter_upwards with t
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound (x - t)) (norm_nonneg _)

private theorem localBumpConvolutionIntegrable {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {bump : ContDiffBump (0 : EuclideanSpace ℝ (Fin n × Fin 2))}
    {g : EuclideanSpace ℝ (Fin n × Fin 2) → F} {K : ℝ}
    (hg : AEStronglyMeasurable g
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
    (hbound : ∀ y, ‖g y‖ ≤ K) (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Integrable (fun t => bump.normed
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) t • g (x - t))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  let μ : Measure (EuclideanSpace ℝ (Fin n × Fin 2)) := volume
  have hkernelInt : Integrable (bump.normed μ) μ :=
    integrable_of_integral_eq_one bump.integral_normed
  have hmp : MeasurePreserving (fun t : EuclideanSpace ℝ (Fin n × Fin 2) => x - t) μ μ := by
    convert (measurePreserving_add_right μ x).comp
      (Measure.measurePreserving_neg μ) using 1
    ext t
    simp [sub_eq_add_neg, add_comm]
  exact integrable_smul_translate_of_norm_bound hkernelInt hg hbound hmp

private theorem integral_smul_translate_sub
    {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure E} {φ : E → ℝ} {g : E → F} {x y : E} {δ : E}
    (hintx : Integrable (fun t => φ t • g (x - t)) μ)
    (hinty : Integrable (fun t => φ t • g (y - t)) μ)
    (hshift : ∀ t, x - t + δ = y - t) :
    (∫ t, φ t • (g (x - t) - g (x - t + δ)) ∂μ) =
      (∫ t, φ t • g (x - t) ∂μ) - (∫ t, φ t • g (y - t) ∂μ) := by
  rw [← integral_sub hintx hinty]
  apply integral_congr_ae
  filter_upwards with t
  rw [hshift t, smul_sub]

/-- Positive fixed-radius averaging preserves an order-zero Hölder bound without any loss. -/
theorem localFixedMollify_holderBoundOn_zero {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {α K : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    {f : EuclideanSpace ℂ (Fin n) → F}
    (hU : IsOpen U) (hS : 0 < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hf : ContinuousOn f U) (hH : HolderBoundOn 0 α K U f) (m : ℕ) :
    HolderBoundOn 0 α K (Metric.ball c S) (localFixedMollify U hη m f) := by
  classical
  let e : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin 2) :=
    complexToRealCoordinateEquiv
  let φ := localKernelBump (n := n) hη m
  let V : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := (e.symm) ⁻¹' U
  let g : EuclideanSpace ℝ (Fin n × Fin 2) → F :=
    V.piecewise (f ∘ e.symm) (fun _ => 0)
  have hV : IsOpen V := hU.preimage e.symm.continuous
  have hfc : ContinuousOn (f ∘ e.symm) V := by
    apply hf.comp e.symm.continuous.continuousOn
    intro x hx
    exact hx
  have hgmeas : AEStronglyMeasurable g
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
    apply AEStronglyMeasurable.piecewise hV.measurableSet
    · exact hfc.aestronglyMeasurable hV.measurableSet
    · exact aestronglyMeasurable_const
  have hr : φ.rOut < η := by
    change localKernelRadius η m < η
    unfold localKernelRadius
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hden : (1 : ℝ) < 4 * ((m : ℝ) + 1) := by nlinarith
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hη (sub_pos.mpr hden)]
  have hsample (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ Metric.ball c S)
      (w : EuclideanSpace ℝ (Fin n × Fin 2)) (hw : ‖w‖ < η) :
      e.symm (e z - w) ∈ U := by
    simpa only [e] using localHolderSampleMem hS hη hCollar z hz w hw
  let L : ℝ →L[ℝ] F →L[ℝ] F := lsmul ℝ ℝ
  have hconv (z : EuclideanSpace ℂ (Fin n)) :
      localFixedMollify U hη m f z =
        (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) ⋆[L,
          (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] g) (e z) := by
    rfl
  have hkernelInt : Integrable
      (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
    integrable_of_integral_eq_one φ.integral_normed
  have hsource := holderBoundOn_zero_iff.mp hH
  rw [holderBoundOn_zero_iff]
  constructor
  · intro z hz
    have hbound : dist
        ((φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) ⋆[L,
          (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] g) (e z)) (0 : F) ≤
        (K : ℝ) := by
      have htmp := MeasureTheory.dist_convolution_le' L
        (show 0 ≤ (K : ℝ) by positivity) hkernelInt φ.support_normed_eq.subset
        hgmeas (x₀ := e z) (R := φ.rOut) (z₀ := (0 : F))
        (by
          intro w hw
          have hw' : dist w (e z) < φ.rOut := by simpa using hw
          have hdiff : ‖e z - w‖ < η := by
            rw [← dist_eq_norm]
            have : dist (e z) w = dist w (e z) := dist_comm _ _
            rw [this]
            exact hw'.trans hr
          have hmem := hsample z hz (e z - w) hdiff
          have hmem' : e.symm w ∈ U := by
            convert hmem using 1; simp
          have hn := hsource.1 (e.symm w) hmem'
          have hg : g w = f (e.symm w) := by simp [g, V, hmem']
          simpa [hg] using hn)
      have hnint : (∫ x, ‖φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) x‖
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) = 1 := by
        calc
          _ = ∫ x, φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
                apply integral_congr_ae
                filter_upwards with x
                exact Real.norm_of_nonneg (φ.nonneg_normed x)
          _ = 1 := φ.integral_normed
      have htmp' : dist
          ((φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) ⋆[L,
            (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] g) (e z)) 0 ≤
          (‖L‖ * ∫ x, ‖φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) x‖
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) * (K : ℝ) := by
        have hz : (fun t : EuclideanSpace ℝ (Fin n × Fin 2) =>
            L (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) t) (0 : F)) = 0 := by
          funext t
          simp [L]
        convert htmp using 1; simp
      calc
        _ ≤ (‖L‖ * ∫ x,
            ‖φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) x‖
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) * (K : ℝ) := htmp'
        _ = (‖L‖ * 1) * (K : ℝ) := by rw [hnint]
        _ ≤ (1 : ℝ) * (K : ℝ) := by
          gcongr
          simpa [L] using (ContinuousLinearMap.opNorm_lsmul_le
            (𝕜 := ℝ) (R := ℝ) (E := F))
        _ = (K : ℝ) := one_mul _
    simpa [hconv z] using hbound
  · intro z hz z' hz'
    let δ : EuclideanSpace ℝ (Fin n × Fin 2) := e z' - e z
    let d : EuclideanSpace ℝ (Fin n × Fin 2) → F := fun x => g x - g (x + δ)
    have hdmeas : AEStronglyMeasurable d
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
      exact hgmeas.sub (hgmeas.comp_measurePreserving
        (measurePreserving_add_right volume δ))
    have hpoint (x : EuclideanSpace ℝ (Fin n × Fin 2))
        (hx : x ∈ Metric.ball (e z) φ.rOut) :
        dist (d x) (0 : F) ≤ (K : ℝ) * dist z z' ^ (α : ℝ) := by
      have hx' : dist x (e z) < φ.rOut := by simpa using hx
      have hxη : ‖e z - x‖ < η := by
        rw [← dist_eq_norm, dist_comm]
        exact hx'.trans hr
      have hmemx : e.symm x ∈ U := by
        have := hsample z hz (e z - x) hxη
        simpa using this
      have hx'η : ‖e z' - (x + δ)‖ < η := by
        rw [← dist_eq_norm, dist_comm]
        have hshift : dist (x + δ) (e z') = dist x (e z) := by
          simp [δ, dist_eq_norm, sub_eq_add_neg, add_assoc]
        rw [hshift]
        exact hx'.trans hr
      have hmemx' : e.symm (x + δ) ∈ U := by
        have := hsample z' hz' (e z' - (x + δ)) hx'η
        simpa using this
      have hgx : g x = f (e.symm x) := by simp [g, V, hmemx]
      have hgx' : g (x + δ) = f (e.symm (x + δ)) := by
        change V.piecewise (f ∘ e.symm) (fun _ => 0) (x + δ) = _
        have hv : x + δ ∈ V := hmemx'
        rw [V.piecewise_eq_of_mem _ _ hv]
        rfl
      have hdist : dist (e.symm x) (e.symm (x + δ)) = dist z z' := by
        calc
          dist (e.symm x) (e.symm (x + δ)) =
              ‖e.symm (x - (x + δ))‖ := by rw [dist_eq_norm, map_sub]
          _ = ‖x - (x + δ)‖ := e.symm.norm_map _
          _ = ‖e z - e z'‖ := by simp [δ, sub_eq_add_neg, add_comm]
          _ = ‖z - z'‖ := by
            rw [← e.map_sub, e.norm_map]
          _ = dist z z' := by rw [dist_eq_norm]
      have hh := hsource.2.dist_le hmemx hmemx'
      rw [hdist] at hh
      simpa [d, hgx, hgx', dist_eq_norm, norm_sub_rev] using hh
    have hgBound (x : EuclideanSpace ℝ (Fin n × Fin 2)) : ‖g x‖ ≤ (K : ℝ) := by
      by_cases hx : x ∈ V
      · have h := hsource.1 (e.symm x) hx
        simpa [g, V, hx] using h
      · simp [g, V, hx]
    have hconvInt (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
        Integrable (fun t : EuclideanSpace ℝ (Fin n × Fin 2) =>
          L (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) t)
            (g (x - t)))
          (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
      simpa [L] using localBumpConvolutionIntegrable
        (bump := φ) hgmeas hgBound x
    have hid :
        (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) ⋆[L,
          (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] d) (e z) =
        (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) ⋆[L,
          (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] g) (e z) -
        (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) ⋆[L,
          (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] g) (e z') := by
      rw [convolution_def, convolution_def, convolution_def]
      have hshift (t : EuclideanSpace ℝ (Fin n × Fin 2)) :
          e z - t + δ = e z' - t := by
        dsimp [δ]
        abel
      simpa [L] using integral_smul_translate_sub
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
        (φ := φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
        (g := g) (x := e z) (y := e z') (δ := δ)
        (by simpa [L] using hconvInt (e z))
        (by simpa [L] using hconvInt (e z')) hshift
    have hdiff : dist
        ((φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) ⋆[L,
          (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] d) (e z)) (0 : F) ≤
        (K : ℝ) * dist z z' ^ (α : ℝ) := by
      have htmp := MeasureTheory.dist_convolution_le' L
        (show 0 ≤ (K : ℝ) * dist z z' ^ (α : ℝ) by positivity)
        hkernelInt φ.support_normed_eq.subset hdmeas (x₀ := e z)
        (R := φ.rOut) (z₀ := (0 : F))
        (by
          intro x hx
          exact hpoint x hx)
      have hnint : (∫ x, ‖φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) x‖
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) = 1 := by
        calc
          _ = ∫ x, φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) x
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
                apply integral_congr_ae
                filter_upwards with x
                exact Real.norm_of_nonneg (φ.nonneg_normed x)
          _ = 1 := φ.integral_normed
      have htmp' : dist
          ((φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) ⋆[L,
            (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))] d) (e z)) 0 ≤
          (‖L‖ * ∫ x, ‖φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) x‖
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) *
              ((K : ℝ) * dist z z' ^ (α : ℝ)) := by
        have hz : (fun t : EuclideanSpace ℝ (Fin n × Fin 2) =>
            L (φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) t) (0 : F)) = 0 := by
          funext t
          simp [L]
        convert htmp using 1; simp
      calc
        _ ≤ (‖L‖ * ∫ x,
            ‖φ.normed (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) x‖
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) *
              ((K : ℝ) * dist z z' ^ (α : ℝ)) := htmp'
        _ = (‖L‖ * 1) * ((K : ℝ) * dist z z' ^ (α : ℝ)) := by rw [hnint]
        _ ≤ (1 : ℝ) * ((K : ℝ) * dist z z' ^ (α : ℝ)) := by
          gcongr
          simpa [L] using (ContinuousLinearMap.opNorm_lsmul_le
            (𝕜 := ℝ) (R := ℝ) (E := F))
        _ = (K : ℝ) * dist z z' ^ (α : ℝ) := one_mul _
    rw [hconv z, hconv z']
    rw [edist_dist, dist_eq_norm, ← hid]
    have hconvert : (K : ENNReal) * edist z z' ^ (α : ℝ) =
        ENNReal.ofReal ((K : ℝ) * dist z z' ^ (α : ℝ)) := by
      calc
        _ = ENNReal.ofReal (K : ℝ) *
              ENNReal.ofReal (dist z z' ^ (α : ℝ)) := by
          rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
            ← ENNReal.ofReal_coe_nnreal]
        _ = _ := (ENNReal.ofReal_mul K.coe_nonneg).symm
    rw [hconvert]
    exact ENNReal.ofReal_le_ofReal (by simpa [dist_eq_norm] using hdiff)

end CalabiYau.Schauder
