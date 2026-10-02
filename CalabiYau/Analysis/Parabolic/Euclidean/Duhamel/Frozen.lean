-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/Duhamel/Frozen.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Approximation
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.PDE
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

-- and its private helpers occur in public declarations.

noncomputable section
open Asymptotics Filter MeasureTheory Real Set
open scoped Interval NNReal RealInnerProductSpace Topology
namespace HeatEquation

section CoreOperators

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section

variable [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]

def lapEval : (V →L[ℝ] V →L[ℝ] F) →L[ℝ] F :=
  ∑ i : Fin (Module.finrank ℝ V),
    (ContinuousLinearMap.apply ℝ F ((stdOrthonormalBasis ℝ V) i)).comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] F)
        ((stdOrthonormalBasis ℝ V) i))

@[simp]
theorem lapEval_apply (A : V →L[ℝ] V →L[ℝ] F) :
    lapEval A =
      ∑ i : Fin (Module.finrank ℝ V),
        A ((stdOrthonormalBasis ℝ V) i)
          ((stdOrthonormalBasis ℝ V) i) := by
  simp [lapEval]

theorem lapEval_dist_le
    (A B : V →L[ℝ] V →L[ℝ] F) :
    dist (lapEval A) (lapEval B) ≤
      Module.finrank ℝ V * dist A B := by
  rw [dist_eq_norm, ← map_sub]
  simp only [lapEval_apply]
  calc
    ‖∑ i : Fin (Module.finrank ℝ V),
        (A - B) ((stdOrthonormalBasis ℝ V) i)
          ((stdOrthonormalBasis ℝ V) i)‖ ≤
        ∑ i : Fin (Module.finrank ℝ V),
          ‖(A - B) ((stdOrthonormalBasis ℝ V) i)
            ((stdOrthonormalBasis ℝ V) i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ V), ‖A - B‖ := by
      gcongr with i
      calc
        ‖(A - B) ((stdOrthonormalBasis ℝ V) i)
            ((stdOrthonormalBasis ℝ V) i)‖ ≤
            ‖(A - B) ((stdOrthonormalBasis ℝ V) i)‖ *
              ‖(stdOrthonormalBasis ℝ V) i‖ :=
          ((A - B) ((stdOrthonormalBasis ℝ V) i)).le_opNorm _
        _ ≤ (‖A - B‖ * ‖(stdOrthonormalBasis ℝ V) i‖) *
              ‖(stdOrthonormalBasis ℝ V) i‖ := by
          gcongr
          exact (A - B).le_opNorm _
        _ = ‖A - B‖ := by simp
    _ = Module.finrank ℝ V * dist A B := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      congr 1
      exact (dist_eq_norm A B).symm

def coreLap (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F)) :
    BoundedContinuousFunction V F :=
  ⟨⟨fun x => lapEval (V := V) (F := F) (d2u x),
      (lapEval (V := V) (F := F)).continuous.comp d2u.continuous⟩, by
    obtain ⟨C, hC⟩ := d2u.bounded
    refine ⟨Module.finrank ℝ V * C, fun x y => ?_⟩
    exact (lapEval_dist_le (d2u x) (d2u y)).trans
      (mul_le_mul_of_nonneg_left (hC x y) (Nat.cast_nonneg _))⟩

@[simp]
theorem coreLap_apply
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F)) (x : V) :
    coreLap d2u x =
      ∑ i : Fin (Module.finrank ℝ V),
        d2u x ((stdOrthonormalBasis ℝ V) i)
          ((stdOrthonormalBasis ℝ V) i) := by
  simp [coreLap]

end

end CoreOperators

section ScaledEvolution

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def heatScaled (t : ℝ) (u : BoundedContinuousFunction V F) (x : V) : F :=
  ∫ z : V, baseHeat z • u (x - heatScale t • z)

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem heatSup_scaled {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    heatSup t u x = heatScaled t u x := by
  let r := heatScale t
  have hr : 0 < r := by
    simpa only [r] using heatScale_pos ht
  let f : V → F := fun z => baseHeat z • u (x - r • z)
  have hscale :=
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure V) f hr.le
  have hscale' :
      (∫ y : V, baseHeat (r⁻¹ • y) • u (x - y)) =
        r ^ Module.finrank ℝ V •
          ∫ z : V, baseHeat z • u (x - r • z) := by
    simpa only [f, smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using hscale
  unfold heatSup supKernel heatKernel heatScaled
  change
    (∫ y : V,
      ((r ^ Module.finrank ℝ V)⁻¹ * baseHeat (r⁻¹ • y)) • u (x - y)) = _
  calc
    (∫ y : V,
        ((r ^ Module.finrank ℝ V)⁻¹ * baseHeat (r⁻¹ • y)) • u (x - y)) =
        (r ^ Module.finrank ℝ V)⁻¹ •
          ∫ y : V, baseHeat (r⁻¹ • y) • u (x - y) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      rw [mul_smul]
    _ = (r ^ Module.finrank ℝ V)⁻¹ •
          (r ^ Module.finrank ℝ V •
            ∫ z : V, baseHeat z • u (x - r • z)) := by
      rw [hscale']
    _ = ∫ z : V, baseHeat z • u (x - r • z) := by
      rw [inv_smul_smul₀ (pow_ne_zero _ hr.ne')]

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem heatScaled_cont (u : BoundedContinuousFunction V F) (x : V) :
    Continuous (fun t : ℝ => heatScaled t u x) := by
  unfold heatScaled
  apply continuous_of_dominated
    (bound := fun z : V => ‖u‖ * baseHeat z)
  · intro t
    apply Continuous.aestronglyMeasurable
    unfold baseHeat
    fun_prop
  · intro t
    apply Filter.Eventually.of_forall
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (baseHeat_nonneg z)]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (u.norm_coe_le_norm _) (baseHeat_nonneg z)
  · exact (baseHeat_int (V := V)).const_mul ‖u‖
  · apply Filter.Eventually.of_forall
    intro z
    unfold heatScale
    fun_prop

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

@[simp]
theorem heatScaled_zero (u : BoundedContinuousFunction V F) (x : V) :
    heatScaled 0 u x = u x := by
  unfold heatScaled heatScale
  simp only [Real.sqrt_zero, zero_smul, sub_zero]
  rw [integral_smul_const, integral_baseHeat, one_smul]

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem kernel_comp_int {K : V → ℝ} (hK : Integrable K)
    (u : BoundedContinuousFunction V F) {p : V → V} (hp : Continuous p) :
    Integrable (fun z : V => K z • u (p z)) := by
  refine (hK.norm.mul_const ‖u‖).mono' ?_ ?_
  · exact hK.aestronglyMeasurable.smul
      ((u.continuous.comp hp).aestronglyMeasurable)
  · filter_upwards with z
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm (p z)) (norm_nonneg _)

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem heatSup_zero {K : ℝ≥0} (u : BoundedContinuousFunction V F)
    (hu : HolderWith K (1 / 2 : ℝ≥0) u) (x : V) :
    Tendsto (fun t : ℝ => heatSup t u x) (𝓝[>] (0 : ℝ)) (𝓝 (u x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt : Tendsto (fun t : ℝ => Real.sqrt (heatScale t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto (fun t : ℝ => Real.sqrt (Real.sqrt t))
        (𝓝 0) (𝓝 0) := by
      change Tendsto (Real.sqrt ∘ Real.sqrt) (𝓝 0) (𝓝 0)
      have ht := (Real.continuous_sqrt.comp Real.continuous_sqrt).tendsto (0 : ℝ)
      rw [show (Real.sqrt ∘ Real.sqrt) 0 = 0 by norm_num] at ht
      exact ht
    simpa only [heatScale, Real.sqrt_zero] using hfull.mono_left nhdsWithin_le_nhds
  have hupper : Tendsto
      (fun t : ℝ => (K : ℝ) * Real.sqrt (heatScale t) * heatC0Half V)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h₁ := Tendsto.const_mul (K : ℝ) hsqrt
    have h₂ := Tendsto.mul_const (heatC0Half V) h₁
    simpa only [mul_zero, zero_mul] using h₂
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hupper
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact heatSup_id_norm ht hu x

private theorem baseFirst_int :
    Integrable (fun z : V => ‖z‖ * baseHeat z) := by
  have h := (gaussMoment_int (V := V) 1
    (by positivity : (0 : ℝ) < (4 : ℝ)⁻¹)).const_mul (baseHeatMass V)⁻¹
  have heq : (fun z : V => ‖z‖ * baseHeat z) = fun z : V =>
      (baseHeatMass V)⁻¹ *
        (‖z‖ ^ 1 * Real.exp (-(4 : ℝ)⁻¹ * ‖z‖ ^ 2)) := by
    funext z
    unfold baseHeat
    ring
  rw [heq]
  exact h

def scaledDt (t : ℝ)
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) (x z : V) : F :=
  baseHeat z •
    du (x - heatScale t • z) ((-(2 * heatScale t)⁻¹) • z)

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem heatScaled_time {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x) (x : V) :
    HasDerivAt (fun s : ℝ => heatScaled s u x)
      (∫ z : V, scaledDt t du x z) t := by
  let s₀ : ℝ := t / 2
  have hs₀ : 0 < s₀ := by
    dsimp only [s₀]
    linarith
  let r₀ : ℝ := heatScale s₀
  have hr₀ : 0 < r₀ := by
    simpa only [r₀] using heatScale_pos hs₀
  let F₀ : ℝ → V → F := fun s z =>
    baseHeat z • u (x - heatScale s • z)
  let F₁ : ℝ → V → F := fun s z => scaledDt s du x z
  let bound : V → ℝ := fun z =>
    ((2 * r₀)⁻¹ * ‖du‖) * (‖z‖ * baseHeat z)
  have hs : Set.Ioi s₀ ∈ 𝓝 t := Ioi_mem_nhds (by
    dsimp only [s₀]
    linarith)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F₀ s) := by
    apply Filter.Eventually.of_forall
    intro s
    apply Continuous.aestronglyMeasurable
    dsimp only [F₀]
    unfold baseHeat
    fun_prop
  have hint : Integrable (F₀ t) := by
    apply kernel_comp_int (baseHeat_int (V := V)) u
    fun_prop
  have hder_meas : AEStronglyMeasurable (F₁ t) := by
    apply Continuous.aestronglyMeasurable
    dsimp only [F₁, scaledDt]
    unfold baseHeat
    fun_prop
  have hbound_int : Integrable bound := by
    dsimp only [bound]
    exact (baseFirst_int (V := V)).const_mul _
  have hcoef : ∀ s ∈ Set.Ioi s₀,
      ‖(-(2 * heatScale s)⁻¹ : ℝ)‖ ≤ (2 * r₀)⁻¹ := by
    intro s hs_mem
    have hs_pos : 0 < s := hs₀.trans hs_mem
    have hrs : r₀ ≤ heatScale s := by
      dsimp only [r₀, heatScale]
      exact Real.sqrt_le_sqrt hs_mem.le
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num)
      (heatScale_pos hs_pos)))]
    exact (inv_le_inv₀ (mul_pos (by norm_num) (heatScale_pos hs_pos))
      (mul_pos (by norm_num) hr₀)).2 (mul_le_mul_of_nonneg_left hrs (by norm_num))
  have hbound : ∀ᵐ z ∂(volume : Measure V), ∀ s ∈ Set.Ioi s₀,
      ‖F₁ s z‖ ≤ bound z := by
    apply Filter.Eventually.of_forall
    intro z s hs_mem
    have hc := hcoef s hs_mem
    dsimp only [F₁, scaledDt, bound]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (baseHeat_nonneg z)]
    calc
      baseHeat z *
          ‖du (x - heatScale s • z) ((-(2 * heatScale s)⁻¹) • z)‖ ≤
          baseHeat z *
            (‖du (x - heatScale s • z)‖ * ‖(-(2 * heatScale s)⁻¹ : ℝ) • z‖) := by
        exact mul_le_mul_of_nonneg_left
          ((du (x - heatScale s • z)).le_opNorm _) (baseHeat_nonneg z)
      _ ≤ baseHeat z * (‖du‖ * ((2 * r₀)⁻¹ * ‖z‖)) := by
        rw [norm_smul]
        apply mul_le_mul_of_nonneg_left _ (baseHeat_nonneg z)
        calc
          ‖du (x - heatScale s • z)‖ *
                (‖(-(2 * heatScale s)⁻¹ : ℝ)‖ * ‖z‖) ≤
              ‖du‖ * (‖(-(2 * heatScale s)⁻¹ : ℝ)‖ * ‖z‖) :=
            mul_le_mul_of_nonneg_right
              (du.norm_coe_le_norm (x - heatScale s • z))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ ≤ ‖du‖ * ((2 * r₀)⁻¹ * ‖z‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
              (norm_nonneg du)
      _ = ((2 * r₀)⁻¹ * ‖du‖) * (‖z‖ * baseHeat z) := by ring
  have hdiff : ∀ᵐ z ∂(volume : Measure V), ∀ s ∈ Set.Ioi s₀,
      HasDerivAt (F₀ · z) (F₁ s z) s := by
    apply Filter.Eventually.of_forall
    intro z s hs_mem
    have hs_pos : 0 < s := hs₀.trans hs_mem
    have hscale : HasDerivAt heatScale (1 / (2 * heatScale s)) s := by
      exact (Real.hasDerivAt_sqrt hs_pos.ne').congr_of_eventuallyEq <|
        Filter.Eventually.of_forall fun q => by rfl
    have harg : HasDerivAt (fun q : ℝ => x - heatScale q • z)
        ((-(2 * heatScale s)⁻¹) • z) s := by
      refine ((hasDerivAt_const s x).sub (hscale.smul_const z)).congr_deriv ?_
      simp only [zero_sub, one_div, neg_smul]
    have hcomp := (hu (x - heatScale s • z)).comp_hasDerivAt s harg
    dsimp only [F₀, F₁, scaledDt]
    exact hcomp.const_smul (baseHeat z)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F₀) (F' := F₁) (bound := bound) hs hmeas hint hder_meas
      hbound hbound_int hdiff
  simpa only [F₀, F₁, heatScaled] using key.2

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private def evalD1
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) (v : V) :
    BoundedContinuousFunction V F :=
  (ContinuousLinearMap.apply ℝ F v).compLeftContinuousBounded V du

private def evalD2
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (v w : V) : BoundedContinuousFunction V F :=
  ((ContinuousLinearMap.apply ℝ F w).comp
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] F) v)).compLeftContinuousBounded V d2u

end

section

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp] private theorem evalD1_apply
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) (v x : V) :
    evalD1 du v x = du x v := rfl

@[simp] private theorem evalD2_apply
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (v w x : V) : evalD2 d2u v w x = d2u x v w := rfl

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem baseD1_integrable (v : V) :
    Integrable (baseD1 v : V → ℝ) := by
  refine (heatD1_int (V := V) (t := (1 : ℝ)) (by norm_num) v).congr ?_
  filter_upwards with x
  simp [heatD1, heatScale]
end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem scaledDt_eq_lap {t : ℝ} (ht : 0 < t)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) :
    (∫ z : V, scaledDt t du x z) = heatScaled t (coreLap d2u) x := by
  let r := heatScale t
  have hr : 0 < r := by
    simpa only [r] using heatScale_pos ht
  let b := stdOrthonormalBasis ℝ V
  let p : V → V := fun z => x - r • z
  have hp : Continuous p := by
    dsimp only [p]
    fun_prop
  have harg : ∀ z : V,
      HasFDerivAt p (-r • ContinuousLinearMap.id ℝ V) z := by
    intro z
    dsimp only [p]
    refine (((hasFDerivAt_const x z).sub
      ((r • ContinuousLinearMap.id ℝ V).hasFDerivAt)).congr_fderiv (by simp)).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall fun y => by rfl
  have hgder : ∀ (i : Fin (Module.finrank ℝ V)) (z : V),
      fderiv ℝ (fun y : V => du (p y) (b i)) z (b i) =
        (-r) • d2u (p z) (b i) (b i) := by
    intro i z
    let ev : (V →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (b i)
    have hcomp := (hdu (p z)).comp z (harg z)
    have heval := ev.hasFDerivAt.comp z hcomp
    have hfd : fderiv ℝ (fun y : V => du (p y) (b i)) z =
        ev.comp ((d2u (p z)).comp (-r • ContinuousLinearMap.id ℝ V)) := by
      exact (heval.congr_of_eventuallyEq <|
        Filter.Eventually.of_forall fun y => by rfl).fderiv
    rw [hfd]
    simp [ev]
  have hgdiff : ∀ (i : Fin (Module.finrank ℝ V)) (z : V),
      DifferentiableAt ℝ (fun y : V => du (p y) (b i)) z := by
    intro i z
    let ev : (V →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (b i)
    exact (ev.hasFDerivAt.comp z ((hdu (p z)).comp z (harg z))).differentiableAt
  have hD1int : ∀ i : Fin (Module.finrank ℝ V),
      Integrable (fun z : V => baseD1 (b i) z • du (p z) (b i)) := by
    intro i
    simpa only [evalD1_apply] using
      kernel_comp_int (baseD1_integrable (V := V) (b i)) (evalD1 du (b i)) hp
  have hD2int : ∀ i : Fin (Module.finrank ℝ V),
      Integrable (fun z : V => baseHeat z • d2u (p z) (b i) (b i)) := by
    intro i
    simpa only [evalD2_apply] using
      kernel_comp_int (baseHeat_int (V := V)) (evalD2 d2u (b i) (b i)) hp
  have hD0int : ∀ i : Fin (Module.finrank ℝ V),
      Integrable (fun z : V => baseHeat z • du (p z) (b i)) := by
    intro i
    simpa only [evalD1_apply] using
      kernel_comp_int (baseHeat_int (V := V)) (evalD1 du (b i)) hp
  have hparts : ∀ i : Fin (Module.finrank ℝ V),
      (∫ z : V, baseD1 (b i) z • du (p z) (b i)) =
        r • ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
    intro i
    have hleft : Integrable (fun z : V =>
        fderiv ℝ (baseHeat : V → ℝ) z (b i) • du (p z) (b i)) := by
      simpa only [(baseHeat_hasFDeriv _).fderiv, baseD1Map_apply] using hD1int i
    have hright : Integrable (fun z : V =>
        baseHeat z • fderiv ℝ (fun y : V => du (p y) (b i)) z (b i)) := by
      have hi : Integrable
          (fun z : V => baseHeat z • d2u (p z) (b i) (b i)) := hD2int i
      have hraw := hi.smul (-r)
      refine hraw.congr (Filter.Eventually.of_forall fun z => ?_)
      change (-r) • (baseHeat z • d2u (p z) (b i) (b i)) =
        baseHeat z • fderiv ℝ (fun y : V => du (p y) (b i)) z (b i)
      rw [hgder i z]
      simp only [smul_smul]
      congr 1
      ring
    have hzero : Integrable (fun z : V => baseHeat z • du (p z) (b i)) :=
      hD0int i
    have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (f := baseHeat) (g := fun z : V => du (p z) (b i)) (v := b i)
      hleft hright hzero
      (fun z _ => (baseHeat_hasFDeriv z).differentiableAt)
      (fun z _ => hgdiff i z)
    simp_rw [(baseHeat_hasFDeriv _).fderiv, baseD1Map_apply, hgder i] at hibp
    have hfactor :
        (∫ z : V, baseHeat z • ((-r) • d2u (p z) (b i) (b i))) =
          (-r) • ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
      rw [← integral_smul]
      apply integral_congr_ae
      filter_upwards with z
      simp only [smul_smul]
      congr 1
      ring
    calc
      (∫ z : V, baseD1 (b i) z • du (p z) (b i)) =
          -(∫ z : V, baseHeat z • ((-r) • d2u (p z) (b i) (b i))) := by
        rw [hibp]
        simp
      _ = -((-r) • ∫ z : V, baseHeat z • d2u (p z) (b i) (b i)) := by
        rw [hfactor]
      _ = r • ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
        simp
  have hdir : ∀ i : Fin (Module.finrank ℝ V),
      (∫ z : V, r⁻¹ • (baseD1 (b i) z • du (p z) (b i))) =
        ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
    intro i
    rw [integral_smul, hparts i, inv_smul_smul₀ hr.ne']
  have hpoint : ∀ z : V, scaledDt t du x z =
      ∑ i : Fin (Module.finrank ℝ V),
        r⁻¹ • (baseD1 (b i) z • du (p z) (b i)) := by
    intro z
    have hz := b.sum_repr' z
    unfold scaledDt
    change baseHeat z • du (p z) ((-(2 * r)⁻¹) • z) = _
    conv_lhs => rw [← hz]
    simp only [map_smul, map_sum, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    unfold baseD1
    rw [real_inner_comm z (b i)]
    rw [hz]
    congr 1
    field_simp [hr.ne']
  have hterm_int : ∀ i : Fin (Module.finrank ℝ V),
      Integrable (fun z : V => r⁻¹ • (baseD1 (b i) z • du (p z) (b i))) :=
    fun i => by
      have hi : Integrable
          (fun z : V => baseD1 (b i) z • du (p z) (b i)) := hD1int i
      exact hi.smul r⁻¹
  unfold heatScaled
  change (∫ z : V, scaledDt t du x z) =
    ∫ z : V, baseHeat z • coreLap d2u (p z)
  calc
    (∫ z : V, scaledDt t du x z) =
        ∫ z : V, ∑ i : Fin (Module.finrank ℝ V),
          r⁻¹ • (baseD1 (b i) z • du (p z) (b i)) := by
      apply integral_congr_ae
      filter_upwards with z
      exact hpoint z
    _ = ∑ i : Fin (Module.finrank ℝ V),
          ∫ z : V, r⁻¹ • (baseD1 (b i) z • du (p z) (b i)) := by
      rw [MeasureTheory.integral_finsetSum _ (fun i _ => hterm_int i)]
    _ = ∑ i : Fin (Module.finrank ℝ V),
          ∫ z : V, baseHeat z • d2u (p z) (b i) (b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hdir i
    _ = ∫ z : V, ∑ i : Fin (Module.finrank ℝ V),
          baseHeat z • d2u (p z) (b i) (b i) := by
      rw [MeasureTheory.integral_finsetSum _ (fun i _ => hD2int i)]
    _ = ∫ z : V, baseHeat z • coreLap d2u (p z) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [coreLap_apply, b, Finset.smul_sum]

theorem heatSup_time {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (x : V) :
    HasDerivAt (fun s : ℝ => heatSup s u x) (heatSup t (coreLap d2u) x) t := by
  have hscaled := heatScaled_time ht u du hu x
  rw [scaledDt_eq_lap ht du d2u hdu x, ← heatSup_scaled ht] at hscaled
  apply hscaled.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact heatSup_scaled hs u x

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem heatSup_primitive {t : ℝ} (ht : 0 < t) {K : ℝ≥0}
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x)
    (hdu : ∀ x : V, HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x)
    (hholder : HolderWith K (1 / 2 : ℝ≥0) u) (x : V) :
    (∫ s in (0 : ℝ)..t, heatSup s (coreLap d2u) x) = heatSup t u x - u x := by
  have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun q : ℝ => heatSup q u x) (heatSup s (coreLap d2u) x) s := by
    intro s hs
    exact heatSup_time hs.1 u du d2u hu hdu x
  have hint : IntervalIntegrable (fun s : ℝ => heatSup s (coreLap d2u) x)
      volume 0 t := by
    have hscaled :=
      (heatScaled_cont (coreLap d2u) x).intervalIntegrable (μ := volume) 0 t
    apply hscaled.congr_ae
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs_mem
    rw [uIoc_of_le ht.le] at hs_mem
    exact (heatSup_scaled hs_mem.1 (coreLap d2u) x).symm
  have hzero := heatSup_zero u hholder x
  have htlim : Tendsto (fun s : ℝ => heatSup s u x) (𝓝[<] t)
      (𝓝 (heatSup t u x)) :=
    (heatSup_time ht u du d2u hu hdu x).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    ht hderiv hint hzero htlim

end

section Duhamel

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def frozenDuhamel (t : ℝ) (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction V F) (x : V) : F :=
  ∫ r in (0 : ℝ)..t, a (t - r) • heatScaled r u x

end

section

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F] [NormedSpace ℝ F]

@[simp]
theorem frozenDuhamel_zero (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction V F) (x : V) :
    frozenDuhamel 0 a u x = 0 := by
  simp [frozenDuhamel]

end

end Duhamel

end ScaledEvolution

end HeatEquation
