module

public import CalabiYau.Geometry.Kahler.Volume
public import CalabiYau.Analysis.MoserIteration.Iteration
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

public section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]

noncomputable def c0Softplus (t : ℝ) : ℝ :=
  1 + Real.log (1 + Real.exp t)

@[expose] noncomputable def c0CenteredSoftplus (u : M → ℝ) : M → ℝ :=
  fun x => c0Softplus (u x)

noncomputable def c0MomentLogMajorant (κ C_S : ℝ) (k : ℕ) : ℝ :=
  (Real.log (max C_S 1 * (1 + (n : ℝ) / 2)) / 2) * (κ⁻¹) ^ k +
    (Real.log κ / 2) * ((k : ℝ) * (κ⁻¹) ^ k)

theorem c0MomentLogMajorant_nonneg
    {κ C_S : ℝ} (hκ : 1 < κ) (k : ℕ) : 0 ≤ c0MomentLogMajorant (n := n) κ C_S k := by
  have hA : 1 ≤ max C_S 1 := le_max_right _ _
  have hn0 : 0 ≤ (n : ℝ) / 2 := by positivity
  have hD : 1 ≤ max C_S 1 * (1 + (n : ℝ) / 2) := by nlinarith
  have hlogD : 0 ≤ Real.log (max C_S 1 * (1 + (n : ℝ) / 2)) := Real.log_nonneg hD
  have hlogκ : 0 ≤ Real.log κ := Real.log_nonneg hκ.le
  dsimp [c0MomentLogMajorant]
  positivity

theorem c0_moment_log_majorant_summable
    {κ C_S : ℝ} (hκ : 1 < κ) : Summable (c0MomentLogMajorant (n := n) κ C_S) := by
  let r : ℝ := κ⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hκ))
  have hr1 : r < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hκ)).2 hκ
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hgeom : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
  have hnatNorm : Summable (fun k : ℕ => ‖(k : ℝ) * r ^ k‖) := by
    simpa [pow_one] using summable_norm_pow_mul_geometric_of_norm_lt_one 1 hrnorm
  have hnat : Summable (fun k : ℕ => (k : ℝ) * r ^ k) := hnatNorm.of_norm
  have hsum : Summable (fun k : ℕ =>
      (Real.log (max C_S 1 * (1 + (n : ℝ) / 2)) / 2) * r ^ k +
        (Real.log κ / 2) * ((k : ℝ) * r ^ k)) :=
    (hgeom.mul_left _).add (hnat.mul_left _)
  exact hsum.congr fun k => by simp [c0MomentLogMajorant, r]

theorem c0_moment_factor_le_exp_logMajorant
    {κ C_S : ℝ} (hκ : 1 < κ) (k : ℕ) :
    (max C_S 1 * (1 + (n : ℝ) * (2 * κ ^ k) / 4)) ^ ((2 * κ ^ k)⁻¹) ≤
      Real.exp (c0MomentLogMajorant (n := n) κ C_S k) := by
  have hκpow : 1 ≤ κ ^ k := one_le_pow₀ hκ.le
  have hqpos : 0 < 2 * κ ^ k := mul_pos (by norm_num) (pow_pos (lt_trans zero_lt_one hκ) k)
  have hA : 0 < max C_S 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hD : 0 < max C_S 1 * (1 + (n : ℝ) / 2) := by positivity
  have hbasePos : 0 < max C_S 1 *
      (1 + (n : ℝ) * (2 * κ ^ k) / 4) := by positivity
  have hbaseLe : max C_S 1 * (1 + (n : ℝ) * (2 * κ ^ k) / 4) ≤
      max C_S 1 * (1 + (n : ℝ) / 2) * κ ^ k := by
    have hinner : 1 + (n : ℝ) / 2 * κ ^ k ≤ (1 + (n : ℝ) / 2) * κ ^ k := by
      nlinarith [hκpow]
    calc
      _ = max C_S 1 * (1 + (n : ℝ) / 2 * κ ^ k) := by ring
      _ ≤ max C_S 1 * ((1 + (n : ℝ) / 2) * κ ^ k) :=
        mul_le_mul_of_nonneg_left hinner hA.le
      _ = max C_S 1 * (1 + (n : ℝ) / 2) * κ ^ k := by ring
  have hlog : Real.log (max C_S 1 *
      (1 + (n : ℝ) * (2 * κ ^ k) / 4)) ≤
      Real.log (max C_S 1 * (1 + (n : ℝ) / 2)) + (k : ℝ) * Real.log κ := by
    calc
      _ ≤ Real.log (max C_S 1 * (1 + (n : ℝ) / 2) * κ ^ k) :=
        Real.log_le_log hbasePos hbaseLe
      _ = Real.log (max C_S 1 * (1 + (n : ℝ) / 2)) +
          (k : ℝ) * Real.log κ := by
        rw [Real.log_mul (ne_of_gt hD) (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hκ))),
          Real.log_pow]
  rw [Real.rpow_def_of_pos hbasePos]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (Real.log (max C_S 1 * (1 + (n : ℝ) / 2)) +
        (k : ℝ) * Real.log κ) * (2 * κ ^ k)⁻¹ :=
      mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr hqpos.le)
    _ = c0MomentLogMajorant κ C_S k := by
      simp [c0MomentLogMajorant, div_eq_mul_inv, inv_pow]
      ring

theorem c0Softplus_nonneg (t : ℝ) : 0 ≤ c0Softplus t := by
  dsimp [c0Softplus]
  have hlog : 0 ≤ Real.log (1 + Real.exp t) :=
    Real.log_nonneg (by linarith [Real.exp_pos t])
  linarith

private theorem c0Softplus_sq_le (t : ℝ) :
    c0Softplus t ^ 2 ≤ (2 * (1 + Real.log 2) ^ 2 + 2) * (1 + t ^ 2) := by
  have hlog : Real.log (1 + Real.exp t) ≤ Real.log 2 + |t| := by
    apply (Real.log_le_iff_le_exp (by positivity)).2
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    have ht : Real.exp t ≤ Real.exp |t| := Real.exp_le_exp.mpr (le_abs_self t)
    have h0 : 1 ≤ Real.exp |t| := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (abs_nonneg t)
    nlinarith
  have hA : 0 ≤ 1 + Real.log 2 := by positivity
  have hρ : 0 ≤ c0Softplus t ∧ c0Softplus t ≤ 1 + Real.log 2 + |t| := by
    constructor
    · exact c0Softplus_nonneg t
    · dsimp [c0Softplus]; linarith
  nlinarith [sq_abs t, sq_nonneg ((1 + Real.log 2) - |t|)]

theorem continuous_c0Softplus : Continuous c0Softplus := by
  have hinner : Continuous (fun t : ℝ => 1 + Real.exp t) :=
    continuous_const.add Real.continuous_exp
  have hlog : Continuous (fun t : ℝ => Real.log (1 + Real.exp t)) :=
    hinner.log (by intro t; positivity)
  change Continuous (fun t : ℝ => 1 + Real.log (1 + Real.exp t))
  exact continuous_const.add hlog

theorem contDiff_c0Softplus : ContDiff ℝ ∞ c0Softplus := by
  change ContDiff ℝ ∞ (fun t : ℝ => 1 + Real.log (1 + Real.exp t))
  have hinner : ContDiff ℝ ∞ (fun t : ℝ => 1 + Real.exp t) := by
    fun_prop
  have hlog : ContDiff ℝ ∞ (fun t : ℝ => Real.log (1 + Real.exp t)) :=
    hinner.log (by intro t; positivity)
  exact contDiff_const.add hlog

theorem deriv_c0Softplus (t : ℝ) :
    deriv c0Softplus t = Real.exp t / (1 + Real.exp t) := by
  change deriv (fun s : ℝ => 1 + Real.log (1 + Real.exp s)) t = _
  rw [deriv_const_add]
  have hinner : DifferentiableAt ℝ (fun s : ℝ => 1 + Real.exp s) t := by
    fun_prop
  have hlog : DifferentiableAt ℝ Real.log (1 + Real.exp t) :=
    Real.differentiableAt_log (by positivity)
  have hcomp := deriv_comp t hlog hinner
  have hfun : Real.log ∘ (fun s : ℝ => 1 + Real.exp s) =
      (fun s : ℝ => Real.log (1 + Real.exp s)) := rfl
  rw [← hfun, hcomp, Real.deriv_log, deriv_const_add, Real.deriv_exp]
  field_simp

theorem deriv_deriv_c0Softplus_nonneg (t : ℝ) :
    0 ≤ deriv (deriv c0Softplus) t := by
  have hfun : deriv c0Softplus = fun s : ℝ => Real.exp s / (1 + Real.exp s) :=
    funext deriv_c0Softplus
  have hnum : DifferentiableAt ℝ Real.exp t := Real.differentiableAt_exp
  have hden : DifferentiableAt ℝ (fun s : ℝ => 1 + Real.exp s) t :=
    hnum.const_add 1
  have hderiv := deriv_fun_div hnum hden (by positivity : 1 + Real.exp t ≠ 0)
  have hden' : deriv (fun s : ℝ => 1 + Real.exp s) t = Real.exp t := by
    rw [deriv_const_add, Real.deriv_exp]
  rw [hfun, hderiv, Real.deriv_exp, hden']
  ring_nf
  positivity

theorem one_le_c0Softplus (t : ℝ) : 1 ≤ c0Softplus t := by
  dsimp [c0Softplus]
  have hlog : 0 ≤ Real.log (1 + Real.exp t) :=
    Real.log_nonneg (by linarith [Real.exp_pos t])
  linarith

/-- On the nonnegative half-line, softplus grows at least linearly with slope `1/2`. -/
theorem c0Softplus_lower_bound_half (t : ℝ) (ht : 0 ≤ t) :
    1 + t / 2 ≤ c0Softplus t := by
  have hlog : t ≤ Real.log (1 + Real.exp t) := by
    calc
      t = Real.log (Real.exp t) := by rw [Real.log_exp]
      _ ≤ Real.log (1 + Real.exp t) :=
        Real.log_le_log (Real.exp_pos t) (by linarith [Real.exp_pos t])
  dsimp [c0Softplus]
  linarith

theorem deriv_c0Softplus_le_one (t : ℝ) : deriv c0Softplus t ≤ 1 := by
  rw [deriv_c0Softplus]
  apply (div_le_one₀ (by positivity : 0 < 1 + Real.exp t)).2
  linarith

private theorem integrable_of_continuous_volume
    (ω₀ : KahlerForm n M) {f : M → ℝ} (hf : Continuous f) : Integrable f ω₀.volume :=
  hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))


/-- Softplus has at most linear growth in L². -/
theorem c0_softplus_integral_sq_le
    (ω₀ : KahlerForm n M) {u : M → ℝ} (hu : Continuous u) :
    ∫ x, c0Softplus (u x) ^ 2 ∂ω₀.volume ≤
      (2 * (1 + Real.log 2) ^ 2 + 2) *
        (ω₀.volume.real Set.univ + ∫ x, u x ^ 2 ∂ω₀.volume) := by
  have hf : Continuous (fun x => c0Softplus (u x)) := continuous_c0Softplus.comp hu
  have hIleft := integrable_of_continuous_volume ω₀ (hf.pow 2)
  have hIright : Integrable (fun x =>
      (2 * (1 + Real.log 2) ^ 2 + 2) * (1 + u x ^ 2)) ω₀.volume :=
    integrable_of_continuous_volume ω₀
      ((continuous_const : Continuous fun _ : M => 2 * (1 + Real.log 2) ^ 2 + 2).mul
        ((continuous_const : Continuous fun _ : M => (1 : ℝ)).add (hu.pow 2)))
  have hIone : Integrable (fun _ : M => (1 : ℝ)) ω₀.volume :=
    integrable_of_continuous_volume ω₀ (continuous_const : Continuous fun _ : M => (1 : ℝ))
  have hIsq : Integrable (fun x => u x ^ 2) ω₀.volume :=
    integrable_of_continuous_volume ω₀ (hu.pow 2)
  have hmono : ∫ x, c0Softplus (u x) ^ 2 ∂ω₀.volume ≤
      ∫ x, (2 * (1 + Real.log 2) ^ 2 + 2) * (1 + u x ^ 2) ∂ω₀.volume :=
    integral_mono_ae hIleft hIright
      (Filter.Eventually.of_forall fun x => c0Softplus_sq_le (u x))
  calc
    ∫ x, c0Softplus (u x) ^ 2 ∂ω₀.volume ≤
        ∫ x, (2 * (1 + Real.log 2) ^ 2 + 2) * (1 + u x ^ 2) ∂ω₀.volume := hmono
    _ = (2 * (1 + Real.log 2) ^ 2 + 2) *
        (ω₀.volume.real Set.univ + ∫ x, u x ^ 2 ∂ω₀.volume) := by
      have hsum : ∫ x, (1 + u x ^ 2) ∂ω₀.volume =
          ω₀.volume.real Set.univ + ∫ x, u x ^ 2 ∂ω₀.volume := by
        rw [integral_add hIone hIsq, integral_const]
        simp
      rw [integral_const_mul, hsum]


/-- Lift a softplus essential bound to a pointwise bound using full support. -/
theorem c0_softplus_pointwise_of_essSup
    (ω₀ : KahlerForm n M) {u : M → ℝ} (hu : Continuous u) {C : ℝ} (hC : 0 ≤ C)
    (hess : eLpNormEssSup (c0CenteredSoftplus u) ω₀.volume ≤ ENNReal.ofReal C) :
    ∀ x, c0CenteredSoftplus u x ≤ C := by
  have hf : Continuous (c0CenteredSoftplus u) := continuous_c0Softplus.comp hu
  have hae : ∀ᵐ x ∂ω₀.volume, c0CenteredSoftplus u x ≤ C := by
    filter_upwards [ae_le_eLpNormEssSup (f := c0CenteredSoftplus u) (μ := ω₀.volume)] with x hx
    have hx' : ‖c0CenteredSoftplus u x‖ₑ ≤ ENNReal.ofReal C := hx.trans hess
    have hx'' : c0Softplus (u x) ≤ C :=
      (ENNReal.ofReal_le_ofReal_iff hC).mp (by
        simpa [Real.enorm_eq_ofReal_abs, c0CenteredSoftplus,
          abs_of_nonneg (c0Softplus_nonneg (u x))] using hx')
    change c0Softplus (u x) ≤ C
    exact hx''
  let U : Set M := {y | C < c0CenteredSoftplus u y}
  have hUopen : IsOpen U := isOpen_lt continuous_const hf
  have hUzero : ω₀.volume U = 0 := by
    apply measure_mono_null (s := U) (t := {y | ¬ c0CenteredSoftplus u y ≤ C})
    · intro y hy
      change C < c0CenteredSoftplus u y at hy
      exact not_le_of_gt hy
    · exact ae_iff.mp hae
  have hUempty : U = ∅ := hUopen.eq_empty_of_measure_zero hUzero
  intro x
  by_contra hx
  have hx' : x ∈ U := lt_of_not_ge hx
  rw [hUempty] at hx'
  simp at hx'

end KahlerForm
