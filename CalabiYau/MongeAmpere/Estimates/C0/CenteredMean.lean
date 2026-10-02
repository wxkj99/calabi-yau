module

public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.MongeAmpere.Estimates.C0.Softplus
public import CalabiYau.MongeAmpere.Estimates.C0.MoserLpIteration
import CalabiYau.MongeAmpere.Estimates.C0.PathEnergy

public section

open scoped Manifold ContDiff ENNReal
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

private theorem integral_sq_eq_centered_add_mean
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} {m V : ℝ}
    (hf : Integrable f μ)
    (hcenter : Integrable (fun x => (f x - m) ^ 2) μ)
    (hmean : ∫ x, f x ∂μ = V * m)
    (hV : μ.real Set.univ = V) :
    ∫ x, f x ^ 2 ∂μ = ∫ x, (f x - m) ^ 2 ∂μ + V * m ^ 2 := by
  have hIcenter : Integrable (fun x => f x - m) μ := hf.sub (integrable_const _)
  have hIcross : Integrable (fun x => (2 * m) * (f x - m)) μ :=
    hIcenter.const_mul (2 * m)
  have hIconst : Integrable (fun _x : X => (m ^ 2 : ℝ)) μ := integrable_const _
  have hcenterMean : ∫ x, (f x - m) ∂μ = 0 := by
    rw [integral_sub hf (integrable_const _), integral_const]
    simp [hmean, hV, smul_eq_mul]
  have hpoint : ∀ x, f x ^ 2 =
      (f x - m) ^ 2 + ((2 * m) * (f x - m) + m ^ 2) := by
    intro x
    ring
  calc
    _ = ∫ x, ((f x - m) ^ 2 + ((2 * m) * (f x - m) + m ^ 2)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => hpoint x
    _ = (∫ x, (f x - m) ^ 2 ∂μ) +
        ∫ x, ((2 * m) * (f x - m) + m ^ 2) ∂μ :=
      integral_add hcenter (hIcross.add hIconst)
    _ = (∫ x, (f x - m) ^ 2 ∂μ) +
        ((2 * m) * (∫ x, (f x - m) ∂μ) + ∫ _x : X, (m ^ 2 : ℝ) ∂μ) := by
      rw [integral_add hIcross hIconst, integral_const_mul]
    _ = ∫ x, (f x - m) ^ 2 ∂μ + V * m ^ 2 := by
      rw [hcenterMean, integral_const, hV]
      simp [smul_eq_mul]

set_option maxHeartbeats 1000000 in

omit [ConnectedSpace M] in
/-- A centered softplus upper-tail estimate, together with the `p = 1` energy and Poincaré
inequalities, gives a uniform initial `L²` bound for a potential whose maximum is `-1`.

The recurrence and finite product are explicit inputs so this module does not depend on a private
theorem from `Estimates.C0`. The proof follows Székelyhidi, Proposition 3.15: `1 < κ` makes the
recurrence powers tend to infinity; then absorb the normalization mean using `m ≤ A + B√m` and
combine the resulting mean bound with Poincaré. -/
theorem c0_normalized_potential_L2_bound
    (ω₀ : KahlerForm n M) {κ C_S C_P K : ℝ}
    (hP : ω₀.PoincareInequality C_P) (hK : 0 ≤ K) (hκ : 1 < κ)
    {B : ENNReal} (hBne : B ≠ ⊤)
    (hprod : ∀ N,
      (∏ k ∈ Finset.range N, c0MomentFactor n κ C_S k) ≤ B)
    (hrec : ∀ {u : M → ℝ},
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u →
      (∀ x, -(n : ℝ) ≤ ω₀.laplacian u x) →
      ∀ k, eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ (k + 1)) ω₀.volume ≤
        c0MomentFactor n κ C_S k *
          eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ k) ω₀.volume) :
    ∃ L : ℝ, ∀ G φ : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G →
      (∀ x, |G x| ≤ K) → ω₀.SolvesMongeAmpere G φ →
      1 ≤ n → (∃ x₀, φ x₀ = -1) → (∀ x, 1 ≤ -φ x) →
      ∫ x, (-φ x) ^ 2 ∂ω₀.volume ≤ L := by
  classical
  let V : ℝ := ω₀.volume.real Set.univ
  let C₀ : ℝ := 2 * (1 + Real.log 2) ^ 2 + 2
  let D : ℝ := max C_P 0 * (2 : ℝ) ^ n * (Real.exp K - 1)
  let A : ℝ := B.toReal ^ 2 * (C₀ * V)
  let R : ℝ := 4 * A * (D + 1) + 1
  refine ⟨V * R ^ 2 + D * V * R, ?_⟩
  intro G φ hG hGbound hsol hn hx₀ hφnorm
  let ψ : M → ℝ := fun x => φ x - ⨍ y, φ y ∂ω₀.volume
  have hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ := by
    exact hsol.1.1.sub contMDiff_const
  have htrace (x : M) :
      0 ≤ ContinuousAlternatingMap.relTrace (ω₀ x)
        (ω₀ x + mddbar n φ x) := by
    exact ContinuousAlternatingMap.relTrace_nonneg (ω₀.isPositive x)
      (hsol.1.2 x).isNonneg
  have hphiLower (x : M) : -(n : ℝ) ≤ ω₀.laplacian φ x := by
    have htrace_eq : ContinuousAlternatingMap.relTrace (ω₀ x)
        (ω₀ x + mddbar n φ x) = (n : ℝ) + ω₀.laplacian φ x := by
      rw [ContinuousAlternatingMap.relTrace_add,
        ContinuousAlternatingMap.relTrace_self (ω₀.isPositive x)]
      rfl
    have ht := htrace x
    rw [htrace_eq] at ht
    linarith
  have hψlower (x : M) : -(n : ℝ) ≤ ω₀.laplacian ψ x := by
    have hsame : ω₀.laplacian ψ x = ω₀.laplacian φ x := by
      change ω₀.laplacian
        (fun y => φ y + -(⨍ z, φ z ∂ω₀.volume)) x = _
      rw [ω₀.laplacian_add_const]
    rw [hsame]
    exact hphiLower x
  have hsoftCont : Continuous (c0CenteredSoftplus ψ) := by
    change Continuous (fun x => c0Softplus (ψ x))
    exact continuous_c0Softplus.comp hψ.continuous
  have hess := c0_centered_softplus_essSup_bound_of_product ω₀ hψ hκ hprod
    hsoftCont.aestronglyMeasurable
    (fun k => hrec hψ hψlower k)
  let u : M → ℝ := fun x => -φ x
  have hWcont : Continuous u := continuous_neg.comp hsol.1.1.continuous
  let F : ℝ → ℝ := fun t => (1 / 2 : ℝ) * t ^ 2
  have hF : ContDiff ℝ ∞ F := by
    change ContDiff ℝ ∞ (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2)
    fun_prop
  have hF' : deriv F = fun t => t := by
    funext t
    change deriv (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) t = t
    rw [deriv_const_mul_field]
    have hpow : deriv (fun t : ℝ => t ^ 2) t = 2 * t := by
      change deriv ((fun t : ℝ => t) ^ 2) t = 2 * t
      rw [deriv_pow differentiableAt_id 2]
      norm_num
    rw [hpow]
    ring
  have hF'' : deriv (deriv F) = fun _ => 1 := by
    rw [hF']
    funext t
    simp
  have henergy := ω₀.normalized_mongeAmpere_energy_bound hsol.1 hn hF (by
    intro x
    rw [hF'']
    norm_num)
  have hMAcont : Continuous (ω₀.mongeAmpere φ) :=
    (ω₀.contMDiff_mongeAmpere hsol.1.1).continuous
  have hI₁ : Integrable (fun x => u x * (ω₀.mongeAmpere φ x - 1)) ω₀.volume :=
    (hWcont.mul (hMAcont.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))
  have hI₂ : Integrable (fun x => u x * (Real.exp K - 1)) ω₀.volume :=
    (hWcont.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))
  have hMAle (x : M) : ω₀.mongeAmpere φ x - 1 ≤ Real.exp K - 1 := by
    have hGx : G x ≤ K := (le_abs_self _).trans (hGbound x)
    rw [hsol.2 x]
    exact sub_le_sub_right (Real.exp_le_exp.mpr hGx) 1
  have hpt (x : M) : u x * (ω₀.mongeAmpere φ x - 1) ≤
      u x * (Real.exp K - 1) :=
    mul_le_mul_of_nonneg_left (hMAle x) (by linarith [hφnorm x])
  have hmono : ∫ x, u x * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume ≤
      ∫ x, u x * (Real.exp K - 1) ∂ω₀.volume :=
    integral_mono_ae hI₁ hI₂ (Filter.Eventually.of_forall hpt)
  have hexpK : 0 ≤ Real.exp K - 1 := by
    have := Real.add_one_le_exp K
    linarith
  have hupper : ∫ x, u x * (Real.exp K - 1) ∂ω₀.volume =
      (Real.exp K - 1) * ∫ x, u x ∂ω₀.volume := by
    calc
      _ = ∫ x, (Real.exp K - 1) * u x ∂ω₀.volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = (Real.exp K - 1) * ∫ x, u x ∂ω₀.volume := integral_const_mul _ _
  have hpow : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have henergy' : ∫ x, ω₀.gradNormSq φ x ∂ω₀.volume ≤
      (2 : ℝ) ^ n * (Real.exp K - 1) * ∫ x, u x ∂ω₀.volume := by
    have hmono₁ := hmono.trans_eq hupper
    have hscaled := mul_le_mul_of_nonneg_left henergy
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    rw [← mul_assoc, hpow, one_mul] at hscaled
    have hmono' := mul_le_mul_of_nonneg_left hmono₁
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    have hmono'' : (2 : ℝ) ^ n *
        ∫ x, deriv F (u x) * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume ≤
        (2 : ℝ) ^ n * ((Real.exp K - 1) * ∫ x, u x ∂ω₀.volume) := by
      simpa [hF'] using hmono'
    simpa [hF'', mul_one, mul_assoc] using hscaled.trans hmono''
  have hvariance := hP.mono (le_max_left C_P 0) |>.integral_sub_average_sq_le hsol.1.1
  have hvariance' : ∫ x, ψ x ^ 2 ∂ω₀.volume ≤
      D * ∫ x, u x ∂ω₀.volume := by
    have henergy'' := mul_le_mul_of_nonneg_left henergy'
      (le_max_right C_P 0)
    dsimp [ψ, D, u]
    calc
      _ ≤ max C_P 0 * ∫ x, ω₀.gradNormSq φ x ∂ω₀.volume := by
        simpa [ψ] using hvariance
      _ ≤ max C_P 0 * ((2 : ℝ) ^ n * (Real.exp K - 1) *
          ∫ x, -φ x ∂ω₀.volume) := henergy''
      _ = max C_P 0 * (2 : ℝ) ^ n * (Real.exp K - 1) *
          ∫ x, -φ x ∂ω₀.volume := by ring
  obtain ⟨x₀, hx₀⟩ := hx₀
  have hVposENN : 0 < ω₀.volume Set.univ :=
    isOpen_univ.measure_pos ω₀.volume ⟨x₀, Set.mem_univ _⟩
  have hVne : ω₀.volume Set.univ ≠ 0 := ne_of_gt hVposENN
  have hVtop : ω₀.volume Set.univ ≠ ⊤ := ne_of_lt (measure_lt_top ω₀.volume _)
  have hVpos : 0 < V := by
    dsimp [V]
    exact ENNReal.toReal_pos hVne hVtop
  have hVnonneg : 0 ≤ V := hVpos.le
  have hUint : Integrable u ω₀.volume :=
    hWcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))
  let m : ℝ := ⨍ x, u x ∂ω₀.volume
  have hmean : ∫ x, u x ∂ω₀.volume = V * m := by
    calc
      _ = ∫ _x, m ∂ω₀.volume := (integral_average ω₀.volume u).symm
      _ = V * m := by simp [V, m, smul_eq_mul]
  have hmeanLower : 1 ≤ m := by
    have hmass := integral_mono_ae (integrable_const (1 : ℝ)) hUint
      (Filter.Eventually.of_forall fun x => hφnorm x)
    have hmass' : V ≤ ∫ x, u x ∂ω₀.volume := by
      simpa [V, integral_const] using hmass
    by_contra hm
    have hmul : V * m < V * 1 := mul_lt_mul_of_pos_left (lt_of_not_ge hm) hVpos
    linarith [hmass', hmean]
  have hC₀ : 0 ≤ C₀ := by positivity
  have hsoftsq : ∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume ≤
      C₀ * (V + D * V * m) := by
    have hsoft := c0_softplus_integral_sq_le ω₀ hψ.continuous
    have hupper : V + ∫ x, ψ x ^ 2 ∂ω₀.volume ≤ V + D * V * m := by
      calc
        _ ≤ V + D * ∫ x, u x ∂ω₀.volume := by linarith [hvariance']
        _ = V + D * V * m := by rw [hmean]; ring
    calc
      _ ≤ C₀ * (V + ∫ x, ψ x ^ 2 ∂ω₀.volume) := by
        simpa [C₀, c0CenteredSoftplus] using hsoft
      _ ≤ C₀ * (V + D * V * m) := mul_le_mul_of_nonneg_left hupper hC₀
  obtain ⟨C, hC⟩ := (isCompact_range hsoftCont).bddAbove
  have hsoftNonneg (x : M) : 0 ≤ c0CenteredSoftplus ψ x :=
    c0Softplus_nonneg (ψ x)
  have hsoftBound : ∀ x, ‖c0CenteredSoftplus ψ x‖ ≤ max C 0 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hsoftNonneg x)]
    exact (hC (Set.mem_range_self x)).trans (le_max_left _ _)
  have hsoftMem : MemLp (c0CenteredSoftplus ψ) (c0MomentExponent κ 0) ω₀.volume :=
    MemLp.of_bound hsoftCont.aestronglyMeasurable (max C 0)
      (Filter.Eventually.of_forall hsoftBound)
  have hLpEq := hsoftMem.eLpNorm_eq_integral_rpow_norm
    (by
      change ENNReal.ofReal (2 * κ ^ 0) ≠ 0
      norm_num)
    (by
      change ENNReal.ofReal (2 * κ ^ 0) ≠ ⊤
      exact (ENNReal.ofReal_lt_top).ne)
  have hp0Real : (c0MomentExponent κ 0).toReal = 2 := by
    change (ENNReal.ofReal (2 * κ ^ 0)).toReal = 2
    norm_num
  have hp0Inv : (c0MomentExponent κ 0).toReal⁻¹ = (1 / 2 : ℝ) := by
    rw [hp0Real]
    norm_num
  have hLpIntegrand :
      (∫ x, ‖c0CenteredSoftplus ψ x‖ ^ (2 : ℝ) ∂ω₀.volume) =
        ∫ x, c0CenteredSoftplus ψ x ^ (2 : ℝ) ∂ω₀.volume := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      have hnorm : ‖c0CenteredSoftplus ψ x‖ = c0CenteredSoftplus ψ x :=
        (Real.norm_eq_abs _).trans (abs_of_nonneg (hsoftNonneg x))
      change ‖c0CenteredSoftplus ψ x‖ ^ 2 = c0CenteredSoftplus ψ x ^ 2
      rw [hnorm]
  have hLpNatIntegral :
      (∫ x, c0CenteredSoftplus ψ x ^ (2 : ℝ) ∂ω₀.volume) =
        ∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => Real.rpow_natCast _ 2
  have hLpRealEq :
      (eLpNorm (c0CenteredSoftplus ψ) (c0MomentExponent κ 0) ω₀.volume).toReal =
        Real.sqrt (∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume) := by
    rw [hLpEq, ENNReal.toReal_ofReal]
    · rw [hp0Inv, hp0Real]
      calc
        _ = (∫ x, c0CenteredSoftplus ψ x ^ (2 : ℝ) ∂ω₀.volume) ^ (1 / 2 : ℝ) := by
          rw [hLpIntegrand]
        _ = (∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume) ^ (1 / 2 : ℝ) :=
          congrArg (fun a : ℝ => a ^ (1 / 2 : ℝ)) hLpNatIntegral
        _ = Real.sqrt (∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume) :=
          (Real.sqrt_eq_rpow _).symm
    · positivity
  have hBnonneg : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have hsoftI_nonneg :
      0 ≤ ∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume :=
    integral_nonneg fun x => sq_nonneg _
  have hessProductEq : B * eLpNorm (c0CenteredSoftplus ψ)
      (c0MomentExponent κ 0) ω₀.volume = ENNReal.ofReal
        (B.toReal * Real.sqrt
          (∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume)) := by
    calc
      _ = ENNReal.ofReal B.toReal * ENNReal.ofReal
          (eLpNorm (c0CenteredSoftplus ψ) (c0MomentExponent κ 0)
            ω₀.volume).toReal := by
        calc
          _ = ENNReal.ofReal B.toReal *
              eLpNorm (c0CenteredSoftplus ψ) (c0MomentExponent κ 0)
                ω₀.volume :=
            congrArg (fun t : ENNReal => t *
              eLpNorm (c0CenteredSoftplus ψ) (c0MomentExponent κ 0)
                ω₀.volume) (ENNReal.ofReal_toReal hBne).symm
          _ = _ := congrArg (fun t : ENNReal => ENNReal.ofReal B.toReal * t)
            (ENNReal.ofReal_toReal hess.2.ne).symm
      _ = ENNReal.ofReal (B.toReal *
          (eLpNorm (c0CenteredSoftplus ψ) (c0MomentExponent κ 0)
            ω₀.volume).toReal) := by
        rw [← ENNReal.ofReal_mul hBnonneg]
      _ = _ := by rw [hLpRealEq]
  have hessBound : eLpNormEssSup (c0CenteredSoftplus ψ) ω₀.volume ≤
      ENNReal.ofReal
        (B.toReal * Real.sqrt (∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume)) := by
    exact hess.1.trans_eq hessProductEq
  have hsoftPoint := c0_softplus_pointwise_of_essSup ω₀ hψ.continuous
    (mul_nonneg hBnonneg (Real.sqrt_nonneg _)) hessBound
  have havgφ : (⨍ y, φ y ∂ω₀.volume) = -m := by
    calc
      (⨍ y, φ y ∂ω₀.volume) = ⨍ y, -u y ∂ω₀.volume := by
        congr 1
        funext y
        simp [u]
      _ = -(⨍ y, u y ∂ω₀.volume) := by simp
      _ = -m := by rfl
  have hψatx₀ : ψ x₀ = m - 1 := by
    dsimp [ψ]
    rw [hx₀, havgφ]
    ring
  have hψnonnegx₀ : 0 ≤ ψ x₀ := by rw [hψatx₀]; linarith
  have hSoft : ∀ t : ℝ, 0 ≤ t → 1 + t / 2 ≤ c0Softplus t := by
    intro t ht
    exact c0Softplus_lower_bound_half t ht
  have hsoftLower : (m + 1) / 2 ≤ c0CenteredSoftplus ψ x₀ := by
    have h := hSoft (ψ x₀) hψnonnegx₀
    rw [hψatx₀] at h
    change (m + 1) / 2 ≤ c0Softplus (ψ x₀)
    calc
      (m + 1) / 2 = 1 + (m - 1) / 2 := by ring
      _ ≤ c0Softplus (m - 1) := h
      _ = c0Softplus (ψ x₀) := by rw [← hψatx₀]
  have hsoftUpper : c0CenteredSoftplus ψ x₀ ≤
      B.toReal * Real.sqrt (∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume) :=
    hsoftPoint x₀
  have hsoftsqLower : ((m + 1) / 2) ^ 2 ≤
      (B.toReal * Real.sqrt
        (∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume)) ^ 2 := by
    have hleft : 0 ≤ (m + 1) / 2 := by linarith
    have hright : 0 ≤ B.toReal * Real.sqrt
        (∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume) :=
      mul_nonneg hBnonneg (Real.sqrt_nonneg _)
    nlinarith
  have hsoftsqUpper :
      (B.toReal * Real.sqrt
        (∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume)) ^ 2 ≤
      B.toReal ^ 2 * (C₀ * (V + D * V * m)) := by
    rw [mul_pow, Real.sq_sqrt hsoftI_nonneg]
    exact mul_le_mul_of_nonneg_left hsoftsq (sq_nonneg B.toReal)
  have hmeanQuadratic : (m + 1) ^ 2 ≤ 4 * A * (1 + D * m) := by
    dsimp [A]
    nlinarith [hsoftsqLower, hsoftsqUpper]
  have hmeanCap : m ≤ 4 * A * (D + 1) + 1 := by
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hfactor : 1 + D * m ≤ (D + 1) * (m + 1) := by
      calc
        1 + D * m = (D + 1) * (m + 1) - (m + D) := by ring
        _ ≤ (D + 1) * (m + 1) :=
          sub_le_self _ (add_nonneg (le_trans (by norm_num) hmeanLower) hD)
    have hquadratic' : (m + 1) ^ 2 ≤
        (4 * A * (D + 1)) * (m + 1) := by
      calc
        (m + 1) ^ 2 ≤ 4 * A * (1 + D * m) := hmeanQuadratic
        _ ≤ 4 * A * ((D + 1) * (m + 1)) :=
          mul_le_mul_of_nonneg_left hfactor (by positivity)
        _ = (4 * A * (D + 1)) * (m + 1) := by ring
    have hfactorBound : m + 1 ≤ 4 * A * (D + 1) := by
      by_contra hn
      have hgt : 4 * A * (D + 1) < m + 1 := lt_of_not_ge hn
      have hmPlusPos : 0 < m + 1 := by linarith [hmeanLower]
      have hmul : (4 * A * (D + 1)) * (m + 1) < (m + 1) ^ 2 :=
        (mul_lt_mul_of_pos_right hgt hmPlusPos).trans_eq (by ring)
      exact (not_lt_of_ge hquadratic') hmul
    linarith
  have hcenterEq (x : M) : u x - m = -ψ x := by
    dsimp [u, ψ]
    rw [havgφ]
    ring
  have huVariance : ∫ x, (u x - m) ^ 2 ∂ω₀.volume =
      ∫ x, ψ x ^ 2 ∂ω₀.volume := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (u x - m) ^ 2 = ψ x ^ 2
      calc
        (u x - m) ^ 2 = (-ψ x) ^ 2 :=
          congrArg (fun t : ℝ => t ^ 2) (hcenterEq x)
        _ = ψ x ^ 2 := by ring
  have hIvar : Integrable (fun x => (u x - m) ^ 2) ω₀.volume :=
    (hWcont.sub continuous_const).pow 2 |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ
        (Set.subset_univ _))
  have huSecondMoment : ∫ x, u x ^ 2 ∂ω₀.volume =
      ∫ x, ψ x ^ 2 ∂ω₀.volume + V * m ^ 2 := by
    have h := integral_sq_eq_centered_add_mean ω₀.volume hUint hIvar hmean (by rfl)
    rw [huVariance] at h
    exact h
  have hmR : m ≤ R := by
    dsimp [R]
    exact hmeanCap
  have hRnonneg : 0 ≤ R := by dsimp [R]; positivity
  have hmSq : m ^ 2 ≤ R ^ 2 := by nlinarith [hmeanLower, hmR]
  have henergyFinal : ∫ x, u x ^ 2 ∂ω₀.volume ≤ V * R ^ 2 + D * V * R := by
    rw [huSecondMoment]
    have hvarianceFinal : ∫ x, ψ x ^ 2 ∂ω₀.volume ≤ D * V * R := by
      calc
        _ ≤ D * ∫ x, u x ∂ω₀.volume := hvariance'
        _ = D * V * m := by rw [hmean]; ring
        _ ≤ D * V * R := by
          exact mul_le_mul_of_nonneg_left hmR (by positivity)
    have hmeanFinal : V * m ^ 2 ≤ V * R ^ 2 :=
      mul_le_mul_of_nonneg_left hmSq hVnonneg
    linarith
  simpa [u] using henergyFinal
end KahlerForm
