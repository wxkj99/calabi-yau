module

public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.MongeAmpere.Estimates.C0.Softplus
public import CalabiYau.MongeAmpere.Estimates.C0.MoserLpIteration
public import CalabiYau.MongeAmpere.Estimates.C0.SubsolutionIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

public section

open scoped Manifold ContDiff
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

theorem c0_softplus_powered_recurrence
    (ω₀ : KahlerForm n M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    (hsub : ∀ x, -(n : ℝ) ≤ ω₀.laplacian u x)
    {κ C_S : ℝ} (hκ : 1 < κ) (hS : ω₀.SobolevInequality κ C_S) :
    ∀ k, eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ (k + 1)) ω₀.volume ≤
      c0MomentFactor n κ C_S k *
        eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ k) ω₀.volume := by
  intro k
  let q : ℝ := κ ^ k
  let p : ℝ := 2 * q
  let v : ℝ → ℝ := c0Softplus
  let h : ℝ → ℝ := fun t => v t ^ q
  let F : ℝ → ℝ := fun t => v t ^ (p + 1)
  have hq : 1 ≤ q := by
    dsimp [q]
    exact one_le_pow₀ hκ.le
  have hvpos (t : ℝ) : 1 ≤ v t := by
    simpa [v] using one_le_c0Softplus t
  have hv : ContDiff ℝ ∞ v := by
    simpa [v] using contDiff_c0Softplus
  have hh : ContDiff ℝ ∞ h := by
    rw [contDiff_iff_contDiffAt]
    intro t
    dsimp [h]
    exact (Real.contDiffAt_rpow_const_of_ne (lt_of_lt_of_le zero_lt_one (hvpos t)).ne').comp
      t (hv.contDiffAt)
  have hF : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro t
    dsimp [F]
    exact (Real.contDiffAt_rpow_const_of_ne (lt_of_lt_of_le zero_lt_one (hvpos t)).ne').comp
      t (hv.contDiffAt)
  have hv' (t : ℝ) : deriv v t = Real.exp t / (1 + Real.exp t) := by
    simpa [v] using deriv_c0Softplus t
  have hv'' (t : ℝ) : 0 ≤ deriv (deriv v) t := by
    simpa [v] using deriv_deriv_c0Softplus_nonneg t
  have hv'nonneg (t : ℝ) : 0 ≤ deriv v t := by rw [hv']; positivity
  have hv'le (t : ℝ) : deriv v t ≤ 1 := by
    simpa [v] using deriv_c0Softplus_le_one t
  have hpowderiv (r : ℝ) :
      deriv (fun t : ℝ => v t ^ r) = fun t => r * v t ^ (r - 1) * deriv v t := by
    funext t
    have houter := Real.hasDerivAt_rpow_const (x := v t) (p := r)
      (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (hvpos t))))
    have hinner := (hv.differentiable (by norm_num)).differentiableAt (x := t) |>.hasDerivAt
    have hcomp := (houter.comp t hinner).deriv
    simpa [Function.comp_def, mul_assoc] using hcomp
  have hF'' (t : ℝ) :
      (4 + 2 / q) * (deriv h t) ^ 2 ≤ deriv (deriv F) t := by
    have hdf := hpowderiv (p + 1)
    have hdf' : deriv F = fun s => (p + 1) * v s ^ p * deriv v s := by
      simpa [F] using hdf
    rw [hdf']
    have hsecond : deriv (fun s : ℝ => (p + 1) * v s ^ p * deriv v s) t =
        (p + 1) * (p * v t ^ (p - 1) * (deriv v t) ^ 2 +
          v t ^ p * deriv (deriv v) t) := by
      have hpowD : DifferentiableAt ℝ (fun s : ℝ => v s ^ p) t := by
        exact (Real.differentiableAt_rpow_const_of_ne p
          (ne_of_gt (lt_of_lt_of_le zero_lt_one (hvpos t)))).comp t
          ((hv.differentiable (by norm_num)).differentiableAt (x := t))
      have hv'D : DifferentiableAt ℝ (deriv v) t := by
        have h2le : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (by exact le_top)
        exact (hv.of_le h2le).differentiable_deriv_two.differentiableAt (x := t)
      rw [deriv_fun_mul (DifferentiableAt.const_mul hpowD (p + 1)) hv'D]
      rw [deriv_const_mul_field, hpowderiv p]
      ring
    rw [hsecond]
    have hcoef : (4 + 2 / q) * q ^ 2 ≤ (p + 1) * p := by
      dsimp [p]
      field_simp
      nlinarith [hq]
    have hpowrelation : v t ^ (2 * q - 2) ≤ v t ^ (p - 1) := by
      apply Real.rpow_le_rpow_of_exponent_le (by linarith [hvpos t])
      dsimp [p]
      linarith
    have hcore : (4 + 2 / q) * q ^ 2 * v t ^ (2 * q - 2) *
        (deriv v t) ^ 2 ≤ (p + 1) * p * v t ^ (p - 1) * (deriv v t) ^ 2 := by
      have hvpow2 : 0 ≤ v t ^ (2 * q - 2) := Real.rpow_nonneg (by linarith [hvpos t]) _
      have hv'2 : 0 ≤ (deriv v t) ^ 2 := sq_nonneg _
      have hcoeff : 0 ≤ (p + 1) * p * (deriv v t) ^ 2 := by positivity
      calc
        _ ≤ (p + 1) * p * v t ^ (2 * q - 2) * (deriv v t) ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef hvpow2) hv'2
        _ ≤ _ := by
          calc
            _ = ((p + 1) * p * v t ^ (2 * q - 2)) * (deriv v t) ^ 2 := by ring
            _ ≤ ((p + 1) * p * v t ^ (p - 1)) * (deriv v t) ^ 2 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpowrelation (by positivity)) hv'2
            _ = _ := by ring
    have hderiv_eq : deriv (fun s : ℝ => v s ^ q) t =
        q * v t ^ (q - 1) * deriv v t := by
      simpa using congrFun (hpowderiv q) t
    rw [hderiv_eq]
    have hpowmul : v t ^ (q - 1) * v t ^ (q - 1) = v t ^ (2 * q - 2) := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one (hvpos t))]
      congr 1
      ring
    have hmult : (q * v t ^ (q - 1) * deriv v t) ^ 2 =
        q ^ 2 * v t ^ (2 * q - 2) * (deriv v t) ^ 2 := by
      calc
        _ = q ^ 2 * (v t ^ (q - 1) * v t ^ (q - 1)) * (deriv v t) ^ 2 := by ring
        _ = _ := by rw [hpowmul]
    rw [hmult]
    have hv''nonneg := hv'' t
    have hcore' : (4 + 2 / q) * (q ^ 2 * v t ^ (2 * q - 2) *
        (deriv v t) ^ 2) ≤ (p + 1) * p * v t ^ (p - 1) * (deriv v t) ^ 2 := by
      convert hcore using 1; ring
    have hY : 0 ≤ v t ^ p * deriv (deriv v) t :=
      mul_nonneg (Real.rpow_nonneg (by linarith [hvpos t]) _) (hv'' t)
    nlinarith [mul_nonneg (by positivity : 0 ≤ p + 1) hY, hcore']
  let A : ℝ := p + 1
  let δ : ℝ := 4 + 2 / q
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A, p]
    positivity
  have hF' : deriv F = fun t => A * v t ^ (2 * q) * deriv v t := by
    have h := hpowderiv (p + 1)
    simpa [F, A, p] using h
  have hF'nonneg (t : ℝ) : 0 ≤ deriv F t := by
    rw [hF']
    exact mul_nonneg (mul_nonneg hA (Real.rpow_nonneg (by linarith [hvpos t]) _))
      (hv'nonneg t)
  have hF'le (t : ℝ) : deriv F t ≤ A * h t ^ 2 := by
    rw [hF']
    dsimp [h]
    have hvpow : 0 ≤ v t ^ (2 * q) := Real.rpow_nonneg (by linarith [hvpos t]) _
    have hpow : v t ^ (2 * q) = (v t ^ q) ^ 2 := by
      rw [← Real.rpow_natCast (v t ^ q) 2, ← Real.rpow_mul (by linarith [hvpos t])]
      congr 1
      ring
    calc
      A * v t ^ (2 * q) * deriv v t ≤ A * v t ^ (2 * q) * 1 :=
        mul_le_mul_of_nonneg_left (hv'le t) (mul_nonneg hA hvpow)
      _ = A * v t ^ (2 * q) := by ring
      _ = A * (v t ^ q) ^ 2 := by rw [hpow]
  have hCS : 0 ≤ max C_S 1 := le_trans (by norm_num) (le_max_right _ _)
  have hS' : ω₀.SobolevInequality κ (max C_S 1) :=
    hS.mono (le_max_left _ _)
  have hsob := subsolution_sobolev_step ω₀ hS' hCS hA hδ hu hsub hh hF hF''
    hF'nonneg hF'le
  have hfactor : δ⁻¹ * ((n : ℝ) * A) = (n : ℝ) * q / 2 := by
    dsimp [δ, A, p]
    field_simp
    ring
  have hsob' :
      (∫ x, |h (u x)| ^ (2 * κ) ∂ω₀.volume) ^ κ⁻¹ ≤
        (max C_S 1 * (1 + (n : ℝ) * q / 2)) *
          ∫ x, h (u x) ^ 2 ∂ω₀.volume := by
    convert hsob using 1
    rw [hfactor]
    ring
  let f : M → ℝ := c0CenteredSoftplus u
  let r₀ : ℝ := 2 * q
  let r₁ : ℝ := 2 * κ * q
  let D : ℝ := max C_S 1 * (1 + (n : ℝ) * q / 2)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hr₁ : 0 < r₁ := by dsimp [r₁]; positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hfcont : Continuous f := by
    dsimp [f, c0CenteredSoftplus]
    exact continuous_c0Softplus.comp hu.continuous
  have hfnonneg (x : M) : 0 ≤ f x := by
    dsimp [f, c0CenteredSoftplus]
    exact c0Softplus_nonneg _
  obtain ⟨C, hC⟩ := (isCompact_range hfcont).bddAbove
  have hbound (x : M) : ‖f x‖ ≤ max C 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg x)]
    exact (hC (Set.mem_range_self x)).trans (le_max_left _ _)
  have hfae : AEStronglyMeasurable f ω₀.volume := hfcont.measurable.aestronglyMeasurable
  have hmem₀ : MemLp f (ENNReal.ofReal r₀) ω₀.volume :=
    MemLp.of_bound hfae (max C 0) (Filter.Eventually.of_forall hbound)
  have hmem₁ : MemLp f (ENNReal.ofReal r₁) ω₀.volume :=
    MemLp.of_bound hfae (max C 0) (Filter.Eventually.of_forall hbound)
  have hLp₀ : lpNorm f (ENNReal.ofReal r₀) ω₀.volume =
      (∫ x, f x ^ r₀ ∂ω₀.volume) ^ r₀⁻¹ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hr₀)
      (ENNReal.ofReal_lt_top.ne) hfae]
    rw [ENNReal.toReal_ofReal hr₀.le]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp [Real.norm_eq_abs, abs_of_nonneg (hfnonneg x)]
  have hLp₁ : lpNorm f (ENNReal.ofReal r₁) ω₀.volume =
      (∫ x, f x ^ r₁ ∂ω₀.volume) ^ r₁⁻¹ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (ENNReal.ofReal_ne_zero_iff.mpr hr₁)
      (ENNReal.ofReal_lt_top.ne) hfae]
    rw [ENNReal.toReal_ofReal hr₁.le]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp [Real.norm_eq_abs, abs_of_nonneg (hfnonneg x)]
  have hsobF :
      (∫ x, f x ^ r₁ ∂ω₀.volume) ^ κ⁻¹ ≤ D * ∫ x, f x ^ r₀ ∂ω₀.volume := by
    have hpoint (x : M) : h (u x) = f x ^ q := by
      rfl
    have hpow (x : M) : (f x ^ q) ^ 2 = f x ^ r₀ := by
      dsimp [r₀]
      calc
        (f x ^ q) ^ 2 = (f x ^ q) ^ (2 : ℝ) := (Real.rpow_natCast (f x ^ q) 2).symm
        _ = f x ^ (q * 2) := (Real.rpow_mul (hfnonneg x) q 2).symm
        _ = f x ^ (2 * q) := by congr 1; ring
    have hpow' (x : M) : |h (u x)| ^ (2 * κ) = f x ^ r₁ := by
      rw [hpoint x, abs_of_nonneg (Real.rpow_nonneg (hfnonneg x) q)]
      calc
        (f x ^ q) ^ (2 * κ) = f x ^ (q * (2 * κ)) :=
          (Real.rpow_mul (hfnonneg x) q (2 * κ)).symm
        _ = f x ^ r₁ := by
          congr 1
          dsimp [r₁]
          ring
    have hInt : (∫ x, h (u x) ^ 2 ∂ω₀.volume) = ∫ x, f x ^ r₀ ∂ω₀.volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp [hpoint x, hpow x]
    have hInt' : (∫ x, |h (u x)| ^ (2 * κ) ∂ω₀.volume) =
        ∫ x, f x ^ r₁ ∂ω₀.volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => hpow' x
    simpa [D, hInt, hInt'] using hsob'
  let I : ℝ := ∫ x, f x ^ r₁ ∂ω₀.volume
  let J : ℝ := ∫ x, f x ^ r₀ ∂ω₀.volume
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun x => Real.rpow_nonneg (hfnonneg x) _
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun x => Real.rpow_nonneg (hfnonneg x) _
  have hroot : I ^ r₁⁻¹ ≤ D ^ r₀⁻¹ * J ^ r₀⁻¹ := by
    have hsobI : I ^ κ⁻¹ ≤ D * J := by simpa [I, J] using hsobF
    have hrpow := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hsobI
      (inv_nonneg.mpr hr₀.le)
    have hmul : (D * J) ^ r₀⁻¹ = D ^ r₀⁻¹ * J ^ r₀⁻¹ :=
      Real.mul_rpow hD hJ
    rw [← Real.rpow_mul hI, hmul] at hrpow
    have hexp : κ⁻¹ * r₀⁻¹ = r₁⁻¹ := by
      dsimp [r₀, r₁]
      field_simp
    rw [hexp] at hrpow
    exact hrpow
  have hLpReal : lpNorm f (ENNReal.ofReal r₁) ω₀.volume ≤
      D ^ r₀⁻¹ * lpNorm f (ENNReal.ofReal r₀) ω₀.volume := by
    rw [hLp₁, hLp₀]
    exact hroot
  have hE₀ : ENNReal.ofReal (lpNorm f (ENNReal.ofReal r₀) ω₀.volume) =
      eLpNorm f (ENNReal.ofReal r₀) ω₀.volume := ofReal_lpNorm hmem₀
  have hE₁ : ENNReal.ofReal (lpNorm f (ENNReal.ofReal r₁) ω₀.volume) =
      eLpNorm f (ENNReal.ofReal r₁) ω₀.volume := ofReal_lpNorm hmem₁
  have hErec : eLpNorm f (ENNReal.ofReal r₁) ω₀.volume ≤
      ENNReal.ofReal (D ^ r₀⁻¹) * eLpNorm f (ENNReal.ofReal r₀) ω₀.volume := by
    rw [← hE₁]
    have hright : 0 ≤ D ^ r₀⁻¹ * lpNorm f (ENNReal.ofReal r₀) ω₀.volume :=
      mul_nonneg (Real.rpow_nonneg hD _) lpNorm_nonneg
    calc
      ENNReal.ofReal (lpNorm f (ENNReal.ofReal r₁) ω₀.volume) ≤
          ENNReal.ofReal (D ^ r₀⁻¹ * lpNorm f (ENNReal.ofReal r₀) ω₀.volume) :=
        (ENNReal.ofReal_le_ofReal_iff hright).2 hLpReal
      _ = ENNReal.ofReal (D ^ r₀⁻¹) *
          eLpNorm f (ENNReal.ofReal r₀) ω₀.volume := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hD _), hE₀]
  have hfactorReal : D ^ r₀⁻¹ =
      (max C_S 1 * (1 + (n : ℝ) * (2 * κ ^ k) / 4)) ^ ((2 * κ ^ k)⁻¹) := by
    dsimp [D, r₀, q]
    congr 1; ring
  have hfactorENN : ENNReal.ofReal (D ^ r₀⁻¹) = c0MomentFactor n κ C_S k := by
    rw [hfactorReal]
    simp [c0MomentFactor]
  have hp₀ : c0MomentExponent κ k = ENNReal.ofReal r₀ := by
    rfl
  have hp₁ : c0MomentExponent κ (k + 1) = ENNReal.ofReal r₁ := by
    change ENNReal.ofReal (2 * κ ^ (k + 1)) = ENNReal.ofReal (2 * κ * κ ^ k)
    congr 1
    rw [pow_succ]
    ring
  rw [hp₁, hp₀, ← hfactorENN]
  exact hErec

end KahlerForm
