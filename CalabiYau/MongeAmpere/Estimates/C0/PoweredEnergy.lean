module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Kahler.Sobolev
import CalabiYau.MongeAmpere.Estimates.C0.PathEnergy
import CalabiYau.MongeAmpere.Estimates.C0.SubsolutionIteration
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

public section

open scoped Manifold ContDiff Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

private noncomputable def c0PowerExtension (p : ℝ) (t : ℝ) : ℝ :=
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  1 + (1 - b t) * (t ^ p - 1)

private theorem c0PowerExtension_contDiff (p : ℝ) :
    ContDiff ℝ ∞ (c0PowerExtension p) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hb : ContDiff ℝ ∞ (b : ℝ → ℝ) := b.contDiff
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hb1 : (b : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] fun _ => 1 := b.eventuallyEq_one
    have hF1 : c0PowerExtension p =ᶠ[𝓝 (0 : ℝ)] fun _ => 1 := by
      filter_upwards [hb1] with t ht
      change 1 + (1 - b t) * (t ^ p - 1) = 1
      rw [ht]
      ring
    exact ContDiffAt.congr_of_eventuallyEq
      (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (1 : ℝ)) 0) hF1
  · have hpow : ContDiffAt ℝ ∞ (fun t : ℝ => t ^ p) x :=
      Real.contDiffAt_rpow_const_of_ne hx
    change ContDiffAt ℝ ∞ (fun t => 1 + (1 - b t) * (t ^ p - 1)) x
    exact contDiffAt_const.add
      ((contDiff_const.sub hb).contDiffAt.mul (hpow.sub contDiffAt_const))

private theorem c0PowerExtension_eventuallyEq_rpow (p x : ℝ) (hx : 1 ≤ x) :
    c0PowerExtension p =ᶠ[𝓝 x] (fun t => t ^ p) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hdist : b.rOut < dist x 0 := by
    have hx' : 1 / 2 < x := by linarith
    simpa [b, Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ x)] using hx'
  have hdistCont : Continuous (fun t : ℝ => dist t 0) := continuous_id.dist continuous_const
  have hnear : ∀ᶠ t in 𝓝 x, b.rOut < dist t 0 :=
    hdistCont.continuousAt.eventually (Ioi_mem_nhds hdist)
  filter_upwards [hnear] with t ht
  have hb0 : b t = 0 := b.zero_of_le_dist ht.le
  change 1 + (1 - b t) * (t ^ p - 1) = t ^ p
  rw [hb0]
  ring

private theorem c0PowerExtension_eq_rpow (p x : ℝ) (hx : 1 ≤ x) :
    c0PowerExtension p x = x ^ p := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hdist : b.rOut ≤ dist x 0 := by
    have hx' : 1 / 2 ≤ x := by linarith
    simpa [b, Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ x)] using hx'
  have hb0 : b x = 0 := b.zero_of_le_dist hdist
  change 1 + (1 - b x) * (x ^ p - 1) = x ^ p
  rw [hb0]
  ring

private theorem c0PowerExtension_deriv (p x : ℝ) (hx : 1 ≤ x) :
    deriv (c0PowerExtension p) x = p * x ^ (p - 1) := by
  rw [(c0PowerExtension_eventuallyEq_rpow p x hx).deriv_eq]
  exact Real.deriv_rpow_const x p

private theorem c0PowerExtension_deriv_deriv (p x : ℝ) (hx : 1 ≤ x) :
    deriv (deriv (c0PowerExtension p)) x = p * (p - 1) * x ^ (p - 2) := by
  have hnear := c0PowerExtension_eventuallyEq_rpow p x hx
  calc
    deriv (deriv (c0PowerExtension p)) x =
        deriv (deriv (fun t : ℝ => t ^ p)) x := hnear.deriv.deriv_eq
    _ = p * (p - 1) * x ^ (p - 2) := by
      rw [Real.deriv_rpow_const']
      change deriv (fun t : ℝ => p * (t ^ (p - 1))) x = _
      rw [deriv_const_mul_field, Real.deriv_rpow_const]
      ring_nf

/-- The full Monge–Ampère weighted energy estimate for powers of a normalized potential.

The energy identity is obtained by testing along the segment of Kähler forms with a convex
power of -φ. The normalization -φ ≥ 1 absorbs the lower power on the right-hand side into the
same moment, leaving a coefficient linear in the test exponent. The coefficient is chosen before
G and φ, with dependence only on the displayed background data. -/
theorem c0_mongeAmpere_powered_energy
    (ω₀ : KahlerForm n M) {K : ℝ} (hK : 0 ≤ K) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ G φ : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G →
      (∀ x, |G x| ≤ K) → ω₀.SolvesMongeAmpere G φ →
      (∀ x, 1 ≤ -φ x) → ∀ q : ℝ, 2 ≤ q →
        ∫ x, ω₀.gradNormSq (fun y => (-φ y) ^ (q / 2)) x ∂ω₀.volume ≤
          A * q * ∫ x, (-φ x) ^ q ∂ω₀.volume := by
  let C : ℝ := 2 ^ n * (Real.exp K - 1)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hexp : 1 ≤ Real.exp K := by
      nlinarith [Real.add_one_le_exp K]
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro G φ hG hGbound hsol hφnorm q hq
  let u : M → ℝ := fun x => -φ x
  have hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u := by
    exact contDiff_neg.contMDiff.comp hsol.1.1
  let F : ℝ → ℝ := c0PowerExtension q
  let H : ℝ → ℝ := c0PowerExtension (q / 2)
  have hF : ContDiff ℝ ∞ F := c0PowerExtension_contDiff q
  have hH : ContDiff ℝ ∞ H := c0PowerExtension_contDiff (q / 2)
  have hFvalue (x : M) : F (u x) = (u x) ^ q := by
    exact c0PowerExtension_eq_rpow q (u x) (hφnorm x)
  have hHvalue (x : M) : H (u x) = (u x) ^ (q / 2) := by
    exact c0PowerExtension_eq_rpow (q / 2) (u x) (hφnorm x)
  have hF' (x : M) : deriv F (u x) = q * (u x) ^ (q - 1) := by
    exact c0PowerExtension_deriv q (u x) (hφnorm x)
  have hF'' (x : M) : deriv (deriv F) (u x) =
      q * (q - 1) * (u x) ^ (q - 2) := by
    exact c0PowerExtension_deriv_deriv q (u x) (hφnorm x)
  have hconv : ∀ x, 0 ≤ deriv (deriv F) (u x) := by
    intro x
    rw [hF'' x]
    have hq0 : 0 ≤ q := by linarith
    have hq1 : 0 ≤ q - 1 := by linarith
    have hu0 : 0 < u x := by linarith [hφnorm x]
    exact mul_nonneg (mul_nonneg hq0 hq1)
      (Real.rpow_nonneg hu0.le _)
  have henergy := ω₀.normalized_mongeAmpere_energy_bound hsol.1 hn hF hconv
  have hcompF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (F ∘ u) :=
    hF.contMDiff.comp hu
  have hcompH : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (H ∘ u) :=
    hH.contMDiff.comp hu
  have htargetFun : (fun x => (u x) ^ (q / 2)) = H ∘ u := by
    funext x
    exact (hHvalue x).symm
  have hgradPoint (x : M) :
      ω₀.gradNormSq (fun y => (u y) ^ (q / 2)) x ≤
        deriv (deriv F) (u x) * ω₀.gradNormSq u x := by
    rw [htargetFun, gradNormSq_comp ω₀ hu hH x,
      c0PowerExtension_deriv (q / 2) (u x) (hφnorm x), hF'' x]
    have huPos : 0 < u x := by linarith [hφnorm x]
    have hpow : ((u x) ^ (q / 2 - 1)) ^ 2 = (u x) ^ (q - 2) := by
      rw [← Real.rpow_two, ← Real.rpow_mul huPos.le]
      congr 1
      ring
    rw [mul_pow, hpow]
    have hcoef : (q / 2) ^ 2 ≤ q * (q - 1) := by
      nlinarith [sq_nonneg (q - 2)]
    have hnonneg : 0 ≤ (u x) ^ (q - 2) * ω₀.gradNormSq u x :=
      mul_nonneg (Real.rpow_nonneg (by linarith [hφnorm x]) _)
        (ω₀.gradNormSq_nonneg u x)
    have hqpow : (q / 2) ^ 2 * (u x) ^ (q - 2) ≤
        q * (q - 1) * (u x) ^ (q - 2) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg huPos.le _)
    calc
      ((q / 2) ^ 2 * (u x) ^ (q - 2)) * ω₀.gradNormSq u x ≤
          (q * (q - 1) * (u x) ^ (q - 2)) * ω₀.gradNormSq u x :=
        mul_le_mul_of_nonneg_right hqpow (ω₀.gradNormSq_nonneg u x)
      _ = q * (q - 1) * (u x) ^ (q - 2) * ω₀.gradNormSq u x := by ring
  have hIntTarget : Integrable
      (fun x => ω₀.gradNormSq (fun y => (u y) ^ (q / 2)) x) ω₀.volume := by
    rw [htargetFun]
    exact integrable_of_continuous_volume ω₀
      (ω₀.contMDiff_gradNormSq hcompH).continuous
  have hF''smooth : ContDiff ℝ ∞ (deriv (deriv F)) := by
    exact contDiff_infty_iff_deriv.mp
      (contDiff_infty_iff_deriv.mp hF |>.2) |>.2
  have hIntWeighted : Integrable
      (fun x => deriv (deriv F) (u x) * ω₀.gradNormSq u x) ω₀.volume :=
    integrable_of_continuous_volume ω₀
      ((hF''smooth.continuous.comp hu.continuous).mul
        (ω₀.contMDiff_gradNormSq hu).continuous)
  have hgradInt :
      ∫ x, ω₀.gradNormSq (fun y => (u y) ^ (q / 2)) x ∂ω₀.volume ≤
        ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume :=
    integral_mono_ae hIntTarget hIntWeighted (Filter.Eventually.of_forall hgradPoint)
  have hpowScale : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have henergyScaled :
      ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume ≤
        (2 : ℝ) ^ n *
          ∫ x, deriv F (u x) * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume := by
    calc
      _ = (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n *
          ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq φ x ∂ω₀.volume) := by
        have hgradNeg : ω₀.gradNormSq u = ω₀.gradNormSq φ := by
          funext x
          have hneg : ContDiff ℝ ∞ (fun t : ℝ => -t) := contDiff_neg
          simpa [u, Function.comp_def] using
            (gradNormSq_comp ω₀ hsol.1.1 hneg x)
        have hreplace :
            (∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume) =
              ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq φ x ∂ω₀.volume := by
          congr 1
          funext x
          rw [hgradNeg]
        rw [hreplace, ← mul_assoc, hpowScale, one_mul]
      _ ≤ (2 : ℝ) ^ n *
          ∫ x, deriv F (u x) * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume :=
        mul_le_mul_of_nonneg_left henergy (pow_nonneg (by norm_num) n)
  have hMAle (x : M) : ω₀.mongeAmpere φ x - 1 ≤ Real.exp K - 1 := by
    have hGx : G x ≤ K := (le_abs_self _).trans (hGbound x)
    rw [hsol.2 x]
    exact sub_le_sub_right (Real.exp_le_exp.mpr hGx) 1
  have hupperPoint (x : M) : deriv F (u x) * (ω₀.mongeAmpere φ x - 1) ≤
      q * (Real.exp K - 1) * (u x) ^ q := by
    rw [hF' x]
    have hu0 : 0 < u x := by linarith [hφnorm x]
    have hq0 : 0 ≤ q := by linarith
    have hpow0 : 0 ≤ (u x) ^ (q - 1) := Real.rpow_nonneg hu0.le _
    have hpowMono : (u x) ^ (q - 1) ≤ (u x) ^ q := by
      exact Real.rpow_le_rpow_of_exponent_le (hφnorm x) (by linarith)
    calc
      q * (u x) ^ (q - 1) * (ω₀.mongeAmpere φ x - 1) ≤
          q * (u x) ^ (q - 1) * (Real.exp K - 1) :=
        mul_le_mul_of_nonneg_left (hMAle x) (mul_nonneg hq0 hpow0)
      _ = q * (Real.exp K - 1) * (u x) ^ (q - 1) := by ring
      _ ≤ q * (Real.exp K - 1) * (u x) ^ q :=
        mul_le_mul_of_nonneg_left hpowMono (mul_nonneg hq0
          (sub_nonneg.mpr (by nlinarith [Real.add_one_le_exp K])))
  have hMAcont : Continuous (ω₀.mongeAmpere φ) :=
    (ω₀.contMDiff_mongeAmpere hsol.1.1).continuous
  have hF'cont : ContDiff ℝ ∞ (deriv F) := contDiff_infty_iff_deriv.mp hF |>.2
  have hIntLeft : Integrable
      (fun x => deriv F (u x) * (ω₀.mongeAmpere φ x - 1)) ω₀.volume :=
    integrable_of_continuous_volume ω₀
      ((hF'cont.continuous.comp hu.continuous).mul (hMAcont.sub continuous_const))
  have hIntRight : Integrable
      (fun x => q * (Real.exp K - 1) * (u x) ^ q) ω₀.volume := by
    have hfun : (fun x => q * (Real.exp K - 1) * (u x) ^ q) =
        fun x => q * (Real.exp K - 1) * F (u x) := by
      funext x
      rw [hFvalue x]
    rw [hfun]
    exact (integrable_of_continuous_volume ω₀ hcompF.continuous).const_mul _
  have hMAInt := integral_mono_ae hIntLeft hIntRight
    (Filter.Eventually.of_forall hupperPoint)
  rw [integral_const_mul] at hMAInt
  calc
    ∫ x, ω₀.gradNormSq (fun y => (-φ y) ^ (q / 2)) x ∂ω₀.volume =
        ∫ x, ω₀.gradNormSq (fun y => (u y) ^ (q / 2)) x ∂ω₀.volume := by
          rfl
    _ ≤ (2 : ℝ) ^ n *
        ∫ x, deriv F (u x) * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume :=
      hgradInt.trans henergyScaled
    _ ≤ (2 : ℝ) ^ n * (q * (Real.exp K - 1) *
        ∫ x, (u x) ^ q ∂ω₀.volume) := by
      have h2nonneg : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
      exact mul_le_mul_of_nonneg_left hMAInt h2nonneg
    _ = C * q * ∫ x, (-φ x) ^ q ∂ω₀.volume := by
      simp [C, u, mul_assoc, mul_left_comm, mul_comm]

end KahlerForm
