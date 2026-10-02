module

public import CalabiYau.Analysis.Elliptic.Schauder.InteriorProvider.Order
public import CalabiYau.Analysis.Elliptic.Schauder.FiniteDifferenceHolder
public import CalabiYau.Analysis.Elliptic.Schauder.SecondJetLimit
import CalabiYau.Analysis.Elliptic.Schauder.FirstOrderRegularity.QuotientEstimate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# First-order Schauder regularity

This is the initial `k = 0` to `k = 1` step for the exact fixed-order slices. The input solution
is only assumed `C²`; its first derivatives need not be `C²`, so the order-zero result cannot be
applied directly to them. The bridge instead has to regularize the translated difference quotients
on nested domains, obtain uniform order-zero estimates (including the coefficient commutators), and
pass to the limit using stability of the Hölder bounds.
-/

open Set Matrix Filter Metric
open scoped Manifold ContDiff NNReal ENNReal Topology

@[expose] public section

/-- A short signed translation of a closed ball remains in the corresponding larger open ball. -/
private theorem first_order_closedBall_translate_into_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (center v : E) {r R h : ℝ}
    (hv : ‖v‖ ≤ 1) (hh : |h| < R - r) :
    ∀ x ∈ Metric.closedBall center r, x + h • v ∈ Metric.ball center R := by
  intro x hx
  have hxdist : dist x center ≤ r := Metric.mem_closedBall.mp hx
  have hstep : ‖h • v‖ ≤ |h| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg h) hv
  rw [Metric.mem_ball]
  calc
    dist (x + h • v) center ≤ dist (x + h • v) x + dist x center := dist_triangle _ _ _
    _ = ‖h • v‖ + dist x center := by simp [dist_eq_norm, add_sub_cancel_left]
    _ ≤ |h| + r := add_le_add hstep hxdist
    _ < R := by linarith

/-- The positive step sequence `η/(m+1)` tends to zero. -/
private theorem first_order_reciprocal_step_tendsto_zero (η : ℝ) :
    Tendsto (fun m : ℕ => η * (((m : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
  have hden : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hden
  simpa using (tendsto_const_nhds.mul hinv :
    Tendsto (fun m : ℕ => η * (((m : ℝ) + 1)⁻¹)) atTop (𝓝 (η * 0)))

/-- C² regularity of a translated quotient on a local set whose translates stay in a larger
  C² domain. -/
private theorem first_differenceQuotient_contDiffOn_of_shift_to
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D U : Set E} {f : E → ℝ} {v : E} {h : ℝ}
    (hf : ContDiffOn ℝ 2 f U) (hDU : D ⊆ U)
    (hshift : ∀ x ∈ D, x + h • v ∈ U) :
    ContDiffOn ℝ 2 (fun x ↦ (f (x + h • v) - f x) / h) D := by
  have hfD : ContDiffOn ℝ 2 f D := hf.mono hDU
  have ht : ContDiffOn ℝ 2 (fun x : E => x + h • v) D := by fun_prop
  have hcomp : ContDiffOn ℝ 2 (fun x => f (x + h • v)) D := hf.comp ht hshift
  exact (hcomp.sub hfD).div_const h

/-- The directional derivative along the translated segment is interval integrable whenever the
  entire path lies in a ball of C¹ regularity. -/
private theorem first_differenceQuotient_intervalIntegrable_centered
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {center : E} {R : ℝ} {f : E → ℝ}
    (hf : ContDiffOn ℝ 1 f (Metric.ball center R))
    {v : E} {h : ℝ} {x : E}
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      x + t • (h • v) ∈ Metric.ball center R) :
    IntervalIntegrable (fun t : ℝ => (fderiv ℝ f (x + t • (h • v))) v)
      MeasureTheory.volume 0 1 := by
  let γ : ℝ → E := fun t ↦ x + t • (h • v)
  have hfdcont : ContinuousOn (fderiv ℝ f) (Metric.ball center R) :=
    hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hγcont : Continuous γ :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hγmaps : Set.MapsTo γ (Set.uIcc (0 : ℝ) 1) (Metric.ball center R) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    simpa [γ] using hpath t ht'
  have hfdγ : ContinuousOn (fun t : ℝ => fderiv ℝ f (γ t)) (Set.uIcc 0 1) :=
    hfdcont.comp hγcont.continuousOn hγmaps
  have hval : ContinuousOn (fun t : ℝ => (fderiv ℝ f (γ t)) v) (Set.uIcc 0 1) :=
    hfdγ.clm_apply continuousOn_const
  simpa [γ] using hval.intervalIntegrable

/-- Interval FTC representation of a translated first difference quotient. -/
private theorem first_differenceQuotient_eq_intervalIntegral
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {center : E} {R : ℝ} {f : E → F}
    (hf : ContDiffOn ℝ 1 f (Metric.ball center R))
    {v : E} {h : ℝ} {x : E}
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      x + t • (h • v) ∈ Metric.ball center R)
    (hh : h ≠ 0) :
    h⁻¹ • (f (x + h • v) - f x) =
      ∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • (h • v))) v := by
  let γ : ℝ → E := fun t ↦ x + t • (h • v)
  have hγ : ∀ t, HasDerivAt γ (h • v) t := by
    intro t
    simpa [γ] using (hasDerivAt_id t).smul_const (h • v) |>.const_add x
  have hcomp : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (f ∘ γ)
      ((fderiv ℝ f (γ t)) (h • v)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hγball : γ t ∈ Metric.ball center R := by
      simpa [γ] using hpath t ht'
    have hdiff : DifferentiableAt ℝ f (γ t) :=
      (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hγball)).differentiableAt (by norm_num)
    simpa [Function.comp_def, γ] using hdiff.hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hfact : ∀ t, (fderiv ℝ f (γ t)) (h • v) =
      h • ((fderiv ℝ f (γ t)) v) := by
    intro t
    rw [(fderiv ℝ f (γ t)).map_smul]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (f ∘ γ)
      (h • ((fderiv ℝ f (γ t)) v)) t := by
    intro t ht
    rw [← hfact]
    exact hcomp t ht
  have hHint : IntervalIntegrable (fun t : ℝ => h • ((fderiv ℝ f (γ t)) v))
      MeasureTheory.volume 0 1 := by
    have hfdcont : ContinuousOn (fderiv ℝ f) (Metric.ball center R) :=
      hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
    have hγcont : Continuous γ :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hγmaps : Set.MapsTo γ (Set.uIcc (0 : ℝ) 1) (Metric.ball center R) := by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have hb := hpath t ht'
      simpa [γ] using hb
    have hfdγ : ContinuousOn (fun t : ℝ => fderiv ℝ f (γ t)) (Set.uIcc 0 1) :=
      hfdcont.comp hγcont.continuousOn hγmaps
    have hval : ContinuousOn (fun t : ℝ => (fderiv ℝ f (γ t)) v) (Set.uIcc 0 1) :=
      hfdγ.clm_apply continuousOn_const
    have hcont : ContinuousOn
        (fun t : ℝ => h • ((fderiv ℝ f (γ t)) v)) (Set.uIcc 0 1) :=
      continuousOn_const.smul hval
    exact hcont.intervalIntegrable
  have hftc : ∫ t in (0 : ℝ)..1, h • ((fderiv ℝ f (γ t)) v) =
      (f ∘ γ) 1 - (f ∘ γ) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hHint
  have hconst : ∫ t in (0 : ℝ)..1, h • ((fderiv ℝ f (γ t)) v) =
      h • ∫ t in (0 : ℝ)..1, (fderiv ℝ f (γ t)) v :=
    intervalIntegral.integral_smul h (fun t : ℝ => (fderiv ℝ f (γ t)) v)
  have heq : h • ∫ t in (0 : ℝ)..1, (fderiv ℝ f (γ t)) v =
      f (x + h • v) - f x := by
    rw [← hconst, hftc]
    simp [γ]
  rw [← heq]
  simp [γ, smul_smul, inv_mul_cancel₀ hh]

/-- Uniform continuity of the directional derivative on a buffered set gives the integrand control
needed for uniform convergence. `hstep` records that the chosen signed steps tend to zero. -/
private theorem first_differenceQuotient_derivative_control_of_uniformContinuity
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K B : Set E} {f : E → F} {v : E} {h : ℕ → ℝ}
    (hKB : K ⊆ B)
    (hpath : ∀ m x, x ∈ K → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      x + t • (h m • v) ∈ B)
    (hUC : UniformContinuousOn (fun x ↦ (fderiv ℝ f x) v) B)
    (hstep : ∀ δ > 0, ∀ᶠ m in atTop, |h m| < δ)
    (hv : ‖v‖ ≤ 1) :
    ∀ ε > 0, ∀ᶠ m in atTop, ∀ x ∈ K, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖(fderiv ℝ f (x + t • (h m • v))) v - (fderiv ℝ f x) v‖ ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hmodδ⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUC) (ε / 2) (by positivity)
  filter_upwards [hstep δ hδ] with m hm
  intro x hx t ht
  have hxB : x ∈ B := hKB hx
  have hyB : x + t • (h m • v) ∈ B := hpath m x hx t ht
  have htabs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdist : dist (x + t • (h m • v)) x ≤ |h m| := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      norm_smul, Real.norm_eq_abs]
    calc
      |t| * (|h m| * ‖v‖) ≤ 1 * (|h m| * 1) := by gcongr
      _ = |h m| := by ring
  have hsmall : dist (x + t • (h m • v)) x < δ := lt_of_le_of_lt hdist hm
  have hclose := hmodδ (x + t • (h m • v)) hyB x hxB hsmall
  rw [dist_eq_norm] at hclose
  exact hclose.le.trans (by linarith)

/-- The interval FTC average and uniform control of its integrand imply uniform convergence of
  difference quotients to the directional derivative. -/
private theorem first_differenceQuotient_tendstoUniformlyOn_of_FTC_average
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K : Set E} {f : E → F} {v : E} {h : ℕ → ℝ}
    (hInt : ∀ m x, x ∈ K →
      IntervalIntegrable (fun t : ℝ ↦ (fderiv ℝ f (x + t • (h m • v))) v)
        MeasureTheory.volume 0 1)
    (havg : ∀ m x, x ∈ K →
      (h m)⁻¹ • (f (x + h m • v) - f x) =
        ∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • (h m • v))) v)
    (hcontrol : ∀ ε > 0, ∀ᶠ m in atTop, ∀ x ∈ K, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖(fderiv ℝ f (x + t • (h m • v))) v - (fderiv ℝ f x) v‖ ≤ ε) :
    TendstoUniformlyOn (fun m x ↦ (h m)⁻¹ • (f (x + h m • v) - f x))
      (fun x ↦ (fderiv ℝ f x) v) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hcontrol' := hcontrol (ε / 2) (by positivity)
  filter_upwards [hcontrol'] with m hm
  intro x hx
  have hdiffInt : IntervalIntegrable
      (fun t : ℝ ↦ (fderiv ℝ f (x + t • (h m • v))) v - (fderiv ℝ f x) v)
      MeasureTheory.volume 0 1 := by
    exact (hInt m x hx).sub intervalIntegrable_const
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (fun t ht => by
        have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        exact hm x hx t ht')
  have hconst : ∫ t in (0 : ℝ)..1, (fderiv ℝ f x) v = (fderiv ℝ f x) v := by simp
  have hdiff : (h m)⁻¹ • (f (x + h m • v) - f x) - (fderiv ℝ f x) v =
      ∫ t in (0 : ℝ)..1,
        ((fderiv ℝ f (x + t • (h m • v))) v - (fderiv ℝ f x) v) := by
    calc
      (h m)⁻¹ • (f (x + h m • v) - f x) - (fderiv ℝ f x) v =
          (∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • (h m • v))) v) -
            (fderiv ℝ f x) v := by rw [havg m x hx]
      _ = (∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • (h m • v))) v) -
            ∫ t in (0 : ℝ)..1, (fderiv ℝ f x) v :=
        congrArg (fun z : F => (∫ t in (0 : ℝ)..1,
          (fderiv ℝ f (x + t • (h m • v))) v) - z) hconst.symm
      _ = ∫ t in (0 : ℝ)..1,
          ((fderiv ℝ f (x + t • (h m • v))) v - (fderiv ℝ f x) v) :=
        (intervalIntegral.integral_sub (hInt m x hx) intervalIntegrable_const).symm
  have hNorm :
      ‖(h m)⁻¹ • (f (x + h m • v) - f x) - (fderiv ℝ f x) v‖ ≤ ε / 2 := by
    rw [hdiff]
    simpa using hnorm
  have hdistNorm :
      dist ((fderiv ℝ f x) v) ((h m)⁻¹ • (f (x + h m • v) - f x)) =
        ‖(h m)⁻¹ • (f (x + h m • v) - f x) - (fderiv ℝ f x) v‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  rw [hdistNorm]
  exact lt_of_le_of_lt hNorm (by linarith)

/-- An FTC average and uniform continuity on a buffer yield uniform convergence of difference
quotients to the directional derivative on the compact target. -/
private theorem first_differenceQuotient_tendstoUniformlyOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {K B : Set E} {f : E → F} {v : E} {h : ℕ → ℝ}
    (hKB : K ⊆ B)
    (hpath : ∀ m x, x ∈ K → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      x + t • (h m • v) ∈ B)
    (hUC : UniformContinuousOn (fun x ↦ (fderiv ℝ f x) v) B)
    (hstep : ∀ δ > 0, ∀ᶠ m in atTop, |h m| < δ)
    (hv : ‖v‖ ≤ 1)
    (hInt : ∀ m x, x ∈ K →
      IntervalIntegrable (fun t : ℝ ↦ (fderiv ℝ f (x + t • (h m • v))) v)
        MeasureTheory.volume 0 1)
    (havg : ∀ m x, x ∈ K →
      (h m)⁻¹ • (f (x + h m • v) - f x) =
        ∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • (h m • v))) v) :
    TendstoUniformlyOn (fun m x ↦ (h m)⁻¹ • (f (x + h m • v) - f x))
      (fun x ↦ (fderiv ℝ f x) v) atTop K := by
  apply first_differenceQuotient_tendstoUniformlyOn_of_FTC_average hInt havg
  exact first_differenceQuotient_derivative_control_of_uniformContinuity
    hKB hpath hUC hstep hv

/-- A uniform limit of C²α quotients on nested balls is C² on the innermost ball. This packages
  the published second-jet compactness/compatibility theorem for the first-order stability step. -/
private theorem first_order_directional_limit_contDiffOn_two {n : ℕ}
    {center : EuclideanSpace ℂ (Fin n)} {r R S : ℝ} {α C : ℝ≥0}
    (hR : r < R) (hS : R < S) (hα : 0 < α) (hαone : α ≤ 1)
    {q : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {g : EuclideanSpace ℂ (Fin n) → ℝ}
    (hsmooth : ∀ m, ContDiffOn ℝ 2 (q m) (Metric.ball center S))
    (hbound : ∀ m, HolderBoundOn 2 α C (Metric.closedBall center R) (q m))
    (hlimit : TendstoUniformlyOn q g atTop (Metric.closedBall center R)) :
    ContDiffOn ℝ 2 g (Metric.ball center r) ∧
      HolderBoundOn 2 α C (Metric.closedBall center r) g := by
  exact CalabiYau.Schauder.secondJetLimit_on_nested_balls
    hR hS hα hαone hsmooth hbound hlimit

/-- Pass a common `HolderBoundOn 2` estimate through locally uniform convergence of its full
  second-jet sequence. This is the exact target-bound limit step used after local regularity. -/
private theorem first_order_holderBoundOn_of_locallyUniformlyConvergent_jets
    {n : ℕ} {K : Set (EuclideanSpace ℂ (Fin n))}
    {α C : ℝ≥0} {q : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {φ : ℕ → ℕ} {g : EuclideanSpace ℂ (Fin n) → ℝ}
    (hbound : ∀ m, HolderBoundOn 2 α C K (q m))
    (hjets : ∀ j ≤ 2, TendstoLocallyUniformlyOn
      (fun m => iteratedFDeriv ℝ j (q (φ m)))
      (iteratedFDeriv ℝ j g) atTop K) :
    HolderBoundOn 2 α C K g := by
  have hsecond := CalabiYau.Schauder.secondDerivative_holderBoundOn_of_tendstoLocallyUniformlyOn
    (fun m => hbound (φ m)) (hjets 2 le_rfl)
  refine ⟨?_, hsecond.1⟩
  intro j hj x hx
  have hnorm : Tendsto
      (fun m => ‖iteratedFDeriv ℝ j (q (φ m)) x‖)
      atTop (𝓝 ‖iteratedFDeriv ℝ j g x‖) := ((hjets j hj).tendsto_at hx).norm
  exact le_of_tendsto hnorm (Eventually.of_forall fun m => (hbound (φ m)).1 j hj x hx)

/-- Local C² regularity of a directional derivative follows from the uniform quotient bounds on
  a slightly larger ball and the FTC uniform limit on a buffered ball. -/
private theorem first_order_directional_derivative_contDiffOn_local
    {n : ℕ} {α : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hlocal : ∀ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W →
      IsCompact (closure W) → closure W ⊆ U →
      ∃ C' : ℝ≥0, (∃ δ : ℝ, 0 < δ ∧
        ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 → 0 < |h| → |h| < δ →
          (∀ z ∈ closure W, z + h • v ∈ U) →
          HolderBoundOn 2 α C' (closure W) (fun z ↦ (u (z + h • v) - u z) / h)))
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (center : EuclideanSpace ℂ (Fin n)) {r R S T : ℝ}
    (_hr : 0 < r) (hR : r < R) (hS : R < S) (hT : S < T)
    (hTU : Metric.closedBall center T ⊆ U)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) :
    ∃ Cq : ℝ≥0, ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ u x v) (Metric.ball center r) ∧
      HolderBoundOn 2 α Cq (Metric.closedBall center r)
        (fun x ↦ fderiv ℝ u x v) := by
  have hTgap : 0 < T - S := by linarith
  have hRT : R < T := hS.trans hT
  have hclosureR : closure (Metric.ball center R) ⊆ Metric.closedBall center R :=
    Metric.closure_ball_subset_closedBall
  have hcompactR : IsCompact (closure (Metric.ball center R)) :=
    (isCompact_closedBall center R).of_isClosed_subset isClosed_closure hclosureR
  have hclosureRU : closure (Metric.ball center R) ⊆ U := by
    exact hclosureR.trans
      ((Metric.closedBall_subset_closedBall hRT.le).trans hTU)
  have hclosureS : closure (Metric.ball center S) ⊆ Metric.closedBall center S :=
    Metric.closure_ball_subset_closedBall
  have hcompactS : IsCompact (closure (Metric.ball center S)) :=
    (isCompact_closedBall center S).of_isClosed_subset isClosed_closure hclosureS
  have hclosureSU : closure (Metric.ball center S) ⊆ U := by
    exact hclosureS.trans ((Metric.closedBall_subset_closedBall hT.le).trans hTU)
  obtain ⟨Cq, hqFamily⟩ := hlocal (Metric.ball center S) Metric.isOpen_ball
    hcompactS hclosureSU
  obtain ⟨δq, hδq, hqUniform⟩ := hqFamily
  let η : ℝ := min δq (T - S) / 2
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hηq : η < δq := by
    have hmin := min_le_left δq (T - S)
    dsimp [η]
    linarith
  have hηbuf : η < T - S := by
    have hmin := min_le_right δq (T - S)
    dsimp [η]
    linarith
  let h : ℕ → ℝ := fun m ↦ η * (((m : ℝ) + 1)⁻¹)
  have hseq : Tendsto h atTop (𝓝 0) := by
    simpa [h] using first_order_reciprocal_step_tendsto_zero η
  have hstep : ∀ ε > 0, ∀ᶠ m in atTop, |h m| < ε := by
    intro ε hε
    have hevent := hseq.eventually (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hevent] with m hm
    have hdist : dist (h m) 0 < ε := Metric.mem_ball.mp hm
    simpa [dist_eq_norm, Real.norm_eq_abs] using hdist
  have hpos (m : ℕ) : 0 < h m := by
    dsimp [h]
    positivity
  have hdenpos (m : ℕ) : 0 < (m : ℝ) + 1 := by positivity
  have hdenle (m : ℕ) : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hinvle (m : ℕ) : (((m : ℝ) + 1)⁻¹) ≤ 1 :=
    (inv_le_one₀ (hdenpos m)).2 (hdenle m)
  have hleη (m : ℕ) : h m ≤ η := by
    dsimp [h]
    calc
      η * (((m : ℝ) + 1)⁻¹) ≤ η * 1 :=
        mul_le_mul_of_nonneg_left (hinvle m) (le_of_lt hηpos)
      _ = η := by simp
  have hsmallq (m : ℕ) : |h m| < δq := by
    rw [abs_of_pos (hpos m)]
    exact (hleη m).trans_lt hηq
  have hsmallbuf (m : ℕ) : |h m| < T - S := by
    rw [abs_of_pos (hpos m)]
    exact (hleη m).trans_lt hηbuf
  have hvle : ‖v‖ ≤ 1 := by rw [hv]
  have hBallTU : Metric.ball center T ⊆ U :=
    (Metric.ball_subset_closedBall).trans hTU
  have hBallSU : Metric.ball center S ⊆ U := by
    exact (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hT.le)).trans hTU
  have hshiftS (m : ℕ) : ∀ x ∈ Metric.ball center S, x + h m • v ∈ U := by
    intro x hx
    have hx' : x ∈ Metric.closedBall center S := Metric.ball_subset_closedBall hx
    have hball := first_order_closedBall_translate_into_ball center v
      (r := S) (R := T) (h := h m) hvle (hsmallbuf m) x hx'
    exact hBallTU hball
  have hshiftR (m : ℕ) :
      ∀ x ∈ Metric.closedBall center R, x + h m • v ∈ U := by
    intro x hx
    have hsmallRT : |h m| < T - R := by
      have hgap : T - S < T - R := by linarith
      exact (hsmallbuf m).trans hgap
    have hball := first_order_closedBall_translate_into_ball center v
      (r := R) (R := T) (h := h m) hvle hsmallRT x hx
    exact hBallTU hball
  have hshiftSclosure (m : ℕ) :
      ∀ x ∈ closure (Metric.ball center S), x + h m • v ∈ U := by
    intro x hx
    have hxS : x ∈ Metric.closedBall center S := hclosureS hx
    have hball := first_order_closedBall_translate_into_ball center v
      (r := S) (R := T) (h := h m) hvle (hsmallbuf m) x hxS
    exact hBallTU hball
  have hclosedRsub : Metric.closedBall center R ⊆ closure (Metric.ball center S) := by
    intro x hx
    apply subset_closure
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))
  let hq : ℕ → EuclideanSpace ℂ (Fin n) → ℝ := fun m x ↦
      (u (x + h m • v) - u x) / h m
  have hsmooth : ∀ m, ContDiffOn ℝ 2 (hq m) (Metric.ball center S) := by
    intro m
    simpa [hq] using first_differenceQuotient_contDiffOn_of_shift_to hu hBallSU (hshiftS m)
  have hbound : ∀ m, HolderBoundOn 2 α Cq (Metric.closedBall center R) (hq m) := by
    intro m
    have hquot := hqUniform v (h m) hv (by
      rw [abs_of_pos (hpos m)]
      exact hpos m) (hsmallq m) (hshiftSclosure m)
    exact hquot.mono_set hclosedRsub
  have hpathIcc (m : ℕ) (x : EuclideanSpace ℂ (Fin n))
      (hx : x ∈ Metric.closedBall center R) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      x + t • (h m • v) ∈ Metric.ball center T := by
    have htabs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htv : ‖t • v‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |t| * ‖v‖ ≤ 1 * 1 := mul_le_mul htabs (by rw [hv]) (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hsmallRT : |h m| < T - R := by
      have hgap : T - S < T - R := by linarith
      exact (hsmallbuf m).trans hgap
    have hball := first_order_closedBall_translate_into_ball center (t • v)
      (r := R) (R := T) (h := h m) htv hsmallRT x hx
    simpa [smul_smul, mul_comm] using hball
  have hu1 : ContDiffOn ℝ 1 u U := hu.of_le (by norm_num)
  have hfdcont : ContinuousOn (fderiv ℝ u) U :=
    hu1.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hdircontU : ContinuousOn (fun x ↦ (fderiv ℝ u x) v) U :=
    hfdcont.clm_apply continuousOn_const
  have hdircontT : ContinuousOn (fun x ↦ (fderiv ℝ u x) v) (Metric.closedBall center T) :=
    hdircontU.mono hTU
  have hUC : UniformContinuousOn (fun x ↦ (fderiv ℝ u x) v)
      (Metric.closedBall center T) :=
    (isCompact_closedBall center T).uniformContinuousOn_of_continuous hdircontT
  have hpathIoc (m : ℕ) (x : EuclideanSpace ℂ (Fin n))
      (hx : x ∈ Metric.closedBall center R) (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      x + t • (h m • v) ∈ Metric.closedBall center T :=
    Metric.ball_subset_closedBall (hpathIcc m x hx t ⟨ht.1.le, ht.2⟩)
  have hpathIcc' (m : ℕ) (x : EuclideanSpace ℂ (Fin n))
      (hx : x ∈ Metric.closedBall center R) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      x + t • (h m • v) ∈ Metric.ball center T := hpathIcc m x hx t ht
  have hInt : ∀ m x, x ∈ Metric.closedBall center R →
      IntervalIntegrable (fun t : ℝ ↦ (fderiv ℝ u (x + t • (h m • v))) v)
        MeasureTheory.volume 0 1 := by
    intro m x hx
    exact first_differenceQuotient_intervalIntegrable_centered (hu1.mono hBallTU)
      (hpathIcc' m x hx)
  have havg : ∀ m x, x ∈ Metric.closedBall center R →
      (h m)⁻¹ • (u (x + h m • v) - u x) =
        ∫ t in (0 : ℝ)..1, (fderiv ℝ u (x + t • (h m • v))) v := by
    intro m x hx
    exact first_differenceQuotient_eq_intervalIntegral (hu1.mono hBallTU)
      (hpathIcc' m x hx) (ne_of_gt (hpos m))
  have hlimit : TendstoUniformlyOn hq (fun x ↦ (fderiv ℝ u x) v)
      atTop (Metric.closedBall center R) := by
    have htend := first_differenceQuotient_tendstoUniformlyOn
      (K := Metric.closedBall center R) (B := Metric.closedBall center T)
      (f := u) (v := v) (h := h)
      (Metric.closedBall_subset_closedBall hRT.le)
      (fun m x hx t ht => hpathIoc m x hx t ht)
      hUC hstep hvle hInt havg
    simpa [hq, div_eq_mul_inv, smul_eq_mul, mul_comm] using htend
  exact ⟨Cq, first_order_directional_limit_contDiffOn_two hR hS hα₀
    (le_of_lt hα₁) hsmooth hbound hlimit⟩

private theorem first_order_holderBoundOn_succ_of_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α C : ℝ≥0} {V : Set E} {f : E → F}
    (hbase : HolderBoundOn k α C V f)
    (hderiv : HolderBoundOn k α C V (fderiv ℝ f)) :
    HolderBoundOn (k + 1) α C V f := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    by_cases hj0 : j = 0
    · subst j
      simpa [norm_iteratedFDeriv_zero] using hbase.1 0 (by omega) x hx
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hj' : j' ≤ k := by omega
      have hnorm := hderiv.1 j' hj' x hx
      simpa only [norm_iteratedFDeriv_fderiv] using hnorm
  · let curry := continuousMultilinearCurryRightEquiv' ℝ k E F
    have hCurry (x : E) (hx : x ∈ V) :
        iteratedFDeriv ℝ k (fderiv ℝ f) x = curry (iteratedFDeriv ℝ (k + 1) f x) := by
      rw [iteratedFDeriv_succ_eq_comp_right (f := f) (x := x) (n := k)]
      simp [curry, LinearIsometryEquiv.apply_symm_apply]
    intro x hx y hy
    have h := hderiv.2 x hx y hy
    rw [hCurry x hx, hCurry y hy] at h
    simpa [curry.dist_map] using h

private theorem first_order_holderBoundOn_of_pointwiseJetLimits
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α C : ℝ≥0} {K : Set E} {q : ℕ → E → F} {g : E → F}
    (hbound : ∀ m, HolderBoundOn k α C K (q m))
    (hjets : ∀ j ≤ k, ∀ x ∈ K,
      Tendsto (fun m ↦ iteratedFDeriv ℝ j (q m) x) atTop
        (𝓝 (iteratedFDeriv ℝ j g x))) :
    HolderBoundOn k α C K g := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hnorm : Tendsto (fun m ↦ ‖iteratedFDeriv ℝ j (q m) x‖) atTop
        (𝓝 ‖iteratedFDeriv ℝ j g x‖) := (hjets j hj x hx).norm
    exact le_of_tendsto hnorm (Eventually.of_forall fun m => (hbound m).1 j hj x hx)
  · intro x hx y hy
    have hdist : Tendsto (fun m ↦
        dist (iteratedFDeriv ℝ k (q m) x) (iteratedFDeriv ℝ k (q m) y)) atTop
        (𝓝 (dist (iteratedFDeriv ℝ k g x) (iteratedFDeriv ℝ k g y))) :=
      (hjets k le_rfl x hx).dist (hjets k le_rfl y hy)
    have hupper : ∀ m,
        dist (iteratedFDeriv ℝ k (q m) x) (iteratedFDeriv ℝ k (q m) y) ≤
          (C : ℝ) * dist x y ^ (α : ℝ) := by
      intro m
      exact (hbound m).2.dist_le hx hy
    have hlimit : dist (iteratedFDeriv ℝ k g x) (iteratedFDeriv ℝ k g y) ≤
        (C : ℝ) * dist x y ^ (α : ℝ) :=
      le_of_tendsto hdist (Eventually.of_forall hupper)
    calc
      edist (iteratedFDeriv ℝ k g x) (iteratedFDeriv ℝ k g y) =
          ENNReal.ofReal (dist (iteratedFDeriv ℝ k g x) (iteratedFDeriv ℝ k g y)) := edist_dist _ _
      _ ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal hlimit
      _ = (C : ℝ≥0∞) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
        rw [ENNReal.ofReal_coe_nnreal]

private theorem first_order_fderiv_gradient_eval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z : E} (hu : ContDiffAt ℝ 3 u z) (b c : E) :
    fderiv ℝ (fun x ↦ fderiv ℝ u x c) z b = fderiv ℝ (fderiv ℝ u) z b c := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) z := hD1.differentiableAt (by norm_num)
  rw [fderiv_clm_apply hdiff (differentiableAt_const c)]
  simp

private theorem first_order_secondDerivative_directional_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z : E} (hu : ContDiffAt ℝ 3 u z) (e b c : E) :
    fderiv ℝ (fderiv ℝ (fun x ↦ fderiv ℝ u x e)) z b c =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x c e) z b := by
  let du : E → ℝ := fun x ↦ fderiv ℝ u x e
  have hDu : ContDiffAt ℝ 2 du z := by
    dsimp [du]
    exact (hu.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hDdu : ContDiffAt ℝ 1 (fderiv ℝ du) z := hDu.fderiv_right (by norm_num)
  have hDiffDdu : DifferentiableAt ℝ (fderiv ℝ du) z := hDdu.differentiableAt (by norm_num)
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEq : (fun x ↦ fderiv ℝ du x c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ (fderiv ℝ u) x c e := by
    filter_upwards [hnear] with x hx
    exact first_order_fderiv_gradient_eval hx c e
  have hEval : fderiv ℝ (fun x ↦ fderiv ℝ du x c) z b =
      fderiv ℝ (fderiv ℝ du) z b c := by
    rw [fderiv_clm_apply hDiffDdu (differentiableAt_const c)]
    simp
  calc
    fderiv ℝ (fderiv ℝ du) z b c = fderiv ℝ (fun x ↦ fderiv ℝ du x c) z b := hEval.symm
    _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x c e) z b := by
      exact congrArg (fun L : E →L[ℝ] ℝ ↦ L b) (hEq.fderiv_eq (𝕜 := ℝ))

private theorem first_order_thirdDerivative_swap_hessian_slots {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z : E} (hu : ContDiffAt ℝ 3 u z) (a b c : E) :
    fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z a =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x c b) z a := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) z :=
    hD1.fderiv_right (by norm_num)
  have hbc : ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z := by
    have hb : ContDiffAt ℝ 1 (fun _ : E ↦ b) z := contDiffAt_const
    have hc : ContDiffAt ℝ 1 (fun _ : E ↦ c) z := contDiffAt_const
    exact (hD2.clm_apply hb).clm_apply hc
  have hcb : ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x c b) z := by
    have hb : ContDiffAt ℝ 1 (fun _ : E ↦ b) z := contDiffAt_const
    have hc : ContDiffAt ℝ 1 (fun _ : E ↦ c) z := contDiffAt_const
    exact (hD2.clm_apply hc).clm_apply hb
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEq : (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ (fderiv ℝ u) x c b := by
    filter_upwards [hnear] with x hx
    have hx2 : ContDiffAt ℝ 2 u x := hx.of_le (by norm_num)
    exact (hx2.isSymmSndFDerivAt (by norm_num)) b c
  have hderiv := hEq.fderiv_eq (𝕜 := ℝ)
  exact congrArg (fun L : E →L[ℝ] ℝ ↦ L a) hderiv

private theorem first_order_thirdDerivative_swap_outer_hessian_slot {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z : E} (hu : ContDiffAt ℝ 3 u z) (a b c : E) :
    fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z a =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x a c) z b := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  let g : E → ℝ := fun x ↦ fderiv ℝ u x c
  have hgc : ContDiffAt ℝ 2 g z := by
    dsimp [g]
    exact hD1.clm_apply contDiffAt_const
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEqB : (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ g x b := by
    filter_upwards [hnear] with x hx
    exact (first_order_fderiv_gradient_eval hx b c).symm
  have hEqA : (fun x ↦ fderiv ℝ (fderiv ℝ u) x a c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ g x a := by
    filter_upwards [hnear] with x hx
    exact (first_order_fderiv_gradient_eval hx a c).symm
  have hDg : ContDiffAt ℝ 1 (fderiv ℝ g) z := hgc.fderiv_right (by norm_num)
  have hDgDiff : DifferentiableAt ℝ (fderiv ℝ g) z := hDg.differentiableAt (by norm_num)
  have hEvalB : fderiv ℝ (fun x ↦ fderiv ℝ g x b) z a =
      fderiv ℝ (fderiv ℝ g) z a b := by
    rw [fderiv_clm_apply hDgDiff (differentiableAt_const b)]
    simp
  have hEvalA : fderiv ℝ (fun x ↦ fderiv ℝ g x a) z b =
      fderiv ℝ (fderiv ℝ g) z b a := by
    rw [fderiv_clm_apply hDgDiff (differentiableAt_const a)]
    simp
  have hsymm := hgc.isSymmSndFDerivAt (by norm_num)
  calc
    fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z a =
        fderiv ℝ (fun x ↦ fderiv ℝ g x b) z a := by
      exact congrArg (fun L : E →L[ℝ] ℝ ↦ L a) (hEqB.fderiv_eq (𝕜 := ℝ))
    _ = fderiv ℝ (fderiv ℝ g) z a b := hEvalB
    _ = fderiv ℝ (fderiv ℝ g) z b a := hsymm a b
    _ = fderiv ℝ (fun x ↦ fderiv ℝ g x a) z b := hEvalA.symm
    _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x a c) z b := by
      exact congrArg (fun L : E →L[ℝ] ℝ ↦ L b) (hEqA.fderiv_eq (𝕜 := ℝ)).symm

private theorem first_order_fderiv_secondJet_eq_directional_secondJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z v : E} (hu : ContDiffAt ℝ 3 u z) :
    fderiv ℝ (iteratedFDeriv ℝ 2 u) z v =
      iteratedFDeriv ℝ 2 (fun x ↦ fderiv ℝ u x v) z := by
  have hD2 : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 u) z := by
    have hc : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 u) z :=
      hu.iteratedFDeriv_right (m := 1) (i := 2) (by norm_num)
    exact hc.differentiableAt (by norm_num)
  ext m
  let a : E := m 0
  let b : E := m 1
  have hsym :
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x a b) z v =
        fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x v b) z a :=
    first_order_thirdDerivative_swap_outer_hessian_slot hu v a b
  have hsym2 :
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x v b) z a =
        fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b v) z a :=
    first_order_thirdDerivative_swap_hessian_slots hu a v b
  have hdir :
      fderiv ℝ (fderiv ℝ (fun x ↦ fderiv ℝ u x v)) z a b =
        fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b v) z a :=
    first_order_secondDerivative_directional_eq hu v a b
  have hjetEval : fderiv ℝ (fun x ↦ (iteratedFDeriv ℝ 2 u x) m) z v =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x a b) z v := by
    have hEq : (fun x ↦ (iteratedFDeriv ℝ 2 u x) m) =ᶠ[𝓝 z]
        fun x ↦ fderiv ℝ (fderiv ℝ u) x a b := by
      filter_upwards [hu.eventually (by norm_num)] with x hx
      simpa [a, b] using (iteratedFDeriv_two_apply u x m)
    exact congrArg (fun L : E →L[ℝ] ℝ ↦ L v) (hEq.fderiv_eq (𝕜 := ℝ))
  calc
    (fderiv ℝ (iteratedFDeriv ℝ 2 u) z v) m =
        fderiv ℝ (fun x ↦ (iteratedFDeriv ℝ 2 u x) m) z v := by
          rw [fderiv_continuousMultilinear_apply_const_apply hD2 m v]
    _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x a b) z v := hjetEval
    _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x v b) z a := hsym
    _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b v) z a := hsym2
    _ = fderiv ℝ (fderiv ℝ (fun x ↦ fderiv ℝ u x v)) z a b := hdir.symm
    _ = (iteratedFDeriv ℝ 2 (fun x ↦ fderiv ℝ u x v) z) m := by
          symm
          simpa [a, b] using
            (iteratedFDeriv_two_apply (fun x ↦ fderiv ℝ u x v) z m)

private theorem first_order_fderiv_firstJet_eq_directional_firstJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z v : E} (hu : ContDiffAt ℝ 3 u z) :
    fderiv ℝ (iteratedFDeriv ℝ 1 u) z v =
      iteratedFDeriv ℝ 1 (fun x ↦ fderiv ℝ u x v) z := by
  have hD1 : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 u) z := by
    have hc : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 1 u) z :=
      hu.iteratedFDeriv_right (m := 1) (i := 1) (by norm_num)
    exact hc.differentiableAt (by norm_num)
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hu2 : ContDiffAt ℝ 2 u z := hu.of_le (by norm_num)
  have hsymm := hu2.isSymmSndFDerivAt (by norm_num)
  ext m
  let a : E := m 0
  have hleft : (fderiv ℝ (iteratedFDeriv ℝ 1 u) z v) m =
      fderiv ℝ (fun x ↦ fderiv ℝ u x a) z v := by
    rw [(fderiv_continuousMultilinear_apply_const_apply hD1 m v).symm]
    have hEq : (fun x ↦ iteratedFDeriv ℝ 1 u x m) =ᶠ[𝓝 z]
        fun x ↦ fderiv ℝ u x a := by
      filter_upwards [hu.eventually (by norm_num)] with x hx
      simp [a, iteratedFDeriv_one_apply]
    exact congrArg (fun L : E →L[ℝ] ℝ ↦ L v) (hEq.fderiv_eq (𝕜 := ℝ))
  have hright : (iteratedFDeriv ℝ 1 (fun x ↦ fderiv ℝ u x v) z) m =
      fderiv ℝ (fderiv ℝ u) z a v := by
    rw [iteratedFDeriv_one_apply]
    rw [fderiv_clm_apply hDu (differentiableAt_const v)]
    simp [a]
  calc
    (fderiv ℝ (iteratedFDeriv ℝ 1 u) z v) m =
        fderiv ℝ (fun x ↦ fderiv ℝ u x a) z v := hleft
    _ = fderiv ℝ (fderiv ℝ u) z v a := by
      rw [fderiv_clm_apply hDu (differentiableAt_const a)]
      simp
    _ = fderiv ℝ (fderiv ℝ u) z a v := hsymm v a
    _ = (iteratedFDeriv ℝ 1 (fun x ↦ fderiv ℝ u x v) z) m := hright.symm

private theorem first_order_fderiv_valueJet_eq_directional_valueJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z v : E} :
    fderiv ℝ (iteratedFDeriv ℝ 0 u) z v =
      iteratedFDeriv ℝ 0 (fun x ↦ fderiv ℝ u x v) z := by
  rw [fderiv_iteratedFDeriv, Function.comp_apply]
  rw [iteratedFDeriv_zero_eq_comp]
  ext m
  simp [continuousMultilinearCurryLeftEquiv_apply, iteratedFDeriv_one_apply]

private theorem first_order_iteratedFDeriv_differenceQuotient_at
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {j : ℕ} {f : E → F} {v : E} {h : ℝ} {x : E}
    (hf₀ : ContDiffAt ℝ j f x) (hf₁ : ContDiffAt ℝ j f (x + h • v)) :
    iteratedFDeriv ℝ j (fun z ↦ h⁻¹ • (f (z + h • v) - f z)) x =
      h⁻¹ • (iteratedFDeriv ℝ j f (x + h • v) - iteratedFDeriv ℝ j f x) := by
  have hshift : ContDiffAt ℝ j (fun z ↦ f (z + h • v)) x := by
    exact hf₁.comp x (by fun_prop)
  have hdiff : iteratedFDeriv ℝ j (fun z ↦ f (z + h • v) - f z) x =
      iteratedFDeriv ℝ j (fun z ↦ f (z + h • v)) x - iteratedFDeriv ℝ j f x := by
    change iteratedFDeriv ℝ j ((fun z ↦ f (z + h • v)) - f) x = _
    exact iteratedFDeriv_sub_apply (i := j) hshift hf₀
  have hshiftI : iteratedFDeriv ℝ j (fun z ↦ f (z + h • v)) x =
      iteratedFDeriv ℝ j f (x + h • v) :=
    iteratedFDeriv_comp_add_right j (h • v) x
  have hqfun : (fun z ↦ h⁻¹ • (f (z + h • v) - f z)) =
      h⁻¹ • (fun z ↦ f (z + h • v) - f z) := rfl
  rw [hqfun, iteratedFDeriv_const_smul_apply (i := j) (a := h⁻¹)
    (hshift.sub hf₀), hdiff, hshiftI]

private theorem first_order_directional_iteratedJet_derivative_compat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {x v : E} (hu : ContDiffAt ℝ 3 u x)
    {j : ℕ} (hj : j ≤ 2) :
    fderiv ℝ (iteratedFDeriv ℝ j u) x v =
      iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ u y v) x := by
  interval_cases j
  · exact first_order_fderiv_valueJet_eq_directional_valueJet
  · exact first_order_fderiv_firstJet_eq_directional_firstJet hu
  · exact first_order_fderiv_secondJet_eq_directional_secondJet hu

private theorem first_order_directionalDifferenceQuotient_tendsto_of_contDiffAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x v : E} {h : ℕ → ℝ}
    (hf : ContDiffAt ℝ 1 f x)
    (hzero : Tendsto h atTop (𝓝 0)) (hnonzero : ∀ m, h m ≠ 0) :
    Tendsto (fun m ↦ (h m)⁻¹ • (f (x + h m • v) - f x)) atTop
      (𝓝 ((fderiv ℝ f x) v)) := by
  let γ : ℝ → E := fun t ↦ x + t • v
  have hγ : HasDerivAt γ v (0 : ℝ) := by
    simpa [γ] using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x
  have hcomp : HasDerivAt (f ∘ γ) ((fderiv ℝ f x) v) (0 : ℝ) := by
    have hfd : HasFDerivAt f (fderiv ℝ f x) x :=
      (hf.differentiableAt (by norm_num)).hasFDerivAt
    have hfd0 : HasFDerivAt f (fderiv ℝ f x) (γ 0) := by simpa [γ] using hfd
    exact hfd0.comp_hasDerivAt 0 hγ
  have hwithin : Tendsto h atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzero, Filter.Eventually.of_forall (fun m ↦ hnonzero m)⟩
  have hlimit := hcomp.tendsto_slope_zero.comp hwithin
  simpa [slope_def_module, γ, Function.comp_def] using hlimit

private theorem first_order_finiteDifference_jets_tendsto_pointwise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {u : E → ℝ} {x v : E} {h : ℕ → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 3 u U) (hx : x ∈ U)
    (hzero : Tendsto h atTop (𝓝 0)) (hnonzero : ∀ m, h m ≠ 0)
    (hshift : ∀ m, x + h m • v ∈ U) :
    ∀ j ≤ 2, Tendsto
      (fun m ↦ iteratedFDeriv ℝ j
        (fun y ↦ (h m)⁻¹ • (u (y + h m • v) - u y)) x)
      atTop (𝓝 (iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ u y v) x)) := by
  intro j hj
  have huAt : ContDiffAt ℝ 3 u x := (hu x hx).contDiffAt (hU.mem_nhds hx)
  have hJetCont : ContDiffAt ℝ 1 (fun y ↦ iteratedFDeriv ℝ j u y) x := by
    have hle : (1 : WithTop ℕ∞) + (j : WithTop ℕ∞) ≤ 3 := by
      exact_mod_cast (show 1 + j ≤ 3 by omega)
    exact huAt.iteratedFDeriv_right (m := 1) (i := j) hle
  have hlimit := first_order_directionalDifferenceQuotient_tendsto_of_contDiffAt
    (f := fun y ↦ iteratedFDeriv ℝ j u y) (x := x) (v := v) (h := h)
    hJetCont hzero hnonzero
  have hcompat := first_order_directional_iteratedJet_derivative_compat (x := x) (v := v) huAt hj
  have hjetEq (m : ℕ) :
      iteratedFDeriv ℝ j
        (fun y ↦ (h m)⁻¹ • (u (y + h m • v) - u y)) x =
        (h m)⁻¹ •
          (iteratedFDeriv ℝ j u (x + h m • v) - iteratedFDeriv ℝ j u x) := by
    apply first_order_iteratedFDeriv_differenceQuotient_at
    · exact (hu x hx).contDiffAt (hU.mem_nhds hx) |>.of_le (by exact_mod_cast (show j ≤ 3 by omega))
    · exact (hu (x + h m • v) (hshift m)).contDiffAt (hU.mem_nhds (hshift m)) |>.of_le
        (by exact_mod_cast (show j ≤ 3 by omega))
  have hlimit' : Tendsto
      (fun m ↦ (h m)⁻¹ •
        (iteratedFDeriv ℝ j u (x + h m • v) - iteratedFDeriv ℝ j u x))
      atTop (𝓝 ((fderiv ℝ (iteratedFDeriv ℝ j u) x) v)) := hlimit
  have hresult := hlimit'.congr' (Filter.Eventually.of_forall fun m ↦ (hjetEq m).symm)
  simpa [hcompat] using hresult

private theorem first_order_compact_open_translation_buffer
    {E : Type*} [MetricSpace E] {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ y, dist y x < δ → y ∈ U := by
  classical
  by_cases hne : K.Nonempty
  · let r : K → ℝ := fun x => Classical.choose (Metric.isOpen_iff.mp hU x (hKU x.property))
    have hr (x : K) : 0 < r x ∧ Metric.ball (x : E) (r x) ⊆ U :=
      Classical.choose_spec (Metric.isOpen_iff.mp hU x (hKU x.property))
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball x (r x / 2))
      (fun _ => Metric.isOpen_ball) (by
        intro z hz
        exact Set.mem_iUnion.2
          ⟨⟨z, hz⟩, Metric.mem_ball_self (div_pos (hr ⟨z, hz⟩).1 (by norm_num))⟩)
    have htne : t.Nonempty := by
      rcases hne with ⟨z, hz⟩
      have hz' := ht hz
      rcases Set.mem_iUnion₂.mp hz' with ⟨a, ha, _⟩
      exact ⟨a, ha⟩
    let δ : ℝ := t.inf' htne (fun x => r x / 3)
    have hδ : 0 < δ := by
      change 0 < t.inf' htne (fun x => r x / 3)
      rw [Finset.lt_inf'_iff]
      intro x hx
      exact div_pos (hr x).1 (by norm_num)
    refine ⟨δ, hδ, ?_⟩
    intro z hz y hy
    have hz' := ht hz
    rcases Set.mem_iUnion₂.mp hz' with ⟨a, ha, hza⟩
    have hδa : δ ≤ r a / 3 := Finset.inf'_le (f := fun x => r x / 3) ha
    have hza' : dist z (a : E) < r a / 2 := by
      simpa [dist_comm] using Metric.mem_ball.mp hza
    apply hr a |>.2
    rw [Metric.mem_ball]
    calc
      dist y (a : E) ≤ dist y z + dist z (a : E) := dist_triangle _ _ _
      _ < δ + r a / 2 := add_lt_add_of_lt_of_le hy hza'.le
      _ ≤ r a / 3 + r a / 2 := add_le_add hδa le_rfl
      _ < r a := by linarith [(hr a).1]
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, hx⟩)

private theorem first_order_contDiffOn_clm_apply_reconstruct
    {𝕜 D E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup D] [NormedSpace 𝕜 D]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {m : WithTop ℕ∞} {f : D → E →L[𝕜] F} {s : Set D}
    (h : ∀ y, ContDiffOn 𝕜 m (fun x => f x y) s) : ContDiffOn 𝕜 m f s := by
  let d := Module.finrank 𝕜 E
  have hd : d = Module.finrank 𝕜 (Fin d → 𝕜) := (Module.finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i => h _)

private theorem first_order_contDiffOn_three_of_unit_directional_derivatives
    {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hdir : ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖ ≤ 1 →
      ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ u x v) U) :
    ContDiffOn ℝ 3 u U := by
  have hall (v : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ u x v) U := by
    by_cases hv : ‖v‖ ≤ 1
    · exact hdir v hv
    · let w : EuclideanSpace ℂ (Fin n) := ‖v‖⁻¹ • v
      have hvpos : 0 < ‖v‖ := by have := norm_nonneg v; linarith
      have hw : ‖w‖ = 1 := by
        dsimp [w]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
        exact inv_mul_cancel₀ (ne_of_gt hvpos)
      have hvw : v = ‖v‖ • w := by
        dsimp [w]
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
      have heq : (fun x ↦ fderiv ℝ u x v) =
          (‖v‖ : ℝ) • (fun x ↦ fderiv ℝ u x w) := by
        funext x
        calc
          (fderiv ℝ u x) v = (fderiv ℝ u x) (‖v‖ • w) :=
            congrArg (fderiv ℝ u x) hvw
          _ = ‖v‖ * (fderiv ℝ u x) w := by
            rw [(fderiv ℝ u x).map_smul]
            simp [smul_eq_mul]
      rw [heq]
      exact (hdir w hw.le).const_smul (‖v‖ : ℝ)
  have hD : ContDiffOn ℝ 2 (fderiv ℝ u) U :=
    first_order_contDiffOn_clm_apply_reconstruct hall
  have hDiff : DifferentiableOn ℝ u U := by
    intro x hx
    have hAt := (hu x hx).contDiffAt (hU.mem_nhds hx)
    exact (hAt.differentiableAt (by norm_num)).differentiableWithinAt
  change ContDiffOn ℝ ((2 : ℕ) + 1) u U
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
  exact ⟨hDiff, by simp, hD⟩

private theorem first_order_clm_norm_le_of_all_unit_vectors
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hunit : ∀ v : E, ‖v‖ = 1 → ‖L v‖ ≤ C) : ‖L‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound L hC
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : E := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      dsimp [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
      field_simp
    have hrecover : (‖v‖ : ℝ) • w = v := by
      dsimp [w]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
    have hscale : L v = ‖v‖ • L w := by
      calc
        L v = L (‖v‖ • w) := congrArg L hrecover.symm
        _ = ‖v‖ • L w := map_smul L _ _
    calc
      ‖L v‖ = ‖‖v‖ • L w‖ := by rw [hscale]
      _ = ‖v‖ * ‖L w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
      _ ≤ ‖v‖ * C := mul_le_mul_of_nonneg_left (hunit w hw) (norm_nonneg _)
      _ = C * ‖v‖ := by ring

private theorem first_order_iteratedFDeriv_clm_apply_at
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {j : ℕ} {f : E → E →L[ℝ] F} {x v}
    (hf : ContDiffAt ℝ j f x) :
    iteratedFDeriv ℝ j (fun y ↦ f y v) x =
      (ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap
        (iteratedFDeriv ℝ j f x) := by
  change iteratedFDeriv ℝ j
    ((ContinuousLinearMap.apply ℝ F v) ∘ f) x = _
  exact (ContinuousLinearMap.apply ℝ F v).iteratedFDeriv_comp_left hf (by exact_mod_cast le_rfl)

private theorem first_order_holderBoundOn_clm_of_all_unit_directions
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α C : ℝ≥0} {K U : Set E} {f : E → E →L[ℝ] F}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ k f U)
    (hdir : ∀ v : E, ‖v‖ = 1 → HolderBoundOn k α C K (fun x ↦ f x v)) :
    HolderBoundOn k α C K f := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hjcont : ContDiffAt ℝ j f x :=
      (hf x (hKU hx)).contDiffAt (hU.mem_nhds (hKU hx)) |>.of_le (by exact_mod_cast hj)
    let D := iteratedFDeriv ℝ j f x
    apply ContinuousMultilinearMap.opNorm_le_bound (by exact_mod_cast C.2)
    intro w
    have hprod : 0 ≤ (C : ℝ) * ∏ i, ‖w i‖ := by positivity
    apply first_order_clm_norm_le_of_all_unit_vectors (D w) hprod
    intro v hv
    have hjet := first_order_iteratedFDeriv_clm_apply_at
      (j := j) (f := f) (x := x) (v := v) hjcont
    have hval := congrArg (fun T => T w) hjet
    have hpoint := (hdir v hv).1 j hj x hx
    have heq : (iteratedFDeriv ℝ j (fun y ↦ f y v) x) w = (D w) v := by
      simpa [D] using hval
    rw [← heq]
    calc
      ‖(iteratedFDeriv ℝ j (fun y ↦ f y v) x) w‖ ≤
          ‖iteratedFDeriv ℝ j (fun y ↦ f y v) x‖ * ∏ i, ‖w i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ (C : ℝ) * ∏ i, ‖w i‖ := mul_le_mul_of_nonneg_right hpoint (by positivity)
  · intro x hx y hy
    have hxU : x ∈ U := hKU hx
    have hyU : y ∈ U := hKU hy
    have hxdiff : ContDiffAt ℝ k f x :=
      (hf x hxU).contDiffAt (hU.mem_nhds hxU)
    have hydiff : ContDiffAt ℝ k f y :=
      (hf y hyU).contDiffAt (hU.mem_nhds hyU)
    let Dx := iteratedFDeriv ℝ k f x
    let Dy := iteratedFDeriv ℝ k f y
    let d : ℝ := (C : ℝ) * dist x y ^ (α : ℝ)
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hDdiff (w : Fin k → E) : ‖(Dx - Dy) w‖ ≤ d * ∏ i, ‖w i‖ := by
      apply first_order_clm_norm_le_of_all_unit_vectors ((Dx - Dy) w)
        (mul_nonneg hd (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      intro v hv
      have hxjet := first_order_iteratedFDeriv_clm_apply_at
        (j := k) (f := f) (x := x) (v := v) hxdiff
      have hyjet := first_order_iteratedFDeriv_clm_apply_at
        (j := k) (f := f) (x := y) (v := v) hydiff
      have hvalx (m : Fin k → E) :
          (iteratedFDeriv ℝ k (fun z ↦ f z v) x) m = (Dx m) v := by
        have h := congrArg (fun T => T m) hxjet
        simpa [Dx] using h
      have hvaly (m : Fin k → E) :
          (iteratedFDeriv ℝ k (fun z ↦ f z v) y) m = (Dy m) v := by
        have h := congrArg (fun T => T m) hyjet
        simpa [Dy] using h
      have hdist : ‖iteratedFDeriv ℝ k (fun z ↦ f z v) x -
          iteratedFDeriv ℝ k (fun z ↦ f z v) y‖ ≤ d := by
        have h := (hdir v hv).2.dist_le hx hy
        simpa [d, dist_eq_norm] using h
      have heval : ((Dx - Dy) w) v =
          (iteratedFDeriv ℝ k (fun z ↦ f z v) x -
            iteratedFDeriv ℝ k (fun z ↦ f z v) y) w := by
        calc
          ((Dx - Dy) w) v = (Dx w) v - (Dy w) v := by simp
          _ = (iteratedFDeriv ℝ k (fun z ↦ f z v) x) w -
              (iteratedFDeriv ℝ k (fun z ↦ f z v) y) w := by rw [hvalx w, hvaly w]
          _ = _ := by simp
      calc
        ‖((Dx - Dy) w) v‖ =
            ‖(iteratedFDeriv ℝ k (fun z ↦ f z v) x -
              iteratedFDeriv ℝ k (fun z ↦ f z v) y) w‖ := by rw [heval]
        _ ≤ ‖iteratedFDeriv ℝ k (fun z ↦ f z v) x -
              iteratedFDeriv ℝ k (fun z ↦ f z v) y‖ * ∏ i, ‖w i‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ d * ∏ i, ‖w i‖ := mul_le_mul_of_nonneg_right hdist (by positivity)
    have hDnorm : ‖Dx - Dy‖ ≤ d := by
      apply ContinuousMultilinearMap.opNorm_le_bound hd
      intro w
      exact hDdiff w
    have hdistJet : dist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) =
        ‖Dx - Dy‖ := by rw [dist_eq_norm]
    calc
      edist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) =
          ENNReal.ofReal (dist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y)) := edist_dist _ _
      _ = ENNReal.ofReal ‖Dx - Dy‖ := by rw [hdistJet]
      _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal hDnorm
      _ = (C : ℝ≥0∞) * edist x y ^ (α : ℝ) := by
        dsimp [d]
        rw [ENNReal.ofReal_mul (by positivity)]
        rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
        rw [ENNReal.ofReal_coe_nnreal]

private theorem first_order_difference_quotient_stability {n : ℕ}
    {α C : ℝ≥0} {U V : Set (EuclideanSpace ℂ (Fin n))}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hV : IsCompact (closure V)) (hVU : closure V ⊆ U)
    (hu : ContDiffOn ℝ 2 u U)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hlocal : ∀ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W →
      IsCompact (closure W) → closure W ⊆ U →
      ∃ C' : ℝ≥0, (∃ δ : ℝ, 0 < δ ∧
        ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 → 0 < |h| → |h| < δ →
          (∀ z ∈ closure W, z + h • v ∈ U) →
          HolderBoundOn 2 α C' (closure W) (fun z ↦ (u (z + h • v) - u z) / h)))
    (hbase : HolderBoundOn 2 α C (closure V) u)
    (hquot : (∃ δ : ℝ, 0 < δ ∧
        ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 → 0 < |h| → |h| < δ →
          (∀ z ∈ closure V, z + h • v ∈ U) →
          HolderBoundOn 2 α C (closure V) (fun z ↦ (u (z + h • v) - u z) / h))) :
    ContDiffOn ℝ 3 u U ∧ HolderBoundOn 3 α C V u := by
  have hdirUnit (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ = 1) :
      ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ u x v) U := by
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    by_cases hn : n = 0
    · subst n
      have hvzero : v = 0 := Subsingleton.elim _ _
      simp [hvzero] at hv
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
      let rr : ℝ := ε / 16
      let R : ℝ := ε / 8
      let S : ℝ := ε / 4
      let T : ℝ := ε / 2
      have hrr : 0 < rr := by dsimp [rr]; positivity
      have hR : 0 < R := by dsimp [R]; positivity
      have hS : 0 < S := by dsimp [S]; positivity
      have hT : 0 < T := by dsimp [T]; positivity
      have hrrR : rr < R := by dsimp [rr, R]; linarith
      have hRS : R < S := by dsimp [R, S]; linarith
      have hST : S < T := by dsimp [S, T]; linarith
      have hTε : T < ε := by dsimp [T]; linarith
      have hTU : Metric.closedBall x T ⊆ U :=
        (Metric.closedBall_subset_ball hTε).trans hball
      have hclosureW :
          closure (Metric.ball x S) ⊆ Metric.closedBall x S :=
        Metric.closure_ball_subset_closedBall
      have hcompactW : IsCompact (closure (Metric.ball x S)) :=
        (isCompact_closedBall x S).of_isClosed_subset isClosed_closure hclosureW
      have hclosureWU : closure (Metric.ball x S) ⊆ U := by
        exact hclosureW.trans
          ((Metric.closedBall_subset_closedBall hST.le).trans hTU)
      obtain ⟨_, hregular, _⟩ := first_order_directional_derivative_contDiffOn_local
        hU hu hlocal hα₀ hα₁ x hrr hrrR hRS hST hTU v hv
      let W : Set (EuclideanSpace ℂ (Fin n)) := U ∩ Metric.ball x rr
      refine ⟨W, hU.inter Metric.isOpen_ball, ⟨hx, Metric.mem_ball_self hrr⟩, ?_⟩
      exact hregular.mono fun y hy => hy.2.2
  have hdir (v : EuclideanSpace ℂ (Fin n)) (_hv : ‖v‖ ≤ 1) :
      ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ u x v) U := by
    by_cases hv0 : v = 0
    · simpa [hv0] using
        (contDiffOn_const : ContDiffOn ℝ 2
          (fun _ : EuclideanSpace ℂ (Fin n) => (0 : ℝ)) U)
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      let w : EuclideanSpace ℂ (Fin n) := ‖v‖⁻¹ • v
      have hw : ‖w‖ = 1 := by
        dsimp [w]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
        exact inv_mul_cancel₀ (ne_of_gt hvpos)
      have hvw : v = ‖v‖ • w := by
        dsimp [w]
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
      have heq : (fun x ↦ fderiv ℝ u x v) =
          (‖v‖ : ℝ) • (fun x ↦ fderiv ℝ u x w) := by
        funext x
        calc
          (fderiv ℝ u x) v = (fderiv ℝ u x) (‖v‖ • w) :=
            congrArg (fderiv ℝ u x) hvw
          _ = ‖v‖ * (fderiv ℝ u x) w := by
            rw [(fderiv ℝ u x).map_smul]
            simp [smul_eq_mul]
      rw [heq]
      exact (hdirUnit w hw).const_smul (‖v‖ : ℝ)
  have hregular : ContDiffOn ℝ 3 u U :=
    first_order_contDiffOn_three_of_unit_directional_derivatives hU hu hdir
  have hbuffer := first_order_compact_open_translation_buffer hV hU hVU
  have hdirBound : ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 →
      HolderBoundOn 2 α C (closure V) (fun x ↦ fderiv ℝ u x v) := by
    intro v hv
    obtain ⟨δ, hδ, hquot⟩ := hquot
    obtain ⟨ρ, hρ, hbuffer⟩ := hbuffer
    let η : ℝ := min δ ρ / 2
    have hη : 0 < η := by dsimp [η]; positivity
    have hηδ : η < δ := by
      have hmin := min_le_left δ ρ
      dsimp [η]
      linarith
    have hηρ : η < ρ := by
      have hmin := min_le_right δ ρ
      dsimp [η]
      linarith
    let h : ℕ → ℝ := fun m ↦ η * (((m : ℝ) + 1)⁻¹)
    have hden : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hzero : Tendsto h atTop (𝓝 0) := by
      dsimp [h]
      simpa using (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden) :
        Tendsto (fun m : ℕ ↦ η * (((m : ℝ) + 1)⁻¹)) atTop (𝓝 (η * 0)))
    have hpos (m : ℕ) : 0 < h m := by dsimp [h]; positivity
    have hle (m : ℕ) : h m ≤ η := by
      dsimp [h]
      have hdenpos : 0 < (m : ℝ) + 1 := by positivity
      have hdenone : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      calc
        η * (((m : ℝ) + 1)⁻¹) ≤ η * 1 :=
          mul_le_mul_of_nonneg_left (inv_le_one₀ hdenpos |>.2 hdenone) (le_of_lt hη)
        _ = η := by ring
    have hstep (m : ℕ) : |h m| < δ := by
      rw [abs_of_pos (hpos m)]
      exact (hle m).trans_lt hηδ
    have hshift (m : ℕ) (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ closure V) :
        x + h m • v ∈ U := by
      apply hbuffer x hx
      have hdist : dist (x + h m • v) x = h m := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (hpos m), hv]
        ring
      rw [hdist]
      exact (hle m).trans_lt hηρ
    let q : ℕ → EuclideanSpace ℂ (Fin n) → ℝ := fun m x ↦
      (h m)⁻¹ • (u (x + h m • v) - u x)
    have hbound (m : ℕ) : HolderBoundOn 2 α C (closure V) (q m) := by
      have hquotm := hquot v (h m) hv (by simpa [abs_of_pos (hpos m)] using hpos m)
        (hstep m) (hshift m)
      simpa [q, div_eq_mul_inv, smul_eq_mul, mul_comm] using hquotm
    have hjets : ∀ j ≤ 2, ∀ x ∈ closure V,
        Tendsto (fun m ↦ iteratedFDeriv ℝ j (q m) x) atTop
          (𝓝 (iteratedFDeriv ℝ j (fun x ↦ fderiv ℝ u x v) x)) := by
      intro j hj x hx
      exact first_order_finiteDifference_jets_tendsto_pointwise hU hregular (hVU hx)
        hzero (fun m ↦ ne_of_gt (hpos m)) (fun m ↦ hshift m x hx) j hj
    exact first_order_holderBoundOn_of_pointwiseJetLimits hbound hjets
  have hF : ContDiffOn ℝ 2 (fderiv ℝ u) U := by
    apply hregular.fderiv_of_isOpen hU
    exact_mod_cast (show (2 : ℕ) + 1 ≤ 3 by norm_num)
  have hderiv : HolderBoundOn 2 α C (closure V) (fderiv ℝ u) :=
    first_order_holderBoundOn_clm_of_all_unit_directions hU hVU hF hdirBound
  have hholder : HolderBoundOn 3 α C (closure V) u :=
    first_order_holderBoundOn_succ_of_fderiv hbase hderiv
  refine ⟨hregular, ?_⟩
  exact hholder.mono_set subset_closure

private theorem first_order_difference_quotient_estimates {n : ℕ}
    (hOrder : InteriorSchauderOrder n 0) :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
      ∀ (lam K : ℝ≥0), 0 < lam →
        ∀ U V : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → IsCompact (closure V) →
          closure V ⊆ U →
          ∃ C : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
            (u : EuclideanSpace ℂ (Fin n) → ℝ),
            (∀ j l, ContDiffOn ℝ 1 (fun z ↦ A z j l) U) → ContDiffOn ℝ 2 u U →
            IsUniformlyEllipticOn A lam U →
            (∀ j l, HolderBoundOn 1 α K U fun z ↦ A z j l) →
            ∀ K₀ K₁ : ℝ≥0, ContDiffOn ℝ 1 (complexEllipticOp A u) U →
              HolderBoundOn 1 α K₁ U (complexEllipticOp A u) →
              (∀ z ∈ U, |u z| ≤ K₀) →
              HolderBoundOn 2 α (C * (K₁ + K₀)) (closure V) u ∧
                (∃ δ : ℝ, 0 < δ ∧
                  ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 →
                    0 < |h| → |h| < δ →
                    (∀ z ∈ closure V, z + h • v ∈ U) →
                    HolderBoundOn 2 α (C * (K₁ + K₀)) (closure V)
                      (fun z ↦ (u (z + h • v) - u z) / h)) ∧
                (∀ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W →
                  IsCompact (closure W) → closure W ⊆ U →
                  ∃ C' : ℝ≥0,
                    (∃ δ : ℝ, 0 < δ ∧
        ∀ (v : EuclideanSpace ℂ (Fin n)) (h : ℝ), ‖v‖ = 1 → 0 < |h| → |h| < δ →
          (∀ z ∈ closure W, z + h • v ∈ U) →
          HolderBoundOn 2 α C' (closure W) (fun z ↦ (u (z + h • v) - u z) / h))) := by
  intro α hα₀ hα₁ lam K hlam U V hU hV hVU
  simpa only [complexEllipticOp.eq_1] using
    CalabiYau.Schauder.firstOrderRegularity_differenceQuotientEstimates hOrder α hα₀ hα₁
      lam K hlam U V hU hV hVU

/--
The difference-quotient and stability bridge from the exact order-zero slice to order one. The
original solution is only C²; every application of the order-zero estimate is to a C² finite
quotient, never to a first derivative of `u`.
-/
private theorem first_order_difference_quotient_bridge (n : ℕ)
    (hOrder : InteriorSchauderOrder n 0) : InteriorSchauderOrder n 1 := by
  intro α hα₀ hα₁ lam K hlam U V hU hV hVU
  obtain ⟨C, hC⟩ := first_order_difference_quotient_estimates hOrder α hα₀ hα₁
    lam K hlam U V hU hV hVU
  refine ⟨C, ?_⟩
  intro A u hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
  obtain ⟨hbase, hquot, hlocal⟩ :=
    hC A u hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
  exact first_order_difference_quotient_stability hU hV hVU hu hα₀ hα₁ hlocal hbase hquot

/-- The first successor step of the interior Schauder estimate, including dimension zero. -/
theorem first_order_regularity (n : ℕ)
    (hOrder : InteriorSchauderOrder n 0) : InteriorSchauderOrder n 1 := by
  exact first_order_difference_quotient_bridge n hOrder

end
