module

public import CalabiYau.Geometry.Complex.Holder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite-difference Hölder bounds

The first difference quotient of a C¹ function inherits its first-derivative Hölder bound on a
smaller ball, provided the direction and step keep all translated line segments inside the outer
ball. This is the finite-difference estimate used in the first-order Schauder regularity argument.
-/

@[expose] public section

open Set
open scoped NNReal ENNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem differenceQuotient_norm_le
    {r R : ℝ} {α K : ℝ≥0} {f : E → F}
    (hR : r < R)
    (hf : ContDiffOn ℝ 1 f (Metric.ball (0 : E) R))
    (hbound : HolderBoundOn 1 α K (Metric.closedBall (0 : E) R) f)
    {v : E} {h : ℝ} (hv : ‖v‖ ≤ 1) (hh₀ : 0 < |h|) (hhR : |h| < R - r)
    {x : E} (hx : x ∈ Metric.closedBall (0 : E) r) :
    ‖h⁻¹ • (f (x + h • v) - f x)‖ ≤ (K : ℝ) := by
  have hxnorm : ‖x‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hstep : ‖h • v‖ ≤ |h| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg h) hv
  have hy : x + h • v ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball]
    calc
      dist (x + h • v) 0 ≤ dist (x + h • v) x + dist x 0 := dist_triangle _ _ _
      _ = ‖h • v‖ + ‖x‖ := by simp [dist_eq_norm, add_sub_cancel_left, add_comm]
      _ ≤ |h| + r := add_le_add hstep hxnorm
      _ < R := by linarith
  have hxball : x ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball]
    calc
      dist x 0 = ‖x‖ := by simp [dist_eq_norm]
      _ ≤ r := hxnorm
      _ < R := hR
  have hderiv (z : E) (hz : z ∈ Metric.ball (0 : E) R) :
      DifferentiableAt ℝ f z :=
    (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num)
  have hderivBound (z : E) (hz : z ∈ Metric.ball (0 : E) R) :
      ‖fderiv ℝ f z‖ ≤ (K : ℝ) := by
    have hz' : z ∈ Metric.closedBall (0 : E) R := by
      rw [Metric.mem_closedBall]
      exact (Metric.mem_ball.mp hz).le
    have hb := hbound.1 1 le_rfl z hz'
    rwa [norm_iteratedFDeriv_one] at hb
  have hLip : LipschitzOnWith K f (Metric.ball (0 : E) R) := by
    have hconvex : Convex ℝ (Metric.ball (0 : E) R) := _root_.convex_ball (0 : E) R
    exact hconvex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) hderiv
      (fun z hz => by exact_mod_cast hderivBound z hz)
  have hdiff : dist (f (x + h • v)) (f x) ≤ (K : ℝ) * dist (x + h • v) x :=
    (lipschitzOnWith_iff_dist_le_mul.mp hLip) (x + h • v) hy x hxball
  have hdist : dist (x + h • v) x = |h| * ‖v‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hquot : ‖f (x + h • v) - f x‖ ≤ (K : ℝ) * (|h| * ‖v‖) := by
    rw [← dist_eq_norm]
    simpa [hdist] using hdiff
  rw [norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    |h|⁻¹ * ‖f (x + h • v) - f x‖ ≤ |h|⁻¹ * ((K : ℝ) * (|h| * ‖v‖)) :=
      mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = (K : ℝ) * ‖v‖ := by
      have hh : |h| ≠ 0 := ne_of_gt hh₀
      field_simp
    _ ≤ (K : ℝ) := by
      exact mul_le_of_le_one_right (by exact_mod_cast K.2) hv

omit [CompleteSpace F] in
/-- A first difference quotient has the same Hölder bound as the derivative on a nested ball.
The quotient is the average of the directional derivative along the translated segment; comparing
these averages at two points preserves the derivative Hölder constant. -/
private theorem directionalDerivative_intervalIntegrable
    {R : ℝ} {f : E → F} (hf : ContDiffOn ℝ 1 f (Metric.ball (0 : E) R))
    {v : E} {h : ℝ} {x : E}
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (h • v) ∈ Metric.ball (0 : E) R) :
    IntervalIntegrable
      (fun t : ℝ => (fderiv ℝ f (x + t • (h • v))) v) MeasureTheory.volume 0 1 := by
  let γ : ℝ → E := fun t => x + t • (h • v)
  have hfdcont : ContinuousOn (fderiv ℝ f) (Metric.ball (0 : E) R) :=
    hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have hγcont : Continuous γ := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hγmaps : Set.MapsTo γ (Set.uIcc (0 : ℝ) 1) (Metric.ball (0 : E) R) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hb := hpath t ht'
    simpa [γ] using hb
  have hfdγ : ContinuousOn (fun t : ℝ => fderiv ℝ f (γ t)) (Set.uIcc 0 1) :=
    hfdcont.comp hγcont.continuousOn hγmaps
  have hval : ContinuousOn (fun t : ℝ => (fderiv ℝ f (γ t)) v) (Set.uIcc 0 1) :=
    hfdγ.clm_apply continuousOn_const
  have hcont : ContinuousOn (fun t : ℝ => (fderiv ℝ f (γ t)) v) (Set.uIcc 0 1) := by
    simpa [γ] using hval
  exact hcont.intervalIntegrable

private theorem differenceQuotient_eq_intervalIntegral
    {R : ℝ} {f : E → F} (hf : ContDiffOn ℝ 1 f (Metric.ball (0 : E) R))
    {v : E} {h : ℝ} {x : E}
    (hpath : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • (h • v) ∈ Metric.ball (0 : E) R)
    (hh : h ≠ 0) :
    h⁻¹ • (f (x + h • v) - f x) =
      ∫ t in (0 : ℝ)..1, (fderiv ℝ f (x + t • (h • v))) v := by
  let γ : ℝ → E := fun t => x + t • (h • v)
  have hγ : ∀ t, HasDerivAt γ (h • v) t := by
    intro t
    simpa [γ] using (hasDerivAt_id t).smul_const (h • v) |>.const_add x
  have hcomp : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (f ∘ γ)
      ((fderiv ℝ f (γ t)) (h • v)) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have hγball : γ t ∈ Metric.ball (0 : E) R := by
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
  have hHint' : IntervalIntegrable (fun t : ℝ => h • ((fderiv ℝ f (γ t)) v))
      MeasureTheory.volume 0 1 := by
    have hfdcont : ContinuousOn (fderiv ℝ f) (Metric.ball (0 : E) R) :=
      hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
    have hγcont : Continuous γ := by
      exact continuous_const.add (continuous_id.smul continuous_const)
    have hγmaps : Set.MapsTo γ (Set.uIcc (0 : ℝ) 1) (Metric.ball (0 : E) R) := by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
      have hb := hpath t ht'
      simpa [γ] using hb
    have hfdγ : ContinuousOn (fun t : ℝ => fderiv ℝ f (γ t)) (Set.uIcc 0 1) :=
      hfdcont.comp hγcont.continuousOn hγmaps
    have hval : ContinuousOn (fun t : ℝ => (fderiv ℝ f (γ t)) v) (Set.uIcc 0 1) :=
      hfdγ.clm_apply continuousOn_const
    have hcont : ContinuousOn (fun t : ℝ => h • ((fderiv ℝ f (γ t)) v)) (Set.uIcc 0 1) :=
      continuousOn_const.smul hval
    exact hcont.intervalIntegrable
  have hftc : ∫ t in (0 : ℝ)..1, h • ((fderiv ℝ f (γ t)) v) =
      (f ∘ γ) 1 - (f ∘ γ) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hHint'
  have hconst : ∫ t in (0 : ℝ)..1, h • ((fderiv ℝ f (γ t)) v) =
      h • ∫ t in (0 : ℝ)..1, (fderiv ℝ f (γ t)) v := by
    exact intervalIntegral.integral_smul h (fun t : ℝ => (fderiv ℝ f (γ t)) v)
  have heq : h • ∫ t in (0 : ℝ)..1, (fderiv ℝ f (γ t)) v =
      f (x + h • v) - f x := by
    rw [← hconst, hftc]
    simp [γ]
  rw [← heq]
  simp [γ, smul_smul, inv_mul_cancel₀ hh]

omit [CompleteSpace F] in
private theorem fderiv_holderOn
    {R : ℝ} {α K : ℝ≥0} {f : E → F}
    (hbound : HolderBoundOn 1 α K (Metric.closedBall (0 : E) R) f)
    {z w : E} (hz : z ∈ Metric.closedBall (0 : E) R)
    (hw : w ∈ Metric.closedBall (0 : E) R) :
    ‖iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f w‖ ≤
      (K : ℝ) * dist z w ^ (α : ℝ) := by
  have h := hbound.2 z hz w hw
  rw [edist_dist, dist_eq_norm] at h
  have hα : 0 ≤ (α : ℝ) := by exact_mod_cast α.2
  have hrpow := ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist z w) hα
  have hcoe : (K : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) := by simp
  have hReal : ENNReal.ofReal ‖iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f w‖ ≤
      ENNReal.ofReal ((K : ℝ) * dist z w ^ (α : ℝ)) := by
    calc
      ENNReal.ofReal ‖iteratedFDeriv ℝ 1 f z - iteratedFDeriv ℝ 1 f w‖ ≤
          (K : ℝ≥0∞) * edist z w ^ (α : ℝ) := h
      _ = ENNReal.ofReal ((K : ℝ) * dist z w ^ (α : ℝ)) := by
        rw [hcoe, edist_dist, hrpow, ← ENNReal.ofReal_mul (show 0 ≤ (K : ℝ) by positivity)]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hReal

theorem holderBoundOn_differenceQuotient
    {r R : ℝ} {α K : ℝ≥0} {f : E → F}
    (hr : 0 < r) (hR : r < R) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : ContDiffOn ℝ 1 f (Metric.ball (0 : E) R))
    (hbound : HolderBoundOn 1 α K (Metric.closedBall (0 : E) R) f)
    {v : E} {h : ℝ} (hv : ‖v‖ ≤ 1) (hh₀ : 0 < |h|) (hhR : |h| < R - r) :
    HolderBoundOn 0 α K (Metric.closedBall (0 : E) r)
      (fun x ↦ h⁻¹ • (f (x + h • v) - f x)) := by
  let q : E → F := fun z => h⁻¹ • (f (z + h • v) - f z)
  have _ : 0 < r ∧ 0 < α ∧ α < 1 := ⟨hr, hα₀, hα₁⟩
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero]
    exact differenceQuotient_norm_le hR hf hbound hv hh₀ hhR hx
  · have hqHolder : HolderOnWith K α q (Metric.closedBall (0 : E) r) := by
      intro x hx y hy
      have hxnorm : ‖x‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have hynorm : ‖y‖ ≤ r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hy
      have hpath (a : E) (ha : ‖a‖ ≤ r) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
          a + t • (h • v) ∈ Metric.ball (0 : E) R := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        have htabs : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hstep : ‖t • (h • v)‖ ≤ |h| := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          calc
            |t| * (|h| * ‖v‖) ≤ 1 * (|h| * 1) := by gcongr
            _ = |h| := by ring
        calc
          ‖a + t • (h • v)‖ ≤ ‖a‖ + ‖t • (h • v)‖ := norm_add_le _ _
          _ ≤ r + |h| := add_le_add ha hstep
          _ < R := by linarith
      have hpathX : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          x + t • (h • v) ∈ Metric.ball (0 : E) R := hpath x hxnorm
      have hpathY : ∀ t ∈ Set.Icc (0 : ℝ) 1,
          y + t • (h • v) ∈ Metric.ball (0 : E) R := hpath y hynorm
      have hIntX := directionalDerivative_intervalIntegrable hf hpathX
      have hIntY := directionalDerivative_intervalIntegrable hf hpathY
      have hqX := differenceQuotient_eq_intervalIntegral hf hpathX (abs_pos.mp hh₀)
      have hqY := differenceQuotient_eq_intervalIntegral hf hpathY (abs_pos.mp hh₀)
      have hqdiff : q x - q y =
          ∫ t in (0 : ℝ)..1,
            (fderiv ℝ f (x + t • (h • v))) v -
              (fderiv ℝ f (y + t • (h • v))) v := by
        rw [intervalIntegral.integral_sub hIntX hIntY, ← hqX, ← hqY]
      let C : ℝ := (K : ℝ) * dist x y ^ (α : ℝ)
      have hCnonneg : 0 ≤ C := by
        dsimp [C]
        positivity
      have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
          ‖(fderiv ℝ f (x + t • (h • v))) v -
            (fderiv ℝ f (y + t • (h • v))) v‖ ≤ C := by
        let zx : E := x + t • (h • v)
        let zy : E := y + t • (h • v)
        have hzxball : zx ∈ Metric.ball (0 : E) R := by
          simpa [zx] using hpathX t ht
        have hzyball : zy ∈ Metric.ball (0 : E) R := by
          simpa [zy] using hpathY t ht
        have hzx : zx ∈ Metric.closedBall (0 : E) R :=
          Metric.ball_subset_closedBall hzxball
        have hzy : zy ∈ Metric.closedBall (0 : E) R :=
          Metric.ball_subset_closedBall hzyball
        have hdist : dist zx zy = dist x y := by
          simp only [zx, zy, dist_eq_norm]
          congr 1
          abel_nf
        have hmap := fderiv_holderOn hbound hzx hzy
        rw [hdist] at hmap
        have hEval : ‖(fderiv ℝ f zx) v - (fderiv ℝ f zy) v‖ ≤
            ‖iteratedFDeriv ℝ 1 f zx - iteratedFDeriv ℝ 1 f zy‖ * ‖v‖ := by
          let m : Fin 1 → E := fun _ => v
          have heval := (iteratedFDeriv ℝ 1 f zx - iteratedFDeriv ℝ 1 f zy).le_opNorm m
          simpa [m, iteratedFDeriv_one_apply] using heval
        calc
          ‖(fderiv ℝ f zx) v - (fderiv ℝ f zy) v‖ ≤
              ‖iteratedFDeriv ℝ 1 f zx - iteratedFDeriv ℝ 1 f zy‖ * ‖v‖ := hEval
          _ ≤ ‖iteratedFDeriv ℝ 1 f zx - iteratedFDeriv ℝ 1 f zy‖ * 1 :=
            mul_le_mul_of_nonneg_left hv (norm_nonneg _)
          _ ≤ C := by simpa [C, hdist] using hmap
      have hnorm : ‖q x - q y‖ ≤ C := by
        rw [hqdiff]
        calc
          ‖∫ t in (0 : ℝ)..1,
              (fderiv ℝ f (x + t • (h • v))) v -
                (fderiv ℝ f (y + t • (h • v))) v‖ ≤ C * |(1 : ℝ) - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
              have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
                rcases (show t ∈ Set.Ioc (0 : ℝ) 1 by simpa using ht) with ⟨ht0, ht1⟩
                exact ⟨ht0.le, ht1⟩
              exact hpoint t ht')
          _ = C := by norm_num
      have hα : 0 ≤ (α : ℝ) := by exact_mod_cast α.2
      have hrpow := ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist x y) hα
      have hcoe : (K : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) := by simp
      have htoENN : (K : ℝ≥0∞) * edist x y ^ (α : ℝ) = ENNReal.ofReal C := by
        dsimp [C]
        rw [hcoe, edist_dist, hrpow, ← ENNReal.ofReal_mul (show 0 ≤ (K : ℝ) by positivity)]
      have hdistQ : edist (q x) (q y) = ENNReal.ofReal ‖q x - q y‖ := by
        rw [edist_dist, dist_eq_norm]
      rw [hdistQ, htoENN]
      exact ENNReal.ofReal_le_ofReal hnorm
    change HolderOnWith K α (iteratedFDeriv ℝ 0 q) (Metric.closedBall (0 : E) r)
    rw [iteratedFDeriv_zero_eq_comp]
    let c := continuousMultilinearCurryFin0 ℝ E F
    intro x hx y hy
    change edist (c.symm (q x)) (c.symm (q y)) ≤ (K : ℝ≥0∞) * edist x y ^ (α : ℝ)
    rw [c.symm.edist_map]
    exact hqHolder x hx y hy

end
