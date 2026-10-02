module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Hölder bounds for averages of inverse-matrix entries

The segment coefficient is defined by integrating matrix entries on `[0,1]`. This lemma records
integrability explicitly and passes a parameter-uniform Hölder bound through that integral.
-/

@[expose] public section

open scoped NNReal Topology
open Set MeasureTheory

/-- An average over the unit interval preserves a uniform entrywise `C^{0,α}` bound. The
integrability hypothesis is stated pointwise in the spatial variable, as required to interpret the
interval integral. -/
theorem exists_holderBoundOn_interval_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α K : ℝ≥0) (hα₀ : 0 < α)
    (U : Set E) (F : ℝ → E → ℂ)
    (hHolder : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HolderBoundOn 0 α K U (F s))
    (hIntegrable : ∀ z ∈ U,
      IntervalIntegrable (fun s ↦ F s z) MeasureTheory.volume 0 1) :
    HolderBoundOn 0 α K U (fun z ↦ ∫ s in (0 : ℝ)..1, F s z) := by
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (z : E) (hz : z ∈ U) :
      ‖F s z‖ ≤ (K : ℝ) := by
    have h := (hHolder s hs).1 0 le_rfl z hz
    simpa only [norm_iteratedFDeriv_zero] using h
  have hinterval (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) 1) (z : E) (hz : z ∈ U) :
      ‖F s z‖ ≤ (K : ℝ) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact hpoint s ⟨hs.1.le, hs.2⟩ z hz
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    -- The unit interval length preserves the pointwise sup bound.
    have hbound : ‖∫ s in (0 : ℝ)..1, F s z‖ ≤ (K : ℝ) := by
      calc
        ‖∫ s in (0 : ℝ)..1, F s z‖ ≤ (K : ℝ) * |(1 : ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
            (C := (K : ℝ)) (fun s hs ↦ hinterval s hs z hz)
        _ = (K : ℝ) := by norm_num
    simpa only [norm_iteratedFDeriv_zero] using hbound
  · intro z hz w hw
    have hdiffint :
        (∫ s in (0 : ℝ)..1, F s z) - (∫ s in (0 : ℝ)..1, F s w) =
          ∫ s in (0 : ℝ)..1, (F s z - F s w) := by
      rw [intervalIntegral.integral_sub (hIntegrable z hz) (hIntegrable w hw)]
    have hnorm (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
        ‖F s z - F s w‖ ≤ (K : ℝ) * dist z w ^ (α : ℝ) := by
      let e := continuousMultilinearCurryFin0 ℝ E ℂ
      have heq : ‖e.symm (F s z) - e.symm (F s w)‖ = ‖F s z - F s w‖ := by
        rw [← e.symm.map_sub, LinearIsometryEquiv.norm_map]
      have h := (hHolder s hs).2.dist_le hz hw
      rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply] at h
      rw [dist_eq_norm, heq] at h
      simpa only [dist_eq_norm] using h
    have hnormint :
        ‖∫ s in (0 : ℝ)..1, (F s z - F s w)‖ ≤
          (K : ℝ) * dist z w ^ (α : ℝ) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := (K : ℝ) * dist z w ^ (α : ℝ)) (fun s hs ↦ by
          have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
            exact ⟨hs.1.le, hs.2⟩
          exact hnorm s hs')
      simpa using h
    have hdist :
        dist (∫ s in (0 : ℝ)..1, F s z) (∫ s in (0 : ℝ)..1, F s w) ≤
          (K : ℝ) * dist z w ^ (α : ℝ) := by
      rw [dist_eq_norm, hdiffint]
      exact hnormint
    have havg : edist (∫ s in (0 : ℝ)..1, F s z) (∫ s in (0 : ℝ)..1, F s w) ≤
        (K : ENNReal) * edist z w ^ (α : ℝ) := by
      calc
        edist (∫ s in (0 : ℝ)..1, F s z) (∫ s in (0 : ℝ)..1, F s w) =
            ENNReal.ofReal (dist (∫ s in (0 : ℝ)..1, F s z)
              (∫ s in (0 : ℝ)..1, F s w)) := edist_dist _ _
        _ ≤ ENNReal.ofReal ((K : ℝ) * dist z w ^ (α : ℝ)) :=
          ENNReal.ofReal_le_ofReal hdist
        _ = (K : ENNReal) * edist z w ^ (α : ℝ) := by
          rw [edist_dist, ENNReal.coe_nnreal_eq,
            ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity : 0 ≤ (α : ℝ)),
            ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ))]
    let e := continuousMultilinearCurryFin0 ℝ E ℂ
    change edist (e.symm (∫ s in (0 : ℝ)..1, F s z))
      (e.symm (∫ s in (0 : ℝ)..1, F s w)) ≤ (K : ENNReal) * edist z w ^ (α : ℝ)
    simpa only [e.symm.edist_map] using havg
