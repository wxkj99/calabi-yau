-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/MasterInequality/CrossBoundsPointwiseProductBounds.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.MasterInequality.Coercivity

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergTestFunction
open Sobolev.NirenbergSubstitution
open Sobolev.NirenbergCoercivity
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergCrossBounds

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem abs_diffQuot_le_of_bound
    {g : E → ℝ} (hg : ContDiff ℝ 1 g) (k : Fin d) (h : ℝ)
    {x : E} {M : ℝ}
    (hM : ∀ y ∈ Metric.cthickening |h| ({x} : Set E),
      |(fderiv ℝ g y) (EuclideanSpace.single k 1)| ≤ M) :
    |diffQuot k h g x| ≤ M := by
  by_cases hh : h = 0
  · subst hh
    rw [diffQuot_zero_h]
    have hx0 : x ∈ Metric.cthickening |0| ({x} : Set E) := by
      have : x ∈ ({x} : Set E) := rfl
      exact self_subset_cthickening _ this
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM x hx0)
    simp only [Pi.zero_apply, abs_zero]
    exact hM0
  set e : E := EuclideanSpace.single k (1 : ℝ) with he
  have hFTC := diffQuot_eq_integral_partialDeriv (d := d) hg k hh x
  rw [hFTC]
  have hpt : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 →
      |(fderiv ℝ g (x + (s * h) • e)) e| ≤ M := by
    intro s hs
    have hin : x + (s * h) • e ∈ Metric.cthickening |h| ({x} : Set E) := by
      refine Metric.mem_cthickening_of_dist_le _ x |h| ({x} : Set E) rfl ?_
      have hsing_norm : ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
      have hdist_eq :
          dist (x + (s * h) • e) x = |s * h| := by
        rw [dist_eq_norm]
        change ‖(x + (s * h) • e) - x‖ = |s * h|
        rw [add_sub_cancel_left, norm_smul, hsing_norm, mul_one,
          Real.norm_eq_abs]
      rw [hdist_eq]
      have hs_nn : 0 ≤ s := le_of_lt hs.1
      have hs_le_one : s ≤ 1 := hs.2
      have habs_eq : |s * h| = s * |h| := by
        rw [abs_mul, abs_of_nonneg hs_nn]
      rw [habs_eq]
      have habs_h_nn : 0 ≤ |h| := abs_nonneg h
      calc s * |h| ≤ 1 * |h| :=
              mul_le_mul_of_nonneg_right hs_le_one habs_h_nn
        _ = |h| := one_mul _
    exact hM _ hin
  have hint_cont : Continuous (fun s : ℝ =>
      (fderiv ℝ g (x + (s * h) • e)) e) := by
    have hfd_cont : Continuous (fun y : E => fderiv ℝ g y) :=
      hg.continuous_fderiv one_ne_zero
    have hgamma_cont : Continuous (fun s : ℝ => x + (s * h) • e) :=
      continuous_const.add
        ((continuous_id.mul continuous_const).smul continuous_const)
    exact (hfd_cont.comp hgamma_cont).clm_apply continuous_const
  have hint_M : ∀ s : ℝ, s ∈ Set.Ioc (0 : ℝ) 1 → 0 ≤ M :=
    fun s hs => le_trans (abs_nonneg _) (hpt s hs)
  have h1 : 0 ∈ Set.Ioc (0 : ℝ) 1 ∨ ¬ (0 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := em _
  have hM_nonneg : 0 ≤ M := by
    have hs1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_refl _⟩
    exact hint_M 1 hs1
  have h_int :
      Integrable (fun s : ℝ => (fderiv ℝ g (x + (s * h) • e)) e)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    hint_cont.integrableOn_Ioc (a := 0) (b := 1)
  have h_int_abs :
      Integrable (fun s : ℝ => |(fderiv ℝ g (x + (s * h) • e)) e|)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    h_int.abs
  have h_int_const :
      Integrable (fun _ : ℝ => M)
        ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) := by
    have h_cont_M : Continuous (fun _ : ℝ => M) := continuous_const
    exact h_cont_M.integrableOn_Ioc (a := 0) (b := 1)
  have h_tri :
      |∫ s in Set.Ioc (0 : ℝ) 1, (fderiv ℝ g (x + (s * h) • e)) e| ≤
        ∫ s in Set.Ioc (0 : ℝ) 1, |(fderiv ℝ g (x + (s * h) • e)) e| := by
    exact abs_integral_le_integral_abs (μ := (volume : Measure ℝ).restrict _)
  have h_mono :
      ∫ s in Set.Ioc (0 : ℝ) 1, |(fderiv ℝ g (x + (s * h) • e)) e| ≤
        ∫ _s in Set.Ioc (0 : ℝ) 1, M := by
    refine integral_mono_ae h_int_abs h_int_const ?_
    refine ae_restrict_iff_subtype measurableSet_Ioc |>.mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro ⟨s, hs⟩
    exact hpt s hs
  have h_const_int :
      ∫ _s in Set.Ioc (0 : ℝ) 1, M = M := by
    rw [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ]
    simp [Real.volume_Ioc]
  rw [h_const_int] at h_mono
  exact le_trans h_tri h_mono

theorem abs_diffQuot_a_le_of_bound_on_set
    {a : E → ℝ} (ha : ContDiff ℝ 1 a) (k : Fin d) (h : ℝ)
    {K : Set E} {M : ℝ}
    (hM : ∀ y ∈ K, |(fderiv ℝ a y) (EuclideanSpace.single k 1)| ≤ M)
    {x : E} (hx : Metric.cthickening |h| ({x} : Set E) ⊆ K) :
    |diffQuot k h a x| ≤ M := by
  refine abs_diffQuot_le_of_bound (d := d) ha k h ?_
  intro y hy
  exact hM y (hx hy)

theorem singleton_cthick_subset
    (η : E → ℝ) {h h₀ : ℝ}
    {Ω' : Set E}
    (hh_support_in_Ω' : Metric.cthickening h₀ (tsupport η) ⊆ Ω')
    (h_abs : |h| ≤ h₀)
    {x : E} (hx : x ∈ tsupport η) :
    Metric.cthickening |h| ({x} : Set E) ⊆ Ω' := by
  intro y hy
  rw [Metric.mem_cthickening_iff] at hy
  refine hh_support_in_Ω' ?_
  rw [Metric.mem_cthickening_iff]
  have hsub : ({x} : Set E) ⊆ tsupport η := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]; exact hx
  have h_anti : Metric.infEDist y (tsupport η) ≤ Metric.infEDist y ({x} : Set E) :=
    Metric.infEDist_anti hsub
  refine le_trans h_anti ?_
  refine le_trans hy ?_
  exact_mod_cast ENNReal.ofReal_le_ofReal h_abs

lemma two_abs_mul_le_eps_sq_add (a b ε : ℝ) (hε : 0 < ε) :
    2 * |a| * |b| ≤ ε * a^2 + (1/ε) * b^2 := by
  simpa only [sq_abs, one_div] using two_mul_le_add_mul_sq (a := |a|) (b := |b|) hε

end Sobolev.NirenbergCrossBounds
