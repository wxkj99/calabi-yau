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

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
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

omit [NeZero d] in
theorem abs_diffQuot_a_le_of_bound_on_set
    {a : E → ℝ} (ha : ContDiff ℝ 1 a) (k : Fin d) (h : ℝ)
    {K : Set E} {M : ℝ}
    (hM : ∀ y ∈ K, |(fderiv ℝ a y) (EuclideanSpace.single k 1)| ≤ M)
    {x : E} (hx : Metric.cthickening |h| ({x} : Set E) ⊆ K) :
    |diffQuot k h a x| ≤ M := by
  refine abs_diffQuot_le_of_bound (d := d) ha k h ?_
  intro y hy
  exact hM y (hx hy)

omit [NeZero d] in
private theorem abs_translate_le_of_bound_on_set
    {a : E → ℝ} (k : Fin d) (h : ℝ)
    {K : Set E} {M : ℝ}
    (hM : ∀ y ∈ K, |a y| ≤ M)
    {x : E} (hx : x + h • EuclideanSpace.single k 1 ∈ K) :
    |translate k h a x| ≤ M := by
  unfold translate
  exact hM _ hx

omit [NeZero d] in
private theorem shift_in_omega'
    (η : E → ℝ) (k : Fin d) {h h₀ : ℝ}
    {Ω' : Set E}
    (hh_support_in_Ω' : Metric.cthickening h₀ (tsupport η) ⊆ Ω')
    (h_abs : |h| ≤ h₀)
    {x : E} (hx : x ∈ tsupport η) :
    x + h • EuclideanSpace.single k 1 ∈ Ω' := by
  refine hh_support_in_Ω' ?_
  refine Metric.mem_cthickening_of_dist_le _ x h₀ (tsupport η) hx ?_
  have hsing_norm : ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
  have hdist_eq :
      dist (x + h • EuclideanSpace.single k 1) x = |h| := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hsing_norm, mul_one,
      Real.norm_eq_abs]
  rw [hdist_eq]
  exact h_abs

omit [NeZero d] in
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

theorem translated_coeff_cutoff_gradient_pointwise_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} {Λ : ℝ}
    (h_Λ : ∀ i j : Fin d, ∀ x ∈ closure Ω', |B.a x i j| ≤ Λ)
    (i j k : Fin d) {h : ℝ}
    (hh_support_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω')
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    |2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x| ≤
      ε * (η x)^2 *
        (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
      (1/ε) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
  let _ := hu
  let _ := hη
  by_cases hx : x ∈ tsupport η
  · have h_shift_in : x + h • EuclideanSpace.single k 1 ∈ closure Ω' := by
      have h_shift_in_Ω' : x + h • EuclideanSpace.single k 1 ∈ Ω' :=
        shift_in_omega' (d := d) η k hh_support_in_Ω' (le_refl _) hx
      exact subset_closure h_shift_in_Ω'
    have h_τa_bound : |translate k h (fun y => B.a y i j) x| ≤ Λ := by
      unfold translate
      exact h_Λ i j _ h_shift_in
    have h_dη_bound : |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ N := by
      have hsing_norm :
          ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ = 1 := by simp
      have h_apply :
          ‖(fderiv ℝ η x) (EuclideanSpace.single j 1)‖ ≤
            ‖fderiv ℝ η x‖ * ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ :=
        (fderiv ℝ η x).le_opNorm _
      rw [hsing_norm, mul_one] at h_apply
      have h2 : ‖(fderiv ℝ η x) (EuclideanSpace.single j 1)‖ ≤ N :=
        h_apply.trans (h_fderiv_eta x)
      rw [Real.norm_eq_abs] at h2
      exact h2
    have h_η_abs : |η x| ≤ 1 := by
      have h_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
      have h0 : 0 ≤ η x := h_in.1
      have h1 : η x ≤ 1 := h_in.2
      rw [abs_of_nonneg h0]; exact h1
    have h_η_nn : 0 ≤ η x := (hη_range ⟨x, rfl⟩).1
    set A : ℝ := η x *
      diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x
    set B' : ℝ := translate k h (fun y => B.a y i j) x *
      ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
      diffQuot k h u x
    have h_eq_lhs :
        |2 * translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            diffQuot k h u x| =
        2 * |A| * |B'| := by
      have hRHS :
          (η x) *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x) *
            (translate k h (fun y => B.a y i j) x *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              diffQuot k h u x) =
          translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            diffQuot k h u x := by ring
      have h_AB' : A * B' =
          translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            diffQuot k h u x := by
        change (η x) * _ * (translate k h _ x * _ * diffQuot k h u x) = _
        exact hRHS
      have h_2AB' : 2 * A * B' =
          2 * translate k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            diffQuot k h u x := by
        have : 2 * (A * B') = 2 *
            (translate k h (fun y => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
              diffQuot k h u x) := by rw [h_AB']
        linarith
      rw [← h_2AB']
      rw [show |2 * A * B'| = 2 * |A| * |B'| by
        rw [show (2 * A * B') = 2 * (A * B') by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
          abs_mul]
        ring]
    rw [h_eq_lhs]
    have h_young := two_abs_mul_le_eps_sq_add A B' ε hε
    refine h_young.trans ?_
    have hA_sq : A^2 = (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 := by
      change ((η x) * _)^2 = _
      ring
    have hB'_sq_le : B'^2 ≤ Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
      have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
        rw [Set.indicator_of_mem hx]
      rw [h_indicator]
      change (translate k h (fun y => B.a y i j) x *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h u x)^2 ≤ _
      have h_τa_sq_le : (translate k h (fun y => B.a y i j) x)^2 ≤ Λ^2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h_τa_bound 2
      have h_dη_sq_le : ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 ≤ N^2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h_dη_bound 2
      have hΛ_nn : 0 ≤ Λ := by
        have h_x_in_Ω' : x ∈ Ω' :=
          hh_support_in_Ω' (self_subset_cthickening _ hx)
        have h_x_in : x ∈ closure Ω' := subset_closure h_x_in_Ω'
        exact le_trans (abs_nonneg _) (h_Λ i j x h_x_in)
      have hN_nn : 0 ≤ N := le_trans (norm_nonneg _) (h_fderiv_eta x)
      have hΛ_sq_nn : 0 ≤ Λ^2 := sq_nonneg _
      have hN_sq_nn : 0 ≤ N^2 := sq_nonneg _
      have h_dq_sq_nn : 0 ≤ (diffQuot k h u x)^2 := sq_nonneg _
      have h_τa_sq_nn : 0 ≤ (translate k h (fun y => B.a y i j) x)^2 := sq_nonneg _
      have h_dη_sq_nn : 0 ≤ ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 := sq_nonneg _
      have h_step1 : (translate k h (fun y => B.a y i j) x)^2 *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 *
            (diffQuot k h u x)^2 ≤
          Λ^2 * N^2 * (diffQuot k h u x)^2 := by
        have h_first :
            (translate k h (fun y => B.a y i j) x)^2 *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 ≤ Λ^2 * N^2 := by
          have hac := mul_le_mul h_τa_sq_le h_dη_sq_le h_dη_sq_nn hΛ_sq_nn
          exact hac
        exact mul_le_mul_of_nonneg_right h_first h_dq_sq_nn
      calc (translate k h (fun y => B.a y i j) x *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              diffQuot k h u x)^2
          = (translate k h (fun y => B.a y i j) x)^2 *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1))^2 *
              (diffQuot k h u x)^2 := by ring
        _ ≤ Λ^2 * N^2 * (diffQuot k h u x)^2 := h_step1
        _ = Λ^2 * N^2 * 1 * (diffQuot k h u x)^2 := by rw [mul_one]
    have hε_pos : 0 < (1 : ℝ) / ε := one_div_pos.mpr hε
    have h_step :
        (1/ε) * B'^2 ≤ (1/ε) * (Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) :=
      mul_le_mul_of_nonneg_left hB'_sq_le hε_pos.le
    calc ε * A^2 + (1/ε) * B'^2
        ≤ ε * A^2 + (1/ε) * (Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) := by
            linarith
      _ = ε * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
          (1/ε) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 := by
            rw [hA_sq]; ring
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_LHS_zero : 2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x = 0 := by
      rw [h_η_zero]; ring
    rw [h_LHS_zero, abs_zero]
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    have h_t1_nn : 0 ≤ ε * (η x)^2 *
        (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 := by
      apply mul_nonneg
      · apply mul_nonneg hε.le (sq_nonneg _)
      · exact sq_nonneg _
    have h_t2_zero : (1/ε) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 = 0 := by
      rw [h_indicator]; ring
    linarith

theorem diffQuot_coeff_cutoff_squared_pointwise_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ}
    {η : E → ℝ}
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    (i j k : Fin d)
    {Ω' : Set E} {M : ℝ} (hM_nn : 0 ≤ M)
    (h_M : ∀ i j : Fin d, ∀ x ∈ closure Ω',
      |(fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single k 1)| ≤ M)
    {h : ℝ}
    (hh_support_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω')
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    |diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| ≤
      ε * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
      (M^2 / (4 * ε)) * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
  classical
  by_cases hx : x ∈ tsupport η
  · have h_dq_a_bound : |diffQuot k h (fun y => B.a y i j) x| ≤ M :=
      abs_diffQuot_a_le_of_bound_on_set (d := d) (B.contDiff_a i j |>.of_le (by norm_cast)) k h
        (h_M i j) ((singleton_cthick_subset (d := d) η hh_support_in_Ω' (le_refl _) hx).trans
          subset_closure)
    have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
    have h_η_nn : 0 ≤ η x := h_η_in.1
    have h_η_le : η x ≤ 1 := h_η_in.2
    have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
    set A : ℝ := η x *
      diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x with hA_def
    set B' : ℝ := M * η x *
      ((fderiv ℝ u x) (EuclideanSpace.single i 1)) with hB'_def
    have h2ε_pos : 0 < 2 * ε := by linarith
    have h_young := two_abs_mul_le_eps_sq_add A B' (2 * ε) h2ε_pos
    have h_AB_abs : |A * B'| ≤ ε * A^2 + (1/(4*ε)) * B'^2 := by
      have h1 : |A * B'| = |A| * |B'| := abs_mul A B'
      have h_double : 2 * (ε * A^2 + (1/(4*ε)) * B'^2) =
          2 * ε * A^2 + (1/(2*ε)) * B'^2 := by
        field_simp
        ring
      have h_ε_ne : ε ≠ 0 := ne_of_gt hε
      linarith [h_young, h_double]
    have h_lhs_bound :
        |diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| ≤
          |A * B'| := by
      have h_lhs_abs_eq : |diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| =
          |diffQuot k h (fun y => B.a y i j) x| * (η x)^2 *
            |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| := by
        rw [abs_mul, abs_mul, abs_mul]
        rw [show |(η x)^2| = (η x)^2 from abs_of_nonneg h_η_sq_nn]
      have h_AB_abs_eq : |A * B'| =
          M * (η x)^2 * |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
          |diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x| := by
        change |(η x * _) * (M * η x * _)| = _
        rw [show η x * diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x *
            (M * η x * (fderiv ℝ u x) (EuclideanSpace.single i 1)) =
          M * (η x)^2 * (fderiv ℝ u x) (EuclideanSpace.single i 1) *
            diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x from by
              rw [sq]; ring]
        rw [abs_mul, abs_mul, abs_mul]
        rw [abs_of_nonneg hM_nn, abs_of_nonneg h_η_sq_nn]
      rw [h_lhs_abs_eq, h_AB_abs_eq]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h_dq_a_bound h_η_sq_nn
    refine h_lhs_bound.trans ?_
    refine h_AB_abs.trans ?_
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx]
    rw [h_indicator]
    have hA_sq : A^2 = (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 := by
      change (η x * _)^2 = _; ring
    have hB'_sq_le : B'^2 ≤ M^2 * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
      change (M * η x * _)^2 ≤ _; nlinarith
    have h_4ε_pos : 0 < 4 * ε := by linarith
    have h_4ε_ne : (4 * ε) ≠ 0 := ne_of_gt h_4ε_pos
    have h_inv_4ε_nn : 0 ≤ 1 / (4 * ε) :=
      one_div_nonneg.mpr (by linarith)
    have h_step :
        (1/(4*ε)) * B'^2 ≤ (1/(4*ε)) * (M^2 * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
      mul_le_mul_of_nonneg_left hB'_sq_le h_inv_4ε_nn
    calc ε * A^2 + (1/(4*ε)) * B'^2
        ≤ ε * A^2 + (1/(4*ε)) *
            (M^2 * (η x)^2 *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) := by linarith
      _ = ε * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
          (M^2 / (4 * ε)) * (η x)^2 * 1 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
            rw [hA_sq]
            have h_div_eq : 1 / (4 * ε) * (M^2 * (η x)^2 *
                ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
                M^2 / (4 * ε) * (η x)^2 * 1 *
                  ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
              field_simp
            linarith [h_div_eq]
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    rw [h_indicator]
    have h_lhs_zero : diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x = 0 := by
      rw [h_η_zero]; ring
    rw [h_lhs_zero, abs_zero]
    have h_t1_nn : 0 ≤ ε * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 := by
      apply mul_nonneg
      · apply mul_nonneg hε.le (sq_nonneg _)
      · exact sq_nonneg _
    have h_t2_zero : (M^2 / (4 * ε)) * (η x)^2 * 0 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 = 0 := by ring
    linarith

theorem diffQuot_coeff_cutoff_gradient_pointwise_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ}
    {η : E → ℝ}
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    (i j k : Fin d)
    {Ω' : Set E} {M : ℝ} (hM_nn : 0 ≤ M)
    (h_M : ∀ i j : Fin d, ∀ x ∈ closure Ω',
      |(fderiv ℝ (fun y : E => B.a y i j) x) (EuclideanSpace.single k 1)| ≤ M)
    {h : ℝ}
    (hh_support_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω') (x : E) :
    |2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x| ≤
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 := by
  classical
  by_cases hx : x ∈ tsupport η
  · have h_dq_a_bound : |diffQuot k h (fun y => B.a y i j) x| ≤ M := by
      have hCD : ContDiff ℝ 1 (fun y : E => B.a y i j) :=
        (B.contDiff_a i j).of_le (by norm_cast)
      exact abs_diffQuot_a_le_of_bound_on_set (d := d) hCD k h
        (h_M i j) ((singleton_cthick_subset (d := d) η hh_support_in_Ω' (le_refl _) hx).trans
          subset_closure)
    have h_dη_bound : |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤ N := by
      have hsing_norm :
          ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ = 1 := by simp
      have h_apply :
          ‖(fderiv ℝ η x) (EuclideanSpace.single j 1)‖ ≤
            ‖fderiv ℝ η x‖ * ‖(EuclideanSpace.single j (1 : ℝ) : E)‖ :=
        (fderiv ℝ η x).le_opNorm _
      rw [hsing_norm, mul_one] at h_apply
      have h2 := h_apply.trans (h_fderiv_eta x)
      rw [Real.norm_eq_abs] at h2
      exact h2
    have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
    have h_η_nn : 0 ≤ η x := h_η_in.1
    have h_η_le : η x ≤ 1 := h_η_in.2
    have hN_nn : 0 ≤ N := le_trans (norm_nonneg _) (h_fderiv_eta x)
    have h_lhs_eq :
        |2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h u x| =
          2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
            |(fderiv ℝ η x) (EuclideanSpace.single j 1)| *
            |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h u x| := by
      rw [show (2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h u x) =
          2 * (diffQuot k h (fun y => B.a y i j) x *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            diffQuot k h u x * η x) from by ring]
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      rw [abs_of_nonneg h_η_nn]
      ring
    rw [h_lhs_eq]
    have h_step1 :
        2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
            |(fderiv ℝ η x) (EuclideanSpace.single j 1)| *
            |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h u x| ≤
          2 * M * (η x) * N *
            |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h u x| := by
      have h_step1a :
          2 * |diffQuot k h (fun y => B.a y i j) x| ≤ 2 * M := by
        linarith
      have h_step1b :
          2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) ≤ 2 * M * (η x) :=
        mul_le_mul_of_nonneg_right h_step1a h_η_nn
      have h_step1c :
          2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤
            2 * M * (η x) * N := by
        have h_step1c1 : 0 ≤ 2 * M * (η x) :=
          mul_nonneg (mul_nonneg (by linarith) hM_nn) h_η_nn
        calc 2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| ≤
            2 * M * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| := by
              exact mul_le_mul_of_nonneg_right h_step1b (abs_nonneg _)
          _ ≤ 2 * M * (η x) * N :=
              mul_le_mul_of_nonneg_left h_dη_bound h_step1c1
      have h_step1c1 : 0 ≤ 2 * M * (η x) * N :=
        mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hM_nn) h_η_nn) hN_nn
      have h_intermediate : 2 * |diffQuot k h (fun y => B.a y i j) x| * (η x) *
              |(fderiv ℝ η x) (EuclideanSpace.single j 1)| *
              |(fderiv ℝ u x) (EuclideanSpace.single i 1)| ≤
            2 * M * (η x) * N *
              |(fderiv ℝ u x) (EuclideanSpace.single i 1)| :=
        mul_le_mul_of_nonneg_right h_step1c (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h_intermediate (abs_nonneg _)
    refine h_step1.trans ?_
    have h_young2 : 2 *
        |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
        |diffQuot k h u x| ≤
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2 := by
      have := two_abs_mul_le_eps_sq_add ((fderiv ℝ u x) (EuclideanSpace.single i 1))
        (diffQuot k h u x) 1 zero_lt_one
      simp at this
      linarith
    have h_MN_η_nn : 0 ≤ M * (η x) * N :=
      mul_nonneg (mul_nonneg hM_nn h_η_nn) hN_nn
    have h_step2 :
        2 * M * (η x) * N *
          |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
          |diffQuot k h u x| ≤
        M * (η x) * N *
          (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) := by
      have h_eq : 2 * M * (η x) * N *
          |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
          |diffQuot k h u x| =
          M * (η x) * N *
          (2 * |(fderiv ℝ u x) (EuclideanSpace.single i 1)| *
            |diffQuot k h u x|) := by ring
      rw [h_eq]
      exact mul_le_mul_of_nonneg_left h_young2 h_MN_η_nn
    refine h_step2.trans ?_
    have h_step3 :
        M * (η x) * N *
          (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) ≤
        M * N *
          (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) := by
      have h_M_η_N_le : M * (η x) * N ≤ M * 1 * N := by
        refine mul_le_mul_of_nonneg_right ?_ hN_nn
        exact mul_le_mul_of_nonneg_left h_η_le hM_nn
      have h_M_N_eq : M * 1 * N = M * N := by ring
      have h_fact_nn : 0 ≤ ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          (diffQuot k h u x)^2 := by
        exact add_nonneg (sq_nonneg _) (sq_nonneg _)
      calc M * (η x) * N *
              (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) ≤
          M * 1 * N *
            (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) :=
            mul_le_mul_of_nonneg_right h_M_η_N_le h_fact_nn
        _ = M * N *
            (((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 + (diffQuot k h u x)^2) := by
            rw [h_M_N_eq]
    refine h_step3.trans ?_
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx]
    rw [h_indicator]
    ring_nf
    rfl
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    have h_lhs_zero : 2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x = 0 := by
      rw [h_η_zero]; ring
    rw [h_lhs_zero, abs_zero, h_indicator]
    have h_t1 : M * N * 0 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 = 0 := by ring
    have h_t2 : M * N * 0 * (diffQuot k h u x)^2 = 0 := by ring
    linarith

omit [NeZero d] in
private lemma fderiv_eta_sq_diffQuot_apply
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    (fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
        (EuclideanSpace.single k 1) =
      2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single k 1)) *
        diffQuot k h u x +
      η x ^ 2 * diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x := by
  have h_apply :=
    Sobolev.NirenbergTestFunction.fderiv_eta_sq_times_diffQuot_apply
      (d := d) hη hu k k hh x
  exact h_apply

omit [NeZero d] in
lemma fderiv_eta_sq_diffQuot_sq_bound
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    ((fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
        (EuclideanSpace.single k 1))^2 ≤
      8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 +
      2 * (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
  rw [fderiv_eta_sq_diffQuot_apply (d := d) hu hη k hh x]
  set A : ℝ := 2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single k 1)) *
    diffQuot k h u x with hA_def
  set B' : ℝ := η x ^ 2 * diffQuot k h
    (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x with hB'_def
  have h_AB_sq : (A + B')^2 ≤ 2 * A^2 + 2 * B'^2 := by nlinarith [sq_nonneg (A - B')]
  refine h_AB_sq.trans ?_
  have hN_nn : 0 ≤ N := le_trans (norm_nonneg _) (h_fderiv_eta x)
  have h_dη_bound : |(fderiv ℝ η x) (EuclideanSpace.single k 1)| ≤ N := by
    have hsing_norm :
        ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
    have h_apply :
        ‖(fderiv ℝ η x) (EuclideanSpace.single k 1)‖ ≤
          ‖fderiv ℝ η x‖ * ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ :=
      (fderiv ℝ η x).le_opNorm _
    rw [hsing_norm, mul_one] at h_apply
    have h2 := h_apply.trans (h_fderiv_eta x)
    rw [Real.norm_eq_abs] at h2
    exact h2
  by_cases hx : x ∈ tsupport η
  · have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 1 := by
      rw [Set.indicator_of_mem hx]
    rw [h_indicator]
    have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
    have h_η_le : η x ≤ 1 := h_η_in.2
    have h_η_nn : 0 ≤ η x := h_η_in.1
    have h_η_sq_le_one : (η x)^2 ≤ 1 := by
      calc (η x)^2 ≤ (1 : ℝ)^2 :=
              pow_le_pow_left₀ h_η_nn h_η_le 2
        _ = 1 := one_pow _
    have h_A_sq_bound : A^2 ≤ 4 * N^2 * (diffQuot k h u x)^2 := by
      change (2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single k 1)) *
        diffQuot k h u x)^2 ≤ _
      have h_pow_2 : (2 * η x * ((fderiv ℝ η x) (EuclideanSpace.single k 1)) *
            diffQuot k h u x)^2 =
          4 * (η x)^2 * ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 *
            (diffQuot k h u x)^2 := by ring
      rw [h_pow_2]
      have h_dη_sq_le : ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 ≤ N^2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h_dη_bound 2
      have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
      have h_dq_sq_nn : 0 ≤ (diffQuot k h u x)^2 := sq_nonneg _
      have h_step1 :
          4 * (η x)^2 * ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 ≤ 4 * 1 * N^2 := by
        have h1 : (η x)^2 ≤ 1 := h_η_sq_le_one
        have h2 : ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 ≤ N^2 := h_dη_sq_le
        have h_first : (η x)^2 * ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 ≤ 1 * N^2 := by
          exact mul_le_mul h1 h2 (sq_nonneg _) (le_of_lt (by linarith [sq_nonneg (η x)]))
        nlinarith
      calc 4 * (η x)^2 * ((fderiv ℝ η x) (EuclideanSpace.single k 1))^2 *
            (diffQuot k h u x)^2 ≤
          4 * 1 * N^2 * (diffQuot k h u x)^2 :=
            mul_le_mul_of_nonneg_right h_step1 h_dq_sq_nn
        _ = 4 * N^2 * (diffQuot k h u x)^2 := by ring
    have h_first : 2 * A^2 ≤ 8 * N^2 * 1 * (diffQuot k h u x)^2 := by
      have h := mul_le_mul_of_nonneg_left h_A_sq_bound (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have h_B'_sq : B'^2 = (η x)^4 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
      change (η x ^ 2 * _)^2 = _
      ring
    have h_B'_sq_le : 2 * B'^2 ≤ 2 * (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
      rw [h_B'_sq]
      have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
      have h_dq_sq_nn : 0 ≤ (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := sq_nonneg _
      have h_4_eq : (η x)^4 = (η x)^2 * (η x)^2 := by ring
      rw [h_4_eq]
      have h_step :
          (η x)^2 * ((η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) ≤
            (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
        have h_inner_nn : 0 ≤ ((η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) :=
          mul_nonneg h_η_sq_nn h_dq_sq_nn
        nlinarith
      nlinarith
    linarith
  · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
    have h_indicator : Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x = 0 :=
      Set.indicator_of_notMem hx _
    rw [h_indicator]
    have h_A_zero : A = 0 := by rw [hA_def, h_η_zero]; ring
    have h_B'_zero : B' = 0 := by rw [hB'_def, h_η_zero]; ring
    rw [h_A_zero, h_B'_zero]
    rw [h_η_zero]
    have h_t1_zero : 8 * N^2 * 0 * (diffQuot k h u x)^2 = 0 := by ring
    have h_t2_zero : 2 * (0 : ℝ)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 = 0 := by ring
    have h_lhs_zero : (0 : ℝ)^2 + 2 * (0 : ℝ)^2 = 0 := by ring
    nlinarith [sq_nonneg (diffQuot k h
      (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x),
      sq_nonneg (diffQuot k h u x)]

end Sobolev.NirenbergCrossBounds
