-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/SubstitutionIdentity/Substitution.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Nirenberg.H2Regularity.Defs
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.Basic
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.SmoothRegularity

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Sobolev
open Sobolev.NirenbergEuclidean
open Sobolev.NirenbergTestFunction
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Sobolev.NirenbergSubstitution

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem integral_diffQuot_mul_eq_neg_integral_mul_diffQuot_locally_supported
    {f g : E → ℝ} (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hf_continuous : Continuous f) (hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hg_support : HasCompactSupport g) :
    ∫ x, diffQuot k h f x * g x ∂(volume : Measure E) =
      -∫ x, f x * diffQuot k (-h) g x ∂(volume : Measure E) := by
  set e : E := EuclideanSpace.single k (1 : ℝ) with he
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have hg_cont : Continuous g := hg_smooth.continuous
  have h_diffQuot_neg_g_cont : Continuous (diffQuot k (-h) g) :=
    continuous_diffQuot_of_continuous (d := d) k (-h) hg_cont
  have h_diffQuot_neg_g_support : HasCompactSupport (diffQuot k (-h) g) :=
    hasCompactSupport_diffQuot_of_hasCompactSupport (d := d) hg_support k (-h)
  have h_translate_h_f_cont : Continuous (translate k h f) :=
    continuous_translate (d := d) k h hf_continuous
  have h_translate_neg_h_g_cont : Continuous (translate k (-h) g) :=
    continuous_translate (d := d) k (-h) hg_cont
  have h_translate_neg_h_g_support : HasCompactSupport (translate k (-h) g) :=
    hasCompactSupport_translate_of_hasCompactSupport (d := d) hg_support k (-h)
  have hfg_int : Integrable (fun x => f x * g x) volume := by
    have hcont : Continuous (fun x : E => f x * g x) := hf_continuous.mul hg_cont
    have hsupp : HasCompactSupport (fun x : E => f x * g x) :=
      hg_support.mul_left
    exact hcont.integrable_of_hasCompactSupport hsupp
  have h_translate_f_g_int :
      Integrable (fun x => translate k h f x * g x) volume := by
    have hcont : Continuous (fun x : E => translate k h f x * g x) :=
      h_translate_h_f_cont.mul hg_cont
    have hsupp : HasCompactSupport (fun x : E => translate k h f x * g x) :=
      hg_support.mul_left
    exact hcont.integrable_of_hasCompactSupport hsupp
  have h_f_translate_g_int :
      Integrable (fun x => f x * translate k (-h) g x) volume := by
    have hcont : Continuous (fun x : E => f x * translate k (-h) g x) :=
      hf_continuous.mul h_translate_neg_h_g_cont
    have hsupp : HasCompactSupport (fun x : E => f x * translate k (-h) g x) :=
      h_translate_neg_h_g_support.mul_left
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hLHS_pointwise : ∀ x : E,
      diffQuot k h f x * g x =
        (translate k h f x * g x - f x * g x) / h := by
    intro x
    rw [diffQuot_apply_of_ne (d := d) k hh f x]
    change (f (x + h • e) - f x) / h * g x =
      (translate k h f x * g x - f x * g x) / h
    change (f (x + h • e) - f x) / h * g x =
      (f (x + h • e) * g x - f x * g x) / h
    rw [div_mul_eq_mul_div, sub_mul]
  have hRHS_pointwise : ∀ x : E,
      f x * diffQuot k (-h) g x =
        (f x * translate k (-h) g x - f x * g x) / (-h) := by
    intro x
    rw [diffQuot_apply_of_ne (d := d) k hnh g x]
    change f x * ((g (x + (-h) • e) - g x) / (-h)) =
      (f x * translate k (-h) g x - f x * g x) / (-h)
    change f x * ((g (x + (-h) • e) - g x) / (-h)) =
      (f x * g (x + (-h) • e) - f x * g x) / (-h)
    rw [mul_div_assoc', mul_sub]
  have hLHS_decomp :
      ∫ x, diffQuot k h f x * g x ∂(volume : Measure E) =
        ((∫ x, translate k h f x * g x ∂(volume : Measure E)) -
            ∫ x, f x * g x ∂(volume : Measure E)) / h := by
    have heq_fun : (fun x => diffQuot k h f x * g x) =
        (fun x => (translate k h f x * g x - f x * g x) / h) := by
      ext x; exact hLHS_pointwise x
    rw [heq_fun, integral_div, integral_sub h_translate_f_g_int hfg_int]
  have hRHS_decomp :
      ∫ x, f x * diffQuot k (-h) g x ∂(volume : Measure E) =
        ((∫ x, f x * translate k (-h) g x ∂(volume : Measure E)) -
            ∫ x, f x * g x ∂(volume : Measure E)) / (-h) := by
    have heq_fun : (fun x => f x * diffQuot k (-h) g x) =
        (fun x => (f x * translate k (-h) g x - f x * g x) / (-h)) := by
      ext x; exact hRHS_pointwise x
    rw [heq_fun, integral_div, integral_sub h_f_translate_g_int hfg_int]
  have h_subst :
      ∫ x, f (x + h • e) * g x ∂(volume : Measure E) =
        ∫ x, f x * g (x + (-h) • e) ∂(volume : Measure E) := by
    have hint :=
      integral_add_right_eq_self
        (μ := (volume : Measure E))
        (f := fun x : E => f (x + h • e) * g x)
        ((-h) • e)
    have hsimp : ∀ x : E,
        f ((x + (-h) • e) + h • e) * g (x + (-h) • e) =
          f x * g (x + (-h) • e) := by
      intro x
      have hsmul : (-h) • e + h • e = (0 : E) := by
        rw [← add_smul]; simp
      have hcoll : (x + (-h) • e) + h • e = x := by
        rw [add_assoc, hsmul, add_zero]
      rw [hcoll]
    rw [show (∫ x, f (x + h • e) * g x ∂(volume : Measure E)) =
        ∫ x, f ((x + (-h) • e) + h • e) * g (x + (-h) • e)
          ∂(volume : Measure E) from hint.symm]
    refine integral_congr_ae ?_
    filter_upwards with x using hsimp x
  have hLHS_subst :
      ∫ x, translate k h f x * g x ∂(volume : Measure E) =
        ∫ x, f x * translate k (-h) g x ∂(volume : Measure E) := by
    have h1 :
        ∫ x, translate k h f x * g x ∂(volume : Measure E) =
          ∫ x, f (x + h • e) * g x ∂(volume : Measure E) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      change f (x + h • EuclideanSpace.single k 1) * g x = f (x + h • e) * g x
      rfl
    have h2 :
        ∫ x, f x * translate k (-h) g x ∂(volume : Measure E) =
          ∫ x, f x * g (x + (-h) • e) ∂(volume : Measure E) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      change f x * g (x + (-h) • EuclideanSpace.single k 1) =
        f x * g (x + (-h) • e)
      rfl
    rw [h1, h2, h_subst]
  rw [hLHS_decomp, hRHS_decomp, hLHS_subst]
  rw [div_neg, neg_neg]

omit [NeZero d] in
theorem nirenbergTestFunction_contDiff_hasCompactSupport_tsupport_subset
    {η u : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {Ω : Set E}
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hh_support : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (nirenbergTestFunction k h η u) ∧
    HasCompactSupport (nirenbergTestFunction k h η u) ∧
    tsupport (nirenbergTestFunction k h η u) ⊆ Ω := by
  refine ⟨?_, ?_, ?_⟩
  · exact contDiff_nirenbergTestFunction (d := d) hη hu k hh
  · exact hasCompactSupport_nirenbergTestFunction (d := d) hη_support k h
  · exact (tsupport_nirenbergTestFunction_subset (d := d) η u k h).trans hh_support

omit [NeZero d] in
private lemma fderiv_diffQuot_pointwise
    {g : E → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) :
    (fun x : E =>
        (fderiv ℝ (diffQuot k h g) x) (EuclideanSpace.single j 1)) =
      diffQuot k h
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) := by
  funext x
  exact fderiv_diffQuot_apply_eq_diffQuot_partial (d := d) hg k j hh x

theorem integral_a_partial_u_partial_diffQuot_eq
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ∫ x, B.a x i j *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        ((fderiv ℝ (nirenbergTestFunction k h η u) x)
          (EuclideanSpace.single j 1))
        ∂(volume : Measure E) =
      -∫ x, diffQuot k h (fun y => B.a y i j *
              ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
          ((fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
            (EuclideanSpace.single j 1))
        ∂(volume : Measure E) := by
  set g : E → ℝ := fun y : E => η y ^ 2 * diffQuot k h u y with hg_def
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    have h_eta_sq : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => η y ^ 2) := hη.pow 2
    have h_diffQuot_u : ContDiff ℝ (⊤ : ℕ∞) (diffQuot k h u) :=
      contDiff_diffQuot_of_contDiff (d := d) hu k hh
    exact h_eta_sq.mul h_diffQuot_u
  have hg_support : HasCompactSupport g := by
    have h_eta_sq_support : HasCompactSupport (fun y : E => η y ^ 2) := by
      have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
        funext y; ring
      rw [heq]
      exact hη_support.mul_right
    exact h_eta_sq_support.mul_right
  set f : E → ℝ := fun y : E =>
    B.a y i j * ((fderiv ℝ u y) (EuclideanSpace.single i 1)) with hf_def
  have hf_cont : Continuous f := by
    have h_a_cont : Continuous (fun y : E => B.a y i j) := B.continuous_a i j
    have h_partial_u_cont :
        Continuous (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) :=
      (hu.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_a_cont.mul h_partial_u_cont
  have h_test_eq : nirenbergTestFunction k h η u = diffQuot k (-h) g := rfl
  have h_LHS_rewrite :
      (fun x : E =>
          B.a x i j *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            ((fderiv ℝ (nirenbergTestFunction k h η u) x)
              (EuclideanSpace.single j 1))) =
        fun x : E =>
          f x * diffQuot k (-h)
            (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) x := by
    funext x
    rw [h_test_eq]
    rw [fderiv_diffQuot_apply_eq_diffQuot_partial (d := d) hg_smooth k j hnh x]
  have hG_smooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) := by
    have h_fderiv_smooth : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := by
      exact hg_smooth.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    have h_apply_smooth :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun T : E →L[ℝ] ℝ => T (EuclideanSpace.single j 1)) := by
      exact (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single j (1 : ℝ))).contDiff
    exact h_apply_smooth.comp h_fderiv_smooth
  have hG_support :
      HasCompactSupport
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) :=
    hg_support.fderiv_apply (𝕜 := ℝ) _
  have h_IBP :
      ∫ x, diffQuot k h f x *
          (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) x
          ∂(volume : Measure E) =
        -∫ x, f x * diffQuot k (-h)
            (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) x
            ∂(volume : Measure E) := by
    exact integral_diffQuot_mul_eq_neg_integral_mul_diffQuot_locally_supported
      (d := d) k hh hf_cont hG_smooth hG_support
  rw [h_LHS_rewrite]
  have hLHS_eq :
      ∫ x, f x * diffQuot k (-h)
            (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) x
            ∂(volume : Measure E) =
        -∫ x, diffQuot k h f x *
            (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single j 1)) x
            ∂(volume : Measure E) := by
    linarith
  rw [hLHS_eq]

theorem integral_principalIntegrand_eq_sum_integral
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u v : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hv_support : HasCompactSupport v) :
    ∫ x, B.principalIntegrand u v x ∂(volume : Measure E) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, B.a x i j *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ v x) (EuclideanSpace.single j 1))
        ∂(volume : Measure E) := by
  classical
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  have hv_C1 : ContDiff ℝ 1 v := hv.of_le (by norm_cast)
  have h_partial_u_cont : ∀ i : Fin d,
      Continuous (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    fun i => (hu_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h_partial_v_cont : ∀ j : Fin d,
      Continuous (fun x : E => (fderiv ℝ v x) (EuclideanSpace.single j 1)) :=
    fun j => (hv_C1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h_partial_v_support : ∀ j : Fin d,
      HasCompactSupport
        (fun x : E => (fderiv ℝ v x) (EuclideanSpace.single j 1)) :=
    fun j => hv_support.fderiv_apply (𝕜 := ℝ) _
  have h_pair_int : ∀ i j : Fin d,
      Integrable (fun x : E =>
        B.a x i j * ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ v x) (EuclideanSpace.single j 1))) volume := by
    intro i j
    have h_a_cont : Continuous (fun x : E => B.a x i j) := B.continuous_a i j
    have h1 : Continuous
        (fun x : E => B.a x i j * ((fderiv ℝ u x) (EuclideanSpace.single i 1))) :=
      h_a_cont.mul (h_partial_u_cont i)
    have h2 : Continuous
        (fun x : E =>
          B.a x i j * ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            ((fderiv ℝ v x) (EuclideanSpace.single j 1))) :=
      h1.mul (h_partial_v_cont j)
    have h_support : HasCompactSupport
        (fun x : E =>
          B.a x i j * ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            ((fderiv ℝ v x) (EuclideanSpace.single j 1))) := by
      exact (h_partial_v_support j).mul_left
    exact h2.integrable_of_hasCompactSupport h_support
  have h_eq_fun :
      (fun x : E => B.principalIntegrand u v x) =
        fun x : E =>
          ∑ i : Fin d, ∑ j : Fin d,
            B.a x i j * ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              ((fderiv ℝ v x) (EuclideanSpace.single j 1)) := by
    funext x
    rfl
  rw [h_eq_fun]
  have h_inner_int : ∀ i : Fin d,
      Integrable (fun x : E =>
        ∑ j : Fin d,
          B.a x i j * ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            ((fderiv ℝ v x) (EuclideanSpace.single j 1))) volume :=
    fun i => integrable_finsetSum _ (fun j _ => h_pair_int i j)
  rw [show (fun x : E =>
      ∑ i : Fin d, ∑ j : Fin d,
        B.a x i j * ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ v x) (EuclideanSpace.single j 1))) =
      fun x : E =>
        ∑ i : Fin d, (fun y : E =>
          ∑ j : Fin d,
            B.a y i j * ((fderiv ℝ u y) (EuclideanSpace.single i 1)) *
              ((fderiv ℝ v y) (EuclideanSpace.single j 1))) x from rfl]
  rw [integral_finsetSum _ (fun i _ => h_inner_int i)]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [show (fun y : E =>
      ∑ j : Fin d,
        B.a y i j * ((fderiv ℝ u y) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ v y) (EuclideanSpace.single j 1))) =
      fun y : E =>
        ∑ j : Fin d, (fun z : E =>
          B.a z i j * ((fderiv ℝ u z) (EuclideanSpace.single i 1)) *
            ((fderiv ℝ v z) (EuclideanSpace.single j 1))) y from rfl]
  rw [integral_finsetSum _ (fun j _ => h_pair_int i j)]

theorem nirenberg_substitution_identity
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    (h_weak : B.IsSmoothWeakSolution u f)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_support : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hh_support : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    -∑ i : Fin d, ∑ j : Fin d, ∫ x, diffQuot k h (fun y => B.a y i j *
            ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
          ((fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
            (EuclideanSpace.single j 1))
        ∂(volume : Measure E)
    + ∫ x in Ω, B.c x * u x * nirenbergTestFunction k h η u x
    = ∫ x in Ω, f x * nirenbergTestFunction k h η u x := by
  classical
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := h_weak.1
  obtain ⟨h_v_smooth, h_v_support, h_v_tsupp⟩ :=
    nirenbergTestFunction_contDiff_hasCompactSupport_tsupport_subset (d := d) hη hη_support hu k hh hh_support
  have h_bilin : B.bilin u (nirenbergTestFunction k h η u) =
      ∫ x in Ω, f x * nirenbergTestFunction k h η u x :=
    h_weak.2 (nirenbergTestFunction k h η u) h_v_smooth h_v_support h_v_tsupp
  have h_bilin_unfold :
      B.bilin u (nirenbergTestFunction k h η u) =
        ∫ x in Ω, B.principalIntegrand u (nirenbergTestFunction k h η u) x +
          B.c x * u x * (nirenbergTestFunction k h η u) x := rfl
  have h_v_C1 : ContDiff ℝ 1 (nirenbergTestFunction k h η u) :=
    h_v_smooth.of_le (by norm_cast)
  have hu_C1 : ContDiff ℝ 1 u := hu.of_le (by norm_cast)
  have h_principal_cont :
      Continuous (B.principalIntegrand u (nirenbergTestFunction k h η u)) :=
    B.continuous_principalIntegrand hu_C1 h_v_C1
  have h_partial_v_support : ∀ j : Fin d,
      HasCompactSupport
        (fun x : E =>
          (fderiv ℝ (nirenbergTestFunction k h η u) x)
            (EuclideanSpace.single j 1)) :=
    fun j => h_v_support.fderiv_apply (𝕜 := ℝ) _
  have h_principal_support :
      HasCompactSupport (B.principalIntegrand u (nirenbergTestFunction k h η u)) := by
    unfold SmoothEllipticBilinearForm.principalIntegrand
    refine HasCompactSupport.intro (K := tsupport (nirenbergTestFunction k h η u))
      (h_v_support) ?_
    intro x hx
    have h_fderiv_v_zero : fderiv ℝ (nirenbergTestFunction k h η u) x = 0 :=
      fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
    refine Finset.sum_eq_zero ?_
    intro i _
    refine Finset.sum_eq_zero ?_
    intro j _
    rw [h_fderiv_v_zero]
    simp
  have h_c_u_v_cont :
      Continuous
        (fun x : E => B.c x * u x * (nirenbergTestFunction k h η u) x) :=
    (B.continuous_c.mul hu.continuous).mul h_v_smooth.continuous
  have h_c_u_v_support :
      HasCompactSupport
        (fun x : E => B.c x * u x * (nirenbergTestFunction k h η u) x) :=
    h_v_support.mul_left
  have h_bilin_integrand_cont :
      Continuous
        (fun x : E =>
          B.principalIntegrand u (nirenbergTestFunction k h η u) x +
            B.c x * u x * (nirenbergTestFunction k h η u) x) :=
    h_principal_cont.add h_c_u_v_cont
  have h_bilin_integrand_support :
      HasCompactSupport
        (fun x : E =>
          B.principalIntegrand u (nirenbergTestFunction k h η u) x +
            B.c x * u x * (nirenbergTestFunction k h η u) x) :=
    h_principal_support.add h_c_u_v_support
  have h_bilin_integrand_tsupport :
      tsupport
        (fun x : E =>
          B.principalIntegrand u (nirenbergTestFunction k h η u) x +
            B.c x * u x * (nirenbergTestFunction k h η u) x) ⊆ Ω := by
    refine subset_trans ?_ h_v_tsupp
    refine closure_minimal ?_ isClosed_closure
    intro x hx
    have h_or :
        B.principalIntegrand u (nirenbergTestFunction k h η u) x ≠ 0 ∨
          B.c x * u x * (nirenbergTestFunction k h η u) x ≠ 0 := by
      by_contra hboth
      rw [not_or] at hboth
      obtain ⟨hb1, hb2⟩ := hboth
      apply hx
      change B.principalIntegrand u (nirenbergTestFunction k h η u) x +
        B.c x * u x * (nirenbergTestFunction k h η u) x = 0
      rw [not_not.mp hb1, not_not.mp hb2, add_zero]
    cases h_or with
    | inl hP =>
      by_contra hx_not
      apply hP
      unfold SmoothEllipticBilinearForm.principalIntegrand
      have h_fderiv_v_zero : fderiv ℝ (nirenbergTestFunction k h η u) x = 0 :=
        fderiv_of_notMem_tsupport (𝕜 := ℝ) hx_not
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      rw [h_fderiv_v_zero]
      simp
    | inr hQ =>
      have hv_ne : (nirenbergTestFunction k h η u) x ≠ 0 := by
        intro hv0
        apply hQ
        rw [hv0, mul_zero]
      have hv_support : x ∈ Function.support (nirenbergTestFunction k h η u) := hv_ne
      exact subset_closure hv_support
  have h_bilin_to_univ :
      ∫ x in Ω, B.principalIntegrand u (nirenbergTestFunction k h η u) x +
            B.c x * u x * (nirenbergTestFunction k h η u) x =
        ∫ x, B.principalIntegrand u (nirenbergTestFunction k h η u) x +
            B.c x * u x * (nirenbergTestFunction k h η u) x
          ∂(volume : Measure E) := by
    have h_zero_compl : ∀ x ∉ Ω,
        B.principalIntegrand u (nirenbergTestFunction k h η u) x +
            B.c x * u x * (nirenbergTestFunction k h η u) x = 0 := by
      intro x hx
      have hx_not : x ∉ tsupport (nirenbergTestFunction k h η u) := by
        intro hx_in; exact hx (h_v_tsupp hx_in)
      have hv_zero : (nirenbergTestFunction k h η u) x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      have h_fderiv_v_zero : fderiv ℝ (nirenbergTestFunction k h η u) x = 0 :=
        fderiv_of_notMem_tsupport (𝕜 := ℝ) hx_not
      change B.principalIntegrand u (nirenbergTestFunction k h η u) x +
          B.c x * u x * (nirenbergTestFunction k h η u) x = 0
      unfold SmoothEllipticBilinearForm.principalIntegrand
      rw [h_fderiv_v_zero, hv_zero]
      simp
    have h := setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure E)) (s := Ω)
      (f := fun x => B.principalIntegrand u (nirenbergTestFunction k h η u) x +
        B.c x * u x * (nirenbergTestFunction k h η u) x) h_zero_compl
    exact h
  have h_f_v_to_univ :
      ∫ x in Ω, f x * nirenbergTestFunction k h η u x =
        ∫ x, f x * nirenbergTestFunction k h η u x ∂(volume : Measure E) := by
    have h_zero_compl : ∀ x ∉ Ω,
        f x * nirenbergTestFunction k h η u x = 0 := by
      intro x hx
      have hx_not : x ∉ tsupport (nirenbergTestFunction k h η u) := by
        intro hx_in; exact hx (h_v_tsupp hx_in)
      have hv_zero : (nirenbergTestFunction k h η u) x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      rw [hv_zero, mul_zero]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure E)) (s := Ω)
      (f := fun x => f x * nirenbergTestFunction k h η u x) h_zero_compl
  have h_c_u_v_to_univ :
      ∫ x in Ω, B.c x * u x * nirenbergTestFunction k h η u x =
        ∫ x, B.c x * u x * nirenbergTestFunction k h η u x
          ∂(volume : Measure E) := by
    have h_zero_compl : ∀ x ∉ Ω,
        B.c x * u x * nirenbergTestFunction k h η u x = 0 := by
      intro x hx
      have hx_not : x ∉ tsupport (nirenbergTestFunction k h η u) := by
        intro hx_in; exact hx (h_v_tsupp hx_in)
      have hv_zero : (nirenbergTestFunction k h η u) x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      rw [hv_zero, mul_zero]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := (volume : Measure E)) (s := Ω)
      (f := fun x => B.c x * u x * nirenbergTestFunction k h η u x) h_zero_compl
  have h_principal_int :
      Integrable (B.principalIntegrand u (nirenbergTestFunction k h η u))
        volume :=
    h_principal_cont.integrable_of_hasCompactSupport h_principal_support
  have h_c_u_v_int :
      Integrable
        (fun x => B.c x * u x * nirenbergTestFunction k h η u x) volume :=
    h_c_u_v_cont.integrable_of_hasCompactSupport h_c_u_v_support
  have h_bilin_split :
      ∫ x, B.principalIntegrand u (nirenbergTestFunction k h η u) x +
          B.c x * u x * (nirenbergTestFunction k h η u) x
          ∂(volume : Measure E) =
        (∫ x, B.principalIntegrand u (nirenbergTestFunction k h η u) x
          ∂(volume : Measure E)) +
          ∫ x, B.c x * u x * nirenbergTestFunction k h η u x
            ∂(volume : Measure E) :=
    integral_add h_principal_int h_c_u_v_int
  have h_sum_int :
      ∫ x, B.principalIntegrand u (nirenbergTestFunction k h η u) x
        ∂(volume : Measure E) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, B.a x i j *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ (nirenbergTestFunction k h η u) x)
            (EuclideanSpace.single j 1))
        ∂(volume : Measure E) :=
    integral_principalIntegrand_eq_sum_integral (d := d) B hu h_v_smooth h_v_support
  have h_pair_IBP : ∀ i j : Fin d,
      ∫ x, B.a x i j *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ (nirenbergTestFunction k h η u) x)
            (EuclideanSpace.single j 1))
        ∂(volume : Measure E) =
        -∫ x, diffQuot k h (fun y => B.a y i j *
                ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
            ((fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
              (EuclideanSpace.single j 1))
          ∂(volume : Measure E) := by
    intro i j
    exact integral_a_partial_u_partial_diffQuot_eq (d := d) B hu hη hη_support
      i j k hh
  have hSwap_sum_neg :
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, B.a x i j *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ (nirenbergTestFunction k h η u) x)
            (EuclideanSpace.single j 1))
        ∂(volume : Measure E) =
      -∑ i : Fin d, ∑ j : Fin d,
        ∫ x, diffQuot k h (fun y => B.a y i j *
                ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
            ((fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
              (EuclideanSpace.single j 1))
          ∂(volume : Measure E) := by
    rw [show
      (∑ i : Fin d, ∑ j : Fin d, ∫ x, B.a x i j *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            ((fderiv ℝ (nirenbergTestFunction k h η u) x)
              (EuclideanSpace.single j 1))
          ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          -∫ x, diffQuot k h (fun y => B.a y i j *
                  ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
              ((fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
                (EuclideanSpace.single j 1))
            ∂(volume : Measure E) from ?_]
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_neg_distrib]
    · refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact h_pair_IBP i j
  have h_chain :
      ∫ x in Ω, f x * nirenbergTestFunction k h η u x =
        -∑ i : Fin d, ∑ j : Fin d,
          ∫ x, diffQuot k h (fun y => B.a y i j *
                  ((fderiv ℝ u y) (EuclideanSpace.single i 1))) x *
              ((fderiv ℝ (fun y : E => η y ^ 2 * diffQuot k h u y) x)
                (EuclideanSpace.single j 1))
            ∂(volume : Measure E) +
          ∫ x in Ω, B.c x * u x * nirenbergTestFunction k h η u x := by
    rw [← h_bilin, h_bilin_unfold, h_bilin_to_univ, h_bilin_split, h_sum_int,
      hSwap_sum_neg, h_c_u_v_to_univ]
  linarith

end Sobolev.NirenbergSubstitution
