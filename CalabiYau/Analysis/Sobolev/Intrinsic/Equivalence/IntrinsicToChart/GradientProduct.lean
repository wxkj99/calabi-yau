-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Intrinsic/Equivalence/IntrinsicToChart/GradientProduct.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.NormEquivalence
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison

@[expose] public section

open CalabiYau.Riemannian

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace EquivalenceReverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.Chart

local notation "EuclN_E" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] in
lemma g_inner_cauchy_schwarz_sq
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    (g.inner x v w)^2 ≤ g.inner x v v * g.inner x w w := by
  have h_inner_self_nn : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
    intro z
    by_cases hz : z = 0
    · rw [hz]
      change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
      rw [(g.inner x).map_zero]
      change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
      simp
    · exact (g.pos x z hz).le
  have hsym : g.inner x v w = g.inner x w v := g.symm x v w
  have h_expand : ∀ t : ℝ, g.inner x (v + t • w) (v + t • w) =
      g.inner x v v + 2 * t * g.inner x v w + t^2 * g.inner x w w := by
    intro t
    have h1 : (g.inner x) (v + t • w) =
        (g.inner x) v + (g.inner x) (t • w) :=
      (g.inner x).map_add v (t • w)
    have h2 : (g.inner x) (t • w) = t • ((g.inner x) w) :=
      (g.inner x).map_smul t w
    have h_step :
        g.inner x (v + t • w) (v + t • w) =
          (g.inner x v) (v + t • w) + (g.inner x) (t • w) (v + t • w) := by
      have happly : g.inner x (v + t • w) =
          (g.inner x) v + (g.inner x) (t • w) := h1
      rw [show g.inner x (v + t • w) (v + t • w) =
            ((g.inner x) (v + t • w)) (v + t • w) from rfl, happly]
      rfl
    rw [h_step]
    rw [(g.inner x v).map_add, (g.inner x v).map_smul]
    rw [h2]
    rw [show ((t • (g.inner x) w) : TangentSpace I x →L[ℝ] ℝ) (v + t • w)
          = t * ((g.inner x w) (v + t • w)) from by
      change t • ((g.inner x) w) (v + t • w) = t * ((g.inner x w) (v + t • w))
      rw [smul_eq_mul]]
    rw [(g.inner x w).map_add, (g.inner x w).map_smul]
    rw [hsym]
    simp only [smul_eq_mul]
    ring
  have h_polynom : ∀ t : ℝ, 0 ≤
      g.inner x v v + 2 * t * g.inner x v w + t^2 * g.inner x w w := fun t => by
    rw [← h_expand t]; exact h_inner_self_nn _
  have h_v_nn : 0 ≤ g.inner x v v := h_inner_self_nn v
  have h_w_nn : 0 ≤ g.inner x w w := h_inner_self_nn w
  by_cases h_w_zero : g.inner x w w = 0
  · have h_zero : g.inner x v w = 0 := by
      by_contra h_ne
      set t₀ : ℝ := -(g.inner x v v + 1) / (2 * g.inner x v w)
      have h_poly_t₀ := h_polynom t₀
      rw [h_w_zero] at h_poly_t₀
      have h_simp :
          g.inner x v v + 2 * t₀ * g.inner x v w + t₀^2 * 0 =
            g.inner x v v + 2 * t₀ * g.inner x v w := by ring
      rw [h_simp] at h_poly_t₀
      have h_eval : 2 * t₀ * g.inner x v w = -(g.inner x v v + 1) := by
        change 2 * (-(g.inner x v v + 1) / (2 * g.inner x v w)) *
            g.inner x v w = -(g.inner x v v + 1)
        field_simp
      linarith
    rw [h_zero]
    have h_prod_nn : 0 ≤ g.inner x v v * g.inner x w w :=
      mul_nonneg h_v_nn h_w_nn
    have hzero_sq : (0 : ℝ)^2 ≤ g.inner x v v * g.inner x w w := by
      rw [zero_pow (Nat.succ_ne_zero 1)]
      exact h_prod_nn
    exact hzero_sq
  · have h_w_pos : 0 < g.inner x w w :=
      lt_of_le_of_ne h_w_nn (Ne.symm h_w_zero)
    set t₀ : ℝ := -g.inner x v w / g.inner x w w
    have h_poly_t₀ := h_polynom t₀
    have h_eval :
        g.inner x v v + 2 * t₀ * g.inner x v w + t₀^2 * g.inner x w w =
          g.inner x v v - (g.inner x v w)^2 / g.inner x w w := by
      change g.inner x v v +
          2 * (-g.inner x v w / g.inner x w w) * g.inner x v w +
          (-g.inner x v w / g.inner x w w)^2 * g.inner x w w =
        g.inner x v v - (g.inner x v w)^2 / g.inner x w w
      field_simp
      ring
    rw [h_eval] at h_poly_t₀
    have h_step : (g.inner x v w)^2 / g.inner x w w ≤ g.inner x v v := by linarith
    rw [div_le_iff₀ h_w_pos] at h_step
    linarith

omit [FiniteDimensional ℝ E] in
lemma abs_g_inner_le_sqrt_mul_sqrt
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  have h_inner_self_nn : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
    intro z
    by_cases hz : z = 0
    · rw [hz]
      change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
      rw [(g.inner x).map_zero]
      change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
      simp
    · exact (g.pos x z hz).le
  have h_sq := g_inner_cauchy_schwarz_sq (I := I) g x v w
  have h_v_nn : 0 ≤ g.inner x v v := h_inner_self_nn v
  have h_w_nn : 0 ≤ g.inner x w w := h_inner_self_nn w
  have h_abs_sq : |g.inner x v w|^2 = (g.inner x v w)^2 := sq_abs _
  have h_sqrt_le :
      Real.sqrt (|g.inner x v w|^2) ≤
        Real.sqrt (g.inner x v v * g.inner x w w) := by
    rw [h_abs_sq]
    exact Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (abs_nonneg _)] at h_sqrt_le
  rw [Real.sqrt_mul h_v_nn] at h_sqrt_le
  exact h_sqrt_le

lemma gradFun_mul_pointwise
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {ρ u : M → ℝ} {x : M}
    (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ x)
    (hu : MDifferentiableAt I 𝓘(ℝ, ℝ) u x) :
    CalabiYau.Riemannian.gradFun (I := I) g
      (fun y : M => ρ y * u y) x =
    ρ x • CalabiYau.Riemannian.gradFun (I := I) g u x +
    u x • CalabiYau.Riemannian.gradFun (I := I) g ρ x := by
  classical
  apply CalabiYau.Riemannian.metricFlatLinear_injective
    (I := I) g x
  ext v
  change g.inner x
      (CalabiYau.Riemannian.gradFun (I := I) g
        (fun y : M => ρ y * u y) x) v =
    g.inner x
      (ρ x • CalabiYau.Riemannian.gradFun (I := I) g u x +
        u x • CalabiYau.Riemannian.gradFun (I := I) g ρ x) v
  rw [CalabiYau.Riemannian.inner_gradFun (I := I) g _ x v]
  have h_fun_eq : (fun y : M => ρ y * u y) = ρ * u := by funext y; rfl
  set d_ρ : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) ρ x with hd_ρ_def
  set d_u : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) u x with hd_u_def
  have h_mfderiv_mul : mfderiv I 𝓘(ℝ, ℝ) (fun y : M => ρ y * u y) x v =
      ρ x * d_u v + u x * d_ρ v := by
    rw [h_fun_eq]
    have h_ρ_at : HasMFDerivAt I 𝓘(ℝ, ℝ) ρ x d_ρ := hρ.hasMFDerivAt
    have h_u_at : HasMFDerivAt I 𝓘(ℝ, ℝ) u x d_u := hu.hasMFDerivAt
    have hAt : HasMFDerivAt I 𝓘(ℝ, ℝ) (ρ * u) x
        ((ρ x • d_u + u x • d_ρ : TangentSpace I x →L[ℝ] ℝ)) :=
      h_ρ_at.mul h_u_at
    rw [hAt.mfderiv]
    change ((ρ x • d_u + u x • d_ρ : TangentSpace I x →L[ℝ] ℝ)) v =
        ρ x * d_u v + u x * d_ρ v
    rw [add_apply, smul_apply,
        smul_apply]
    simp [smul_eq_mul]
  rw [h_mfderiv_mul]
  symm
  have h1 : (g.inner x)
      (ρ x • CalabiYau.Riemannian.gradFun (I := I) g u x +
       u x • CalabiYau.Riemannian.gradFun (I := I) g ρ x) =
      (g.inner x) (ρ x • CalabiYau.Riemannian.gradFun
        (I := I) g u x) +
      (g.inner x) (u x • CalabiYau.Riemannian.gradFun
        (I := I) g ρ x) :=
    (g.inner x).map_add _ _
  change ((g.inner x)
      (ρ x • CalabiYau.Riemannian.gradFun (I := I) g u x +
       u x • CalabiYau.Riemannian.gradFun (I := I) g ρ x)) v =
    ρ x * d_u v + u x * d_ρ v
  rw [h1]
  rw [show (((g.inner x) (ρ x • CalabiYau.Riemannian.gradFun
      (I := I) g u x)) + ((g.inner x) (u x •
      CalabiYau.Riemannian.gradFun (I := I) g ρ x))) v =
      ((g.inner x) (ρ x • CalabiYau.Riemannian.gradFun
        (I := I) g u x)) v +
      ((g.inner x) (u x • CalabiYau.Riemannian.gradFun
        (I := I) g ρ x)) v from rfl]
  rw [(g.inner x).map_smul, (g.inner x).map_smul]
  rw [show (ρ x • (g.inner x) (CalabiYau.Riemannian.gradFun
        (I := I) g u x)) v = ρ x • ((g.inner x)
        (CalabiYau.Riemannian.gradFun (I := I) g u x)) v from rfl]
  rw [show (u x • (g.inner x) (CalabiYau.Riemannian.gradFun
        (I := I) g ρ x)) v = u x • ((g.inner x)
        (CalabiYau.Riemannian.gradFun (I := I) g ρ x)) v from rfl]
  simp only [smul_eq_mul]
  rw [show ((g.inner x) (CalabiYau.Riemannian.gradFun
        (I := I) g u x)) v = d_u v from by
    rw [hd_u_def]
    exact CalabiYau.Riemannian.inner_gradFun (I := I) g u x v]
  rw [show ((g.inner x) (CalabiYau.Riemannian.gradFun
        (I := I) g ρ x)) v = d_ρ v from by
    rw [hd_ρ_def]
    exact CalabiYau.Riemannian.inner_gradFun (I := I) g ρ x v]

lemma continuous_sqrt_g_inner_gradFun_self
    [I.Boundaryless]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    Continuous (fun x : M => Real.sqrt
      (g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g f x)
        (CalabiYau.Riemannian.gradFun (I := I) g f x))) := by
  have hcont := TangentBundle.continuous_g_inner_of_smooth_sections
    (I := I) (M := M) g
    (CalabiYau.Riemannian.gradG (I := I) g ⟨_, hf⟩)
    (CalabiYau.Riemannian.gradG (I := I) g ⟨_, hf⟩)
  have hcoe : (fun x : M => g.inner x
        ((CalabiYau.Riemannian.gradG (I := I) g ⟨_, hf⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((CalabiYau.Riemannian.gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)) =
      (fun x : M => g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g f x)
        (CalabiYau.Riemannian.gradFun (I := I) g f x)) := by
    funext x
    rw [CalabiYau.Riemannian.grad_g_apply (I := I) g ⟨_, hf⟩ x]
    change g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g f x)
        (CalabiYau.Riemannian.gradFun (I := I) g f x) =
      g.inner x
        (CalabiYau.Riemannian.gradFun (I := I) g f x)
        (CalabiYau.Riemannian.gradFun (I := I) g f x)
    rfl
  rw [hcoe] at hcont
  exact Real.continuous_sqrt.comp hcont

lemma exists_continuous_sup_of_compactSpace
    [CompactSpace M]
    {f : M → ℝ} (hf : Continuous f) (hf_nn : ∀ x, 0 ≤ f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, f x ≤ C := by
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hrange : IsCompact (Set.range f) := isCompact_range hf
    obtain ⟨C, hC_le⟩ := hrange.bddAbove
    refine ⟨C, ?_, fun x => hC_le ⟨x, rfl⟩⟩
    exact le_trans (hf_nn x₀) (hC_le ⟨x₀, rfl⟩)
  · refine ⟨0, le_refl _, fun x => (hM ⟨x⟩).elim⟩

private lemma chartAtlasPOU_le_one
    [T2Space M] [SigmaCompactSpace M] (α : M) (x : M) :
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 := by
  exact (CalabiYau.RiemannianVolume.chartAtlasPOU I M).le_one α x

private lemma chartAtlasPOU_nonneg
    [T2Space M] [SigmaCompactSpace M] (α : M) (x : M) :
    0 ≤ ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
  (CalabiYau.RiemannianVolume.chartAtlasPOU I M).nonneg α x

lemma abs_chartAtlasPOU_le_one
    [T2Space M] [SigmaCompactSpace M] (α : M) (x : M) :
    |((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| ≤ 1 :=
  abs_le.mpr ⟨by linarith [chartAtlasPOU_nonneg (I := I) (M := M) α x],
    chartAtlasPOU_le_one (I := I) (M := M) α x⟩

lemma sqrt_g_inner_gradFun_pou_mul_le
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (α : M) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun (I := I) g
            (fun y : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y) x)
          (CalabiYau.Riemannian.gradFun (I := I) g
            (fun y : M => ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) y * u y) x)) ≤
        K * (|u x| +
          Real.sqrt
            (g.inner x
              (CalabiYau.Riemannian.gradFun (I := I) g u x)
              (CalabiYau.Riemannian.gradFun (I := I) g u x))) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    CalabiYau.RiemannianVolume.chartAtlasPOU I M α
  obtain ⟨K_grad_ρ, hK_grad_ρ_nn, hK_grad_ρ⟩ :=
    exists_continuous_sup_of_compactSpace (M := M)
      (f := fun x : M => Real.sqrt
        (g.inner x
          (CalabiYau.Riemannian.gradFun (I := I) g
            ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (CalabiYau.Riemannian.gradFun (I := I) g
            ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)))
      (continuous_sqrt_g_inner_gradFun_self (I := I) (M := M) g ρ.contMDiff)
      (fun _ => Real.sqrt_nonneg _)
  refine ⟨max 1 K_grad_ρ, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro x
  have hρ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    ρ.contMDiff.mdifferentiable (by simp) x
  have hu_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) u x :=
    hu.mdifferentiable (by simp) x
  have h_grad_eq := gradFun_mul_pointwise (I := I) g (ρ := (ρ : M → ℝ)) (u := u)
    (x := x) hρ_diff hu_diff
  rw [h_grad_eq]
  set gu : TangentSpace I x :=
    CalabiYau.Riemannian.gradFun (I := I) g u x with hgu_def
  set gρ : TangentSpace I x :=
    CalabiYau.Riemannian.gradFun (I := I) g
      ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hgρ_def
  set a : TangentSpace I x := ((ρ : M → ℝ)) x • gu
  set b : TangentSpace I x := u x • gρ
  have ha_self_eq : g.inner x a a = ((ρ : M → ℝ) x)^2 * g.inner x gu gu := by
    change (g.inner x ((((ρ : M → ℝ) x)) • gu)) ((((ρ : M → ℝ) x)) • gu) =
      _ * g.inner x gu gu
    rw [(g.inner x).map_smul, smul_apply]
    rw [(g.inner x gu).map_smul]
    simp [smul_eq_mul, sq]
    ring
  have hb_self_eq : g.inner x b b = (u x)^2 * g.inner x gρ gρ := by
    change (g.inner x ((u x) • gρ)) ((u x) • gρ) =
      _ * g.inner x gρ gρ
    rw [(g.inner x).map_smul, smul_apply]
    rw [(g.inner x gρ).map_smul]
    simp [smul_eq_mul, sq]
    ring
  have h_sym : g.inner x a b = g.inner x b a := g.symm x a b
  have h_inner_self_nn : ∀ z : TangentSpace I x, 0 ≤ g.inner x z z := by
    intro z
    by_cases hz : z = 0
    · rw [hz]
      change ((g.inner x) (0 : TangentSpace I x)) (0 : TangentSpace I x) ≥ 0
      rw [(g.inner x).map_zero]
      change (0 : TangentSpace I x →L[ℝ] ℝ) (0 : TangentSpace I x) ≥ 0
      simp
    · exact (g.pos x z hz).le
  have h_a_nn : 0 ≤ g.inner x a a := h_inner_self_nn _
  have h_b_nn : 0 ≤ g.inner x b b := h_inner_self_nn _
  have h_apb_nn : 0 ≤ g.inner x (a + b) (a + b) := h_inner_self_nn _
  have h_apb_eq : g.inner x (a + b) (a + b) =
      g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
    have h_step : g.inner x (a + b) (a + b) =
        g.inner x a (a + b) + g.inner x b (a + b) := by
      have h1 : (g.inner x) (a + b) = (g.inner x) a + (g.inner x) b :=
        (g.inner x).map_add a b
      change ((g.inner x) (a + b)) (a + b) = _
      rw [h1]
      rfl
    rw [h_step, (g.inner x a).map_add, (g.inner x b).map_add]
    rw [h_sym]
    ring
  have h_CS_ab := abs_g_inner_le_sqrt_mul_sqrt (I := I) g x a b
  have h_apb_le_sum_sq :
      g.inner x (a + b) (a + b) ≤
        (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b))^2 := by
    rw [h_apb_eq]
    have h_sqrt_a_sq : Real.sqrt (g.inner x a a)^2 = g.inner x a a :=
      Real.sq_sqrt h_a_nn
    have h_sqrt_b_sq : Real.sqrt (g.inner x b b)^2 = g.inner x b b :=
      Real.sq_sqrt h_b_nn
    have h_2ab_le : 2 * g.inner x a b ≤
        2 * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)) := by
      have h_le_abs : g.inner x a b ≤ |g.inner x a b| := le_abs_self _
      linarith
    nlinarith only [h_2ab_le, h_sqrt_a_sq, h_sqrt_b_sq,
      Real.sqrt_nonneg (g.inner x a a), Real.sqrt_nonneg (g.inner x b b)]
  have h_sum_nn : 0 ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_sqrt_apb_le : Real.sqrt (g.inner x (a + b) (a + b)) ≤
      Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
    have h := Real.sqrt_le_sqrt h_apb_le_sum_sq
    rw [Real.sqrt_sq h_sum_nn] at h
    exact h
  refine h_sqrt_apb_le.trans ?_
  have h_sqrt_a : Real.sqrt (g.inner x a a) =
      |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) := by
    rw [ha_self_eq]
    have hgu_nn : 0 ≤ g.inner x gu gu := h_inner_self_nn _
    rw [Real.sqrt_mul (sq_nonneg _)]
    rw [Real.sqrt_sq_eq_abs]
  have h_sqrt_b : Real.sqrt (g.inner x b b) =
      |u x| * Real.sqrt (g.inner x gρ gρ) := by
    rw [hb_self_eq]
    have hgρ_nn : 0 ≤ g.inner x gρ gρ := h_inner_self_nn _
    rw [Real.sqrt_mul (sq_nonneg _)]
    rw [Real.sqrt_sq_eq_abs]
  rw [h_sqrt_a, h_sqrt_b]
  have hρ_abs : |((ρ : M → ℝ)) x| ≤ 1 := abs_chartAtlasPOU_le_one (I := I) (M := M) α x
  have hsqrt_gu_nn : 0 ≤ Real.sqrt (g.inner x gu gu) := Real.sqrt_nonneg _
  have hsqrt_gρ_nn : 0 ≤ Real.sqrt (g.inner x gρ gρ) := Real.sqrt_nonneg _
  have h_term1 : |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) ≤
      Real.sqrt (g.inner x gu gu) := by
    calc |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu)
        ≤ 1 * Real.sqrt (g.inner x gu gu) :=
          mul_le_mul_of_nonneg_right hρ_abs hsqrt_gu_nn
      _ = Real.sqrt (g.inner x gu gu) := one_mul _
  have h_term2 : |u x| * Real.sqrt (g.inner x gρ gρ) ≤
      |u x| * K_grad_ρ := by
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact hK_grad_ρ x
  have hM := le_max_left (1 : ℝ) K_grad_ρ
  have hM' := le_max_right (1 : ℝ) K_grad_ρ
  set K := max (1 : ℝ) K_grad_ρ
  have hK_nn : 0 ≤ K := le_trans zero_le_one hM
  have h_step1 : Real.sqrt (g.inner x gu gu) ≤ K * Real.sqrt (g.inner x gu gu) := by
    have := mul_le_mul_of_nonneg_right hM hsqrt_gu_nn
    linarith
  have h_step2 : K_grad_ρ * |u x| ≤ K * |u x| :=
    mul_le_mul_of_nonneg_right hM' (abs_nonneg _)
  calc |((ρ : M → ℝ)) x| * Real.sqrt (g.inner x gu gu) +
        |u x| * Real.sqrt (g.inner x gρ gρ)
      ≤ Real.sqrt (g.inner x gu gu) + |u x| * K_grad_ρ :=
        add_le_add h_term1 h_term2
    _ = Real.sqrt (g.inner x gu gu) + K_grad_ρ * |u x| := by ring
    _ ≤ K * Real.sqrt (g.inner x gu gu) + K * |u x| :=
        add_le_add h_step1 h_step2
    _ = K * (|u x| + Real.sqrt (g.inner x gu gu)) := by ring

end EquivalenceReverse
end Sobolev
