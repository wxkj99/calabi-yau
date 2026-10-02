-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/H1Compl/Intrinsic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Intrinsic.Lp.H1
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open Sobolev.IntrinsicLp
open Sobolev.IntrinsicH1Lp

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma g_inner_zero_left
    (g : SmoothRiemannianMetric I M) (x : M) (y : TangentSpace I x) :
    g.inner x (0 : TangentSpace I x) y = 0 := by
  rw [map_zero, zero_apply]

private lemma g_inner_add_left
    (g : SmoothRiemannianMetric I M) (x : M) (v w y : TangentSpace I x) :
    g.inner x (v + w) y = g.inner x v y + g.inner x w y := by
  rw [map_add (g.inner x), add_apply]

private lemma g_inner_add_right
    (g : SmoothRiemannianMetric I M) (x : M) (v y w : TangentSpace I x) :
    g.inner x v (y + w) = g.inner x v y + g.inner x v w :=
  ContinuousLinearMap.map_add (g.inner x v) y w

private lemma g_inner_smul_left
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v y : TangentSpace I x) :
    g.inner x (c • v) y = c * g.inner x v y := by
  rw [map_smul (g.inner x), smul_apply, smul_eq_mul]

private lemma g_inner_smul_right
    (g : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) (c : ℝ)
    (y : TangentSpace I x) :
    g.inner x v (c • y) = c * g.inner x v y := by
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

private lemma g_inner_add_diag
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    g.inner x (v + w) (v + w) =
      g.inner x v v + 2 * g.inner x v w + g.inner x w w := by
  rw [g_inner_add_left g x v w (v + w),
    g_inner_add_right g x v v w, g_inner_add_right g x w v w]
  have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
  rw [hsymm]; ring

private lemma g_norm_triangle
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    Real.sqrt (g.inner x (v + w) (v + w)) ≤
      Real.sqrt (g.inner x v v) + Real.sqrt (g.inner x w w) := by
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · simp [a, hv0]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · simp [b, hw0]
    · exact (g.pos x w hw0).le
  have hCS_sq : c ^ 2 ≤ a * b := by
    have hquad : ∀ t : ℝ, 0 ≤ t * t * a + 2 * t * c + b := by
      intro t
      have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
        rcases eq_or_ne (t • v + w) 0 with hz | hnz
        · rw [hz]; exact le_of_eq (g_inner_zero_left g x _).symm
        · exact (g.pos x _ hnz).le
      have h_expand : g.inner x (t • v + w) (t • v + w) =
          t * t * a + 2 * t * c + b := by
        rw [g_inner_add_left g x (t • v) w (t • v + w),
            g_inner_add_right g x (t • v) (t • v) w,
            g_inner_add_right g x w (t • v) w,
            g_inner_smul_left g x t v (t • v),
            g_inner_smul_left g x t v w,
            g_inner_smul_right g x v t v,
            g_inner_smul_right g x w t v]
        have hsymm : g.inner x w v = g.inner x v w := g.symm x w v
        rw [hsymm]; ring
      rw [h_expand] at hpos
      exact hpos
    rcases lt_or_eq_of_le ha_nn with ha_pos | ha_zero
    · have hroot := hquad (-c / a)
      have hsimp : -c / a * (-c / a) * a + 2 * (-c / a) * c + b = b - c^2 / a := by
        field_simp; ring
      rw [hsimp] at hroot
      have hcsa : c ^ 2 / a ≤ b := by linarith
      have h1 : c ^ 2 = a * (c ^ 2 / a) := by field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_left hcsa ha_nn
    · have ha_eq : a = 0 := ha_zero.symm
      have hv_zero : v = 0 := by
        by_contra hne
        have hpos : 0 < g.inner x v v := g.pos x v hne
        rw [show g.inner x v v = a from rfl, ha_eq] at hpos
        exact lt_irrefl 0 hpos
      have hc_eq : c = 0 := by
        change g.inner x v w = 0
        rw [hv_zero]; exact g_inner_zero_left g x w
      rw [hc_eq, ha_eq]; simp
  have hsqrt_mul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b :=
    Real.sqrt_mul ha_nn b
  have hC : |c| ≤ Real.sqrt a * Real.sqrt b := by
    rw [← Real.sqrt_sq_eq_abs, ← hsqrt_mul]
    exact Real.sqrt_le_sqrt hCS_sq
  have hc_le : c ≤ Real.sqrt a * Real.sqrt b := (le_abs_self c).trans hC
  have h_expand : g.inner x (v + w) (v + w) = a + 2 * c + b :=
    g_inner_add_diag g x v w
  rw [h_expand]
  have h_le_sq : a + 2 * c + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have h_sq_expand : (Real.sqrt a + Real.sqrt b) ^ 2 =
        a + 2 * (Real.sqrt a * Real.sqrt b) + b := by
      have ha_sq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha_nn
      have hb_sq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb_nn
      nlinarith [ha_sq, hb_sq]
    rw [h_sq_expand]; linarith
  have h_nn : 0 ≤ Real.sqrt a + Real.sqrt b :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_sqrt_le := Real.sqrt_le_sqrt h_le_sq
  rw [show Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) = Real.sqrt a + Real.sqrt b
      from Real.sqrt_sq h_nn] at h_sqrt_le
  exact h_sqrt_le

private lemma g_norm_const_smul
    (g : SmoothRiemannianMetric I M) (x : M) (c : ℝ) (v : TangentSpace I x) :
    Real.sqrt (g.inner x (c • v) (c • v)) =
      |c| * Real.sqrt (g.inner x v v) := by
  rw [g_inner_smul_left g x c v (c • v), g_inner_smul_right g x v c v]
  rw [show c * (c * g.inner x v v) = c ^ 2 * g.inner x v v from by ring]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev H1Bundle [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) : Type _ :=
  WithLp 2 ((Lp ℝ 2 (riemannianVolumeMeasure I M g)) ×
    (Lp E 2 (riemannianVolumeMeasure I M g)))

def IsH1Pair [T2Space M] [SigmaCompactSpace M] (g : SmoothRiemannianMetric I M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure I M g))
    (G : Lp E 2 (riemannianVolumeMeasure I M g)) : Prop :=
  HasWeakRiemannianGradLp (I := I) (M := M) g
    (fun x : M => (u : M → ℝ) x) (fun x : M => (G : M → E) x) ∧
  MemLp (fun x : M => Real.sqrt (g.inner x ((G : M → E) x) ((G : M → E) x))) 2
    (riemannianVolumeMeasure I M g) ∧
  PairAEMeasurable (I := I) (M := M) g (fun x : M => (G : M → E) x)

namespace IsH1Pair

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

theorem zero (g : SmoothRiemannianMetric I M) :
    IsH1Pair (I := I) (M := M) g
      (0 : Lp ℝ 2 (riemannianVolumeMeasure I M g))
      (0 : Lp E 2 (riemannianVolumeMeasure I M g)) := by
  refine ⟨?_, ?_, ?_⟩
  · have h0u : (fun x : M => ((0 : Lp ℝ 2 (riemannianVolumeMeasure I M g)) : M → ℝ) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : ℝ)) := by
      have h := Lp.coeFn_zero (E := ℝ) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))
      filter_upwards [h] with x hx
      exact hx
    have h0G : (fun x : M => ((0 : Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : E)) := by
      have h := Lp.coeFn_zero (E := E) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))
      filter_upwards [h] with x hx
      exact hx
    exact hasWeakRiemannianGradLp_congr_ae (I := I) (M := M) (g := g)
      h0u.symm h0G.symm (HasWeakRiemannianGradLp.zero (I := I) (M := M) g)
  · have h0G : (fun x : M => ((0 : Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : E)) := by
      have h := Lp.coeFn_zero (E := E) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))
      filter_upwards [h] with x hx
      exact hx
    refine memLp_g_norm_congr_ae (I := I) (M := M) (g := g) (p := 2) h0G.symm ?_
    have hcongr : (fun x : M => Real.sqrt
          (g.inner x ((fun _ : M => (0 : E)) x) ((fun _ : M => (0 : E)) x))) =
        (fun _ : M => (0 : ℝ)) := by
      funext x
      change Real.sqrt (g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x)) = 0
      have hg0 : g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 := by
        simp
      rw [hg0]; exact Real.sqrt_zero
    rw [hcongr]
    exact MemLp.zero
  · have h0G : (fun x : M => ((0 : Lp E 2 (riemannianVolumeMeasure I M g)) : M → E) x)
        =ᵐ[riemannianVolumeMeasure I M g] (fun _ : M => (0 : E)) := by
      have h := Lp.coeFn_zero (E := E) (μ := riemannianVolumeMeasure I M g)
        (p := (2 : ℝ≥0∞))
      filter_upwards [h] with x hx
      exact hx
    exact PairAEMeasurable.congr_ae (I := I) (M := M) (g := g) h0G.symm
      (PairAEMeasurable.zero (I := I) (M := M) g)

theorem add (g : SmoothRiemannianMetric I M)
    {u v : Lp ℝ 2 (riemannianVolumeMeasure I M g)}
    {G G' : Lp E 2 (riemannianVolumeMeasure I M g)}
    (hu : IsH1Pair (I := I) (M := M) g u G)
    (hv : IsH1Pair (I := I) (M := M) g v G') :
    IsH1Pair (I := I) (M := M) g (u + v) (G + G') := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  obtain ⟨hG_weak, hG_p, hG_pair⟩ := hu
  obtain ⟨hG'_weak, hG'_p, hG'_pair⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · have h_sum_G : (fun x : M => ((G + G' : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => (G : M → E) x + (G' : M → E) x) := by
      filter_upwards [Lp.coeFn_add G G'] with x hx; exact hx
    have h_sum_u : (fun x : M => ((u + v : Lp ℝ 2 (riemannianVolumeMeasure I M g)) :
          M → ℝ) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => (u : M → ℝ) x + (v : M → ℝ) x) := by
      filter_upwards [Lp.coeFn_add u v] with x hx; exact hx
    have h_add : HasWeakRiemannianGradLp (I := I) (M := M) g
        (fun x : M => (u : M → ℝ) x + (v : M → ℝ) x)
        (fun x : M => (G : M → E) x + (G' : M → E) x) :=
      HasWeakRiemannianGradLp.add (I := I) (M := M) (p := 2) (by norm_num)
        hG_weak hG'_weak (Lp.memLp u) (Lp.memLp v) hG_p hG'_p
    exact hasWeakRiemannianGradLp_congr_ae (I := I) (M := M) (g := g)
      h_sum_u.symm h_sum_G.symm h_add
  · have h_sum_G : (fun x : M => ((G + G' : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => (G : M → E) x + (G' : M → E) x) := by
      filter_upwards [Lp.coeFn_add G G'] with x hx; exact hx
    refine memLp_g_norm_congr_ae (I := I) (M := M) (g := g) (p := 2) h_sum_G.symm ?_
    have hAESM : AEStronglyMeasurable
        (fun x : M => Real.sqrt
          (g.inner x ((fun y : M => (G : M → E) y + (G' : M → E) y) x)
            ((fun y : M => (G : M → E) y + (G' : M → E) y) x)))
        (riemannianVolumeMeasure I M g) := by
      have hGG : AEStronglyMeasurable
          (fun x : M => g.inner x ((G : M → E) x) ((G : M → E) x))
          (riemannianVolumeMeasure I M g) :=
        hG_pair (fun x : M => (G : M → E) x) (Lp.aestronglyMeasurable G)
      have hGG' : AEStronglyMeasurable
          (fun x : M => g.inner x ((G : M → E) x) ((G' : M → E) x))
          (riemannianVolumeMeasure I M g) :=
        hG_pair (fun x : M => (G' : M → E) x) (Lp.aestronglyMeasurable G')
      have hG'G' : AEStronglyMeasurable
          (fun x : M => g.inner x ((G' : M → E) x) ((G' : M → E) x))
          (riemannianVolumeMeasure I M g) :=
        hG'_pair (fun x : M => (G' : M → E) x) (Lp.aestronglyMeasurable G')
      have hG'G : AEStronglyMeasurable
          (fun x : M => g.inner x ((G' : M → E) x) ((G : M → E) x))
          (riemannianVolumeMeasure I M g) := by
        have hcong2 : (fun x : M => g.inner x ((G' : M → E) x) ((G : M → E) x)) =
            (fun x : M => g.inner x ((G : M → E) x) ((G' : M → E) x)) := by
          funext x
          exact g.symm x ((G' : M → E) x) ((G : M → E) x)
        rw [hcong2]; exact hGG'
      have hsum_aem : AEStronglyMeasurable
          (fun x : M => g.inner x ((G : M → E) x + (G' : M → E) x)
            ((G : M → E) x + (G' : M → E) x))
          (riemannianVolumeMeasure I M g) := by
        have hpt : ∀ x : M,
            g.inner x ((G : M → E) x + (G' : M → E) x)
              ((G : M → E) x + (G' : M → E) x) =
            g.inner x ((G : M → E) x) ((G : M → E) x) +
              (g.inner x ((G : M → E) x) ((G' : M → E) x) +
              (g.inner x ((G' : M → E) x) ((G : M → E) x) +
              g.inner x ((G' : M → E) x) ((G' : M → E) x))) := by
          intro x
          calc g.inner x ((G : M → E) x + (G' : M → E) x)
                  ((G : M → E) x + (G' : M → E) x)
              = g.inner x ((G : M → E) x) ((G : M → E) x + (G' : M → E) x) +
                g.inner x ((G' : M → E) x) ((G : M → E) x + (G' : M → E) x) :=
                g_inner_add_left g x ((G : M → E) x) ((G' : M → E) x)
                  ((G : M → E) x + (G' : M → E) x)
            _ = (g.inner x ((G : M → E) x) ((G : M → E) x) +
                  g.inner x ((G : M → E) x) ((G' : M → E) x)) +
                (g.inner x ((G' : M → E) x) ((G : M → E) x) +
                  g.inner x ((G' : M → E) x) ((G' : M → E) x)) := by
                congr 1
                · exact g_inner_add_right g x ((G : M → E) x)
                    ((G : M → E) x) ((G' : M → E) x)
                · exact g_inner_add_right g x ((G' : M → E) x)
                    ((G : M → E) x) ((G' : M → E) x)
            _ = g.inner x ((G : M → E) x) ((G : M → E) x) +
                  (g.inner x ((G : M → E) x) ((G' : M → E) x) +
                  (g.inner x ((G' : M → E) x) ((G : M → E) x) +
                  g.inner x ((G' : M → E) x) ((G' : M → E) x))) := by ring
        have hcong : (fun x : M => g.inner x ((G : M → E) x + (G' : M → E) x)
              ((G : M → E) x + (G' : M → E) x)) =
            (fun x : M => g.inner x ((G : M → E) x) ((G : M → E) x) +
              (g.inner x ((G : M → E) x) ((G' : M → E) x) +
              (g.inner x ((G' : M → E) x) ((G : M → E) x) +
              g.inner x ((G' : M → E) x) ((G' : M → E) x)))) := by
          funext x; exact hpt x
        rw [hcong]
        exact hGG.add (hGG'.add (hG'G.add hG'G'))
      exact Real.continuous_sqrt.comp_aestronglyMeasurable hsum_aem
    refine MemLp.of_le (g := fun x : M =>
        Real.sqrt (g.inner x ((G : M → E) x) ((G : M → E) x)) +
          Real.sqrt (g.inner x ((G' : M → E) x) ((G' : M → E) x)))
      (hG_p.add hG'_p) hAESM ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h_tri := g_norm_triangle (I := I) (M := M) g x
      ((G : M → E) x) ((G' : M → E) x)
    have hLHS_nn : 0 ≤ Real.sqrt
        (g.inner x ((fun y : M => (G : M → E) y + (G' : M → E) y) x)
          ((fun y : M => (G : M → E) y + (G' : M → E) y) x)) :=
      Real.sqrt_nonneg _
    have hRHS_nn : 0 ≤ Real.sqrt (g.inner x ((G : M → E) x) ((G : M → E) x)) +
        Real.sqrt (g.inner x ((G' : M → E) x) ((G' : M → E) x)) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs (Real.sqrt _),
      Real.norm_eq_abs (Real.sqrt _ + Real.sqrt _),
      abs_of_nonneg hLHS_nn, abs_of_nonneg hRHS_nn]
    exact h_tri
  · have h_sum_G : (fun x : M => ((G + G' : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => (G : M → E) x + (G' : M → E) x) := by
      filter_upwards [Lp.coeFn_add G G'] with x hx; exact hx
    have hsum_pair : PairAEMeasurable (I := I) (M := M) g
        (fun x : M => (G : M → E) x + (G' : M → E) x) :=
      PairAEMeasurable.add (I := I) (M := M) (g := g) hG_pair hG'_pair
    exact PairAEMeasurable.congr_ae (I := I) (M := M) (g := g) h_sum_G.symm hsum_pair

theorem const_smul (g : SmoothRiemannianMetric I M) (c : ℝ)
    {u : Lp ℝ 2 (riemannianVolumeMeasure I M g)}
    {G : Lp E 2 (riemannianVolumeMeasure I M g)}
    (hu : IsH1Pair (I := I) (M := M) g u G) :
    IsH1Pair (I := I) (M := M) g (c • u) (c • G) := by
  have : IsFiniteMeasure (riemannianVolumeMeasure I M g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  obtain ⟨hG_weak, hG_p, hG_pair⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · have h_smul_G : (fun x : M => ((c • G : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c • (G : M → E) x) := by
      filter_upwards [Lp.coeFn_smul c G] with x hx; exact hx
    have h_smul_u : (fun x : M => ((c • u : Lp ℝ 2 (riemannianVolumeMeasure I M g)) :
          M → ℝ) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c * (u : M → ℝ) x) := by
      filter_upwards [Lp.coeFn_smul c u] with x hx; simpa using hx
    have h_smul : HasWeakRiemannianGradLp (I := I) (M := M) g
        (fun x : M => c * (u : M → ℝ) x) (fun x : M => c • (G : M → E) x) :=
      HasWeakRiemannianGradLp.const_smul (I := I) (M := M) (p := 2) (by norm_num) c
        hG_weak (Lp.memLp u)
    exact hasWeakRiemannianGradLp_congr_ae (I := I) (M := M) (g := g)
      h_smul_u.symm h_smul_G.symm h_smul
  · have h_smul_G : (fun x : M => ((c • G : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c • (G : M → E) x) := by
      filter_upwards [Lp.coeFn_smul c G] with x hx; exact hx
    refine memLp_g_norm_congr_ae (I := I) (M := M) (g := g) (p := 2) h_smul_G.symm ?_
    have hpt : ∀ x : M, Real.sqrt (g.inner x (c • (G : M → E) x) (c • (G : M → E) x)) =
        |c| * Real.sqrt (g.inner x ((G : M → E) x) ((G : M → E) x)) := fun x =>
      g_norm_const_smul g x c ((G : M → E) x)
    have hcongr : (fun x : M => Real.sqrt
        (g.inner x ((fun y : M => c • (G : M → E) y) x)
          ((fun y : M => c • (G : M → E) y) x))) =
        (fun x : M => |c| * Real.sqrt (g.inner x ((G : M → E) x) ((G : M → E) x))) := by
      funext x; exact hpt x
    rw [hcongr]
    exact hG_p.const_mul (|c|)
  · have h_smul_G : (fun x : M => ((c • G : Lp E 2 (riemannianVolumeMeasure I M g)) :
          M → E) x) =ᵐ[riemannianVolumeMeasure I M g]
        (fun x : M => c • (G : M → E) x) := by
      filter_upwards [Lp.coeFn_smul c G] with x hx; exact hx
    have hsmul_pair : PairAEMeasurable (I := I) (M := M) g
        (fun x : M => c • (G : M → E) x) :=
      PairAEMeasurable.const_smul (I := I) (M := M) c hG_pair
    exact PairAEMeasurable.congr_ae (I := I) (M := M) (g := g) h_smul_G.symm hsmul_pair

end IsH1Pair

def h1IntrinsicSubmodule
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    Submodule ℝ (H1Bundle (I := I) (M := M) g) where
  carrier := { p : H1Bundle (I := I) (M := M) g |
    IsH1Pair (I := I) (M := M) g (WithLp.ofLp p).1 (WithLp.ofLp p).2 }
  add_mem' {p q} hp hq := by
    change IsH1Pair (I := I) (M := M) g (WithLp.ofLp (p + q)).1 (WithLp.ofLp (p + q)).2
    have hofLp_add : WithLp.ofLp (p + q) = WithLp.ofLp p + WithLp.ofLp q := by
      simp
    have h1 : (WithLp.ofLp (p + q)).1 = (WithLp.ofLp p).1 + (WithLp.ofLp q).1 := by
      rw [hofLp_add]; rfl
    have h2 : (WithLp.ofLp (p + q)).2 = (WithLp.ofLp p).2 + (WithLp.ofLp q).2 := by
      rw [hofLp_add]; rfl
    rw [h1, h2]
    exact IsH1Pair.add (I := I) (M := M) g hp hq
  zero_mem' := by
    change IsH1Pair (I := I) (M := M) g
      (WithLp.ofLp (0 : H1Bundle (I := I) (M := M) g)).1
      (WithLp.ofLp (0 : H1Bundle (I := I) (M := M) g)).2
    have hofLp_zero : WithLp.ofLp (0 : H1Bundle (I := I) (M := M) g) = 0 := by
      simp
    rw [hofLp_zero]
    exact IsH1Pair.zero (I := I) (M := M) g
  smul_mem' c p hp := by
    change IsH1Pair (I := I) (M := M) g (WithLp.ofLp (c • p)).1 (WithLp.ofLp (c • p)).2
    have hofLp_smul : WithLp.ofLp (c • p) = c • WithLp.ofLp p := by
      simp
    have h1 : (WithLp.ofLp (c • p)).1 = c • (WithLp.ofLp p).1 := by
      rw [hofLp_smul]; rfl
    have h2 : (WithLp.ofLp (c • p)).2 = c • (WithLp.ofLp p).2 := by
      rw [hofLp_smul]; rfl
    rw [h1, h2]
    exact IsH1Pair.const_smul (I := I) (M := M) g c hp

abbrev H1Intrinsic [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) : Type _ :=
  h1IntrinsicSubmodule (I := I) (M := M) g

namespace H1Intrinsic

variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

def toLp (g : SmoothRiemannianMetric I M) :
    H1Intrinsic (I := I) (M := M) g →ₗ[ℝ] Lp ℝ 2 (riemannianVolumeMeasure I M g) where
  toFun u := (WithLp.ofLp (u : H1Bundle (I := I) (M := M) g)).1
  map_add' u v := by
    change (WithLp.ofLp ((u + v : H1Intrinsic (I := I) (M := M) g) :
        H1Bundle (I := I) (M := M) g)).1 = _
    have h : (WithLp.ofLp ((u + v : H1Intrinsic (I := I) (M := M) g) :
          H1Bundle (I := I) (M := M) g)) =
        WithLp.ofLp ((u : H1Bundle (I := I) (M := M) g)) +
        WithLp.ofLp ((v : H1Bundle (I := I) (M := M) g)) := by
      simp
    rw [h]; rfl
  map_smul' c u := by
    change (WithLp.ofLp ((c • u : H1Intrinsic (I := I) (M := M) g) :
        H1Bundle (I := I) (M := M) g)).1 = _
    have h : (WithLp.ofLp ((c • u : H1Intrinsic (I := I) (M := M) g) :
          H1Bundle (I := I) (M := M) g)) =
        c • WithLp.ofLp ((u : H1Bundle (I := I) (M := M) g)) := by
      simp
    rw [h]; rfl

def gradL2 (g : SmoothRiemannianMetric I M) :
    H1Intrinsic (I := I) (M := M) g →ₗ[ℝ] Lp E 2 (riemannianVolumeMeasure I M g) where
  toFun u := (WithLp.ofLp (u : H1Bundle (I := I) (M := M) g)).2
  map_add' u v := by
    change (WithLp.ofLp ((u + v : H1Intrinsic (I := I) (M := M) g) :
        H1Bundle (I := I) (M := M) g)).2 = _
    have h : (WithLp.ofLp ((u + v : H1Intrinsic (I := I) (M := M) g) :
          H1Bundle (I := I) (M := M) g)) =
        WithLp.ofLp ((u : H1Bundle (I := I) (M := M) g)) +
        WithLp.ofLp ((v : H1Bundle (I := I) (M := M) g)) := by
      simp
    rw [h]; rfl
  map_smul' c u := by
    change (WithLp.ofLp ((c • u : H1Intrinsic (I := I) (M := M) g) :
        H1Bundle (I := I) (M := M) g)).2 = _
    have h : (WithLp.ofLp ((c • u : H1Intrinsic (I := I) (M := M) g) :
          H1Bundle (I := I) (M := M) g)) =
        c • WithLp.ofLp ((u : H1Bundle (I := I) (M := M) g)) := by
      simp
    rw [h]; rfl

@[simp] lemma toLp_apply (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    toLp (I := I) (M := M) g u =
      (WithLp.ofLp (u : H1Bundle (I := I) (M := M) g)).1 := rfl

@[simp] lemma gradL2_apply (g : SmoothRiemannianMetric I M)
    (u : H1Intrinsic (I := I) (M := M) g) :
    gradL2 (I := I) (M := M) g u =
      (WithLp.ofLp (u : H1Bundle (I := I) (M := M) g)).2 := rfl

end H1Intrinsic

end

end Laplacian
end Analysis
end CalabiYau

end
