-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Operator/VariationalLaplacian.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Operator.SmoothResolvent
public import CalabiYau.Analysis.Elliptic.Operator.SmoothDenseLp

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

theorem resolvent_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (resolvent (I := I) (M := M) g) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h_orth : ∀ v : H1Compl g,
      ⟪h1ComplToLp (I := I) (M := M) g v, f⟫_ℝ = 0 := by
    intro v
    have h := resolvent_inner_eq_lpFunctional (I := I) (M := M) g f v
    rw [hf] at h
    rw [inner_zero_left] at h
    linarith
  have h_dense : DenseRange (h1ComplToLp (I := I) (M := M) g) :=
    denseRange_H1ComplToLp (I := I) (M := M) g
  have h_inner_zero : ∀ w : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
      (innerSL ℝ f) w = 0 := by
    intro w
    have h_eq_on_range :
        (fun y : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) =>
            (innerSL ℝ f) y) ∘ (h1ComplToLp (I := I) (M := M) g) =
        (fun _ : H1Compl g => (0 : ℝ)) := by
      funext v
      change ⟪f, h1ComplToLp (I := I) (M := M) g v⟫_ℝ = 0
      rw [real_inner_comm]
      exact h_orth v
    have h_func_eq :
        (fun y : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) =>
            (innerSL ℝ f) y) =
        (fun _ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) => (0 : ℝ)) :=
      h_dense.equalizer (innerSL ℝ f).continuous continuous_const h_eq_on_range
    have := congrFun h_func_eq w
    exact this
  have h_self : ⟪f, f⟫_ℝ = 0 := by
    have := h_inner_zero f
    rwa [innerSL_apply_apply] at this
  rw [real_inner_self_eq_norm_sq] at h_self
  have h_norm_zero : ‖f‖ = 0 := by
    have h_pow_zero : ‖f‖ ^ 2 = 0 := h_self
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h_pow_zero
  exact norm_eq_zero.mp h_norm_zero

def laplacianDomain (g : SmoothRiemannianMetric I M) :
    Submodule ℝ (H1Compl g) :=
  LinearMap.range (resolvent (I := I) (M := M) g).toLinearMap

lemma laplacianDomain_mem_iff (g : SmoothRiemannianMetric I M) {u : H1Compl g} :
    u ∈ laplacianDomain (I := I) (M := M) g ↔
      ∃ f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
        u = resolvent (I := I) (M := M) g f := by
  unfold laplacianDomain
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩

def laplacianDomain.preimage (g : SmoothRiemannianMetric I M)
    (u : laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  Classical.choose ((laplacianDomain_mem_iff (I := I) (M := M) g).mp u.2)

@[simp] lemma resolvent_laplacianDomain_preimage_eq
    (g : SmoothRiemannianMetric I M)
    (u : laplacianDomain (I := I) (M := M) g) :
    resolvent (I := I) (M := M) g
        (laplacianDomain.preimage (I := I) (M := M) g u) =
      (u : H1Compl g) :=
  (Classical.choose_spec ((laplacianDomain_mem_iff (I := I) (M := M) g).mp u.2)).symm

lemma laplacianDomain_preimage_add (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g (u + v) =
      laplacianDomain.preimage (I := I) (M := M) g u +
      laplacianDomain.preimage (I := I) (M := M) g v := by
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  rw [(resolvent (I := I) (M := M) g).map_add]
  rw [resolvent_laplacianDomain_preimage_eq, resolvent_laplacianDomain_preimage_eq]
  rfl

lemma laplacianDomain_preimage_smul (g : SmoothRiemannianMetric I M)
    (c : ℝ) (u : laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g (c • u) =
      c • laplacianDomain.preimage (I := I) (M := M) g u := by
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  rw [(resolvent (I := I) (M := M) g).map_smul]
  rw [resolvent_laplacianDomain_preimage_eq]
  rfl

def laplacianDomain.preimageLin (g : SmoothRiemannianMetric I M) :
    laplacianDomain (I := I) (M := M) g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) where
  toFun := laplacianDomain.preimage (I := I) (M := M) g
  map_add' := laplacianDomain_preimage_add (I := I) (M := M) g
  map_smul' c u := laplacianDomain_preimage_smul (I := I) (M := M) g c u

def laplacianOp (g : SmoothRiemannianMetric I M) :
    laplacianDomain (I := I) (M := M) g →ₗ[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ((h1ComplToLp (I := I) (M := M) g).toLinearMap.comp
    (laplacianDomain (I := I) (M := M) g).subtype) -
  laplacianDomain.preimageLin (I := I) (M := M) g

@[simp] lemma laplacianOp_apply (g : SmoothRiemannianMetric I M)
    (u : laplacianDomain (I := I) (M := M) g) :
    laplacianOp (I := I) (M := M) g u =
      h1ComplToLp (I := I) (M := M) g (u : H1Compl g) -
        laplacianDomain.preimage (I := I) (M := M) g u := by
  unfold laplacianOp
  rw [LinearMap.sub_apply]
  rfl

theorem laplacianOp_resolvent (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    laplacianOp (I := I) (M := M) g
        ⟨resolvent (I := I) (M := M) g f,
          (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨f, rfl⟩⟩ =
      h1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g f) - f := by
  rw [laplacianOp_apply]
  have h_preimage_eq :
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨resolvent (I := I) (M := M) g f,
            (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨f, rfl⟩⟩ = f := by
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
  rw [h_preimage_eq]

lemma smoothToH1Compl_mem_laplacianDomain
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    smoothToH1Compl (I := I) (M := M) g u ∈
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomain_mem_iff]
  refine ⟨smoothToLp (I := I) (M := M) g u.oneSubLapClassical, ?_⟩
  exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u

theorem laplacianOp_smoothToH1Compl
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    laplacianOp (I := I) (M := M) g
        ⟨smoothToH1Compl (I := I) (M := M) g u,
          smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u⟩ =
      smoothToLp (I := I) (M := M) g u -
        smoothToLp (I := I) (M := M) g u.oneSubLapClassical := by
  rw [show (⟨smoothToH1Compl (I := I) (M := M) g u,
        smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u⟩ :
        laplacianDomain (I := I) (M := M) g) =
      ⟨resolvent (I := I) (M := M) g
        (smoothToLp (I := I) (M := M) g u.oneSubLapClassical),
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
          ⟨smoothToLp (I := I) (M := M) g u.oneSubLapClassical, rfl⟩⟩ from ?_]
  · rw [laplacianOp_resolvent]
    have h_eq : resolvent (I := I) (M := M) g
          (smoothToLp (I := I) (M := M) g u.oneSubLapClassical) =
        smoothToH1Compl (I := I) (M := M) g u :=
      (smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u).symm
    rw [h_eq, h1ComplToLp_smoothToH1Compl]
  · apply Subtype.ext
    exact smoothToH1Compl_eq_resolvent_oneSubLap (I := I) (M := M) u

theorem laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian
    {g : SmoothRiemannianMetric I M} (u : SmoothScalar g) :
    laplacianOp (I := I) (M := M) g
        ⟨smoothToH1Compl (I := I) (M := M) g u,
          smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u⟩ =
      smoothToLp (I := I) (M := M) g u.laplacian := by
  rw [laplacianOp_smoothToH1Compl]
  rw [← map_sub, SmoothScalar.sub_oneSubLapClassical]

private lemma h1Inner_eq_lpInner_with_preimage
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪(u : H1Compl g), (v : H1Compl g)⟫_ℝ =
      ⟪h1ComplToLp (I := I) (M := M) g (v : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g u⟫_ℝ := by
  have h_u_eq : (u : H1Compl g) = resolvent (I := I) (M := M) g
      (laplacianDomain.preimage (I := I) (M := M) g u) :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g u).symm
  rw [h_u_eq]
  exact resolvent_inner_eq_lpFunctional (I := I) (M := M) g
    (laplacianDomain.preimage (I := I) (M := M) g u) (v : H1Compl g)

private lemma lpInner_preimage_swap
    (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪h1ComplToLp (I := I) (M := M) g (v : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g u⟫_ℝ =
      ⟪h1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianDomain.preimage (I := I) (M := M) g v⟫_ℝ := by
  rw [← h1Inner_eq_lpInner_with_preimage (I := I) (M := M) g u v]
  rw [← h1Inner_eq_lpInner_with_preimage (I := I) (M := M) g v u]
  exact real_inner_comm _ _

theorem laplacianOp_symmetric (g : SmoothRiemannianMetric I M)
    (u v : laplacianDomain (I := I) (M := M) g) :
    ⟪h1ComplToLp (I := I) (M := M) g (u : H1Compl g),
        laplacianOp (I := I) (M := M) g v⟫_ℝ =
      ⟪laplacianOp (I := I) (M := M) g u,
        h1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ := by
  rw [laplacianOp_apply, laplacianOp_apply]
  rw [inner_sub_right, inner_sub_left]
  have h_swap := lpInner_preimage_swap (I := I) (M := M) g v u
  have h_swap_inner :
      ⟪h1ComplToLp (I := I) (M := M) g (u : H1Compl g),
          laplacianDomain.preimage (I := I) (M := M) g v⟫_ℝ =
        ⟪laplacianDomain.preimage (I := I) (M := M) g u,
          h1ComplToLp (I := I) (M := M) g (v : H1Compl g)⟫_ℝ := by
    rw [h_swap, real_inner_comm]
  linarith [h_swap_inner]

end Laplacian
end Analysis
end CalabiYau

end
