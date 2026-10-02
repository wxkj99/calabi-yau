module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.CompactPotentialLaplacian

/-!
# Global bound for the mixed-potential error

In the differentiated Monge–Ampère equation the right-hand side contributes
the intrinsic reference Laplacian of `G`. The local estimates bound its mixed
Wirtinger derivatives on each fixed compact chart piece and contract them
against the inverse fixed reference metric. Finite compact chart pieces then
cover the manifold, giving a uniform global bound without asserting any
uniform scale for the point-selected charts. There is no curvature claim.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
Lemma 3.10, pp. 45–46. Each Wirtinger derivative has the factor `1/2`
from `TraceHessian`, so the mixed derivative has factor `1/4` relative to
the corresponding real two-plane Laplacian.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

omit [T2Space M] in
/-- The invariant reference Laplacian of a uniformly chartwise C³ family is
uniformly bounded on a compact manifold. Unlike raw derivatives in the
point-selected chart, this intrinsic scalar can be controlled using a finite
cover by fixed compact chart pieces and the local mixed-derivative estimate
in `MixedPotentialDerivative`; no uniform chart radius or chart scale at every
`x` is asserted. -/
theorem exists_uniform_c3RefinedTrace_referencePotentialLaplacian_bound
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ S, ∀ x : M, |ω₀.laplacian p.1 x| ≤ A := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let e (x : M) := extChartAt I x
  let c (x : M) := e x x
  have hr (x : M) : ∃ r : ℝ, 0 < r ∧ Metric.ball (c x) r ⊆ (e x).target :=
    Metric.isOpen_iff.mp (isOpen_extChartAt_target x) (c x) (mem_extChartAt_target x)
  let r (x : M) : ℝ := Classical.choose (hr x)
  have hrpos (x : M) : 0 < r x := (Classical.choose_spec (hr x)).1
  have hrball (x : M) : Metric.ball (c x) (r x) ⊆ (e x).target :=
    (Classical.choose_spec (hr x)).2
  let K (x : M) : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall (c x) (r x / 2)
  let V (x : M) : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball (c x) (r x / 2)
  have hKcompact (x : M) : IsCompact (K x) := isCompact_closedBall _ _
  have hVopen (x : M) : IsOpen (V x) := Metric.isOpen_ball
  have hVK (x : M) : V x ⊆ K x := Metric.ball_subset_closedBall
  have hKt (x : M) : K x ⊆ (e x).target := by
    intro z hz
    apply hrball x
    have hz' : dist (c x) z ≤ r x / 2 := by
      simpa [K, dist_comm, Metric.mem_closedBall] using hz
    rw [Metric.mem_ball]
    rw [dist_comm] at hz'
    linarith [hrpos x]
  have hUopen (x : M) : IsOpen ((e x).source ∩ (e x) ⁻¹' V x) := by
    rw [extChartAt_source (I := I) x]
    exact isOpen_extChartAt_preimage (H := EuclideanSpace ℂ (Fin n))
      (I := I) x (hVopen x)
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M,
      (e x).source ∩ (e x) ⁻¹' V x := by
    intro y _
    refine Set.mem_iUnion.2 ⟨y, ?_⟩
    constructor
    · exact mem_extChartAt_source y
    · change e y y ∈ V y
      rw [Metric.mem_ball]
      simp [c, dist_self, hrpos]
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (e x).source ∩ (e x) ⁻¹' V x) hUopen hcover
  have hLocal (x : M) : ∃ A : ℝ, 0 ≤ A ∧ ∀ p ∈ S, ∀ z ∈ K x,
      |ω₀.laplacian p.1 ((e x).symm z)| ≤ A := by
    have hMixed := exists_uniform_c3RefinedTrace_mixedPotentialDerivative_bound
      S hS hG x (K x) (hKcompact x) (hKt x)
    exact exists_uniform_c3RefinedTrace_compactChartPotentialLaplacian_bound
      ω₀ S hS x (K x) (hKcompact x) (hKt x) hMixed
  let bound (x : M) : ℝ := Classical.choose (hLocal x)
  have hbound (x : M) : 0 ≤ bound x ∧ ∀ p ∈ S, ∀ z ∈ K x,
      |ω₀.laplacian p.1 ((e x).symm z)| ≤ bound x :=
    Classical.choose_spec (hLocal x)
  refine ⟨∑ x ∈ t, bound x, Finset.sum_nonneg (fun x hx => (hbound x).1), ?_⟩
  intro p hp y
  have hy := ht (Set.mem_univ y)
  rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
  have hyK : e x y ∈ K x := hVK x hyx.2
  have hxy : (e x).symm (e x y) = y := (e x).left_inv hyx.1
  calc
    |ω₀.laplacian p.1 y| = |ω₀.laplacian p.1 ((e x).symm (e x y))| := by rw [hxy]
    _ ≤ bound x := (hbound x).2 p hp (e x y) hyK
    _ ≤ ∑ z ∈ t, bound z := Finset.single_le_sum (fun z hz => (hbound z).1) hx

end KahlerForm
