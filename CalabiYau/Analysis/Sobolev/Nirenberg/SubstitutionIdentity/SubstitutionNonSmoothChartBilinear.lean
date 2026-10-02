-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Nirenberg/SubstitutionIdentity/SubstitutionNonSmoothChartBilinear.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.ChartBilinear.ZeroBoundaryHOne
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.SmoothRegularity
public import CalabiYau.Analysis.Sobolev.Nirenberg.TestFunction.WeakRegularity
public import CalabiYau.Analysis.Sobolev.Nirenberg.SubstitutionIdentity.SubstitutionNonSmooth

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal Pointwise

namespace CalabiYau
namespace Analysis
namespace Sobolev
namespace SubstitutionNonSmoothChartBilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.ChartLocalLaplacian
open CalabiYau.Laplacian.ChartMeasureEquiv
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open Sobolev.NirenbergTestFunction

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma nirenbergTestFunction_tsupport_in_thickening
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) {η : EuclN → ℝ}
    {K_0 : Set EuclN} (hη_support_in_K_0 : tsupport η ⊆ K_0)
    (u : EuclN → ℝ) :
    tsupport (nirenbergTestFunction k h η u) ⊆
      Metric.cthickening |h| K_0 := by
  classical
  have h_support := nirenbergTestFunction_tsupport_subset
    (d := Module.finrank ℝ E) (η := η) k h u
  refine h_support.trans ?_
  intro x hx
  rcases hx with hx_in | hx_trans
  · have hx_K_0 : x ∈ K_0 := hη_support_in_K_0 hx_in
    exact Metric.self_subset_cthickening _ hx_K_0
  · have hy_K_0 : x + (-h) • EuclideanSpace.single k 1 ∈ K_0 :=
      hη_support_in_K_0 hx_trans
    have h_dist : dist x (x + (-h) • EuclideanSpace.single k 1) ≤ |h| := by
      have h_norm_eq : dist x (x + (-h) • EuclideanSpace.single k 1) = |h| := by
        rw [dist_eq_norm]
        have h_step : x - (x + (-h) • EuclideanSpace.single k 1) =
            h • EuclideanSpace.single k 1 := by
          rw [sub_add_eq_sub_sub, sub_self, zero_sub, ← neg_smul, neg_neg]
        rw [h_step]
        rw [norm_smul]
        simp [Real.norm_eq_abs]
      rw [h_norm_eq]
    refine Metric.mem_cthickening_of_dist_le _ _ |h| K_0 hy_K_0 ?_
    exact h_dist

omit [NeZero (Module.finrank ℝ E)] in
lemma weightedInvGramOnEuclid_bounded_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E))
    {K : Set EuclN} (hK : IsCompact K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |weightedInvGramOnEuclid (I := I) g α i j y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_refl _, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have h_pull : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (weightedInvGramOnEuclid_contDiffOn (I := I) g α i j).continuousOn
  have h_pull_K : ContinuousOn (weightedInvGramOnEuclid (I := I) g α i j) K :=
    h_pull.mono hK_in
  have h_abs_K : ContinuousOn
      (fun y => |weightedInvGramOnEuclid (I := I) g α i j y|) K :=
    continuous_abs.comp_continuousOn h_pull_K
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  obtain ⟨y_max, _hy_max, h_max_eq⟩ := hK.exists_isMaxOn hKne h_abs_K
  refine ⟨|weightedInvGramOnEuclid (I := I) g α i j y_max|, abs_nonneg _, ?_⟩
  intro y hy
  exact h_max_eq hy

def principalTermChartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∫ x in K_0,
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        Sobolev.translate
          (d := Module.finrank ℝ E) k h
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) ^ 2 *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial i) x *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) x
    ∂(volume : Measure EuclN)

def cross1TermChartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∫ x in K_0,
        2 *
          Sobolev.translate
            (d := Module.finrank ℝ E) k h
            (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
          (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h (D.weakPartial i) x *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart x
        ∂(volume : Measure EuclN)

def cross2TermChartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∫ x in K_0,
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h
          (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
        (η x) ^ 2 *
        D.weakPartial i x *
        Sobolev.diffQuot
          (d := Module.finrank ℝ E) k h (D.weakPartial j) x
      ∂(volume : Measure EuclN)

def cross3TermChartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∫ x in K_0,
        2 *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h
            (fun y => weightedInvGramOnEuclid (I := I) g α i j y) x *
          (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          D.weakPartial i x *
          Sobolev.diffQuot
            (d := Module.finrank ℝ E) k h D.uChart x
        ∂(volume : Measure EuclN)

def cTermChartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∫ x in Metric.cthickening |h| K_0,
    densityOnEuclid (I := I) g α x * D.uChart x *
      nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η D.uChart x
  ∂(volume : Measure EuclN)

def fTermChartBilinear
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  ∫ x in Metric.cthickening |h| K_0,
    densityOnEuclid (I := I) g α x * D.fChart x *
      nirenbergTestFunction
        (d := Module.finrank ℝ E) k h η D.uChart x
  ∂(volume : Measure EuclN)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma cthickening_K_0_isCompact
    {K_0 : Set EuclN} (hK_0_compact : IsCompact K_0) {h : ℝ} :
    IsCompact (Metric.cthickening |h| K_0) := by
  classical
  have h_bdd : Bornology.IsBounded (Metric.cthickening |h| K_0) :=
    hK_0_compact.isBounded.cthickening
  have h_closed : IsClosed (Metric.cthickening |h| K_0) :=
    Metric.isClosed_cthickening
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨h_closed, h_bdd⟩

def chartBilinearLHS
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  principalTermChartBilinear (I := I) (M := M) D K_0 η k h
    + cross1TermChartBilinear (I := I) (M := M) D K_0 η k h
    + cross2TermChartBilinear (I := I) (M := M) D K_0 η k h
    + cross3TermChartBilinear (I := I) (M := M) D K_0 η k h
    + fTermChartBilinear (I := I) (M := M) D K_0 η k h

def chartBilinearRHS
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {α : M}
    (D : ChartBilinearH1ComplData (I := I) (M := M) g α)
    (K_0 : Set EuclN) (η : EuclN → ℝ)
    (k : Fin (Module.finrank ℝ E)) (h : ℝ) : ℝ :=
  cTermChartBilinear (I := I) (M := M) D K_0 η k h

end SubstitutionNonSmoothChartBilinear
end Sobolev
end Analysis
end CalabiYau
