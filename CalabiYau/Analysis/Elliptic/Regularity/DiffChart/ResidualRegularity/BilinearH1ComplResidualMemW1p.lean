-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/DiffChart/ResidualRegularity/BilinearH1ComplResidualMemW1p.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
public import CalabiYau.Analysis.Elliptic.Regularity.GradInner.CLM.Leibniz
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.LocalRegularity
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.H1Completion
public import CalabiYau.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul
public import CalabiYau.Analysis.Elliptic.Regularity.Iterated.Defs
public import CalabiYau.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
public import CalabiYau.Analysis.Elliptic.MetricExtension
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Smooth
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import CalabiYau.Geometry.Riemannian.Metric.Basic
public import CalabiYau.Geometry.Manifold.Bundle.Section
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.VossWeylFormula
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.Real
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Field
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Algebra.Contraction
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Fiber
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Defs
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Composition
public import CalabiYau.Mathlib.Analysis.Normed.Module.Multilinear.Composition
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
public import CalabiYau.Mathlib.Analysis.Calculus.ContDiff.LinearIsometry
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Data.Bundle
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Basis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Curry.Basic
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.TensorProduct
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Section
public import CalabiYau.Geometry.Manifold.Tensor.Product.Basis
public import CalabiYau.Geometry.Manifold.Tensor.Product.Bundle
public import CalabiYau.Geometry.Manifold.Tensor.Product.Pretrivialization
public import CalabiYau.Geometry.Manifold.Tensor.Product.Defs
public import CalabiYau.Mathlib.LinearAlgebra.TensorProduct.HomEquiv
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Curry
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Flip
public import CalabiYau.Mathlib.Analysis.Normed.Module.Multilinear.Flip
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Mul
public import CalabiYau.Mathlib.Analysis.Normed.Module.Alternating.DomCongr
public import Mathlib.LinearAlgebra.Alternating.Basic
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Shuffle.Decomposition
public import CalabiYau.Mathlib.LinearAlgebra.Alternating.ShuffleSplit
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.Tactic.Cases
public import CalabiYau.Geometry.Manifold.Tensor.Product.Fiber
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import CalabiYau.Mathlib.LinearAlgebra.Dual.PredualBasis
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import CalabiYau.Geometry.Manifold.LieDerivative.Tensor
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Coordinates.BundleBasis
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
public import CalabiYau.Geometry.Manifold.Connection.TensorNabla.InducedConnection
public import CalabiYau.Geometry.Manifold.Bundle.TangentSpace
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic
public import CalabiYau.Geometry.Manifold.Coordinates.Calculus.FixedBaseDerivative
public import CalabiYau.Geometry.Riemannian.Operator.Scalar.Calculus
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Mul
public import CalabiYau.Geometry.Riemannian.TensorInner.Tangent.Riemannian
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import CalabiYau.Geometry.Manifold.Bundle.Frame
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import CalabiYau.Geometry.Manifold.Bundle.Equiv
public import CalabiYau.Geometry.Manifold.Bundle.Zero
public import CalabiYau.Geometry.Riemannian.Metric.Coordinates.ChartGram
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.NormSquared
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.CompactSupport
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Green.Identities
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Analysis.Normed.Group.Uniform
public import CalabiYau.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import CalabiYau.Analysis.Sobolev.Chart.RiemannianMeasureComparison
public import CalabiYau.Analysis.Sobolev.Manifold.Measure.UniformChartComparison
public import CalabiYau.Analysis.Sobolev.Chart.BanachCompleteness.CompletenessLp
public import CalabiYau.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Basic
public import CalabiYau.Analysis.Sobolev.Manifold.RiemannianRellich
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import CalabiYau.Analysis.Sobolev.Manifold.Rellich.Compactness

@[expose] public section
open CalabiYau.Riemannian

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplResidualMemW1p

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Laplacian.LaplacianDomainSmoothMul
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open CalabiYau.Analysis.Sobolev.Chart
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma chartPushedRaw_smooth_eq_zero_off_image_tsupport
    {α : M} {f : M → ℝ}
    {y : EuclN}
    (hy : y ∉ (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f))) :
    chartPushedRaw (I := I) (M := M) α f y = 0 := by
  classical
  by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
  · exact _root_.Sobolev.Chart.chartPushedRaw_eq_zero_off_image_tsupport
      (I := I) (M := M) (u := f) α hy_target hy
  · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α f hy_target

variable [CompactSpace M] in
private lemma chartPushedRaw_smooth_hasCompactSupport
    {α : M} {f : M → ℝ}
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPushedRaw (I := I) (M := M) α f) := by
  classical
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hK_compact : IsCompact K := by
    refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
    have h_tsupp_compact : IsCompact (tsupport f) :=
      (isClosed_tsupport _).isCompact
    have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
      apply (continuousOn_extChartAt (I := I) α).mono
      intro x hx
      have hsrc : x ∈ (chartAt H α).source := hf_support hx
      rw [← CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hsrc
      exact hsrc
    exact h_tsupp_compact.image_of_continuousOn h_cont
  apply HasCompactSupport.of_support_subset_isCompact hK_compact
  intro y hy_support
  by_contra hyK
  apply hy_support
  exact chartPushedRaw_smooth_eq_zero_off_image_tsupport
    (I := I) (M := M) (f := f) (α := α) hyK

section

variable [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]

private lemma chartPushedRaw_smooth_continuous
    {α : M} {f : M → ℝ}
    (hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_support : tsupport f ⊆ (chartAt H α).source) :
    Continuous (chartPushedRaw (I := I) (M := M) α f) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hK_compact : IsCompact K := by
    refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
    have h_tsupp_compact : IsCompact (tsupport f) :=
      (isClosed_tsupport _).isCompact
    have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
      apply (continuousOn_extChartAt (I := I) α).mono
      intro x hx
      have hsrc : x ∈ (chartAt H α).source := hf_support hx
      rw [← CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at hsrc
      exact hsrc
    exact h_tsupp_compact.image_of_continuousOn h_cont
  have hK_in_Ω : K ⊆ Ω := by
    intro y hy
    rcases hy with ⟨z, hz, hzy⟩
    rcases hz with ⟨x, hx_support, hxz⟩
    have hxsrc : x ∈ (chartAt H α).source := hf_support hx_support
    rw [hΩ_def, chartTargetEuclid]
    refine ⟨z, ?_, hzy⟩
    rw [← hxz]
    have : x ∈ (extChartAt I α).source := by
      rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)]
      exact hxsrc
    exact (extChartAt I α).map_source this
  have hKc_open : IsOpen (Kᶜ : Set EuclN) := hK_compact.isClosed.isOpen_compl
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy_Ω : y ∈ Ω
  · have hΩ_nhds : Ω ∈ 𝓝 y := hΩ_open.mem_nhds hy_Ω
    have h_eq_on_Ω : ∀ z ∈ Ω, chartPushedRaw (I := I) (M := M) α f z =
        f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
      intro z hz
      exact chartPushedRaw_apply_of_mem (I := I) (M := M) α f hz
    have h_smooth_cont : ContinuousOn
        (fun z : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        Ω := by
      have hscalar : ContDiffOn ℝ ∞
          (fun z : E => f ((extChartAt I α).symm z))
          (extChartAt I α).target :=
        CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
          (I := I) α hf_smooth
      have htoEuc_cont : Continuous ((toEuclidean (E := E)).symm) :=
        (toEuclidean (E := E)).symm.continuous
      have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm) Ω (extChartAt I α).target := by
        intro z hz
        rw [hΩ_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hz
        exact hz
      have hcont_scalar := hscalar.continuousOn
      exact hcont_scalar.comp htoEuc_cont.continuousOn hmaps
    refine ContinuousAt.congr (f := fun z =>
      f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) ?_ ?_
    · exact (h_smooth_cont y hy_Ω).continuousAt hΩ_nhds
    · filter_upwards [hΩ_nhds] with z hz using (h_eq_on_Ω z hz).symm
  · have hy_Kc : y ∈ (Kᶜ : Set EuclN) := by
      intro hy_K
      exact hy_Ω (hK_in_Ω hy_K)
    have hKc_nhds : (Kᶜ : Set EuclN) ∈ 𝓝 y := hKc_open.mem_nhds hy_Kc
    have h_eq_zero_on_Kc : ∀ z ∈ (Kᶜ : Set EuclN),
        chartPushedRaw (I := I) (M := M) α f z = 0 := by
      intro z hz
      exact chartPushedRaw_smooth_eq_zero_off_image_tsupport
        (I := I) (M := M) (f := f) (α := α) hz
    refine ContinuousAt.congr (f := fun _ : EuclN => (0 : ℝ)) ?_ ?_
    · exact continuousAt_const
    · filter_upwards [hKc_nhds] with z hz using (h_eq_zero_on_Kc z hz).symm

private lemma chartPushedRaw_smooth_memLp
    {α : M} {f : M → ℝ}
    (hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (p : ℝ≥0∞) :
    MemLp (chartPushedRaw (I := I) (M := M) α f) p
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have hcont : Continuous (chartPushedRaw (I := I) (M := M) α f) :=
    chartPushedRaw_smooth_continuous (I := I) (M := M)
      (f := f) (α := α) hf_smooth hf_support
  have hcompact : HasCompactSupport (chartPushedRaw (I := I) (M := M) α f) :=
    chartPushedRaw_smooth_hasCompactSupport
      (I := I) (M := M) (f := f) (α := α) hf_support
  have hmemLp_full : MemLp (chartPushedRaw (I := I) (M := M) α f) p
      (volume : Measure EuclN) :=
    hcont.memLp_of_hasCompactSupport (μ := volume) hcompact
  exact hmemLp_full.restrict _

theorem memW1p_chartPushedRaw_of_contMDiff_tsupport
    {α : M} {f : M → ℝ}
    (hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf_support : tsupport f ⊆ (chartAt H α).source)
    (p : ℝ≥0∞) :
    Sobolev.Euclidean.MemW1p (d := Module.finrank ℝ E) p
      (chartPushedRaw (I := I) (M := M) α f)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ⟨?_, ?_⟩
  · exact chartPushedRaw_smooth_memLp (I := I) (M := M)
      (f := f) (α := α) hf_smooth hf_support p
  · intro i
    set Λ : EuclN → ℝ := chartPushedRaw (I := I) (M := M) α f with hΛ_def
    set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
    set K : Set EuclN :=
      (toEuclidean (E := E)) '' ((extChartAt I α) '' (tsupport f)) with hK_def
    have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
    have hK_compact : IsCompact K := by
      refine IsCompact.image ?_ (toEuclidean (E := E)).continuous
      have h_tsupp_compact : IsCompact (tsupport f) :=
        (isClosed_tsupport _).isCompact
      have h_cont : ContinuousOn (extChartAt I α) (tsupport f) := by
        apply (continuousOn_extChartAt (I := I) α).mono
        intro x hx
        have hsrc : x ∈ (chartAt H α).source := hf_support hx
        rw [← CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)] at hsrc
        exact hsrc
      exact h_tsupp_compact.image_of_continuousOn h_cont
    have hKc_open : IsOpen (Kᶜ : Set EuclN) := hK_compact.isClosed.isOpen_compl
    have hK_in_Ω : K ⊆ Ω := by
      intro y hy
      rcases hy with ⟨z, hz, hzy⟩
      rcases hz with ⟨x, hx_support, hxz⟩
      have hxsrc : x ∈ (chartAt H α).source := hf_support hx_support
      rw [hΩ_def, chartTargetEuclid]
      refine ⟨z, ?_, hzy⟩
      rw [← hxz]
      have : x ∈ (extChartAt I α).source := by
        rw [CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
        exact hxsrc
      exact (extChartAt I α).map_source this
    have hΛ_smooth : ContDiff ℝ ∞ Λ := by
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hy_Ω : y ∈ Ω
      · have hΩ_nhds : Ω ∈ 𝓝 y := hΩ_open.mem_nhds hy_Ω
        have h_eq_on_Ω : ∀ z ∈ Ω, Λ z =
            f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
          intro z hz
          exact chartPushedRaw_apply_of_mem (I := I) (M := M) α f hz
        have h_smooth_form : ContDiffOn ℝ ∞
            (fun z : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
            Ω := by
          have hscalar : ContDiffOn ℝ ∞
              (fun z : E => f ((extChartAt I α).symm z))
              (extChartAt I α).target :=
            CalabiYau.DivergenceTheorem.scalarOnE_contDiffOn
              (I := I) α hf_smooth
          have htoEuc_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
            ContinuousLinearEquiv.contDiff _
          have hmaps : Set.MapsTo ((toEuclidean (E := E)).symm) Ω (extChartAt I α).target := by
            intro z hz
            rw [hΩ_def, chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hz
            exact hz
          exact hscalar.comp htoEuc_smooth.contDiffOn hmaps
        have h_smooth_at : ContDiffAt ℝ ∞
            (fun z : EuclN => f ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) y := by
          exact (h_smooth_form y hy_Ω).contDiffAt (hΩ_open.mem_nhds hy_Ω)
        apply h_smooth_at.congr_of_eventuallyEq
        filter_upwards [hΩ_nhds] with z hz using h_eq_on_Ω z hz
      · have hy_Kc : y ∈ (Kᶜ : Set EuclN) := fun hy_K => hy_Ω (hK_in_Ω hy_K)
        have hKc_nhds : (Kᶜ : Set EuclN) ∈ 𝓝 y := hKc_open.mem_nhds hy_Kc
        refine ContDiffAt.congr_of_eventuallyEq (f := fun _ : EuclN => (0 : ℝ))
          contDiffAt_const ?_
        filter_upwards [hKc_nhds] with z hz
        exact chartPushedRaw_smooth_eq_zero_off_image_tsupport
          (I := I) (M := M) (f := f) (α := α) hz
    have hΛ_compact : HasCompactSupport Λ :=
      chartPushedRaw_smooth_hasCompactSupport
        (I := I) (M := M) (f := f) (α := α) hf_support
    have hΛ_smooth_top : ContDiff ℝ (⊤ : ℕ∞) Λ := hΛ_smooth
    have hΛ_smooth_C1 : ContDiff ℝ 1 Λ := hΛ_smooth.of_le (by norm_cast)
    have hw_univ : Sobolev.Euclidean.MemW1pWitness (d := Module.finrank ℝ E) p Λ Set.univ :=
      Sobolev.Euclidean.MemW1pWitness.ofContDiffHasCompactSupport (p := p) hΛ_smooth_top hΛ_compact
    have hw_chart : Sobolev.Euclidean.MemW1pWitness (d := Module.finrank ℝ E) p Λ
        (chartTargetEuclid (I := I) (M := M) α) :=
      hw_univ.restrict
        (Set.subset_univ _)
    refine ⟨fun x => hw_chart.weakGrad x i,
      hw_chart.weakGrad_component_memLp i, hw_chart.isWeakGrad i⟩

end

section

variable [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def fHLeibnizResidualSmoothRep
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) : M → ℝ :=
  fun x : M =>
    -((2 : ℝ) * g.inner x (gradFun (I := I) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x)
      (gradFun (I := I) g v.toFun x)) -
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x * v.toFun x

theorem fHLeibnizResidualLp_smoothToH1Compl_coeFn_ae
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    ((CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v) :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fHLeibnizResidualSmoothRep (I := I) (M := M) g α v := by
  classical
  set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α
  set Δρα : C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α
  have h_gradInnerCLM_smooth :
      gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g v) =
        gradInnerSmooth (I := I) (M := M) g ρα v :=
    gradInnerCLM_smoothToH1Compl (I := I) (M := M) g ρα v
  have h_H1ComplToLp_smooth :
      h1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v) =
        smoothToLp (I := I) (M := M) g v :=
    h1ComplToLp_smoothToH1Compl (I := I) (M := M) g v
  have h_lp_eq :
      CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) =
        -((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) -
          smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v) := by
    unfold CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
    rw [h_gradInnerCLM_smooth, h_H1ComplToLp_smooth]
  rw [h_lp_eq]
  have h_grad_coeFn := gradInnerSmooth_coeFn (I := I) (M := M) g ρα v
  have h_smoothMul_coeFn :=
    smoothMulLp_apply_coeFn (I := I) (M := M) g Δρα
      (smoothToLp (I := I) (M := M) g v)
  have h_smoothToLp_coeFn :
      (smoothToLp (I := I) (M := M) g v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g] v.toFun :=
    MemLp.coeFn_toLp v.memLp_two
  have h_sub_coe :
      (((-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) -
          smoothMulLp (I := I) (M := M) g Δρα
            (smoothToLp (I := I) (M := M) g v)) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        fun x : M =>
          ((-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x -
          ((smoothMulLp (I := I) (M := M) g Δρα
              (smoothToLp (I := I) (M := M) g v) :
              Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x :=
    MeasureTheory.Lp.coeFn_sub _ _
  have h_neg_coe :
      ((-((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        fun x : M => -(((((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) x :=
    MeasureTheory.Lp.coeFn_neg _
  have h_smul_coe :
      ((((2 : ℝ) • gradInnerSmooth (I := I) (M := M) g ρα v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
          riemannianVolumeMeasure (I := I) (M := M) g]
        (2 : ℝ) • ((gradInnerSmooth (I := I) (M := M) g ρα v :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    MeasureTheory.Lp.coeFn_smul _ _
  filter_upwards [h_sub_coe, h_neg_coe, h_smul_coe, h_grad_coeFn,
    h_smoothMul_coeFn, h_smoothToLp_coeFn] with x hx_sub hx_neg hx_smul hx_grad
    hx_smoothMul hx_smoothToLp
  rw [hx_sub]
  rw [hx_neg]
  rw [hx_smul]
  rw [hx_smoothMul]
  rw [hx_smoothToLp]
  unfold fHLeibnizResidualSmoothRep
  simp only [Pi.smul_apply, smul_eq_mul, hx_grad]
  ring

end

end

end DiffChartBilinearH1ComplResidualMemW1p
end Laplacian
end Analysis
end CalabiYau

end
