-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/DiffChart/ResidualRegularity/BilinearH1ComplResidual.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidualMemW1p
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
public import Mathlib.Data.Real.Basic
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

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplResidual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Laplacian.LaplacianDomainSmoothMul
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def smoothFChartResidual
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) : EuclN → ℝ :=
  CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
    (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v)

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothFChartResidual_tendsto_fChartResidual_lp_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (v : ℕ → SmoothScalar g)
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n =>
      eLpNorm
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y -
          CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
            (I := I) (M := M) g α u_h y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0) := by
  classical
  have h_residual_tendsto : Tendsto (fun n =>
      CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n)))
      atTop (𝓝 (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α u_h)) := by
    set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α
    set Δρα : C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α
    have h_A : Tendsto (fun n => -((2 : ℝ) •
        gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g (v n))))
        atTop (𝓝 (-((2 : ℝ) •
          gradInnerCLM (I := I) (M := M) g ρα u_h))) := by
      have h_grad : Tendsto (fun n =>
          gradInnerCLM (I := I) (M := M) g ρα
            (smoothToH1Compl (I := I) (M := M) g (v n)))
          atTop (𝓝 (gradInnerCLM (I := I) (M := M) g ρα u_h)) :=
        ((gradInnerCLM (I := I) (M := M) g ρα).continuous.tendsto _).comp
          h_tendsto
      have h_smul : Tendsto (fun n => (2 : ℝ) •
          gradInnerCLM (I := I) (M := M) g ρα
            (smoothToH1Compl (I := I) (M := M) g (v n)))
          atTop (𝓝 ((2 : ℝ) •
            gradInnerCLM (I := I) (M := M) g ρα u_h)) :=
        Tendsto.const_smul h_grad (2 : ℝ)
      exact h_smul.neg
    have h_B : Tendsto (fun n =>
        smoothMulLp (I := I) (M := M) g Δρα
          (h1ComplToLp (I := I) (M := M) g
            (smoothToH1Compl (I := I) (M := M) g (v n))))
        atTop (𝓝 (smoothMulLp (I := I) (M := M) g Δρα
          (h1ComplToLp (I := I) (M := M) g u_h))) := by
      have h_H1Lp : Tendsto (fun n =>
          h1ComplToLp (I := I) (M := M) g
            (smoothToH1Compl (I := I) (M := M) g (v n)))
          atTop (𝓝 (h1ComplToLp (I := I) (M := M) g u_h)) :=
        ((h1ComplToLp (I := I) (M := M) g).continuous.tendsto _).comp h_tendsto
      exact ((smoothMulLp (I := I) (M := M) g Δρα).continuous.tendsto _).comp h_H1Lp
    have h_sub : Tendsto (fun n =>
        -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g (v n))) -
          smoothMulLp (I := I) (M := M) g Δρα
            (h1ComplToLp (I := I) (M := M) g
              (smoothToH1Compl (I := I) (M := M) g (v n))))
        atTop (𝓝 (-((2 : ℝ) • gradInnerCLM (I := I) (M := M) g ρα u_h) -
          smoothMulLp (I := I) (M := M) g Δρα
            (h1ComplToLp (I := I) (M := M) g u_h))) :=
      h_A.sub h_B
    simpa only [CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp,
      ρα, Δρα] using h_sub
  have h_chartPulled_tendsto : Tendsto (fun n =>
      chartPushedRawLpFromLp (I := I) (M := M) g α
        (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))))
      atTop (𝓝 (chartPushedRawLpFromLp (I := I) (M := M) g α
        (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α u_h))) :=
    CalabiYau.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRawLpFromLp_tendsto
      (I := I) (M := M) g α h_residual_tendsto
  have h_norm_tendsto : Tendsto (fun n =>
      ‖chartPushedRawLpFromLp (I := I) (M := M) g α
        (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h)‖)
      atTop (𝓝 0) := by
    have h_sub : Tendsto (fun n =>
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h))
        atTop (𝓝 0) := by
      have := h_chartPulled_tendsto.sub (tendsto_const_nhds
        (x := chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h)))
      simpa using this
    change Tendsto
      ((fun a => ‖a‖) ∘ fun n =>
        chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)) atTop (𝓝 0)
    simpa only [norm_zero] using (continuous_norm.tendsto (0 :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))).comp h_sub
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_eLpNorm_eq : ∀ n,
      eLpNorm
        (((chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)) : Lp ℝ 2 _) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      ENNReal.ofReal
        ‖chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h)‖ := by
    intro n
    rw [Lp.norm_def]
    rw [ENNReal.ofReal_toReal
      ((Lp.memLp _).eLpNorm_lt_top.ne)]
  have h_eLp_tendsto : Tendsto (fun n =>
      eLpNorm
        (((chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)) : Lp ℝ 2 _) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0) := by
    have h_funeq : (fun n =>
        eLpNorm
          (((chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
            chartPushedRawLpFromLp (I := I) (M := M) g α
              (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
                (I := I) (M := M) g α u_h)) : Lp ℝ 2 _) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) =
        fun n => ENNReal.ofReal
          ‖chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)‖ := by
      funext n
      exact h_eLpNorm_eq n
    rw [h_funeq]
    have h_ofReal_zero : ENNReal.ofReal (0 : ℝ) = 0 := by simp
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from h_ofReal_zero.symm]
    exact ENNReal.tendsto_ofReal h_norm_tendsto
  have h_subFun_aeEq : ∀ n,
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h) : Lp ℝ 2 _) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y -
        CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h y := by
    intro n
    have h_sub_coe :=
      MeasureTheory.Lp.coeFn_sub
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))))
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h))
    filter_upwards [h_sub_coe] with y hy
    rw [hy]
    rfl
  convert h_eLp_tendsto using 1
  funext n
  exact eLpNorm_congr_ae (h_subFun_aeEq n).symm

end DiffChartBilinearH1ComplResidual
end Laplacian
end Analysis
end CalabiYau

end
