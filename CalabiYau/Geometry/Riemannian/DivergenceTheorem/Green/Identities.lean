-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/DivergenceTheorem/Green/Identities.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.Formula
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.CompactSupport
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.Support
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.Operator.DirectionalDerivative
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import CalabiYau.Geometry.Riemannian.Volume.Family.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import CalabiYau.Geometry.Riemannian.Metric.Basic
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
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Data.Bundle
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Curry.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.TensorProduct
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Section
public import CalabiYau.Geometry.Manifold.Tensor.Product.Basis
public import CalabiYau.Geometry.Manifold.Tensor.Product.Bundle
public import CalabiYau.Geometry.Manifold.Tensor.Product.Pretrivialization
public import CalabiYau.Geometry.Manifold.Tensor.Product.Defs
public import CalabiYau.Mathlib.LinearAlgebra.TensorProduct.HomEquiv
public import Mathlib.LinearAlgebra.Dual.Defs
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
public import Mathlib.Topology.FiberBundle.Basic
public import CalabiYau.Geometry.Manifold.Tensor.Product.Fiber
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import CalabiYau.Geometry.Manifold.Bundle.Section
public import CalabiYau.Mathlib.LinearAlgebra.Dual.PredualBasis
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import CalabiYau.Geometry.Manifold.LieDerivative.Tensor
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Coordinates.BundleBasis
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
public import CalabiYau.Geometry.Manifold.Connection.TensorNabla.InducedConnection
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import CalabiYau.Geometry.Manifold.Bundle.TangentSpace
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic
public import CalabiYau.Geometry.Manifold.Coordinates.Calculus.FixedBaseDerivative
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import CalabiYau.Geometry.Riemannian.Volume.Invariance
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Geometry.Manifold.Metrizable
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import CalabiYau.Geometry.Riemannian.Volume.Family.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import CalabiYau.Geometry.Riemannian.Operator.Scalar.Calculus

@[expose] public section


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

open CalabiYau.Riemannian
namespace CalabiYau.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_support : HasCompactSupport h) :
    ∫ x, g.inner x ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨_, hh⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * ΔG (I := I) g ⟨_, hh⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG (I := I) g ⟨_, hh⟩ with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g ⟨_, hh⟩ hh_support
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hf X hX_cs
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨_, hh⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    let fb : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
    change tangentSectionAction (I := I) X (⇑fb) x =
      g.inner x ((gradG (I := I) g fb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨_, hh⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
    rw [tangentSectionAction_eq_inner_grad_g (I := I) g fb X x]
    change g.inner x (X x) ((gradG (I := I) g fb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((gradG (I := I) g fb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x)
    exact g.symm x _ _
  have hRHS_eq : ∀ x : M,
      f x * divergenceG (I := I) g X x = f x * ΔG (I := I) g ⟨_, hh⟩ x := by
    intro x
    rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((gradG (I := I) g ⟨_, hf⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨_, hh⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, f x * divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x * ΔG (I := I) g ⟨_, hh⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

end CalabiYau.DivergenceTheorem
