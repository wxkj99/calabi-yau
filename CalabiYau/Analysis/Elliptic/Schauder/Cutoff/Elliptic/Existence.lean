-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Cutoff/Elliptic/Existence.lean
-- Locally modified.
module
public import CalabiYau.Mathlib.Geometry.Manifold.PartitionOfUnity.CompactSupport
public import CalabiYau.Analysis.Parabolic.Euclidean.Duhamel.Frozen
public import CalabiYau.Mathlib.Analysis.Holder.Localization
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section


noncomputable section

open Filter Real Set
open scoped ContDiff NNReal RealInnerProductSpace Topology

namespace CalabiYau.Schauder

open HeatEquation

variable {X A : Type*} [TopologicalSpace X]
  [NormedAddCommGroup A] [NormedSpace Real A]

def compactSupportBoundedContinuousFunction (f : X → A) (hf : Continuous f)
    (hcs : HasCompactSupport f) : BoundedContinuousFunction X A :=
  BoundedContinuousFunction.ofNormedAddCommGroup f hf
    (Classical.choose (hf.bounded_above_of_compact_support hcs))
    (Classical.choose_spec (hf.bounded_above_of_compact_support hcs))

omit [NormedSpace Real A] in
@[simp]
theorem compactSupportBoundedContinuousFunction_apply (f : X → A) (hf : Continuous f)
    (hcs : HasCompactSupport f) (x : X) :
    compactSupportBoundedContinuousFunction f hf hcs x = f x := rfl

section Euclidean

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V] [FiniteDimensional Real V]

end Euclidean

end CalabiYau.Schauder

end
