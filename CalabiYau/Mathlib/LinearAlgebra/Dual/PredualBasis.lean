-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Multilinear/PredualBasis.lean
-- Locally modified.
/-
Authors: Jack McCarthy
-/
module
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

noncomputable section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {d : ℕ}

def Module.Basis.cDualBasis [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (B : Module.Basis (Fin d) 𝕜 E) :
    Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜) :=
  B.dualBasis.map LinearMap.toContinuousLinearMap

@[simp]
theorem Module.Basis.cDualBasis_apply_self [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (B : Module.Basis (Fin d) 𝕜 E) (i j : Fin d) :
    B.cDualBasis i (B j) = if i = j then (1 : 𝕜) else 0 := by
  change B.dualBasis i (B j) = _
  rw [Module.Basis.dualBasis_apply_self]
  split_ifs with h1 h2 <;> simp_all [eq_comm]

