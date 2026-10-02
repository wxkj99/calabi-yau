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

theorem exists_predual_basis [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (b : Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜)) :
    ∃ B : Module.Basis (Fin d) 𝕜 E,
      ∀ i j, b i (B j) = if i = j then 1 else 0 := by
  let b_alg : Module.Basis (Fin d) 𝕜 (E →ₗ[𝕜] 𝕜) :=
    b.map (LinearMap.toContinuousLinearMap (𝕜 := 𝕜) (E := E)).symm
  let B : Module.Basis (Fin d) 𝕜 E :=
    b_alg.dualBasis.map (Module.evalEquiv 𝕜 E).symm
  refine ⟨B, fun i j => ?_⟩
  have agree : ∀ x, b i x = (b_alg i) x := by
    intro x; simp [b_alg, Module.Basis.map_apply]
  rw [agree]
  change (b_alg i) (B j) = _
  simp [B, Module.Basis.map_apply, Finsupp.single_apply]

theorem cdual_sum_repr {d : ℕ} [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    (b : Module.Basis (Fin d) 𝕜 E) (α : E →L[𝕜] 𝕜) :
    (∑ k, (α (b k)) • LinearMap.toContinuousLinearMap (b.coord k)) = α := by
  apply ContinuousLinearMap.coe_injective
  rw [show ((∑ k, (α (b k)) • LinearMap.toContinuousLinearMap (b.coord k)
        : E →L[𝕜] 𝕜) : E →ₗ[𝕜] 𝕜) =
      ∑ k, (α (b k)) • (b.coord k) by
    rw [ContinuousLinearMap.toLinearMap_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap]]
  exact b.sum_dual_apply_smul_coord (α : E →ₗ[𝕜] 𝕜)
