-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Elliptic/CompactEllipticity.lean
-- Locally modified.
module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import CalabiYau.Mathlib.Analysis.InnerProductSpace.Coercivity
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false


noncomputable section

open Matrix Set
open scoped RealInnerProductSpace

namespace CalabiYau.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

theorem exists_uniform_matrix_quadratic_lower_bound
    {X n : Type*} [TopologicalSpace X]
    [Fintype n]
    {K : Set X} (hK : IsCompact K)
    (A : X → Matrix n n Real)
    (hAcont : ∀ i j, ContinuousOn (fun x ↦ A x i j) K)
    (hApos : ∀ x ∈ K, (A x).PosDef) :
    ∃ c : Real, 0 < c ∧ ∀ x ∈ K, ∀ v : Euc n,
      c * ‖v‖ ^ 2 ≤ star v ⬝ᵥ A x *ᵥ v := by
  classical
  let e : Euc n →ₗ[Real] (n → Real) :=
    (PiLp.continuousLinearEquiv 2 Real (fun _ : n => Real)).toLinearMap
  let B : X → Euc n →L[Real] Euc n →L[Real] Real := fun x =>
    ((Matrix.toBilin' (A x)).comp e e).toContinuousBilinearMap
  have hB (x : X) (v w : Euc n) : B x v w = v ⬝ᵥ A x *ᵥ w := by
    simp only [B, LinearMap.toContinuousBilinearMap_apply,
      LinearMap.BilinForm.comp_apply, Matrix.toBilin'_apply']
    rfl
  let Q : X × Euc n → Real := fun p ↦
    ∑ i, ∑ j, A p.1 i j * p.2 i * p.2 j
  have hQcont : ContinuousOn Q (K ×ˢ (Set.univ : Set (Euc n))) := by
    refine continuousOn_finsetSum Finset.univ (fun i _ ↦ ?_)
    refine continuousOn_finsetSum Finset.univ (fun j _ ↦ ?_)
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (hAcont i j).comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
    · have hval : Continuous (fun v : Euc n => (v : n → Real)) :=
        (PiLp.continuousLinearEquiv 2 Real (fun _ : n ↦ Real)).continuous
      exact ((continuous_apply i).comp (hval.comp continuous_snd)).continuousOn
    · have hval : Continuous (fun v : Euc n => (v : n → Real)) :=
        (PiLp.continuousLinearEquiv 2 Real (fun _ : n ↦ Real)).continuous
      exact ((continuous_apply j).comp (hval.comp continuous_snd)).continuousOn
  have hBQ (p : X × Euc n) : B p.1 p.2 p.2 = Q p := by
    rw [hB]
    simp only [Q, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hBc : ContinuousOn (fun p : X × Euc n => B p.1 p.2 p.2)
      (K ×ˢ (univ : Set (Euc n))) := hQcont.congr fun p _ => hBQ p
  have hBp : ∀ x ∈ K, ∀ v : Euc n, v ≠ 0 → 0 < B x v v := by
    intro x hx v hv
    have hv' : (v : n → Real) ≠ 0 := by
      intro h
      exact hv (PiLp.ext fun i => congrFun h i)
    rw [hB]
    simpa only [Pi.star_apply, star_trivial] using (hApos x hx).dotProduct_mulVec_pos hv'
  obtain ⟨c, hc, hbound⟩ := hBc.exists_uniform_bilin_quadratic_lower_bound hK hBp
  refine ⟨c, hc, ?_⟩
  intro x hx v
  have h := hbound x hx v
  rw [hB] at h
  simpa only [Pi.star_apply, star_trivial] using h

end CalabiYau.Schauder
