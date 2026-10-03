-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Multilinear/Bundle/Basis.lean
-- Locally modified.
/-
Authors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace CalabiYau.Tensor.Multilinear

noncomputable section

open _root_.Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

noncomputable instance multilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) := by
  have : Module.Finite 𝕜 F := inferInstance
  have : Module.Free 𝕜 F := inferInstance
  have : Module.Finite 𝕜 𝕜 := inferInstance
  have : Module.Free 𝕜 𝕜 := inferInstance
  infer_instance

noncomputable instance continuousMultilinearMap_finiteDimensional (s : ℕ) :
    FiniteDimensional 𝕜 (MLF s) := by
  have : FiniteDimensional 𝕜 (MultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    multilinearMap_finiteDimensional s
  exact FiniteDimensional.of_injective
    ContinuousMultilinearMap.toMultilinearMapLinear
    ContinuousMultilinearMap.toMultilinearMap_injective

theorem finrank_continuousMultilinearMap (s : ℕ) :
    Module.finrank 𝕜 (MLF s) = (Module.finrank 𝕜 F) ^ s := by
  induction s with
  | zero =>
    have e := continuousMultilinearCurryFin0 𝕜 F 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    simp [pow_zero, Module.finrank_self]
  | succ s ih =>
    have e := continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (s + 1) => F) 𝕜
    rw [e.toLinearEquiv.finrank_eq]
    have : FiniteDimensional 𝕜 (MLF s) := continuousMultilinearMap_finiteDimensional s
    have : Module.Free 𝕜 F := inferInstance
    have : Module.Free 𝕜 (MLF s) := inferInstance
    have e2 : (F →L[𝕜] MLF s) ≃ₗ[𝕜] (F →ₗ[𝕜] MLF s) := LinearMap.toContinuousLinearMap.symm
    rw [e2.finrank_eq, Module.finrank_linearMap 𝕜 𝕜, ih]
    ring

noncomputable def continuousMultilinearMapBasisElem {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) (σ : Fin s → Fin d) : MLF s :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin s) (1 : 𝕜)).compContinuousLinearMap
    (fun j => LinearMap.toContinuousLinearMap (b.coord (σ j)))

theorem continuousMultilinearMap_basisElem_apply {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F) (s : ℕ)
    (σ σ' : Fin s → Fin d) :
    continuousMultilinearMapBasisElem b s σ (fun j => b (σ' j)) =
    if σ = σ' then 1 else 0 := by
  simp_rw [continuousMultilinearMapBasisElem,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : σ = σ'
  · subst h; simp
  · simp only [h, ite_false]
    have ⟨j, hj⟩ : ∃ j, σ j ≠ σ' j := by contrapose! h; exact funext h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right (Ne.symm hj))

theorem continuousMultilinearMap_basisElem_linearIndependent {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (s : ℕ) :
    LinearIndependent 𝕜 (continuousMultilinearMapBasisElem b s) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc σ'
  have h1 : (∑ σ : Fin s → Fin d, c σ • continuousMultilinearMapBasisElem b s σ)
      (fun j => b (σ' j)) = 0 := by rw [hc]; rfl
  simp only [sum_apply, smul_apply,
    continuousMultilinearMap_basisElem_apply] at h1
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  rwa [smul_eq_mul, mul_one] at h1

noncomputable def continuousMultilinearMapBasis {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) : Module.Basis (Fin s → Fin d) 𝕜 (MLF s) :=
  Module.Basis.mk (continuousMultilinearMap_basisElem_linearIndependent b s)
    ((continuousMultilinearMap_basisElem_linearIndependent b s).span_eq_top_of_card_eq_finrank'
      (by
        have hd : Module.finrank 𝕜 F = d := by
          rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          finrank_continuousMultilinearMap, hd])).ge

theorem continuousMultilinearMap_basis_repr {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s : ℕ) (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) (σ : Fin s → Fin d) :
    (continuousMultilinearMapBasis b s).repr f σ = f (fun j => b (σ j)) := by
  have hbasis : ∀ ρ, (continuousMultilinearMapBasis b s) ρ =
      continuousMultilinearMapBasisElem b s ρ :=
    fun ρ => congr_fun (Module.Basis.coe_mk
      (continuousMultilinearMap_basisElem_linearIndependent b s) _) ρ
  conv_rhs => rw [← (continuousMultilinearMapBasis b s).sum_repr f]
  simp only [sum_apply, smul_apply,
    smul_eq_mul, hbasis, continuousMultilinearMap_basisElem_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

section smooth

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  (E : B → Type*) [Π x, AddCommMonoid (E x)] [Π x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [Π x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

omit [ContMDiffVectorBundle n F E IB] in
theorem contMDiff_multilinearSection_iff_coord {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) {s : ℕ}
    (f : ∀ x : B, _root_.Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContMDiff IB (IB.prod 𝓘(𝕜, MLF s)) n
      (fun x => TotalSpace.mk' (MLF s) x (f x)) ↔
    ∀ σ : Fin s → Fin d, ∀ x₀ : B,
      ContMDiffAt IB 𝓘(𝕜, 𝕜) n
        (fun x => (continuousMultilinearMapBasis b s).repr
          (trivializationAt (MLF s)
            (_root_.Bundle.continuousMultilinearMap 𝕜 s F E) x₀ ⟨x, f x⟩).2 σ) x₀ := by
  set Bb := continuousMultilinearMapBasis b s
  constructor
  · intro hf σ x₀
    have hsec := (contMDiffAt_section x₀).mp hf.contMDiffAt
    exact (LinearMap.toContinuousLinearMap (Bb.coord σ)).contMDiffAt.comp x₀ hsec
  · intro hcoord x₀
    rw [contMDiffAt_section]
    let g := fun x => (trivializationAt (MLF s)
        (_root_.Bundle.continuousMultilinearMap 𝕜 s F E) x₀ ⟨x, f x⟩).2
    change ContMDiffAt IB 𝓘(𝕜, MLF s) n g x₀
    rw [show g = fun x => Bb.equivFun.symm (Bb.equivFun (g x)) from
        funext fun x => (Bb.equivFun.symm_apply_apply (g x)).symm]
    exact (Bb.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt).comp x₀
      (contMDiffAt_pi_space.mpr fun σ => hcoord σ x₀)

end smooth

end

end CalabiYau.Tensor.Multilinear
