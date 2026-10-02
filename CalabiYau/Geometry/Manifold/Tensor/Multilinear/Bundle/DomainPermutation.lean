-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Multilinear/Bundle/DomainPermutation.lean
-- Locally modified.
/-
Authors: Jack McCarthy (pattern), extended for slot permutation of smooth sections
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.TensorProduct

@[expose] public section

open CalabiYau.Tensor.Multilinear

noncomputable section

open Bundle Set
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

theorem triv_coord_domDomCongr {s s' d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F)
    (e : Fin s ≃ Fin s')
    (idx : Fin s' → Fin d) (x₀ x : B)
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    (continuousMultilinearMapBasis b s').repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s' => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s' F E x) x₀
        ⟨x, ContinuousMultilinearMap.domDomCongr e α⟩).2 idx =
    (continuousMultilinearMapBasis b s).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀ ⟨x, α⟩).2
        (idx ∘ e) := by
  simp_rw [continuousMultilinearMap_basis_repr]
  have htriv : ∀ {m : ℕ} (T : Bundle.continuousMultilinearMap 𝕜 m F E x) (w : Fin m → F),
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin m => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 m F E x) x₀ ⟨x, T⟩).2 w =
      T (fun i => (trivializationAt F E x₀).symmL 𝕜 x (w i)) := by
    intro m T w; rfl
  simp_rw [htriv, ContinuousMultilinearMap.domDomCongr_apply, Function.comp]

end Bundle.continuousMultilinearMap

namespace CalabiYau.MultilinearSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

noncomputable def domDomCongr {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) :
    MultilinearSection 𝕜 F IB E n s' :=
  ⟨fun x => ContinuousMultilinearMap.domDomCongr e (α x), by
    let d := Module.finrank 𝕜 F
    let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
    rw [contMDiff_multilinearSection_iff_coord E n b]
    intro idx x₀
    have hα := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (α x : Bundle.continuousMultilinearMap 𝕜 s F E x))).mp α.contMDiff)
    simp_rw [Bundle.continuousMultilinearMap.triv_coord_domDomCongr b e idx x₀ _ (α _)]
    exact hα (idx ∘ e) x₀⟩

@[simp] theorem domDomCongr_apply {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : MultilinearSection 𝕜 F IB E n s) (x : B) :
    (domDomCongr (IB := IB) n e α) x = ContinuousMultilinearMap.domDomCongr e (α x) :=
  rfl

@[simp] theorem domDomCongr_refl {s : ℕ} (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n (Equiv.refl (Fin s)) α = α := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]

@[simp] theorem domDomCongr_zero {s s' : ℕ} (e : Fin s ≃ Fin s') :
    domDomCongr (IB := IB) n e (0 : MultilinearSection 𝕜 F IB E n s)
      = (0 : MultilinearSection 𝕜 F IB E n s') := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContMDiffSection.coe_zero]

theorem domDomCongr_id_of_valPres {s : ℕ} (e : Fin s ≃ Fin s)
    (he : ∀ i, ((e i : Fin s) : ℕ) = (i : ℕ))
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e α = α := by
  have hee : e = Equiv.refl (Fin s) := Equiv.ext fun i => Fin.ext (he i)
  rw [hee, domDomCongr_refl]

theorem domDomCongr_trans {s s' s'' : ℕ} (e₁ : Fin s ≃ Fin s') (e₂ : Fin s' ≃ Fin s'')
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e₂ (domDomCongr (IB := IB) n e₁ α)
      = domDomCongr (IB := IB) n (e₁.trans e₂) α := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]

theorem domDomCongr_add {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α β : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e (α + β)
      = domDomCongr (IB := IB) n e α + domDomCongr (IB := IB) n e β := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]

theorem domDomCongr_smul {s s' : ℕ} (e : Fin s ≃ Fin s') (c : 𝕜)
    (α : MultilinearSection 𝕜 F IB E n s) :
    domDomCongr (IB := IB) n e (c • α) = c • domDomCongr (IB := IB) n e α := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  simp [domDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContMDiffSection.coe_smul]

end CalabiYau.MultilinearSection
