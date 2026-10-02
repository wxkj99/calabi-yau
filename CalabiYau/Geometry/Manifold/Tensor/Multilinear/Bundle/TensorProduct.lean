-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Multilinear/Bundle/TensorProduct.lean
-- Locally modified.
/-
Authors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Fiber
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Section
public import CalabiYau.Geometry.Manifold.Tensor.Product.Basis
public import CalabiYau.Geometry.Manifold.Tensor.Product.Bundle
public import CalabiYau.Geometry.Manifold.Bundle.Section
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

open CalabiYau.Tensor.Multilinear

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable def productFun {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  ofModel (F := F) (E := E)
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv)

scoped infixl:70 " ⊗ₘ " => productFun

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem product_fun_apply {s q : ℕ} {x : B}
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x)
    (v : Fin (s + q) → E x) :
    productFun α β v = α (v ∘ Fin.castAdd q) * β (v ∘ Fin.natAdd s) := by
  have hx : x ∈ (trivializationAt F E x).baseSet := mem_baseSet_trivializationAt F E x
  change (continuousLinearEquivAt (F := F) (E := E) (s + q) x).symm
    ((toModel (F := F) (E := E) α |>.smulRight
      (toModel (F := F) (E := E) β)).uncurrySum.domDomCongr finSumFinEquiv) v = _
  have hsymm : ∀ (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜)
      (w : Fin (s + q) → E x),
      (continuousLinearEquivAt (F := F) (E := E) (s + q) x).symm f w =
      f (fun i => (trivializationAt F E x).continuousLinearMapAt 𝕜 x (w i)) := by
    intro f w; rfl
  rw [hsymm]
  simp only [ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.smulRight_apply]
  conv_lhs =>
    rw [show ∀ (c : 𝕜) (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
        (w : Fin q → F), (c • f) w = c * f w
      from fun c f w => by simp [smul_apply, smul_eq_mul]]
  simp_rw [show ∀ (n : ℕ) (T : Bundle.continuousMultilinearMap 𝕜 n F E x)
      (w : Fin n → F), toModel T w =
      T (fun i => (trivializationAt F E x).symmL 𝕜 x (w i)) from fun _ _ _ => rfl,
    Function.comp, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  congr 1
  · congr 1; funext i; simp only [Function.comp]
    exact (trivializationAt F E x).symmₗ_linearMapAt hx _
  · congr 1; funext i; simp only [Function.comp]
    exact (trivializationAt F E x).symmₗ_linearMapAt hx _

theorem triv_coord_product {s q d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F)
    (σ : Fin (s + q) → Fin d) (x₀ x : B)
    (α : Bundle.continuousMultilinearMap 𝕜 s F E x)
    (β : Bundle.continuousMultilinearMap 𝕜 q F E x) :
    (continuousMultilinearMapBasis b (s + q)).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
        ⟨x, productFun α β⟩).2 σ =
    (continuousMultilinearMapBasis b s).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀ ⟨x, α⟩).2
        (σ ∘ Fin.castAdd q) *
    (continuousMultilinearMapBasis b q).repr
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 q F E x) x₀ ⟨x, β⟩).2
        (σ ∘ Fin.natAdd s) := by
  simp_rw [continuousMultilinearMap_basis_repr]
  have htriv : ∀ (n : ℕ) (T : Bundle.continuousMultilinearMap 𝕜 n F E x)
      (w : Fin n → F),
      (trivializationAt (ContinuousMultilinearMap 𝕜 (fun _ : Fin n => F) 𝕜)
        (fun x => Bundle.continuousMultilinearMap 𝕜 n F E x) x₀ ⟨x, T⟩).2 w =
      T (fun i => (trivializationAt F E x₀).symmL 𝕜 x (w i)) := by
    intro n T w; rfl
  simp_rw [htriv, product_fun_apply]
  rfl

noncomputable def productBilinear (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 q F E x →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  LinearMap.mk₂ 𝕜 productFun
    (fun α₁ α₂ β => by
      apply toModel_injective (F := F) (E := E)
      simp only [productFun, toModel_add, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 add_apply,
                 smul_apply, smul_eq_mul]
      ring)
    (fun c α β => by
      apply toModel_injective (F := F) (E := E)
      simp only [productFun, toModel_smul, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 smul_apply, smul_eq_mul]
      ring)
    (fun α β₁ β₂ => by
      apply toModel_injective (F := F) (E := E)
      simp only [productFun, toModel_add, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 add_apply,
                 smul_apply, smul_eq_mul]
      ring)
    (fun c α β => by
      apply toModel_injective (F := F) (E := E)
      simp only [productFun, toModel_smul, toModel_ofModel]
      ext m
      simp only [ContinuousMultilinearMap.domDomCongr_apply,
                 ContinuousMultilinearMap.uncurrySum_apply,
                 ContinuousMultilinearMap.smulRight_apply,
                 smul_apply, smul_eq_mul]
      ring)

noncomputable def fromTensor (s q : ℕ) (x : B) :
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) →ₗ[𝕜]
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x :=
  TensorProduct.lift (productBilinear (F := F) (E := E) s q x)

noncomputable def modelProduct (s q : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 :=
  (f.smulRight g).uncurrySum.domDomCongr finSumFinEquiv

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem modelProduct_apply (s q : ℕ)
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (v : Fin (s + q) → F) :
    modelProduct s q f g v = f (v ∘ Fin.castAdd q) * g (v ∘ Fin.natAdd s) := by
  simp only [modelProduct, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.smulRight_apply]
  congr 1

noncomputable def modelFromTensor (s q : ℕ) :
    TensorProduct 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) →ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 :=
  TensorProduct.lift (LinearMap.mk₂ 𝕜 (modelProduct (𝕜 := 𝕜) (F := F) s q)
    (fun f₁ f₂ g => by ext v; simp [modelProduct_apply, add_mul])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring)
    (fun f g₁ g₂ => by ext v; simp [modelProduct_apply, mul_add])
    (fun c f g => by ext v; simp [modelProduct_apply]; ring))

theorem modelFromTensor_basisElem {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s q : ℕ) (σ : Fin (s + q) → Fin d) :
    modelFromTensor (𝕜 := 𝕜) (F := F) s q
      (continuousMultilinearMapBasisElem b s (σ ∘ Fin.castAdd q) ⊗ₜ[𝕜]
       continuousMultilinearMapBasisElem b q (σ ∘ Fin.natAdd s)) =
    continuousMultilinearMapBasisElem b (s + q) σ := by
  ext v
  simp only [modelFromTensor, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
    modelProduct_apply]
  simp only [continuousMultilinearMapBasisElem,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply, smul_eq_mul, mul_one,
    LinearMap.coe_toContinuousLinearMap', Function.comp]
  rw [← Fin.prod_univ_add (fun i => (b.coord (σ i)) (v i))]

theorem modelFromTensor_surjective {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s q : ℕ) :
    Function.Surjective (modelFromTensor (𝕜 := 𝕜) (F := F) s q) := by
  rw [← LinearMap.range_eq_top]
  rw [eq_top_iff]
  intro f _
  rw [← (continuousMultilinearMapBasis b (s + q)).sum_repr f]
  apply Submodule.sum_mem
  intro σ _
  apply Submodule.smul_mem
  rw [show (continuousMultilinearMapBasis b (s + q)) σ =
    continuousMultilinearMapBasisElem b (s + q) σ from
    congr_fun (Module.Basis.coe_mk
      (continuousMultilinearMap_basisElem_linearIndependent b (s + q)) _) σ]
  rw [← modelFromTensor_basisElem b s q σ]
  exact LinearMap.mem_range_self _ _

noncomputable def modelFromTensorEquiv {d : ℕ} (b : Module.Basis (Fin d) 𝕜 F)
    (s q : ℕ) :
    TensorProduct 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) ≃ₗ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (s + q) => F) 𝕜 := by
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  haveI : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional q
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofBijective (modelFromTensor s q)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        rw [Module.finrank_tensorProduct,
          finrank_continuousMultilinearMap s,
          finrank_continuousMultilinearMap q,
          finrank_continuousMultilinearMap (s + q), pow_add])).mpr
      (modelFromTensor_surjective b s q),
     modelFromTensor_surjective b s q⟩

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem product_fun_ofModel {s q : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (g : ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜) :
    productFun (ofModel (F := F) (E := E) (x := x) f)
                (ofModel (F := F) (E := E) (x := x) g) =
    ofModel (modelProduct s q f g) := by
  simp only [productFun, modelProduct, toModel_ofModel]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem fromTensor_map_ofModel {s q : ℕ} {x : B}
    (t : TensorProduct 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)) :
    fromTensor s q x (TensorProduct.map
      ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 →ₗ[𝕜]
        Bundle.continuousMultilinearMap 𝕜 s F E x)
      ((continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm :
        ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜 →ₗ[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x) t) =
    ofModel (F := F) (E := E) (x := x) (modelFromTensor s q t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp [fromTensor, modelFromTensor, ofModel]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [map_add, ofModel]
    exact congrArg₂ (· + ·) ih₁ ih₂
  | tmul f g =>
    simp only [TensorProduct.map_tmul, fromTensor, TensorProduct.lift.tmul,
      productBilinear, LinearMap.mk₂_apply, modelFromTensor]
    exact product_fun_ofModel f g

noncomputable def equiv (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x ≃ₗ[𝕜]
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) := by
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) s x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) q x
  haveI := instFiniteDimensional (𝕜 := 𝕜) (F := F) (E := E) (s + q) x
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 q F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : Module.Free 𝕜 (Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) :=
    Module.Free.of_divisionRing 𝕜 _
  haveI : FiniteDimensional 𝕜 (TensorProduct 𝕜
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  exact LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_tensorProduct,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) s x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) q x,
        finrank_eq (𝕜 := 𝕜) (F := F) (E := E) (s + q) x, pow_add])

end Bundle.continuousMultilinearMap

end

noncomputable section

open Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

local notation "MLF" s => ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

namespace Bundle.continuousMultilinearMap

theorem triv_fromTensor_eq_modelFromTensor (s q : ℕ) (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (t : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 q F E x) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    (trivializationAt (MLF (s + q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
      ⟨x, fromTensor s q x t⟩).2 =
    modelFromTensor (𝕜 := 𝕜) (F := F) s q
      ((trivializationAt ((MLF s) ⊗[𝕜] (MLF q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                   Bundle.continuousMultilinearMap 𝕜 q F E x) x₀
        ⟨x, t⟩).2) := by
  let := Bundle.TensorProduct.tensorFiberTopology
    𝕜 (MLF s) (MLF q)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E)
  let := Bundle.TensorProduct.fiberBundle
    (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
  have hxs : x ∈ (trivializationAt (MLF s)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x) x₀).baseSet := hx
  have hxq : x ∈ (trivializationAt (MLF q)
      (fun x => Bundle.continuousMultilinearMap 𝕜 q F E x) x₀).baseSet := hx
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    change (trivializationAt _ _ x₀
      ⟨x, (0 : Bundle.continuousMultilinearMap 𝕜 (s + q) F E x)⟩).2 = 0
    ext w; rfl
  | add t₁ t₂ ih₁ ih₂ =>
    have hlin : ∀ (a b : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
        Bundle.continuousMultilinearMap 𝕜 q F E x),
        (trivializationAt (MLF (s + q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
          ⟨x, fromTensor s q x (a + b)⟩).2 =
        (trivializationAt (MLF (s + q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
          ⟨x, fromTensor s q x a⟩).2 +
        (trivializationAt (MLF (s + q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
          ⟨x, fromTensor s q x b⟩).2 := by
      intro a b; ext w; simp [map_add]; rfl
    rw [hlin, ih₁, ih₂]
    simp only [Bundle.TensorProduct.tensorProduct_trivializationAt,
      Trivialization.tensorProduct_apply, map_add]
  | tmul α β =>
    ext w
    change (productFun α β) (fun i => (trivializationAt F E x₀).symmL 𝕜 x (w i)) = _
    rw [product_fun_apply]
    simp only [Bundle.TensorProduct.tensorProduct_trivializationAt,
      Trivialization.tensorProduct_apply, TensorProduct.map_tmul, modelFromTensor,
      TensorProduct.lift.tmul, LinearMap.mk₂_apply, modelProduct_apply]
    have hs : ⇑((trivializationAt (MLF s)
        (Bundle.continuousMultilinearMap 𝕜 s F E) x₀).continuousLinearMapAt 𝕜 x) =
        fun y => (trivializationAt (MLF s)
          (Bundle.continuousMultilinearMap 𝕜 s F E) x₀ ⟨x, y⟩).2 := by
      change ⇑((trivializationAt (MLF s) _ x₀).linearMapAt 𝕜 x) = _
      exact (trivializationAt (MLF s) _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hxs
    have hq' : ⇑((trivializationAt (MLF q)
        (Bundle.continuousMultilinearMap 𝕜 q F E) x₀).continuousLinearMapAt 𝕜 x) =
        fun y => (trivializationAt (MLF q)
          (Bundle.continuousMultilinearMap 𝕜 q F E) x₀ ⟨x, y⟩).2 := by
      change ⇑((trivializationAt (MLF q) _ x₀).linearMapAt 𝕜 x) = _
      exact (trivializationAt (MLF q) _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hxq
    change _ = (⇑((trivializationAt (MLF s) (Bundle.continuousMultilinearMap 𝕜 s F E) x₀
        ).continuousLinearMapAt 𝕜 x) α) (w ∘ Fin.castAdd q) *
      (⇑((trivializationAt (MLF q) (Bundle.continuousMultilinearMap 𝕜 q F E) x₀
        ).continuousLinearMapAt 𝕜 x) β) (w ∘ Fin.natAdd s)
    rw [hs, hq']; rfl

theorem triv_toTensor_eq_modelFromTensorEquiv_symm {d : ℕ}
    (b : Module.Basis (Fin d) 𝕜 F) (s q : ℕ) (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (t : Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
         Bundle.continuousMultilinearMap 𝕜 q F E x) :
    letI := Bundle.TensorProduct.tensorFiberTopology
      𝕜 (MLF s) (MLF q)
      (Bundle.continuousMultilinearMap 𝕜 s F E)
      (Bundle.continuousMultilinearMap 𝕜 q F E)
    letI := Bundle.TensorProduct.fiberBundle
      (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
      (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
      (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
    (modelFromTensorEquiv (𝕜 := 𝕜) (F := F) b s q).symm
      ((trivializationAt (MLF (s + q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
        ⟨x, fromTensor s q x t⟩).2) =
    (trivializationAt ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) x₀
      ⟨x, t⟩).2 := by
  let := Bundle.TensorProduct.tensorFiberTopology
    𝕜 (MLF s) (MLF q)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E)
  let := Bundle.TensorProduct.fiberBundle
    (𝕜 := 𝕜) (B := B) (F₁ := MLF s) (F₂ := MLF q)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)
  rw [triv_fromTensor_eq_modelFromTensor s q x₀ x hx t]
  exact (modelFromTensorEquiv b s q).symm_apply_apply _

end Bundle.continuousMultilinearMap

namespace CalabiYau.MultilinearSection

variable (n : WithTop ℕ∞) [ContMDiffVectorBundle n F E IB]

section Product

variable {s q : ℕ}

noncomputable def product
    (α : MultilinearSection 𝕜 F IB E n s)
    (β : MultilinearSection 𝕜 F IB E n q) :
    MultilinearSection 𝕜 F IB E n (s + q) :=
  ⟨fun x => (α x).productFun (β x), by
    let d := Module.finrank 𝕜 F
    let b : Module.Basis (Fin d) 𝕜 F := Module.finBasis 𝕜 F
    rw [contMDiff_multilinearSection_iff_coord E n b]
    intro σ x₀
    have hα := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (α x : Bundle.continuousMultilinearMap 𝕜 s F E x))).mp α.contMDiff)
    have hβ := ((contMDiff_multilinearSection_iff_coord E n b
      (fun x => (β x : Bundle.continuousMultilinearMap 𝕜 q F E x))).mp β.contMDiff)
    simp_rw [Bundle.continuousMultilinearMap.triv_coord_product b σ x₀ _ (α _) (β _)]
    exact (contMDiffAt_const (c := ContinuousLinearMap.mul 𝕜 𝕜).clm_apply
      (hα (σ ∘ Fin.castAdd q) x₀)).clm_apply (hβ (σ ∘ Fin.natAdd s) x₀)⟩

@[simp] theorem product_zero (α : MultilinearSection 𝕜 F IB E n s) :
    product (IB := IB) n α (0 : MultilinearSection 𝕜 F IB E n q)
      = (0 : MultilinearSection 𝕜 F IB E n (s + q)) := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  change Bundle.continuousMultilinearMap.productFun (α x)
    ((0 : MultilinearSection 𝕜 F IB E n q) x) V = _
  simp [Bundle.continuousMultilinearMap.product_fun_apply, ContMDiffSection.coe_zero]

theorem product_add_left (α β : MultilinearSection 𝕜 F IB E n s)
    (γ : MultilinearSection 𝕜 F IB E n q) :
    product (IB := IB) n (α + β) γ
      = product (IB := IB) n α γ + product (IB := IB) n β γ := by
  refine DFunLike.ext _ _ fun x => ?_
  ext V
  change Bundle.continuousMultilinearMap.productFun ((α + β) x) (γ x) V
    = Bundle.continuousMultilinearMap.productFun (α x) (γ x) V
      + Bundle.continuousMultilinearMap.productFun (β x) (γ x) V
  have hab : (α + β) x = α x + β x := rfl
  rw [hab]
  simp [Bundle.continuousMultilinearMap.product_fun_apply,
    add_apply, add_mul]

end Product

section TensorProductInstances

variable {s q : ℕ}

local instance multilinearTensorFiberTopology {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    ∀ x : B, TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                                Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.tensorFiberTopology 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (Bundle.continuousMultilinearMap 𝕜 s F E)
    (Bundle.continuousMultilinearMap 𝕜 q F E)

local instance multilinearTensorFiberBundle {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    FiberBundle
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.fiberBundle (𝕜 := 𝕜)
    (F₁ := ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (F₂ := ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)

local instance multilinearTensorVectorBundle {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    {B : Type*} [TopologicalSpace B] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] (s q : ℕ) :
    VectorBundle 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 ⊗[𝕜]
       ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  Bundle.TensorProduct.vectorBundle (𝕜 := 𝕜)
    (F₁ := ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (F₂ := ContinuousMultilinearMap 𝕜 (fun _ : Fin q => F) 𝕜)
    (E₁ := Bundle.continuousMultilinearMap 𝕜 s F E)
    (E₂ := Bundle.continuousMultilinearMap 𝕜 q F E)

section BundleEquiv

open Bundle.continuousMultilinearMap

noncomputable def multilinearTensorFiberwiseEquiv (s q : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + q) F E x ≃ₗ[𝕜]
    TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) (s + q) x).toLinearEquiv.trans
    ((modelFromTensorEquiv (Module.finBasis 𝕜 F) s q).symm.trans
      (TensorProduct.congr
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) s x).symm.toLinearEquiv
        (continuousLinearEquivAt (𝕜 := 𝕜) (F := F) (E := E) q x).symm.toLinearEquiv))

theorem multilinearTensorFiberwiseEquiv_symm_eq (s q : ℕ) (x : B)
    (t : TensorProduct 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (Bundle.continuousMultilinearMap 𝕜 q F E x)) :
    (multilinearTensorFiberwiseEquiv s q x).symm t = fromTensor s q x t := by
  induction t using TensorProduct.induction_on with
  | zero => simp [multilinearTensorFiberwiseEquiv, fromTensor]
  | add _ _ ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  | tmul a b =>
    simp only [multilinearTensorFiberwiseEquiv, LinearEquiv.trans_symm,
      LinearEquiv.symm_symm, LinearEquiv.trans_apply]
    simp only [fromTensor, TensorProduct.lift.tmul, productBilinear, LinearMap.mk₂_apply]
    rfl

noncomputable def modelFromTensorCLM (s q : ℕ) :
    ((MLF s) ⊗[𝕜] (MLF q)) →L[𝕜] (MLF (s + q)) :=
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) s
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) q
  haveI : FiniteDimensional 𝕜 ((MLF s) ⊗[𝕜] (MLF q)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  (modelFromTensor (𝕜 := 𝕜) (F := F) s q).toContinuousLinearMap

noncomputable def modelToTensorCLM (s q : ℕ) :
    (MLF (s + q)) →L[𝕜] ((MLF s) ⊗[𝕜] (MLF q)) :=
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) s
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) q
  haveI : FiniteDimensional 𝕜 ((MLF s) ⊗[𝕜] (MLF q)) :=
    Module.Finite.tensorProduct 𝕜 _ _
  haveI := continuousMultilinearMap_finiteDimensional (𝕜 := 𝕜) (F := F) (s + q)
  LinearMap.toContinuousLinearMap
    (modelFromTensorEquiv (𝕜 := 𝕜) (F := F) (Module.finBasis 𝕜 F) s q).symm.toLinearMap

theorem trivializationAt_multilinearTensorFiberwiseEquiv_eq (s q : ℕ) (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (α : Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) :
    (trivializationAt ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) x₀
      ⟨x, multilinearTensorFiberwiseEquiv s q x α⟩).2 =
    modelToTensorCLM s q
      ((trivializationAt (MLF (s + q))
        (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) x₀
        ⟨x, α⟩).2) := by
  set t := multilinearTensorFiberwiseEquiv s q x α
  have hα : α = fromTensor s q x t := by
    rw [← multilinearTensorFiberwiseEquiv_symm_eq]
    exact ((multilinearTensorFiberwiseEquiv s q x).symm_apply_apply α).symm
  rw [hα]
  exact (triv_toTensor_eq_modelFromTensorEquiv_symm (Module.finBasis 𝕜 F) s q x₀ x hx t).symm

omit [ContMDiffVectorBundle n F E IB] in
theorem multilinearTensorFiberwiseEquiv_smooth
    (_hE : ContMDiffVectorBundle n F E IB) :
    ContMDiff
      (IB.prod 𝓘(𝕜, MLF (s + q)))
      (IB.prod 𝓘(𝕜, (MLF s) ⊗[𝕜] (MLF q)))
      n
      (fun p : TotalSpace (MLF (s + q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) =>
        (⟨p.1, multilinearTensorFiberwiseEquiv s q p.1 p.2⟩ :
          TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x))) := by
  let _ := _hE
  let := _hE
  have : ContMDiffVectorBundle n
      ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) IB := inferInstance
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜, MLF (s + q)))
        𝓘(𝕜, MLF (s + q)) n
        (fun p => (trivializationAt (MLF (s + q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const (c := modelToTensorCLM s q)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt F E p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (mem_baseSet_trivializationAt F E p₀.proj)
    ] with p hp
    exact trivializationAt_multilinearTensorFiberwiseEquiv_eq s q p₀.proj p.proj hp p.snd

omit [ContMDiffVectorBundle n F E IB] in
theorem multilinearTensorFiberwiseEquiv_symm_smooth
    (_hE : ContMDiffVectorBundle n F E IB) :
    ContMDiff
      (IB.prod 𝓘(𝕜, (MLF s) ⊗[𝕜] (MLF q)))
      (IB.prod 𝓘(𝕜, MLF (s + q)))
      n
      (fun p : TotalSpace ((MLF s) ⊗[𝕜] (MLF q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 q F E x) =>
        (⟨p.1, (multilinearTensorFiberwiseEquiv s q p.1).symm p.2⟩ :
          TotalSpace (MLF (s + q))
            (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x))) := by
  let _ := _hE
  let := _hE
  let : NormedAddCommGroup ((MLF s) ⊗[𝕜] (MLF q)) :=
    Bundle.TensorProduct.instNormedAddCommGroupTensor
  let : NormedSpace 𝕜 ((MLF s) ⊗[𝕜] (MLF q)) :=
    Bundle.TensorProduct.instNormedSpaceModelTensor
  have : ContMDiffVectorBundle n
      ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) IB := inferInstance
  intro p₀
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact (contMDiff_proj
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x)).contMDiffAt
  · have h_fiber : ContMDiffAt
        (IB.prod 𝓘(𝕜, (MLF s) ⊗[𝕜] (MLF q)))
        𝓘(𝕜, (MLF s) ⊗[𝕜] (MLF q)) n
        (fun p => (trivializationAt ((MLF s) ⊗[𝕜] (MLF q))
          (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                     Bundle.continuousMultilinearMap 𝕜 q F E x) p₀.proj p).2)
        p₀ :=
      (contMDiffAt_totalSpace.mp contMDiffAt_id).2
    refine ((contMDiffAt_const (c := modelFromTensorCLM s q)).clm_apply
        h_fiber).congr_of_eventuallyEq ?_
    filter_upwards [
      ((trivializationAt F E p₀.proj).open_baseSet.preimage
        (FiberBundle.continuous_proj _ _)).mem_nhds
        (mem_baseSet_trivializationAt F E p₀.proj)
    ] with p hp
    rw [multilinearTensorFiberwiseEquiv_symm_eq]
    exact triv_fromTensor_eq_modelFromTensor s q p₀.proj p.proj hp p.snd

noncomputable def multilinearBundleTensorProductEquiv :
    ContMDiffVectorBundleEquiv 𝕜 IB n
      (MLF (s + q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 (s + q) F E x)
      ((MLF s) ⊗[𝕜] (MLF q))
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  ContMDiffVectorBundleEquiv.ofFiberwiseLinearEquiv
    (fun x => multilinearTensorFiberwiseEquiv s q x)
    (multilinearTensorFiberwiseEquiv_smooth n inferInstance)
    (multilinearTensorFiberwiseEquiv_symm_smooth n inferInstance)

noncomputable def toTensorProduct
    (α : MultilinearSection 𝕜 F IB E n (s + q)) :
    ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
      (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                 Bundle.continuousMultilinearMap 𝕜 q F E x) :=
  ⟨fun x => multilinearTensorFiberwiseEquiv s q x (α x),
   ((multilinearTensorFiberwiseEquiv_smooth n inferInstance).comp α.contMDiff).congr fun _ => rfl⟩

noncomputable def fromTensorProduct
    (γ : ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x)) :
    MultilinearSection 𝕜 F IB E n (s + q) :=
  ⟨fun x => (multilinearTensorFiberwiseEquiv s q x).symm (γ x),
   ((multilinearTensorFiberwiseEquiv_symm_smooth n inferInstance).comp γ.contMDiff).congr fun _
     => rfl⟩

theorem fromTensorProduct_toTensorProduct
    (α : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    (fromTensorProduct n (toTensorProduct n α)).1 x = α x :=
  (multilinearTensorFiberwiseEquiv s q x).symm_apply_apply (α x)

theorem toTensorProduct_fromTensorProduct
    (γ : ContMDiffSection IB ((MLF s) ⊗[𝕜] (MLF q)) n
            (fun x => Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                       Bundle.continuousMultilinearMap 𝕜 q F E x))
    (x : B) :
    (toTensorProduct n (fromTensorProduct n γ)).1 x = γ x :=
  (multilinearTensorFiberwiseEquiv s q x).apply_symm_apply (γ x)

theorem toTensorProduct_add
    (α β : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    (toTensorProduct n (α + β)).1 x =
    (toTensorProduct n α).1 x + (toTensorProduct n β).1 x :=
  map_add _ (α x) (β x)

theorem toTensorProduct_smulByFun
    (φ : B → 𝕜) (hφ : ContMDiff IB 𝓘(𝕜) n φ)
    (α : MultilinearSection 𝕜 F IB E n (s + q)) (x : B) :
    (toTensorProduct n (smulByFun n φ hφ α)).1 x =
    φ x • (toTensorProduct n α).1 x :=
  map_smul _ (φ x) (α x)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem fromTensorProduct_add
    (γ₁ γ₂ : ∀ x : B, Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                        Bundle.continuousMultilinearMap 𝕜 q F E x) (x : B) :
    fromTensor s q x (γ₁ x + γ₂ x) = fromTensor s q x (γ₁ x) + fromTensor s q x (γ₂ x) :=
  map_add _ _ _

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] in
theorem fromTensorProduct_smul
    (c : 𝕜) (γ : ∀ x : B, Bundle.continuousMultilinearMap 𝕜 s F E x ⊗[𝕜]
                    Bundle.continuousMultilinearMap 𝕜 q F E x) (x : B) :
    fromTensor s q x (c • γ x) = c • fromTensor s q x (γ x) :=
  (fromTensor s q x).map_smul c (γ x)

end BundleEquiv

end TensorProductInstances

end CalabiYau.MultilinearSection

end
