-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Wedge.lean
-- Locally modified.
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
Modified by: Ziyang Qin
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Reindexing.Permutation
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Coordinates.MultiKroneckerDelta
public import CalabiYau.Mathlib.LinearAlgebra.Dual.PredualBasis
public import CalabiYau.Mathlib.LinearAlgebra.Alternating.ShuffleSplit
public import CalabiYau.Mathlib.Analysis.Normed.Module.Alternating.DomCongr
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Composition
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Curry
public import CalabiYau.Geometry.Manifold.Tensor.Product.Defs
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Coordinates.Basis
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Shuffle.Derivative
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Shuffle.Placement

@[expose] public section


noncomputable section

namespace ContinuousAlternatingMap

section wedge

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {M'' : Type*} [NormedAddCommGroup M''] [NormedSpace 𝕜 M'']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n p m' d : ℕ}

instance real_smulCommClass_continuousLinearMap {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    SMulCommClass ℝ ℝ (E →L[ℝ] F) :=
  ⟨by
    intro c d f
    ext x
    simp [smul_smul, mul_comm]⟩

def wedgeProduct (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') : M [⋀^Fin (m + n)]→L[𝕜] N'' :=
  uncurryFinAdd (f.compContinuousAlternatingMap₂ g h)

notation g "∧["f"]" h => wedgeProduct g h f
notation g "∧["𝕜"]" h => wedgeProduct g h (ContinuousLinearMap.mul 𝕜 𝕜)

noncomputable def covectorWedge (α : M →L[𝕜] 𝕜) (β : M [⋀^Fin n]→L[𝕜] 𝕜) :
    M [⋀^Fin (n + 1)]→L[𝕜] 𝕜 :=
  uncurryFin (α.smulRight β)

notation:70 α " ∧₁ " β => covectorWedge α β

theorem wedge_product_def {g : M [⋀^Fin m]→L[𝕜] N} {h : M [⋀^Fin n]→L[𝕜] N'}
    {f : N →L[𝕜] N' →L[𝕜] N''} {x : Fin (m + n) → M} :
    (g ∧[f] h) x = uncurryFinAdd (f.compContinuousAlternatingMap₂ g h) x :=
  rfl

open scoped TensorProduct

theorem factorial_nsmul_wedge_product_eq_alternatization
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (m + n) → M) :
    (m.factorial * n.factorial) • (g ∧[f] h) v =
      MultilinearMap.alternatization (tensorProductMap g h f).toMultilinearMap v := by
  let φ : N ⊗[𝕜] N' →ₗ[𝕜] N'' := TensorProduct.lift
    { toFun := fun n => (f n).toLinearMap
      map_add' := by intro x y; ext; simp [map_add]
      map_smul' := by intro c x; ext; simp [map_smul] }
  have hφ : ∀ a b, φ (a ⊗ₜ[𝕜] b) = f a b := fun _ _ => rfl
  have h_factor : (tensorProductMap g h f).toMultilinearMap =
      (φ.compMultilinearMap (MultilinearMap.domCoprod
        ↑g.toAlternatingMap ↑h.toAlternatingMap)).domDomCongr finSumFinEquiv := by
    ext x; simp [tensorProductMap, MultilinearMap.domDomCongr_apply,
      LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply, hφ]; rfl
  rw [h_factor, ContinuousAlternatingMap.alternatization_domDomCongr,
    LinearMap.compMultilinearMap_alternatization,
    MultilinearMap.domCoprod_alternization_eq, Fintype.card_fin, Fintype.card_fin]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.smul_apply, map_nsmul]
  change _ = _ • φ ((g.toAlternatingMap.domCoprod h.toAlternatingMap) (v ∘ ⇑finSumFinEquiv))
  rw [show φ ((g.toAlternatingMap.domCoprod h.toAlternatingMap) (v ∘ ⇑finSumFinEquiv)) =
    (uncurrySum (f.compContinuousAlternatingMap₂ g h)) (v ∘ ⇑finSumFinEquiv) from
    congr_fun (congr_arg DFunLike.coe
      (lift_comp_domCoprod_eq_uncurrySum g h f φ hφ)) _]; rfl

theorem wedge_product_eq_alternatization [CharZero 𝕜]
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (m + n) → M) :
    (g ∧[f] h) v = ((↑(m.factorial * n.factorial) : 𝕜))⁻¹ •
      MultilinearMap.alternatization (tensorProductMap g h f).toMultilinearMap v := by
  have h_ne : (↑(m.factorial * n.factorial) : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos n)).ne'
  have h_eq := factorial_nsmul_wedge_product_eq_alternatization g h f v
  rw [← h_eq, ← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀ h_ne]

theorem wedge_product_mul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] 𝕜} {x : Fin (m + n) → M} :
    (g ∧[ContinuousLinearMap.mul 𝕜 𝕜] h) x =
    uncurryFinAdd ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

theorem add_wedge (g₁ g₂ : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      ((g₁ + g₂) ∧[f] h) = (g₁ ∧[f] h) + (g₂ ∧[f] h) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    _root_.sum_apply, _root_.sum_apply, _root_.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  refine Quotient.inductionOn' σ fun σ₁ => ?_
  repeat rw [uncurrySum_summand_eval]
  repeat rw [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [add_apply, map_add]
  let u : Fin m → M := fun i => (x ∘ ⇑finSumFinEquiv) (σ₁ (Sum.inl i))
  let v : Fin n → M := fun i => (x ∘ ⇑finSumFinEquiv) (σ₁ (Sum.inr i))
  let z : N' := h v
  change Equiv.Perm.sign σ₁ • (f (g₁ u) z + f (g₂ u) z) =
    Equiv.Perm.sign σ₁ • f (g₁ u) z + Equiv.Perm.sign σ₁ • f (g₂ u) z
  exact smul_add (Equiv.Perm.sign σ₁) (f (g₁ u) z) (f (g₂ u) z)

theorem wedge_add (g : M [⋀^Fin m]→L[𝕜] N)
    (h₁ h₂ : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      (g ∧[f] (h₁ + h₂)) = (g ∧[f] h₁) + (g ∧[f] h₂) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    _root_.sum_apply, _root_.sum_apply, _root_.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  refine Quotient.inductionOn' σ fun σ₁ => ?_
  repeat rw [uncurrySum_summand_eval]
  repeat rw [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [add_apply, map_add, smul_add]

theorem smul_wedge (c : 𝕜) (g : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      ((c • g) ∧[f] h) = c • (g ∧[f] h) := by
  ext x
  rw [smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    _root_.sum_apply, _root_.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  refine Quotient.inductionOn' σ fun σ₁ => ?_
  repeat rw [uncurrySum_summand_eval]
  repeat rw [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [ContinuousAlternatingMap.smul_apply, f.map_smul, smul_comm]
  rfl

theorem wedge_smul (c : 𝕜) (g : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      (g ∧[f] (c • h)) = c • (g ∧[f] h) := by
  ext x
  rw [smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    _root_.sum_apply, _root_.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  refine Quotient.inductionOn' σ fun σ₁ => ?_
  repeat rw [uncurrySum_summand_eval]
  repeat rw [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [ContinuousAlternatingMap.smul_apply, ContinuousLinearMap.map_smul, smul_comm]

theorem norm_wedge_product_le (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    ‖g ∧[f] h‖ ≤
      Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * (‖f‖ * ‖g‖ * ‖h‖) := by
  refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
  change ‖uncurryFinAdd (f.compContinuousAlternatingMap₂ g h) v‖ ≤ _
  rw [uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
      _root_.sum_apply]
  have key : ∀ q : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
      ‖uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) q
          (v ∘ ⇑finSumFinEquiv)‖ ≤ (‖f‖ * ‖g‖ * ‖h‖) * ∏ i, ‖v i‖ := by
    intro q
    induction q using Quotient.inductionOn' with | h σ =>
    rw [uncurrySum_summand_eval]
    have hsign : ∀ z : N'', ‖(Equiv.Perm.sign σ : ℤˣ) • z‖ = ‖z‖ := fun z => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
    rw [hsign]
    change ‖f (g (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i))))
            (h (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i))))‖ ≤ _
    calc ‖f (g _) (h _)‖
        ≤ ‖f‖ * ‖g (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i)))‖ *
            ‖h (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i)))‖ := f.le_opNorm₂ _ _
      _ ≤ ‖f‖ * (‖g‖ * ∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i))‖) *
            (‖h‖ * ∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i))‖) := by
          gcongr
          · exact g.le_opNorm _
          · exact h.le_opNorm _
      _ = ‖f‖ * ‖g‖ * ‖h‖ *
            ((∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i))‖) *
              ∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i))‖) := by ring
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ k : Fin m ⊕ Fin n, ‖(v ∘ ⇑finSumFinEquiv) (σ k)‖ := by
          rw [← Fintype.prod_sum_type (fun k => ‖(v ∘ ⇑finSumFinEquiv) (σ k)‖)]
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ k : Fin m ⊕ Fin n, ‖(v ∘ ⇑finSumFinEquiv) k‖ := by
          rw [Equiv.prod_comp σ (fun k => ‖(v ∘ ⇑finSumFinEquiv) k‖)]
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ i, ‖v i‖ := by
          simp only [Function.comp_apply]
          rw [Equiv.prod_comp finSumFinEquiv (fun i => ‖v i‖)]
  calc ‖∑ q, uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) q
            (v ∘ ⇑finSumFinEquiv)‖
      ≤ ∑ q, ‖uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) q
            (v ∘ ⇑finSumFinEquiv)‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
          (‖f‖ * ‖g‖ * ‖h‖) * ∏ i, ‖v i‖ := Finset.sum_le_sum fun q _ => key q
    _ = (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) : ℝ) *
          ((‖f‖ * ‖g‖ * ‖h‖) * ∏ i, ‖v i‖) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * (‖f‖ * ‖g‖ * ‖h‖) *
          ∏ i, ‖v i‖ := by ring

theorem isBoundedBilinearMap_wedgeProduct (f : N →L[𝕜] N' →L[𝕜] N'') :
    IsBoundedBilinearMap 𝕜 (fun p : (M [⋀^Fin m]→L[𝕜] N) × (M [⋀^Fin n]→L[𝕜] N') =>
      wedgeProduct p.1 p.2 f) := by
  refine { add_left := ?_, smul_left := ?_, add_right := ?_, smul_right := ?_, bound := ?_ }
  · intro g₁ g₂ h
    exact add_wedge g₁ g₂ h f
  · intro c g h
    exact smul_wedge c g h f
  · intro g h₁ h₂
    exact wedge_add g h₁ h₂ f
  · intro c g h
    exact wedge_smul c g h f
  · refine ⟨(Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) : ℝ) * ‖f‖ + 1,
      by positivity, ?_⟩
    intro g h
    calc
      ‖wedgeProduct g h f‖ ≤
          (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) : ℝ) *
            (‖f‖ * ‖g‖ * ‖h‖) := norm_wedge_product_le g h f
      _ ≤ ((Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) : ℝ) * ‖f‖ + 1) *
          ‖g‖ * ‖h‖ := by
        nlinarith [norm_nonneg g, norm_nonneg h]

noncomputable def wedgeProductL (f : N →L[𝕜] N' →L[𝕜] N'') :
    (M [⋀^Fin m]→L[𝕜] N) →L[𝕜] (M [⋀^Fin n]→L[𝕜] N') →L[𝕜]
        (M [⋀^Fin (m + n)]→L[𝕜] N'') :=
  LinearMap.mkContinuous₂
    { toFun := fun g =>
        { toFun := fun h => wedgeProduct g h f
          map_add' := fun h₁ h₂ => wedge_add g h₁ h₂ f
          map_smul' := fun c h => wedge_smul c g h f }
      map_add' := fun g₁ g₂ => by ext h : 1; exact add_wedge g₁ g₂ h f
      map_smul' := fun c g => by ext h : 1; exact smul_wedge c g h f }
    (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * ‖f‖ + 1) fun g h => by
      change ‖wedgeProduct g h f‖ ≤ _
      have hwedge := norm_wedge_product_le g h f
      nlinarith [hwedge, norm_nonneg g, norm_nonneg h, norm_nonneg f]

@[simp] theorem wedge_productL_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N') :
    wedgeProductL f g h = wedgeProduct g h f := rfl

theorem uncurryFin_wedge_productL_precompL_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (v : Fin (m + n + 1) → M) :
    uncurryFin ((wedgeProductL f).precompL M g' h) v =
      ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
        wedgeProduct (g' (v k)) h f (k.removeNth v) := by
  rw [uncurryFin_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.precompL_apply, wedge_productL_apply]

theorem wedge_product_uncurryFin_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (v : Fin (m + n + 1) → M) :
    domDomCongr Fin.finAddFlipAssoc (wedgeProduct (uncurryFin g') h f) v =
      (wedgeProduct (uncurryFin g') h f) (v ∘ ⇑Fin.finAddFlipAssoc) := by
  rw [ContinuousAlternatingMap.domDomCongr_apply]

private def uncurryFinLeftExpandedSummand
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (w : Fin (m + 1) ⊕ Fin n → M)
    (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) (j : Fin (m + 1)) : N'' :=
  Equiv.Perm.sign τ •
    f (((-1 : ℤ) ^ j.val) •
        g' (w (τ (Sum.inl j)))
          (j.removeNth fun i : Fin (m + 1) => w (τ (Sum.inl i))))
      (h fun i : Fin n => w (τ (Sum.inr i)))

private theorem uncurrySum_summand_uncurryFin_left_expand_mk
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (w : Fin (m + 1) ⊕ Fin n → M)
    (τ : Equiv.Perm (Fin (m + 1) ⊕ Fin n)) :
    uncurrySum.summand (f.compContinuousAlternatingMap₂ (uncurryFin g') h)
        (Quotient.mk'' τ) w =
      ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ j := by
  rw [uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [uncurryFin_apply]
  let L : N →L[𝕜] N'' :=
    (ContinuousLinearMap.apply 𝕜 N'' (h fun i : Fin n => w (τ (Sum.inr i)))).comp f
  change Equiv.Perm.sign τ •
      L (∑ k : Fin (m + 1),
        (-1 : ℤ) ^ k.val •
          g' (w (τ (Sum.inl k))) (k.removeNth fun i : Fin (m + 1) => w (τ (Sum.inl i)))) =
    ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ j
  rw [_root_.map_sum L]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [L, uncurryFinLeftExpandedSummand]

private theorem derivShuffleLeft_expanded_summand_eq
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (v : Fin (m + n + 1) → M)
    (k : Fin (m + n + 1)) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    ((-1 : ℤ) ^ k.val) •
      (uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h)
        (Quotient.mk'' σ) ((k.removeNth v) ∘ ⇑finSumFinEquiv)) =
      uncurryFinLeftExpandedSummand f g' h
        ((v ∘ ⇑Fin.finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
        (derivShuffleLeftInsertRankedRepresentative k σ) (derivShuffleRank k σ) := by
  rw [uncurrySum_summand_eval]
  unfold uncurryFinLeftExpandedSummand
  rw [derivShuffleLeftInsertRankedRepresentative_sign]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [derivShuffleLeftInsertRankedRepresentative_inl_j]
  simp only [Function.comp_apply]
  have hleft :
      (fun i : Fin m =>
          ((v ∘ ⇑Fin.finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
            (derivShuffleLeftInsertRankedRepresentative k σ (Sum.inl ((derivShuffleRank k σ).succAbove i)))) =
        fun i : Fin m => ((k.removeNth v) ∘ ⇑finSumFinEquiv) (σ (Sum.inl i)) := by
    funext i
    rw [derivShuffleLeftInsertRankedRepresentative_inl_succAbove]
    simp only [Equiv.symm_trans, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
      Equiv.trans_apply, Function.comp_apply, Equiv.apply_symm_apply]
    rw [Fin.removeNth_apply]
  have hright :
      (fun i : Fin n =>
          ((v ∘ ⇑Fin.finAddFlipAssoc) ∘ ⇑finSumFinEquiv)
            (derivShuffleLeftInsertRankedRepresentative k σ (Sum.inr i))) =
        fun i : Fin n => ((k.removeNth v) ∘ ⇑finSumFinEquiv) (σ (Sum.inr i)) := by
    funext i
    rw [derivShuffleLeftInsertRankedRepresentative_inr]
    simp only [Equiv.symm_trans, Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd,
      Equiv.trans_apply, Function.comp_apply, Equiv.apply_symm_apply]
    rw [Fin.removeNth_apply]
  have hleft_remove :
      (derivShuffleRank k σ).removeNth
          (fun i : Fin (m + 1) =>
            v (Fin.finAddFlipAssoc (finSumFinEquiv (derivShuffleLeftInsertRankedRepresentative k σ (Sum.inl i))))) =
        fun i : Fin m => v (k.succAbove (finSumFinEquiv (σ (Sum.inl i)))) := by
    funext i
    simpa [Function.comp_apply, Fin.removeNth_apply] using congr_fun hleft i
  have hright_eval :
      (fun i : Fin n =>
          v (Fin.finAddFlipAssoc (finSumFinEquiv (derivShuffleLeftInsertRankedRepresentative k σ (Sum.inr i))))) =
        fun i : Fin n => v (k.succAbove (finSumFinEquiv (σ (Sum.inr i)))) := by
    funext i
    simpa [Function.comp_apply, Fin.removeNth_apply] using congr_fun hright i
  have hk_eval :
      v (Fin.finAddFlipAssoc (finSumFinEquiv (finSuccSumEquiv.symm k))) = v k := by
    change v (finSuccSumEquiv (finSuccSumEquiv.symm k)) = v k
    rw [Equiv.apply_symm_apply]
  rw [hleft_remove, hright_eval, hk_eval]
  simp only [Fin.removeNth_apply]
  simp only [Units.smul_def, smul_smul, mul_assoc]
  simp only [Int.reduceNeg, Units.val_mul, map_zsmul, FunLike.coe_smul,
    Pi.smul_apply, smul_smul, mul_assoc]
  congr 1
  rcases Nat.even_or_odd k.val with hq | hq <;>
    rcases Nat.even_or_odd (derivShuffleRank k σ).val with hj | hj
  · have hqu : ((-1 : ℤˣ) ^ k.val) = 1 := hq.neg_one_pow
    have hqz : (-1 : ℤ) ^ k.val = 1 := hq.neg_one_pow
    have hju : ((-1 : ℤˣ) ^ (derivShuffleRank k σ).val) = 1 := hj.neg_one_pow
    have hjz : (-1 : ℤ) ^ (derivShuffleRank k σ).val = 1 := hj.neg_one_pow
    simp [hqu, hqz, hju, hjz]
  · have hqu : ((-1 : ℤˣ) ^ k.val) = 1 := hq.neg_one_pow
    have hqz : (-1 : ℤ) ^ k.val = 1 := hq.neg_one_pow
    have hju : ((-1 : ℤˣ) ^ (derivShuffleRank k σ).val) = -1 := hj.neg_one_pow
    have hjz : (-1 : ℤ) ^ (derivShuffleRank k σ).val = -1 := hj.neg_one_pow
    simp [hqu, hqz, hju, hjz]
  · have hqu : ((-1 : ℤˣ) ^ k.val) = -1 := hq.neg_one_pow
    have hqz : (-1 : ℤ) ^ k.val = -1 := hq.neg_one_pow
    have hju : ((-1 : ℤˣ) ^ (derivShuffleRank k σ).val) = 1 := hj.neg_one_pow
    have hjz : (-1 : ℤ) ^ (derivShuffleRank k σ).val = 1 := hj.neg_one_pow
    simp [hqu, hqz, hju, hjz]
  · have hqu : ((-1 : ℤˣ) ^ k.val) = -1 := hq.neg_one_pow
    have hqz : (-1 : ℤ) ^ k.val = -1 := hq.neg_one_pow
    have hju : ((-1 : ℤˣ) ^ (derivShuffleRank k σ).val) = -1 := hj.neg_one_pow
    have hjz : (-1 : ℤ) ^ (derivShuffleRank k σ).val = -1 := hj.neg_one_pow
    simp [hqu, hqz, hju, hjz]

private lemma card_filter_comp_perm_local {n : ℕ} (e : Equiv.Perm (Fin n))
    (P : Fin n → Prop) [DecidablePred P] :
    (Finset.univ.filter (P ∘ ⇑e)).card = (Finset.univ.filter P).card := by
  have : Finset.univ.filter (P ∘ ⇑e) = (Finset.univ.filter P).map e.symm.toEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply, Function.comp_apply]
    exact ⟨fun h => ⟨e i, h, by simp⟩, fun ⟨j, hj, hji⟩ => by simpa [← hji]⟩
  rw [this, Finset.card_map]

private lemma derivShuffleRank_of_coset
    (k : Fin (m + n + 1)) (σ₁ σ₂ : Equiv.Perm (Fin m ⊕ Fin n))
    (h : (Quotient.mk'' (derivShuffleLeftInsertRepresentative k σ₁) :
        Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
      Quotient.mk'' (derivShuffleLeftInsertRepresentative k σ₂)) :
    derivShuffleRank k σ₁ = derivShuffleRank k σ₂ := by
  have hrel : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range
      (derivShuffleLeftInsertRepresentative k σ₁) (derivShuffleLeftInsertRepresentative k σ₂) := by
    rwa [← Quotient.eq]
  have hσrel : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range σ₁ σ₂ :=
    derivShuffleLeftInsertRepresentative_leftRel_injective k σ₁ σ₂ hrel
  rw [QuotientGroup.leftRel_apply] at hσrel
  obtain ⟨⟨τl, τr⟩, hblock⟩ := hσrel
  have hσ₂ : σ₂ = σ₁ * Equiv.Perm.sumCongr τl τr := by
    have hmul := inv_mul_eq_iff_eq_mul.mp hblock.symm
    rw [Equiv.Perm.sumCongrHom_apply] at hmul
    exact hmul
  apply Fin.ext
  simp only [derivShuffleRank, permFinOfSum, Equiv.permCongr_apply,
    finSumFinEquiv_symm_apply_castAdd]
  have hmap : (fun i : Fin m => (finSumFinEquiv (σ₂ (Sum.inl i))).val < k.val) =
      (fun i : Fin m => (finSumFinEquiv (σ₁ (Sum.inl i))).val < k.val) ∘ τl := by
    funext i
    have hel : finSumFinEquiv (σ₂ (Sum.inl i)) = finSumFinEquiv (σ₁ (Sum.inl (τl i))) := by
      congr 1
      erw [hσ₂]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      congr 1
    rw [hel]
    rfl
  have hfilter : (Finset.univ.filter (fun i : Fin m =>
        (finSumFinEquiv (σ₂ (Sum.inl i))).val < k.val)) =
      Finset.univ.filter ((fun i : Fin m =>
        (finSumFinEquiv (σ₁ (Sum.inl i))).val < k.val) ∘ τl) := by
    ext i
    simp [hmap]
  rw [hfilter]
  exact (card_filter_comp_perm_local τl (fun i : Fin m =>
    (finSumFinEquiv (σ₁ (Sum.inl i))).val < k.val)).symm

private lemma preimage_k_injective (τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n))
    (j₁ j₂ : Fin (m + 1))
    (h : (derivShuffleEquivLeft.symm (τ', j₁)).1 = (derivShuffleEquivLeft.symm (τ', j₂)).1) :
    j₁ = j₂ := by
  let k : Fin (m + n + 1) := (derivShuffleEquivLeft.symm (τ', j₁)).1
  let σ₁ : Equiv.Perm (Fin m ⊕ Fin n) := Quot.out (derivShuffleEquivLeft.symm (τ', j₁)).2
  let σ₂ : Equiv.Perm (Fin m ⊕ Fin n) := Quot.out (derivShuffleEquivLeft.symm (τ', j₂)).2
  have hk₂ : (derivShuffleEquivLeft.symm (τ', j₂)).1 = k := by
    simpa [k] using h.symm
  have hσ₁ : (derivShuffleEquivLeft.symm (τ', j₁)).2 = Quotient.mk'' σ₁ := by
    exact (Quot.out_eq (q := (derivShuffleEquivLeft.symm (τ', j₁)).2)).symm
  have hσ₂ : (derivShuffleEquivLeft.symm (τ', j₂)).2 = Quotient.mk'' σ₂ := by
    exact (Quot.out_eq (q := (derivShuffleEquivLeft.symm (τ', j₂)).2)).symm
  have hpre₁ : derivShuffleEquivLeft (k, Quotient.mk'' σ₁) = (τ', j₁) := by
    have hin : (k, Quotient.mk'' σ₁) = derivShuffleEquivLeft.symm (τ', j₁) :=
      Prod.ext rfl hσ₁.symm
    exact (congrArg derivShuffleEquivLeft hin).trans
      (derivShuffleEquivLeft.apply_symm_apply (τ', j₁))
  have hpre₂ : derivShuffleEquivLeft (k, Quotient.mk'' σ₂) = (τ', j₂) := by
    have hin : (k, Quotient.mk'' σ₂) = derivShuffleEquivLeft.symm (τ', j₂) :=
      Prod.ext hk₂.symm hσ₂.symm
    exact (congrArg derivShuffleEquivLeft hin).trans
      (derivShuffleEquivLeft.apply_symm_apply (τ', j₂))
  have hrank₁ : derivShuffleRank k σ₁ = j₁ := by
    have h₁ := congrArg Prod.snd hpre₁
    simpa using h₁
  have hrank₂ : derivShuffleRank k σ₂ = j₂ := by
    have h₂ := congrArg Prod.snd hpre₂
    simpa using h₂
  have hcoset₁ : (Quotient.mk'' (derivShuffleLeftInsertRepresentative k σ₁) :
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) = τ' := by
    have h₁ := congrArg Prod.fst hpre₁
    simpa using h₁
  have hcoset₂ : (Quotient.mk'' (derivShuffleLeftInsertRepresentative k σ₂) :
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) = τ' := by
    have h₂ := congrArg Prod.fst hpre₂
    simpa using h₂
  have hrank : derivShuffleRank k σ₁ = derivShuffleRank k σ₂ :=
    derivShuffleRank_of_coset k σ₁ σ₂ (hcoset₁.trans hcoset₂.symm)
  rw [← hrank₁, hrank, hrank₂]

private lemma coset_mul_sumCongr (τ₀ ρ : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (h : (Quotient.mk'' ρ : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
      Quotient.mk'' τ₀) :
    ∃ τl : Equiv.Perm (Fin (m + 1)), ∃ τr : Equiv.Perm (Fin n),
      ρ = τ₀ * Equiv.Perm.sumCongr τl τr := by
  have hrel : QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin (m + 1)) (Fin n)).range ρ τ₀ := by
    rwa [← Quotient.eq]
  rw [QuotientGroup.leftRel_apply] at hrel
  obtain ⟨⟨τl, τr⟩, hblock⟩ := hrel
  refine ⟨τl⁻¹, τr⁻¹, ?_⟩
  have h₁ : ρ * Equiv.Perm.sumCongr τl τr = τ₀ :=
    (inv_mul_eq_iff_eq_mul.mp hblock.symm).symm
  calc
    ρ = ρ * Equiv.Perm.sumCongr τl τr * Equiv.Perm.sumCongr τl⁻¹ τr⁻¹ := by
      have hprod : Equiv.Perm.sumCongr τl τr * Equiv.Perm.sumCongr τl⁻¹ τr⁻¹ = 1 := by
        ext x
        cases x <;> simp
      rw [mul_assoc, hprod, mul_one]
    _ = τ₀ * Equiv.Perm.sumCongr τl⁻¹ τr⁻¹ := by
      rw [h₁]
private def removeHole {m : ℕ} (p : Fin (m + 1)) (x : Fin (m + 1)) (hx : x ≠ p) : Fin m :=
  if h : x < p then
    ⟨x.val, by
      have hxmp : x.val < p.val := h
      have hpm : p.val ≤ m := Nat.lt_succ_iff.mp (by simpa using p.isLt)
      omega⟩
  else
    ⟨x.val - 1, by
      have hp : p.val < x.val := lt_of_le_of_ne (le_of_not_gt h) (by
        intro heq
        exact hx (Fin.ext heq.symm))
      have hxm : x.val ≤ m := Nat.lt_succ_iff.mp (by simpa using x.isLt)
      omega⟩

@[simp] private theorem succAbove_removeHole {m : ℕ} (p : Fin (m + 1)) (x : Fin (m + 1))
    (hx : x ≠ p) :
    p.succAbove (removeHole p x hx) = x := by
  by_cases h : x < p
  · let i : Fin m := ⟨x.val, by
        have hxmp : x.val < p.val := h
        have hpm : p.val ≤ m := Nat.lt_succ_iff.mp (by simpa using p.isLt)
        omega⟩
    have h1 : removeHole p x hx = i := by
      rw [removeHole]
      simp [h, i]
    rw [h1]
    have hcond : (Fin.castSucc i : Fin (m + 1)) < p := by
      simpa [i] using h
    rw [Fin.succAbove]
    rw [if_pos hcond]
    change i.castSucc = x
    apply Fin.ext
    simp [i]
  · have hp : p.val < x.val := lt_of_le_of_ne (le_of_not_gt h) (by
      intro heq
      exact hx (Fin.ext heq.symm))
    let i : Fin m := ⟨x.val - 1, by
        have hxm : x.val ≤ m := Nat.lt_succ_iff.mp (by simpa using x.isLt)
        omega⟩
    have h1 : removeHole p x hx = i := by
      rw [removeHole]
      simp [h, i]
    rw [h1]
    have hnot : ¬ (Fin.castSucc i : Fin (m + 1)) < p := by
      intro hc
      have hi : i.val = x.val - 1 := rfl
      have hcv : (Fin.castSucc i : Fin (m + 1)).val = x.val - 1 := rfl
      omega
    have hxsub : x.val - 1 + 1 = x.val := by omega
    rw [Fin.succAbove]
    rw [if_neg hnot]
    change i.succ = x
    apply Fin.ext
    simp [i, hxsub]

@[simp] private theorem removeHole_succAbove {m : ℕ} (p : Fin (m + 1)) (i : Fin m) :
    removeHole p (p.succAbove i) (Fin.succAbove_ne p i) = i := by
  apply Fin.ext
  by_cases h : (Fin.castSucc i : Fin (m + 1)) < p
  · have hcast : p.succAbove i = (Fin.castSucc i : Fin (m + 1)) := by
      rw [Fin.succAbove]
      rw [if_pos h]
    simp [removeHole, hcast, h]
  · have hsucc : p.succAbove i = (i.succ : Fin (m + 1)) := by
      rw [Fin.succAbove]
      rw [if_neg h]
    have hnot : ¬ (i.succ : Fin (m + 1)) < p := by
      intro hc
      have hcv : (Fin.castSucc i : Fin (m + 1)).val = i.val := rfl
      have hsv : (i.succ : Fin (m + 1)).val = i.val + 1 := rfl
      omega
    simp [removeHole, hsucc, hnot]

private def inducedPerm {m : ℕ} (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) : Equiv.Perm
    (Fin m) where
  toFun i := removeHole (τl j) (τl (j.succAbove i)) (by
    intro h
    exact Fin.succAbove_ne j i (Equiv.injective τl h))
  invFun i := removeHole j (τl.symm ((τl j).succAbove i)) (by
    intro h
    have h' : (τl j).succAbove i = τl j := by
      simpa using congrArg τl h
    exact Fin.succAbove_ne (τl j) i h')
  left_inv i := by
    simp [removeHole_succAbove]
  right_inv i := by
    simp [removeHole_succAbove]

private theorem inducedPerm_succAbove {m : ℕ} (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1))
    (i : Fin m) :
    (τl j).succAbove (inducedPerm τl j i) = τl (j.succAbove i) := by
  unfold inducedPerm
  exact succAbove_removeHole (τl j) (τl (j.succAbove i)) (by
    intro h
    exact Fin.succAbove_ne j i (Equiv.injective τl h))

private theorem inducedPerm_mul {m : ℕ} (τ₁ τ₂ : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) :
    inducedPerm (τ₁ * τ₂) j = inducedPerm τ₁ (τ₂ j) * inducedPerm τ₂ j := by
  ext i
  simp [inducedPerm]

private theorem inducedPerm_one {m : ℕ} (j : Fin (m + 1)) :
    inducedPerm (1 : Equiv.Perm (Fin (m + 1))) j = 1 := by
  ext i
  simp [inducedPerm]

private theorem succAbove_val_of_lt {m : ℕ} (j : Fin (m + 1)) (i : Fin m) (h : i.val < j.val) :
    (j.succAbove i).val = i.val := by
  rw [Fin.succAbove]
  rw [if_pos (by
    change i.val < j.val
    exact h)]
  rfl

private theorem succAbove_val_of_ge {m : ℕ} (j : Fin (m + 1)) (i : Fin m) (h : j.val ≤ i.val) :
    (j.succAbove i).val = i.val + 1 := by
  rw [Fin.succAbove]
  rw [if_neg]
  · rfl
  · intro hc
    have hcv : (Fin.castSucc i : Fin (m + 1)).val = i.val := rfl
    omega

private theorem removeHole_val_of_lt {m : ℕ} (p : Fin (m + 1)) (x : Fin (m + 1)) (hx : x ≠ p)
    (h : x.val < p.val) : (removeHole p x hx).val = x.val := by
  rw [removeHole]
  by_cases hx' : x < p
  · simp [hx']
  · have hnp : ¬ x.val < p.val := by
      intro hc
      exact hx' hc
    omega

private theorem removeHole_val_of_ge {m : ℕ} (p : Fin (m + 1)) (x : Fin (m + 1)) (hx : x ≠ p)
    (h : p.val < x.val) : (removeHole p x hx).val = x.val - 1 := by
  rw [removeHole]
  by_cases hx' : x < p
  · have hc : x.val < p.val := hx'
    omega
  · simp [hx']
private theorem inducedPerm_swap_left {m : ℕ} (j b : Fin (m + 1)) (hjb : j < b) :
    inducedPerm (Equiv.swap j b) j =
      Fin.cycleIcc (⟨j.val, by omega⟩ : Fin m) ⟨b.val - 1, by omega⟩ := by
  ext i
  dsimp [inducedPerm]
  by_cases hm : m = 0
  · subst hm
    exact Fin.elim0 i
  have : NeZero m := ⟨hm⟩
  have hbj1 : b.val - 1 < m := by omega
  have hjm : j.val < m := by omega
  by_cases h1 : i.val < j.val
  · have hsucc : (j.succAbove i).val = i.val := succAbove_val_of_lt j i h1
    have hne2 : j.succAbove i ≠ b := by
      intro hne
      have : i.val = b.val := by
        simpa [hsucc] using congrArg Fin.val hne
      omega
    have hswap : (Equiv.swap j b (j.succAbove i)).val = i.val := by
      simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2, hsucc]
    have hrm : (removeHole b (j.succAbove i) hne2).val = i.val := by
      have hx : (j.succAbove i).val < b.val := by
        rw [hsucc]
        omega
      rw [removeHole_val_of_lt b (j.succAbove i) hne2 hx]
      exact hsucc
    have hcyc : (Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i).val = i.val := by
      have hlt : i < ⟨j.val, hjm⟩ := h1
      exact congrArg Fin.val (Fin.cycleIcc_of_lt hlt)
    have hswapel : Equiv.swap j b (j.succAbove i) = j.succAbove i := by
      simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2]
    simpa [hswapel, hrm] using hcyc.symm
  · have hge : j.val ≤ i.val := le_of_not_gt h1
    by_cases h2 : i.val < b.val - 1
    · have hsucc : (j.succAbove i).val = i.val + 1 := succAbove_val_of_ge j i hge
      have hne2 : j.succAbove i ≠ b := by
        intro hne
        have : i.val + 1 = b.val := by
          simpa [hsucc] using congrArg Fin.val hne
        omega
      have hswap : (Equiv.swap j b (j.succAbove i)).val = i.val + 1 := by
        simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2, hsucc]
      have hrm : (removeHole b (j.succAbove i) hne2).val = i.val + 1 := by
        have hx : (j.succAbove i).val < b.val := by
          rw [hsucc]
          omega
        rw [removeHole_val_of_lt b (j.succAbove i) hne2 hx]
        exact hsucc
      have hcyc : (Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i).val = i.val + 1 := by
        have hle : (⟨j.val, hjm⟩ : Fin m) ≤ i := by
          exact hge
        have hlt2 : i < ⟨b.val - 1, hbj1⟩ := h2
        have hstep := congrArg Fin.val (Fin.cycleIcc_of_ge_of_lt hle hlt2)
        rw [hstep]
        exact Fin.val_add_one_of_lt' (by omega)
      have hswapel : Equiv.swap j b (j.succAbove i) = j.succAbove i := by
        simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2]
      simpa [hswapel, hrm] using hcyc.symm
    · have hge2 : b.val - 1 ≤ i.val := le_of_not_gt h2
      by_cases h3 : i.val = b.val - 1
      · have hsucc : (j.succAbove i).val = i.val + 1 := succAbove_val_of_ge j i hge
        have hb : j.succAbove i = b := by
          apply Fin.ext
          have hjvb : j.val < b.val := hjb
          have hbpos : 0 < b.val := lt_of_le_of_lt (Nat.zero_le j.val) hjvb
          simp [hsucc, h3]
          omega
        have hsa : Equiv.swap j b (j.succAbove i) = j := by
          rw [hb]
          simp
        have hrm' : (Equiv.swap j b (j.succAbove i)) ≠ (Equiv.swap j b) j := by
          intro hne
          have : j = b := by
            rw [hsa, Equiv.swap_apply_left] at hne
            exact hne
          exact hjb.ne this
        have hrm : (removeHole ((Equiv.swap j b) j) (Equiv.swap j b
          (j.succAbove i)) hrm').val = j.val := by
          have hx : (Equiv.swap j b (j.succAbove i)).val < (Equiv.swap j b j).val := by
            rw [hsa, Equiv.swap_apply_left]
            exact hjb
          exact (removeHole_val_of_lt (Equiv.swap j b j) (Equiv.swap j b
            (j.succAbove i)) hrm' hx).trans (congrArg Fin.val hsa)
        have hcyc : (Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i).val = j.val := by
          have hjvb : j.val < b.val := hjb
          have hbpos : 0 < b.val := lt_of_le_of_lt (Nat.zero_le j.val) hjvb
          have hle : (⟨j.val, hjm⟩ : Fin m) ≤ ⟨b.val - 1, hbj1⟩ := by
            exact (show j.val ≤ b.val - 1 from by omega)
          have hi : i = (⟨b.val - 1, hbj1⟩ : Fin m) := by
            apply Fin.ext
            exact h3
          have hlast : Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i = ⟨j.val, hjm⟩ := by
            rw [hi]
            exact Fin.cycleIcc_of_last hle
          exact congrArg Fin.val hlast
        exact hrm.trans hcyc.symm
      · have hge3 : b.val ≤ i.val := by omega
        have hsucc : (j.succAbove i).val = i.val + 1 := succAbove_val_of_ge j i hge
        have hne2 : j.succAbove i ≠ b := by
          intro hne
          have : i.val + 1 = b.val := by
            simpa [hsucc] using congrArg Fin.val hne
          omega
        have hswap : (Equiv.swap j b (j.succAbove i)).val = i.val + 1 := by
          simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2, hsucc]
        have hrm : (removeHole b (j.succAbove i) hne2).val = i.val := by
          have hx : b.val < (j.succAbove i).val := by
            rw [hsucc]
            omega
          rw [removeHole_val_of_ge b (j.succAbove i) hne2 hx]
          omega
        have hcyc : (Fin.cycleIcc (⟨j.val, hjm⟩ : Fin m) ⟨b.val - 1, hbj1⟩ i).val = i.val := by
          have hgt : (⟨b.val - 1, hbj1⟩ : Fin m) < i := by
            exact (show b.val - 1 < i.val from by omega)
          exact congrArg Fin.val (Fin.cycleIcc_of_gt hgt)
        have hswapel : Equiv.swap j b (j.succAbove i) = j.succAbove i := by
          simp [Equiv.swap_apply_def, Fin.succAbove_ne, hne2]
        simpa [hswapel, hrm] using hcyc.symm

private theorem inducedPerm_revPerm {m : ℕ} (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) :
    inducedPerm ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin
      (m + 1)))⁻¹)
      (Fin.rev j) =
      (Fin.revPerm : Equiv.Perm (Fin m)) * inducedPerm τl j * (Fin.revPerm : Equiv.Perm
        (Fin m))⁻¹ := by
  ext i
  have hconj : (Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin
    (m + 1)))⁻¹ =
      Fin.revPerm * τl * Fin.revPerm⁻¹ := rfl
  have hmain : ∀ x : Fin m, Fin.rev (inducedPerm τl j x) =
      (inducedPerm ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm
        (Fin (m + 1)))⁻¹) (Fin.rev j)) (Fin.rev x) := by
    intro x
    have hsa := inducedPerm_succAbove τl j x
    have hL : (Fin.rev (τl j)).succAbove (Fin.rev (inducedPerm τl j x)) =
        Fin.rev ((τl j).succAbove (inducedPerm τl j x)) := by
      simp [Fin.succAbove_rev_left]
    have hR : ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin
      (m + 1)))⁻¹)
          ((Fin.rev j).succAbove (Fin.rev x)) =
        Fin.rev (τl (j.succAbove x)) := by
      have hstep1 : ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm
        (Fin (m + 1)))⁻¹)
          ((Fin.rev j).succAbove (Fin.rev x)) =
          Fin.revPerm (τl (Fin.revPerm⁻¹ ((Fin.rev j).succAbove (Fin.rev x)))) := by
        rfl
      rw [hstep1]
      have hsj : Fin.rev (j.succAbove x) = (Fin.rev j).succAbove (Fin.rev x) := by
        simp [Fin.succAbove_rev_right, Fin.rev_rev]
      have hsj' : Fin.revPerm⁻¹ ((Fin.rev j).succAbove (Fin.rev x)) = j.succAbove x := by
        rw [← hsj]
        simp [Fin.rev_rev]
      rw [hsj']
      rfl
    have hleft : (Fin.rev (τl j)).succAbove (Fin.rev (inducedPerm τl j x)) =
        ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹)
          ((Fin.rev j).succAbove (Fin.rev x)) := by
      rw [hL, hsa, hR]
    have hright : (Fin.rev (τl j)).succAbove
          ((inducedPerm ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl *
            (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹) (Fin.rev j)) (Fin.rev x)) =
        ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹)
          ((Fin.rev j).succAbove (Fin.rev x)) := by
      simpa [hconj, Fin.rev_rev, Function.comp_apply] using
        inducedPerm_succAbove ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl *
          (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹) (Fin.rev j) (Fin.rev x)
    exact (Fin.succAbove_right_injective (p := Fin.rev (τl j))).eq_iff.mp (hleft.trans hright.symm)
  change (inducedPerm ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) * τl * (Fin.revPerm : Equiv.Perm
    (Fin (m + 1)))⁻¹) (Fin.rev j) i).val =
    (Fin.rev (inducedPerm τl j (Fin.rev i))).val
  have hsub := hmain (Fin.rev i)
  rw [hsub]
  congr 1
  simp [Fin.rev_rev]

private theorem sign_swap_ne {m : ℕ} (j b : Fin (m + 1)) (h : j ≠ b) :
    Equiv.Perm.sign (Equiv.swap j b) = (-1 : ℤˣ) := by
  simp [h]

private theorem neg_one_pow_ite (n : ℕ) : (-1 : ℤˣ) ^ n = if Even n then 1 else -1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (-1 : ℤˣ) ^ n.succ = (-1 : ℤˣ) ^ n * (-1 : ℤˣ) := by
      simpa using (pow_succ (a := (-1 : ℤˣ)) (n := n))
    rw [hstep, ih]
    by_cases hn : Even n
    · have hodd : ¬ Even (n + 1) := by
        rw [Nat.even_iff]
        have hn' : n % 2 = 0 := (Nat.even_iff.mp hn)
        omega
      simp [hn, hodd]
    · have hev : Even (n + 1) := by
        rw [Nat.even_iff]
        have hn' : n % 2 = 1 := by
          have hcases := Nat.mod_two_eq_zero_or_one n
          have hn0 : n % 2 ≠ 0 := by
            intro h0
            apply hn
            rw [Nat.even_iff]
            exact h0
          omega
        omega
      simp [hn, hev]

theorem neg_one_pow_add (n m : ℕ) : (-1 : ℤˣ) ^ (n + m) = (-1 : ℤˣ) ^ n * (-1 : ℤˣ) ^ m := by
  rw [neg_one_pow_ite (n := n + m), neg_one_pow_ite (n := n), neg_one_pow_ite (n := m)]
  have hmod : (n + m) % 2 = (n % 2 + m % 2) % 2 := by omega
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    simp [Nat.even_iff, hn, hm, hmod]

private theorem inducedPerm_swap_sign_left {m : ℕ} (j b : Fin (m + 1)) (hjb : j < b) :
    Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) =
      Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ (j.val + b.val) := by
  rw [inducedPerm_swap_left j b hjb]
  have hle : (⟨j.val, by omega⟩ : Fin m) ≤ ⟨b.val - 1, by omega⟩ := by
    exact (show j.val ≤ b.val - 1 from by omega)
  rw [Fin.sign_cycleIcc_of_le hle]
  rw [sign_swap_ne j b hjb.ne]
  have hcombine : (-1 : ℤˣ) * (-1 : ℤˣ) ^ (j.val + b.val) = (-1 : ℤˣ) ^ (1 + j.val + b.val) := by
    rw [mul_comm]
    have hstep : (-1 : ℤˣ) ^ (j.val + b.val).succ = (-1 : ℤˣ) ^ (j.val + b.val) * (-1 : ℤˣ) := by
      simpa using (pow_succ (a := (-1 : ℤˣ)) (n := j.val + b.val))
    rw [← hstep]
    rw [show (j.val + b.val).succ = 1 + j.val + b.val from by omega]
  rw [hcombine]
  have hpow_ite (n : ℕ) : (-1 : ℤˣ) ^ n = if Even n then 1 else -1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : (-1 : ℤˣ) ^ n.succ = (-1 : ℤˣ) ^ n * (-1 : ℤˣ) := by
        simpa using (pow_succ (a := (-1 : ℤˣ)) (n := n))
      rw [hstep, ih]
      by_cases hn : Even n
      · have hodd : ¬ Even (n + 1) := by
          rw [Nat.even_iff]
          have hn' : n % 2 = 0 := (Nat.even_iff.mp hn)
          omega
        simp [hn, hodd]
      · have hev : Even (n + 1) := by
          rw [Nat.even_iff]
          have hn' : n % 2 = 1 := by
            have hcases := Nat.mod_two_eq_zero_or_one n
            have hn0 : n % 2 ≠ 0 := by
              intro h
              apply hn
              rw [Nat.even_iff]
              exact h
            omega
          omega
        simp [hn, hev]
  have hjvb : j.val < b.val := hjb
  have hmod : (b.val - 1 - j.val) % 2 = (1 + j.val + b.val) % 2 := by omega
  have hvals : (⟨b.val - 1, by omega⟩ : Fin m).val - (⟨j.val,
    by omega⟩ : Fin m).val = b.val - 1 - j.val := by
    rw [show (⟨b.val - 1, by omega⟩ : Fin m).val = b.val - 1 from rfl,
      show (⟨j.val, by omega⟩ : Fin m).val = j.val from rfl]
  rw [hvals]
  change (-1 : ℤˣ) ^ (b.val - 1 - j.val) = (-1 : ℤˣ) ^ (1 + j.val + b.val)
  simp [hpow_ite, Nat.even_iff, hmod]

private theorem inducedPerm_swap_sign_right {m : ℕ} (j b : Fin (m + 1)) (hbj : b < j) :
    Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) =
      Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ (j.val + b.val) := by
  have hrev := inducedPerm_revPerm (τl := Equiv.swap j b) (j := j)
  have hconj : (Fin.revPerm : Equiv.Perm (Fin (m + 1))) * Equiv.swap j b *
    (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹ =
      Equiv.swap (Fin.rev j) (Fin.rev b) := by
    ext x
    by_cases hx : x = Fin.rev j
    · subst hx
      simp [Fin.revPerm, Fin.rev_rev]
    · by_cases hx' : x = Fin.rev b
      · subst hx'
        simp [Fin.revPerm, Fin.rev_rev]
      · have hrnj : Fin.rev x ≠ j := by
          intro h
          apply hx
          rw [← h]
          simp [Fin.rev_rev]
        have hrnb : Fin.rev x ≠ b := by
          intro h
          apply hx'
          rw [← h]
          simp [Fin.rev_rev]
        simp [Equiv.swap_apply_def, hx, hx', hrnj, hrnb, Fin.rev_rev]
  have hjv : (Fin.rev j).val = m - j.val := by
    change (m + 1) - (j.val + 1) = m - j.val
    omega
  have hbv : (Fin.rev b).val = m - b.val := by
    change (m + 1) - (b.val + 1) = m - b.val
    omega
  have hrevlt : Fin.rev j < Fin.rev b := by
    change (Fin.rev j).val < (Fin.rev b).val
    rw [hjv, hbv]
    omega
  have hsig1 := inducedPerm_swap_sign_left (j := Fin.rev j) (b := Fin.rev b) hrevlt
  have hsign_conj : Equiv.Perm.sign (Equiv.swap (Fin.rev j) (Fin.rev b)) = Equiv.Perm.sign
    (Equiv.swap j b) := by
    rw [sign_swap_ne (Fin.rev j) (Fin.rev b) (ne_of_lt hrevlt),
      sign_swap_ne j b (ne_of_lt hbj).symm]
  have hsign_rev : Equiv.Perm.sign ((Fin.revPerm : Equiv.Perm (Fin m)) * inducedPerm
    (Equiv.swap j b) j * (Fin.revPerm : Equiv.Perm (Fin m))⁻¹) =
      Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    have h1 : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) * (Equiv.Perm.sign
      (Fin.revPerm : Equiv.Perm (Fin m)) * Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j)) =
        Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) := by
      rw [← mul_assoc]
      have hs : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) * Equiv.Perm.sign
        (Fin.revPerm : Equiv.Perm (Fin m)) = 1 := by
        rw [← Equiv.Perm.sign_mul]
        have hsq : (Fin.revPerm : Equiv.Perm (Fin m)) * (Fin.revPerm : Equiv.Perm (Fin m)) = 1 := by
          ext x
          simp
        rw [hsq, Equiv.Perm.sign_one]
      rw [hs, one_mul]
    simpa [mul_assoc, mul_comm, mul_left_comm] using h1
  have hmain : Equiv.Perm.sign (inducedPerm ((Fin.revPerm : Equiv.Perm (Fin
    (m + 1))) * Equiv.swap j b * (Fin.revPerm : Equiv.Perm (Fin (m + 1)))⁻¹) (Fin.rev j)) =
      Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) := by
    rw [hrev]
    exact hsign_rev
  rw [← hmain]
  rw [hconj]
  rw [hsig1]
  rw [hsign_conj]
  change Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ ((Fin.rev j).val + (Fin.rev b).val) =
    Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ (j.val + b.val)
  congr 1
  have hmod : ((m - j.val) + (m - b.val)) % 2 = (j.val + b.val) % 2 := by omega
  change (-1 : ℤˣ) ^ ((Fin.rev j).val + (Fin.rev b).val) = (-1 : ℤˣ) ^ (j.val + b.val)
  simp [neg_one_pow_ite, Nat.even_iff, hmod]

private theorem inducedPerm_swap_sign {m : ℕ} (j b : Fin (m + 1)) :
    Equiv.Perm.sign (inducedPerm (Equiv.swap j b) j) =
      Equiv.Perm.sign (Equiv.swap j b) * (-1 : ℤˣ) ^ (j.val + b.val) := by
  by_cases h : j = b
  · subst h
    have h1 : inducedPerm (Equiv.swap j j) j = (1 : Equiv.Perm (Fin m)) := by
      have hswap : Equiv.swap j j = (1 : Equiv.Perm (Fin (m + 1))) := Equiv.swap_self j
      rw [hswap]
      exact inducedPerm_one j
    rw [h1]
    simp only [Equiv.Perm.sign_one, Equiv.swap_self, Equiv.Perm.sign_refl, one_mul]
    have hjj : Even (j.val + j.val) := by
      rw [Nat.even_iff]
      omega
    rw [show (-1 : ℤˣ) ^ (j.val + j.val) = 1 from by
      rw [neg_one_pow_ite (n := j.val + j.val)]
      simp [hjj]]
  · rcases lt_or_gt_of_ne h with hjb | hbj
    · exact inducedPerm_swap_sign_left j b hjb
    · exact inducedPerm_swap_sign_right j b hbj

private theorem removeHole_congr {m : ℕ} (p : Fin (m + 1)) {x y : Fin (m + 1)} (hxy : x = y)
    (hx : x ≠ p) (hy : y ≠ p) : removeHole p x hx = removeHole p y hy := by
  subst y
  apply Fin.ext
  by_cases hlt : x < p
  · rw [removeHole_val_of_lt p x hx hlt]
  · have hpne : p ≠ x := by
      intro h
      exact hx h.symm
    have hvne : p.val ≠ x.val := by
      intro h
      exact hpne (Fin.ext h)
    have hge : p.val < x.val := lt_of_le_of_ne (le_of_not_gt hlt) hvne
    rw [removeHole_val_of_ge p x hx hge]

private theorem inducedPerm_swap_away {m : ℕ} (a b j' : Fin (m + 1)) (haj : j' ≠ a) (hbj : j' ≠ b) :
    inducedPerm (Equiv.swap a b) j' =
      Equiv.swap (removeHole j' a (Ne.symm haj)) (removeHole j' b (Ne.symm hbj)) := by
  ext i
  dsimp [inducedPerm]
  by_cases hia : j'.succAbove i = a
  · have hne : Equiv.swap a b (j'.succAbove i) ≠ j' := by
      rw [hia]
      intro h
      have hb : b = j' := by
        simpa [Equiv.swap_apply_def] using h
      exact (Ne.symm hbj) hb
    have hrm : (removeHole j' (Equiv.swap a b (j'.succAbove i)) hne).val = (removeHole j' b
      (Ne.symm hbj)).val := by
      have harg : Equiv.swap a b (j'.succAbove i) = b := by
        rw [hia]
        simp
      exact congrArg Fin.val (removeHole_congr j' harg hne (Ne.symm hbj))
    have hi : i = removeHole j' a (Ne.symm haj) := by
      have hsa1 : j'.succAbove (removeHole j' a (Ne.symm haj)) = a := succAbove_removeHole j' a
        (Ne.symm haj)
      exact ((Fin.succAbove_right_injective (p := j')).eq_iff.mp (hsa1.trans hia.symm)).symm
    rw [hi]
    simp [Equiv.swap_apply_def, haj, hbj]
  · by_cases hib : j'.succAbove i = b
    · have hne : Equiv.swap a b (j'.succAbove i) ≠ j' := by
        rw [hib]
        intro h
        have ha : a = j' := by
          simpa [Equiv.swap_apply_def] using h
        exact (Ne.symm haj) ha
      have hrm : (removeHole j' (Equiv.swap a b (j'.succAbove i)) hne).val = (removeHole j' a
        (Ne.symm haj)).val := by
        have harg : Equiv.swap a b (j'.succAbove i) = a := by
          rw [hib]
          simp
        exact congrArg Fin.val (removeHole_congr j' harg hne (Ne.symm haj))
      have hi : i = removeHole j' b (Ne.symm hbj) := by
        have hsa1 : j'.succAbove (removeHole j' b
          (Ne.symm hbj)) = b := succAbove_removeHole j' b (Ne.symm hbj)
        exact ((Fin.succAbove_right_injective (p := j')).eq_iff.mp (hsa1.trans hib.symm)).symm
      have hba : b ≠ a := by
        intro hba
        exact hia (hib.trans hba)
      rw [hi]
      simp [Equiv.swap_apply_def, haj, hbj, hba]
    · have hfix : Equiv.swap a b (j'.succAbove i) = j'.succAbove i := by
        simp [Equiv.swap_apply_def, hia, hib]
      have hne : Equiv.swap a b (j'.succAbove i) ≠ j' := by
        intro h
        exact Fin.succAbove_ne j' i (hfix.symm.trans h)
      have hrm : (removeHole j' (Equiv.swap a b (j'.succAbove i)) hne).val = i.val := by
        have h1 : removeHole j' (Equiv.swap a b (j'.succAbove i)) hne = removeHole j'
          (j'.succAbove i) (Fin.succAbove_ne j' i) :=
          removeHole_congr j' hfix hne (Fin.succAbove_ne j' i)
        have h2 : (removeHole j' (j'.succAbove i) (Fin.succAbove_ne j' i)).val = i.val :=
          congrArg Fin.val (removeHole_succAbove j' i)
        exact (congrArg Fin.val h1).trans h2
      have hne_a : i ≠ removeHole j' a (Ne.symm haj) := by
        intro h
        have : j'.succAbove (removeHole j' a (Ne.symm haj)) = j'.succAbove i := by rw [h]
        have : j'.succAbove i = a := by
          rw [succAbove_removeHole] at this
          exact this.symm
        exact hia this
      have hne_b : i ≠ removeHole j' b (Ne.symm hbj) := by
        intro h
        have : j'.succAbove (removeHole j' b (Ne.symm hbj)) = j'.succAbove i := by rw [h]
        have : j'.succAbove i = b := by
          rw [succAbove_removeHole] at this
          exact this.symm
        exact hib this
      simp [Equiv.swap_apply_def, hne_a, hne_b, haj, hbj, hia, hib]

private theorem inducedPerm_swap_sign' {m : ℕ} (a b j' : Fin (m + 1)) :
    Equiv.Perm.sign (inducedPerm (Equiv.swap a b) j') =
      Equiv.Perm.sign (Equiv.swap a b) * (-1 : ℤˣ) ^ (j'.val + (Equiv.swap a b j').val) := by
  by_cases hab : a = b
  · rw [hab]
    simp only [Equiv.swap_self, Equiv.Perm.sign_refl, Equiv.refl_apply, one_mul]
    have hrefl : inducedPerm (Equiv.refl (Fin (m + 1))) j' = 1 := by
      change inducedPerm (1 : Equiv.Perm (Fin (m + 1))) j' = 1
      exact inducedPerm_one j'
    rw [hrefl]
    simp only [Equiv.Perm.sign_one]
    have hjj : Even (j'.val + j'.val) := by
      rw [Nat.even_iff]
      omega
    rw [show (-1 : ℤˣ) ^ (j'.val + j'.val) = 1 from by
      rw [neg_one_pow_ite (n := j'.val + j'.val)]
      simp [hjj]]
  · by_cases haj : j' = a
    · rw [haj]
      simpa using inducedPerm_swap_sign a b
    · by_cases hbj : j' = b
      · rw [hbj]
        simpa [Equiv.swap_comm] using inducedPerm_swap_sign b a
      · rw [inducedPerm_swap_away a b j' haj hbj]
        have hsa : Equiv.swap a b j' = j' := by
          simp [Equiv.swap_apply_def, haj, hbj]
        rw [hsa]
        have hne : removeHole j' a (Ne.symm haj) ≠ removeHole j' b (Ne.symm hbj) := by
          intro h
          have h1 : j'.succAbove (removeHole j' a
            (Ne.symm haj)) = a := succAbove_removeHole j' a (Ne.symm haj)
          have h2 : j'.succAbove (removeHole j' b
            (Ne.symm hbj)) = b := succAbove_removeHole j' b (Ne.symm hbj)
          have hcong : j'.succAbove (removeHole j' a (Ne.symm haj)) = j'.succAbove
            (removeHole j' b (Ne.symm hbj)) := by
            exact congrArg (fun z => j'.succAbove z) h
          exact hab (h1.symm.trans (hcong.trans h2))
        have hsig1 : Equiv.Perm.sign (Equiv.swap (removeHole j' a (Ne.symm haj))
          (removeHole j' b (Ne.symm hbj))) = (-1 : ℤˣ) := by
          simp [hne]
        rw [hsig1]
        simp only [hab, Equiv.Perm.sign_swap', one_mul, neg_mul, if_false]
        have hjj : Even (j'.val + j'.val) := by
          rw [Nat.even_iff]
          omega
        rw [show (-1 : ℤˣ) ^ (j'.val + j'.val) = 1 from by
          rw [neg_one_pow_ite (n := j'.val + j'.val)]
          simp [hjj]]

private theorem sign_inducedPerm {m : ℕ} (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1)) :
    Equiv.Perm.sign (inducedPerm τl j) =
      Equiv.Perm.sign τl * (-1 : ℤˣ) ^ (j.val + (τl j).val) := by
  refine Trunc.induction_on (Equiv.Perm.truncSwapFactors τl) ?_
  rintro ⟨l, hprod, hswap⟩
  have hP' : ∀ (l : List (Equiv.Perm (Fin (m + 1)))), (∀ g ∈ l, g.IsSwap) →
      Equiv.Perm.sign (inducedPerm l.prod j) =
        Equiv.Perm.sign l.prod * (-1 : ℤˣ) ^ (j.val + (l.prod j).val) := by
    intro l
    induction l with
    | nil =>
        intro hswap
        have hjj : Even (j.val + j.val) := by
          rw [Nat.even_iff]
          omega
        simp only [List.prod_nil, inducedPerm_one, Equiv.Perm.sign_one, Equiv.Perm.coe_one,
          id_eq, one_mul]
        rw [show (-1 : ℤˣ) ^ (j.val + j.val) = 1 from by
          rw [neg_one_pow_ite (n := j.val + j.val)]
          simp [hjj]]
    | cons s l' ih =>
        intro hswap
        rcases hswap s (by simp) with ⟨a, b, hab, rfl⟩
        have hsig_sub := ih (fun g hg => hswap g (by simp [hg]))
        have hsign_mul : Equiv.Perm.sign (inducedPerm (Equiv.swap a b * l'.prod) j) =
            Equiv.Perm.sign (Equiv.swap a b) * (-1 : ℤˣ) ^ ((l'.prod j).val + (Equiv.swap a b
              (l'.prod j)).val) *
              (Equiv.Perm.sign l'.prod * (-1 : ℤˣ) ^ (j.val + (l'.prod j).val)) := by
          rw [inducedPerm_mul]
          rw [Equiv.Perm.sign_mul]
          rw [inducedPerm_swap_sign' a b (l'.prod j)]
          rw [hsig_sub]
        have hpow : (-1 : ℤˣ) ^ ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val + (j.val +
          (l'.prod j).val)) =
            (-1 : ℤˣ) ^ (j.val + (Equiv.swap a b (l'.prod j)).val) := by
          rw [neg_one_pow_ite, neg_one_pow_ite]
          have hmod : ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val + (j.val +
            (l'.prod j).val)) % 2 =
              (j.val + (Equiv.swap a b (l'.prod j)).val) % 2 := by omega
          simp [Nat.even_iff, hmod]
        calc
          Equiv.Perm.sign (inducedPerm (Equiv.swap a b * l'.prod) j)
              = Equiv.Perm.sign (Equiv.swap a b) * (-1 : ℤˣ) ^ ((l'.prod j).val +
                (Equiv.swap a b (l'.prod j)).val) *
                  (Equiv.Perm.sign l'.prod * (-1 : ℤˣ) ^ (j.val + (l'.prod j).val)) := hsign_mul
          _ = (Equiv.Perm.sign (Equiv.swap a b) * Equiv.Perm.sign l'.prod) *
                (-1 : ℤˣ) ^ ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val + (j.val +
                  (l'.prod j).val)) := by
                rw [neg_one_pow_add ((l'.prod j).val + (Equiv.swap a b (l'.prod j)).val)
                  (j.val + (l'.prod j).val)]
                ac_rfl
          _ = Equiv.Perm.sign (Equiv.swap a b * l'.prod) * (-1 : ℤˣ) ^ (j.val + (Equiv.swap a b
            (l'.prod j)).val) := by
                rw [← Equiv.Perm.sign_mul, hpow]
          _ = Equiv.Perm.sign (Equiv.swap a b * l'.prod) * (-1 : ℤˣ) ^ (j.val +
            ((Equiv.swap a b * l'.prod) j).val) := by
                congr 1
  have hP := hP' l hswap
  rw [← hprod]
  exact hP

section Transport

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n : ℕ}

omit [NormedAddCommGroup M] in
private theorem removeNth_comp_perm' (τl : Equiv.Perm (Fin (m + 1))) (j : Fin (m + 1))
    (a : Fin (m + 1) → M) :
    j.removeNth (a ∘ τl) = (τl j).removeNth a ∘ inducedPerm τl j := by
  ext i
  change a (τl (j.succAbove i)) = a ((τl j).succAbove (inducedPerm τl j i))
  rw [inducedPerm_succAbove]

private theorem uncurryFinLeftExpandedSummand_mul_sumCongr
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (w : Fin (m + 1) ⊕ Fin n → M)
    (τ₀ : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (τl : Equiv.Perm (Fin (m + 1))) (τr : Equiv.Perm (Fin n)) (j : Fin (m + 1)) :
    uncurryFinLeftExpandedSummand f g' h w (τ₀ * Equiv.Perm.sumCongr τl τr) j =
      uncurryFinLeftExpandedSummand f g' h w τ₀ (τl j) := by
  unfold uncurryFinLeftExpandedSummand
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_sumCongr]
  have hh : h (fun i : Fin n => w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inr i))) =
      Equiv.Perm.sign τr • h (fun i : Fin n => w (τ₀ (Sum.inr i))) := by
    have hcomp : (fun i : Fin n => w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inr i))) =
        (fun i : Fin n => w (τ₀ (Sum.inr i))) ∘ τr := by
      funext i
      simp [Function.comp_apply, Equiv.Perm.coe_mul]
    rw [hcomp]
    exact h.map_perm (fun i : Fin n => w (τ₀ (Sum.inr i))) τr
  have hg : g' (w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inl j))) (j.removeNth (fun i : Fin
    (m + 1) => w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inl i)))) =
      Equiv.Perm.sign (inducedPerm τl j) • g' (w (τ₀ (Sum.inl (τl j)))) ((τl j).removeNth
        (fun i : Fin (m + 1) => w (τ₀ (Sum.inl i)))) := by
    have hfirst : (τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inl j) = τ₀ (Sum.inl (τl j)) := by
      simp [Equiv.Perm.coe_mul]
    rw [hfirst]
    have hcomp : (fun i : Fin (m + 1) => w ((τ₀ * Equiv.Perm.sumCongr τl τr) (Sum.inl i))) =
        (fun i : Fin (m + 1) => w (τ₀ (Sum.inl i))) ∘ τl := by
      funext i
      simp [Function.comp_apply, Equiv.Perm.coe_mul]
    rw [hcomp]
    rw [removeNth_comp_perm' τl j (fun i : Fin (m + 1) => w (τ₀ (Sum.inl i)))]
    exact (g' (w (τ₀ (Sum.inl (τl j))))).map_perm
      ((τl j).removeNth (fun i : Fin (m + 1) => w (τ₀ (Sum.inl i)))) (inducedPerm τl j)
  rw [hh, hg]
  have hsig : Equiv.Perm.sign (inducedPerm τl j) = Equiv.Perm.sign τl * (-1 : ℤˣ) ^ (j.val +
    (τl j).val) :=
    sign_inducedPerm τl j
  have hsig : Equiv.Perm.sign (inducedPerm τl j) = Equiv.Perm.sign τl * (-1 : ℤˣ) ^ (j.val +
    (τl j).val) :=
    sign_inducedPerm τl j
  simp only [Units.smul_def, smul_smul]
  simp only [Int.reduceNeg, Units.val_mul, map_zsmul, FunLike.coe_smul,
    Pi.smul_apply, smul_smul, mul_assoc]
  rw [hsig]
  congr 1
  have hjj : Even (j.val + j.val) := by
    rw [Nat.even_iff]
    omega
  have hpow2 : (-1 : ℤ) ^ (j.val + j.val) = 1 := by
    rw [show j.val + j.val = 2 * j.val from by omega]
    rw [pow_mul]
    simp
  have hsgn (x : ℤˣ) : (x : ℤ) * (x : ℤ) = 1 := by
    rcases Int.units_eq_one_or x with rfl | rfl <;> simp
  have hunitpow (k : ℕ) : (↑((-1 : ℤˣ) ^ k) : ℤ) = (-1 : ℤ) ^ k := by
    exact map_pow (Units.coeHom ℤ) (-1 : ℤˣ) k
  have hpowj : (-1 : ℤ) ^ j.val * (-1 : ℤ) ^ (j.val + (τl j).val) = (-1 : ℤ) ^ (τl j).val := by
    rw [← pow_add (a := (-1 : ℤ)) (m := j.val) (n := j.val + (τl j).val)]
    rw [show j.val + (j.val + (τl j).val) = (j.val + j.val) + (τl j).val from by omega]
    rw [pow_add (a := (-1 : ℤ)) (m := j.val + j.val) (n := (τl j).val)]
    rw [hpow2]
    simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign τl) with hτl | hτl <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τr) with hτr | hτr <;>
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ₀) with hτ₀ | hτ₀ <;>
        simp [hτl, hτr, hτ₀, hpowj, hunitpow]

end Transport

private theorem uncurryFin_wedge_productL_precompL_fiber
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (w : Fin (m + 1) ⊕ Fin n → M)
    (τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) :
    (∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w
        (derivShuffleLeftInsertRankedRepresentative (derivShuffleEquivLeft.symm (τ', j)).1
          (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)) j) =
      ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w (Quot.out τ') j := by
  let τ₀ : Equiv.Perm (Fin (m + 1) ⊕ Fin n) := Quot.out τ'
  let ρ : Fin (m + 1) → Equiv.Perm (Fin (m + 1) ⊕ Fin n) := fun j =>
    derivShuffleLeftInsertRankedRepresentative (derivShuffleEquivLeft.symm (τ', j)).1
      (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)
  let k : Fin (m + 1) → Fin (m + n + 1) := fun j =>
    (derivShuffleEquivLeft.symm (τ', j)).1
  have hρ_coset : ∀ j : Fin (m + 1),
      (Quotient.mk'' (derivShuffleLeftInsertRankedRepresentative (derivShuffleEquivLeft.symm (τ', j)).1
        (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)) :
          Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) = τ' := by
    intro j
    have hpre : derivShuffleEquivLeft ((derivShuffleEquivLeft.symm (τ', j)).1,
        Quotient.mk'' (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)) = (τ', j) := by
      have h₁ := derivShuffleEquivLeft.apply_symm_apply (τ', j)
      convert h₁ using 1
      congr 1
      apply Prod.ext
      · rfl
      · exact Quot.out_eq (q := (derivShuffleEquivLeft.symm (τ', j)).2)
    have h₁ := congrArg Prod.fst (hpre.symm.trans (derivShuffleEquivLeft_apply_mk_ranked
      (derivShuffleEquivLeft.symm (τ', j)).1 (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)))
    simpa [ρ] using h₁.symm
  have hρ_inl : ∀ j : Fin (m + 1),
      ρ j (Sum.inl j) = finSuccSumEquiv.symm (k j) := by
    intro j
    have hrank : derivShuffleRank (k j) (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2) = j := by
      let σ : Equiv.Perm (Fin m ⊕ Fin n) := Quot.out (derivShuffleEquivLeft.symm (τ', j)).2
      have hσ : (derivShuffleEquivLeft.symm (τ', j)).2 = Quotient.mk'' σ := by
        exact (Quot.out_eq (q := (derivShuffleEquivLeft.symm (τ', j)).2)).symm
      have hpre : derivShuffleEquivLeft (k j, Quotient.mk'' σ) = (τ', j) := by
        have h₁ := derivShuffleEquivLeft.apply_symm_apply (τ', j)
        convert h₁ using 1
        congr 1
        apply Prod.ext
        · rfl
        · exact hσ.symm
      have h₁ := congrArg Prod.snd hpre
      simpa [k, σ] using h₁
    have h₁ : ρ j (Sum.inl (derivShuffleRank (k j) (Quot.out (derivShuffleEquivLeft.symm (τ',
      j)).2))) =
        finSuccSumEquiv.symm (k j) := by
      simp [ρ, k, derivShuffleLeftInsertRankedRepresentative_inl_j]
    have hslot : (Sum.inl j : Fin (m + 1) ⊕ Fin n) = Sum.inl (derivShuffleRank (k j) (Quot.out
      (derivShuffleEquivLeft.symm (τ', j)).2)) := by
      exact congrArg (Sum.inl : Fin (m + 1) → Fin (m + 1) ⊕ Fin n) hrank.symm
    rw [hslot]
    exact h₁
  let ψ : Fin (m + 1) → Fin (m + 1) := fun j =>
    match τ₀⁻¹ (finSuccSumEquiv.symm (k j)) with
    | Sum.inl ℓ => ℓ
    | Sum.inr _ => 0
  have hψ_val : ∀ j : Fin (m + 1),
      uncurryFinLeftExpandedSummand f g' h w (ρ j) j =
        uncurryFinLeftExpandedSummand f g' h w τ₀ (ψ j) := by
    intro j
    have hcoset : (Quotient.mk'' (ρ j) : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
        Quotient.mk'' τ₀ := by
      exact (hρ_coset j).trans (Quot.out_eq (q := τ')).symm
    obtain ⟨τl, τr, hdecomp⟩ := coset_mul_sumCongr τ₀ (ρ j) hcoset
    have htrans : uncurryFinLeftExpandedSummand f g' h w (ρ j) j =
        uncurryFinLeftExpandedSummand f g' h w τ₀ (τl j) := by
      rw [hdecomp]
      exact uncurryFinLeftExpandedSummand_mul_sumCongr f g' h w τ₀ τl τr j
    have hψj : Sum.inl (τl j) = τ₀⁻¹ (finSuccSumEquiv.symm (k j)) := by
      have h₂ : ρ j (Sum.inl j) = τ₀ (Sum.inl (τl j)) := by
        rw [hdecomp]
        simp [Equiv.Perm.coe_mul]
      rw [← hρ_inl j]
      simp [h₂]
    have hψj' : τl j = ψ j := by
      unfold ψ
      rw [← hψj]
    rw [htrans, hψj']
  have hψ_inl : ∀ j : Fin (m + 1), ∃ τl_j : Fin (m + 1),
      τ₀⁻¹ (finSuccSumEquiv.symm (k j)) = Sum.inl τl_j := by
    intro j
    have hcoset : (Quotient.mk'' (ρ j) : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
        Quotient.mk'' τ₀ := by
      exact (hρ_coset j).trans (Quot.out_eq (q := τ')).symm
    obtain ⟨τl, τr, hdecomp⟩ := coset_mul_sumCongr τ₀ (ρ j) hcoset
    have h₂ : ρ j (Sum.inl j) = τ₀ (Sum.inl (τl j)) := by
      rw [hdecomp]
      simp [Equiv.Perm.coe_mul]
    have h₃ : τ₀⁻¹ (finSuccSumEquiv.symm (k j)) = Sum.inl (τl j) := by
      rw [← hρ_inl j]
      rw [h₂]
      simp
    exact ⟨τl j, h₃⟩
  have hψ_inj : Function.Injective ψ := by
    intro j₁ j₂ h
    have hk : k j₁ = k j₂ := by
      obtain ⟨τl₁, h₁⟩ := hψ_inl j₁
      obtain ⟨τl₂, h₂⟩ := hψ_inl j₂
      have hψ₁ : ψ j₁ = τl₁ := by
        unfold ψ
        rw [h₁]
      have hψ₂ : ψ j₂ = τl₂ := by
        unfold ψ
        rw [h₂]
      have hτl : τl₁ = τl₂ := by
        rw [← hψ₁, ← hψ₂, h]
      have hpre : τ₀⁻¹ (finSuccSumEquiv.symm (k j₁)) = τ₀⁻¹ (finSuccSumEquiv.symm (k j₂)) := by
        rw [h₁, h₂, hτl]
      have hk' : finSuccSumEquiv.symm (k j₁) = finSuccSumEquiv.symm (k j₂) :=
        (Equiv.injective τ₀⁻¹) hpre
      exact Equiv.injective finSuccSumEquiv.symm hk'
    exact preimage_k_injective τ' j₁ j₂ hk
  have hψ_surj : Function.Surjective ψ := by
    intro ℓ
    exact (Fintype.bijective_iff_injective_and_card ψ).2 ⟨hψ_inj, by simp⟩ |>.2 ℓ
  calc
    (∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w (ρ j) j)
        = ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ₀ (ψ j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          exact hψ_val j
    _ = ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w τ₀ j := by
          refine Finset.sum_bij (fun j _ => ψ j) ?_ ?_ ?_ ?_
          · intro j hj
            simp
          · intro j₁ hj₁ j₂ hj₂ h
            exact hψ_inj h
          · intro ℓ hℓ
            obtain ⟨j, hj⟩ := hψ_surj ℓ
            exact ⟨j, by simp, hj⟩
          · intro j hj
            rfl
    _ = ∑ j : Fin (m + 1), uncurryFinLeftExpandedSummand f g' h w (Quot.out τ') j := rfl

theorem uncurryFin_wedge_productL_precompL_eq_domDomCongr
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N') :
    uncurryFin ((wedgeProductL f).precompL M g' h) =
      domDomCongr Fin.finAddFlipAssoc (wedgeProduct (uncurryFin g') h f) := by
  ext v
  let w : Fin (m + 1) ⊕ Fin n → M := (v ∘ ⇑Fin.finAddFlipAssoc) ∘ ⇑finSumFinEquiv
  calc
    uncurryFin ((wedgeProductL f).precompL M g' h) v
        = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            wedgeProduct (g' (v k)) h f (k.removeNth v) := by
          exact uncurryFin_wedge_productL_precompL_apply f g' h v
    _ = ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
            uncurrySum (f.compContinuousAlternatingMap₂ (g' (v k)) h)
              ((k.removeNth v) ∘ ⇑finSumFinEquiv) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [wedge_product_def]
          simp [uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply]
    _ = ∑ k : Fin (m + n + 1), ∑ σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
            (-1 : ℤ) ^ k.val •
              uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h) σ
                ((k.removeNth v) ∘ ⇑finSumFinEquiv) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [uncurrySum_apply]
          simp [Finset.smul_sum]
    _ = ∑ k : Fin (m + n + 1), ∑ σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
            uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftInsertRankedRepresentative k (Quot.out σ))
              (derivShuffleRank k (Quot.out σ)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          have hstep := derivShuffleLeft_expanded_summand_eq f g' h v k (Quot.out σ)
          have hcong :
              uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h) σ
                  ((k.removeNth v) ∘ ⇑finSumFinEquiv) =
                uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h)
                  (Quotient.mk'' (Quot.out σ)) ((k.removeNth v) ∘ ⇑finSumFinEquiv) :=
            congrArg (fun q : Equiv.Perm.ModSumCongr (Fin m) (Fin n) =>
              uncurrySum.summand (f.compContinuousAlternatingMap₂ (g' (v k)) h) q
                ((k.removeNth v) ∘ ⇑finSumFinEquiv)) (Quot.out_eq (q := σ)).symm
          rw [hcong]
          exact hstep
    _ = ∑ q : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1),
            uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftInsertRankedRepresentative
              (derivShuffleEquivLeft.symm q).1
              (Quot.out (derivShuffleEquivLeft.symm q).2)) q.2 := by
          have hconv : (∑ k : Fin (m + n + 1), ∑ σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
                uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftInsertRankedRepresentative k (Quot.out σ))
                  (derivShuffleRank k (Quot.out σ))) =
              ∑ p : (Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n)),
                uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftInsertRankedRepresentative p.1
                  (Quot.out p.2))
                  (derivShuffleRank p.1 (Quot.out p.2)) := by
            simpa [Finset.univ_product_univ] using
              (Finset.sum_product (s := (Finset.univ : Finset (Fin (m + n + 1))))
                (t := (Finset.univ : Finset (Equiv.Perm.ModSumCongr (Fin m) (Fin n))))
                (f := fun p : (Fin (m + n + 1) × Equiv.Perm.ModSumCongr (Fin m) (Fin n)) =>
                  uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftInsertRankedRepresentative p.1
                    (Quot.out p.2))
                    (derivShuffleRank p.1 (Quot.out p.2)))).symm
          rw [hconv]
          refine Finset.sum_bij (fun p _ => derivShuffleEquivLeft p) ?_ ?_ ?_ ?_
          · intro p hp
            simp
          · intro p₁ hp₁ p₂ hp₂ h
            exact Equiv.injective derivShuffleEquivLeft h
          · intro q hq
            exact ⟨derivShuffleEquivLeft.symm q, by simp, by simp⟩
          · intro p hp
            rw [show (derivShuffleEquivLeft.symm (derivShuffleEquivLeft p)).1 = p.1 from by simp,
              show (derivShuffleEquivLeft.symm (derivShuffleEquivLeft p)).2 = p.2 from by simp]
            have hpair : p = (p.1, Quotient.mk'' (Quot.out p.2)) := by
              apply Prod.ext
              · rfl
              · exact (Quot.out_eq (q := p.2)).symm
            have h2 : (derivShuffleEquivLeft p).2 = derivShuffleRank p.1 (Quot.out p.2) := by
              have h := derivShuffleEquivLeft_apply_mk_ranked p.1 (Quot.out p.2)
              conv_lhs =>
                rw [hpair]
              rw [h]
            rw [h2]
    _ = ∑ τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n), ∑ j : Fin (m + 1),
            uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftInsertRankedRepresentative
              (derivShuffleEquivLeft.symm (τ', j)).1
              (Quot.out (derivShuffleEquivLeft.symm (τ', j)).2)) j := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product (s := (Finset.univ : Finset (Equiv.Perm.ModSumCongr (Fin
              (m + 1)) (Fin n))))
              (t := (Finset.univ : Finset (Fin (m + 1))))
              (f := fun p : (Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) × Fin (m + 1)) =>
                uncurryFinLeftExpandedSummand f g' h w (derivShuffleLeftInsertRankedRepresentative
                  (derivShuffleEquivLeft.symm p).1
                  (Quot.out (derivShuffleEquivLeft.symm p).2)) p.2))
    _ = ∑ τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n), ∑ j : Fin (m + 1),
            uncurryFinLeftExpandedSummand f g' h w (Quot.out τ') j := by
          refine Finset.sum_congr rfl ?_
          intro τ' hτ'
          exact uncurryFin_wedge_productL_precompL_fiber f g' h w τ'
    _ = ∑ τ' : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n),
            uncurrySum.summand (f.compContinuousAlternatingMap₂ (uncurryFin g') h) τ' w := by
          refine Finset.sum_congr rfl ?_
          intro τ' hτ'
          exact (uncurrySum_summand_uncurryFin_left_expand_mk f g' h w (Quot.out τ')).symm.trans
            (congrArg (fun q : Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n) =>
              uncurrySum.summand (f.compContinuousAlternatingMap₂ (uncurryFin g') h) q w)
              (Quot.out_eq (q := τ')))
    _ = uncurrySum (f.compContinuousAlternatingMap₂ (uncurryFin g') h) w := by
          rw [uncurrySum_apply, _root_.sum_apply]
    _ = (wedgeProduct (uncurryFin g') h f) (v ∘ ⇑Fin.finAddFlipAssoc) := by
          rw [wedge_product_def, uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply]
    _ = domDomCongr Fin.finAddFlipAssoc (wedgeProduct (uncurryFin g') h f) v := by
          rw [wedge_product_uncurryFin_apply]

private def placementSummand (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (P : Equiv.Perm.ThreeShuffle m n p) (w : Fin (m + n + p) → M) : 𝕜 :=
  g (w ∘ P.mBlock.1.orderEmbOfFin P.mBlock.2) *
    h (w ∘ (Equiv.Perm.ThreeShuffle.nBlock P).1.orderEmbOfFin
      (Equiv.Perm.ThreeShuffle.nBlock P).2) *
      l (w ∘ (Equiv.Perm.ThreeShuffle.pBlock P).1.orderEmbOfFin
        (Equiv.Perm.ThreeShuffle.pBlock P).2)

private theorem wedge_mul_assoc_rhs_expand (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M) :
    ((g ∧[𝕜] h) ∧[𝕜] l) w =
      ∑ q₂ : Equiv.Perm.ModSumCongr (Fin (m + n)) (Fin p),
        Equiv.Perm.sign (Quot.out q₂ : Equiv.Perm (Fin (m + n) ⊕ Fin p)) •
          ((g ∧[𝕜] h) ((w ∘ finSumFinEquiv) ∘ (Quot.out q₂ : Equiv.Perm (Fin
            (m + n) ⊕ Fin p)) ∘ Sum.inl) *
            l ((w ∘ finSumFinEquiv) ∘ (Quot.out q₂ : Equiv.Perm (Fin
              (m + n) ⊕ Fin p)) ∘ Sum.inr)) := by
  rw [wedge_product_def, uncurryFinAdd]
  rw [ContinuousAlternatingMap.domDomCongr_apply]
  rw [uncurrySum_apply]
  simp only [_root_.sum_apply]
  rw [Finset.sum_congr rfl]
  intro q₂ _
  let σ₂ : Equiv.Perm (Fin (m + n) ⊕ Fin p) := Quot.out q₂
  change uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂
    (g ∧[𝕜] h) l)
      q₂ (w ∘ finSumFinEquiv) =
    Equiv.Perm.sign σ₂ • ((g ∧[𝕜] h) ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) *
      l ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inr))
  conv_lhs =>
    rw [← Quotient.out_eq q₂]
  rw [uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  calc
    Equiv.Perm.sign σ₂ •
        (((g ∧[𝕜] h) fun i => (w ∘ finSumFinEquiv) (σ₂ (Sum.inl i))) *
          l fun i => (w ∘ finSumFinEquiv) (σ₂ (Sum.inr i))) =
        Equiv.Perm.sign σ₂ •
          ((g ∧[𝕜] h) ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) *
            l fun i => (w ∘ finSumFinEquiv) (σ₂ (Sum.inr i))) := by
      apply congrArg (fun s : 𝕜 => Equiv.Perm.sign σ₂ • s)
      apply congrArg (fun x : 𝕜 => x * l (fun i => (w ∘ finSumFinEquiv) (σ₂ (Sum.inr i))))
      apply congrArg (g ∧[𝕜] h)
      funext i
      rfl
    _ = Equiv.Perm.sign σ₂ •
          ((g ∧[𝕜] h) ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) *
            l ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inr)) := by
      apply congrArg (fun s : 𝕜 => Equiv.Perm.sign σ₂ • s)
      apply congrArg (fun y : 𝕜 => (g ∧[𝕜] h) ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) * y)
      apply congrArg l
      funext i
      rfl

private theorem wedge_mul_assoc_rhs_inner (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M)
    (σ₂ : Equiv.Perm (Fin (m + n) ⊕ Fin p)) :
    ∑ q₄ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
      Equiv.Perm.sign σ₂ •
        uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) q₄
          ((((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) ∘ finSumFinEquiv)) *
          l ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inr) =
      Equiv.Perm.sign σ₂ • ((g ∧[𝕜] h) ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) *
          l ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inr)) := by
  let v₁ : Fin (m + n) → M := (w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl
  let v₂ : Fin p → M := (w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inr
  change ∑ q₄ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
      Equiv.Perm.sign σ₂ • uncurrySum.summand
        ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) q₄
        (v₁ ∘ finSumFinEquiv) * l v₂ =
    Equiv.Perm.sign σ₂ • ((g ∧[𝕜] h) v₁ * l v₂)
  have hgh : (g ∧[𝕜] h) v₁ =
      ∑ q₄ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
        uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) q₄
          (v₁ ∘ finSumFinEquiv) := by
    rw [wedge_product_def, uncurryFinAdd]
    rw [ContinuousAlternatingMap.domDomCongr_apply]
    rw [uncurrySum_apply]
    simp only [_root_.sum_apply]
  calc
    (∑ q₄ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
        (Equiv.Perm.sign σ₂ • uncurrySum.summand
          ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) q₄
          (v₁ ∘ finSumFinEquiv)) * l v₂)
        = (Equiv.Perm.sign σ₂ • (∑ q₄ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
            uncurrySum.summand
              ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) q₄
              (v₁ ∘ finSumFinEquiv))) * l v₂ := by
      simp [Units.smul_def, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = Equiv.Perm.sign σ₂ • ((∑ q₄ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
          uncurrySum.summand
            ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) q₄
            (v₁ ∘ finSumFinEquiv)) * l v₂) := by
      simp [Units.smul_def, mul_assoc]
    _ = Equiv.Perm.sign σ₂ • ((g ∧[𝕜] h) v₁ * l v₂) := by
      simp [hgh, Units.smul_def]

private theorem wedge_mul_assoc_rhs_quot (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M)
    (σ₂ : Equiv.Perm (Fin (m + n) ⊕ Fin p)) :
    Equiv.Perm.sign σ₂ •
      ((g ∧[𝕜] h) ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) * l ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inr)) =
      uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂
        (g ∧[𝕜] h) l) (Quotient.mk'' σ₂) (w ∘ finSumFinEquiv) := by
  rw [uncurrySum_summand_eval]
  simp [ContinuousLinearMap.compContinuousAlternatingMap₂_apply, ContinuousLinearMap.mul_apply']
  rfl

private theorem wedge_mul_assoc_rhs_cosets (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M)
    (σ₂ σ₂' : Equiv.Perm (Fin (m + n) ⊕ Fin p))
    (hσ : Equiv.Perm.TwoShuffle.ofPerm σ₂ = Equiv.Perm.TwoShuffle.ofPerm σ₂') :
    Equiv.Perm.sign σ₂ •
      ((g ∧[𝕜] h) ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) * l ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inr)) =
      Equiv.Perm.sign σ₂' •
        ((g ∧[𝕜] h) ((w ∘ finSumFinEquiv) ∘ σ₂' ∘ Sum.inl) *
          l ((w ∘ finSumFinEquiv) ∘ σ₂' ∘ Sum.inr)) := by
  rw [wedge_mul_assoc_rhs_quot g h l w σ₂]
  rw [wedge_mul_assoc_rhs_quot g h l w σ₂']
  rw [Equiv.Perm.TwoShuffle.quotient_eq_of_ofPerm_eq hσ]

private theorem wedge_mul_assoc_rhs_can_point (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M)
    (q₂ : Equiv.Perm.ModSumCongr (Fin (m + n)) (Fin p))
    (q₄ : Equiv.Perm.ModSumCongr (Fin m) (Fin n)) :
    Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂, q₄)).rightOuter.toPerm) •
      uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) q₄
        ((((w ∘ finSumFinEquiv) ∘ (Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂,
          q₄)).rightOuter.toPerm ∘ Sum.inl) ∘
          finSumFinEquiv)) *
        l ((w ∘ finSumFinEquiv) ∘ (Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂,
          q₄)).rightOuter.toPerm ∘ Sum.inr) =
      (Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂, q₄)).canonicalRight) : 𝕜) •
          placementSummand g h l (Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂, q₄)) w := by
  let P : Equiv.Perm.ThreeShuffle m n p := Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂, q₄)
  let σ₂ : Equiv.Perm (Fin (m + n) ⊕ Fin p) := P.rightOuter.toPerm
  let τ₂ : Equiv.Perm (Fin m ⊕ Fin n) := P.rightInner.toPerm
  have hτ : Quotient.mk'' τ₂ = q₄ := by
    dsimp [τ₂, P, Equiv.Perm.ThreeShuffle.leftShuffle]
    rw [Equiv.Perm.ThreeShuffle.leftAssocShuffle_rightInner]
    exact (Equiv.Perm.TwoShuffle.modSumCongrTwoShuffle m n).left_inv q₄
  change Equiv.Perm.sign σ₂ •
    uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) q₄
      ((((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) ∘ finSumFinEquiv)) * l
        ((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inr) =
    (Equiv.Perm.sign (Equiv.Perm.ThreeShuffle.canonicalRight P) : 𝕜) • placementSummand g h l P w
  have hg : (fun i => (((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) ∘ finSumFinEquiv) (τ₂ (Sum.inl i))) =
      w ∘ P.mBlock.1.orderEmbOfFin P.mBlock.2 := by
    funext i
    change w (finSumFinEquiv (σ₂ (Sum.inl (finSumFinEquiv (τ₂ (Sum.inl i)))))) =
      w (P.mBlock.1.orderEmbOfFin P.mBlock.2 i)
    rw [Equiv.Perm.TwoShuffle.toPerm_inl, Equiv.Perm.TwoShuffle.toPerm_inl]
    exact congrArg w (Equiv.Perm.ThreeShuffle.rightInner_emb P i)
  have hh : (fun j => (((w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inl) ∘ finSumFinEquiv) (τ₂ (Sum.inr j))) =
      w ∘ (Equiv.Perm.ThreeShuffle.nBlock P).1.orderEmbOfFin
        (Equiv.Perm.ThreeShuffle.nBlock P).2 := by
    funext j
    change w (finSumFinEquiv (σ₂ (Sum.inl (finSumFinEquiv (τ₂ (Sum.inr j)))))) =
      w ((Equiv.Perm.ThreeShuffle.nBlock P).1.orderEmbOfFin (Equiv.Perm.ThreeShuffle.nBlock P).2 j)
    rw [Equiv.Perm.TwoShuffle.toPerm_inl, Equiv.Perm.TwoShuffle.toPerm_inr]
    exact congrArg w (Equiv.Perm.ThreeShuffle.rightInner_compl_emb P j)
  have hl : (w ∘ finSumFinEquiv) ∘ σ₂ ∘ Sum.inr =
      w ∘ (Equiv.Perm.ThreeShuffle.pBlock P).1.orderEmbOfFin
        (Equiv.Perm.ThreeShuffle.pBlock P).2 := by
    funext k
    change w (finSumFinEquiv (σ₂ (Sum.inr k))) =
      w ((Equiv.Perm.ThreeShuffle.pBlock P).1.orderEmbOfFin (Equiv.Perm.ThreeShuffle.pBlock P).2 k)
    rw [Equiv.Perm.TwoShuffle.toPerm_inr]
    rfl
  rw [← hτ]
  rw [uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [hg, hh, hl]
  rw [placementSummand]
  have hsign : Equiv.Perm.sign (Equiv.Perm.ThreeShuffle.canonicalRight P) =
      Equiv.Perm.sign σ₂ * Equiv.Perm.sign τ₂ := by
    change Equiv.Perm.sign (Equiv.Perm.ThreeShuffle.mergeRight (P.rightOuter.toPerm)
      (P.rightInner.toPerm)) =
      Equiv.Perm.sign (P.rightOuter.toPerm) * Equiv.Perm.sign (P.rightInner.toPerm)
    exact Equiv.Perm.ThreeShuffle.sign_mergeRight (P.rightOuter.toPerm) (P.rightInner.toPerm)
  rw [hsign]
  simp [Units.smul_def, smul_eq_mul, Units.val_mul, mul_assoc]

private theorem wedge_mul_assoc_rhs_can (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M) :
    ((g ∧[𝕜] h) ∧[𝕜] l) w =
      ∑ q₂ : Equiv.Perm.ModSumCongr (Fin (m + n)) (Fin p),
        ∑ q₄ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
          Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂, q₄)).rightOuter.toPerm) •
            uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) q₄
              ((((w ∘ finSumFinEquiv) ∘
                (Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂, q₄)).rightOuter.toPerm ∘ Sum.inl) ∘
                finSumFinEquiv)) *
              l ((w ∘ finSumFinEquiv) ∘
                (Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂,
                  q₄)).rightOuter.toPerm ∘ Sum.inr) := by
  rw [wedge_mul_assoc_rhs_expand]
  rw [Finset.sum_congr rfl]
  intro q₂ _
  let σ₀ : Equiv.Perm (Fin (m + n) ⊕ Fin p) :=
    (Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₂)).toPerm
  have hσ₀ : Equiv.Perm.TwoShuffle.ofPerm σ₀ = Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₂) := by
    dsimp [σ₀]
    rw [Equiv.Perm.TwoShuffle.ofPerm_toPerm]
  have hσ₀' : ∀ q₄ : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
      (Equiv.Perm.ThreeShuffle.leftShuffle m n p (q₂, q₄)).rightOuter.toPerm = σ₀ := by
    intro q₄
    dsimp [σ₀, Equiv.Perm.ThreeShuffle.leftShuffle]
    simp [Equiv.Perm.TwoShuffle.modSumCongrTwoShuffle]
  rw [wedge_mul_assoc_rhs_cosets g h l w (Quot.out q₂) σ₀ hσ₀.symm]
  rw [← wedge_mul_assoc_rhs_inner g h l w σ₀]
  rw [Finset.sum_congr rfl]
  intro q₄ _
  rw [← hσ₀' q₄]

private theorem wedge_mul_assoc_rhs_sum (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M) :
    ((g ∧[𝕜] h) ∧[𝕜] l) w =
      ∑ P : Equiv.Perm.ThreeShuffle m n p,
        (Equiv.Perm.sign
          (Equiv.Perm.ThreeShuffle.canonicalRight P) : 𝕜) • placementSummand g h l P w := by
  rw [wedge_mul_assoc_rhs_can]
  rw [← Finset.sum_product (Finset.univ : Finset (Equiv.Perm.ModSumCongr (Fin (m + n)) (Fin p)))
    (Finset.univ : Finset (Equiv.Perm.ModSumCongr (Fin m) (Fin n)))
    (fun x : Equiv.Perm.ModSumCongr (Fin (m + n)) (Fin p) × Equiv.Perm.ModSumCongr (Fin m)
      (Fin n) =>
      Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.leftShuffle m n p x).rightOuter.toPerm) •
        uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x.2
          ((((w ∘ finSumFinEquiv) ∘
            (Equiv.Perm.ThreeShuffle.leftShuffle m n p x).rightOuter.toPerm ∘ Sum.inl) ∘
            finSumFinEquiv)) *
          l ((w ∘ finSumFinEquiv) ∘
            (Equiv.Perm.ThreeShuffle.leftShuffle m n p x).rightOuter.toPerm ∘ Sum.inr))]
  simp only [Finset.univ_product_univ]
  rw [← Finset.sum_bij (fun x : Equiv.Perm.ModSumCongr (Fin (m + n)) (Fin p) ×
        Equiv.Perm.ModSumCongr (Fin m)
          (Fin n) => fun _ => Equiv.Perm.ThreeShuffle.leftShuffle m n p x)
    (fun x _ => Finset.mem_univ _) (by
      intro a₁ _ a₂ _ h
      exact (Equiv.Perm.ThreeShuffle.leftShuffle m n p).injective h) (by
      intro b _
      refine ⟨(Equiv.Perm.ThreeShuffle.leftShuffle m n p).symm b, Finset.mem_univ _, ?_⟩
      exact (Equiv.Perm.ThreeShuffle.leftShuffle m n p).apply_symm_apply b) (by
      intro a _
      exact wedge_mul_assoc_rhs_can_point g h l w a.1 a.2)]

private theorem wedge_mul_assoc_lhs_expand (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M) :
    (g ∧[𝕜] (h ∧[𝕜] l)) (w ∘ Fin.finAssoc.symm) =
      ∑ q₁ : Equiv.Perm.ModSumCongr (Fin m) (Fin (n + p)),
        Equiv.Perm.sign (Quot.out q₁ : Equiv.Perm (Fin m ⊕ Fin (n + p))) •
          (g ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ (Quot.out q₁ : Equiv.Perm (Fin m ⊕ Fin
            (n + p))) ∘ Sum.inl) *
            (h ∧[𝕜] l) ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ (Quot.out q₁ : Equiv.Perm
              (Fin m ⊕ Fin (n + p))) ∘ Sum.inr)) := by
  rw [wedge_product_def, uncurryFinAdd]
  rw [ContinuousAlternatingMap.domDomCongr_apply]
  rw [uncurrySum_apply]
  simp only [_root_.sum_apply]
  rw [Finset.sum_congr rfl]
  intro q₁ _
  let σ₁ : Equiv.Perm (Fin m ⊕ Fin (n + p)) := Quot.out q₁
  change uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g
    (h ∧[𝕜] l))
      q₁ ((w ∘ Fin.finAssoc.symm) ∘ finSumFinEquiv) =
    Equiv.Perm.sign σ₁ • (g ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inl) *
      (h ∧[𝕜] l) ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr))
  conv_lhs =>
    rw [← Quotient.out_eq q₁]
  rw [uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rfl

private theorem wedge_mul_assoc_lhs_inner (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M)
    (σ₁ : Equiv.Perm (Fin m ⊕ Fin (n + p))) :
    ∑ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
      Equiv.Perm.sign σ₁ •
        uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h l) q₃
          ((((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr) ∘ finSumFinEquiv)) *
          g ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inl) =
      Equiv.Perm.sign σ₁ • (g ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inl) *
          (h ∧[𝕜] l) ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr)) := by
  let v₁ : Fin (n + p) → M := (w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr
  let v₂ : Fin m → M := (w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inl
  change ∑ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
      Equiv.Perm.sign σ₁ • uncurrySum.summand
        ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h l) q₃
        (v₁ ∘ finSumFinEquiv) * g v₂ =
    Equiv.Perm.sign σ₁ • (g v₂ * (h ∧[𝕜] l) v₁)
  have hhl : (h ∧[𝕜] l) v₁ =
      ∑ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
        uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h l) q₃
          (v₁ ∘ finSumFinEquiv) := by
    rw [wedge_product_def, uncurryFinAdd]
    rw [ContinuousAlternatingMap.domDomCongr_apply]
    rw [uncurrySum_apply]
    simp only [_root_.sum_apply]
  calc
    (∑ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
        (Equiv.Perm.sign σ₁ • uncurrySum.summand
          ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h l) q₃
          (v₁ ∘ finSumFinEquiv)) * g v₂)
        = (Equiv.Perm.sign σ₁ • (∑ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
            uncurrySum.summand
              ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h l) q₃
              (v₁ ∘ finSumFinEquiv))) * g v₂ := by
      simp [Units.smul_def, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    _ = Equiv.Perm.sign σ₁ • ((∑ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
          uncurrySum.summand
            ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h l) q₃
            (v₁ ∘ finSumFinEquiv)) * g v₂) := by
      simp [Units.smul_def, mul_assoc]
    _ = Equiv.Perm.sign σ₁ • (g v₂ * (h ∧[𝕜] l) v₁) := by
      rw [show (∑ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
            uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h l) q₃
              (v₁ ∘ finSumFinEquiv)) * g v₂ =
          g v₂ * (∑ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
            uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ h l) q₃
              (v₁ ∘ finSumFinEquiv)) from by
        rw [mul_comm]]
      simp [hhl, Units.smul_def]

private theorem wedge_mul_assoc_lhs_quot (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M)
    (σ₁ : Equiv.Perm (Fin m ⊕ Fin (n + p))) :
    Equiv.Perm.sign σ₁ •
      ((g ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inl) *
        (h ∧[𝕜] l) ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr))) =
      uncurrySum.summand ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g (h ∧[𝕜] l))
        (Quotient.mk'' σ₁) ((w ∘ Fin.finAssoc.symm) ∘ finSumFinEquiv) := by
  rw [uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rfl

private theorem wedge_mul_assoc_lhs_cosets (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M)
    (σ₁ σ₁' : Equiv.Perm (Fin m ⊕ Fin (n + p)))
    (hσ : Equiv.Perm.TwoShuffle.ofPerm σ₁ = Equiv.Perm.TwoShuffle.ofPerm σ₁') :
    Equiv.Perm.sign σ₁ •
      ((g ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inl) *
        (h ∧[𝕜] l) ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr))) =
      Equiv.Perm.sign σ₁' •
        ((g ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁' ∘ Sum.inl) *
          (h ∧[𝕜] l) ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁' ∘ Sum.inr))) := by
  rw [wedge_mul_assoc_lhs_quot g h l w σ₁]
  rw [wedge_mul_assoc_lhs_quot g h l w σ₁']
  rw [Equiv.Perm.TwoShuffle.quotient_eq_of_ofPerm_eq hσ]

private theorem wedge_mul_assoc_lhs_can_point (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M)
    (q₁ : Equiv.Perm.ModSumCongr (Fin m) (Fin (n + p)))
    (q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p)) :
    Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftOuter.toPerm) •
      Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftInner.toPerm) •
        g (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘
          (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftOuter.toPerm ∘ Sum.inl)) *
        h (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘
          (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftOuter.toPerm ∘ Sum.inr ∘
            finSumFinEquiv ∘ (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁,
              q₃)).leftInner.toPerm ∘ Sum.inl)) *
        l (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘
          (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftOuter.toPerm ∘ Sum.inr ∘
            finSumFinEquiv ∘ (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁,
              q₃)).leftInner.toPerm ∘ Sum.inr)) =
      (Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).canonicalLeft) : 𝕜) •
          placementSummand g h l (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)) w := by
  let P : Equiv.Perm.ThreeShuffle m n p := Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)
  let σ₁ : Equiv.Perm (Fin m ⊕ Fin (n + p)) := P.leftOuter.toPerm
  let τ₁ : Equiv.Perm (Fin n ⊕ Fin p) := P.leftInner.toPerm
  change Equiv.Perm.sign σ₁ • Equiv.Perm.sign τ₁ •
    g ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inl) *
    h (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr ∘ finSumFinEquiv) ∘ τ₁ ∘ Sum.inl) *
    l (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr ∘ finSumFinEquiv) ∘ τ₁ ∘ Sum.inr) =
    (Equiv.Perm.sign (Equiv.Perm.ThreeShuffle.canonicalLeft P) : 𝕜) • placementSummand g h l P w
  have hg : (w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inl =
      w ∘ P.mBlock.1.orderEmbOfFin P.mBlock.2 := by
    funext i
    change w (Fin.finAssoc.symm (finSumFinEquiv (σ₁ (Sum.inl i)))) =
      w (P.mBlock.1.orderEmbOfFin P.mBlock.2 i)
    rw [Equiv.Perm.TwoShuffle.toPerm_inl]
    rw [Equiv.Perm.ThreeShuffle.finAssoc_symm_finAssocOrder]
    exact congrArg w (Equiv.Perm.ThreeShuffle.leftOuter_emb P i)
  have hh : ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr ∘ finSumFinEquiv) ∘ τ₁ ∘
    Sum.inl =
      w ∘ (Equiv.Perm.ThreeShuffle.nBlock P).1.orderEmbOfFin
        (Equiv.Perm.ThreeShuffle.nBlock P).2 := by
    funext j
    change w (Fin.finAssoc.symm (finSumFinEquiv (σ₁ (Sum.inr (finSumFinEquiv (τ₁ (Sum.inl j))))))) =
      w ((Equiv.Perm.ThreeShuffle.nBlock P).1.orderEmbOfFin (Equiv.Perm.ThreeShuffle.nBlock P).2 j)
    rw [Equiv.Perm.TwoShuffle.toPerm_inr, Equiv.Perm.TwoShuffle.toPerm_inl]
    rw [Equiv.Perm.ThreeShuffle.finAssoc_symm_finAssocOrder]
    exact congrArg w ((Equiv.Perm.ThreeShuffle.leftOuter_compl_emb P
      ((Equiv.Perm.ThreeShuffle.leftInner P).1.orderEmbOfFin
        (Equiv.Perm.ThreeShuffle.leftInner P).2 j)).trans
      (Equiv.Perm.ThreeShuffle.leftInner_emb P j))
  have hl : ((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₁ ∘ Sum.inr ∘ finSumFinEquiv) ∘ τ₁ ∘
    Sum.inr =
      w ∘ (Equiv.Perm.ThreeShuffle.pBlock P).1.orderEmbOfFin
        (Equiv.Perm.ThreeShuffle.pBlock P).2 := by
    funext k
    change w (Fin.finAssoc.symm (finSumFinEquiv (σ₁ (Sum.inr (finSumFinEquiv (τ₁ (Sum.inr k))))))) =
      w ((Equiv.Perm.ThreeShuffle.pBlock P).1.orderEmbOfFin (Equiv.Perm.ThreeShuffle.pBlock P).2 k)
    rw [Equiv.Perm.TwoShuffle.toPerm_inr, Equiv.Perm.TwoShuffle.toPerm_inr]
    rw [Equiv.Perm.ThreeShuffle.finAssoc_symm_finAssocOrder]
    exact congrArg w ((Equiv.Perm.ThreeShuffle.leftOuter_compl_emb P
      (((Equiv.Perm.ThreeShuffle.leftInner P).1ᶜ : Finset (Fin (n + p))).orderEmbOfFin
        (by rw [Finset.card_compl, (Equiv.Perm.ThreeShuffle.leftInner P).2,
          Fintype.card_fin]; omega) k)).trans
      (Equiv.Perm.ThreeShuffle.leftInner_compl_emb P k))
  rw [hg, hh, hl]
  rw [placementSummand]
  have hsign : Equiv.Perm.sign (Equiv.Perm.ThreeShuffle.canonicalLeft P) =
      Equiv.Perm.sign σ₁ * Equiv.Perm.sign τ₁ := by
    change Equiv.Perm.sign (Equiv.Perm.ThreeShuffle.mergeLeft (P.leftOuter.toPerm)
      (P.leftInner.toPerm)) =
      Equiv.Perm.sign (P.leftOuter.toPerm) * Equiv.Perm.sign (P.leftInner.toPerm)
    exact Equiv.Perm.ThreeShuffle.sign_mergeLeft (P.leftOuter.toPerm) (P.leftInner.toPerm)
  rw [hsign]
  simp [Units.smul_def, Units.val_mul, mul_assoc]

private theorem wedge_mul_assoc_lhs_can (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M) :
    (g ∧[𝕜] (h ∧[𝕜] l)) (w ∘ Fin.finAssoc.symm) =
      ∑ q₁ : Equiv.Perm.ModSumCongr (Fin m) (Fin (n + p)),
        ∑ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
          Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftOuter.toPerm) •
            Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁,
              q₃)).leftInner.toPerm) •
              g (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘
                (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftOuter.toPerm ∘ Sum.inl)) *
              h (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘
                (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftOuter.toPerm ∘ Sum.inr ∘
                  finSumFinEquiv ∘ (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁,
                    q₃)).leftInner.toPerm ∘ Sum.inl)) *
              l (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘
                (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftOuter.toPerm ∘ Sum.inr ∘
                  finSumFinEquiv ∘ (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁,
                    q₃)).leftInner.toPerm ∘ Sum.inr)) := by
  rw [wedge_mul_assoc_lhs_expand]
  rw [Finset.sum_congr rfl]
  intro q₁ _
  let σ₀ : Equiv.Perm (Fin m ⊕ Fin (n + p)) :=
    (Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₁)).toPerm
  have hσ₀ : Equiv.Perm.TwoShuffle.ofPerm σ₀ = Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₁) := by
    dsimp [σ₀]
    rw [Equiv.Perm.TwoShuffle.ofPerm_toPerm]
  have hσ₀' : ∀ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
      (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftOuter.toPerm = σ₀ := by
    intro q₃
    dsimp [σ₀, Equiv.Perm.ThreeShuffle.rightShuffle]
    simp [Equiv.Perm.ThreeShuffle.rightAssocShuffle_leftOuter,
      Equiv.Perm.TwoShuffle.modSumCongrTwoShuffle]
  have hτ₀' : ∀ q₃ : Equiv.Perm.ModSumCongr (Fin n) (Fin p),
      (Equiv.Perm.ThreeShuffle.rightShuffle m n p (q₁, q₃)).leftInner.toPerm =
        (Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm := by
    intro q₃
    dsimp [Equiv.Perm.ThreeShuffle.rightShuffle]
    simp [Equiv.Perm.ThreeShuffle.rightAssocShuffle_leftInner,
      Equiv.Perm.TwoShuffle.modSumCongrTwoShuffle]
  rw [wedge_mul_assoc_lhs_cosets g h l w (Quot.out q₁) σ₀ hσ₀.symm]
  rw [← wedge_mul_assoc_lhs_inner g h l w σ₀]
  rw [Finset.sum_congr rfl]
  intro q₃ _
  rw [hσ₀' q₃, hτ₀' q₃]
  have hτ : Quotient.mk''
      ((Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm : Equiv.Perm (Fin n ⊕ Fin p)) = q₃ := by
    exact (Equiv.Perm.TwoShuffle.quotient_eq_of_ofPerm_eq (by
      change Equiv.Perm.TwoShuffle.ofPerm ((Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm) =
        Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)
      rw [Equiv.Perm.TwoShuffle.ofPerm_toPerm])).trans (Quotient.out_eq q₃)
  conv_lhs =>
    rw [← hτ]
  rw [uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    ContinuousLinearMap.mul_apply',
    Units.smul_def]
  have hh' : (fun i : Fin n =>
        (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₀ ∘ Sum.inr) ∘ finSumFinEquiv)
          (((Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm : Equiv.Perm (Fin n ⊕ Fin p))
            (Sum.inl i))) =
      (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₀ ∘ Sum.inr ∘ finSumFinEquiv) ∘
        ((Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm : Equiv.Perm
          (Fin n ⊕ Fin p)) ∘ Sum.inl) := by
    funext i
    rfl
  have hl' : (fun i : Fin p =>
        (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₀ ∘ Sum.inr) ∘ finSumFinEquiv)
          (((Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm : Equiv.Perm (Fin n ⊕ Fin p))
            (Sum.inr i))) =
      (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘ σ₀ ∘ Sum.inr ∘ finSumFinEquiv) ∘
        ((Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm : Equiv.Perm
          (Fin n ⊕ Fin p)) ∘ Sum.inr) := by
    funext i
    rfl
  rw [hh', hl']
  simp only [Equiv.Perm.ThreeShuffle.finAssoc_finAssocOrder, OrderIso.coe_symm_toEquiv,
    zsmul_eq_mul]
  rw [show h (((w ∘ (Equiv.Perm.ThreeShuffle.finAssocOrder m n p).symm ∘ finSumFinEquiv) ∘
        σ₀ ∘ Sum.inr ∘ finSumFinEquiv) ∘
        (Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm ∘ Sum.inl) =
      h ((w ∘ (Equiv.Perm.ThreeShuffle.finAssocOrder m n p).symm ∘ finSumFinEquiv) ∘
        σ₀ ∘ Sum.inr ∘ finSumFinEquiv ∘
        (Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm ∘ Sum.inl) from rfl]
  rw [show l (((w ∘ (Equiv.Perm.ThreeShuffle.finAssocOrder m n p).symm ∘ finSumFinEquiv) ∘
        σ₀ ∘ Sum.inr ∘ finSumFinEquiv) ∘
        (Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm ∘ Sum.inr) =
      l ((w ∘ (Equiv.Perm.ThreeShuffle.finAssocOrder m n p).symm ∘ finSumFinEquiv) ∘
        σ₀ ∘ Sum.inr ∘ finSumFinEquiv ∘
        (Equiv.Perm.TwoShuffle.ofPerm (Quot.out q₃)).toPerm ∘ Sum.inr) from rfl]
  ring

private theorem wedge_mul_assoc_lhs_sum (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (w : Fin (m + n + p) → M) :
    (g ∧[𝕜] (h ∧[𝕜] l)) (w ∘ Fin.finAssoc.symm) =
      ∑ P : Equiv.Perm.ThreeShuffle m n p,
        (Equiv.Perm.sign
          (Equiv.Perm.ThreeShuffle.canonicalLeft P) : 𝕜) • placementSummand g h l P w := by
  rw [wedge_mul_assoc_lhs_can]
  rw [← Finset.sum_product (Finset.univ : Finset (Equiv.Perm.ModSumCongr (Fin m) (Fin (n + p))))
    (Finset.univ : Finset (Equiv.Perm.ModSumCongr (Fin n) (Fin p)))
    (fun x : Equiv.Perm.ModSumCongr (Fin m) (Fin (n + p)) × Equiv.Perm.ModSumCongr (Fin n)
      (Fin p) =>
      Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.rightShuffle m n p x).leftOuter.toPerm) •
        Equiv.Perm.sign ((Equiv.Perm.ThreeShuffle.rightShuffle m n p x).leftInner.toPerm) •
          g (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘
            (Equiv.Perm.ThreeShuffle.rightShuffle m n p x).leftOuter.toPerm ∘ Sum.inl)) *
          h (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘
            (Equiv.Perm.ThreeShuffle.rightShuffle m n p x).leftOuter.toPerm ∘ Sum.inr ∘
              finSumFinEquiv ∘
                (Equiv.Perm.ThreeShuffle.rightShuffle m n p x).leftInner.toPerm ∘ Sum.inl)) *
          l (((w ∘ Fin.finAssoc.symm ∘ finSumFinEquiv) ∘
            (Equiv.Perm.ThreeShuffle.rightShuffle m n p x).leftOuter.toPerm ∘ Sum.inr ∘
              finSumFinEquiv ∘
                (Equiv.Perm.ThreeShuffle.rightShuffle m n p x).leftInner.toPerm ∘ Sum.inr)))]
  simp only [Finset.univ_product_univ]
  rw [← Finset.sum_bij (fun x : Equiv.Perm.ModSumCongr (Fin m) (Fin (n + p)) ×
        Equiv.Perm.ModSumCongr (Fin n)
          (Fin p) => fun _ => Equiv.Perm.ThreeShuffle.rightShuffle m n p x)
    (fun x _ => Finset.mem_univ _) (by
      intro a₁ _ a₂ _ h
      exact (Equiv.Perm.ThreeShuffle.rightShuffle m n p).injective h) (by
      intro b _
      refine ⟨(Equiv.Perm.ThreeShuffle.rightShuffle m n p).symm b, Finset.mem_univ _, ?_⟩
      exact (Equiv.Perm.ThreeShuffle.rightShuffle m n p).apply_symm_apply b) (by
      intro a _
      exact wedge_mul_assoc_lhs_can_point g h l w a.1 a.2)]

theorem wedge_mul_assoc (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) :
    domDomCongr Fin.finAssoc.symm (g ∧[𝕜] (h ∧[𝕜] l)) = ((g ∧[𝕜] h) ∧[𝕜] l) := by
  apply ContinuousAlternatingMap.ext
  intro w
  rw [ContinuousAlternatingMap.domDomCongr_apply]
  rw [wedge_mul_assoc_lhs_sum g h l w]
  rw [wedge_mul_assoc_rhs_sum g h l w]
  rw [Finset.sum_congr rfl]
  intro P _
  rw [Equiv.Perm.ThreeShuffle.sign_canonicalLeft_canonicalRight P]
private lemma finAddCongr_val (i : Fin (m + n)) : (Fin.finAddCongr i).val = i.val := rfl

private lemma finAddFlip_trans_finAddCongr_eq :
    (finAddFlip.trans (Fin.finAddCongr (m := n) (n := m)) : Equiv.Perm (Fin (m + n))) =
      (_root_.finCongr (add_comm m n)).symm.permCongr (Equiv.Perm.addCasesSwapPerm n m) := by
  ext i
  by_cases h : i.val < m
  · simp [Equiv.permCongr_apply, Equiv.Perm.addCasesSwapPerm, _root_.finCongr,
      finAddFlip_apply_mk_left h, finAddCongr_val]
    simp [h]
  · have hge : m ≤ i.val := le_of_not_gt h
    simp [Equiv.permCongr_apply, Equiv.Perm.addCasesSwapPerm, _root_.finCongr,
      finAddFlip_apply_mk_right hge, finAddCongr_val]
    simp [h]

private lemma finAddFlip_trans_finAddCongr_sign :
    Equiv.Perm.sign (finAddFlip.trans (Fin.finAddCongr (m := n) (n := m)) :
      Equiv.Perm (Fin (m + n))) = (-1 : ℤˣ) ^ (m * n) := by
  rw [finAddFlip_trans_finAddCongr_eq, Equiv.Perm.sign_permCongr, Equiv.Perm.addCasesSwapPerm_sign]
  exact congrArg (fun k : ℕ => (-1 : ℤˣ) ^ k) (Nat.mul_comm n m)

private lemma units_neg_one_pow_smul {A : Type*} [AddCommGroup A] [Module 𝕜 A] (k : ℕ) (x : A) :
    ((-1 : ℤˣ) ^ k) • x = (-1 : 𝕜) ^ k • x := by
  rw [Units.smul_def]
  rw [← Int.cast_smul_eq_zsmul (R := 𝕜) ((((-1 : ℤˣ) ^ k : ℤˣ) : ℤ)) x]
  have hcast : ((((-1 : ℤˣ) ^ k : ℤˣ) : ℤ) : 𝕜) = (-1 : 𝕜) ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show (-1 : ℤˣ) ^ (k + 1) = (-1 : ℤˣ) ^ k * (-1 : ℤˣ) from pow_succ (-1 : ℤˣ) k]
      rw [pow_succ, Units.val_mul, Int.cast_mul, ih]
      norm_num
  rw [hcast]

private theorem uncurrySum_summand_swap (g : M [⋀^Fin m]→L[𝕜] 𝕜)
    (h : M [⋀^Fin n]→L[𝕜] 𝕜) (v : Fin (n + m) → M)
    (σ : Equiv.Perm.ModSumCongr (Fin n) (Fin m)) :
    uncurrySum.summand (ContinuousLinearMap.mul 𝕜 𝕜 |>.compContinuousAlternatingMap₂ h g)
        σ (v ∘ finSumFinEquiv) =
      uncurrySum.summand (ContinuousLinearMap.mul 𝕜 𝕜 |>.compContinuousAlternatingMap₂ g h)
        (Equiv.Perm.finAddFlipEquiv (m := n) (n := m) σ)
        ((v ∘ finAddFlip) ∘ finSumFinEquiv) := by
  refine Quotient.inductionOn' σ ?_
  intro σ'
  change uncurrySum.summand (ContinuousLinearMap.mul 𝕜 𝕜 |>.compContinuousAlternatingMap₂ h g)
      (Quotient.mk'' σ') (v ∘ finSumFinEquiv) =
    uncurrySum.summand (ContinuousLinearMap.mul 𝕜 𝕜 |>.compContinuousAlternatingMap₂ g h)
      (Quotient.mk'' (Equiv.Perm.sumCommPerm σ'))
      ((v ∘ finAddFlip) ∘ finSumFinEquiv)
  rw [uncurrySum_summand_eval, uncurrySum_summand_eval]
  rw [Equiv.Perm.sign_sumCommPerm]
  congr 1
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  change (h (fun i => (v ∘ finSumFinEquiv) (σ' (Sum.inl i)))) *
      (g (fun i => (v ∘ finSumFinEquiv) (σ' (Sum.inr i)))) =
    (g (fun i => ((v ∘ finAddFlip) ∘ finSumFinEquiv) ((Equiv.Perm.sumCommPerm σ') (Sum.inl i)))) *
      (h (fun i => ((v ∘ finAddFlip) ∘ finSumFinEquiv) ((Equiv.Perm.sumCommPerm σ') (Sum.inr i))))
  rw [mul_comm]
  congr 1
  · apply congrArg g
    funext j
    change v (finSumFinEquiv (σ' (Sum.inr j))) =
      v (finAddFlip (finSumFinEquiv (Equiv.sumComm (Fin n) (Fin m) (σ' (Sum.inr j)))))
    congr 1
    simpa [Equiv.sumComm] using (Fin.finAddFlip_finSumFinEquiv (m := m) (n := n)
      (Equiv.sumComm (Fin n) (Fin m) (σ' (Sum.inr j)))).symm
  · apply congrArg h
    funext i
    change v (finSumFinEquiv (σ' (Sum.inl i))) =
      v (finAddFlip (finSumFinEquiv (Equiv.sumComm (Fin n) (Fin m) (σ' (Sum.inl i)))))
    congr 1
    simpa [Equiv.sumComm] using (Fin.finAddFlip_finSumFinEquiv (m := m) (n := n)
      (Equiv.sumComm (Fin n) (Fin m) (σ' (Sum.inl i)))).symm

private theorem wedge_product_swap (g : M [⋀^Fin m]→L[𝕜] 𝕜)
    (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (h ∧[𝕜] g) = (g ∧[𝕜] h).domDomCongr finAddFlip := by
  ext v
  rw [wedge_product_def]
  rw [ContinuousAlternatingMap.domDomCongr_apply]
  rw [wedge_product_def]
  rw [uncurryFinAdd, uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply, uncurrySum_apply,
    _root_.sum_apply, _root_.sum_apply]
  refine Finset.sum_bij
    (fun (σ : Equiv.Perm.ModSumCongr (Fin n) (Fin m)) _ =>
      Equiv.Perm.finAddFlipEquiv (m := n) (n := m) σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp
  · intro σ₁ hσ₁ σ₂ hσ₂ h
    exact Equiv.injective (Equiv.Perm.finAddFlipEquiv (m := n) (n := m)) h
  · intro τ hτ
    exact ⟨(Equiv.Perm.finAddFlipEquiv (m := n) (n := m)).symm τ, by simp,
      Equiv.apply_symm_apply _ τ⟩
  · intro σ hσ
    exact uncurrySum_summand_swap g h v σ

private lemma domDomCongr_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (f : M [⋀^ι]→L[𝕜] 𝕜) :
    domDomCongr σ f = Equiv.Perm.sign σ • f := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact AlternatingMap.domDomCongr_perm (R := 𝕜) (M := M) (N' := 𝕜) (ι := ι)
    (g := f.toAlternatingMap) σ

theorem wedge_antisymm
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (g ∧[𝕜] h) = ((-1 : 𝕜)^(m*n) • (h ∧[𝕜] g)).domDomCongr Fin.finAddCongr := by
  have hswap : (h ∧[𝕜] g) = (g ∧[𝕜] h).domDomCongr finAddFlip := wedge_product_swap g h
  have h₁ : (h ∧[𝕜] g).domDomCongr Fin.finAddCongr = (-1 : 𝕜) ^ (m * n) • (g ∧[𝕜] h) := by
    rw [hswap]
    rw [domDomCongr_trans (e₁ := finAddFlip) (e₂ := Fin.finAddCongr)
      (f := g ∧[𝕜] h)]
    rw [domDomCongr_perm (finAddFlip.trans (Fin.finAddCongr (m := n) (n := m)))]
    rw [finAddFlip_trans_finAddCongr_sign]
    exact units_neg_one_pow_smul (m * n) (g ∧[𝕜] h)
  rw [ContinuousAlternatingMap.domDomCongr_smul]
  rw [h₁]
  ext v
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [smul_smul]
  have hsq : (-1 : 𝕜) ^ (m * n) * (-1 : 𝕜) ^ (m * n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hsq, one_smul]

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]

open Fin

theorem wedge_self_odd_zero (g : M [⋀^Fin m]→L[𝕜] 𝕜) (m_odd : Odd m) (h2 : (2 : 𝕜) ≠ 0) :
    (g ∧[𝕜] g) = 0 := by
  let h := wedge_antisymm g g
  rw[Odd.neg_one_pow (Odd.mul m_odd m_odd)] at h
  suffices (g ∧[𝕜] g) = -(g ∧[𝕜] g) by
    rw[← sub_eq_zero, sub_neg_eq_add, DFunLike.ext_iff] at this
    ext x
    have hx : (g ∧[𝕜] g) x + (g ∧[𝕜] g) x = 0 := by
      simpa using this x
    rw [← two_mul] at hx
    exact (mul_eq_zero.mp hx).resolve_left h2
  simp only [finAddCongr, finCongr_refl, neg_smul, one_smul, domDomCongr_refl] at h
  exact h

end wedge

end ContinuousAlternatingMap
