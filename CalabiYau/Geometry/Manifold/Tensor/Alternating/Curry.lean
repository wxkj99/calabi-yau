-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Curry.lean
-- Locally modified.
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Flip
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Composition
public import CalabiYau.Mathlib.Analysis.Normed.Module.Alternating.DomCongr
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Shuffle.Decomposition
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.Tactic.Cases

@[expose] public section

namespace ContinuousAlternatingMap

noncomputable section curry

variable {𝕜 E F G ι ι' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [Fintype ι] [Fintype ι']
  {m n : ℕ}

def uncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) : E [⋀^Fin (n + 1)]→L[𝕜] F :=
  AlternatingMap.mkContinuous (.alternatizeUncurryFin <| toAlternatingMapLinear ∘ₗ f)
    ((n + 1) * ‖f‖) fun v ↦ calc
      _ = ‖∑ k, (-1) ^ k.val • f (v k) (k.removeNth v)‖ := by
        simp [AlternatingMap.alternatizeUncurryFin_apply]
      _ ≤ ∑ k, ‖f‖ * ‖v k‖ * ∏ j, ‖v (k.succAbove j)‖ := by
        refine norm_sum_le_of_le _ fun k _ ↦ ?_
        rw [norm_isUnit_zsmul _ (.pow _ isUnit_one.neg)]
        exact (f (v k)).le_of_opNorm_le (f.le_opNorm _) _
      _ = _ := by
        simp [mul_assoc, ← Fin.prod_univ_succAbove (‖v ·‖)]

theorem norm_uncurryFin_le (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    ‖uncurryFin f‖ ≤ (n + 1) * ‖f‖ :=
  AlternatingMap.mkContinuous_norm_le _ (by positivity) _

theorem uncurryFin_apply (f : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) (v : Fin (n + 1) → E) :
    uncurryFin f v = ∑ k, (-1) ^ k.val • f (v k) (k.removeNth v) :=
  AlternatingMap.alternatizeUncurryFin_apply ..

theorem uncurryFin_add (f g : E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) :
    uncurryFin (f + g) = uncurryFin f + uncurryFin g := by
  ext v
  simp [uncurryFin_apply, Finset.sum_add_distrib]

theorem uncurryFin_smul {M : Type*} [Monoid M] [DistribMulAction M F] [ContinuousConstSMul M F]
    [SMulCommClass 𝕜 M F] (c : M) (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    uncurryFin (c • f) = c • uncurryFin f := by
  ext v
  simp [uncurryFin_apply, smul_comm _ c, Finset.smul_sum]

@[simps! apply]
def uncurryFinCLM :
    (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F :=
  LinearMap.mkContinuous
    { toFun := uncurryFin (𝕜 := 𝕜) (E := E) (F := F) (n := n)
      map_add' := by exact uncurryFin_add
      map_smul' := by exact uncurryFin_smul }
    (n + 1) norm_uncurryFin_le

def curryFin (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  f.curryLeft

theorem curryFin_apply (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (m : Fin n → E) :
    curryFin f x m = f (Fin.cons x m) :=
  rfl

theorem norm_curryFin_le (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    ‖curryFin f‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun x => ?_)
  refine ContinuousAlternatingMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun m => ?_)
  rw [curryFin_apply]
  exact f.1.norm_map_cons_le x m

theorem curryFin_add (f g : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryFin (f + g) = curryFin f + curryFin g := by
  ext e v
  simp [curryFin_apply]

theorem curryFin_smul {M : Type*} [Monoid M] [DistribMulAction M F] [ContinuousConstSMul M F]
    [SMulCommClass 𝕜 M F] (c : M) (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryFin (c • f) = c • curryFin f := by
  ext e v
  simp [curryFin_apply]

def curryFinRight
    (F : E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] G) (x : E) :
    E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin n]→L[𝕜] G :=
  let g : (E [⋀^Fin (n + 1)]→L[𝕜] G) →L[𝕜] (E [⋀^Fin n]→L[𝕜] G) :=
    LinearMap.mkContinuous
      { toFun := fun f => curryFin f x
        map_add' := fun f₁ f₂ => by rw [curryFin_add]; rfl
        map_smul' := fun c f => by rw [curryFin_smul]; rfl }
      ‖x‖
      (fun f => by
        change ‖curryFin f x‖ ≤ ‖x‖ * ‖f‖
        calc ‖curryFin f x‖
            ≤ ‖curryFin f‖ * ‖x‖ := (curryFin f).le_opNorm x
          _ ≤ ‖f‖ * ‖x‖ := by
              exact mul_le_mul_of_nonneg_right (norm_curryFin_le f) (norm_nonneg _)
          _ = ‖x‖ * ‖f‖ := by ring)
  g.compContinuousAlternatingMap F

@[simp] theorem curryFinRight_apply
    (F : E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] G)
    (x : E) (v : Fin (m + 1) → E) (w : Fin n → E) :
    curryFinRight F x v w = F v (Fin.cons x w) := by
  change curryFin (F v) x w = F v (Fin.cons x w)
  rw [curryFin_apply]

variable [DecidableEq ι] [DecidableEq ι']

def uncurrySum.summand (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm.ModSumCongr ι ι') :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => E) F :=
  Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (ContinuousMultilinearMap.uncurrySum
          (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
            : ContinuousMultilinearMap 𝕜 (fun _ => E) (F)).domDomCongr σ)
    fun σ₁ σ₂ H => by
      rw [QuotientGroup.leftRel_apply] at H
      obtain ⟨⟨sl, sr⟩, h⟩ := H
      ext v
      simp only [_root_.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
        ContinuousMultilinearMap.uncurrySum_apply]
      replace h := inv_mul_eq_iff_eq_mul.mp h.symm
      have : Equiv.Perm.sign (σ₁ * Equiv.Perm.sumCongrHom _ _ (sl, sr))
        = Equiv.Perm.sign σ₁ * (Equiv.Perm.sign sl * Equiv.Perm.sign sr) := by simp
      rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, smul_comm]
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]
      erw [← (f.flipAlternating
        ((fun i ↦ v (σ₁ (Sum.map (⇑sl) (⇑sr) i))) ∘ Sum.inr)).map_congr_perm fun i => v (σ₁ _)]
      simp only [AlternatingMap.coe_mk, ContinuousMultilinearMap.coe_coe,
        coe_toContinuousMultilinearMap]
      erw [← (f fun i ↦ v (σ₁ (Sum.inl i))).map_congr_perm fun i => v (σ₁ _)]
      simp [ContinuousMultilinearMap.flipAlternating]
      rfl

theorem uncurrySum.summand_quotient_mk
    (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm (ι ⊕ ι')) :
    uncurrySum.summand f (Quotient.mk'' σ) = Equiv.Perm.sign σ •
    (ContinuousMultilinearMap.uncurrySum
    (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
      : ContinuousMultilinearMap 𝕜 (fun _ => E) F).domDomCongr σ :=
  rfl

theorem uncurrySum_summand_eval
    (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm (ι ⊕ ι')) (v : ι ⊕ ι' → E) :
    uncurrySum.summand f (Quotient.mk'' σ) v =
      Equiv.Perm.sign σ • f (fun i => v (σ (Sum.inl i))) (fun i => v (σ (Sum.inr i))) := by
  rw [uncurrySum.summand_quotient_mk]
  rfl

theorem uncurrySum.summand_add_swap_smul_eq_zero (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm.ModSumCongr ι ι') {v : ι ⊕ ι' → E}
    {i j : ι ⊕ ι'} (hv : v i = v j) (hij : i ≠ j) :
    uncurrySum.summand f σ v + uncurrySum.summand f (Equiv.swap i j • σ) v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  change uncurrySum.summand f (Quotient.mk'' σ) v +
    uncurrySum.summand f (Quotient.mk'' (Equiv.swap i j * σ)) v = 0
  rw [uncurrySum_summand_eval, uncurrySum_summand_eval,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  have hleft : (fun k : ι => v ((Equiv.swap i j * σ) (Sum.inl k))) =
      fun k : ι => v (σ (Sum.inl k)) := by
    funext k
    exact Equiv.apply_swap_eq_self hv (σ (Sum.inl k))
  have hright : (fun k : ι' => v ((Equiv.swap i j * σ) (Sum.inr k))) =
      fun k : ι' => v (σ (Sum.inr k)) := by
    funext k
    exact Equiv.apply_swap_eq_self hv (σ (Sum.inr k))
  rw [hleft, hright]
  rw [mul_smul, Units.neg_smul, one_smul]
  exact add_neg_cancel
    (Equiv.Perm.sign σ • f (fun k => v (σ (Sum.inl k))) (fun k => v (σ (Sum.inr k))))

theorem uncurrySum.summand_eq_zero_of_smul_invariant (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F)
    (σ : Equiv.Perm.ModSumCongr ι ι') {v : ι ⊕ ι' → E}
    {i j : ι ⊕ ι'} (hv : v i = v j) (hij : i ≠ j) :
    Equiv.swap i j • σ = σ → uncurrySum.summand f σ v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  intro hσ
  rw [uncurrySum_summand_eval]
  rcases hi : σ⁻¹ i with val | val <;> rcases hj : σ⁻¹ j with val_1 | val_1 <;>
    rw [Equiv.Perm.inv_eq_iff_eq] at hi hj <;> subst hi hj <;> revert val val_1
  case inl.inr =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inl i')
    dsimp only at hσ
    rw [smul_eq_mul, ← Equiv.mul_swap_eq_swap_mul, mul_inv_rev, Equiv.swap_inv,
      inv_mul_cancel_right] at hσ
    simp at hσ
  case inr.inl =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inr i')
    dsimp only at hσ
    rw [smul_eq_mul, ← Equiv.mul_swap_eq_swap_mul, mul_inv_rev, Equiv.swap_inv,
      inv_mul_cancel_right] at hσ
    simp at hσ
  case inr.inr =>
    intro i' j' hv hij _
    have hz := (f (fun i => v (σ (Sum.inl i)))).map_eq_zero_of_eq
      (fun i => v (σ (Sum.inr i))) hv fun hij' =>
        hij (congrArg (fun i => σ (Sum.inr i)) hij')
    rw [hz]
    exact smul_zero _
  case inl.inl =>
    intro i' j' hv hij _
    have hz := f.map_eq_zero_of_eq (fun i => v (σ (Sum.inl i))) hv fun hij' =>
        hij (congrArg (fun i => σ (Sum.inl i)) hij')
    rw [hz]
    change Equiv.Perm.sign σ • (0 : F) = 0
    exact smul_zero _

def uncurrySum (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) : E [⋀^ι ⊕ ι']→L[𝕜] F :=
    { ∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ with
    toFun := fun v => (⇑(∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      rw [_root_.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => uncurrySum.summand_add_swap_smul_eq_zero f σ hv hij)
          (fun σ _ => mt <| uncurrySum.summand_eq_zero_of_smul_invariant f σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.swap_smul_involutive i j σ }

theorem uncurrySum_apply (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (m : ι ⊕ ι' → E) :
    uncurrySum f m = (∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ) m :=
  rfl

def uncurryFinAdd (f : E [⋀^Fin m]→L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    E [⋀^Fin (m + n)]→L[𝕜] F :=
  ContinuousAlternatingMap.domDomCongr finSumFinEquiv (uncurrySum f)

variable [DecidableEq ι] [DecidableEq ι']

open scoped TensorProduct

theorem lift_comp_domCoprod_eq_uncurrySum
    {N N' N'' : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    [NormedAddCommGroup N'] [NormedSpace 𝕜 N'] [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
    (g : E [⋀^Fin m]→L[𝕜] N) (h : E [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'')
    (φ : N ⊗[𝕜] N' →ₗ[𝕜] N'') (hφ : ∀ a b, φ (a ⊗ₜ[𝕜] b) = f a b) :
    φ.compAlternatingMap (g.toAlternatingMap.domCoprod h.toAlternatingMap) =
      (uncurrySum (f.compContinuousAlternatingMap₂ g h)).toAlternatingMap := by
  ext w; simp only [LinearMap.compAlternatingMap_apply, coe_toAlternatingMap]
  change φ ((g.toAlternatingMap.domCoprod h.toAlternatingMap) w) =
    (uncurrySum (f.compContinuousAlternatingMap₂ g h)) w
  rw [uncurrySum_apply, _root_.sum_apply,
    AlternatingMap.domCoprod_apply, _root_.sum_apply, _root_.map_sum φ]
  apply Finset.sum_congr rfl; intro q _
  induction q using Quotient.inductionOn' with | h σ =>
  simp only [AlternatingMap.domCoprod.summand_mk'', uncurrySum.summand_quotient_mk,
    _root_.smul_apply, MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.uncurrySum_apply,
    Function.comp_def]
  simp only [ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [LinearMap.map_smul_of_tower φ, hφ]; rfl

variable {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']

end curry
end ContinuousAlternatingMap
