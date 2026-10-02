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
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Reindexing.Domain
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

lemma toAlternatingMap_uncurryFin (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    (uncurryFin f).toAlternatingMap = .alternatizeUncurryFin (toAlternatingMapLinear ∘ₗ f) :=
  rfl

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

theorem uncurryFin_uncurryFinCLM_comp_of_symmetric {f : E →L[𝕜] E →L[𝕜] E [⋀^Fin n]→L[𝕜] F}
    (hf : ∀ x y, f x y = f y x) :
    uncurryFin (uncurryFinCLM.comp f) = 0 := by
  let g := LinearMap.compr₂ f.toLinearMap₁₂ toAlternatingMapLinear
  have g_symm : ∀ x y, g x y = g y x := by
    intro x y
    have : g x y = (f x y).toAlternatingMap := rfl
    aesop
  let h₀ := AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_of_symmetric (g_symm)
  exact toAlternatingMap_injective h₀

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

theorem uncurryFin_curryFin (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    uncurryFin (curryFin f) = (n + 1 : ℕ) • f := by
  apply toAlternatingMap_injective
  rw [toAlternatingMap_uncurryFin]
  have h : toAlternatingMapLinear ∘ₗ (curryFin f).toLinearMap =
      AlternatingMap.curryLeft f.toAlternatingMap := by
    ext x m; rfl
  rw [h, AlternatingMap.alternatizeUncurryFin_curryLeft]
  rfl

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

theorem uncurrySum.summand_quot_mk
    (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) (σ : Equiv.Perm (ι ⊕ ι')) :
    uncurrySum.summand f (Quot.mk
    (⇑(QuotientGroup.leftRel (Equiv.Perm.sumCongrHom ι ι').range)) σ) = Equiv.Perm.sign σ •
    (ContinuousMultilinearMap.uncurrySum
    (f.toContinuousMultilinearMap.flipAlternating.toContinuousMultilinearMap.flipMultilinear)
      : ContinuousMultilinearMap 𝕜 (fun _ => E) F).domDomCongr σ :=
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

theorem uncurrySum_coe (f : E [⋀^ι]→L[𝕜] E [⋀^ι']→L[𝕜] F) :
    ((uncurrySum f).toContinuousMultilinearMap : ContinuousMultilinearMap 𝕜 (fun _ => E) F) =
      ∑ σ : Equiv.Perm.ModSumCongr ι ι', uncurrySum.summand f σ :=
  ContinuousMultilinearMap.ext fun _ => rfl

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

theorem summand_left_match
    (F : E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] N'')
    (x : E) (w : Fin (m + 1) ⊕ Fin (n + 1) → E) (hw : w (Sum.inl 0) = x)
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inl k)
    (σ' : Equiv.Perm (Fin m ⊕ Fin (n + 1)))
    (hσ' : Quotient.mk'' σ' = shuffleLeftRestrict
      ⟨Quotient.mk'' σ, shuffleLeftRestrict_subtype_of_inv σ hσ⟩) :
    uncurrySum.summand F (Quotient.mk'' σ) w =
      uncurrySum.summand (curryFin F x) (Quotient.mk'' σ') (w ∘ Sum.map Fin.succ id) := by
  have h_coset : (Quotient.mk'' σ' :
      Equiv.Perm.ModSumCongr (Fin m) (Fin (n + 1))) =
      Quotient.mk'' (shuffleLeftRestrictRepresentative σ hσ) := by
    rw [hσ']
    change Quotient.mk'' (shuffleLeftRestrictRepresentative (Quotient.out (Quotient.mk'' σ)) _) =
      Quotient.mk'' (shuffleLeftRestrictRepresentative σ hσ)
    apply Quotient.sound'
    apply shuffleLeftRestrictRepresentative_respects_leftRel
    rw [QuotientGroup.leftRel_apply]
    have h_eq : (Quotient.mk'' (Quotient.out (Quotient.mk'' σ)) :
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1))) = Quotient.mk'' σ :=
      Quotient.out_eq _
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact' h_eq)
  rw [h_coset]
  set k := hσ.choose
  set hk := hσ.choose_spec
  set σ_can := shuffleLeftRestrictRepresentative σ hσ
  have h_sign : Equiv.Perm.sign σ_can =
      Equiv.Perm.sign σ * Equiv.Perm.sign (Equiv.swap 0 k) := by
    change Equiv.Perm.sign (shuffleLeftRestrictRepresentative σ hσ) = _
    unfold shuffleLeftRestrictRepresentative
    rw [restrictComplement_sign _ (normalizeLeft_fixes σ k hk)]
    unfold normalizeLeft
    rw [Equiv.Perm.sign_mul]
    congr 1
    rw [Equiv.Perm.sign_sumCongr]; simp
  rw [uncurrySum_summand_eval, uncurrySum_summand_eval]
  set ν := normalizeLeft σ k
  have hν_fix : ν (Sum.inl 0) = Sum.inl 0 := normalizeLeft_fixes σ k hk
  have hσ_can_eq : σ_can = restrictComplement ν := rfl
  have hν_inl : ∀ a : Fin (m + 1), ν (Sum.inl a) = σ (Sum.inl ((Equiv.swap 0 k) a)) := by
    intro a; rfl
  have hν_inr : ∀ b : Fin (n + 1), ν (Sum.inr b) = σ (Sum.inr b) := by
    intro b; rfl
  have hw'_inl : ∀ j : Fin m, (w ∘ Sum.map Fin.succ id) (σ_can (Sum.inl j)) =
      w (ν (Sum.inl j.succ)) := by
    intro j
    change w (Sum.map Fin.succ id (σ_can (Sum.inl j))) = w (ν (Sum.inl j.succ))
    rw [hσ_can_eq, restrictComplement_lift ν hν_fix (Sum.inl j)]
    rfl
  have hw'_inr : ∀ b : Fin (n + 1), (w ∘ Sum.map Fin.succ id) (σ_can (Sum.inr b)) =
      w (ν (Sum.inr b)) := by
    intro b
    change w (Sum.map Fin.succ id (σ_can (Sum.inr b))) = w (ν (Sum.inr b))
    rw [hσ_can_eq, restrictComplement_lift ν hν_fix (Sum.inr b)]
    rfl
  have h_inr_eq : (fun i => w (σ (Sum.inr i))) =
      (fun i => (w ∘ Sum.map Fin.succ id) (σ_can (Sum.inr i))) := by
    funext b; rw [hw'_inr, hν_inr]
  have h_first_eq : ((fun i => w (σ (Sum.inl i))) ∘ (Equiv.swap (0 : Fin (m + 1)) k)) =
      Fin.cons x (fun j => (w ∘ Sum.map Fin.succ id) (σ_can (Sum.inl j))) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.cons_zero]
      rw [show σ (Sum.inl k) = Sum.inl (0 : Fin (m + 1)) from ?_, hw]
      have := hk; rw [← Equiv.eq_symm_apply] at this; exact this.symm
    · intro j
      simp only [Function.comp_apply, Fin.cons_succ]
      rw [hσ_can_eq, restrictComplement_lift ν hν_fix (Sum.inl j),
          show Sum.map Fin.succ id (Sum.inl j : Fin m ⊕ Fin (n + 1)) =
            Sum.inl j.succ from rfl, hν_inl]
  have h_alt : (F ((fun i => w (σ (Sum.inl i))) ∘ (Equiv.swap (0 : Fin (m + 1)) k)) :
      E [⋀^Fin (n + 1)]→L[𝕜] N'') =
      Equiv.Perm.sign (Equiv.swap (0 : Fin (m + 1)) k) • F (fun i => w (σ (Sum.inl i))) := by
    have := F.toAlternatingMap.map_perm (fun i => w (σ (Sum.inl i)))
      (Equiv.swap (0 : Fin (m + 1)) k)
    simp only [ContinuousAlternatingMap.coe_toAlternatingMap] at this
    exact this
  rw [h_inr_eq]
  rw [show (curryFin F x) (fun j => (w ∘ Sum.map Fin.succ id) (σ_can (Sum.inl j))) =
      F (Fin.cons x (fun j => (w ∘ Sum.map Fin.succ id) (σ_can (Sum.inl j)))) from rfl]
  rw [← h_first_eq]
  rw [h_alt]
  rw [h_sign]
  simp only [ContinuousAlternatingMap.smul_apply]
  rw [smul_smul, mul_assoc, Int.units_mul_self, mul_one]

theorem summand_right_match
    (F : E [⋀^Fin (m + 1)]→L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] N'')
    (x : E) (w : Fin (m + 1) ⊕ Fin (n + 1) → E) (hw : w (Sum.inl 0) = x)
    (σ : Equiv.Perm (Fin (m + 1) ⊕ Fin (n + 1)))
    (hσ : ∃ k, σ⁻¹ (Sum.inl 0) = Sum.inr k)
    (σ' : Equiv.Perm (Fin (m + 1) ⊕ Fin n))
    (hσ' : Quotient.mk'' σ' =
      shuffleRightRestrict ⟨Quotient.mk'' σ,
        shuffleRightRestrict_subtype_of_inv σ hσ⟩) :
    uncurrySum.summand F (Quotient.mk'' σ) w =
      -(uncurrySum.summand (curryFinRight F x) (Quotient.mk'' σ')
        (fun y => w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
          (Sum.map id Fin.succ y)))) := by
  have h_coset : (Quotient.mk'' σ' :
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin n)) =
      Quotient.mk'' (shuffleRightRestrictRepresentative σ hσ) := by
    rw [hσ']
    change Quotient.mk'' (shuffleRightRestrictRepresentative (Quotient.out (Quotient.mk'' σ)) _) =
      Quotient.mk'' (shuffleRightRestrictRepresentative σ hσ)
    apply Quotient.sound'
    apply shuffleRightRestrictRepresentative_respects_leftRel
    rw [QuotientGroup.leftRel_apply]
    have h_eq : (Quotient.mk'' (Quotient.out (Quotient.mk'' σ)) :
      Equiv.Perm.ModSumCongr (Fin (m + 1)) (Fin (n + 1))) = Quotient.mk'' σ :=
      Quotient.out_eq _
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact' h_eq)
  rw [h_coset]
  set k := hσ.choose
  set hk := hσ.choose_spec
  set σ_can := shuffleRightRestrictRepresentative σ hσ
  have h_sign : Equiv.Perm.sign σ_can =
      -Equiv.Perm.sign σ * Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) k) := by
    change Equiv.Perm.sign (shuffleRightRestrictRepresentative σ hσ) = _
    unfold shuffleRightRestrictRepresentative
    rw [restrictComplementRight_sign _ (normalizeRight_fixes σ k hk)]
    unfold normalizeRight
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_sumCongr,
      Equiv.Perm.sign_swap (show (Sum.inl (0 : Fin (m + 1)) : Fin (m + 1) ⊕ Fin (n + 1)) ≠
        Sum.inr 0 from by simp)]
    simp
  set ν := normalizeRight σ k
  have hν_fix : ν (Sum.inr 0) = Sum.inr 0 := normalizeRight_fixes σ k hk
  have hσ_can_eq : σ_can = restrictComplementRight ν := rfl
  have hν_inl : ∀ a : Fin (m + 1),
      ν (Sum.inl a) =
        Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0) (σ (Sum.inl a)) := by
    intro a; rfl
  have hν_inr : ∀ b : Fin (n + 1),
      ν (Sum.inr b) =
        Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
          (σ (Sum.inr ((Equiv.swap (0 : Fin (n + 1)) k) b))) := by
    intro b; rfl
  have hw_R_inl : ∀ j : Fin (m + 1),
      w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
        (Sum.map id Fin.succ (σ_can (Sum.inl j)))) =
      w (σ (Sum.inl j)) := by
    intro j
    rw [hσ_can_eq, restrictComplementRight_lift ν hν_fix (Sum.inl j)]
    change w (Equiv.swap _ _ (ν (Sum.inl j))) = _
    rw [hν_inl, Equiv.swap_apply_self]
  have hw_R_inr : ∀ j : Fin n,
      w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
        (Sum.map id Fin.succ (σ_can (Sum.inr j)))) =
      w (σ (Sum.inr ((Equiv.swap (0 : Fin (n + 1)) k) j.succ))) := by
    intro j
    rw [hσ_can_eq, restrictComplementRight_lift ν hν_fix (Sum.inr j)]
    change w (Equiv.swap _ _ (ν (Sum.inr j.succ))) = _
    rw [hν_inr, Equiv.swap_apply_self]
  rw [uncurrySum_summand_eval, uncurrySum_summand_eval]
  have h_first_eq : (fun i => w (σ (Sum.inl i))) =
      (fun i => w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
        (Sum.map id Fin.succ (σ_can (Sum.inl i))))) := by
    funext i; rw [hw_R_inl]
  have h_second_eq : ((fun i => w (σ (Sum.inr i))) ∘ (Equiv.swap (0 : Fin (n + 1)) k)) =
      Fin.cons x (fun j => w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
        (Sum.map id Fin.succ (σ_can (Sum.inr j))))) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp only [Function.comp_apply, Equiv.swap_apply_left, Fin.cons_zero]
      rw [show σ (Sum.inr k) = Sum.inl (0 : Fin (m + 1)) from ?_, hw]
      have := hk; rw [← Equiv.eq_symm_apply] at this; exact this.symm
    · intro j
      simp only [Function.comp_apply, Fin.cons_succ]
      rw [hw_R_inr]
  have h_alt : (F (fun i => w (σ (Sum.inl i))) :
      E [⋀^Fin (n + 1)]→L[𝕜] N'')
      ((fun i => w (σ (Sum.inr i))) ∘ (Equiv.swap (0 : Fin (n + 1)) k)) =
      Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) k) •
        (F (fun i => w (σ (Sum.inl i)))) (fun i => w (σ (Sum.inr i))) := by
    have := (F (fun i => w (σ (Sum.inl i)))).toAlternatingMap.map_perm
      (fun i => w (σ (Sum.inr i))) (Equiv.swap (0 : Fin (n + 1)) k)
    simp only [ContinuousAlternatingMap.coe_toAlternatingMap] at this
    exact this
  change Equiv.Perm.sign σ • F _ _ = -(Equiv.Perm.sign σ_can • _)
  rw [show ((curryFinRight F x)
      (fun i => w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
        (Sum.map id Fin.succ (σ_can (Sum.inl i)))) :
        Fin (m + 1) → E) :
      E [⋀^Fin n]→L[𝕜] N'')
      (fun i => w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
        (Sum.map id Fin.succ (σ_can (Sum.inr i))))) =
    F (fun i => w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
        (Sum.map id Fin.succ (σ_can (Sum.inl i)))))
      (Fin.cons x (fun i => w (Equiv.swap (Sum.inl (0 : Fin (m + 1))) (Sum.inr 0)
        (Sum.map id Fin.succ (σ_can (Sum.inr i)))))) from rfl]
  rw [← h_first_eq, ← h_second_eq, h_alt, h_sign]
  rw [smul_smul]
  rw [show (-Equiv.Perm.sign σ * Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) k)) *
      Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) k) = -Equiv.Perm.sign σ from by
    rw [mul_assoc, Int.units_mul_self, mul_one]]
  rw [show (-Equiv.Perm.sign σ : ℤˣ) • (F (fun i => w (σ (Sum.inl i)))
      : E [⋀^Fin (n + 1)]→L[𝕜] N'') (fun i => w (σ (Sum.inr i))) =
    -(Equiv.Perm.sign σ • (F (fun i => w (σ (Sum.inl i))))
      (fun i => w (σ (Sum.inr i)))) from by
    rw [Units.neg_smul]]
  rw [neg_neg]

theorem curryFin_sum_smul_clm {κ : Type*} {p : ℕ}
    (s : Finset κ) (c : κ → 𝕜)
    (f : κ → E [⋀^Fin (p + 1)]→L[𝕜] F) :
    curryFin (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • curryFin (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    ext y v; simp [curryFin_apply]
  | insert _ _ hni ih =>
    rw [Finset.sum_insert hni, curryFin_add, curryFin_smul, ih, Finset.sum_insert hni]

theorem curryFin_sum_smul {κ : Type*} {p : ℕ}
    (s : Finset κ) (c : κ → 𝕜)
    (f : κ → E [⋀^Fin (p + 1)]→L[𝕜] F) (x : E) :
    curryFin (∑ i ∈ s, c i • f i) x = ∑ i ∈ s, c i • curryFin (f i) x := by
  have := congr_fun (congr_arg DFunLike.coe (curryFin_sum_smul_clm s c f)) x
  simpa only [_root_.sum_apply, _root_.smul_apply] using this

end curry
end ContinuousAlternatingMap
