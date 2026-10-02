-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Alternating/Composition.lean
-- Locally modified.
/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Coauthors: Jack McCarthy
-/
module
public import CalabiYau.Mathlib.Analysis.Normed.Module.Multilinear.Composition
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import CalabiYau.Mathlib.Analysis.Calculus.ContDiff.LinearIsometry
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

@[expose] public section


open ContinuousAlternatingMap

noncomputable section Comp

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι : Type*} [Fintype ι]
  {ι' : Type*} [Fintype ι']
def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' := by
  let F₁ : MultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') := MultilinearMap.mk
    (toFun := fun v => (f (g v)).compContinuousAlternatingMap h)
    (map_update_add' := fun m i x y => by
      simp only [ContinuousAlternatingMap.map_update_add, map_add]
      congr)
    (map_update_smul' := fun m i c x => by
      rw [ContinuousAlternatingMap.map_update_smul, ContinuousLinearMap.map_smul]
      congr)
  let F₂ : ContinuousMultilinearMap 𝕜 (fun _ ↦ M) (M' [⋀^ι']→L[𝕜] N'') :=
    F₁.mkContinuous (‖f‖ * ‖g‖ * ‖h‖) (H := by
      intro m
      unfold F₁
      simp only [MultilinearMap.coe_mk]
      apply ContinuousAlternatingMap.opNorm_le_bound
      · positivity
      intro m'
      simp only [compContinuousAlternatingMap_coe, Function.comp_apply]
      calc
        ‖(f (g m)) (h m')‖ ≤ ‖f (g m)‖ * ‖h m'‖ := ContinuousLinearMap.le_opNorm (f (g m)) (h m')
        _ ≤ ‖f (g m)‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_left
          · exact ContinuousAlternatingMap.le_opNorm h m'
          positivity
        _ ≤ ‖f‖ * ‖g m‖ * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · exact ContinuousLinearMap.le_opNorm f (g m)
          positivity
        _ ≤ ‖f‖ * (‖g‖ * ∏ i, ‖m i‖) * (‖h‖ * ∏ i, ‖m' i‖) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left
            · exact ContinuousAlternatingMap.le_opNorm g m
            positivity
          positivity
        _ = (‖f‖ * ‖g‖ * ‖h‖ * ∏ i, ‖m i‖) * ∏ i, ‖m' i‖ := by ring)
  exact ContinuousAlternatingMap.mk F₂ (map_eq_zero_of_eq' := by
    intro v i j h₁ h₂
    simp only [MultilinearMap.toFun_eq_coe, ContinuousMultilinearMap.coe_coe,
      MultilinearMap.coe_mkContinuous, MultilinearMap.coe_mk, F₂, F₁]
    have : g v = 0 := g.map_eq_zero_of_eq' v i j h₁ h₂
    rw [this, ContinuousLinearMap.map_zero]
    ext v'
    rfl)

theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m') :=
  rfl

end ContinuousLinearMap

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {ι ι' : Type*}
variable
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
section

variable [Fintype ι] [Fintype ι']

def compContinuousAlternatingMap₂ (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') : M [⋀^ι]→L[𝕜] M' [⋀^ι']→L[𝕜] N'' :=
  f.compContinuousAlternatingMap₂ g h

theorem compContinuousAlternatingMap₂_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^ι]→L[𝕜] N) (h : M' [⋀^ι']→L[𝕜] N') (m : ι → M) (m' : ι' → M') :
    f.compContinuousAlternatingMap₂ g h m m' = f (g m) (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_mul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] 𝕜) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) * (h m') :=
  rfl

theorem compContinuousAlternatingMap₂_lsmul_apply
    (g : M [⋀^ι]→L[𝕜] 𝕜) (h : M' [⋀^ι']→L[𝕜] N) (m : ι → M) (m' : ι' → M') :
    (ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h m m' = (g m) • (h m') :=
  rfl

end

section

variable [Fintype ι']

theorem compContinuousLinearMap_add {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (L₁ L₂ : E [⋀^ι]→L[𝕜] N)
    (A : E' →L[𝕜] E) :
    (L₁ + L₂).compContinuousLinearMap A =
      L₁.compContinuousLinearMap A + L₂.compContinuousLinearMap A := by
  ext v
  rfl

theorem compContinuousLinearMap_smul {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (c : 𝕜) (L : E [⋀^ι]→L[𝕜] N)
    (A : E' →L[𝕜] E) :
    (c • L).compContinuousLinearMap A = c • L.compContinuousLinearMap A := by
  ext v
  rfl

theorem compContinuousLinearMap_zero {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] (A : E' →L[𝕜] E) :
    (0 : E [⋀^ι]→L[𝕜] N).compContinuousLinearMap A = 0 := by
  ext v
  rfl

end

end ContinuousAlternatingMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Finite ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

end Continuous

section Smooth
variable {𝕜 ι F₁ F₂} [NontriviallyNormedField 𝕜]
open scoped Bundle Manifold

variable [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] in
private theorem norm_alternatization_le (f : ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) :
    ‖ContinuousMultilinearMap.alternatization f‖ ≤
      (Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖ := by
  refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
  change ‖ContinuousMultilinearMap.alternatization f v‖ ≤
    (Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖ * ∏ i, ‖v i‖
  rw [ContinuousMultilinearMap.alternatization_apply_apply]
  calc
    ‖∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ)‖
        ≤ ∑ σ : Equiv.Perm ι, ‖Equiv.Perm.sign σ • f (v ∘ σ)‖ := norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm ι, ‖f‖ * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro σ _
      have hnorm : ‖Equiv.Perm.sign σ • f (v ∘ σ)‖ = ‖f (v ∘ σ)‖ := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
      rw [hnorm]
      calc
        ‖f (v ∘ σ)‖ ≤ ‖f‖ * ∏ i, ‖(v ∘ σ) i‖ := ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖f‖ * ∏ i, ‖v i‖ := by
          simp only [Function.comp_apply]
          rw [Equiv.prod_comp σ (fun i => ‖v i‖)]
    _ = (Fintype.card (Equiv.Perm ι) : ℝ) * (‖f‖ * ∏ i, ‖v i‖) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖ * ∏ i, ‖v i‖ := by ring

section

variable [CharZero 𝕜] [Fintype ι] [DecidableEq ι] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

noncomputable def ContinuousMultilinearMap.alternatizationCLM : (ContinuousMultilinearMap 𝕜
    (fun _ : ι => F₁) F₂) →L[𝕜]
    (F₁ [⋀^ι]→L[𝕜] F₂) :=
  LinearMap.mkContinuous
    { toFun := fun f => (↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹ •
        ContinuousMultilinearMap.alternatization f
      map_add' := by
        intro f g
        ext v
        rw [show ContinuousMultilinearMap.alternatization (f + g) =
            ContinuousMultilinearMap.alternatization f +
              ContinuousMultilinearMap.alternatization g from
          (ContinuousMultilinearMap.alternatization.map_add f g)]
        rw [smul_add]
      map_smul' := by
        intro c f
        have hlin : ContinuousMultilinearMap.alternatization (c • f) =
            c • ContinuousMultilinearMap.alternatization f := by
          ext v
          rw [ContinuousMultilinearMap.alternatization_apply_apply]
          simp only [_root_.smul_apply]
          rw [ContinuousAlternatingMap.smul_apply,
            ContinuousMultilinearMap.alternatization_apply_apply,
            Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro σ _
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
        ext v
        simp only [ContinuousAlternatingMap.smul_apply, hlin]
        exact smul_comm ((↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹) c
          (ContinuousMultilinearMap.alternatization f v) }
    (‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ * Fintype.card (Equiv.Perm ι))
    (by
      intro f
      calc
        ‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹ • ContinuousMultilinearMap.alternatization f‖
            ≤ ‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ *
                ‖ContinuousMultilinearMap.alternatization f‖ :=
              norm_smul_le (r := (↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹)
                (x := ContinuousMultilinearMap.alternatization f)
        _ ≤ ‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ *
                ((Fintype.card (Equiv.Perm ι) : ℝ) * ‖f‖) := by
          exact mul_le_mul_of_nonneg_left (norm_alternatization_le f) (norm_nonneg _)
        _ = (‖(↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹‖ * Fintype.card (Equiv.Perm ι)) * ‖f‖ := by
          ring)

theorem ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap
    (L : F₁ [⋀^ι]→L[𝕜] F₂) :
    ContinuousMultilinearMap.alternatizationCLM
      (ContinuousAlternatingMap.toContinuousMultilinearMap L) = L := by
  ext v
  simp only [ContinuousMultilinearMap.alternatizationCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousAlternatingMap.smul_apply]
  rw [ContinuousMultilinearMap.alternatization_apply_apply]
  change ((↑(Fintype.card (Equiv.Perm ι)) : 𝕜)⁻¹ •
    (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • L (v ∘ σ))) = L v
  have hsum : ∑ σ : Equiv.Perm ι,
    Equiv.Perm.sign σ • L (v ∘ σ) = (Fintype.card (Equiv.Perm ι) : 𝕜) • L v := by
    calc
      (∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • L (v ∘ σ)) = ∑ σ : Equiv.Perm ι, L v := by
        apply Finset.sum_congr rfl
        intro σ _
        change Equiv.Perm.sign σ • (L.toAlternatingMap (v ∘ σ)) = L.toAlternatingMap v
        rw [L.toAlternatingMap.map_perm v σ]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
        · rw [hs]
          exact (one_zsmul (a := ((↑(1 : ℤˣ) : ℤ) • L.toAlternatingMap v))).trans
            (one_zsmul (a := L.toAlternatingMap v))
        · rw [hs]
          exact ((neg_one_zsmul (x := ((↑(-1 : ℤˣ) : ℤ) • L.toAlternatingMap v))).trans
            (congrArg Neg.neg (neg_one_zsmul (x := L.toAlternatingMap v)))).trans
            (neg_neg (a := L.toAlternatingMap v))
      _ = (Fintype.card (Equiv.Perm ι) : 𝕜) • L v := by
        rw [Finset.sum_const]
        exact (Nat.cast_smul_eq_nsmul 𝕜 (Fintype.card (Equiv.Perm ι)) (L v)).symm
  rw [hsum]
  simp only [Fintype.card_perm, smul_smul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos (Fintype.card ι)).ne',
    Nat.factorial_ne_zero (Fintype.card ι)]
  simp

end

section

variable [CharZero 𝕜] [Fintype ι] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff :
    ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ =>
      (compContinuousLinearMapCLM p : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜]
        (F₁ [⋀^ι]→L[𝕜] F₂))) := by
  classical
  let ψ : (F₁ [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let altCLM : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
    ContinuousMultilinearMap.alternatizationCLM
  let B : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) →ₗ[𝕜]
      (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
    { toFun := fun M => altCLM.comp (M.comp ψ.toContinuousLinearMap)
      map_add' := by intro M₁ M₂; ext L; simp
      map_smul' := by intro c M; ext L; simp }
  have hbound : ∀ (M : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)),
      ‖B M‖ ≤ ‖altCLM‖ * ‖M‖ := by
    intro M
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg altCLM)
      (norm_nonneg M)) ?_
    intro L
    calc
      ‖altCLM (M (ψ L))‖ ≤ ‖altCLM‖ * ‖M (ψ L)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖altCLM‖ * (‖M‖ * ‖L‖) := by
        have h1 : ‖M (ψ L)‖ ≤ ‖M‖ * ‖L‖ := by
          calc
            ‖M (ψ L)‖ ≤ ‖M‖ * ‖ψ L‖ := ContinuousLinearMap.le_opNorm M (ψ L)
            _ = ‖M‖ * ‖L‖ := by rw [ψ.norm_map]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg altCLM)
      _ = ‖altCLM‖ * ‖M‖ * ‖L‖ := by rw [← mul_assoc]
  have hΦlin : IsLinearMap 𝕜 (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) :=
    { map_add := by intro M₁ M₂; ext L; simp
      map_smul := by intro c M; ext L; simp }
  have hΦ : IsBoundedLinearMap 𝕜 (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) :=
    hΦlin.with_bound (‖altCLM‖) hbound
  have hΦcont : ContDiff 𝕜 ⊤ (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) := by
    simpa using (IsBoundedLinearMap.contDiff (𝕜 := 𝕜) (n := ⊤)
      (f := (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
        (B M : (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) hΦ)
  convert hΦcont.comp ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff using 1
  funext p
  ext L x
  change (compContinuousLinearMapCLM p) L x =
    (ContinuousMultilinearMap.alternatizationCLM
      (ContinuousAlternatingMap.toContinuousMultilinearMap
      (L.compContinuousLinearMap p))) x
  rw [ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap]
  rfl

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff :
    let F : (F₁ →L[𝕜] F₁) → (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁))) (𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤ F := by
  rw [contMDiff_iff_contDiff]
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace 𝕜 F₁'] :
    ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁' =>
      (compContinuousLinearMapCLM p : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜]
        (F₁ [⋀^ι]→L[𝕜] F₂))) := by
  classical
  let ψ : (F₁' [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let ψ₀ : (F₁ [⋀^ι]→L[𝕜] F₂) →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂ :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLI
  let altCLM : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜] (F₁' [⋀^ι]→L[𝕜] F₂) :=
    ContinuousMultilinearMap.alternatizationCLM
  let altCLM₀ : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
    ContinuousMultilinearMap.alternatizationCLM
  let B : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) →ₗ[𝕜]
      (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
    { toFun := fun M => altCLM₀.comp (M.comp ψ.toContinuousLinearMap)
      map_add' := by intro M₁ M₂; ext L; simp
      map_smul' := by intro c M; ext L; simp }
  have hbound : ∀ (M : (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)),
      ‖B M‖ ≤ ‖altCLM₀‖ * ‖M‖ := by
    intro M
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg altCLM₀)
      (norm_nonneg M)) ?_
    intro L
    calc
      ‖altCLM₀ (M (ψ L))‖ ≤ ‖altCLM₀‖ * ‖M (ψ L)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖altCLM₀‖ * (‖M‖ * ‖L‖) := by
        have h1 : ‖M (ψ L)‖ ≤ ‖M‖ * ‖L‖ := by
          calc
            ‖M (ψ L)‖ ≤ ‖M‖ * ‖ψ L‖ := ContinuousLinearMap.le_opNorm M (ψ L)
            _ = ‖M‖ * ‖L‖ := by rw [ψ.norm_map]
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg altCLM₀)
      _ = ‖altCLM₀‖ * ‖M‖ * ‖L‖ := by rw [← mul_assoc]
  have hΦlin : IsLinearMap 𝕜 (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) :=
    { map_add := by intro M₁ M₂; ext L; simp
      map_smul := by intro c M; ext L; simp }
  have hΦ : IsBoundedLinearMap 𝕜 (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) :=
    hΦlin.with_bound (‖altCLM₀‖) hbound
  have hΦcont : ContDiff 𝕜 ⊤ (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
      (B M : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) := by
    simpa using (IsBoundedLinearMap.contDiff (𝕜 := 𝕜) (n := ⊤)
      (f := (fun M : ((ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁') F₂) →L[𝕜]
        (ContinuousMultilinearMap 𝕜 (fun _ : ι => F₁) F₂)) =>
        (B M : (F₁' [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) hΦ)
  convert hΦcont.comp ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff_of_space
    using 1
  funext p
  ext L x
  change (compContinuousLinearMapCLM p) L x =
    (ContinuousMultilinearMap.alternatizationCLM
      (ContinuousAlternatingMap.toContinuousMultilinearMap
      (L.compContinuousLinearMap p))) x
  rw [ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap]
  rfl

end

end Smooth

section Smooth
variable {ι F₁ F₂}
open scoped Bundle Manifold

section

variable [Fintype ι] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_real :
    ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁ =>
      (compContinuousLinearMapCLM p : (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        (F₁ [⋀^ι]→L[ℝ] F₂))) := by
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] :
    ContDiff ℝ ⊤ (fun p : F₁ →L[ℝ] F₁' =>
      (compContinuousLinearMapCLM p : (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ]
        (F₁ [⋀^ι]→L[ℝ] F₂))) := by
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space

theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff_of_space_real
    {F₁' : Type*} [NormedAddCommGroup F₁'] [NormedSpace ℝ F₁'] :
    let F : (F₁ →L[ℝ] F₁') → (F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)
      := fun p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p
    ContMDiff (𝓘(ℝ, (F₁ →L[ℝ] F₁'))) (𝓘(ℝ,
      ((F₁' [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)))) ⊤ F := by
  rw [contMDiff_iff_contDiff]
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff_of_space_real

end

end Smooth

end Comp
