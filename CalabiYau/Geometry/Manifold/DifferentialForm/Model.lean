-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Exterior/Model.lean
-- Locally modified.
module
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import CalabiYau.Geometry.Manifold.Tensor.Alternating.Wedge

@[expose] public section


noncomputable section

open ContinuousAlternatingMap
open scoped ContDiff

namespace CalabiYau
namespace DifferentialForm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n m k l : ℕ}

theorem contDiffOn_extDeriv_infty {s : Set E} (alpha : E → E [⋀^Fin n]→L[ℝ] F)
    (hAlpha : ContDiffOn ℝ ∞ alpha s) (hs : IsOpen s) :
    ContDiffOn ℝ ∞ (fun x => extDeriv alpha x) s := by
  have hf : ContDiffOn ℝ ∞ (fderiv ℝ alpha) s := hAlpha.fderiv_of_isOpen hs (by simp)
  have hc : ContDiff ℝ ∞ (fun L : E →L[ℝ] E [⋀^Fin n]→L[ℝ] F =>
      alternatizeUncurryFinCLM ℝ E F L) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := E →L[ℝ] E [⋀^Fin n]→L[ℝ] F)
      (F := E [⋀^Fin (n + 1)]→L[ℝ] F)
      (alternatizeUncurryFinCLM (n := n) ℝ E F)
  exact hc.comp_contDiffOn hf

theorem wedge_product_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (g : E [⋀^Fin k]→L[ℝ] ℝ) (h : E [⋀^Fin l]→L[ℝ] ℝ)
    (A : E' →L[ℝ] E) :
    (g ∧[ℝ] h).compContinuousLinearMap A =
      (g.compContinuousLinearMap A) ∧[ℝ] (h.compContinuousLinearMap A) := by
  ext v
  simp only [compContinuousLinearMap_apply, wedge_product_def]
  change uncurryFinAdd (ContinuousLinearMap.compContinuousAlternatingMap₂
    (ContinuousLinearMap.mul ℝ ℝ) g h) (A ∘ v) =
      uncurryFinAdd (ContinuousLinearMap.compContinuousAlternatingMap₂
        (ContinuousLinearMap.mul ℝ ℝ) (g.compContinuousLinearMap A)
        (h.compContinuousLinearMap A)) v
  rw [uncurryFinAdd, uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply, uncurrySum_apply,
    _root_.sum_apply, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  refine Quotient.inductionOn' σ ?_
  intro σ'
  rw [uncurrySum_summand_eval, uncurrySum_summand_eval]
  simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    compContinuousLinearMap_apply, Function.comp_apply]
  rfl

theorem domDomCongr_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (σ : Fin m ≃ Fin n) (L : E [⋀^Fin m]→L[ℝ] F) (A : E' →L[ℝ] E) :
    (domDomCongr σ L).compContinuousLinearMap A =
      domDomCongr σ (L.compContinuousLinearMap A) := by
  ext v
  rfl

theorem constOfIsEmpty_compContinuousLinearMap {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (y : F) (A : E' →L[ℝ] E) :
    (constOfIsEmpty ℝ E (Fin 0) y).compContinuousLinearMap A =
      constOfIsEmpty ℝ E' (Fin 0) y := by
  ext v
  rfl

end DifferentialForm
end CalabiYau

end
