-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/PositiveDefinite/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.LinearChangeOfVariables
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Matrix Real
open scoped MatrixOrder RealInnerProductSpace

namespace HeatEquation

section PositiveDefinite

variable {n : Type*} [Fintype n] [DecidableEq n]
private abbrev matrixCLM (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
  Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A
def spdSqrtEquiv (A : Matrix n n ℝ) (hA : A.PosDef) :
    EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n :=
  let S := CFC.sqrt A
  let hS : S.PosDef := hA.isStrictlyPositive.sqrt.posDef
  let L := matrixCLM S
  have hunit : IsUnit S :=
    (Matrix.isUnit_iff_isUnit_det S).mpr
      (isUnit_iff_ne_zero.mpr hS.det_pos.ne')
  have hinj : Function.Injective L := by
    intro x y hxy
    apply WithLp.ofLp_injective
    apply Matrix.mulVec_injective_of_isUnit hunit
    simpa only [L, matrixCLM, Matrix.ofLp_toEuclideanCLM] using
      congrArg WithLp.ofLp hxy
  ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr
      (L.toLinearMap.surjective_of_injective hinj))

@[simp]
theorem spdSqrtEquiv_apply (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : EuclideanSpace ℝ n) :
    spdSqrtEquiv A hA x =
      matrixCLM (CFC.sqrt A) x := by
  rfl

theorem spdSqrt_comp (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : EuclideanSpace ℝ n) :
    spdSqrtEquiv A hA (spdSqrtEquiv A hA x) =
      matrixCLM A x := by
  simp only [spdSqrtEquiv_apply]
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]

theorem spdSqrt_selfAdj (A : Matrix n n ℝ) (hA : A.PosDef) :
    IsSelfAdjoint
      (spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) := by
  have heq :
      (spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) =
        matrixCLM (CFC.sqrt A) := by
    apply ContinuousLinearMap.ext
    intro x
    exact spdSqrtEquiv_apply A hA x
  rw [heq]
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  rw [show
    (matrixCLM (CFC.sqrt A) :
      EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) =
        Matrix.toEuclideanLin (CFC.sqrt A) from
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (CFC.sqrt A)]
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (CFC.sqrt_nonneg A).isSelfAdjoint.isHermitian
theorem spdSqrt_norm_sq (A : Matrix n n ℝ) (hA : A.PosDef)
    (x : EuclideanSpace ℝ n) :
    ‖spdSqrtEquiv A hA x‖ ^ 2 =
      inner ℝ x (matrixCLM A x) := by
  calc
    ‖spdSqrtEquiv A hA x‖ ^ 2 =
        inner ℝ (spdSqrtEquiv A hA x) (spdSqrtEquiv A hA x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ x (spdSqrtEquiv A hA (spdSqrtEquiv A hA x)) :=
      (spdSqrt_selfAdj A hA).isSymmetric x (spdSqrtEquiv A hA x)
    _ = inner ℝ x (matrixCLM A x) := by
      rw [spdSqrt_comp]

theorem spdSqrt_det (A : Matrix n n ℝ) (hA : A.PosDef) :
    LinearMap.det
        ((spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
          EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) =
      Real.sqrt A.det := by
  let b := (EuclideanSpace.basisFun n ℝ).toBasis
  have hlin :
      ((spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
        EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) =
        Matrix.toLin b b (CFC.sqrt A) := by
    apply LinearMap.ext
    intro x
    change spdSqrtEquiv A hA x = Matrix.toLin b b (CFC.sqrt A) x
    rw [spdSqrtEquiv_apply]
    rfl
  calc
    LinearMap.det
        ((spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
          EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) =
        (LinearMap.toMatrix b b
          ((spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ]
            EuclideanSpace ℝ n) : EuclideanSpace ℝ n →ₗ[ℝ]
              EuclideanSpace ℝ n)).det :=
      (LinearMap.det_toMatrix b _).symm
    _ = (CFC.sqrt A).det := by rw [hlin, LinearMap.toMatrix_toLin]
    _ = Real.sqrt A.det := by simpa using hA.posSemidef.det_sqrt

theorem gaussSPD_int (A : Matrix n n ℝ) (hA : A.PosDef) :
    ∫ x : EuclideanSpace ℝ n,
        Real.exp (-inner ℝ x (matrixCLM A x)) =
      (Real.sqrt A.det)⁻¹ *
        (Real.pi : ℝ) ^ (Fintype.card n / 2 : ℝ) := by
  let L := spdSqrtEquiv A hA
  let f : EuclideanSpace ℝ n → ℝ := fun y => Real.exp (-‖y‖ ^ 2)
  have hdet : LinearMap.det (L : EuclideanSpace ℝ n →ₗ[ℝ]
      EuclideanSpace ℝ n) = Real.sqrt A.det := spdSqrt_det A hA
  have hdet_pos : 0 < LinearMap.det (L : EuclideanSpace ℝ n →ₗ[ℝ]
      EuclideanSpace ℝ n) := hdet ▸ Real.sqrt_pos.2 hA.det_pos
  have hmap : MeasureTheory.Measure.map
      (L : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ n)) =
        ENNReal.ofReal ((LinearMap.det (L : EuclideanSpace ℝ n →ₗ[ℝ]
          EuclideanSpace ℝ n))⁻¹) • MeasureTheory.volume := by
    simpa [abs_of_pos hdet_pos] using
      MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ n)) hdet_pos.ne'
  calc
    ∫ x : EuclideanSpace ℝ n, Real.exp (-inner ℝ x (matrixCLM A x)) =
        ∫ x : EuclideanSpace ℝ n, f (L x) := by
          congr 1
          funext x
          simp only [f, L, spdSqrt_norm_sq]
    _ = ∫ y : EuclideanSpace ℝ n, f y ∂MeasureTheory.Measure.map
          (L : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n)
          MeasureTheory.volume := by
            rw [MeasureTheory.integral_map]
            · rfl
            · exact (L : EuclideanSpace ℝ n →L[ℝ]
                EuclideanSpace ℝ n).continuous.aemeasurable
            · exact Real.continuous_exp.comp
                (continuous_neg.comp (continuous_norm.pow 2)) |>.aestronglyMeasurable
    _ = (LinearMap.det (L : EuclideanSpace ℝ n →ₗ[ℝ]
          EuclideanSpace ℝ n))⁻¹ * ∫ y : EuclideanSpace ℝ n, f y := by
            rw [hmap, MeasureTheory.integral_smul_measure]
            simp [ENNReal.toReal_ofReal, hdet_pos.le, smul_eq_mul]
    _ = (Real.sqrt A.det)⁻¹ *
        (Real.pi : ℝ) ^ (Fintype.card n / 2 : ℝ) := by
          rw [hdet]
          simp only [f]
          have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm
            (V := EuclideanSpace ℝ n) (b := 1) zero_lt_one
          simpa only [neg_one_mul, div_one, finrank_euclideanSpace] using
            congrArg (fun z => (Real.sqrt A.det)⁻¹ * z) hg

theorem spdSqrt_apply_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMax : ℝ} (hMax : 0 ≤ ellMax)
    (hupper : ∀ x : EuclideanSpace ℝ n,
      inner ℝ x (matrixCLM A x) ≤ ellMax * ‖x‖ ^ 2)
    (x : EuclideanSpace ℝ n) :
    ‖spdSqrtEquiv A hA x‖ ≤ √ellMax * ‖x‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _)),
    spdSqrt_norm_sq, mul_pow, Real.sq_sqrt hMax]
  exact hupper x

theorem spdSqrt_norm_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMax : ℝ} (hMax : 0 ≤ ellMax)
    (hupper : ∀ x : EuclideanSpace ℝ n,
      inner ℝ x (matrixCLM A x) ≤ ellMax * ‖x‖ ^ 2) :
    ‖(spdSqrtEquiv A hA : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖ ≤
      √ellMax := by
  exact ContinuousLinearMap.opNorm_le_bound _ (sqrt_nonneg ellMax)
    (spdSqrt_apply_le A hA hMax hupper)

theorem spdSqrt_symm_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMin : ℝ} (hMin : 0 < ellMin)
    (hlower : ∀ x : EuclideanSpace ℝ n,
      ellMin * ‖x‖ ^ 2 ≤ inner ℝ x (matrixCLM A x))
    (y : EuclideanSpace ℝ n) :
    ‖(spdSqrtEquiv A hA).symm y‖ ≤ (√ellMin)⁻¹ * ‖y‖ := by
  have hsq := hlower ((spdSqrtEquiv A hA).symm y)
  rw [← spdSqrt_norm_sq A hA,
    ContinuousLinearEquiv.apply_symm_apply] at hsq
  rw [inv_mul_eq_div, le_div_iff₀ (Real.sqrt_pos.2 hMin)]
  have hsqrt :
      √ellMin * ‖(spdSqrtEquiv A hA).symm y‖ ≤ ‖y‖ := by
    rw [← sq_le_sq₀
      (mul_nonneg (sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _),
      mul_pow, Real.sq_sqrt hMin.le]
    exact hsq
  simpa [mul_comm] using hsqrt

theorem spdSqrt_inv_le (A : Matrix n n ℝ) (hA : A.PosDef)
    {ellMin : ℝ} (hMin : 0 < ellMin)
    (hlower : ∀ x : EuclideanSpace ℝ n,
      ellMin * ‖x‖ ^ 2 ≤ inner ℝ x (matrixCLM A x)) :
    ‖((spdSqrtEquiv A hA).symm :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖ ≤ (√ellMin)⁻¹ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (sqrt_nonneg ellMin))
    (spdSqrt_symm_le A hA hMin hlower)

end PositiveDefinite

end HeatEquation
