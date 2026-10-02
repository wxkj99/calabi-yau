-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Elliptic/VariableCoefficient/Basic.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Schauder.ConstantCoefficient.Estimate
public import CalabiYau.Analysis.Holder.Bilinear
public import CalabiYau.Analysis.Elliptic.Schauder.Cutoff.Product
public import CalabiYau.Analysis.Estimates.Absorption
public import CalabiYau.Analysis.Holder.Interpolation
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Real
open scoped BoundedContinuousFunction NNReal RealInnerProductSpace

namespace CalabiYau.Schauder

open HeatEquation

private abbrev Euc (n : Type*) := EuclideanSpace Real n

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace Real F]

def hessianComponentBoundedContinuousFunction
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (i j : n) :
    BoundedContinuousFunction (Euc n) F :=
  (ContinuousLinearMap.apply Real F (EuclideanSpace.basisFun n Real j))
    |>.compLeftContinuousBounded (Euc n)
      ((ContinuousLinearMap.apply Real (Euc n →L[Real] F)
        (EuclideanSpace.basisFun n Real i))
        |>.compLeftContinuousBounded (Euc n) d2u)

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem hessianComponentBoundedContinuousFunction_apply
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (i j : n) (x : Euc n) :
    hessianComponentBoundedContinuousFunction d2u i j x =
      d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j) := rfl

def variableMatrixLap
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, ∑ j, a i j • hessianComponentBoundedContinuousFunction d2u i j

def matrixLapBoundedContinuousFunction
    (A : Matrix n n Real)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, ∑ j, (A i j) • hessianComponentBoundedContinuousFunction d2u i j

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem matrixLapBoundedContinuousFunction_apply
    (A : Matrix n n Real)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (x : Euc n) :
    matrixLapBoundedContinuousFunction A d2u x = matrixLap A (d2u x) := by
  simp only [matrixLapBoundedContinuousFunction, matrixLap,
    BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply, hessianComponentBoundedContinuousFunction_apply]

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem variableMatrixLap_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (x : Euc n) :
    variableMatrixLap a d2u x =
      matrixLap (fun i j ↦ a i j x) (d2u x) := by
  simp only [variableMatrixLap, matrixLap,
    BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rfl

def contDiffHolderSpaceVariableMatrixLaplacian
    (alpha : NNReal)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha) :
    ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha →L[Real]
      BoundedHolderSpace (X := Euc n) (F := F) alpha :=
  ∑ i, ∑ j,
    (boundedHolderSpaceSmu alpha (a i j)).comp
      ((boundedHolderSpaceMap alpha
        (hessianComponentEval (F := F) i j)).comp
        (contDiffHolderSpaceTopJet 2 alpha))

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem contDiffHolderSpaceVariableMatrixLaplacian_apply
    (alpha : NNReal)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (u : ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha)
    (x : Euc n) :
    contDiffHolderSpaceVariableMatrixLaplacian alpha a u x =
      matrixLap (fun i j ↦ a i j x)
        (hessianCurryEquiv (Euc n) F
          (iteratedFDeriv Real 2 (contDiffHolderSpaceFun u) x)) := by
  simp only [contDiffHolderSpaceVariableMatrixLaplacian,
    sum_apply, boundedHolderSpace_sum_apply,
    ContinuousLinearMap.comp_apply, boundedHolderSpaceSmu_apply,
    boundedHolderSpaceMap_apply, contDiffHolderSpaceTopJet_apply,
    hessianComponentEval_apply, matrixLap]

omit [DecidableEq n] [Nonempty n] in
theorem norm_contDiffHolderSpaceVariableMatrixLaplacian_le
    (alpha : NNReal)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha) :
    ‖contDiffHolderSpaceVariableMatrixLaplacian
      (F := F) alpha a‖ ≤ 3 * ∑ i, ∑ j, ‖a i j‖ := by
  classical
  have hsmu : ∀ f : BoundedHolderSpace (X := Euc n) (F := Real) alpha,
      ‖boundedHolderSpaceSmu (F := F) alpha f‖ ≤ 3 * ‖f‖ := by
    intro f
    calc
      ‖boundedHolderSpaceSmu (F := F) alpha f‖ ≤
          ‖boundedHolderSpaceSmu (X := Euc n) (F := F) alpha‖ * ‖f‖ :=
        (boundedHolderSpaceSmu (X := Euc n) (F := F) alpha).le_opNorm f
      _ ≤ 3 * ‖f‖ := mul_le_mul_of_nonneg_right
        (norm_boundedHolderSpaceSmu_le
          (X := Euc n) (F := F) alpha) (norm_nonneg _)
  have hterm : ∀ i j,
      ‖(boundedHolderSpaceSmu alpha (a i j)).comp
        ((boundedHolderSpaceMap alpha
          (hessianComponentEval (F := F) i j)).comp
          (contDiffHolderSpaceTopJet 2 alpha))‖ ≤
        3 * ‖a i j‖ := by
    intro i j
    calc
      ‖(boundedHolderSpaceSmu alpha (a i j)).comp
          ((boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (contDiffHolderSpaceTopJet 2 alpha))‖ ≤
        ‖boundedHolderSpaceSmu alpha (a i j)‖ *
          ‖(boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (contDiffHolderSpaceTopJet 2 alpha)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (3 * ‖a i j‖) * (1 * 1) := mul_le_mul (hsmu (a i j))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul
            ((norm_boundedHolderSpaceMap_le alpha
              (hessianComponentEval (F := F) i j)).trans
                (norm_hessianComponentEval_le_one (F := F) i j))
            (norm_contDiffHolderSpaceTopJet_le
              (V := Euc n) (F := F) 2 alpha)
            (norm_nonneg _) zero_le_one))
        (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg (a i j)))
      _ = 3 * ‖a i j‖ := by ring
  unfold contDiffHolderSpaceVariableMatrixLaplacian
  calc
    ‖∑ i, ∑ j,
        (boundedHolderSpaceSmu alpha (a i j)).comp
          ((boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (contDiffHolderSpaceTopJet 2 alpha))‖ ≤
      ∑ i, ∑ j,
        ‖(boundedHolderSpaceSmu alpha (a i j)).comp
          ((boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (contDiffHolderSpaceTopJet 2 alpha))‖ :=
      (norm_sum_le Finset.univ fun i ↦ ∑ j,
        (boundedHolderSpaceSmu alpha (a i j)).comp
          ((boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (contDiffHolderSpaceTopJet 2 alpha))).trans
        (Finset.sum_le_sum fun i _hi ↦ norm_sum_le Finset.univ fun j ↦
          (boundedHolderSpaceSmu alpha (a i j)).comp
            ((boundedHolderSpaceMap alpha
              (hessianComponentEval (F := F) i j)).comp
              (contDiffHolderSpaceTopJet 2 alpha)))
    _ ≤ ∑ i, ∑ j, 3 * ‖a i j‖ :=
      Finset.sum_le_sum fun i _hi ↦
        Finset.sum_le_sum fun j _hj ↦ hterm i j
    _ = 3 * ∑ i, ∑ j, ‖a i j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

def parabolicC2HolderSpaceVariableMatrixLaplacian
    (alpha : NNReal)
    (a : n → n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha) :
    ParabolicC2HolderSpace (V := Euc n) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := Euc n) (F := F) alpha :=
  ∑ i, ∑ j,
    (boundedHolderSpaceSmu alpha (a i j)).comp
      ((boundedHolderSpaceMap alpha
        (hessianComponentEval (F := F) i j)).comp
        (parabolicC2HolderSpaceSpatialHessian alpha))

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicC2HolderSpaceVariableMatrixLaplacian_apply
    (alpha : NNReal)
    (a : n → n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (u : ParabolicC2HolderSpace (V := Euc n) (F := F) alpha)
    (p : ParabolicPoint (Euc n)) :
    parabolicC2HolderSpaceVariableMatrixLaplacian alpha a u p =
      matrixLap (fun i j ↦ a i j p)
        (hessianCurryEquiv (Euc n) F
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u) p)) := by
  simp only [parabolicC2HolderSpaceVariableMatrixLaplacian,
    sum_apply, boundedHolderSpace_sum_apply,
    ContinuousLinearMap.comp_apply, boundedHolderSpaceSmu_apply,
    boundedHolderSpaceMap_apply,
    parabolicC2HolderSpaceSpatialHessian_apply,
    hessianComponentEval_apply, matrixLap]

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicC2HolderSpaceVariableMatrixLaplacian_le
    (alpha : NNReal)
    (a : n → n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha) :
    ‖parabolicC2HolderSpaceVariableMatrixLaplacian
      (F := F) alpha a‖ ≤ 3 * ∑ i, ∑ j, ‖a i j‖ := by
  classical
  have hsmu : ∀ f : ParabolicHolderSpace
      (V := Euc n) (F := Real) alpha,
      ‖boundedHolderSpaceSmu (F := F) alpha f‖ ≤ 3 * ‖f‖ := by
    intro f
    calc
      ‖boundedHolderSpaceSmu (F := F) alpha f‖ ≤
          ‖boundedHolderSpaceSmu
            (X := ParabolicPoint (Euc n)) (F := F) alpha‖ * ‖f‖ :=
        (boundedHolderSpaceSmu
          (X := ParabolicPoint (Euc n)) (F := F) alpha).le_opNorm f
      _ ≤ 3 * ‖f‖ := mul_le_mul_of_nonneg_right
        (norm_boundedHolderSpaceSmu_le
          (X := ParabolicPoint (Euc n)) (F := F) alpha) (norm_nonneg _)
  have hterm : ∀ i j,
      ‖(boundedHolderSpaceSmu alpha (a i j)).comp
        ((boundedHolderSpaceMap alpha
          (hessianComponentEval (F := F) i j)).comp
          (parabolicC2HolderSpaceSpatialHessian alpha))‖ ≤
        3 * ‖a i j‖ := by
    intro i j
    calc
      ‖(boundedHolderSpaceSmu alpha (a i j)).comp
          ((boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (parabolicC2HolderSpaceSpatialHessian alpha))‖ ≤
        ‖boundedHolderSpaceSmu alpha (a i j)‖ *
          ‖(boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (parabolicC2HolderSpaceSpatialHessian alpha)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (3 * ‖a i j‖) * (1 * 1) := mul_le_mul (hsmu (a i j))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul
            ((norm_boundedHolderSpaceMap_le alpha
              (hessianComponentEval (F := F) i j)).trans
                (norm_hessianComponentEval_le_one (F := F) i j))
            (norm_parabolicC2HolderSpaceSpatialHessian_le
              (V := Euc n) (F := F) alpha)
            (norm_nonneg _) zero_le_one))
        (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg (a i j)))
      _ = 3 * ‖a i j‖ := by ring
  unfold parabolicC2HolderSpaceVariableMatrixLaplacian
  calc
    ‖∑ i, ∑ j,
        (boundedHolderSpaceSmu alpha (a i j)).comp
          ((boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (parabolicC2HolderSpaceSpatialHessian alpha))‖ ≤
      ∑ i, ∑ j,
        ‖(boundedHolderSpaceSmu alpha (a i j)).comp
          ((boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (parabolicC2HolderSpaceSpatialHessian alpha))‖ :=
      (norm_sum_le Finset.univ fun i ↦ ∑ j,
        (boundedHolderSpaceSmu alpha (a i j)).comp
          ((boundedHolderSpaceMap alpha
            (hessianComponentEval (F := F) i j)).comp
            (parabolicC2HolderSpaceSpatialHessian alpha))).trans
        (Finset.sum_le_sum fun i _hi ↦ norm_sum_le Finset.univ fun j ↦
          (boundedHolderSpaceSmu alpha (a i j)).comp
            ((boundedHolderSpaceMap alpha
              (hessianComponentEval (F := F) i j)).comp
              (parabolicC2HolderSpaceSpatialHessian alpha)))
    _ ≤ ∑ i, ∑ j, 3 * ‖a i j‖ :=
      Finset.sum_le_sum fun i _hi ↦
        Finset.sum_le_sum fun j _hj ↦ hterm i j
    _ = 3 * ∑ i, ∑ j, ‖a i j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

def parabolicC2HolderSpaceVariableMatrixOperator
    (alpha : NNReal)
    (a : n → n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha) :
    ParabolicC2HolderSpace (V := Euc n) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := Euc n) (F := F) alpha :=
  parabolicC2HolderSpaceTimeDerivative alpha -
    parabolicC2HolderSpaceVariableMatrixLaplacian alpha a

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem parabolicC2HolderSpaceVariableMatrixOperator_apply
    (alpha : NNReal)
    (a : n → n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha)
    (u : ParabolicC2HolderSpace (V := Euc n) (F := F) alpha)
    (p : ParabolicPoint (Euc n)) :
    parabolicC2HolderSpaceVariableMatrixOperator alpha a u p =
      parabolicTimeDerivative (parabolicC2HolderSpaceFun u) p -
        matrixLap (fun i j ↦ a i j p)
          (hessianCurryEquiv (Euc n) F
            (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u) p)) := by
  simp only [parabolicC2HolderSpaceVariableMatrixOperator,
    sub_apply, boundedHolderSpace_sub_apply,
    parabolicC2HolderSpaceTimeDerivative_apply,
    parabolicC2HolderSpaceVariableMatrixLaplacian_apply]

omit [DecidableEq n] [Nonempty n] in
theorem norm_parabolicC2HolderSpaceVariableMatrixOperator_le
    (alpha : NNReal)
    (a : n → n → ParabolicHolderSpace (V := Euc n) (F := Real) alpha) :
    ‖parabolicC2HolderSpaceVariableMatrixOperator
      (F := F) alpha a‖ ≤ 1 + 3 * ∑ i, ∑ j, ‖a i j‖ := by
  calc
    ‖parabolicC2HolderSpaceVariableMatrixOperator
        (F := F) alpha a‖ ≤
      ‖parabolicC2HolderSpaceTimeDerivative
        (V := Euc n) (F := F) alpha‖ +
      ‖parabolicC2HolderSpaceVariableMatrixLaplacian
        (F := F) alpha a‖ := norm_sub_le _ _
    _ ≤ 1 + 3 * ∑ i, ∑ j, ‖a i j‖ :=
      add_le_add
        (norm_parabolicC2HolderSpaceTimeDerivative_le
          (V := Euc n) (F := F) alpha)
        (norm_parabolicC2HolderSpaceVariableMatrixLaplacian_le
          (F := F) alpha a)

def frozenMatrixLap
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, ∑ j, (a i j x0) • hessianComponentBoundedContinuousFunction d2u i j

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem frozenMatrixLap_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (x : Euc n) :
    frozenMatrixLap a x0 d2u x =
      matrixLap (fun i j ↦ a i j x0) (d2u x) := by
  simp only [frozenMatrixLap, matrixLap,
    BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply, hessianComponentBoundedContinuousFunction_apply]

def matrixLapFreezeDefect
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    BoundedContinuousFunction (Euc n) F :=
  ∑ i, ∑ j,
    ((a i j x0) • hessianComponentBoundedContinuousFunction d2u i j -
      a i j • hessianComponentBoundedContinuousFunction d2u i j)

omit [DecidableEq n] [Nonempty n] in
@[simp]
theorem matrixLapFreezeDefect_apply
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (x : Euc n) :
    matrixLapFreezeDefect a x0 d2u x =
      ∑ i, ∑ j, (a i j x0 - a i j x) •
        d2u x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j) := by
  simp only [matrixLapFreezeDefect,
    BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  change (a i j x0) •
      d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j) -
    a i j x • d2u x (EuclideanSpace.basisFun n Real i)
      (EuclideanSpace.basisFun n Real j) = _
  rw [sub_smul]

omit [DecidableEq n] [Nonempty n] in
theorem frozenMatrixLap_eq_variableMatrixLap_add_defect
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) :
    frozenMatrixLap a x0 d2u =
      variableMatrixLap a d2u + matrixLapFreezeDefect a x0 d2u := by
  ext x
  simp only [frozenMatrixLap_apply, BoundedContinuousFunction.add_apply,
    variableMatrixLap_apply, matrixLapFreezeDefect_apply, matrixLap]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  module

omit [DecidableEq n] [Nonempty n] in
theorem norm_apply_euclideanBasis_le_one
    {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G] (i : n) :
    ‖ContinuousLinearMap.apply Real G
      (EuclideanSpace.basisFun n Real i)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro A
  change ‖A (EuclideanSpace.basisFun n Real i)‖ ≤ 1 * ‖A‖
  simpa only [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
    mul_one, one_mul] using A.le_opNorm (EuclideanSpace.basisFun n Real i)

omit [DecidableEq n] [Nonempty n] in
theorem norm_hessianComponentBoundedContinuousFunction_apply_le
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F)) (i j : n) (x : Euc n) :
    ‖hessianComponentBoundedContinuousFunction d2u i j x‖ ≤ ‖d2u x‖ := by
  calc
    ‖d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j)‖ ≤
        ‖d2u x (EuclideanSpace.basisFun n Real i)‖ *
          ‖EuclideanSpace.basisFun n Real j‖ :=
      (d2u x (EuclideanSpace.basisFun n Real i)).le_opNorm _
    _ ≤ (‖d2u x‖ * ‖EuclideanSpace.basisFun n Real i‖) *
          ‖EuclideanSpace.basisFun n Real j‖ := by
      gcongr
      exact (d2u x).le_opNorm _
    _ = ‖d2u x‖ := by
      rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
        (EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
        mul_one, mul_one]

omit [DecidableEq n] [Nonempty n] in
theorem hessianComponentBoundedContinuousFunction_holderWith
    {alpha K : NNReal}
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hd2u : HolderWith K alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (i j : n) :
    HolderWith K alpha (hessianComponentBoundedContinuousFunction d2u i j : Euc n → F) := by
  intro x y
  have hreal : dist (hessianComponentBoundedContinuousFunction d2u i j x)
      (hessianComponentBoundedContinuousFunction d2u i j y) ≤
      (K : Real) * dist x y ^ (alpha : Real) := by
    rw [dist_eq_norm]
    change ‖d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j) -
      d2u y (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j)‖ ≤ _
    rw [← sub_apply, ← sub_apply]
    calc
      ‖(d2u x - d2u y) (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤ ‖d2u x - d2u y‖ := by
        calc
          _ ≤ ‖(d2u x - d2u y) (EuclideanSpace.basisFun n Real i)‖ *
              ‖EuclideanSpace.basisFun n Real j‖ :=
            ((d2u x - d2u y) (EuclideanSpace.basisFun n Real i)).le_opNorm _
          _ ≤ (‖d2u x - d2u y‖ *
                ‖EuclideanSpace.basisFun n Real i‖) *
              ‖EuclideanSpace.basisFun n Real j‖ := by
            gcongr
            exact (d2u x - d2u y).le_opNorm _
          _ = ‖d2u x - d2u y‖ := by
            rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
              (EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
              mul_one, mul_one]
      _ = dist (d2u x) (d2u y) :=
        (dist_eq_norm (d2u x) (d2u y)).symm
      _ ≤ (K : Real) * dist x y ^ (alpha : Real) := hd2u.dist_le x y
  rw [edist_dist, edist_dist]
  calc
    ENNReal.ofReal (dist (hessianComponentBoundedContinuousFunction d2u i j x)
        (hessianComponentBoundedContinuousFunction d2u i j y)) ≤
        ENNReal.ofReal ((K : Real) * dist x y ^ (alpha : Real)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (K : ENNReal) * ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul K.coe_nonneg]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = (K : ENNReal) * ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

omit [DecidableEq n] [Nonempty n] in
theorem norm_matrixLapFreezeDefect_le
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (omega : n → n → NNReal) (M : NNReal)
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M) :
    ‖matrixLapFreezeDefect a x0 d2u‖ ≤
      ∑ i, ∑ j, (omega i j : Real) * M := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [matrixLapFreezeDefect_apply]
  calc
    ‖∑ i, ∑ j, (a i j x0 - a i j x) •
        d2u x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j)‖ ≤
        ∑ i, ∑ j, ‖(a i j x0 - a i j x) •
          d2u x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)‖ :=
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, (omega i j : Real) * M := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul]
      exact mul_le_mul (homega i j x)
        ((norm_hessianComponentBoundedContinuousFunction_apply_le d2u i j x).trans
          (hd2unorm x))
        (norm_nonneg _) (by positivity)

omit [DecidableEq n] [Nonempty n] in
theorem matrixLapFreezeDefect_holderWith
    {alpha Kd2u : NNReal}
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (Ka omega : n → n → NNReal) (M : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2u : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F)) :
    HolderWith
      (∑ i, ∑ j, (omega i j * Kd2u + M * Ka i j)) alpha
      (matrixLapFreezeDefect a x0 d2u : Euc n → F) := by
  classical
  let C : n → n → NNReal :=
    fun i j ↦ omega i j * Kd2u + M * Ka i j
  have hcomponent : ∀ i j,
      HolderWith (C i j) alpha (fun x ↦
        (a i j x0 - a i j x) •
          d2u x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) := by
    intro i j
    have hcoeff : HolderWith (Ka i j) alpha
        (fun x : Euc n ↦ a i j x0 - a i j x) := by
      intro x y
      rw [show edist (a i j x0 - a i j x) (a i j x0 - a i j y) =
          edist (a i j x) (a i j y) by
        simp only [edist_dist, Real.dist_eq]
        rw [show a i j x0 - a i j x - (a i j x0 - a i j y) =
          -(a i j x - a i j y) by ring, abs_neg]]
      exact ha i j x y
    have hhess := hessianComponentBoundedContinuousFunction_holderWith d2u hd2u i j
    apply holderWith_smul_of_norm_le hcoeff hhess
    · exact homega i j
    · intro x
      exact (norm_hessianComponentBoundedContinuousFunction_apply_le d2u i j x).trans
        (hd2unorm x)
  have hinner : ∀ i,
      HolderWith (∑ j, C i j) alpha (fun x ↦
        ∑ j, (a i j x0 - a i j x) •
          d2u x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) := by
    intro i
    exact holderWith_finset_sum Finset.univ
      (fun j _ ↦ hcomponent i j)
  have hall := holderWith_finset_sum Finset.univ
    (K := fun i ↦ ∑ j, C i j)
    (f := fun i x ↦ ∑ j, (a i j x0 - a i j x) •
      d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j))
    (fun i _ ↦ hinner i)
  have heq : (matrixLapFreezeDefect a x0 d2u : Euc n → F) =
      fun x ↦ ∑ i, ∑ j, (a i j x0 - a i j x) •
        d2u x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j) := by
    funext x
    exact matrixLapFreezeDefect_apply a x0 d2u x
  rw [heq]
  simpa only [C] using hall

omit [DecidableEq n] [Nonempty n] in
theorem norm_matrixLapFreezeDefect_le_of_support
    (s : Set (Euc n))
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (omega : n → n → NNReal) (M : NNReal)
    (homega : ∀ i j x, x ∈ s → ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2usupport : ∀ x, x ∉ s → d2u x = 0) :
    ‖matrixLapFreezeDefect a x0 d2u‖ ≤
      ∑ i, ∑ j, (omega i j : Real) * M := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  intro x
  rw [matrixLapFreezeDefect_apply]
  by_cases hx : x ∈ s
  · calc
      ‖∑ i, ∑ j, (a i j x0 - a i j x) •
          d2u x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)‖ ≤
          ∑ i, ∑ j, ‖(a i j x0 - a i j x) •
            d2u x (EuclideanSpace.basisFun n Real i)
              (EuclideanSpace.basisFun n Real j)‖ :=
        (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _)
      _ ≤ ∑ i, ∑ j, (omega i j : Real) * M := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_smul]
        exact mul_le_mul (homega i j x hx)
          ((norm_hessianComponentBoundedContinuousFunction_apply_le d2u i j x).trans
            (hd2unorm x))
          (norm_nonneg _) (by positivity)
  · rw [hd2usupport x hx]
    simp only [zero_apply, smul_zero,
      Finset.sum_const_zero, norm_zero]
    exact Finset.sum_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦
        mul_nonneg (omega i j).coe_nonneg M.coe_nonneg

omit [DecidableEq n] [Nonempty n] in
theorem matrixLapFreezeDefect_holderWith_of_support
    {alpha Kd2u : NNReal} (s : Set (Euc n))
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (Ka omega : n → n → NNReal) (M : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      (s.domRestrict (a i j : Euc n → Real)))
    (homega : ∀ i j x, x ∈ s → ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2u : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hd2usupport : ∀ x, x ∉ s → d2u x = 0) :
    HolderWith
      (∑ i, ∑ j, (omega i j * Kd2u + M * Ka i j)) alpha
      (matrixLapFreezeDefect a x0 d2u : Euc n → F) := by
  classical
  let C : n → n → NNReal :=
    fun i j ↦ omega i j * Kd2u + M * Ka i j
  have hcomponent : ∀ i j,
      HolderWith (C i j) alpha (fun x ↦
        (a i j x0 - a i j x) •
          d2u x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) := by
    intro i j
    have hcoeff : HolderWith (Ka i j) alpha
        (s.domRestrict fun x : Euc n ↦ a i j x0 - a i j x) := by
      intro x y
      change edist (a i j x0 - a i j x.1) (a i j x0 - a i j y.1) ≤ _
      rw [show edist (a i j x0 - a i j x.1) (a i j x0 - a i j y.1) =
          edist (a i j x.1) (a i j y.1) by
        simp only [edist_dist, Real.dist_eq]
        rw [show a i j x0 - a i j x.1 - (a i j x0 - a i j y.1) =
          -(a i j x.1 - a i j y.1) by ring, abs_neg]]
      exact ha i j x y
    have hhess := hessianComponentBoundedContinuousFunction_holderWith d2u hd2u i j
    apply holderWith_smul_of_restrict_of_support hcoeff hhess
    · exact homega i j
    · intro x
      exact (norm_hessianComponentBoundedContinuousFunction_apply_le d2u i j x).trans
        (hd2unorm x)
    · intro x hx
      rw [hessianComponentBoundedContinuousFunction_apply, hd2usupport x hx]
      simp
  have hinner : ∀ i,
      HolderWith (∑ j, C i j) alpha (fun x ↦
        ∑ j, (a i j x0 - a i j x) •
          d2u x (EuclideanSpace.basisFun n Real i)
            (EuclideanSpace.basisFun n Real j)) := by
    intro i
    exact holderWith_finset_sum Finset.univ
      (fun j _ ↦ hcomponent i j)
  have hall := holderWith_finset_sum Finset.univ
    (K := fun i ↦ ∑ j, C i j)
    (f := fun i x ↦ ∑ j, (a i j x0 - a i j x) •
      d2u x (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j))
    (fun i _ ↦ hinner i)
  have heq : (matrixLapFreezeDefect a x0 d2u : Euc n → F) =
      fun x ↦ ∑ i, ∑ j, (a i j x0 - a i j x) •
        d2u x (EuclideanSpace.basisFun n Real i)
          (EuclideanSpace.basisFun n Real j) := by
    funext x
    exact matrixLapFreezeDefect_apply a x0 d2u x
  rw [heq]
  simpa only [C] using hall

def matrixFreezeInterpolationHolderConst
    (epsilon alpha : NNReal) (Ka omega : n → n → NNReal) : NNReal :=
  ∑ i, ∑ j,
    (omega i j + 2 * epsilon ^ (alpha : Real) * Ka i j)

def matrixFreezeInterpolationSupConst
    (epsilon alpha : NNReal) (omega : n → n → NNReal) : NNReal :=
  ∑ i, ∑ j, 2 * omega i j * epsilon ^ (alpha : Real)

def matrixFreezeInterpolationSourceHolderConst
    (epsilon M Kf : NNReal) (Ka : n → n → NNReal) : NNReal :=
  Kf + ∑ i, ∑ j, hessianInterpolationFunctionConst epsilon M * Ka i j

def matrixFreezeInterpolationSourceSupConst
    (epsilon M Bf : NNReal) (omega : n → n → NNReal) : NNReal :=
  Bf + ∑ i, ∑ j, omega i j * hessianInterpolationFunctionConst epsilon M

section Estimates

variable [CompleteSpace F]

theorem frozen_matrix_laplacian_schauder_estimate
    {alpha K B : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hbound : ‖frozenMatrixLap a x0 d2u‖ ≤ B)
    (hholder : HolderWith K alpha (frozenMatrixLap a x0 d2u)) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha K B u := by
  let A : Matrix n n Real := fun i j ↦ a i j x0
  have heq : spdMatrixLap A hA d2u = frozenMatrixLap a x0 d2u := by
    ext x
    let hspd : spdMatrixLap A hA d2u x = matrixLap A (d2u x) :=
      spdMatrixLap_apply A hA d2u x
    let hfrozen : frozenMatrixLap a x0 d2u x =
        matrixLap A (d2u x) := frozenMatrixLap_apply a x0 d2u x
    exact hspd.trans hfrozen.symm
  apply spd_laplacian_schauder_estimate halpha0 halpha1 A hA
    u du d2u hu hdu
  · rw [heq]
    exact hbound
  · rw [heq]
    exact hholder

theorem variable_coefficient_schauder_estimate_of_freeze_defect
    {alpha Kf Kdefect Bf Bdefect : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hdefectBound : ‖matrixLapFreezeDefect a x0 d2u‖ ≤ Bdefect)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (hdefectHolder : HolderWith Kdefect alpha
      (matrixLapFreezeDefect a x0 d2u)) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (Kf + Kdefect) (Bf + Bdefect) u := by
  have hbound : ‖frozenMatrixLap a x0 d2u‖ ≤ Bf + Bdefect := by
    rw [frozenMatrixLap_eq_variableMatrixLap_add_defect]
    exact (norm_add_le _ _).trans (add_le_add hfBound hdefectBound)
  have hholder : HolderWith (Kf + Kdefect) alpha
      (frozenMatrixLap a x0 d2u) := by
    rw [frozenMatrixLap_eq_variableMatrixLap_add_defect]
    exact hfHolder.add hdefectHolder
  exact frozen_matrix_laplacian_schauder_estimate halpha0 halpha1
    a x0 hA u du d2u hu hdu hbound hholder

theorem variable_coefficient_schauder_estimate_of_coefficient_oscillation_on
    {alpha Kf Kd2u Bf : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (s : Set (Euc n))
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal) (M : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      (s.domRestrict (a i j : Euc n → Real)))
    (homega : ∀ i j x, x ∈ s → ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hd2usupport : ∀ x, x ∉ s → d2u x = 0) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (Kf + ∑ i, ∑ j, (omega i j * Kd2u + M * Ka i j))
        (Bf + ∑ i, ∑ j, omega i j * M) u := by
  let Kdefect : NNReal :=
    ∑ i, ∑ j, (omega i j * Kd2u + M * Ka i j)
  let Bdefect : NNReal := ∑ i, ∑ j, omega i j * M
  have hdefectBound : ‖matrixLapFreezeDefect a x0 d2u‖ ≤ Bdefect := by
    have hraw := norm_matrixLapFreezeDefect_le_of_support s a x0 d2u omega M
      homega hd2unorm hd2usupport
    exact_mod_cast hraw
  have hdefectHolder : HolderWith Kdefect alpha
      (matrixLapFreezeDefect a x0 d2u) :=
    matrixLapFreezeDefect_holderWith_of_support s a x0 d2u Ka omega M
      ha homega hd2unorm hd2uHolder hd2usupport
  exact variable_coefficient_schauder_estimate_of_freeze_defect
    halpha0 halpha1 a x0 hA u du d2u hu hdu hfBound hdefectBound
    hfHolder hdefectHolder

theorem variable_coefficient_schauder_estimate_of_coefficient_oscillation
    {alpha Kf Kd2u Bf : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal) (M : NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F)) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (Kf + ∑ i, ∑ j, (omega i j * Kd2u + M * Ka i j))
        (Bf + ∑ i, ∑ j, omega i j * M) u := by
  apply variable_coefficient_schauder_estimate_of_coefficient_oscillation_on
    halpha0 halpha1 Set.univ a x0 hA u du d2u hu hdu hfBound hfHolder
    Ka omega M
  · exact fun i j ↦ (ha i j).holderOnWith Set.univ |>.holderWith
  · exact fun i j x _ ↦ homega i j x
  · exact hd2unorm
  · exact hd2uHolder
  · simp

theorem variable_coefficient_schauder_estimate_of_interpolated_hessian_control_on
    {alpha Kf Bf X epsilon : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hepsilon : 0 < epsilon) (s : Set (Euc n))
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      (s.domRestrict (a i j : Euc n → Real)))
    (homega : ∀ i j x, x ∈ s → ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2uHolder : HolderWith X alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hd2usupport : ∀ x, x ∉ s → d2u x = 0)
    (hX : (X : ENNReal) ≤
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (matrixFreezeInterpolationHolderConst epsilon alpha Ka omega)
        (matrixFreezeInterpolationSupConst epsilon alpha omega) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (matrixFreezeInterpolationSourceHolderConst epsilon ‖u‖₊ Kf Ka)
        (matrixFreezeInterpolationSourceSupConst epsilon ‖u‖₊ Bf omega) u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (matrixFreezeInterpolationHolderConst epsilon alpha Ka omega)
            (matrixFreezeInterpolationSupConst epsilon alpha omega)) : NNReal) := by
  let I : NNReal := hessianInterpolationFunctionConst epsilon ‖u‖₊
  let P : NNReal := epsilon ^ (alpha : Real)
  let Kbase : NNReal := matrixFreezeInterpolationSourceHolderConst epsilon ‖u‖₊ Kf Ka
  let Bbase : NNReal := matrixFreezeInterpolationSourceSupConst epsilon ‖u‖₊ Bf omega
  let Kosc : NNReal := matrixFreezeInterpolationHolderConst epsilon alpha Ka omega
  let Bosc : NNReal := matrixFreezeInterpolationSupConst epsilon alpha omega
  let delta : NNReal := spdLaplacianSchauderDefectConst
    (fun i j ↦ a i j x0) hA alpha Kosc Bosc
  let C : NNReal := spdLaplacianSchauderConst
    (fun i j ↦ a i j x0) hA alpha Kbase Bbase u
  have hd2unorm : ∀ x,
      ‖d2u x‖ ≤ hessianInterpolationConst epsilon alpha ‖u‖₊ X := by
    intro x
    exact (d2u.norm_coe_le_norm x).trans
      (norm_hessian_le_hessianInterpolationConst u du d2u hu hdu
        hepsilon hd2uHolder)
  have hraw := variable_coefficient_schauder_estimate_of_coefficient_oscillation_on
    halpha0 halpha1 s a x0 hA u du d2u hu hdu hfBound hfHolder
    Ka omega (hessianInterpolationConst epsilon alpha ‖u‖₊ X)
    ha homega hd2unorm hd2uHolder hd2usupport
  have hK :
      Kf + ∑ i, ∑ j,
          (omega i j * X +
            hessianInterpolationConst epsilon alpha ‖u‖₊ X * Ka i j) =
        Kbase + X * Kosc := by
    change Kf + ∑ i, ∑ j,
        (omega i j * X + (I + 2 * X * P) * Ka i j) =
      (Kf + ∑ i, ∑ j, I * Ka i j) +
        X * ∑ i, ∑ j, (omega i j + 2 * P * Ka i j)
    have hsum :
        (∑ i, ∑ j,
          (omega i j * X + (I + 2 * X * P) * Ka i j)) =
          (∑ i, ∑ j, I * Ka i j) +
            X * ∑ i, ∑ j, (omega i j + 2 * P * Ka i j) := by
      calc
        _ = ∑ i, ∑ j,
            (I * Ka i j + X * (omega i j + 2 * P * Ka i j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = ∑ i,
            ((∑ j, I * Ka i j) +
              ∑ j, X * (omega i j + 2 * P * Ka i j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_add_distrib]
        _ = (∑ i, ∑ j, I * Ka i j) +
            ∑ i, ∑ j, X * (omega i j + 2 * P * Ka i j) := by
          rw [Finset.sum_add_distrib]
        _ = (∑ i, ∑ j, I * Ka i j) +
            X * ∑ i, ∑ j, (omega i j + 2 * P * Ka i j) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    rw [hsum]
    ring
  have hB :
      Bf + ∑ i, ∑ j,
          omega i j * hessianInterpolationConst epsilon alpha ‖u‖₊ X =
        Bbase + X * Bosc := by
    change Bf + ∑ i, ∑ j,
        omega i j * (I + 2 * X * P) =
      (Bf + ∑ i, ∑ j, omega i j * I) +
        X * ∑ i, ∑ j, 2 * omega i j * P
    have hsum :
        (∑ i, ∑ j, omega i j * (I + 2 * X * P)) =
          (∑ i, ∑ j, omega i j * I) +
            X * ∑ i, ∑ j, 2 * omega i j * P := by
      calc
        _ = ∑ i, ∑ j,
            (omega i j * I + X * (2 * omega i j * P)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = ∑ i,
            ((∑ j, omega i j * I) +
              ∑ j, X * (2 * omega i j * P)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_add_distrib]
        _ = (∑ i, ∑ j, omega i j * I) +
            ∑ i, ∑ j, X * (2 * omega i j * P) := by
          rw [Finset.sum_add_distrib]
        _ = (∑ i, ∑ j, omega i j * I) +
            X * ∑ i, ∑ j, 2 * omega i j * P := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    rw [hsum]
    ring
  rw [hK, hB,
    spdLaplacianSchauderConst_add_source halpha1
      (fun i j ↦ a i j x0) hA Kbase (X * Kosc) Bbase (X * Bosc) u,
    spdLaplacianSchauderDefectConst_nnreal_mul
      (fun i j ↦ a i j x0) hA alpha X Kosc Bosc] at hraw
  have hraw' :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
        (C : ENNReal) + (delta : ENNReal) * X := by
    simpa only [C, delta, ENNReal.coe_add, ENNReal.coe_mul,
      mul_comm] using hraw
  have hself :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
        (C : ENNReal) + (delta : ENNReal) *
          eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) :=
    hraw'.trans (by gcongr)
  have hfinite :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≠ ⊤ :=
    ne_of_lt (hraw'.trans_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.coe_lt_top,
        ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top⟩))
  have habsorb := ennreal_le_coe_div_one_sub_of_le_add_mul
    hfinite (show delta < 1 by simpa only [delta, Kosc, Bosc] using hsmall)
    hself
  simpa only [C, delta, Kbase, Bbase, Kosc, Bosc] using habsorb

theorem variable_coefficient_schauder_estimate_of_interpolation_scale_on
    {alpha Kf Kd2u Bf M epsilon : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hepsilon : 0 < epsilon) (s : Set (Euc n))
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      (s.domRestrict (a i j : Euc n → Real)))
    (homega : ∀ i j x, x ∈ s → ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm0 : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hd2usupport : ∀ x, x ∉ s → d2u x = 0)
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (matrixFreezeInterpolationHolderConst epsilon alpha Ka omega)
        (matrixFreezeInterpolationSupConst epsilon alpha omega) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
        (matrixFreezeInterpolationSourceHolderConst epsilon ‖u‖₊ Kf Ka)
        (matrixFreezeInterpolationSourceSupConst epsilon ‖u‖₊ Bf omega) u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (matrixFreezeInterpolationHolderConst epsilon alpha Ka omega)
            (matrixFreezeInterpolationSupConst epsilon alpha omega)) : NNReal) := by
  let e := hessianCurryEquiv (Euc n) F
  have heq : ∀ x, e (iteratedFDeriv Real 2 (u : Euc n → F) x) = d2u x :=
    hessianCurryEquiv_iteratedFDeriv_two u du d2u hu hdu
  let Cspatial : Nat → NNReal
    | 0 => ‖u‖₊
    | 1 => ‖du‖₊
    | _ => M
  have hspatial : ∀ j ≤ 2, ∀ x ∈ (Set.univ : Set (Euc n)),
      ‖iteratedFDeriv Real j (u : Euc n → F) x‖ ≤ Cspatial j := by
    intro j hj x hx
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]
      simpa only [Cspatial, coe_nnnorm] using u.norm_coe_le_norm x
    · rw [norm_iteratedFDeriv_one, (hu x).fderiv]
      simpa only [Cspatial, coe_nnnorm] using du.norm_coe_le_norm x
    · rw [← e.norm_map (iteratedFDeriv Real 2 (u : Euc n → F) x), heq]
      simpa only [Cspatial] using hd2unorm0 x
  have hiterHolder : HolderWith Kd2u alpha
      (iteratedFDeriv Real 2 (u : Euc n → F)) := by
    have hcomp := e.symm.lipschitz.holderWith.comp hd2uHolder
    have hfun : e.symm ∘ (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) =
        iteratedFDeriv Real 2 (u : Euc n → F) := by
      funext x
      rw [Function.comp_apply, ← heq x, e.symm_apply_apply]
    rw [hfun] at hcomp
    simpa using hcomp
  have hgaugeBound := eContDiffHolderGaugeOn_le
    Cspatial Kd2u hspatial
      ((hiterHolder.holderOnWith Set.univ).holderWith)
  have hgaugeFinite :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≠ ⊤ :=
    ne_of_lt (hgaugeBound.trans_lt (by simp))
  let X : NNReal :=
    (eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F)).toNNReal
  have hcoeX : (X : ENNReal) =
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) :=
    ENNReal.coe_toNNReal hgaugeFinite
  have hgaugeLeX :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤ X :=
    hcoeX.ge
  have hiterRestrict := topSpatialJet_holderWith_restrict hgaugeLeX
  have hd2uRestrict : HolderWith X alpha
      ((Set.univ : Set (Euc n)).domRestrict
        (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F)) := by
    have hcomp := e.lipschitz.holderWith.comp hiterRestrict
    have hfun : e ∘ ((Set.univ : Set (Euc n)).domRestrict
        (iteratedFDeriv Real 2 (u : Euc n → F))) =
      (Set.univ : Set (Euc n)).domRestrict
        (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) := by
      funext x
      exact heq x
    rw [hfun] at hcomp
    simpa using hcomp
  have hd2uHolderX : HolderWith X alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) := by
    intro x y
    let h : edist (d2u x) (d2u y) ≤
        (X : ENNReal) * edist x y ^ (alpha : Real) :=
      hd2uRestrict
        (⟨x, Set.mem_univ x⟩ : Set.univ)
        (⟨y, Set.mem_univ y⟩ : Set.univ)
    exact h
  exact variable_coefficient_schauder_estimate_of_interpolated_hessian_control_on
    halpha0 halpha1 hepsilon s a x0 hA u du d2u hu hdu hfBound hfHolder
    Ka omega ha homega hd2uHolderX hd2usupport hcoeX.le hsmall

theorem variable_coefficient_schauder_estimate_of_small_oscillation_of_hessian_control_on
    {alpha Kf Bf X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (s : Set (Euc n))
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      (s.domRestrict (a i j : Euc n → Real)))
    (homega : ∀ i j x, x ∈ s → ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ X)
    (hd2uHolder : HolderWith X alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hd2usupport : ∀ x, x ∉ s → d2u x = 0)
    (hX : (X : ENNReal) ≤
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA
        alpha Kf Bf u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  let Kosc : NNReal := ∑ i, ∑ j, (omega i j + Ka i j)
  let Bosc : NNReal := ∑ i, ∑ j, omega i j
  let epsilon : NNReal := spdLaplacianSchauderDefectConst
    (fun i j ↦ a i j x0) hA alpha Kosc Bosc
  let C : NNReal := spdLaplacianSchauderConst
    (fun i j ↦ a i j x0) hA alpha Kf Bf u
  have hK : (∑ i, ∑ j, (omega i j * X + X * Ka i j)) = X * Kosc := by
    simp only [Kosc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hB : (∑ i, ∑ j, omega i j * X) = X * Bosc := by
    simp only [Bosc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hraw := variable_coefficient_schauder_estimate_of_coefficient_oscillation_on
    halpha0 halpha1 s a x0 hA u du d2u hu hdu hfBound hfHolder
    Ka omega X ha homega hd2unorm hd2uHolder hd2usupport
  rw [hK, hB,
    spdLaplacianSchauderConst_add_source halpha1
      (fun i j ↦ a i j x0) hA Kf (X * Kosc) Bf (X * Bosc) u,
    spdLaplacianSchauderDefectConst_nnreal_mul
      (fun i j ↦ a i j x0) hA alpha X Kosc Bosc] at hraw
  have hraw' :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
        (C : ENNReal) + (epsilon : ENNReal) * X := by
    simpa only [C, epsilon, ENNReal.coe_add, ENNReal.coe_mul,
      mul_comm] using hraw
  have hself :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
        (C : ENNReal) + (epsilon : ENNReal) *
          eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) :=
    hraw'.trans (by gcongr)
  have hfinite :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≠ ⊤ :=
    ne_of_lt (hraw'.trans_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.coe_lt_top,
        ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top⟩))
  have habsorb := ennreal_le_coe_div_one_sub_of_le_add_mul
    hfinite (show epsilon < 1 by simpa only [epsilon, Kosc, Bosc] using hsmall)
    hself
  simpa only [C, epsilon, Kosc, Bosc] using habsorb

theorem variable_coefficient_schauder_estimate_of_small_oscillation_of_hessian_control
    {alpha Kf Bf X : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm : ∀ x, ‖d2u x‖ ≤ X)
    (hd2uHolder : HolderWith X alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hX : (X : ENNReal) ≤
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA
        alpha Kf Bf u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  apply variable_coefficient_schauder_estimate_of_small_oscillation_of_hessian_control_on
    halpha0 halpha1 Set.univ a x0 hA u du d2u hu hdu hfBound hfHolder
    Ka omega
  · exact fun i j ↦ (ha i j).holderOnWith Set.univ |>.holderWith
  · exact fun i j x _ ↦ homega i j x
  · exact hd2unorm
  · exact hd2uHolder
  · simp
  · exact hX
  · exact hsmall

theorem variable_coefficient_schauder_estimate_of_small_oscillation_on
    {alpha Kf Kd2u Bf M : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (s : Set (Euc n))
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha
      (s.domRestrict (a i j : Euc n → Real)))
    (homega : ∀ i j x, x ∈ s → ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm0 : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hd2usupport : ∀ x, x ∉ s → d2u x = 0)
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA
        alpha Kf Bf u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  let e := hessianCurryEquiv (Euc n) F
  have heq : ∀ x, e (iteratedFDeriv Real 2 (u : Euc n → F) x) = d2u x :=
    hessianCurryEquiv_iteratedFDeriv_two u du d2u hu hdu
  let Cspatial : Nat → NNReal
    | 0 => ‖u‖₊
    | 1 => ‖du‖₊
    | _ => M
  have hspatial : ∀ j ≤ 2, ∀ x ∈ (Set.univ : Set (Euc n)),
      ‖iteratedFDeriv Real j (u : Euc n → F) x‖ ≤ Cspatial j := by
    intro j hj x hx
    interval_cases j
    · rw [norm_iteratedFDeriv_zero]
      simpa only [Cspatial, coe_nnnorm] using u.norm_coe_le_norm x
    · rw [norm_iteratedFDeriv_one, (hu x).fderiv]
      simpa only [Cspatial, coe_nnnorm] using du.norm_coe_le_norm x
    · rw [← e.norm_map (iteratedFDeriv Real 2 (u : Euc n → F) x), heq]
      simpa only [Cspatial] using hd2unorm0 x
  have hiterHolder : HolderWith Kd2u alpha
      (iteratedFDeriv Real 2 (u : Euc n → F)) := by
    have hcomp := e.symm.lipschitz.holderWith.comp hd2uHolder
    have hfun : e.symm ∘ (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) =
        iteratedFDeriv Real 2 (u : Euc n → F) := by
      funext x
      rw [Function.comp_apply, ← heq x, e.symm_apply_apply]
    rw [hfun] at hcomp
    simpa using hcomp
  have hgaugeBound := eContDiffHolderGaugeOn_le
    Cspatial Kd2u hspatial
      ((hiterHolder.holderOnWith Set.univ).holderWith)
  have hgaugeFinite :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≠ ⊤ :=
    ne_of_lt (hgaugeBound.trans_lt (by simp))
  let X : NNReal :=
    (eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F)).toNNReal
  have hcoeX : (X : ENNReal) =
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) := by
    exact ENNReal.coe_toNNReal hgaugeFinite
  have hgaugeLeX :
      eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤ X :=
    hcoeX.ge
  have hd2unorm : ∀ x, ‖d2u x‖ ≤ X := by
    intro x
    calc
      ‖d2u x‖ = ‖e (iteratedFDeriv Real 2 (u : Euc n → F) x)‖ :=
        congrArg norm (heq x).symm
      _ = ‖iteratedFDeriv Real 2 (u : Euc n → F) x‖ := e.norm_map _
      _ ≤ X := spatialJet_norm_le hgaugeLeX le_rfl (Set.mem_univ x)
  have hiterRestrict := topSpatialJet_holderWith_restrict hgaugeLeX
  have hd2uRestrict : HolderWith X alpha
      ((Set.univ : Set (Euc n)).domRestrict
        (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F)) := by
    have hcomp := e.lipschitz.holderWith.comp hiterRestrict
    have hfun : e ∘ ((Set.univ : Set (Euc n)).domRestrict
        (iteratedFDeriv Real 2 (u : Euc n → F))) =
      (Set.univ : Set (Euc n)).domRestrict
        (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) := by
      funext x
      exact heq x
    rw [hfun] at hcomp
    simpa using hcomp
  have hd2uHolderX : HolderWith X alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) := by
    intro x y
    let h : edist (d2u x) (d2u y) ≤
        (X : ENNReal) * edist x y ^ (alpha : Real) :=
      hd2uRestrict
        (⟨x, Set.mem_univ x⟩ : Set.univ)
        (⟨y, Set.mem_univ y⟩ : Set.univ)
    exact h
  exact variable_coefficient_schauder_estimate_of_small_oscillation_of_hessian_control_on
    halpha0 halpha1 s a x0 hA u du d2u hu hdu hfBound hfHolder
    Ka omega ha homega hd2unorm hd2uHolderX hd2usupport hcoeX.le hsmall

theorem variable_coefficient_schauder_estimate_of_small_oscillation
    {alpha Kf Kd2u Bf M : NNReal}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedContinuousFunction (Euc n) Real) (x0 : Euc n)
    (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[Real] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[Real] Euc n →L[Real] F))
    (hu : ∀ x, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x)
    (hfBound : ‖variableMatrixLap a d2u‖ ≤ Bf)
    (hfHolder : HolderWith Kf alpha (variableMatrixLap a d2u))
    (Ka omega : n → n → NNReal)
    (ha : ∀ i j, HolderWith (Ka i j) alpha (a i j : Euc n → Real))
    (homega : ∀ i j x, ‖a i j x0 - a i j x‖ ≤ omega i j)
    (hd2unorm0 : ∀ x, ‖d2u x‖ ≤ M)
    (hd2uHolder : HolderWith Kd2u alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F))
    (hsmall : spdLaplacianSchauderDefectConst
      (fun i j ↦ a i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1) :
    eContDiffHolderGaugeOn 2 alpha Set.univ (u : Euc n → F) ≤
      ((spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA
        alpha Kf Bf u) /
        (1 - spdLaplacianSchauderDefectConst
          (fun i j ↦ a i j x0) hA alpha
            (∑ i, ∑ j, (omega i j + Ka i j))
            (∑ i, ∑ j, omega i j)) : NNReal) := by
  apply variable_coefficient_schauder_estimate_of_small_oscillation_on
    halpha0 halpha1 Set.univ a x0 hA u du d2u hu hdu hfBound hfHolder
    Ka omega
  · exact fun i j ↦ (ha i j).holderOnWith Set.univ |>.holderWith
  · exact fun i j x _ ↦ homega i j x
  · exact hd2unorm0
  · exact hd2uHolder
  · simp
  · exact hsmall

def variableCoefficientSchauderDefectConst
    (alpha : NNReal)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (x0 : Euc n) (hA : Matrix.PosDef (fun i j ↦ a i j x0)) : NNReal :=
  spdLaplacianSchauderDefectConst (fun i j ↦ a i j x0) hA alpha
    (∑ i, ∑ j,
      (boundedHolderSpaceOscillationAt (a i j) x0 +
        boundedHolderSpaceHolderConst (a i j)))
    (∑ i, ∑ j, boundedHolderSpaceOscillationAt (a i j) x0)

def variableCoefficientSchauderNormConst
    (alpha : NNReal)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (x0 : Euc n) (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha) : NNReal :=
  let f := contDiffHolderSpaceVariableMatrixLaplacian alpha a u
  (spdLaplacianSchauderConst (fun i j ↦ a i j x0) hA alpha
    ‖f‖₊ ‖f‖₊
    (contDiffHolderSpaceToBoundedContinuousFunction 2 alpha u)) /
    (1 - variableCoefficientSchauderDefectConst alpha a x0 hA)

theorem variable_coefficient_schauder_norm_estimate_of_small_oscillation
    {alpha : NNReal} (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (a : n → n → BoundedHolderSpace (X := Euc n) (F := Real) alpha)
    (x0 : Euc n) (hA : Matrix.PosDef (fun i j ↦ a i j x0))
    (u : ContDiffHolderSpace (V := Euc n) (F := F) 2 alpha)
    (hsmall : variableCoefficientSchauderDefectConst alpha a x0 hA < 1) :
    ‖u‖ ≤ variableCoefficientSchauderNormConst alpha a x0 hA u := by
  let a0 : n → n → BoundedContinuousFunction (Euc n) Real :=
    fun i j ↦ boundedHolderSpaceToBoundedContinuousFunction
      alpha halpha0 (a i j)
  let u0 := contDiffHolderSpaceToBoundedContinuousFunction 2 alpha u
  let du := contDiffHolderSpaceFDeriv 2 alpha (by omega) u
  let d2 := contDiffHolderSpaceHessianHolder alpha u
  let d2u := boundedHolderSpaceToBoundedContinuousFunction alpha halpha0 d2
  let f := contDiffHolderSpaceVariableMatrixLaplacian alpha a u
  let f0 := boundedHolderSpaceToBoundedContinuousFunction alpha halpha0 f
  let Ka : n → n → NNReal :=
    fun i j ↦ boundedHolderSpaceHolderConst (a i j)
  let omega : n → n → NNReal :=
    fun i j ↦ boundedHolderSpaceOscillationAt (a i j) x0
  have hu : ∀ x : Euc n, HasFDerivAt (u0 : Euc n → F) (du x) x := by
    intro x
    let h : HasFDerivAt (u0 : Euc n → F) (du x) x :=
      contDiffHolderSpace_hasFDerivAt 2 alpha (by omega) u x
    exact h
  have hdu : ∀ x : Euc n,
      HasFDerivAt (du : Euc n → Euc n →L[Real] F) (d2u x) x := by
    intro x
    have hd2eq : d2u x =
        contDiffHolderSpaceHessian 2 alpha (by omega) u x := by
      simp only [d2u, d2,
        boundedHolderSpaceToBoundedContinuousFunction_apply,
        contDiffHolderSpaceHessianHolder_apply,
        contDiffHolderSpaceHessian_apply]
    rw [hd2eq]
    simpa only [du] using
      contDiffHolderSpaceFDeriv_hasFDerivAt 2 alpha (by omega) u x
  have hsource : variableMatrixLap a0 d2u = f0 := by
    apply BoundedContinuousFunction.ext
    intro x
    simp only [variableMatrixLap_apply, a0, d2u, d2,
      boundedHolderSpaceToBoundedContinuousFunction_apply, f0, f,
      contDiffHolderSpaceHessianHolder_apply,
      contDiffHolderSpaceVariableMatrixLaplacian_apply]
    rw [← hessianCurryEquiv_iteratedFDeriv_two_eq_fderiv]
  have hfBound : ‖variableMatrixLap a0 d2u‖ ≤ ‖f‖₊ := by
    rw [hsource, BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    change ‖f x‖ ≤ (‖f‖₊ : Real)
    simpa using norm_boundedHolderSpace_apply_le f x
  have hfHolder : HolderWith ‖f‖₊ alpha (variableMatrixLap a0 d2u) := by
    rw [hsource]
    let h : HolderWith ‖f‖₊ alpha (f0 : Euc n → F) :=
      boundedHolderSpace_holderWith f
    exact h
  have ha : ∀ i j, HolderWith (Ka i j) alpha
      (a0 i j : Euc n → Real) := by
    intro i j
    let h : HolderWith (Ka i j) alpha (a0 i j : Euc n → Real) :=
      boundedHolderSpace_holderWith_holderConst (a i j)
    exact h
  have homega : ∀ i j x, ‖a0 i j x0 - a0 i j x‖ ≤ omega i j := by
    intro i j x
    simp only [a0, boundedHolderSpaceToBoundedContinuousFunction_apply]
    exact norm_sub_le_boundedHolderSpaceOscillationAt (a i j) x0 x
  have hd2unorm : ∀ x, ‖d2u x‖ ≤ ‖d2‖₊ := by
    intro x
    simp only [d2u, boundedHolderSpaceToBoundedContinuousFunction_apply]
    simpa using norm_boundedHolderSpace_apply_le d2 x
  have hd2uHolder : HolderWith ‖d2‖₊ alpha
      (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) := by
    let h : HolderWith ‖d2‖₊ alpha
        (d2u : Euc n → Euc n →L[Real] Euc n →L[Real] F) :=
      boundedHolderSpace_holderWith d2
    exact h
  have hsmall' : spdLaplacianSchauderDefectConst
      (fun i j ↦ a0 i j x0) hA alpha
        (∑ i, ∑ j, (omega i j + Ka i j))
        (∑ i, ∑ j, omega i j) < 1 := by
    simpa only [a0, boundedHolderSpaceToBoundedContinuousFunction_apply,
      omega, Ka, variableCoefficientSchauderDefectConst] using hsmall
  have hgauge := variable_coefficient_schauder_estimate_of_small_oscillation
    halpha0 halpha1 a0 x0 hA u0 du d2u hu hdu hfBound hfHolder
      Ka omega ha homega hd2unorm hd2uHolder hsmall'
  rw [norm_contDiffHolderSpace_eq]
  have hreal := ENNReal.toReal_mono ENNReal.coe_ne_top hgauge
  let h :
      (eContDiffHolderGaugeOn 2 alpha Set.univ (contDiffHolderSpaceFun u)).toReal ≤
        (variableCoefficientSchauderNormConst alpha a x0 hA u : Real) := hreal
  exact h

end Estimates

end CalabiYau.Schauder

end
