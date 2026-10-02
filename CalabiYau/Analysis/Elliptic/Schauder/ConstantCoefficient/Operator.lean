-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Elliptic/ConstantCoefficient/Operator.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.Duhamel.Frozen
public import CalabiYau.Analysis.Parabolic.Euclidean.Duhamel.FrozenPositiveDefinite
public import CalabiYau.Analysis.Holder.Operator

@[expose] public section


noncomputable section

open scoped NNReal RealInnerProductSpace

namespace CalabiYau.Schauder

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace Real V]
  [FiniteDimensional Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def laplacianEval : (V [×2]→L[Real] F) →L[Real] F :=
  HeatEquation.lapEval.comp
    (hessianCurryEquiv V F).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem laplacianEval_apply (A : V [×2]→L[Real] F) :
    laplacianEval A =
      HeatEquation.lapEval
        (hessianCurryEquiv V F A) :=
  rfl

theorem norm_laplacianEval_le :
    ‖laplacianEval (V := V) (F := F)‖ ≤ Module.finrank Real V := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Nat.cast_nonneg _)
  intro A
  have h := HeatEquation.lapEval_dist_le
    (V := V) (F := F) (hessianCurryEquiv V F A) 0
  simpa only [laplacianEval_apply, map_zero, dist_zero_right,
    LinearIsometryEquiv.norm_map] using h

def contDiffHolderSpaceLaplacian (alpha : NNReal) :
    ContDiffHolderSpace (V := V) (F := F) 2 alpha →L[Real]
      BoundedHolderSpace (X := V) (F := F) alpha :=
  (boundedHolderSpaceMap alpha (laplacianEval (V := V) (F := F))).comp
    (contDiffHolderSpaceTopJet 2 alpha)

@[simp]
theorem contDiffHolderSpaceLaplacian_apply
    (alpha : NNReal)
    (f : ContDiffHolderSpace (V := V) (F := F) 2 alpha) (x : V) :
    contDiffHolderSpaceLaplacian alpha f x =
      laplacianEval
        (iteratedFDeriv Real 2 (contDiffHolderSpaceFun f) x) :=
  rfl

theorem norm_contDiffHolderSpaceLaplacian_le (alpha : NNReal) :
    ‖contDiffHolderSpaceLaplacian (V := V) (F := F) alpha‖ ≤
      Module.finrank Real V := by
  calc
    ‖contDiffHolderSpaceLaplacian (V := V) (F := F) alpha‖ ≤
        ‖boundedHolderSpaceMap alpha
          (laplacianEval (V := V) (F := F))‖ *
        ‖contDiffHolderSpaceTopJet (V := V) (F := F) 2 alpha‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖laplacianEval (V := V) (F := F)‖ * 1 := by
      gcongr
      · exact norm_boundedHolderSpaceMap_le alpha
          (laplacianEval (V := V) (F := F))
      · exact norm_contDiffHolderSpaceTopJet_le
          (V := V) (F := F) 2 alpha
    _ ≤ Module.finrank Real V := by
      simpa only [mul_one] using norm_laplacianEval_le (V := V) (F := F)

section Matrix

variable {n : Type*} [Fintype n]

def hessianComponentEval (i j : n) :
    (EuclideanSpace Real n [×2]→L[Real] F) →L[Real] F :=
  (ContinuousLinearMap.apply Real F
    (EuclideanSpace.basisFun n Real j)).comp
    ((ContinuousLinearMap.apply Real
      (EuclideanSpace Real n →L[Real] F)
      (EuclideanSpace.basisFun n Real i)).comp
      (hessianCurryEquiv (EuclideanSpace Real n) F).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem hessianComponentEval_apply (i j : n)
    (H : EuclideanSpace Real n [×2]→L[Real] F) :
    hessianComponentEval i j H =
      hessianCurryEquiv (EuclideanSpace Real n) F H
        (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j) := by
  simp only [hessianComponentEval, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]

theorem norm_hessianComponentEval_le_one (i j : n) :
    ‖hessianComponentEval (F := F) i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro H
  rw [hessianComponentEval_apply, one_mul]
  calc
    ‖hessianCurryEquiv (EuclideanSpace Real n) F H
        (EuclideanSpace.basisFun n Real i)
        (EuclideanSpace.basisFun n Real j)‖ ≤
      ‖hessianCurryEquiv (EuclideanSpace Real n) F H
          (EuclideanSpace.basisFun n Real i)‖ *
        ‖EuclideanSpace.basisFun n Real j‖ :=
      (hessianCurryEquiv (EuclideanSpace Real n) F H
        (EuclideanSpace.basisFun n Real i)).le_opNorm _
    _ ≤ (‖hessianCurryEquiv (EuclideanSpace Real n) F H‖ *
          ‖EuclideanSpace.basisFun n Real i‖) *
        ‖EuclideanSpace.basisFun n Real j‖ := by
      gcongr
      exact (hessianCurryEquiv (EuclideanSpace Real n) F H).le_opNorm _
    _ = ‖H‖ := by
      rw [(EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one i,
        (EuclideanSpace.basisFun n Real).orthonormal.norm_eq_one j,
        LinearIsometryEquiv.norm_map, mul_one, mul_one]

def matrixLaplacianEval (A : Matrix n n Real) :
    (EuclideanSpace Real n [×2]→L[Real] F) →L[Real] F :=
  ∑ i, ∑ j, (A i j) • hessianComponentEval (F := F) i j

@[simp]
theorem matrixLaplacianEval_apply (A : Matrix n n Real)
    (H : EuclideanSpace Real n [×2]→L[Real] F) :
    matrixLaplacianEval A H =
      HeatEquation.matrixLap A
        (hessianCurryEquiv (EuclideanSpace Real n) F H) := by
  simp only [matrixLaplacianEval,
    HeatEquation.matrixLap,
    sum_apply, smul_apply,
    hessianComponentEval_apply]

def contDiffHolderSpaceMatrixLaplacian
    (A : Matrix n n Real) (alpha : NNReal) :
    ContDiffHolderSpace (V := EuclideanSpace Real n) (F := F) 2 alpha →L[Real]
      BoundedHolderSpace (X := EuclideanSpace Real n) (F := F) alpha :=
  (boundedHolderSpaceMap alpha (matrixLaplacianEval (F := F) A)).comp
    (contDiffHolderSpaceTopJet 2 alpha)

@[simp]
theorem contDiffHolderSpaceMatrixLaplacian_apply
    (A : Matrix n n Real) (alpha : NNReal)
    (u : ContDiffHolderSpace
      (V := EuclideanSpace Real n) (F := F) 2 alpha)
    (x : EuclideanSpace Real n) :
    contDiffHolderSpaceMatrixLaplacian A alpha u x =
      matrixLaplacianEval A
        (iteratedFDeriv Real 2 (contDiffHolderSpaceFun u) x) :=
  rfl

end Matrix

def parabolicC2HolderSpaceLaplacian (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha :=
  (boundedHolderSpaceMap alpha (laplacianEval (V := V) (F := F))).comp
    (parabolicC2HolderSpaceSpatialHessian alpha)

@[simp]
theorem parabolicC2HolderSpaceLaplacian_apply
    (alpha : NNReal)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicC2HolderSpaceLaplacian alpha u p =
      laplacianEval
        (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u) p) :=
  rfl

theorem norm_parabolicC2HolderSpaceLaplacian_le (alpha : NNReal) :
    ‖parabolicC2HolderSpaceLaplacian (V := V) (F := F) alpha‖ ≤
      Module.finrank Real V := by
  calc
    ‖parabolicC2HolderSpaceLaplacian (V := V) (F := F) alpha‖ ≤
        ‖boundedHolderSpaceMap alpha
          (laplacianEval (V := V) (F := F))‖ *
        ‖parabolicC2HolderSpaceSpatialHessian
          (V := V) (F := F) alpha‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖laplacianEval (V := V) (F := F)‖ * 1 := by
      gcongr
      · exact norm_boundedHolderSpaceMap_le alpha
          (laplacianEval (V := V) (F := F))
      · exact norm_parabolicC2HolderSpaceSpatialHessian_le
          (V := V) (F := F) alpha
    _ ≤ Module.finrank Real V := by
      simpa only [mul_one] using norm_laplacianEval_le (V := V) (F := F)

def parabolicHeatOperator (alpha : NNReal) :
    ParabolicC2HolderSpace (V := V) (F := F) alpha →L[Real]
      ParabolicHolderSpace (V := V) (F := F) alpha :=
  parabolicC2HolderSpaceTimeDerivative alpha -
    parabolicC2HolderSpaceLaplacian alpha

@[simp]
theorem parabolicHeatOperator_apply
    (alpha : NNReal)
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (p : ParabolicPoint V) :
    parabolicHeatOperator alpha u p =
      parabolicTimeDerivative (parabolicC2HolderSpaceFun u) p -
        laplacianEval
          (parabolicSpatialJet 2 (parabolicC2HolderSpaceFun u) p) :=
  rfl

theorem norm_parabolicHeatOperator_le (alpha : NNReal) :
    ‖parabolicHeatOperator (V := V) (F := F) alpha‖ ≤
      1 + Module.finrank Real V := by
  calc
    ‖parabolicHeatOperator (V := V) (F := F) alpha‖ ≤
        ‖parabolicC2HolderSpaceTimeDerivative
          (V := V) (F := F) alpha‖ +
        ‖parabolicC2HolderSpaceLaplacian
          (V := V) (F := F) alpha‖ := norm_sub_le _ _
    _ ≤ 1 + Module.finrank Real V :=
      add_le_add
        (norm_parabolicC2HolderSpaceTimeDerivative_le
          (V := V) (F := F) alpha)
        (norm_parabolicC2HolderSpaceLaplacian_le
          (V := V) (F := F) alpha)

end CalabiYau.Schauder
