-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/Duhamel/FrozenPositiveDefinite.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.Duhamel.Frozen
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.PositiveDefinite.Basic
public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor

@[expose] public section

-- and its private helpers occur in public declarations.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open MeasureTheory Real Matrix
open scoped RealInnerProductSpace InnerProductSpace TensorProduct
namespace HeatEquation
private abbrev Euc (n : Type*) := EuclideanSpace ℝ n
section Pullback

variable {V F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def linPullBoundedContinuousFunction (L : V ≃L[ℝ] V) (u : BoundedContinuousFunction V F) :
    BoundedContinuousFunction V F where
  toFun := fun x => u (L x)
  continuous_toFun := u.continuous.comp L.continuous
  map_bounded' := by
    obtain ⟨C, hC⟩ := u.bounded
    exact ⟨C, fun x y => hC (L x) (L y)⟩

omit [NormedSpace ℝ F] in
@[simp]
theorem linPullBoundedContinuousFunction_apply (L : V ≃L[ℝ] V)
    (u : BoundedContinuousFunction V F) (x : V) :
    linPullBoundedContinuousFunction L u x = u (L x) := rfl

omit [NormedSpace ℝ F] in
theorem norm_linPullBoundedContinuousFunction (L : V ≃L[ℝ] V)
    (u : BoundedContinuousFunction V F) :
    ‖linPullBoundedContinuousFunction L u‖ = ‖u‖ := by
  apply le_antisymm
  · rw [BoundedContinuousFunction.norm_le (norm_nonneg u)]
    intro x
    exact u.norm_coe_le_norm (L x)
  · rw [BoundedContinuousFunction.norm_le (norm_nonneg (linPullBoundedContinuousFunction L u))]
    intro x
    simpa only [linPullBoundedContinuousFunction_apply, ContinuousLinearEquiv.apply_symm_apply] using
      (linPullBoundedContinuousFunction L u).norm_coe_le_norm (L.symm x)

def precompJet (L : V ≃L[ℝ] V) :
    (V →L[ℝ] F) →L[ℝ] V →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ V V F).flip
    (L : V →L[ℝ] V)

@[simp]
theorem precompJet_apply (L : V ≃L[ℝ] V) (D : V →L[ℝ] F) (v : V) :
    precompJet L D v = D (L v) := by
  simp [precompJet, ContinuousLinearMap.compL_apply]

theorem norm_precompJet_le (L : V ≃L[ℝ] V) (D : V →L[ℝ] F) :
    ‖precompJet L D‖ ≤ ‖(L : V →L[ℝ] V)‖ * ‖D‖ := by
  rw [mul_comm]
  exact D.opNorm_comp_le (L : V →L[ℝ] V)

def pushHess (L : V ≃L[ℝ] V) :
    (V →L[ℝ] V →L[ℝ] F) →L[ℝ] V →L[ℝ] V →L[ℝ] F :=
  let P := precompJet (F := F) L
  ((ContinuousLinearMap.compL ℝ V (V →L[ℝ] F) (V →L[ℝ] F)) P).comp
    ((ContinuousLinearMap.compL ℝ V V (V →L[ℝ] F)).flip
      (L : V →L[ℝ] V))

@[simp]
theorem pushHess_apply (L : V ≃L[ℝ] V)
    (B : V →L[ℝ] V →L[ℝ] F) (v w : V) :
    pushHess L B v w = B (L v) (L w) := by
  simp [pushHess, precompJet, ContinuousLinearMap.compL_apply]

theorem norm_pushHess_le (L : V ≃L[ℝ] V)
    (B : V →L[ℝ] V →L[ℝ] F) :
    ‖pushHess L B‖ ≤ ‖(L : V →L[ℝ] V)‖ ^ 2 * ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (sq_nonneg _) (norm_nonneg B))
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg B)) (norm_nonneg v))
  intro w
  rw [pushHess_apply]
  calc
    ‖B (L v) (L w)‖ ≤ ‖B (L v)‖ * ‖L w‖ :=
      (B (L v)).le_opNorm (L w)
    _ ≤ (‖B‖ * ‖L v‖) *
        (‖(L : V →L[ℝ] V)‖ * ‖w‖) := by
      gcongr
      · exact B.le_opNorm (L v)
      · exact (L : V →L[ℝ] V).le_opNorm w
    _ ≤ (‖B‖ * (‖(L : V →L[ℝ] V)‖ * ‖v‖)) *
        (‖(L : V →L[ℝ] V)‖ * ‖w‖) := by
      gcongr
      exact (L : V →L[ℝ] V).le_opNorm v
    _ = (‖(L : V →L[ℝ] V)‖ ^ 2 * ‖B‖ * ‖v‖) * ‖w‖ := by
      ring

theorem lipschitzWith_pushHess (L : V ≃L[ℝ] V) :
    LipschitzWith (‖(L : V →L[ℝ] V)‖₊ ^ 2)
      (pushHess (F := F) L) := by
  apply LipschitzWith.of_dist_le_mul
  intro B C
  rw [dist_eq_norm, ← map_sub]
  simpa only [NNReal.coe_pow, coe_nnnorm, dist_eq_norm] using
    norm_pushHess_le L (B - C)

def pullJet1 (L : V ≃L[ℝ] V)
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) :
    BoundedContinuousFunction V (V →L[ℝ] F) :=
  (precompJet (F := F) L).compLeftContinuousBounded V (linPullBoundedContinuousFunction L du)

def pullJet2 (L : V ≃L[ℝ] V)
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F)) :
    BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F) := by
  let P : (V →L[ℝ] V →L[ℝ] F) →L[ℝ] V →L[ℝ] V →L[ℝ] F :=
    pushHess (V := V) (F := F) L
  refine
    { toFun := fun x => P (d2u (L x))
      continuous_toFun := P.continuous.comp (d2u.continuous.comp L.continuous)
      map_bounded' := ?_ }
  obtain ⟨C, hC⟩ := d2u.bounded
  refine ⟨‖P‖ * C, fun x y => (P.dist_le_opNorm _ _).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hC (L x) (L y)) (norm_nonneg P)

@[simp]
theorem pullJet1_apply (L : V ≃L[ℝ] V)
    (du : BoundedContinuousFunction V (V →L[ℝ] F)) (x v : V) :
    pullJet1 L du x v = du (L x) (L v) := by
  simp [pullJet1]

@[simp]
theorem pullJet2_apply (L : V ≃L[ℝ] V)
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (x v w : V) :
    pullJet2 L d2u x v w = d2u (L x) (L v) (L w) := by
  simp [pullJet2]

theorem linPull_fderiv (L : V ≃L[ℝ] V)
    (u : BoundedContinuousFunction V F)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (hu : ∀ x : V, HasFDerivAt (u : V → F) (du x) x) (x : V) :
    HasFDerivAt (linPullBoundedContinuousFunction L u : V → F) (pullJet1 L du x) x := by
  have h := (hu (L x)).comp x L.hasFDerivAt
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

theorem pullJet1_fderiv (L : V ≃L[ℝ] V)
    (du : BoundedContinuousFunction V (V →L[ℝ] F))
    (d2u : BoundedContinuousFunction V (V →L[ℝ] V →L[ℝ] F))
    (hdu : ∀ x : V,
      HasFDerivAt (du : V → V →L[ℝ] F) (d2u x) x) (x : V) :
    HasFDerivAt (pullJet1 L du : V → V →L[ℝ] F)
      (pullJet2 L d2u x) x := by
  have houter := (hdu (L x)).comp x L.hasFDerivAt
  have h := (precompJet (F := F) L).hasFDerivAt.comp x houter
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

end Pullback

section TraceAlgebra

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lapEval_basis {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ V) (B : V →L[ℝ] V →L[ℝ] F) :
    lapEval B = ∑ i, B (e i) (e i) := by
  let T : V ⊗[ℝ] V →ₗ[ℝ] F := TensorProduct.lift B.toLinearMap₁₂
  have h := congrArg T
    (InnerProductSpace.canonicalCovariantTensor_eq_sum V e)
  simp only [T, InnerProductSpace.canonicalCovariantTensor, map_sum,
    TensorProduct.lift.tmul, ContinuousLinearMap.toLinearMap₁₂_apply] at h
  rw [lapEval_apply]
  exact h

variable {n : Type*} [Fintype n] [DecidableEq n]

def factorLap (L : Euc n ≃L[ℝ] Euc n)
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) : F :=
  ∑ i : n, B (L (EuclideanSpace.basisFun n ℝ i))
    (L (EuclideanSpace.basisFun n ℝ i))

def matrixLap (A : Matrix n n ℝ)
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) : F :=
  ∑ i : n, ∑ j : n,
    A i j • B (EuclideanSpace.basisFun n ℝ i)
      (EuclideanSpace.basisFun n ℝ j)

omit [DecidableEq n] in
theorem factorLap_pull (L : Euc n ≃L[ℝ] Euc n)
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) :
    factorLap L (pushHess (F := F) L.symm B) = lapEval B := by
  unfold factorLap
  simp only [pushHess_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact (lapEval_basis (EuclideanSpace.basisFun n ℝ) B).symm
omit [DecidableEq n] in
private theorem factorLap_self (L : Euc n ≃L[ℝ] Euc n)
    (hL : IsSelfAdjoint (L : Euc n →L[ℝ] Euc n))
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) :
    factorLap L B =
      ∑ i : n, ∑ j : n,
        (⟪EuclideanSpace.basisFun n ℝ i,
          L (L (EuclideanSpace.basisFun n ℝ j))⟫_ℝ) •
            B (EuclideanSpace.basisFun n ℝ i)
              (EuclideanSpace.basisFun n ℝ j) := by
  let e := EuclideanSpace.basisFun n ℝ
  have hdiag : ∀ k : n,
      B (L (e k)) (L (e k)) =
        ∑ i : n, ∑ j : n,
          (⟪e i, L (e k)⟫_ℝ * ⟪e j, L (e k)⟫_ℝ) • B (e i) (e j) := by
    intro k
    have hk := e.sum_repr' (L (e k))
    calc
      B (L (e k)) (L (e k)) =
          B (∑ i : n, ⟪e i, L (e k)⟫_ℝ • e i)
            (∑ j : n, ⟪e j, L (e k)⟫_ℝ • e j) :=
        (congrArg (fun z => B z z) hk).symm
      _ = ∑ i : n, ∑ j : n,
          (⟪e i, L (e k)⟫_ℝ * ⟪e j, L (e k)⟫_ℝ) • B (e i) (e j) := by
        simp only [map_sum, map_smul, _root_.sum_apply,
          _root_.smul_apply, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_comm]
  have hcoef : ∀ i j : n,
      (∑ k : n, ⟪e i, L (e k)⟫_ℝ * ⟪e j, L (e k)⟫_ℝ) =
        ⟪e i, L (L (e j))⟫_ℝ := by
    intro i j
    calc
      (∑ k : n, ⟪e i, L (e k)⟫_ℝ * ⟪e j, L (e k)⟫_ℝ) =
          ∑ k : n, ⟪L (e i), e k⟫_ℝ * ⟪e k, L (e j)⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro k hk
        have hleft :
            ⟪e i, L (e k)⟫_ℝ = ⟪L (e i), e k⟫_ℝ := by
          change ⟪e i, (L : Euc n →L[ℝ] Euc n) (e k)⟫_ℝ =
            ⟪(L : Euc n →L[ℝ] Euc n) (e i), e k⟫_ℝ
          exact (hL.isSymmetric (e i) (e k)).symm
        have hright :
            ⟪e j, L (e k)⟫_ℝ = ⟪e k, L (e j)⟫_ℝ := by
          calc
            ⟪e j, L (e k)⟫_ℝ = ⟪L (e k), e j⟫_ℝ :=
              real_inner_comm _ _
            _ = ⟪e k, L (e j)⟫_ℝ := by
              change ⟪(L : Euc n →L[ℝ] Euc n) (e k), e j⟫_ℝ =
                ⟪e k, (L : Euc n →L[ℝ] Euc n) (e j)⟫_ℝ
              exact hL.isSymmetric (e k) (e j)
        rw [hleft, hright]
      _ = ⟪L (e i), L (e j)⟫_ℝ := e.sum_inner_mul_inner _ _
      _ = ⟪e i, L (L (e j))⟫_ℝ := hL.isSymmetric _ _
  unfold factorLap
  rw [Finset.sum_congr rfl (fun k _ => hdiag k)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.sum_smul, hcoef]

theorem spd_factorLap (A : Matrix n n ℝ) (hA : A.PosDef)
    (B : Euc n →L[ℝ] Euc n →L[ℝ] F) :
    factorLap (spdSqrtEquiv A hA) B = matrixLap A B := by
  rw [factorLap_self (spdSqrtEquiv A hA) (spdSqrt_selfAdj A hA)]
  unfold matrixLap
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [spdSqrt_comp]
  have hentry :
      (⟪EuclideanSpace.basisFun n ℝ i,
        Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A
          (EuclideanSpace.basisFun n ℝ j)⟫_ℝ) = A i j := by
    rw [Matrix.inner_toEuclideanCLM]
    simp [EuclideanSpace.basisFun_apply, dotProduct, Matrix.mulVec]
  rw [hentry]

end TraceAlgebra

section SPDEvolution

variable {n F : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def spdDuhamel (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction (Euc n) F) (x : Euc n) : F :=
  let L := spdSqrtEquiv A hA
  frozenDuhamel t a (linPullBoundedContinuousFunction L u) (L.symm x)

def spdDuhamelD1 (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (x : Euc n) : Euc n →L[ℝ] F :=
  let L := spdSqrtEquiv A hA
  (frozenDuhamel t a (pullJet1 L du) (L.symm x)).comp
    (L.symm : Euc n →L[ℝ] Euc n)

def spdDuhamelD2 (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F))
    (x : Euc n) : Euc n →L[ℝ] Euc n →L[ℝ] F :=
  let L := spdSqrtEquiv A hA
  pushHess (F := F) L.symm
    (frozenDuhamel t a (pullJet2 L d2u) (L.symm x))

omit [Nonempty n]
  [CompleteSpace F] in
@[simp]
theorem spdDuhamel_zero (A : Matrix n n ℝ) (hA : A.PosDef)
    (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction (Euc n) F) (x : Euc n) :
    spdDuhamel A hA 0 a u x = 0 := by
  simp [spdDuhamel]

omit [Nonempty n]
  [CompleteSpace F] in
@[simp]
theorem spdDuhamelD1_zero (A : Matrix n n ℝ) (hA : A.PosDef)
    (a : BoundedContinuousFunction ℝ ℝ)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (x : Euc n) : spdDuhamelD1 A hA 0 a du x = 0 := by
  ext v
  simp [spdDuhamelD1]

omit [Nonempty n]
  [CompleteSpace F] in
@[simp]
theorem spdDuhamelD2_zero (A : Matrix n n ℝ) (hA : A.PosDef)
    (a : BoundedContinuousFunction ℝ ℝ)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F))
    (x : Euc n) : spdDuhamelD2 A hA 0 a d2u x = 0 := by
  ext v w
  simp [spdDuhamelD2]

omit [CompleteSpace F] in
theorem spdDuhamel_space (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (hu : ∀ x : Euc n, HasFDerivAt (u : Euc n → F) (du x) x)
    (x : Euc n) :
    HasFDerivAt (fun y : Euc n => spdDuhamel A hA t a u y)
      (spdDuhamelD1 A hA t a du x) x := by
  let L := spdSqrtEquiv A hA
  have hpull : ∀ z : Euc n,
      HasFDerivAt (linPullBoundedContinuousFunction L u : Euc n → F) (pullJet1 L du z) z :=
    fun z => linPull_fderiv L u du hu z
  have h := (frozenDuhamel_space t a (linPullBoundedContinuousFunction L u)
    (pullJet1 L du) hpull (L.symm x)).comp x L.symm.hasFDerivAt
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

omit [CompleteSpace F] in
theorem spdDuhamelD1_space (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F))
    (hdu : ∀ x : Euc n,
      HasFDerivAt (du : Euc n → Euc n →L[ℝ] F) (d2u x) x)
    (x : Euc n) :
    HasFDerivAt (fun y : Euc n => spdDuhamelD1 A hA t a du y)
      (spdDuhamelD2 A hA t a d2u x) x := by
  let L := spdSqrtEquiv A hA
  have hpull : ∀ z : Euc n,
      HasFDerivAt (pullJet1 L du : Euc n → Euc n →L[ℝ] F)
        (pullJet2 L d2u z) z :=
    fun z => pullJet1_fderiv L du d2u hdu z
  have hz := frozenDuhamel_space t a (pullJet1 L du)
    (pullJet2 L d2u) hpull (L.symm x)
  have hdom := hz.comp x L.symm.hasFDerivAt
  have h := (precompJet (F := F) L.symm).hasFDerivAt.comp x hdom
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

theorem spdDuhamel_lap (A : Matrix n n ℝ) (hA : A.PosDef) (t : ℝ)
    (a : BoundedContinuousFunction ℝ ℝ)
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F)) (x : Euc n) :
    matrixLap A (spdDuhamelD2 A hA t a d2u x) =
      frozenDuhamel t a
        (coreLap (pullJet2 (spdSqrtEquiv A hA) d2u))
        ((spdSqrtEquiv A hA).symm x) := by
  let L := spdSqrtEquiv A hA
  let d2p := pullJet2 L d2u
  let B : Euc n →L[ℝ] Euc n →L[ℝ] F :=
    frozenDuhamel t a d2p (L.symm x)
  have hfactor :
      factorLap L (pushHess L.symm B) = lapEval B :=
    factorLap_pull (F := F) (n := n) L B
  have hlap :
      lapEval B = frozenDuhamel t a (coreLap d2p) (L.symm x) := by
    exact frozenDuhamel_lap (V := Euc n) (F := F) t a d2p (L.symm x)
  change matrixLap A (pushHess L.symm B) =
    frozenDuhamel t a (coreLap d2p) (L.symm x)
  calc
    _ = factorLap L (pushHess L.symm B) :=
      (spd_factorLap A hA _).symm
    _ = lapEval B := hfactor
    _ = frozenDuhamel t a (coreLap d2p) (L.symm x) := hlap

theorem spdDuhamel_pde {t : ℝ} (ht : 0 < t)
    (A : Matrix n n ℝ) (hA : A.PosDef)
    (a da : BoundedContinuousFunction ℝ ℝ)
    (ha : ∀ q : ℝ, HasDerivAt (a : ℝ → ℝ) (da q) q)
    (u : BoundedContinuousFunction (Euc n) F)
    (du : BoundedContinuousFunction (Euc n) (Euc n →L[ℝ] F))
    (d2u : BoundedContinuousFunction (Euc n)
      (Euc n →L[ℝ] Euc n →L[ℝ] F))
    (hu : ∀ x : Euc n, HasFDerivAt (u : Euc n → F) (du x) x)
    (hdu : ∀ x : Euc n,
      HasFDerivAt (du : Euc n → Euc n →L[ℝ] F) (d2u x) x)
    (x : Euc n) :
    HasFDerivAt (fun y : Euc n => spdDuhamel A hA t a u y)
        (spdDuhamelD1 A hA t a du x) x ∧
      HasFDerivAt (fun y : Euc n => spdDuhamelD1 A hA t a du y)
        (spdDuhamelD2 A hA t a d2u x) x ∧
      HasDerivAt (fun q : ℝ => spdDuhamel A hA q a u x)
        (matrixLap A (spdDuhamelD2 A hA t a d2u x) + a t • u x) t := by
  refine ⟨spdDuhamel_space A hA t a u du hu x,
    spdDuhamelD1_space A hA t a du d2u hdu x, ?_⟩
  let L := spdSqrtEquiv A hA
  have hpull0 : ∀ z : Euc n,
      HasFDerivAt (linPullBoundedContinuousFunction L u : Euc n → F) (pullJet1 L du z) z :=
    fun z => linPull_fderiv L u du hu z
  have hpull1 : ∀ z : Euc n,
      HasFDerivAt (pullJet1 L du : Euc n → Euc n →L[ℝ] F)
        (pullJet2 L d2u z) z :=
    fun z => pullJet1_fderiv L du d2u hdu z
  have htime := frozenDuhamel_time ht a da ha (linPullBoundedContinuousFunction L u)
    (pullJet1 L du) (pullJet2 L d2u) hpull0 hpull1 (L.symm x)
  have hlap := spdDuhamel_lap A hA t a d2u x
  simpa only [spdDuhamel, L, linPullBoundedContinuousFunction_apply,
    ContinuousLinearEquiv.apply_symm_apply, hlap, add_comm] using htime

end SPDEvolution

end HeatEquation
