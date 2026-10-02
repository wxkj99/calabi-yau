-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/PointwiseInner/DualMetric.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Metric.Coordinates.ChartGram
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Manifold Set Filter Bundle CalabiYau.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace CalabiYau.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def modelInnerAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  let e := tangentSpaceModelContinuousLinearEquiv (I := I) x
  e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x)

omit [Module.Finite ℝ E] in
@[simp] lemma modelInnerAt_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v w : E) :
    modelInnerAt (I := I) (M := M) g x v w =
      g.inner x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w) := rfl

omit [Module.Finite ℝ E] in
lemma modelInnerAt_symm
    (g : SmoothRiemannianMetric I M) (x : M) (v w : E) :
    modelInnerAt (I := I) (M := M) g x v w =
      modelInnerAt (I := I) (M := M) g x w v :=
  g.symm x _ _

omit [Module.Finite ℝ E] in
lemma modelInnerAt_pos_of_ne_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    {v : E} (hv : v ≠ 0) :
    0 < modelInnerAt (I := I) (M := M) g x v v :=
  g.pos x _ ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.injective.ne hv)

omit [Module.Finite ℝ E] in
lemma modelInnerAt_nonneg
    (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    0 ≤ modelInnerAt (I := I) (M := M) g x v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [modelInnerAt, map_zero]
  · exact le_of_lt (modelInnerAt_pos_of_ne_zero (I := I) (M := M) g x hv)

omit [Module.Finite ℝ E] in
lemma modelInnerAt_eq_zero_iff
    (g : SmoothRiemannianMetric I M) (x : M) (v : E) :
    modelInnerAt (I := I) (M := M) g x v v = 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [modelInnerAt, h]⟩
  by_contra hv
  have hpos := modelInnerAt_pos_of_ne_zero (I := I) (M := M) g x hv
  exact absurd h (ne_of_gt hpos)

def gramMatrixAt (g : SmoothRiemannianMetric I M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    modelInnerAt (I := I) (M := M) g x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)

@[simp] lemma gramMatrixAt_apply (g : SmoothRiemannianMetric I M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    gramMatrixAt (I := I) (M := M) g x i j =
      modelInnerAt (I := I) (M := M) g x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := rfl

lemma gramMatrixAt_isHermitian
    (g : SmoothRiemannianMetric I M) (x : M) :
    (gramMatrixAt (I := I) (M := M) g x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (gramMatrixAt (I := I) (M := M) g x j i) =
    gramMatrixAt (I := I) (M := M) g x i j
  rw [gramMatrixAt_apply, gramMatrixAt_apply, star_trivial]
  exact g.symm x _ _

lemma gramMatrixAt_inv_isHermitian
    (g : SmoothRiemannianMetric I M) (x : M) :
    ((gramMatrixAt (I := I) (M := M) g x)⁻¹).IsHermitian :=
  (gramMatrixAt_isHermitian (I := I) (M := M) g x).inv

lemma gramMatrixAt_posDef
    (g : SmoothRiemannianMetric I M) (x : M) :
    (gramMatrixAt (I := I) (M := M) g x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (gramMatrixAt_isHermitian (I := I) (M := M) g x) ?_
  intro v hv
  let w : E := ∑ i : Fin (Module.finrank ℝ E),
    v i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) i
  have hw_ne : w ≠ 0 := by
    intro h
    have hlin : LinearIndependent ℝ ((CalabiYau.Tensor.Coordinates.chartModelBasis E) : Fin _ → E) :=
      (CalabiYau.Tensor.Coordinates.chartModelBasis E).linearIndependent
    rw [Fintype.linearIndependent_iff] at hlin
    exact hv (funext (hlin v h))
  have hquad : star v ⬝ᵥ (gramMatrixAt (I := I) (M := M) g x) *ᵥ v =
      modelInnerAt (I := I) (M := M) g x w w := by
    have hbilin :
        modelInnerAt (I := I) (M := M) g x w w =
          ∑ j : Fin (Module.finrank ℝ E),
            v j * ∑ i : Fin (Module.finrank ℝ E),
              v i * modelInnerAt (I := I) (M := M) g x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
                ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
      change modelInnerAt (I := I) (M := M) g x (∑ i, v i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
          (∑ j, v j • (CalabiYau.Tensor.Coordinates.chartModelBasis E) j) = _
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hsm1 :
          (modelInnerAt (I := I) (M := M) g x (∑ i, v i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
              (v j • (CalabiYau.Tensor.Coordinates.chartModelBasis E) j)
            = v j * (modelInnerAt (I := I) (M := M) g x (∑ i, v i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
        have hh : (modelInnerAt (I := I) (M := M) g x (∑ i, v i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
              (v j • (CalabiYau.Tensor.Coordinates.chartModelBasis E) j)
            = v j • (modelInnerAt (I := I) (M := M) g x (∑ i, v i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) :=
          ContinuousLinearMap.map_smul
            (modelInnerAt (I := I) (M := M) g x (∑ i, v i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
            (v j) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j)
        rw [hh, smul_eq_mul]
      rw [hsm1]
      congr 1
      rw [map_sum, sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      have hsm2 :
          (modelInnerAt (I := I) (M := M) g x (v i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
              ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) =
            v i * (modelInnerAt (I := I) (M := M) g x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
        have hh : modelInnerAt (I := I) (M := M) g x (v i • (CalabiYau.Tensor.Coordinates.chartModelBasis E) i) =
            v i • modelInnerAt (I := I) (M := M) g x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) :=
          ContinuousLinearMap.map_smul (modelInnerAt (I := I) (M := M) g x) (v i) ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
        rw [hh, smul_apply, smul_eq_mul]
      exact hsm2
    rw [hbilin]
    have hLHS :
        ∑ i : Fin (Module.finrank ℝ E),
            star (v i) * (gramMatrixAt (I := I) (M := M) g x *ᵥ v) i =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              v i * v j * modelInnerAt (I := I) (M := M) g x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
                ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [star_trivial]
      change v i * (∑ j : Fin (Module.finrank ℝ E),
          gramMatrixAt (I := I) (M := M) g x i j * v j) = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [gramMatrixAt_apply]
      ring
    change ∑ i : Fin (Module.finrank ℝ E),
        star (v i) * (gramMatrixAt (I := I) (M := M) g x *ᵥ v) i = _
    rw [hLHS]
    have hRHS :
        ∑ j : Fin (Module.finrank ℝ E),
            v j * ∑ i : Fin (Module.finrank ℝ E),
              v i * modelInnerAt (I := I) (M := M) g x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
                ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              v i * v j * modelInnerAt (I := I) (M := M) g x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
                ((CalabiYau.Tensor.Coordinates.chartModelBasis E) j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [hRHS]
  rw [hquad]
  exact g.pos x w hw_ne

lemma gramMatrixAt_inv_posSemidef
    (g : SmoothRiemannianMetric I M) (x : M) :
    ((gramMatrixAt (I := I) (M := M) g x)⁻¹).PosSemidef :=
  (gramMatrixAt_posDef (I := I) (M := M) g x).inv.posSemidef

lemma gramMatrixAt_inv_eigenvalues_pos
    (g : SmoothRiemannianMetric I M) (x : M) (k : Fin (Module.finrank ℝ E)) :
    0 < (gramMatrixAt_inv_isHermitian (I := I) (M := M) g x).eigenvalues k := by
  have hpd : ((gramMatrixAt (I := I) (M := M) g x)⁻¹).PosDef :=
    (gramMatrixAt_posDef (I := I) (M := M) g x).inv
  exact hpd.eigenvalues_pos k

lemma gramMatrixAt_isUnit
    (g : SmoothRiemannianMetric I M) (x : M) :
    IsUnit (gramMatrixAt (I := I) (M := M) g x) :=
  (gramMatrixAt_posDef (I := I) (M := M) g x).isUnit

lemma gramMatrixAt_inv_mul_self
    (g : SmoothRiemannianMetric I M) (x : M) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ *
        gramMatrixAt (I := I) (M := M) g x = 1 := by
  refine Matrix.nonsing_inv_mul _ ?_
  exact Matrix.isUnit_iff_isUnit_det _ |>.mp
    (gramMatrixAt_isUnit (I := I) (M := M) g x)

noncomputable def separableFormAt
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ) (v : Fin r → E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
    (fun i => modelInnerAt (I := I) (M := M) g x (v i))

omit [Module.Finite ℝ E] in
@[simp]
lemma separableFormAt_apply
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ) (v w : Fin r → E) :
    separableFormAt (I := I) (M := M) g x r v w =
      ∏ i : Fin r, modelInnerAt (I := I) (M := M) g x (v i) (w i) := by
  unfold separableFormAt
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

private noncomputable def lowerAllUpperIndicesFn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) : ℝ :=
  T (separableFormAt (I := I) (M := M) g x r
      (fun i : Fin r => v (Fin.castAdd s i)))
    (fun j : Fin s => v (Fin.natAdd r j))

private lemma castAdd_ne_natAdd {r s : ℕ} (i : Fin r) (j : Fin s) :
    Fin.castAdd s i ≠ Fin.natAdd r j := by
  intro h
  have hcoe := Fin.val_eq_of_eq h
  simp [Fin.castAdd, Fin.natAdd] at hcoe
  omega

private lemma natAdd_ne_castAdd {r s : ℕ} (j : Fin s) (i : Fin r) :
    Fin.natAdd r j ≠ Fin.castAdd s i := fun h => castAdd_ne_natAdd i j h.symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E] in
private lemma update_castAdd_first
    {r s : ℕ} (v : Fin (r + s) → E) (i : Fin r) (c : E) :
    (fun k : Fin r => Function.update v (Fin.castAdd s i) c (Fin.castAdd s k)) =
      Function.update (fun k : Fin r => v (Fin.castAdd s k)) i c := by
  classical
  funext k
  rw [Function.update_apply, Function.update_apply]
  by_cases hk : k = i
  · subst hk
    simp
  · rw [if_neg hk, if_neg]
    intro h
    exact hk (Fin.castAdd_injective r s h.symm).symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E] in
private lemma update_castAdd_first_noop_last
    {r s : ℕ} (v : Fin (r + s) → E) (i : Fin r) (c : E) :
    (fun j : Fin s => Function.update v (Fin.castAdd s i) c (Fin.natAdd r j)) =
      (fun j : Fin s => v (Fin.natAdd r j)) := by
  classical
  funext j
  rw [Function.update_apply]
  rw [if_neg (natAdd_ne_castAdd j i)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E] in
private lemma update_natAdd_last_noop_first
    {r s : ℕ} (v : Fin (r + s) → E) (j : Fin s) (c : E) :
    (fun k : Fin r => Function.update v (Fin.natAdd r j) c (Fin.castAdd s k)) =
      (fun k : Fin r => v (Fin.castAdd s k)) := by
  classical
  funext k
  rw [Function.update_apply]
  rw [if_neg (castAdd_ne_natAdd k j)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E] in
private lemma update_natAdd_last
    {r s : ℕ} (v : Fin (r + s) → E) (j : Fin s) (c : E) :
    (fun k : Fin s => Function.update v (Fin.natAdd r j) c (Fin.natAdd r k)) =
      Function.update (fun k : Fin s => v (Fin.natAdd r k)) j c := by
  classical
  funext k
  rw [Function.update_apply, Function.update_apply]
  by_cases hk : k = j
  · subst hk
    simp
  · rw [if_neg hk, if_neg]
    intro h
    exact hk (Fin.natAdd_injective s r h.symm).symm

omit [Module.Finite ℝ E] in
private lemma separableFormAt_update_add
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ)
    (v : Fin r → E) (i : Fin r) (a b : E) :
    separableFormAt (I := I) (M := M) g x r
        (Function.update v i (a + b))
      = separableFormAt (I := I) (M := M) g x r (Function.update v i a) +
        separableFormAt (I := I) (M := M) g x r (Function.update v i b) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro w
  simp only [separableFormAt_apply, add_apply]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase, Function.update_self]
  have hrest : ∀ (c : E),
      ∏ k ∈ Finset.univ.erase i, modelInnerAt (I := I) (M := M) g x (Function.update v i c k) (w k)
        = ∏ k ∈ Finset.univ.erase i, modelInnerAt (I := I) (M := M) g x (v k) (w k) := by
    intro c
    refine Finset.prod_congr rfl ?_
    intro k hk
    rw [Finset.mem_erase] at hk
    rw [Function.update_of_ne hk.1]
  rw [hrest, hrest, hrest]
  have h_inner_add : modelInnerAt (I := I) (M := M) g x (a + b) (w i) =
      modelInnerAt (I := I) (M := M) g x a (w i) + modelInnerAt (I := I) (M := M) g x b (w i) := by
    have : modelInnerAt (I := I) (M := M) g x (a + b) = modelInnerAt (I := I) (M := M) g x a + modelInnerAt (I := I) (M := M) g x b :=
      ContinuousLinearMap.map_add (modelInnerAt (I := I) (M := M) g x) a b
    rw [this, add_apply]
  rw [h_inner_add]
  ring

omit [Module.Finite ℝ E] in
private lemma separableFormAt_update_smul
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ)
    (v : Fin r → E) (i : Fin r) (c : ℝ) (a : E) :
    separableFormAt (I := I) (M := M) g x r
        (Function.update v i (c • a))
      = c • separableFormAt (I := I) (M := M) g x r (Function.update v i a) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro w
  simp only [separableFormAt_apply, smul_apply,
    smul_eq_mul]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase, Function.update_self]
  have hrest : ∀ (c' : E),
      ∏ k ∈ Finset.univ.erase i, modelInnerAt (I := I) (M := M) g x (Function.update v i c' k) (w k)
        = ∏ k ∈ Finset.univ.erase i, modelInnerAt (I := I) (M := M) g x (v k) (w k) := by
    intro c'
    refine Finset.prod_congr rfl ?_
    intro k hk
    rw [Finset.mem_erase] at hk
    rw [Function.update_of_ne hk.1]
  rw [hrest, hrest]
  have h_inner_smul : modelInnerAt (I := I) (M := M) g x (c • a) (w i) = c * modelInnerAt (I := I) (M := M) g x a (w i) := by
    have : modelInnerAt (I := I) (M := M) g x (c • a) = c • modelInnerAt (I := I) (M := M) g x a :=
      ContinuousLinearMap.map_smul (modelInnerAt (I := I) (M := M) g x) c a
    rw [this, smul_apply, smul_eq_mul]
  rw [h_inner_smul]
  ring

private noncomputable def lowerAllUpperIndicesML
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    MultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ := by
  classical
  refine MultilinearMap.mk'
    (fun v => lowerAllUpperIndicesFn (I := I) (M := M) g r s x T v)
    (fun v i a b => ?_) (fun v i c a => ?_)
  · refine Fin.addCases ?_ ?_ i
    · intro i'
      simp only [lowerAllUpperIndicesFn]
      rw [update_castAdd_first_noop_last,
          update_castAdd_first_noop_last,
          update_castAdd_first_noop_last,
          update_castAdd_first,
          update_castAdd_first,
          update_castAdd_first]
      rw [separableFormAt_update_add,
          ContinuousLinearMap.map_add,
          add_apply]
    · intro j'
      simp only [lowerAllUpperIndicesFn]
      rw [update_natAdd_last_noop_first,
          update_natAdd_last_noop_first,
          update_natAdd_last_noop_first,
          update_natAdd_last,
          update_natAdd_last,
          update_natAdd_last]
      rw [ContinuousMultilinearMap.map_update_add]
  · refine Fin.addCases ?_ ?_ i
    · intro i'
      simp only [lowerAllUpperIndicesFn]
      rw [update_castAdd_first_noop_last,
          update_castAdd_first_noop_last,
          update_castAdd_first,
          update_castAdd_first]
      rw [separableFormAt_update_smul,
          ContinuousLinearMap.map_smul,
          smul_apply]
    · intro j'
      simp only [lowerAllUpperIndicesFn]
      rw [update_natAdd_last_noop_first,
          update_natAdd_last_noop_first,
          update_natAdd_last,
          update_natAdd_last]
      rw [ContinuousMultilinearMap.map_update_smul]

@[simp]
private lemma lowerAllUpperIndicesML_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    lowerAllUpperIndicesML (I := I) (M := M) g r s x T v =
      T (separableFormAt (I := I) (M := M) g x r
          (fun i : Fin r => v (Fin.castAdd s i)))
        (fun j : Fin s => v (Fin.natAdd r j)) := by
  classical
  unfold lowerAllUpperIndicesML
  rfl

private lemma lowerAllUpperIndicesML_norm_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    ‖lowerAllUpperIndicesML (I := I) (M := M) g r s x T v‖
      ≤ (‖T‖ * ∏ _i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) *
        ∏ j : Fin (r + s), ‖v j‖ := by
  classical
  rw [lowerAllUpperIndicesML_apply]
  have hsplit : ∏ j : Fin (r + s), ‖v j‖
      = (∏ i : Fin r, ‖v (Fin.castAdd s i)‖) *
        ∏ j : Fin s, ‖v (Fin.natAdd r j)‖ := by
    rw [Fin.prod_univ_add]
  set α := separableFormAt (I := I) (M := M) g x r
      (fun i : Fin r => v (Fin.castAdd s i)) with hα_def
  have hα_bound :
      ‖α‖ ≤ ∏ i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖ * ‖v (Fin.castAdd s i)‖ := by
    rw [hα_def]
    change ‖(ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
            (fun i => modelInnerAt (I := I) (M := M) g x (v (Fin.castAdd s i)))‖ ≤ _
    have h₁ :
        ‖(ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
            (fun i => modelInnerAt (I := I) (M := M) g x (v (Fin.castAdd s i)))‖
          ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ‖ *
            ∏ i : Fin r, ‖modelInnerAt (I := I) (M := M) g x (v (Fin.castAdd s i))‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ)
        (fun i => modelInnerAt (I := I) (M := M) g x (v (Fin.castAdd s i)))
    have h_mkPi : ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ‖ = 1 :=
      ContinuousMultilinearMap.norm_mkPiAlgebra
    rw [h_mkPi] at h₁
    rw [one_mul] at h₁
    refine h₁.trans ?_
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_
    intro i _
    exact (modelInnerAt (I := I) (M := M) g x).le_opNorm (v (Fin.castAdd s i))
  calc ‖T α (fun j : Fin s => v (Fin.natAdd r j))‖
      ≤ ‖T α‖ * ∏ j : Fin s, ‖v (Fin.natAdd r j)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ (‖T‖ * ‖α‖) * ∏ j : Fin s, ‖v (Fin.natAdd r j)‖ := by
        gcongr
        exact T.le_opNorm α
    _ ≤ (‖T‖ * (∏ i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖ * ‖v (Fin.castAdd s i)‖)) *
          ∏ j : Fin s, ‖v (Fin.natAdd r j)‖ := by
        gcongr
    _ = (‖T‖ * (∏ i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) *
            (∏ i : Fin r, ‖v (Fin.castAdd s i)‖)) *
          ∏ j : Fin s, ‖v (Fin.natAdd r j)‖ := by
        rw [Finset.prod_mul_distrib]; ring
    _ = (‖T‖ * ∏ i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) *
          ((∏ i : Fin r, ‖v (Fin.castAdd s i)‖) *
            ∏ j : Fin s, ‖v (Fin.natAdd r j)‖) := by ring
    _ = (‖T‖ * ∏ i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) *
          ∏ j : Fin (r + s), ‖v j‖ := by rw [← hsplit]

private noncomputable def lowerAllUpperIndicesCMLM
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ :=
  (lowerAllUpperIndicesML (I := I) (M := M) g r s x T).mkContinuous
    (‖T‖ * ∏ _i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖)
    (lowerAllUpperIndicesML_norm_bound (I := I) (M := M) g r s x T)

@[simp]
private lemma lowerAllUpperIndicesCMLM_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T v =
      T (separableFormAt (I := I) (M := M) g x r
          (fun i : Fin r => v (Fin.castAdd s i)))
        (fun j : Fin s => v (Fin.natAdd r j)) := by
  unfold lowerAllUpperIndicesCMLM
  change (lowerAllUpperIndicesML (I := I) (M := M) g r s x T) v = _
  rw [lowerAllUpperIndicesML_apply]

private lemma lowerAllUpperIndicesCMLM_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x 0 = 0 := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [lowerAllUpperIndicesCMLM_apply, zero_apply]
  rfl

private lemma lowerAllUpperIndicesCMLM_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T₁ T₂ : TensorRSModel r s ℝ E) :
    lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x (T₁ + T₂) =
      lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T₁ +
        lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T₂ := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  simp [add_apply]

private lemma lowerAllUpperIndicesCMLM_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (T : TensorRSModel r s ℝ E) :
    lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x (c • T) =
      c • lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  simp [smul_apply, smul_apply]

private noncomputable def lowerAllUpperIndicesAddHom
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →+
      ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ where
  toFun := fun T => lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T
  map_zero' := lowerAllUpperIndicesCMLM_zero
    (I := I) (M := M) g r s x
  map_add' := fun T₁ T₂ =>
    lowerAllUpperIndicesCMLM_add (I := I) (M := M) g r s x T₁ T₂

private lemma lowerAllUpperIndicesCMLM_norm_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) :
    ‖lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T‖
      ≤ (∏ _i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) * ‖T‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound ?_ ?_
  · exact mul_nonneg (Finset.prod_nonneg
      (fun _ _ => norm_nonneg _)) (norm_nonneg _)
  · intro v
    have h := lowerAllUpperIndicesML_norm_bound
      (I := I) (M := M) g r s x T v
    have heval :
        ‖lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T v‖ =
          ‖lowerAllUpperIndicesML (I := I) (M := M) g r s x T v‖ := by
      rw [lowerAllUpperIndicesCMLM_apply, lowerAllUpperIndicesML_apply]
    rw [heval]
    calc ‖lowerAllUpperIndicesML (I := I) (M := M) g r s x T v‖
        ≤ (‖T‖ * ∏ _i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) *
            ∏ j : Fin (r + s), ‖v j‖ := h
      _ = (∏ _i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) * ‖T‖ *
            ∏ j : Fin (r + s), ‖v j‖ := by ring

noncomputable def lowerAllUpperIndices
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ where
  toFun := fun T => lowerAllUpperIndicesCMLM (I := I) (M := M) g r s x T
  map_add' := lowerAllUpperIndicesCMLM_add (I := I) (M := M) g r s x
  map_smul' := lowerAllUpperIndicesCMLM_smul (I := I) (M := M) g r s x
  cont := AddMonoidHomClass.continuous_of_bound
    (lowerAllUpperIndicesAddHom (I := I) (M := M) g r s x)
    (∏ i : Fin r, ‖modelInnerAt (I := I) (M := M) g x‖) (fun T =>
      (lowerAllUpperIndicesCMLM_norm_bound
        (I := I) (M := M) g r s x T).trans_eq (by ring))

@[simp]
lemma lowerAllUpperIndices_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    lowerAllUpperIndices (I := I) (M := M) g r s x T v =
      T (separableFormAt (I := I) (M := M) g x r
          (fun i : Fin r => v (Fin.castAdd s i)))
        (fun j : Fin s => v (Fin.natAdd r j)) :=
  lowerAllUpperIndicesCMLM_apply (I := I) (M := M) g r s x T v

private lemma separableFormAt_basis_apply
    (g : SmoothRiemannianMetric I M) (x : M) (r : ℕ)
    (idx jdx : Fin r → Fin (Module.finrank ℝ E)) :
    separableFormAt (I := I) (M := M) g x r
        (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (idx k))
        (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)) =
      ∏ k : Fin r,
        gramMatrixAt (I := I) (M := M) g x (idx k) (jdx k) := by
  rw [separableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [gramMatrixAt_apply]

private lemma lower_at_basis_pair_zero_of_lower_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (T : TensorRSModel r s ℝ E)
    (hT : lowerAllUpperIndices (I := I) (M := M) g r s x T = 0)
    (idx : Fin r → Fin (Module.finrank ℝ E))
    (jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (T (separableFormAt (I := I) (M := M) g x r
          (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (idx k))))
        (fun j : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx j)) = 0 := by
  have hzero :
      lowerAllUpperIndices (I := I) (M := M) g r s x T
          (Fin.append
            (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (idx k))
            (fun j : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx j))) = 0 := by
    rw [hT]
    rfl
  rw [lowerAllUpperIndices_apply] at hzero
  have hcast :
      (fun k : Fin r =>
          Fin.append
            (fun k' : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (idx k'))
            (fun j' : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx j'))
            (Fin.castAdd s k)) =
        (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (idx k)) := by
    funext k
    exact Fin.append_left _ _ k
  have hnat :
      (fun j : Fin s =>
          Fin.append
            (fun k' : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (idx k'))
            (fun j' : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx j'))
            (Fin.natAdd r j)) =
        (fun j : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx j)) := by
    funext j
    exact Fin.append_right _ _ j
  rw [hcast, hnat] at hzero
  exact hzero

private lemma cmlm_eq_zero_of_basis_zero
    {p : ℕ} (S : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ)
    (h : ∀ φ : Fin p → Fin (Module.finrank ℝ E),
      S (fun k : Fin p => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (φ k)) = 0) :
    S = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear
    (e := fun _ : Fin p => CalabiYau.Tensor.Coordinates.chartModelBasis E) ?_
  intro v
  rw [ContinuousMultilinearMap.toMultilinearMap_zero,
    zero_apply]
  exact h v

private lemma tensor0SModel_ext_basis
    {p : ℕ} (S₁ S₂ : ContinuousMultilinearMap ℝ (fun _ : Fin p => E) ℝ)
    (h : ∀ φ : Fin p → Fin (Module.finrank ℝ E),
      S₁ (fun k : Fin p => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (φ k)) =
        S₂ (fun k : Fin p => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (φ k))) :
    S₁ = S₂ := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear
    (e := fun _ : Fin p => CalabiYau.Tensor.Coordinates.chartModelBasis E) ?_
  intro v
  exact h v

theorem lowerAllUpperIndices_injective
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) :
    Function.Injective
      (lowerAllUpperIndices (I := I) (M := M) g r s x) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro T hT
  let n : ℕ := Module.finrank ℝ E
  refine ContinuousLinearMap.ext ?_
  intro α
  refine cmlm_eq_zero_of_basis_zero (E := E) (p := s) (T α) ?_
  intro kdx
  have hTβ : ∀ idx : Fin r → Fin n,
      (T (separableFormAt (I := I) (M := M) g x r
            (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (idx k))))
          (fun j : Fin s => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (kdx j)) = 0 :=
    fun idx => lower_at_basis_pair_zero_of_lower_zero
      (I := I) (M := M) g r s x T hT idx kdx
  let Ginv : Matrix (Fin n) (Fin n) ℝ :=
    (gramMatrixAt (I := I) (M := M) g x)⁻¹
  let G : Matrix (Fin n) (Fin n) ℝ :=
    gramMatrixAt (I := I) (M := M) g x
  have hGinvG : Ginv * G = 1 := by
    change (gramMatrixAt (I := I) (M := M) g x)⁻¹ *
        gramMatrixAt (I := I) (M := M) g x = 1
    exact gramMatrixAt_inv_mul_self (I := I) (M := M) g x
  let c : (Fin r → Fin n) → ℝ := fun idx =>
    ∑ jdx : Fin r → Fin n,
      α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)) *
        ∏ k : Fin r, Ginv (jdx k) (idx k)
  have hspan :
      α = ∑ idx : Fin r → Fin n, c idx •
        separableFormAt (I := I) (M := M) g x r
          (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (idx k)) := by
    refine tensor0SModel_ext_basis _ _ ?_
    intro kdx'
    rw [sum_apply]
    have hRHS_step :
        (∑ idx : Fin r → Fin n,
          (c idx • separableFormAt (I := I) (M := M) g x r
            (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (idx k)))
            (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (kdx' k)))
          = ∑ idx : Fin r → Fin n,
            c idx * ∏ k : Fin r, G (idx k) (kdx' k) := by
      refine Finset.sum_congr rfl ?_
      intro idx _
      rw [smul_apply, smul_eq_mul,
        separableFormAt_basis_apply]
    rw [hRHS_step]
    have hRHS_expand :
        ∑ idx : Fin r → Fin n,
            c idx * ∏ k : Fin r, G (idx k) (kdx' k)
          = ∑ jdx : Fin r → Fin n,
            α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)) *
              ∑ idx : Fin r → Fin n,
                (∏ k : Fin r, Ginv (jdx k) (idx k)) *
                  ∏ k : Fin r, G (idx k) (kdx' k) := by
      have h1 : ∀ idx : Fin r → Fin n,
          c idx * ∏ k : Fin r, G (idx k) (kdx' k)
            = ∑ jdx : Fin r → Fin n,
              α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)) *
                ((∏ k : Fin r, Ginv (jdx k) (idx k)) *
                  ∏ k : Fin r, G (idx k) (kdx' k)) := by
        intro idx
        change (∑ jdx : Fin r → Fin n,
              α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)) *
                ∏ k : Fin r, Ginv (jdx k) (idx k)) *
              ∏ k : Fin r, G (idx k) (kdx' k) = _
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro jdx _
        ring
      rw [Finset.sum_congr rfl (fun idx _ => h1 idx)]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro jdx _
      rw [Finset.mul_sum]
    rw [hRHS_expand]
    have hcombine : ∀ jdx : Fin r → Fin n,
        ∑ idx : Fin r → Fin n,
            (∏ k : Fin r, Ginv (jdx k) (idx k)) *
              ∏ k : Fin r, G (idx k) (kdx' k)
          = ∑ idx : Fin r → Fin n,
            ∏ k : Fin r, Ginv (jdx k) (idx k) * G (idx k) (kdx' k) := by
      intro jdx
      refine Finset.sum_congr rfl ?_
      intro idx _
      rw [← Finset.prod_mul_distrib]
    have hfubini : ∀ jdx : Fin r → Fin n,
        ∑ idx : Fin r → Fin n,
            ∏ k : Fin r, Ginv (jdx k) (idx k) * G (idx k) (kdx' k)
          = ∏ k : Fin r,
            ∑ ik : Fin n, Ginv (jdx k) ik * G ik (kdx' k) := by
      intro jdx
      rw [Fintype.prod_sum (κ := fun _ : Fin r => Fin n)
          (f := fun k ik => Ginv (jdx k) ik * G ik (kdx' k))]
    have hkron : ∀ jdx : Fin r → Fin n, ∀ k : Fin r,
        ∑ ik : Fin n, Ginv (jdx k) ik * G ik (kdx' k)
          = (1 : Matrix (Fin n) (Fin n) ℝ) (jdx k) (kdx' k) := by
      intro jdx k
      have h := hGinvG
      have hentry : (Ginv * G) (jdx k) (kdx' k) =
          (1 : Matrix (Fin n) (Fin n) ℝ) (jdx k) (kdx' k) := by
        rw [h]
      rw [← hentry]
      rw [Matrix.mul_apply]
    have hone_pi : ∀ jdx : Fin r → Fin n,
        ∏ k : Fin r,
            (1 : Matrix (Fin n) (Fin n) ℝ) (jdx k) (kdx' k)
          = if jdx = kdx' then 1 else 0 := by
      intro jdx
      simp only [Matrix.one_apply]
      by_cases hjk : jdx = kdx'
      · subst hjk
        simp
      · rw [if_neg hjk]
        have hjk' : ∃ k : Fin r, jdx k ≠ kdx' k := Function.ne_iff.mp hjk
        obtain ⟨k₀, hk₀⟩ := hjk'
        refine Finset.prod_eq_zero (Finset.mem_univ k₀) ?_
        rw [if_neg hk₀]
    have hsimplify :
        ∑ jdx : Fin r → Fin n,
            α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)) *
              ∑ idx : Fin r → Fin n,
                (∏ k : Fin r, Ginv (jdx k) (idx k)) *
                  ∏ k : Fin r, G (idx k) (kdx' k)
          = α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (kdx' k)) := by
      have hrewrite : ∀ jdx : Fin r → Fin n,
          α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)) *
              ∑ idx : Fin r → Fin n,
                (∏ k : Fin r, Ginv (jdx k) (idx k)) *
                  ∏ k : Fin r, G (idx k) (kdx' k)
            = α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)) *
              if jdx = kdx' then (1 : ℝ) else 0 := by
        intro jdx
        rw [hcombine jdx, hfubini jdx]
        congr 1
        rw [Finset.prod_congr rfl (fun k _ => hkron jdx k)]
        exact hone_pi jdx
      rw [Finset.sum_congr rfl (fun jdx _ => hrewrite jdx)]
      have hsum :
          ∑ jdx : Fin r → Fin n,
              α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)) *
                (if jdx = kdx' then (1 : ℝ) else 0)
            = ∑ jdx : Fin r → Fin n,
              if jdx = kdx' then
                α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k))
              else 0 := by
        refine Finset.sum_congr rfl ?_
        intro jdx _
        by_cases hjk : jdx = kdx'
        · subst hjk; simp
        · simp [hjk]
      rw [hsum]
      have h := Finset.sum_ite_eq' Finset.univ kdx'
        (fun jdx => α (fun k : Fin r => (CalabiYau.Tensor.Coordinates.chartModelBasis E) (jdx k)))
      rw [h, if_pos (Finset.mem_univ _)]
    rw [hsimplify]
  rw [hspan]
  rw [map_sum]
  rw [sum_apply]
  refine Finset.sum_eq_zero ?_
  intro idx _
  rw [ContinuousLinearMap.map_smul, smul_apply,
    smul_eq_mul]
  rw [hTβ idx, mul_zero]

end CalabiYau.L2

end
