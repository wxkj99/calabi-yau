-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Connection/TensorNabla/InducedConnection.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.LieDerivative.Tensor
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace CalabiYau
namespace TensorLieDeriv

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter
    CalabiYau.Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

def covariantDerivTensor0SModelAt (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  dα_X - lieDerivCorrection s ΓX α

omit [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_tensor0SModelAt_apply (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α =
      dα_X - lieDerivCorrection s ΓX α := by
  rfl

def covariantDerivTensor0SModel (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderiv 𝕜 α x (X x)) (ΓX x) (α x)

def covariantDerivTensor0SModelWithin (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDerivTensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x)

def covariantDerivTensorRSModelAt (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    TensorRSModel r s 𝕜 E :=
  dT_X
    - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
    + T.comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r ΓX)

@[simp] theorem covariantDeriv_tensorRSModelAt_apply (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E) :
    covariantDerivTensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T =
      dT_X
        - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX).comp T
        + T.comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r ΓX) := by
  rfl

theorem covariantDeriv_tensorRSModelAt_eval (r s : ℕ)
    (dT_X : TensorRSModel r s 𝕜 E) (ΓX : E →L[𝕜] E)
    (T : TensorRSModel r s 𝕜 E)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) r) (v : Fin s → E) :
    (covariantDerivTensorRSModelAt (𝕜 := 𝕜) (E := E) r s dT_X ΓX T β) v =
      (dT_X β) v -
        ((lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s ΓX) (T β)) v +
        (T ((lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r ΓX) β)) v := by
  simp [covariantDerivTensorRSModelAt, sub_eq_add_neg, add_assoc]


variable {Idx : Type*} [Fintype Idx]
section ChristoffelModel

variable {Idx : Type*} [Fintype Idx]

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_eval_update_basis_sum {s : ℕ}
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (v : Fin s → E) (i : Fin s) (w : E) :
    α (Function.update v i w) =
      ∑ k : Idx, basis.coord k w *
        α (Function.update v i (basis k)) := by
  classical
  have hw : w = ∑ k : Idx, basis.coord k w • basis k := by
    exact (basis.sum_repr w).symm
  calc
    α (Function.update v i w) =
        α (Function.update v i (∑ k : Idx, basis.coord k w • basis k)) := by
      exact congrArg (fun z => α (Function.update v i z)) hw
    _ = ∑ k : Idx,
        α (Function.update v i (basis.coord k w • basis k)) := by
      have h := α.toMultilinearMap.map_update_sum
        (Finset.univ : Finset Idx) i (fun k : Idx => basis.coord k w • basis k) v
      simpa using h
    _ = ∑ k : Idx, basis.coord k w *
        α (Function.update v i (basis k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [α.map_update_smul]
      simp [smul_eq_mul]

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_one_eval_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 1) (v : E) :
    α (fun _ : Fin 1 => v) =
      ∑ k : Idx, basis.coord k v * α (fun _ : Fin 1 => basis k) := by
  have hupdate (w : E) :
      Function.update (fun _ : Fin 1 => v) (0 : Fin 1) w =
        fun _ : Fin 1 => w := by
    funext q
    fin_cases q
    simp
  have h := tensor0SModel_eval_update_basis_sum basis α
    (fun _ : Fin 1 => v) (0 : Fin 1) v
  simpa [hupdate] using h

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_two_eval_first_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k v *
        α (fun q : Fin 2 => if q = 0 then basis k else w) := by
  let base : Fin 2 → E := fun q => if q = 0 then v else w
  have hupdate (z : E) :
      Function.update base (0 : Fin 2) z =
        fun q : Fin 2 => if q = 0 then z else w := by
    funext q
    fin_cases q <;> simp [base]
  have h := tensor0SModel_eval_update_basis_sum basis α base (0 : Fin 2) v
  have hbase : Function.update base (0 : Fin 2) v = base := by
    funext q
    fin_cases q <;> simp [base]
  simpa [hbase, hupdate] using h

omit [CompleteSpace 𝕜] in
private theorem tensor0SModel_two_eval_second_basis_sum
    (basis : Module.Basis Idx 𝕜 E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 2) (v w : E) :
    α (fun q : Fin 2 => if q = 0 then v else w) =
      ∑ k : Idx, basis.coord k w *
        α (fun q : Fin 2 => if q = 0 then v else basis k) := by
  let base : Fin 2 → E := fun q => if q = 0 then v else w
  have hupdate (z : E) :
      Function.update base (1 : Fin 2) z =
        fun q : Fin 2 => if q = 0 then v else z := by
    funext q
    fin_cases q <;> simp [base]
  have h := tensor0SModel_eval_update_basis_sum basis α base (1 : Fin 2) w
  have hbase : Function.update base (1 : Fin 2) w = base := by
    funext q
    fin_cases q <;> simp [base]
  simpa [hbase, hupdate] using h

end ChristoffelModel

def covariantDerivTensorRSModel (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDerivTensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderiv 𝕜 T x (X x)) (ΓX x) (T x)

def covariantDerivTensorRSModelWithin (r s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (T : E → TensorRSModel r s 𝕜 E) (u : Set E) (x : E) :
    TensorRSModel r s 𝕜 E :=
  covariantDerivTensorRSModelAt (𝕜 := 𝕜) (E := E) r s
    (fderivWithin 𝕜 T u x (X x)) (ΓX x) (T x)

end ModelCovariantDerivative

section TangentCovariantDerivative

variable [IsManifold I 1 M]

def covariantDerivVectorField
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    TangentSpace I x :=
  cov Y x (X x)

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_vectorField_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    covariantDerivVectorField (I := I) cov X Y x = cov Y x (X x) := by
  rfl

noncomputable def tangentConstInChart (x₀ : M) (v : E) (p : M) :
    TangentSpace I p :=
  (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v

omit [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] in
@[simp] lemma tangentConstInChart_apply (x₀ : M) (v : E) (p : M) :
    tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v p =
      (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 p v := by
  rfl

section ConnectionEndomorphism

variable [IsManifold I 2 M]

end ConnectionEndomorphism

end TangentCovariantDerivative

section SmoothVectorFieldRSNabla

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

noncomputable def tensor0SModelAt (s : ℕ) (x₀ x : M)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (fun p : M => Tensor0SSpace s I p) x₀)
    ⟨x, A⟩).2

omit [CompleteSpace 𝕜] in
theorem tensor0SModelAt_trivializationAt_symm (s : ℕ) (x₀ : M)
    (T : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀
        ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
          (fun p : M => Tensor0SSpace s I p) x₀).symm
          x₀ T) = T := by
  unfold tensor0SModelAt
  exact congrArg Prod.snd
    ((trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (fun p : M => Tensor0SSpace s I p) x₀).apply_mk_symm
        (mem_baseSet_trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
          (fun p : M => Tensor0SSpace s I p) x₀)
        T)

noncomputable def tensor0SModelInChart (s : ℕ) (x₀ : M)
    (A : (x : M) →
      Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (y : E) : Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  tensor0SModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s x₀ ((extChartAt I x₀).symm y) (A ((extChartAt I x₀).symm y))

private noncomputable def vectorFieldModelInChart (x₀ : M)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) (y : E) : E :=
  tangentSpaceModelContinuousLinearEquiv (I := 𝓘(𝕜, E)) y
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      X (range I) y)

noncomputable def mcovariantDerivTensor0SWithin (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s)
    (u : Set M) (x₀ : M) : Tensor0SSpace s I x₀ := by
  let X' : E → E := vectorFieldModelInChart (I := I) (n := n) x₀ X
  let α' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s x₀ (fun x => α x)
  exact
    (trivializationAt (Tensor0SModel (𝕜 := 𝕜) (E := E) s)
      (fun p : M => Tensor0SSpace s I p) x₀).symm
        x₀
      (covariantDerivTensor0SModelWithin s X' ΓX α'
        ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
        (extChartAt I x₀ x₀))

noncomputable def mcovariantDerivTensorRSWithin (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (ΓX : E → E →L[𝕜] E)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ := by
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  let X' : E → E := vectorFieldModelInChart (I := I) (n := n) x₀ X
  let T' : E → TensorRSModel r s 𝕜 E :=
    fun y =>
      ((trivializationAt (TensorRSModel r s 𝕜 E)
          (fun x => TensorRSSpace r s I x) x₀)
        ⟨(extChartAt I x₀).symm y, T.toFun ((extChartAt I x₀).symm y)⟩).2
  exact
    (trivializationAt (TensorRSModel r s 𝕜 E)
        (fun x => TensorRSSpace r s I x) x₀).symm x₀
      (covariantDerivTensorRSModelWithin r s X' ΓX T'
        ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
        (extChartAt I x₀ x₀))

section ExtractedConnection

variable [IsManifold I 2 M]

end ExtractedConnection

end SmoothVectorFieldRSNabla

end

end TensorLieDeriv

namespace Tensor0SBundle

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Function
    CalabiYau.TensorLieDeriv
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [CompleteSpace 𝕜]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable {n : WithTop ℕ∞}
variable [IsManifold I n M]
variable [IsManifold I (n + 1) M]

end

end Tensor0SBundle
end CalabiYau
