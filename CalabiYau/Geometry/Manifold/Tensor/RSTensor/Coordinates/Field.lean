-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/RSTensor/Coordinates/Field.lean
-- Locally modified.
/-
Authors: Yuan Liao, Jack McCarthy
Modified by: Ziyang Qin
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Coordinates.BundleBasis
public import CalabiYau.Geometry.Manifold.Tensor.Product.Defs
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Basis
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.TensorProduct
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.DomainPermutation

@[expose] public section

open CalabiYau.Tensor.Multilinear

namespace CalabiYau
namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

abbrev TensorRSField (r s : ℕ) :=
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ContMDiffSection I
    (TensorRSModel r s 𝕜 E)
    n
    (fun x : M => TensorRSSpace r s I x)

abbrev Tensor0SField (s : ℕ) :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ContMDiffSection I
    (Tensor0SModel s 𝕜 E)
    n
    (fun x : M => Tensor0SSpace s I x)

end

section SmulByFun


section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
variable {r s : ℕ} [CompleteSpace 𝕜]

def tensorRSFieldSmulByFun
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  ⟨fun x => φ x • α x, by
    let := tensorRSBundleFiber (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    let := tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
    intro x₀
    rw [contMDiffAt_section]
    have hα := α.contMDiff x₀
    rw [contMDiffAt_section] at hα
    set e := trivializationAt (TensorRSModel r s 𝕜 E) (fun x => TensorRSSpace r s I x) x₀
    refine ((hφ x₀).smul hα).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀))
      fun x hx => (e.linear 𝕜 hx).2 _ _⟩

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞)
variable {r s : ℕ}

@[simp]
theorem tensorRSField_smulByFun_apply
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : TensorRSField n r s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    tensorRSFieldSmulByFun n φ hφ α x = φ x • α x :=
  rfl

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]
variable {r s : ℕ} [CompleteSpace 𝕜]

def tensor0SFieldSmulByFun
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  ⟨fun x => φ x • α x, hφ.smul_section α.contMDiff⟩

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞)
variable {r s : ℕ}

@[simp]
theorem tensor0SField_smulByFun_apply
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) (x : M) :
    tensor0SFieldSmulByFun n φ hφ α x = φ x • α x :=
  rfl

end

end SmulByFun

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

noncomputable def Tensor0SField.fromScalarField [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) :
    Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  ⟨fun x => ContinuousMultilinearMap.constOfIsEmpty 𝕜
      (fun _ : Fin 0 => TangentSpace I x) (f x), by
    let d := Module.finrank 𝕜 E
    let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) n b _).mpr
      fun σ x₀ => ?_
    have hcoord : ∀ x, (continuousMultilinearMapBasis b 0).repr
        (trivializationAt (Tensor0SModel 0 𝕜 E)
          (fun x => Tensor0SSpace 0 I x) x₀
          ⟨x, ContinuousMultilinearMap.constOfIsEmpty 𝕜
            (fun _ : Fin 0 => TangentSpace I x) (f x)⟩).2 σ = f x := by
      intro x
      simp_rw [continuousMultilinearMap_basis_repr]
      rfl
    exact (hf.contMDiffAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => hcoord x)⟩

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞)

@[simp]
theorem Tensor0SField.fromScalarField_apply [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) (x : M) (v : Fin 0 → TangentSpace I x) :
    Tensor0SField.fromScalarField n f hf x v = f x := by
  unfold Tensor0SField.fromScalarField
  exact ContinuousMultilinearMap.constOfIsEmpty_apply _ _ _ _

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

noncomputable def Tensor0SField.toScalarField
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) : M → 𝕜 :=
  fun x => Tensor0SSpace.toModel (α x) Fin.elim0

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞)

theorem Tensor0SField.toScalarField_contMDiff [CompleteSpace 𝕜]
    (hM : IsManifold I (n + 1) M)
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    ContMDiff I 𝓘(𝕜) n α.toScalarField := by
  rcases hM with ⟨⟩
  let : IsManifold I (n + 1) M := IsManifold.mk
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  have hα := ((contMDiff_multilinearSection_iff_coord (TangentSpace I) n b
    (fun x => (α x : Tensor0SSpace 0 I x))).mp α.contMDiff)
  intro x₀
  refine (hα Fin.elim0 x₀).congr_of_eventuallyEq ?_
  have hbase := (trivializationAt (Tensor0SModel 0 𝕜 E)
    (fun x => Tensor0SSpace 0 I x) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  have hα_const : α x = ContinuousMultilinearMap.constOfIsEmpty 𝕜
      (fun _ : Fin 0 => TangentSpace I x) (Tensor0SField.toScalarField n α x) := by
    ext v
    simp only [tensor0SSpaceContinuousLinearEquiv,             Tensor0SField.toScalarField, Tensor0SSpace.toModel]
    change DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
      (α x) v =
      DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
      (α x) Fin.elim0
    exact congrArg _ (Subsingleton.elim v Fin.elim0)
  simp only [Tensor0SField.toScalarField]
  conv_rhs => rw [hα_const]
  simp_rw [continuousMultilinearMap_basis_repr]
  rfl

@[simp]
theorem Tensor0SField.toScalarField_fromScalarField [CompleteSpace 𝕜]
    (f : M → 𝕜) (hf : ContMDiff I 𝓘(𝕜) n f) :
    Tensor0SField.toScalarField n (Tensor0SField.fromScalarField n f hf) = f := by
  ext x
  exact Tensor0SField.fromScalarField_apply n f hf x Fin.elim0

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

@[simp]
theorem Tensor0SField.fromScalarField_toScalarField [CompleteSpace 𝕜]
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField.fromScalarField n (Tensor0SField.toScalarField n α)
      (Tensor0SField.toScalarField_contMDiff n
        (inferInstance : IsManifold I (n + 1) M) α) = α := by
  let := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  apply ContMDiffSection.ext; intro x
  simp only [Tensor0SField.fromScalarField]
  symm; ext v
  simp only [tensor0SSpaceContinuousLinearEquiv,         Tensor0SField.toScalarField, Tensor0SSpace.toModel]
  change DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
    (α x) v =
    DFunLike.coe (F := ContinuousMultilinearMap 𝕜 (fun _ : Fin 0 => TangentSpace I x) 𝕜)
    (α x) Fin.elim0
  exact congrArg _ (Subsingleton.elim v Fin.elim0)

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞)

@[simp]
theorem Tensor0SField.toScalarField_add
    (α β : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (α + β).toScalarField n = α.toScalarField n + β.toScalarField n := by
  ext x
  simp only [Tensor0SField.toScalarField, Pi.add_apply]
  rw [show (α + β) x = α x + β x from rfl, Tensor0SSpace.toModel_add,
    add_apply]

@[simp]
theorem Tensor0SField.toScalarField_smulByFun
    (φ : M → 𝕜) (hφ : ContMDiff I 𝓘(𝕜) n φ)
    (α : Tensor0SField n 0 (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    (tensor0SFieldSmulByFun n φ hφ α).toScalarField n = φ * α.toScalarField n := by
  ext x
  simp only [Tensor0SField.toScalarField, tensor0SField_smulByFun_apply,
    Tensor0SSpace.toModel_smul, smul_apply, Pi.mul_apply, smul_eq_mul]

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

noncomputable def tensor0SSpaceEvalScalar (x : M) :
    Tensor0SSpace 0 I x →L[𝕜] 𝕜 :=
  (ContinuousMultilinearMap.apply 𝕜
    (fun _ : Fin 0 => TangentSpace I x) 𝕜 Fin.elim0).comp
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x).toContinuousLinearMap

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

@[simp]
theorem Tensor0SSpace.evalScalar_apply (x : M) (c : Tensor0SSpace 0 I x) :
    tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x c = c Fin.elim0 := by
  change
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 0 x c) Fin.elim0 = c Fin.elim0
  rw [tensor0SSpaceFiberContinuousLinearEquiv_apply]
  rfl

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

noncomputable def Tensor0SSpace.toRS0 {s : ℕ} {x : M} (A : Tensor0SSpace s I x) :
    TensorRSSpace 0 s I x :=
  (tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x).smulRight A

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

@[simp]
theorem Tensor0SSpace.toRS0_apply {s : ℕ} {x : M}
    (A : Tensor0SSpace s I x) (c : Tensor0SSpace 0 I x) :
    Tensor0SSpace.toRS0 A c =
      tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x c • A :=
  rfl

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞) [IsManifold I (n + 1) M]

noncomputable def Tensor0SField.toTensorRSField {s : ℕ}
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    TensorRSField n 0 s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) :=
  by
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0 s
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 0
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  exact ⟨fun x =>
      (tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x).smulRight (α x), by
    intro x₀
    rw [contMDiffAt_section x₀]
    have hα := (contMDiffAt_section x₀).mp α.contMDiff.contMDiffAt
    refine ((contMDiffAt_const
      (c := ContinuousLinearMap.smulRightL 𝕜
        (Tensor0SModel 0 𝕜 E)
        (Tensor0SModel s 𝕜 E)
        (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin 0 => E) 𝕜 Fin.elim0))).clm_apply
      hα).congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x₀)] with x hx
    have hx_s : x ∈ (trivializationAt (Tensor0SModel s 𝕜 E)
      (fun y => Tensor0SSpace s I y) x₀).baseSet := hx
    apply ContinuousLinearMap.ext
    intro c₀
    apply ContinuousMultilinearMap.ext
    intro m
    rw [hom_trivializationAt_apply]
    simp only [ContinuousLinearMap.inCoordinates,
      ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRightL_apply_apply,
      smul_apply,
      map_smul,
      Tensor0SSpace.evalScalar_apply]
    have hc₀ :
        ((trivializationAt (Tensor0SModel 0 𝕜 E)
          (fun y => Tensor0SSpace 0 I y) x₀).symmL 𝕜 x c₀) Fin.elim0 =
          (ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin 0 => E) 𝕜 Fin.elim0) c₀ := by
      change (Tensor0SSpace.constInChart (𝕜 := 𝕜) (I := I) 0 x₀ c₀ x) Fin.elim0 =
        c₀ Fin.elim0
      rw [Tensor0SSpace.constInChart_apply (𝕜 := 𝕜) (I := I)
        (x₀ := x₀) (x := x) 0 hx c₀ Fin.elim0]
      exact congrArg c₀ (Subsingleton.elim _ _)
    rw [hc₀]
    have hαx :
        ((trivializationAt (Tensor0SModel s 𝕜 E)
          (fun y => Tensor0SSpace s I y) x₀).continuousLinearMapAt 𝕜 x (α x)) m =
          (trivializationAt (Tensor0SModel s 𝕜 E)
            (fun y => Tensor0SSpace s I y) x₀ ⟨x, α x⟩).2 m := by
      rw [(trivializationAt (Tensor0SModel s 𝕜 E)
        (fun y => Tensor0SSpace s I y) x₀).continuousLinearMapAt_apply 𝕜]
      exact congrArg (fun A : Tensor0SModel s 𝕜 E => A m)
        (congrFun ((trivializationAt _ (fun y => Tensor0SSpace s I y) x₀
          ).coe_linearMapAt_of_mem (R := 𝕜) hx_s) (α x))
    rw [hαx]
    ⟩

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]
variable (n : WithTop ℕ∞)

@[simp]
theorem Tensor0SField.toRS0_apply {s : ℕ}
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (x : M) (c : Tensor0SSpace 0 I x) :
    α.toTensorRSField n x c =
      tensor0SSpaceEvalScalar (𝕜 := 𝕜) (I := I) (M := M) x c • α x :=
  rfl

end

end
end Tensor0SBundle

namespace Tensor0SBundle
noncomputable section

open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section

variable [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable (n : WithTop ℕ∞)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I (n + 1) M]
variable {s q : ℕ}

noncomputable def Tensor0SField.domDomCongr {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n s' (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) := by
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MultilinearSection.domDomCongr (F := E) (E := TangentSpace I) (IB := I) n e α

@[simp]
theorem Tensor0SField.domDomCongr_apply {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (x : M) :
    Tensor0SField.domDomCongr n e α x = Tensor0SSpace.domDomCongr (α x) e := by
  apply tensor0SSpace_ext (I := I) s' x
  intro v
  change ContinuousMultilinearMap.domDomCongr e
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x (α x)) v = _
  rw [ContinuousMultilinearMap.domDomCongr_apply, Tensor0SSpace.domDomCongr_apply]
  simp only [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]

noncomputable def tensor0SFieldProduct
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M))
    (β : Tensor0SField n q (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField n (s + q) (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) := by
  letI : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact MultilinearSection.product (F := E) (E := TangentSpace I) (IB := I) n α β

@[simp]
theorem Tensor0SField.domDomCongr_zero {s s' : ℕ} (e : Fin s ≃ Fin s') :
    Tensor0SField.domDomCongr n e
        (0 : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) = 0 := by
  apply DFunLike.ext _ _
  intro x
  apply tensor0SSpace_ext (I := I) s' x
  intro v
  change Tensor0SSpace.eval
      (Tensor0SSpace.domDomCongr (0 : Tensor0SSpace s I x) e) v =
    Tensor0SSpace.eval (0 : Tensor0SSpace s' I x) v
  rw [Tensor0SSpace.eval_domDomCongr]
  simp

@[simp]
theorem Tensor0SField.domDomCongr_refl {s : ℕ}
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField.domDomCongr n (Equiv.refl (Fin s)) α = α := by
  let _ : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  unfold Tensor0SField.domDomCongr
  exact MultilinearSection.domDomCongr_refl n α

theorem Tensor0SField.domDomCongr_trans {s s' s'' : ℕ}
    (e₁ : Fin s ≃ Fin s') (e₂ : Fin s' ≃ Fin s'')
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField.domDomCongr n e₂ (Tensor0SField.domDomCongr n e₁ α) =
      Tensor0SField.domDomCongr n (e₁.trans e₂) α := by
  let _ : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  unfold Tensor0SField.domDomCongr
  exact MultilinearSection.domDomCongr_trans n e₁ e₂ α

theorem Tensor0SField.domDomCongr_add {s s' : ℕ} (e : Fin s ≃ Fin s')
    (α β : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField.domDomCongr n e (α + β) =
      Tensor0SField.domDomCongr n e α + Tensor0SField.domDomCongr n e β := by
  let _ : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  unfold Tensor0SField.domDomCongr
  exact MultilinearSection.domDomCongr_add n e α β

@[simp]
theorem tensor0SField_product_zero
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    tensor0SFieldProduct n α
        (0 : Tensor0SField n q (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) = 0 := by
  let _ : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  unfold tensor0SFieldProduct
  exact MultilinearSection.product_zero n α

theorem Tensor0SField.domDomCongr_id_of_valPres {s : ℕ} (e : Fin s ≃ Fin s)
    (he : ∀ i, ((e i : Fin s) : ℕ) = (i : ℕ))
    (α : Tensor0SField n s (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)) :
    Tensor0SField.domDomCongr n e α = α := by
  have hee : e = Equiv.refl (Fin s) := Equiv.ext fun i => Fin.ext (he i)
  subst e
  apply DFunLike.ext _ _
  intro x
  apply tensor0SSpace_ext (I := I) s x
  intro v
  change Tensor0SSpace.eval (Tensor0SSpace.domDomCongr (α x) (Equiv.refl (Fin s))) v =
    Tensor0SSpace.eval (α x) v
  rw [Tensor0SSpace.eval_domDomCongr]
  rfl

end

end
end Tensor0SBundle
end CalabiYau
