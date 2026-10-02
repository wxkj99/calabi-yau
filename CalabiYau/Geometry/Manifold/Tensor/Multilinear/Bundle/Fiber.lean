-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Tensor/Multilinear/Bundle/Fiber.lean
-- Locally modified.
/-
Authors: Jack McCarthy
-/
module
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Defs
public import CalabiYau.Geometry.Manifold.Tensor.Multilinear.Bundle.Basis

@[expose] public section

open CalabiYau.Tensor.Multilinear

noncomputable section

open Bundle Set

open scoped Manifold Topology Bundle ContDiff BigOperators

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {B : Type*} [TopologicalSpace B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {s : ℕ}

instance instFunLike (s : ℕ) (x : B) :
    FunLike (Bundle.continuousMultilinearMap 𝕜 s F E x) (Fin s → E x) 𝕜 :=
  ContinuousMultilinearMap.funLike

theorem topology_eq (s : ℕ) (x : B) :
    (inferInstance : TopologicalSpace (Bundle.continuousMultilinearMap 𝕜 s F E x)) =
    (inferInstanceAs (TopologicalSpace
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜))) := by
  change instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x = _
  simp only [instTopologicalSpaceContinuousMultilinearMap]
  set e := trivializationAt F E x
  set g : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => e.symmL 𝕜 x) with hg_def
  have hfactor : (↑(Pretrivialization.continuousMultilinearMap 𝕜 s e) ∘
      TotalSpace.mk' _ x) = Prod.mk x ∘ g := by funext; rfl
  rw [hfactor, ← induced_compose, (isInducing_prodMkRight x).eq_induced.symm]
  set g' := ContinuousMultilinearMap.compContinuousLinearMapL (F := 𝕜)
    (E₁ := fun _ : Fin s => F) (E := fun _ : Fin s => E x)
    (fun _ => e.continuousLinearMapAt 𝕜 x) with hg'_def
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  have hleft : Function.LeftInverse g' g := by
    intro L
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp [g, g']
    apply congrArg L
    funext i
    exact e.symmₗ_linearMapAt hx (v i)
  have hright : Function.RightInverse g' g := by
    intro M
    apply ContinuousMultilinearMap.ext
    intro v
    dsimp [g, g']
    apply congrArg M
    funext i
    exact e.linearMapAt_symmₗ hx (v i)
  exact (Homeomorph.mk ⟨g, g', hleft, hright⟩
    g.continuous g'.continuous).isInducing.eq_induced.symm

instance instNormedAddCommGroup (s : ℕ) (x : B) :
    NormedAddCommGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; infer_instance

instance instNormedSpace (s : ℕ) (x : B) :
    NormedSpace 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  delta Bundle.continuousMultilinearMap; exact ContinuousMultilinearMap.normedSpace

instance instT2Space (s : ℕ) (x : B) :
    @T2Space (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@T2Space (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _)

instance instIsTopologicalAddGroup (s : ℕ) (x : B) :
    @IsTopologicalAddGroup (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@IsTopologicalAddGroup
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _)

instance instContinuousSMul (s : ℕ) (x : B) :
    @ContinuousSMul 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) _ _ inferInstance :=
  (topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x).symm ▸
    inferInstanceAs (@ContinuousSMul 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜) _ _ _)

instance instContinuousAdd (s : ℕ) (x : B) :
    @ContinuousAdd (Bundle.continuousMultilinearMap 𝕜 s F E x) inferInstance _ :=
  @IsTopologicalAddGroup.toContinuousAdd _ inferInstance _ (instIsTopologicalAddGroup s x)

def continuousLinearEquivAt (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x ≃L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 where
  toFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).symmL 𝕜 x)
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)
  left_inv L := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).symmₗ_linearMapAt
      (mem_baseSet_trivializationAt F E x) (v i)
  right_inv M := ContinuousMultilinearMap.ext fun v => by
    dsimp [ContinuousMultilinearMap.compContinuousLinearMapL]
    congr 1; funext i
    exact (trivializationAt F E x).linearMapAt_symmₗ
      (mem_baseSet_trivializationAt F E x) (v i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).symmL 𝕜 x)).continuous
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x) _
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from topology_eq s x]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ => (trivializationAt F E x).continuousLinearMapAt 𝕜 x)).continuous

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E] in
@[ext]
theorem ext {s : ℕ} {x : B}
    {T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x}
    (h : ∀ m, T₁ m = T₂ m) : T₁ = T₂ :=
  ContinuousMultilinearMap.ext h

def toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  continuousLinearEquivAt (F := F) (E := E) s x T

def toModelL (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x →L[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜 :=
  (continuousLinearEquivAt (F := F) (E := E) s x).toContinuousLinearMap

def ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    Bundle.continuousMultilinearMap 𝕜 s F E x :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm f

@[simp]
theorem toModelL_apply {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModelL (F := F) (E := E) s x T = toModel T := rfl

@[simp]
theorem toModel_add {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ + T₂) =
      toModel T₁ + toModel T₂ :=
  map_add (continuousLinearEquivAt (F := F) (E := E) s x) T₁ T₂

@[simp]
theorem toModel_smul {s : ℕ} {x : B}
    (c : 𝕜) (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (c • T) = c • toModel T :=
  map_smul (continuousLinearEquivAt (F := F) (E := E) s x) c T

@[simp]
theorem toModel_zero {s : ℕ} {x : B} :
    toModel (F := F) (E := E)
      (0 : Bundle.continuousMultilinearMap 𝕜 s F E x) = 0 :=
  map_zero (continuousLinearEquivAt (F := F) (E := E) s x)

@[simp]
theorem toModel_neg {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (-T) = -toModel T :=
  map_neg (continuousLinearEquivAt (F := F) (E := E) s x) T

@[simp]
theorem toModel_sub {s : ℕ} {x : B}
    (T₁ T₂ : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    toModel (F := F) (E := E) (T₁ - T₂) =
      toModel T₁ - toModel T₂ :=
  map_sub (continuousLinearEquivAt (F := F) (E := E) s x) T₁ T₂

@[simp]
theorem ofModel_toModel {s : ℕ} {x : B}
    (T : Bundle.continuousMultilinearMap 𝕜 s F E x) :
    ofModel (F := F) (E := E) (toModel T) = T :=
  (continuousLinearEquivAt (F := F) (E := E) s x).symm_apply_apply T

@[simp]
theorem toModel_ofModel {s : ℕ} {x : B}
    (f : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :
    toModel (F := F) (E := E) (ofModel (x := x) f) = f :=
  (continuousLinearEquivAt (F := F) (E := E) s x).apply_symm_apply f

theorem toModel_continuous {s : ℕ} {x : B} :
    Continuous
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).continuous_toFun

theorem toModel_injective {s : ℕ} {x : B} :
    Function.Injective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).injective

theorem toModel_surjective {s : ℕ} {x : B} :
    Function.Surjective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).surjective

theorem toModel_bijective {s : ℕ} {x : B} :
    Function.Bijective
      (fun T : Bundle.continuousMultilinearMap 𝕜 s F E x =>
        toModel (F := F) (E := E) T) :=
  (continuousLinearEquivAt (F := F) (E := E) s x).bijective

def fiberContinuousLinearEquiv (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 s F E x ≃L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜 where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    change @Continuous (Bundle.continuousMultilinearMap 𝕜 s F E x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜)
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace id
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from
        topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace
  continuous_invFun := by
    change @Continuous (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E x) 𝕜)
      (Bundle.continuousMultilinearMap 𝕜 s F E x)
      ContinuousMultilinearMap.instTopologicalSpace
      (instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x) id
    rw [show instTopologicalSpaceContinuousMultilinearMap 𝕜 s F E x =
      ContinuousMultilinearMap.instTopologicalSpace from
        topology_eq (𝕜 := 𝕜) (F := F) (E := E) s x]
    exact @continuous_id _ ContinuousMultilinearMap.instTopologicalSpace

def curryFin0Equiv (x : B) :
    Bundle.continuousMultilinearMap 𝕜 0 F E x ≃L[𝕜] 𝕜 :=
  (fiberContinuousLinearEquiv (F := F) 0 x).trans
    (continuousMultilinearCurryFin0 𝕜 (E x) 𝕜)

@[simp] theorem curryFin0Equiv_apply (x : B)
    (T : Bundle.continuousMultilinearMap 𝕜 0 F E x) :
    curryFin0Equiv (𝕜 := 𝕜) (F := F) (E := E) x T = T Fin.elim0 := by
  change T 0 = T Fin.elim0
  exact congrArg T (Subsingleton.elim _ _)

@[simp] theorem curryFin0Equiv_symm_apply (x : B) (c : 𝕜) (v : Fin 0 → E x) :
    (curryFin0Equiv (𝕜 := 𝕜) (F := F) (E := E) x).symm c v = c := rfl

def curryLeftEquiv (s : ℕ) (x : B) :
    Bundle.continuousMultilinearMap 𝕜 (s + 1) F E x ≃L[𝕜]
      (E x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 s F E x) :=
  (fiberContinuousLinearEquiv (F := F) (s + 1) x).trans
    ((continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E x) 𝕜).toContinuousLinearEquiv.trans
      ((ContinuousLinearEquiv.refl 𝕜 (E x)).arrowCongr
        (fiberContinuousLinearEquiv (F := F) s x).symm))

@[simp] theorem curryLeftEquiv_apply (s : ℕ) (x : B)
    (T : Bundle.continuousMultilinearMap 𝕜 (s + 1) F E x)
    (v : E x) (w : Fin s → E x) :
    curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := E) s x T v w = T (Fin.cons v w) := rfl

@[simp] theorem curryLeftEquiv_symm_apply (s : ℕ) (x : B)
    (A : E x →L[𝕜] Bundle.continuousMultilinearMap 𝕜 s F E x)
    (v : Fin (s + 1) → E x) :
    (curryLeftEquiv (𝕜 := 𝕜) (F := F) (E := E) s x).symm A v = A (v 0) (Fin.tail v) := rfl

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

noncomputable instance instFiniteDimensional (s : ℕ) (x : B) :
    FiniteDimensional 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) := by
  have : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) :=
    continuousMultilinearMap_finiteDimensional s
  exact (continuousLinearEquivAt (F := F) (E := E) s x).symm.toLinearEquiv.finiteDimensional

@[simp]
theorem finrank_eq (s : ℕ) (x : B) :
    Module.finrank 𝕜 (Bundle.continuousMultilinearMap 𝕜 s F E x) =
    (Module.finrank 𝕜 F) ^ s := by
  rw [(continuousLinearEquivAt (F := F) (E := E) s x).toLinearEquiv.finrank_eq,
      finrank_continuousMultilinearMap s]

end Bundle.continuousMultilinearMap

end
