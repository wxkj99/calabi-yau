-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Operator/Gradient/Basic.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Coordinates.Fields.Scalar
public import CalabiYau.Geometry.Manifold.Coordinates.Fields.Vector
public import CalabiYau.Geometry.Manifold.Coordinates.Frame.Chart
public import CalabiYau.Geometry.Riemannian.Metric.Coordinates.ChartGram
public import CalabiYau.Geometry.Riemannian.Operator.DirectionalDerivative
public import CalabiYau.Geometry.Manifold.Tensor.Coordinates.PartialDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix
open CalabiYau.DivergenceTheorem
open CalabiYau.Tensor.Coordinates

namespace CalabiYau.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def metricFlatLinear (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    rw [map_add, add_apply]
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    rw [map_smul, smul_apply]

omit [Module.Finite ℝ E] in
@[simp] lemma metricFlatLinear_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatLinear (I := I) g x v w = g.inner x v w := rfl

omit [Module.Finite ℝ E] in
lemma metricFlatLinear_injective (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (metricFlatLinear (I := I) g x) := by
  intro v w hvw
  have hzero : ∀ z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L z) hvw
    simp only [metricFlatLinear_apply] at h
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub, sub_apply]
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl 0) (hzero (v - w) ▸ hpos)

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma metricFlatLinear_finrank_eq (x : M) :
    Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace I x →ₗ[ℝ] ℝ) :=
  Subspace.dual_finrank_eq.symm

def metricFlatMap (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[ℝ] (TangentSpace I x →ₗ[ℝ] ℝ) :=
  LinearMap.linearEquivOfInjective
    (metricFlatLinear (I := I) g x)
    (metricFlatLinear_injective (I := I) g x)
    (metricFlatLinear_finrank_eq (I := I) (M := M) x)

@[simp] lemma metricFlatMap_apply (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatMap (I := I) g x v w = g.inner x v w := rfl

lemma metricFlatMap_apply_symm (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x ((metricFlatMap (I := I) g x).symm α) w = α w := by
  have h := (metricFlatMap (I := I) g x).apply_symm_apply α
  have hh : metricFlatMap (I := I) g x ((metricFlatMap (I := I) g x).symm α) w = α w :=
    congrArg (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L w) h
  rw [metricFlatMap_apply] at hh
  exact hh

def metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) : TangentSpace I x :=
  (metricFlatMap (I := I) g x).symm α

@[simp] lemma metricSharp_def (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) :
    metricSharp (I := I) g x α = (metricFlatMap (I := I) g x).symm α := rfl

lemma inner_metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x (metricSharp (I := I) g x α) w = α w :=
  metricFlatMap_apply_symm (I := I) g x α w

lemma inner_metricSharp_right (g : SmoothRiemannianMetric I M) (x : M)
    (α : TangentSpace I x →ₗ[ℝ] ℝ) (w : TangentSpace I x) :
    g.inner x w (metricSharp (I := I) g x α) = α w := by
  rw [g.symm x w (metricSharp (I := I) g x α)]
  exact inner_metricSharp (I := I) g x α w

def gradFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap

@[simp] lemma gradFun_def (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    gradFun (I := I) g f x =
      metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap := rfl

lemma inner_gradFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradFun (I := I) g f x) v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  rw [gradFun_def]
  exact inner_metricSharp (I := I) g x (mfderiv I 𝓘(ℝ, ℝ) f x).toLinearMap v

lemma inner_gradFun_right (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (v : TangentSpace I x) :
    g.inner x v (gradFun (I := I) g f x) = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  rw [g.symm x v (gradFun (I := I) g f x)]
  exact inner_gradFun (I := I) g f x v

lemma gradFun_eq_zero_of_mfderiv_eq_zero
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) {x : M}
    (hf : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    gradFun (I := I) g f x = (0 : TangentSpace I x) := by
  rw [gradFun_def, hf]
  exact LinearEquiv.map_zero _

def chartInvGramMatrix (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x)⁻¹

lemma chartInvGramMatrix_mul_chartGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartInvGramMatrix (I := I) g α x * CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x = 1 := by
  have hpos := CalabiYau.Tensor.Coordinates.chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

lemma chartGramMatrix_mul_chartInvGramMatrix
    (g : SmoothRiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x * chartInvGramMatrix (I := I) g α x = 1 := by
  have hpos := CalabiYau.Tensor.Coordinates.chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp : (fun x : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).adjugate i j) =
      (fun x : M => ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ))).det) := by
    funext x
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 : (fun x : M => ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ))).det) =
      (fun x : M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).updateRow j
              (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun x : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun _ : M => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i
          (1 : ℝ)) k) := by
      funext x
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq : (fun x : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun x : M => CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x (σ k) k) := by
      funext x
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact CalabiYau.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

lemma chartInvGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hcongr : ∀ x ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartInvGramMatrix (I := I) g α x i j =
        ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).det)⁻¹ *
          (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).adjugate i j := by
    intro x hx
    have hdet_pos := CalabiYau.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).det ≠ 0 := ne_of_gt hdet_pos
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).det •
            (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).adjugate) i j =
      ((CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).det)⁻¹ *
          (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ ?_
  · have hdet_smooth : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).det)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      CalabiYau.Tensor.Coordinates.chartGramMatrix_det_contMDiffOn (I := I) g α
    intro x hx
    have hdet_pos := CalabiYau.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).det ≠ 0 := ne_of_gt hdet_pos
    have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
        (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x).det := contDiffAt_inv _ hdet_ne
    have h_at := hdet_smooth x hx
    exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt x h_at
  · exact chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j

noncomputable def chartInvGramMatrixL1Sum
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) : ℝ :=
  ∑ ij : (Fin (Module.finrank ℝ E)) × (Fin (Module.finrank ℝ E)),
    |chartInvGramMatrix (I := I) g α x ij.1 ij.2|

lemma chartInvGramMatrix_l1Sum_nonneg
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    0 ≤ chartInvGramMatrixL1Sum (I := I) (M := M) g α x := by
  unfold chartInvGramMatrixL1Sum
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma chartInvGramMatrix_l1Sum_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (chartInvGramMatrixL1Sum (I := I) (M := M) g α)
      (chartAt H α).source := by
  classical
  unfold chartInvGramMatrixL1Sum
  refine continuousOn_finsetSum _ (fun ij _ => ?_)
  have h_base_eq :
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source := rfl
  have h1 :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => chartInvGramMatrix (I := I) g α x ij.1 ij.2)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α ij.1 ij.2
  have h_cont : ContinuousOn
      (fun x : M => chartInvGramMatrix (I := I) g α x ij.1 ij.2)
      (chartAt H α).source := by
    have := h1.continuousOn
    rw [h_base_eq] at this
    exact this
  exact h_cont.abs

def gradChartCoeff (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) : ℝ :=
  ∑ j : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α x i j *
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)

@[simp] lemma gradChartCoeff_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    gradChartCoeff (I := I) g α f i x =
      ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α x i j *
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) := rfl

def gradChartLocal (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    gradChartCoeff (I := I) g α f i x •
      CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x

lemma mfderiv_chartBasisVecFiber_of_mdifferentiableAt
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hxchart : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv I 𝓘(ℝ, ℝ) f x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x) =
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  set φ := extChartAt I α
  have hxsrc : x ∈ φ.source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hxchart
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hxchart
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y = (scalarOnE (I := I) α f) (φ y) := by
    have hsrc_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I) α).mem_nhds hxsrc
    filter_upwards [hsrc_nhd] with y hy
    rw [scalarOnE_def, φ.left_inv hy]
  have hcong : f =ᶠ[𝓝 x] (scalarOnE (I := I) α f) ∘ (extChartAt I α) := hcomp_eq
  have hmfderiv_cong : mfderiv I 𝓘(ℝ, ℝ) f x =
      mfderiv I 𝓘(ℝ, ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x :=
    Filter.EventuallyEq.mfderiv_eq hcong
  rw [hmfderiv_cong]
  have hphi_mdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I α) x :=
    mdifferentiableAt_extChartAt (I := I) (x := α) hxchart
  have hcomp_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x := by
    have h := hcong.mdifferentiableAt_iff (𝕜 := ℝ) (I := I) (I' := 𝓘(ℝ, ℝ))
    exact h.mp hf
  have hphi_symm_mdiff : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm (φ x) := by
    have hcontMDiffOn : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
        (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
    have htgt_int : (extChartAt I α).target ∈ 𝓝 (φ x) := by
      have hint_open : IsOpen (interior (extChartAt I α).target) := isOpen_interior
      exact mem_nhds_iff.mpr ⟨interior _, interior_subset, hint_open, hx_int⟩
    have hcont_at : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (φ x) :=
      (hcontMDiffOn (φ x) (interior_subset hx_int)).contMDiffAt htgt_int
    exact hcont_at.mdifferentiableAt (by simp)
  have hsymm_at_x : (extChartAt I α).symm (φ x) = x := φ.left_inv hxsrc
  have hf_at_symm : MDifferentiableAt I 𝓘(ℝ, ℝ) f ((extChartAt I α).symm (φ x)) := by
    rw [hsymm_at_x]; exact hf
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (f ∘ (extChartAt I α).symm) (φ x) :=
    hf_at_symm.comp (φ x) hphi_symm_mdiff
  have hscalar_eq : (scalarOnE (I := I) α f) = f ∘ (extChartAt I α).symm := by
    funext y; rfl
  have hg_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (scalarOnE (I := I) α f) (φ x) := by
    rw [hscalar_eq]; exact hf_comp_symm
  have hchain :
      mfderiv I 𝓘(ℝ, ℝ) ((scalarOnE (I := I) α f) ∘ (extChartAt I α)) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f) (φ x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) :=
    mfderiv_comp x hg_mdiff hphi_mdiff
  rw [hchain]
  rw [show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (scalarOnE (I := I) α f) (φ x)
      = fderiv ℝ (scalarOnE (I := I) α f) (φ x) from
        mfderiv_eq_fderiv (𝕜 := ℝ) (f := scalarOnE (I := I) α f)]
  have hmfderiv_chartBasis :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x
          (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
        = (CalabiYau.Tensor.Coordinates.chartModelBasis E) i := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hxchart]
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) α
    have heq : CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x = T.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) :=
      by rw [CalabiYau.Tensor.Coordinates.chartBasisVecFiber, T.symmL_apply hbase]
    rw [heq]
    have h_apply :
        T.continuousLinearMapAt ℝ x (T.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i))
          = (CalabiYau.Tensor.Coordinates.chartModelBasis E) i := by
      have heqsymm : T.symm x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i)
            = T.symmL ℝ x ((CalabiYau.Tensor.Coordinates.chartModelBasis E) i) := by
        exact (Bundle.Trivialization.symmL_apply T hbase _).symm
      rw [heqsymm, Bundle.Trivialization.continuousLinearMapAt_symmL T (b := x) hbase]
    exact h_apply
  change fderiv ℝ (scalarOnE (I := I) α f) (φ x)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I α) x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x))
      = CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (φ x)
  rw [hmfderiv_chartBasis]
  rfl

lemma inner_gradChartLocal_chartBasis
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner x (gradChartLocal (I := I) g α f x)
        (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x)
      = CalabiYau.Tensor.Coordinates.partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  unfold gradChartLocal
  rw [show g.inner x (∑ i, gradChartCoeff (I := I) g α f i x •
            CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
          (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) =
        ∑ i, gradChartCoeff (I := I) g α f i x *
          g.inner x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
            (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [show (g.inner x (∑ i, gradChartCoeff (I := I) g α f i x •
              CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)) =
          (∑ i, gradChartCoeff (I := I) g α f i x •
              g.inner x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)) from ?_]
    · rw [sum_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [smul_apply, smul_eq_mul]
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
  have ha : ∀ i, gradChartCoeff (I := I) g α f i x =
      ∑ j, chartInvGramMatrix (I := I) g α x i j *
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) := fun i => rfl
  rw [show ∑ i, gradChartCoeff (I := I) g α f i x *
            g.inner x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
              (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) =
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)) *
              CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x i k from ?_]
  swap
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [ha i]
    rfl
  rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
              CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f)
                (extChartAt I α x)) *
                CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x i k =
          ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
              CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x i k) *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) from ?_]
  swap
  · rw [show ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f)
                  (extChartAt I α x)) *
                  CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x i k =
              ∑ i, ∑ j, (chartInvGramMatrix (I := I) g α x i j *
                  CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x i k) *
                  CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f)
                    (extChartAt I α x) from ?_]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← Finset.sum_mul]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
  have hsym : ∀ i, CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x i k =
      CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x k i := fun i => g.symm x _ _
  have hkron : ∀ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
        CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x i k) =
      if k = j then (1 : ℝ) else 0 := by
    intro j
    rw [show (∑ i, chartInvGramMatrix (I := I) g α x i j *
              CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x i k) =
            (∑ i, CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x k i *
              chartInvGramMatrix (I := I) g α x i j) from ?_]
    swap
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsym i]
      ring
    have hidentity : (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x *
          chartInvGramMatrix (I := I) g α x) k j =
        if k = j then (1 : ℝ) else 0 := by
      rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hx]
      rw [Matrix.one_apply]
    rw [← hidentity]
    rw [Matrix.mul_apply]
  rw [show ∑ j, (∑ i, chartInvGramMatrix (I := I) g α x i j *
            CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x i k) *
              CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) =
          ∑ j, (if k = j then (1 : ℝ) else 0) *
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) from
      Finset.sum_congr rfl (fun j _ => by rw [hkron j])]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    rw [if_neg (Ne.symm hjk), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

lemma gradChartLocal_eq_gradFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target) :
    gradChartLocal (I := I) g α f x = gradFun (I := I) g f x := by
  classical
  have hxchart : x ∈ (chartAt H α).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx; exact hx
  set f' : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f x with hf'_def
  have hmfderiv_basis : ∀ k, f' (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) =
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x) := by
    intro k
    rw [hf'_def]
    exact mfderiv_chartBasisVecFiber_of_mdifferentiableAt
      (I := I) α hf hxchart hx_int k
  apply metricFlatLinear_injective (I := I) g x
  ext v
  change g.inner x (gradChartLocal (I := I) g α f x) v =
    g.inner x (gradFun (I := I) g f x) v
  rw [inner_gradFun (I := I) g f x v]
  change g.inner x (gradChartLocal (I := I) g α f x) v = f' v
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    CalabiYau.Tensor.Coordinates.chartBasisFamily (I := I) α hx
  set c : Fin (Module.finrank ℝ E) → ℝ := fun k => b.repr v k
  have hv_decomp : v = ∑ k, c k • CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x := by
    have h1 : v = ∑ k, b.repr v k • b k := (b.sum_repr v).symm
    rw [h1]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [CalabiYau.Tensor.Coordinates.chartBasisFamily_apply (I := I) α hx k]
  rw [hv_decomp]
  rw [show g.inner x (gradChartLocal (I := I) g α f x)
        (∑ k, c k • CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * g.inner x (gradChartLocal (I := I) g α f x)
          (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [show f' (∑ k, c k • CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) =
        ∑ k, c k * f' (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) from ?_]
  swap
  · rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  rw [inner_gradChartLocal_chartBasis (I := I) g α f hx k, hmfderiv_basis k]

theorem chartBasisFamily_repr_gradFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBasisFamily (I := I) α hx).repr (gradFun (I := I) g f x) i =
      gradChartCoeff (I := I) g α f i x := by
  classical
  rw [← gradChartLocal_eq_gradFun (I := I) g α hf hx hx_int]
  unfold gradChartLocal
  simp_rw [← chartBasisFamily_apply (I := I) α hx]
  simp [Finsupp.single_apply]

theorem grad_norm_sq_chart_of_mem_interior
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H α).source)
    (hxint : extChartAt I α x ∈ interior (extChartAt I α).target) :
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) =
      ∑ i, ∑ j, chartInvGramMatrix (I := I) g α x i j *
        partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) *
        partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hgrad := gradChartLocal_eq_gradFun (I := I) g α hf hbase hxint
  rw [inner_gradFun (I := I) g f x, ← hgrad]
  unfold gradChartLocal
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) α hf hx hxint i]
  change gradChartCoeff (I := I) g α f i x *
      partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) = _
  unfold gradChartCoeff
  rw [Finset.sum_mul]

theorem g_inner_gradFun_le_chartInvGramMatrix_l1Sum_mul_sum_sq_partials_of_mem_interior
    (g : SmoothRiemannianMetric I M) (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H α).source)
    (hxint : extChartAt I α x ∈ interior (extChartAt I α).target) :
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) ≤
      chartInvGramMatrixL1Sum (I := I) (M := M) g α x *
        ∑ k : Fin (Module.finrank ℝ E),
          (partialDeriv (E := E) k (scalarOnE (I := I) α f)
            (extChartAt I α x)) ^ 2 := by
  classical
  rw [grad_norm_sq_chart_of_mem_interior g α hf hx hxint]
  let d : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    partialDeriv (E := E) k (scalarOnE (I := I) α f) (extChartAt I α x)
  let D : ℝ := ∑ k, (d k) ^ 2
  have hd (k : Fin (Module.finrank ℝ E)) : (d k) ^ 2 ≤ D :=
    Finset.single_le_sum (fun j _ => sq_nonneg (d j)) (Finset.mem_univ k)
  have hprod (i j : Fin (Module.finrank ℝ E)) : |d j * d i| ≤ D := by
    rw [abs_mul]
    have hsq : 0 ≤ d j ^ 2 - 2 * |d j| * |d i| + d i ^ 2 := by
      simpa [sub_sq, sq_abs] using sq_nonneg (|d j| - |d i|)
    nlinarith [hd i, hd j]
  change (∑ i, ∑ j, chartInvGramMatrix (I := I) g α x i j * d j * d i) ≤
    chartInvGramMatrixL1Sum (I := I) (M := M) g α x * D
  unfold chartInvGramMatrixL1Sum
  rw [Finset.sum_mul, Fintype.sum_prod_type]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ |chartInvGramMatrix (I := I) g α x i j * d j * d i| := le_abs_self _
    _ = |chartInvGramMatrix (I := I) g α x i j| * |d j * d i| := by
      rw [mul_assoc, abs_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hprod i j) (abs_nonneg _)

theorem grad_norm_sq_chart
    (g : SmoothRiemannianMetric I M) [I.Boundaryless]
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H α).source) :
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) =
      ∑ i, ∑ j, chartInvGramMatrix (I := I) g α x i j *
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x) *
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]
      exact hx
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source hxsrc)
  have hgrad := gradChartLocal_eq_gradFun (I := I) g α hf hbase hx_int
  rw [inner_gradFun (I := I) g f x, ← hgrad]
  unfold gradChartLocal
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul,
    mfderiv_chartBasisVecFiber_of_mdifferentiableAt
      (I := I) α hf hx hx_int i]
  change gradChartCoeff (I := I) g α f i x *
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) α f) (extChartAt I α x) = _
  unfold gradChartCoeff
  rw [Finset.sum_mul]

theorem g_inner_gradFun_le_chartInvGramMatrix_l1Sum_mul_sum_sq_partials
    (g : SmoothRiemannianMetric I M) [I.Boundaryless]
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : x ∈ (chartAt H α).source) :
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) ≤
      chartInvGramMatrixL1Sum (I := I) (M := M) g α x *
        ∑ k : Fin (Module.finrank ℝ E),
          (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) k (scalarOnE (I := I) α f)
            (extChartAt I α x)) ^ 2 := by
  classical
  have hbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have hxsrc : x ∈ (extChartAt I α).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
    have hxtgt : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α hxtgt
  have hgrad_eq :
      gradFun (I := I) g f x = gradChartLocal (I := I) g α f x :=
    (gradChartLocal_eq_gradFun (I := I) g α hf hbase hx_int).symm
  rw [hgrad_eq]
  set c : Fin (Module.finrank ℝ E) → ℝ := fun i =>
    gradChartCoeff (I := I) g α f i x with hc_def
  have hgcl_eq :
      gradChartLocal (I := I) g α f x =
        ∑ i, c i • CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x := by
    unfold gradChartLocal
    rfl
  rw [hgcl_eq]
  set Gmat : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g α x with hGmat_def
  have hG_form : g.inner x
        (∑ i, c i • CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
        (∑ j, c j • CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)
      = dotProduct (star c) (Matrix.mulVec Gmat c) :=
    (CalabiYau.Tensor.Coordinates.chartGramMatrix_dotProduct_mulVec (I := I) g α x c).symm
  rw [hG_form]
  set d : Fin (Module.finrank ℝ E) → ℝ := fun j =>
    CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) (extChartAt I α x)
    with hd_def
  set Ginv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    chartInvGramMatrix (I := I) g α x with hGinv_def
  have hc_eq : ∀ i, c i = ∑ j, Ginv i j * d j := by
    intro i
    rfl
  have hcGc_expand :
      dotProduct (star c) (Matrix.mulVec Gmat c) =
        ∑ i, ∑ j, c i * c j * Gmat i j := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    have h_dot : dotProduct (Gmat i) c =
        ∑ j', Gmat i j' * c j' := rfl
    ring
  rw [hcGc_expand]
  have h_cGc_eq_dGd :
      (∑ i, ∑ j, c i * c j * Gmat i j) =
        ∑ j, ∑ k, Ginv j k * d j * d k := by
    have hstep1 :
        (∑ i, ∑ j, c i * c j * Gmat i j) =
          ∑ j, c j * (∑ i, c i * Gmat i j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hstep1]
    have h_dot_sum : ∀ j, (∑ i, c i * Gmat i j) = d j := by
      intro j
      have hsym : ∀ i, Gmat i j = Gmat j i := fun i => g.symm x _ _
      have h_step :
          (∑ i, c i * Gmat i j) =
            (∑ i, ∑ k, Ginv i k * d k * Gmat j i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hc_eq i]
        rw [hsym i]
        rw [Finset.sum_mul]
      rw [h_step]
      have h_swap : (∑ i, ∑ k, Ginv i k * d k * Gmat j i) =
          ∑ k, d k * (∑ i, Gmat j i * Ginv i k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [h_swap]
      have h_id : ∀ k, (∑ i, Gmat j i * Ginv i k) =
          (Gmat * Ginv) j k := by
        intro k
        rfl
      have h_id_eq_one : ∀ k, (∑ i, Gmat j i * Ginv i k) =
          if j = k then (1 : ℝ) else 0 := by
        intro k
        rw [h_id k, hGmat_def, hGinv_def]
        rw [chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hbase]
        rw [Matrix.one_apply]
      rw [show (∑ k, d k * (∑ i, Gmat j i * Ginv i k)) =
            ∑ k, d k * (if j = k then (1 : ℝ) else 0) from
        Finset.sum_congr rfl (fun k _ => by rw [h_id_eq_one k])]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hjk
        rw [if_neg (Ne.symm hjk), mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ j) hk
    have hstep2 :
        (∑ j, c j * (∑ i, c i * Gmat i j)) =
          ∑ j, c j * d j := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_dot_sum j]
    rw [hstep2]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hc_eq j]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [h_cGc_eq_dGd]
  set D : ℝ := ∑ k, (d k) ^ 2 with hD_def
  have hD_nn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hd_sq_le : ∀ j, (d j) ^ 2 ≤ D := by
    intro j
    rw [hD_def]
    refine Finset.single_le_sum (f := fun k => (d k) ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hd_abs_le_sqrtD : ∀ j, |d j| ≤ Real.sqrt D := by
    intro j
    rw [show |d j| = Real.sqrt ((d j) ^ 2) by rw [Real.sqrt_sq_eq_abs]]
    exact Real.sqrt_le_sqrt (hd_sq_le j)
  have h_dj_dk_le_D : ∀ j k, |d j * d k| ≤ D := by
    intro j k
    rw [abs_mul]
    have h := mul_le_mul (hd_abs_le_sqrtD j) (hd_abs_le_sqrtD k)
      (abs_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.mul_self_sqrt hD_nn] at h
    exact h
  have h_main_le :
      (∑ j, ∑ k, Ginv j k * d j * d k) ≤
        chartInvGramMatrixL1Sum (I := I) (M := M) g α x * D := by
    unfold chartInvGramMatrixL1Sum
    rw [Finset.sum_mul]
    rw [show (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            |chartInvGramMatrix (I := I) g α x ij.1 ij.2| * D) =
          ∑ j, ∑ k, |Ginv j k| * D from ?_]
    swap
    · rw [← Finset.sum_product']
      rfl
    refine Finset.sum_le_sum (fun j _ => ?_)
    refine Finset.sum_le_sum (fun k _ => ?_)
    have h1 : Ginv j k * d j * d k ≤ |Ginv j k * (d j * d k)| := by
      have h := le_abs_self (Ginv j k * (d j * d k))
      have heq : Ginv j k * d j * d k = Ginv j k * (d j * d k) := by ring
      rw [heq]
      exact h
    refine h1.trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h_dj_dk_le_D j k) (abs_nonneg _)
  exact h_main_le

private lemma gradChartCoeff_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeff (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  refine contMDiffOn_finsetSum (fun j _ => ?_)
  refine ContMDiffOn.mul ?_ ?_
  · have h1 : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x => chartInvGramMatrix (I := I) g α x i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    refine h1.mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  · have hpartial : ContDiffOn ℝ ∞
        (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) := by
      have hbase : ContDiffOn ℝ ∞
          (scalarOnE (I := I) α f) (extChartAt I α).target :=
        scalarOnE_contDiffOn (I := I) α hf
      have hbase_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α f)
          (interior (extChartAt I α).target) := hbase.mono interior_subset
      have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (scalarOnE (I := I) α f))
          (interior (extChartAt I α).target) :=
        hbase_int.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
      have hconst : ContDiffOn ℝ ∞ (fun _ : E => (CalabiYau.Tensor.Coordinates.chartModelBasis E) j)
          (interior (extChartAt I α).target) := contDiffOn_const
      exact hfderiv.clm_apply hconst
    have hpartialM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
        (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f))
        (interior (extChartAt I α).target) := hpartial.contMDiffOn
    have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        (chartAt H α).source := contMDiffOn_extChartAt
    have hchart' : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α : M → E)
        ((extChartAt I α).source ∩
          (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
      refine hchart.mono ?_
      intro x hx
      have h1 : x ∈ (extChartAt I α).source := hx.1
      rw [extChartAt_source_eq_chartAt_source (I := I)] at h1
      exact h1
    have hsubset : (extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target ⊆
          (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target :=
      fun _ hx => hx.2
    exact hpartialM.comp hchart' hsubset

private lemma gradChartLocal_contMDiffOn_total
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
  classical
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) ∞ (gradChartCoeff (I := I) g α f i)
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    fun i => gradChartCoeff_contMDiffOn (I := I) g α hf i
  have hbasis : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    refine (CalabiYau.Tensor.Coordinates.chartBasisVec_contMDiffOn (I := I) α i).mono ?_
    intro x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have := hx.1
    rw [extChartAt_source_eq_chartAt_source (I := I)] at this
    exact this
  have hsmul : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (gradChartCoeff (I := I) g α f i x • CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) := by
    intro i
    exact (hcoeff i).smul_section (hbasis i)
  have hsum : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x
        (∑ i, gradChartCoeff (I := I) g α f i x •
          CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x))
      ((extChartAt I α).source ∩
        (extChartAt I α) ⁻¹' interior (extChartAt I α).target) :=
    ContMDiffOn.sum_section (fun i _ => hsmul i)
  exact hsum

private lemma gradChartLocal_contMDiffOn_total_baseSet [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradChartLocal (I := I) g α f x))
      (chartAt H α).source := by
  refine (gradChartLocal_contMDiffOn_total (I := I) g α hf).mono ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  · rw [show (extChartAt I α : M → E) ⁻¹' interior (extChartAt I α).target =
          (extChartAt I α : M → E) ⁻¹' (extChartAt I α).target from ?_]
    · exact (extChartAt I α).map_source
        (by rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx)
    · congr 1
      exact (isOpen_extChartAt_target (I := I) α).interior_eq

lemma gradFun_contMDiff_total [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E x (gradFun (I := I) g f x)) := by
  intro x
  have hx_source : x ∈ (chartAt H x).source := mem_chart_source H x
  have hsrc_open : IsOpen ((chartAt H x).source) := (chartAt H x).open_source
  have hsmooth_local : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (gradChartLocal (I := I) g x f y))
      (chartAt H x).source :=
    gradChartLocal_contMDiffOn_total_baseSet (I := I) g x hf
  have heq_on_source : ∀ y ∈ (chartAt H x).source,
      gradChartLocal (I := I) g x f y = gradFun (I := I) g f y := by
    intro y hy
    have hbase : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hy
    have hy_int : extChartAt I x y ∈ interior (extChartAt I x).target := by
      have hys : y ∈ (extChartAt I x).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hy
      have hytgt : extChartAt I x y ∈ (extChartAt I x).target :=
        (extChartAt I x).map_source hys
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) x hytgt
    have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
      hf.mdifferentiable (by simp) y
    exact gradChartLocal_eq_gradFun (I := I) g x hf_mdiff hbase hy_int
  have hsmooth_local2 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (gradFun (I := I) g f y))
      (chartAt H x).source := by
    refine hsmooth_local.congr ?_
    intro y hy
    have h := heq_on_source y hy
    change TotalSpace.mk' E y (gradFun (I := I) g f y) =
      TotalSpace.mk' E y (gradChartLocal (I := I) g x f y)
    rw [h]
  exact (hsmooth_local2 x hx_source).contMDiffAt (hsrc_open.mem_nhds hx_source)

def gradG [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => gradFun (I := I) g f x, gradFun_contMDiff_total (I := I) g f.contMDiff⟩

@[simp] lemma grad_g_apply [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    (gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      gradFun (I := I) g f x := rfl

theorem tangentSectionAction_eq_inner_grad_g [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) X f x =
      g.inner x (X x)
        ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
  rw [grad_g_apply]
  rw [inner_gradFun_right (I := I) g f x (X x)]
  rfl

theorem inner_grad_g_symm [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (f h : C^∞⟮I, M; ℝ⟯)
    (x : M) :
    g.inner x ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g h : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((gradG (I := I) g h : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g f : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) :=
  g.symm x _ _

lemma gradFun_eq_zero_of_eventuallyEq_zero
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ))) :
    gradFun (I := I) g f x = (0 : TangentSpace I x) := by
  apply gradFun_eq_zero_of_mfderiv_eq_zero
  rw [Filter.EventuallyEq.mfderiv_eq hf]
  rw [mfderiv_const]
  rfl

lemma support_gradFun_subset
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    Function.support (fun x : M => gradFun (I := I) g f x) ⊆ tsupport f := by
  intro x hx
  by_contra hxnotin
  have h_open : IsOpen (tsupport f)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hev : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
    filter_upwards [h_open.mem_nhds hxnotin] with y hy
    by_contra hne
    exact hy (subset_tsupport _ hne)
  exact hx (gradFun_eq_zero_of_eventuallyEq_zero (I := I) g hev)

lemma hasCompactSupport_grad_g [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    (f : C^∞⟮I, M; ℝ⟯) (hf_cs : HasCompactSupport f) :
    HasCompactSupport ((gradG (I := I) g f :
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)) := by
  refine HasCompactSupport.of_support_subset_isCompact (hf_cs : IsCompact (tsupport f)) ?_
  intro x hx
  show x ∈ tsupport f
  exact support_gradFun_subset (I := I) g f hx

end CalabiYau.Riemannian

end

open Manifold
open scoped ContDiff Manifold NNReal

noncomputable section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.Riemannian

theorem grad_norm_le_of_mvfderiv_bound
    (metric : CalabiYau.SmoothRiemannianMetric I M)
    {u : M → ℝ} {x : M} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ v : TangentSpace I x,
      |mvfderiv (I := I) u x v| ≤ C * Real.sqrt (metric.inner x v v)) :
    Real.sqrt (metric.inner x (gradFun metric u x) (gradFun metric u x)) ≤ C := by
  let v : TangentSpace I x := gradFun metric u x
  have hpos : 0 ≤ metric.inner x v v := by
    rcases eq_or_ne v 0 with hv | hv
    · simp [hv]
    · exact (metric.pos x v hv).le
  have hdu : metric.inner x v v = mvfderiv (I := I) u x v := by
    exact inner_gradFun metric u x v
  have hh := hu v
  rw [← hdu, abs_of_nonneg hpos] at hh
  have hs := Real.sq_sqrt hpos
  change Real.sqrt (metric.inner x v v) ≤ C
  nlinarith [Real.sqrt_nonneg (metric.inner x v v)]

end
