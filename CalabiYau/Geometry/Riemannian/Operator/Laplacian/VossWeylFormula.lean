-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Operator/Laplacian/VossWeylFormula.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.ChartInvariance

@[expose] public section


noncomputable section

open CalabiYau.DivergenceTheorem
open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace CalabiYau.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

def chartInvGramOnE (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

lemma chartInvGramOnE_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y =
      chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) i j := rfl

def gradChartCoeffOnE (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    ∑ j : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α i j y *
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) j (scalarOnE (I := I) α f) y

def chartVossWeylIntegrand (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y =>
    gradChartCoeffOnE (I := I) g α f i y * chartDensityOnE (I := I) g α y

lemma chartVossWeylIntegrand_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (i : Fin (Module.finrank ℝ E)) (y : E) :
    chartVossWeylIntegrand (I := I) g α f i y =
      gradChartCoeffOnE (I := I) g α f i y *
        chartDensityOnE (I := I) g α y := rfl

def chartVossWeylLaplacian (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ)
    (x : M) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
        (chartVossWeylIntegrand (I := I) g α f i)
        (extChartAt I α x))
    / chartDensity (I := I) g α x

lemma chartVossWeylLaplacian_def
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M) :
    chartVossWeylLaplacian (I := I) g α f x =
      (∑ i : Fin (Module.finrank ℝ E),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
            (chartVossWeylIntegrand (I := I) g α f i)
            (extChartAt I α x))
        / chartDensity (I := I) g α x := rfl

lemma chartCoeff_grad_g_eq_gradChartCoeff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior (extChartAt I α).target)
    (i : Fin (Module.finrank ℝ E)) :
    chartCoeff (I := I) α (gradG (I := I) g ⟨_, hf⟩) i x =
      gradChartCoeff (I := I) g α f i x := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := CalabiYau.Tensor.Coordinates.chartModelBasis E
  have hxchart : x ∈ (chartAt H α).source := by
    rw [trivializationAt_baseSet_eq_chartAt_source] at hx; exact hx
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hf.mdifferentiable (by simp) x
  have hgrad_eq :
      gradFun (I := I) g f x =
        ∑ k : Fin (Module.finrank ℝ E),
          gradChartCoeff (I := I) g α f k x •
            CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x :=
    (gradChartLocal_eq_gradFun (I := I) g α hf_mdiff hx hx_int).symm
  set L : TangentSpace I x ≃L[ℝ] E := T.continuousLinearEquivAt ℝ x hx with hL_def
  have hL_apply : ∀ v : TangentSpace I x, L v = (T ⟨x, v⟩).2 := fun _ => rfl
  have hL_basis : ∀ k : Fin (Module.finrank ℝ E),
      L (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) α k x) = b k := by
    intro k
    rw [hL_apply]
    exact CalabiYau.Tensor.Coordinates.trivializationAt_chartBasisVec_snd (I := I) α k hx
  have hLgrad : L (gradFun (I := I) g f x) =
      ∑ k : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α f k x • b k := by
    rw [hgrad_eq]
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
    rw [hL_basis k]
  have hrepr_basis_combo :
      b.repr (∑ k : Fin (Module.finrank ℝ E),
            gradChartCoeff (I := I) g α f k x • b k) i =
        gradChartCoeff (I := I) g α f i x := by
    rw [map_sum]
    rw [Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · rw [map_smul, Module.Basis.repr_self]
      simp
    · intro k _ hki
      rw [map_smul, Module.Basis.repr_self]
      simp [Ne.symm hki]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hgrad_g_x : ((gradG (I := I) g ⟨_, hf⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) = gradFun (I := I) g f x :=
    grad_g_apply (I := I) g ⟨_, hf⟩ x
  unfold chartCoeff
  rw [show ((gradG (I := I) g ⟨_, hf⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) = gradFun (I := I) g f x
      from hgrad_g_x]
  rw [show (T ⟨x, gradFun (I := I) g f x⟩).2 = L (gradFun (I := I) g f x)
      from (hL_apply (gradFun (I := I) g f x)).symm]
  rw [hLgrad]
  exact hrepr_basis_combo

private lemma chartCoeffOnE_grad_g_eq_gradChartCoeffOnE [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    chartCoeffOnE (I := I) α (gradG (I := I) g ⟨_, hf⟩) i y =
      gradChartCoeffOnE (I := I) g α f i y := by
  classical
  set z : M := (extChartAt I α).symm y with hz_def
  have hz_source : z ∈ (extChartAt I α).source := (extChartAt I α).map_target hy
  have hz_chart : z ∈ (chartAt H α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hz_source; exact hz_source
  have hz_base : z ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hz_chart
  have htarget_eq_int :
      (extChartAt I α).target = interior (extChartAt I α).target :=
    (isOpen_extChartAt_target (I := I) α).interior_eq.symm
  have hz_image_int : extChartAt I α z ∈ interior (extChartAt I α).target := by
    have h1 : extChartAt I α z = y := (extChartAt I α).right_inv hy
    rw [h1]
    rw [← htarget_eq_int]
    exact hy
  have hpw :=
    chartCoeff_grad_g_eq_gradChartCoeff (I := I) g α hf hz_base hz_image_int i
  have hext_z : extChartAt I α z = y := (extChartAt I α).right_inv hy
  unfold chartCoeffOnE gradChartCoeffOnE
  rw [hpw]
  unfold gradChartCoeff
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hext_z]
  rw [chartInvGramOnE_def]

lemma localDivergence_grad_g_eq_chartVossWeylLaplacian [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    localDivergence (I := I) g α (gradG (I := I) g ⟨_, hf⟩) x =
      chartVossWeylLaplacian (I := I) g α f x := by
  classical
  rw [localDivergence_def, chartVossWeylLaplacian_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  set y₀ : E := extChartAt I α x with hy₀_def
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx
  have hy₀_target : y₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc
  have htarget_open : IsOpen (extChartAt I α).target :=
    isOpen_extChartAt_target (I := I) α
  have htarget_nhd : (extChartAt I α).target ∈ 𝓝 y₀ :=
    htarget_open.mem_nhds hy₀_target
  have hev : (fun y : E =>
        chartCoeffOnE (I := I) α (gradG (I := I) g ⟨_, hf⟩) i y *
          chartDensityOnE (I := I) g α y) =ᶠ[𝓝 y₀]
      chartVossWeylIntegrand (I := I) g α f i := by
    filter_upwards [htarget_nhd] with y hy
    rw [chartVossWeylIntegrand_def,
        chartCoeffOnE_grad_g_eq_gradChartCoeffOnE (I := I) g α hf i hy]
  unfold CalabiYau.Tensor.Coordinates.partialDeriv
  rw [hev.fderiv_eq]

end CalabiYau.Riemannian
