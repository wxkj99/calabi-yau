-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/DivergenceTheorem/Global/PartitionOfUnity.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.Formula
public import CalabiYau.Geometry.Riemannian.Operator.DirectionalDerivative
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.ChartInvariance
public import CalabiYau.Geometry.Riemannian.Volume.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

@[expose] public section


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace CalabiYau.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

def smoothSmul (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => φ x • X x, hφ.smul_section X.contMDiff⟩

omit [Module.Finite ℝ E] in
@[simp] lemma smoothSmul_apply (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (smoothSmul (I := I) φ hφ X) x = φ x • X x := rfl

lemma chartCoeff_smoothSmul (α : M)
    (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E))
    {x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartCoeff (I := I) α (smoothSmul (I := I) φ hφ X) i x =
      φ x * chartCoeff (I := I) α X i x := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  have hlin : (T ⟨x, (smoothSmul (I := I) φ hφ X) x⟩).2 =
      φ x • (T ⟨x, X x⟩).2 := by
    have h := (T.linear ℝ hx).map_smul (φ x) (X x)
    change (T ⟨x, φ x • X x⟩).2 = φ x • (T ⟨x, X x⟩).2
    exact h
  unfold chartCoeff
  rw [hlin]
  rw [LinearEquiv.map_smul]
  rw [Finsupp.smul_apply, smul_eq_mul]

lemma chartCoeffOnE_smoothSmul (α : M)
    (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E))
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    chartCoeffOnE (I := I) α (smoothSmul (I := I) φ hφ X) i y =
      scalarOnE (I := I) α φ y * chartCoeffOnE (I := I) α X i y := by
  have hsymm_source : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  have hsymm_chart : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymm_source
    exact hsymm_source
  have hsymm_base : (extChartAt I α).symm y ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsymm_chart
  unfold chartCoeffOnE scalarOnE
  exact chartCoeff_smoothSmul (I := I) α φ hφ X i hsymm_base

private lemma localDivergence_at_self_smoothSmul [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (x : M)
    (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    localDivergence (I := I) g x (smoothSmul (I := I) φ hφ X) x =
      φ x * localDivergence (I := I) g x X x +
        tangentSectionAction (I := I) X φ x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  have hρ_pos : 0 < chartDensity (I := I) g x x :=
    chartDensity_pos (I := I) g x hbase
  have hρ_ne : chartDensity (I := I) g x x ≠ 0 := ne_of_gt hρ_pos
  rw [localDivergence_def, localDivergence_def]
  set u : E → ℝ := scalarOnE (I := I) x φ with hu_def
  set v : Fin (Module.finrank ℝ E) → E → ℝ :=
    fun i y => chartCoeffOnE (I := I) x X i y * chartDensityOnE (I := I) g x y with hv_def
  have hintegrand_eq : ∀ y ∈ (extChartAt I x).target,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) x (smoothSmul (I := I) φ hφ X) i y *
          chartDensityOnE (I := I) g x y =
        u y * v i y := by
    intro y hy i
    rw [chartCoeffOnE_smoothSmul (I := I) x φ hφ X i hy]
    change scalarOnE (I := I) x φ y * chartCoeffOnE (I := I) x X i y *
        chartDensityOnE (I := I) g x y =
      u y * (chartCoeffOnE (I := I) x X i y * chartDensityOnE (I := I) g x y)
    ring
  have htarget_open : IsOpen (extChartAt I x).target := isOpen_extChartAt_target (I := I) x
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ := htarget_open.mem_nhds hy₀_target
  have hpartial_eq : ∀ i : Fin (Module.finrank ℝ E),
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
        (fun y => chartCoeffOnE (I := I) x (smoothSmul (I := I) φ hφ X) i y *
          chartDensityOnE (I := I) g x y) y₀ =
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (fun y => u y * v i y) y₀ := by
    intro i
    unfold CalabiYau.Tensor.Coordinates.partialDeriv
    have hev : (fun y => chartCoeffOnE (I := I) x
            (smoothSmul (I := I) φ hφ X) i y * chartDensityOnE (I := I) g x y) =ᶠ[𝓝 y₀]
        (fun y => u y * v i y) := by
      filter_upwards [htarget_nhd] with y hy
      exact hintegrand_eq y hy i
    rw [hev.fderiv_eq]
  have hu_diff : DifferentiableAt ℝ u y₀ := by
    have hu_smooth : ContDiffOn ℝ ∞ u (extChartAt I x).target :=
      scalarOnE_contDiffOn (I := I) x hφ
    have hu_at : ContDiffAt ℝ ∞ u y₀ := by
      have h_within := hu_smooth y₀ hy₀_target
      exact h_within.contDiffAt htarget_nhd
    exact hu_at.differentiableAt (by simp)
  have hv_diff : ∀ i : Fin (Module.finrank ℝ E), DifferentiableAt ℝ (v i) y₀ := by
    intro i
    have hv_smooth : ContDiffOn ℝ ∞ (v i) (extChartAt I x).target :=
      chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g x X i
    have hv_at : ContDiffAt ℝ ∞ (v i) y₀ := by
      have h_within := hv_smooth y₀ hy₀_target
      exact h_within.contDiffAt htarget_nhd
    exact hv_at.differentiableAt (by simp)
  have hLeibniz : ∀ i : Fin (Module.finrank ℝ E),
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (fun y => u y * v i y) y₀ =
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i u y₀ * v i y₀ +
          u y₀ * CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (v i) y₀ := by
    intro i
    unfold CalabiYau.Tensor.Coordinates.partialDeriv
    have hmul : fderiv ℝ (fun y => u y * v i y) y₀ =
        u y₀ • fderiv ℝ (v i) y₀ + v i y₀ • fderiv ℝ u y₀ :=
      fderiv_fun_mul hu_diff (hv_diff i)
    rw [hmul]
    rw [add_apply,
        smul_apply, smul_apply]
    simp only [smul_eq_mul]
    ring
  have hLHS_num :
      ∑ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
          (fun y => chartCoeffOnE (I := I) x (smoothSmul (I := I) φ hφ X) i y *
            chartDensityOnE (I := I) g x y) y₀ =
      ∑ i : Fin (Module.finrank ℝ E),
        (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i u y₀ * v i y₀ +
          u y₀ * CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (v i) y₀) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hpartial_eq i, hLeibniz i]
  rw [hLHS_num]
  rw [Finset.sum_add_distrib]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            u y₀ * CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (v i) y₀) =
          u y₀ *
            ∑ i : Fin (Module.finrank ℝ E),
              CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (v i) y₀ from
        (Finset.mul_sum _ _ _).symm]
  rw [add_div]
  rw [add_comm]
  have hsymm_inv : (extChartAt I x).symm y₀ = x := (extChartAt I x).left_inv hxsrc
  have hu_eq_φ : u y₀ = φ x := by
    change scalarOnE (I := I) x φ y₀ = φ x
    exact scalarOnE_extChartAt (I := I) x φ hxsrc
  congr 1
  · rw [hu_eq_φ]
    rw [mul_div_assoc]
  · have hρOnE : chartDensityOnE (I := I) g x y₀ = chartDensity (I := I) g x x := by
      change chartDensity (I := I) g x ((extChartAt I x).symm y₀) = _
      rw [hsymm_inv]
    have heach : ∀ i : Fin (Module.finrank ℝ E),
        CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i u y₀ * v i y₀ =
          (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i u y₀ * chartCoeffOnE (I := I) x X i y₀) *
            chartDensity (I := I) g x x := by
      intro i
      change CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i u y₀ *
          (chartCoeffOnE (I := I) x X i y₀ * chartDensityOnE (I := I) g x y₀) =
        (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i u y₀ * chartCoeffOnE (I := I) x X i y₀) *
          chartDensity (I := I) g x x
      rw [hρOnE]
      ring
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i u y₀ * v i y₀) =
            ∑ i : Fin (Module.finrank ℝ E),
              (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i u y₀ * chartCoeffOnE (I := I) x X i y₀) *
                chartDensity (I := I) g x x from
          Finset.sum_congr rfl (fun i _ => heach i)]
    rw [← Finset.sum_mul]
    rw [mul_div_assoc, div_self hρ_ne, mul_one]
    have hchartCoeff : ∀ i : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) x X i y₀ = chartCoeff (I := I) x X i x := by
      intro i
      change chartCoeff (I := I) x X i ((extChartAt I x).symm y₀) = _
      rw [hsymm_inv]
    have htsa := tangentSectionAction_chartLocal_of_boundaryless (I := I) x X hφ
      (mem_chart_source H x)
    rw [htsa]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [hchartCoeff i]
    change CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) x φ) y₀ * chartCoeff (I := I) x X i x =
      chartCoeff (I := I) x X i x * CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i (scalarOnE (I := I) x φ)
        (extChartAt I x x)
    ring

theorem divergence_g_smoothSmul [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (φ : M → ℝ) (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ x : M, divergenceG (I := I) g (smoothSmul (I := I) φ hφ X) x =
      φ x * divergenceG (I := I) g X x +
        tangentSectionAction (I := I) X φ x := by
  intro x
  rw [divergence_g_def, divergence_g_def]
  exact localDivergence_at_self_smoothSmul (I := I) g x φ hφ X

omit [Module.Finite ℝ E] in
theorem tangentSectionAction_finset_sum
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (x : M)
    (hf : ∀ α ∈ s, MDifferentiableAt I 𝓘(ℝ) (f α) x) :
    tangentSectionAction (I := I) X (∑ α ∈ s, f α) x =
      ∑ α ∈ s, tangentSectionAction (I := I) X (f α) x := by
  classical
  have heq : ∀ g : M → ℝ, ∀ y : M, ∀ v : TangentSpace I y,
      (mfderiv I 𝓘(ℝ, ℝ) g y) v = mvfderiv (I := I) g y v := by
    intro g y v
    rfl
  simp only [tangentSectionAction_def, heq]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (mvfderiv (I := I) (fun _ : M => (0 : ℝ)) x) (X x) = 0
    change (((NormedSpace.fromTangentSpace ((fun _ : M => (0 : ℝ)) x)).toContinuousLinearMap ∘L
        (mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => (0 : ℝ)) x)) (X x) : ℝ) = 0
    rw [mfderiv_const]
    rfl
  | insert α s hα ih =>
    have hmem_α : α ∈ insert α s := Finset.mem_insert_self α s
    have hmem_rest : ∀ β ∈ s, MDifferentiableAt I 𝓘(ℝ) (f β) x := by
      intro β hβ
      exact hf β (Finset.mem_insert_of_mem hβ)
    have ih_eq := ih hmem_rest
    rw [Finset.sum_insert hα, Finset.sum_insert hα]
    have hsum_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (∑ β ∈ s, f β) x := by
      have aux : ∀ (t : Finset ι), (∀ β ∈ t, MDifferentiableAt I 𝓘(ℝ) (f β) x) →
          MDifferentiableAt I 𝓘(ℝ, ℝ) (∑ β ∈ t, f β) x := by
        intro t ht
        induction t using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          exact mdifferentiable_const ..
        | insert γ t' hγ ih' =>
          have hmem_γ : γ ∈ insert γ t' := Finset.mem_insert_self γ t'
          have ht_rest : ∀ β ∈ t', MDifferentiableAt I 𝓘(ℝ) (f β) x := by
            intro β hβ
            exact ht β (Finset.mem_insert_of_mem hβ)
          rw [Finset.sum_insert hγ]
          exact (ht γ hmem_γ).add (ih' ht_rest)
      exact aux s hmem_rest
    rw [mvfderiv_add (hf α hmem_α) hsum_diff]
    rw [add_apply]
    rw [ih_eq]

theorem divergence_g_add [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ x : M, divergenceG (I := I) g (X + Y) x =
      divergenceG (I := I) g X x + divergenceG (I := I) g Y x := by
  intro x
  classical
  rw [divergence_g_def, divergence_g_def, divergence_g_def]
  rw [localDivergence_def, localDivergence_def, localDivergence_def]
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have htarget_open : IsOpen (extChartAt I x).target := isOpen_extChartAt_target (I := I) x
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ := htarget_open.mem_nhds hy₀_target
  have hchartCoeff_add : ∀ z ∈ (trivializationAt E (TangentSpace I) x).baseSet,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) x (X + Y) i z =
          chartCoeff (I := I) x X i z + chartCoeff (I := I) x Y i z := by
    intro z hz i
    classical
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) x
    have hadd : (T ⟨z, (X + Y) z⟩).2 = (T ⟨z, X z⟩).2 + (T ⟨z, Y z⟩).2 := by
      have h := (T.linear ℝ hz).map_add (X z) (Y z)
      change (T ⟨z, X z + Y z⟩).2 = (T ⟨z, X z⟩).2 + (T ⟨z, Y z⟩).2
      exact h
    unfold chartCoeff
    rw [hadd]
    rw [LinearEquiv.map_add]
    rw [Finsupp.add_apply]
  have hchartCoeffOnE_add : ∀ y ∈ (extChartAt I x).target,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) x (X + Y) i y =
          chartCoeffOnE (I := I) x X i y + chartCoeffOnE (I := I) x Y i y := by
    intro y hy i
    have hsymm_source : (extChartAt I x).symm y ∈ (extChartAt I x).source :=
      (extChartAt I x).map_target hy
    have hsymm_chart : (extChartAt I x).symm y ∈ (chartAt H x).source := by
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsymm_source
      exact hsymm_source
    have hsymm_base : (extChartAt I x).symm y ∈
        (trivializationAt E (TangentSpace I) x).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hsymm_chart
    unfold chartCoeffOnE
    exact hchartCoeff_add ((extChartAt I x).symm y) hsymm_base i
  have hpartial_split : ∀ i : Fin (Module.finrank ℝ E),
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
        (fun y => chartCoeffOnE (I := I) x (X + Y) i y *
          chartDensityOnE (I := I) g x y) y₀ =
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
        (fun y => chartCoeffOnE (I := I) x X i y *
          chartDensityOnE (I := I) g x y) y₀ +
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
        (fun y => chartCoeffOnE (I := I) x Y i y *
          chartDensityOnE (I := I) g x y) y₀ := by
    intro i
    unfold CalabiYau.Tensor.Coordinates.partialDeriv
    have hev : (fun y => chartCoeffOnE (I := I) x (X + Y) i y *
            chartDensityOnE (I := I) g x y) =ᶠ[𝓝 y₀]
        (fun y => chartCoeffOnE (I := I) x X i y * chartDensityOnE (I := I) g x y +
          chartCoeffOnE (I := I) x Y i y * chartDensityOnE (I := I) g x y) := by
      filter_upwards [htarget_nhd] with y hy
      rw [hchartCoeffOnE_add y hy i]
      ring
    rw [hev.fderiv_eq]
    have hfX : DifferentiableAt ℝ
        (fun y => chartCoeffOnE (I := I) x X i y * chartDensityOnE (I := I) g x y) y₀ := by
      have hsmooth :=
        (chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g x X i) y₀ hy₀_target
      exact (hsmooth.contDiffAt htarget_nhd).differentiableAt (by simp)
    have hfY : DifferentiableAt ℝ
        (fun y => chartCoeffOnE (I := I) x Y i y * chartDensityOnE (I := I) g x y) y₀ := by
      have hsmooth :=
        (chartCoeffOnE_mul_chartDensityOnE_contDiffOn (I := I) g x Y i) y₀ hy₀_target
      exact (hsmooth.contDiffAt htarget_nhd).differentiableAt (by simp)
    rw [fderiv_fun_add hfX hfY]
    rfl
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
              (fun y => chartCoeffOnE (I := I) x (X + Y) i y *
                chartDensityOnE (I := I) g x y) y₀) =
          ∑ i : Fin (Module.finrank ℝ E),
            (CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
              (fun y => chartCoeffOnE (I := I) x X i y *
                chartDensityOnE (I := I) g x y) y₀ +
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
              (fun y => chartCoeffOnE (I := I) x Y i y *
                chartDensityOnE (I := I) g x y) y₀) from
        Finset.sum_congr rfl (fun i _ => hpartial_split i)]
  rw [Finset.sum_add_distrib]
  rw [add_div]

end CalabiYau.DivergenceTheorem
