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

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

omit [Module.Finite ℝ E] in
theorem sum_tangentSectionAction_partitionOfUnity_eq_zero
    {ι : Type*} {s : Set M}
    (rho : SmoothPartitionOfUnity ι I M s)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx : x ∈ interior s) :
    ∑ i ∈ rho.fintsupport x, tangentSectionAction X (rho i) x = 0 := by
  have hd (i : ι) (_ : i ∈ rho.fintsupport x) : MDifferentiableAt I 𝓘(Real) (rho i) x :=
    (rho i).contMDiff.mdifferentiableAt (by simp)
  rw [← tangentSectionAction_finset_sum X (rho.fintsupport x) (fun i => (rho i : M → Real)) x hd]
  have heq : (∑ i ∈ rho.fintsupport x, (rho i : M → Real)) =ᶠ[𝓝 x]
      (fun _ : M => (1 : Real)) := by
    filter_upwards [rho.eventually_finsupport_subset x, mem_interior_iff_mem_nhds.mp hx] with y hy hys
    simpa only [Finset.sum_apply] using rho.sum_finsupport' y hys hy
  change mfderiv I 𝓘(Real) (∑ i ∈ rho.fintsupport x, (rho i : M → Real)) x (X x) = 0
  rw [heq.mfderiv_eq]
  change mfderiv I 𝓘(Real) (fun _ : M => (1 : Real)) x (X x) = 0
  rw [mfderiv_const]
  rfl

omit [Module.Finite ℝ E] in
theorem tsum_tangentSectionAction_partitionOfUnity_eq_zero
    {ι : Type*} {s : Set M}
    (rho : SmoothPartitionOfUnity ι I M s)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx : x ∈ interior s) :
    ∑' i, tangentSectionAction X (rho i) x = 0 := by
  classical
  rw [tsum_eq_sum (s := rho.fintsupport x)]
  · exact sum_tangentSectionAction_partitionOfUnity_eq_zero rho X hx
  · intro i hi
    have hxi : x ∉ tsupport (rho i : M → Real) :=
      fun h => hi ((rho.mem_fintsupport_iff x i).mpr h)
    change mfderiv I 𝓘(Real) (rho i : M → Real) x (X x) = 0
    rw [(notMem_tsupport_iff_eventuallyEq.mp hxi).mfderiv_eq]
    change mfderiv I 𝓘(Real) (fun _ : M => (0 : Real)) x (X x) = 0
    rw [mfderiv_const]
    rfl

omit [Module.Finite ℝ E] in
theorem tangentSectionAction_const
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (c : ℝ) (x : M) :
    tangentSectionAction (I := I) X (fun _ => c) x = 0 := by
  unfold tangentSectionAction
  rw [mfderiv_const]
  rfl

omit [Module.Finite ℝ E] in
theorem tangentSectionAction_zero_fun
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) X (fun _ : M => (0 : ℝ)) x = 0 :=
  tangentSectionAction_const (I := I) X 0 x

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
private lemma pou_tsum_eq_finset_sum_eventually
    (ρ : SmoothPartitionOfUnity M I M univ) (x : M) :
    (fun y : M => ∑' α : M, (ρ α : M → ℝ) y) =ᶠ[𝓝 x]
      (fun y : M => ∑ α ∈ ρ.fintsupport x, (ρ α : M → ℝ) y) := by
  classical
  filter_upwards [ρ.eventually_finsupport_subset x] with y hy
  refine tsum_eq_sum ?_
  intro α hα
  by_contra hne
  have hα_finsupp : α ∈ ρ.finsupport y := by
    rw [ρ.mem_finsupport]
    exact hne
  exact hα (hy hα_finsupp)

omit [Module.Finite ℝ E] in
theorem tangentSectionAction_pou_tsum_eq_zero
    (ρ : SmoothPartitionOfUnity M I M univ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    tangentSectionAction (I := I) X (fun y : M => ∑' α : M, (ρ α : M → ℝ) y) x = 0 := by
  classical
  have h_eq_one_at_x : ∀ᶠ y in 𝓝 x, (∑' α : M, (ρ α : M → ℝ) y) = 1 := by
    classical
    filter_upwards [ρ.eventually_finsupport_subset x] with y hy
    have h1 : (∑' α : M, (ρ α : M → ℝ) y) =
        ∑ α ∈ ρ.fintsupport x, (ρ α : M → ℝ) y := by
      refine tsum_eq_sum ?_
      intro α hα
      by_contra hne
      have hα_finsupp : α ∈ ρ.finsupport y := by
        rw [ρ.mem_finsupport]
        exact hne
      exact hα (hy hα_finsupp)
    rw [h1]
    exact ρ.sum_finsupport' y (mem_univ y) hy
  have h_eq : (fun y : M => ∑' α : M, (ρ α : M → ℝ) y) =ᶠ[𝓝 x]
      (fun _ : M => (1 : ℝ)) := h_eq_one_at_x
  unfold tangentSectionAction
  rw [Filter.EventuallyEq.mfderiv_eq h_eq]
  rw [mfderiv_const]
  rfl

theorem divergence_g_pou_tsum [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    (ρ : SmoothPartitionOfUnity M I M univ)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ x : M, divergenceG (I := I) g X x =
      ∑' α : M, divergenceG (I := I) g
        (smoothSmul (I := I) (ρ α : M → ℝ) (ρ α).contMDiff X) x := by
  intro x
  classical
  set S : Finset M := ρ.fintsupport x with hS_def
  have h_tsum_eq_sum :
      (∑' α : M, divergenceG (I := I) g
          (smoothSmul (I := I) (ρ α : M → ℝ) (ρ α).contMDiff X) x) =
        ∑ α ∈ S, divergenceG (I := I) g
          (smoothSmul (I := I) (ρ α : M → ℝ) (ρ α).contMDiff X) x := by
    refine tsum_eq_sum ?_
    intro α hα
    have hxnotin : x ∉ tsupport (ρ α : M → ℝ) := by
      intro h
      apply hα
      rw [ρ.mem_fintsupport_iff]
      exact h
    rw [divergence_g_smoothSmul (I := I) g (ρ α : M → ℝ) (ρ α).contMDiff X x]
    have hραx : (ρ α : M → ℝ) x = 0 := by
      by_contra hne
      exact hxnotin (subset_tsupport _ hne)
    have htsa_zero : tangentSectionAction (I := I) X (ρ α : M → ℝ) x = 0 := by
      unfold tangentSectionAction
      have h_open : IsOpen (tsupport (ρ α : M → ℝ))ᶜ :=
        (isClosed_tsupport _).isOpen_compl
      have hev : (ρ α : M → ℝ) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [h_open.mem_nhds hxnotin] with y hy
        by_contra hne
        exact hy (subset_tsupport _ hne)
      rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_const]
      rfl
    rw [hραx, htsa_zero, zero_mul, add_zero]
  rw [h_tsum_eq_sum]
  have h_each : ∀ α ∈ S,
      divergenceG (I := I) g
        (smoothSmul (I := I) (ρ α : M → ℝ) (ρ α).contMDiff X) x =
        (ρ α : M → ℝ) x * divergenceG (I := I) g X x +
          tangentSectionAction (I := I) X (ρ α : M → ℝ) x := by
    intro α _
    exact divergence_g_smoothSmul (I := I) g (ρ α : M → ℝ) (ρ α).contMDiff X x
  rw [Finset.sum_congr rfl h_each]
  rw [Finset.sum_add_distrib]
  rw [show (∑ α ∈ S, (ρ α : M → ℝ) x * divergenceG (I := I) g X x) =
        (∑ α ∈ S, (ρ α : M → ℝ) x) * divergenceG (I := I) g X x from
      (Finset.sum_mul _ _ _).symm]
  rw [ρ.sum_finsupport' x (mem_univ x)
        (ρ.finsupport_subset_fintsupport x)]
  rw [one_mul]
  have hsum_action : ∑ α ∈ S,
      tangentSectionAction (I := I) X (ρ α : M → ℝ) x = 0 :=
    sum_tangentSectionAction_partitionOfUnity_eq_zero ρ X (by simp)
  rw [hsum_action]
  ring

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

theorem divergence_g_zero [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    ∀ x : M, divergenceG (I := I) g
      (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x = 0 := by
  intro x
  classical
  rw [divergence_g_def, localDivergence_def]
  have hbase : x ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact mem_chart_source H x
  set y₀ : E := extChartAt I x x with hy₀_def
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hy₀_target : y₀ ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have htarget_open : IsOpen (extChartAt I x).target := isOpen_extChartAt_target (I := I) x
  have htarget_nhd : (extChartAt I x).target ∈ 𝓝 y₀ := htarget_open.mem_nhds hy₀_target
  have hchartCoeff_zero : ∀ z ∈ (trivializationAt E (TangentSpace I) x).baseSet,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeff (I := I) x
          (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i z = 0 := by
    intro z hz i
    classical
    set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
      trivializationAt E (TangentSpace I) x
    have hzero : ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) z : E) = 0 := by
      change ((0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) z : E) = (0 : E)
      rfl
    have h0 : (T ⟨z, (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) z⟩).2 = 0 := by
      have h := (T.linear ℝ hz).map_zero
      change (T ⟨z, (0 : TangentSpace I z)⟩).2 = 0
      exact h
    unfold chartCoeff
    rw [h0]
    simp
  have hchartCoeffOnE_zero : ∀ y ∈ (extChartAt I x).target,
      ∀ i : Fin (Module.finrank ℝ E),
        chartCoeffOnE (I := I) x
          (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i y = 0 := by
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
    exact hchartCoeff_zero _ hsymm_base i
  have hpartial_zero : ∀ i : Fin (Module.finrank ℝ E),
      CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
        (fun y => chartCoeffOnE (I := I) x
          (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i y *
          chartDensityOnE (I := I) g x y) y₀ = 0 := by
    intro i
    unfold CalabiYau.Tensor.Coordinates.partialDeriv
    have hev : (fun y => chartCoeffOnE (I := I) x
            (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i y *
            chartDensityOnE (I := I) g x y) =ᶠ[𝓝 y₀]
        (fun _ : E => (0 : ℝ)) := by
      filter_upwards [htarget_nhd] with y hy
      rw [hchartCoeffOnE_zero y hy i]
      ring
    rw [hev.fderiv_eq]
    rw [show (fun _ : E => (0 : ℝ)) = Function.const E (0 : ℝ) from rfl, fderiv_const]
    rfl
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            CalabiYau.Tensor.Coordinates.partialDeriv (E := E) i
              (fun y => chartCoeffOnE (I := I) x
                (0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) i y *
                chartDensityOnE (I := I) g x y) y₀) = 0 from
        Finset.sum_eq_zero (fun i _ => hpartial_zero i)]
  rw [zero_div]

end CalabiYau.DivergenceTheorem
