module

public import CalabiYau.Geometry.Kahler.Basic
public import CalabiYau.Geometry.Riemannian.Metric.Basic

/-!
# The Riemannian metric associated to a Kähler form

For the convention `ω = i ∑ gⱼₖ̄ dzⱼ ∧ dżₖ`, the associated real metric is
`g(u, v) = ω(u, Jv)`. In complex dimension one, `i dz ∧ dż = 2 dx ∧ dy`
and this gives `g = 2 (dx² + dy²)`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Bundle Bornology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The smooth Riemannian metric associated to a Kähler form, with convention
`g(u, v) = ω(u, Jv)`. -/
private theorem finiteDimensional_continuousMultilinearTwo
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (E [×2]→L[ℝ] ℝ) := by
  let : FiniteDimensional ℝ (E →L[ℝ] ℝ) := inferInstance
  let : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let e : (E [×2]→L[ℝ] ℝ) ≃ₗᵢ[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
    (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ).trans
      (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ))
  exact FiniteDimensional.of_injective e.toLinearEquiv.toLinearMap e.injective

private noncomputable def innerAtCLM (ω₀ : KahlerForm n M) (x : M) :
    TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x →L[ℝ]
      TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x →L[ℝ] ℝ := by
  let E := EuclideanSpace ℂ (Fin n)
  letI : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := {
    norm_smul_le a b := by
      change ‖a • (show E from b)‖ ≤ ‖a‖ * ‖(show E from b)‖
      exact norm_smul_le a (show E from b) }
  let e := CalabiYau.tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(ℝ, E)) x
  let J := EuclideanSpace.complexStructure n
  let eCLM := e.toContinuousLinearMap
  let JCLM := J.comp eCLM
  let β : ContinuousMultilinearMap ℝ
      (fun _ : Fin 2 => TangentSpace 𝓘(ℝ, E) x) ℝ :=
    (ω₀ x).toContinuousMultilinearMap.compContinuousLinearMap
      (fun i => if i = 0 then eCLM else JCLM)
  exact (continuousMultilinearCurryFin1 ℝ (TangentSpace 𝓘(ℝ, E) x)
      (TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ))
    ((continuousMultilinearCurryRightEquiv' ℝ 1
      (TangentSpace 𝓘(ℝ, E) x) ℝ) β)

private theorem innerAtCLM_apply (ω₀ : KahlerForm n M) (x : M)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) :
    ω₀.innerAtCLM x v w = ω₀.innerAt x v w := by
  simp only [innerAtCLM, continuousMultilinearCurryFin1_apply,
    continuousMultilinearCurryRightEquiv_apply',
    ContinuousMultilinearMap.compContinuousLinearMap_apply, KahlerForm.innerAt]
  have hvec :
      (fun i : Fin 2 =>
        (if i = 0 then
          (CalabiYau.tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).toContinuousLinearMap
        else (EuclideanSpace.complexStructure n).comp
          (CalabiYau.tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).toContinuousLinearMap)
          ((Fin.snoc (Fin.snoc (0 : Fin 0 →
            TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) v) w :
              Fin 2 → TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) i)) =
        ![CalabiYau.tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x v,
          EuclideanSpace.complexStructure n
            (CalabiYau.tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x w)] := by
    funext i
    fin_cases i <;> simp
  rw [hvec]
  rfl

private theorem modelInnerAt_isVonNBounded (ω₀ : KahlerForm n M) (x : M) :
    IsVonNBounded ℝ {z : EuclideanSpace ℂ (Fin n) |
      (ω₀ x) ![z, EuclideanSpace.complexStructure n z] < 1} := by
  let E := EuclideanSpace ℂ (Fin n)
  let α := ω₀ x
  let J := EuclideanSpace.complexStructure n
  let q : E → ℝ := fun z => α ![z, J z]
  let s : Set E := Metric.sphere 0 1
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  have hqs : Continuous q := by
    dsimp [q]
    exact α.toContinuousMultilinearMap.cont.comp (by fun_prop)
  have hcompact : IsCompact s := by
    dsimp [s]
    exact isCompact_sphere 0 1
  by_cases hn : n = 0
  · subst n
    have hsub : Subsingleton E := by infer_instance
    let : Subsingleton E := hsub
    exact IsVonNBounded.of_subsingleton
  · have hne : s.Nonempty := by
      rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
      let e : E := EuclideanSpace.single 0 (1 : ℂ)
      have he : e ≠ 0 := by
        intro h
        have hh := congrArg (fun z : E => z 0) h
        norm_num [e, EuclideanSpace.single] at hh
      refine ⟨‖e‖⁻¹ • e, ?_⟩
      have hnorm : ‖‖e‖⁻¹ • e‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg e))]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr he)
      change dist (‖e‖⁻¹ • e) 0 = 1
      rw [dist_zero_right]
      exact hnorm
    obtain ⟨z₀, hz₀s, hmin⟩ := hcompact.exists_isMinOn hne hqs.continuousOn
    have hz₀ne : z₀ ≠ 0 := by
      intro hz
      subst z₀
      simp [s] at hz₀s
    have hz₀pos : 0 < q z₀ := by
      exact (ω₀.isPositive x).2 z₀ hz₀ne
    have hscale (c : ℝ) (z : E) : q (c • z) = c ^ 2 * q z := by
      dsimp [q]
      have hJ : J (c • z) = c • J z := J.map_smul c z
      rw [hJ]
      have h := α.toContinuousMultilinearMap.map_smul_univ (fun _ : Fin 2 => c) ![z, J z]
      have hvec : (fun i : Fin 2 => c • ![z, J z] i) = ![c • z, c • J z] := by
        funext i
        fin_cases i <;> simp
      rw [← hvec]
      simpa [pow_two] using h
    have hqnorm (z : E) (hz : z ≠ 0) : q z ≥ q z₀ * ‖z‖ ^ 2 := by
      let u : E := ‖z‖⁻¹ • z
      have hu_norm : ‖u‖ = 1 := by
        dsimp [u]
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)
      have hu : u ∈ s := by
        simpa [s] using hu_norm
      have hminu := hmin hu
      have hscaleu := hscale (‖z‖⁻¹) z
      have hnorm : (‖z‖⁻¹) ^ 2 * ‖z‖ ^ 2 = 1 := by
        field_simp [norm_ne_zero_iff.mpr hz]
      change q z₀ ≤ q (‖z‖⁻¹ • z) at hminu
      rw [hscaleu] at hminu
      calc
        q z₀ * ‖z‖ ^ 2 ≤ ((‖z‖⁻¹) ^ 2 * q z) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hminu (sq_nonneg ‖z‖)
        _ = ((‖z‖⁻¹) ^ 2 * ‖z‖ ^ 2) * q z := by ring
        _ = q z := by rw [hnorm]; simp
    rw [NormedSpace.isVonNBounded_iff']
    refine ⟨Real.sqrt (1 / q z₀), ?_⟩
    intro z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · have h := hqnorm z hz0
      have hzbound : q z < 1 := hz
      have hnormsq : ‖z‖ ^ 2 < 1 / q z₀ := by
        apply (lt_div_iff₀ hz₀pos).2
        nlinarith [h, hzbound, sq_nonneg ‖z‖]
      have hsqrtNorm := Real.sqrt_le_sqrt hnormsq.le
      rw [Real.sqrt_sq (norm_nonneg z)] at hsqrtNorm
      simpa using hsqrtNorm

private theorem innerAt_isVonNBounded (ω₀ : KahlerForm n M) (x : M) :
    IsVonNBounded ℝ {v : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x |
      ω₀.innerAt x v v < 1} := by
  let e := CalabiYau.tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x
  let S : Set (EuclideanSpace ℂ (Fin n)) :=
    {z | (ω₀ x) ![z, EuclideanSpace.complexStructure n z] < 1}
  have hS : IsVonNBounded ℝ S := modelInnerAt_isVonNBounded ω₀ x
  have himage : e.symm '' S =
      {v : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x |
        ω₀.innerAt x v v < 1} := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [S, e, KahlerForm.innerAt] using hz
    · intro hv
      refine ⟨e v, ?_, e.symm_apply_apply v⟩
      simpa [S, e, KahlerForm.innerAt] using hv
  rw [← himage]
  exact hS.image e.symm.toContinuousLinearMap

private theorem innerAtCLM_section_contMDiff (ω₀ : KahlerForm n M) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      ((𝓘(ℝ, EuclideanSpace ℂ (Fin n))).prod
        𝓘(ℝ, EuclideanSpace ℂ (Fin n) →L[ℝ]
          EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (EuclideanSpace ℂ (Fin n) →L[ℝ]
        EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x →L[ℝ]
          TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x →L[ℝ] ℝ)
        x (ω₀.innerAtCLM x)) := by
  let E := EuclideanSpace ℂ (Fin n)
  let I := 𝓘(ℝ, E)
  let formToMetricCLM : (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ]
      (E →L[ℝ] E →L[ℝ] ℝ) := by
    letI : FiniteDimensional ℝ E := inferInstance
    letI : FiniteDimensional ℝ (E [×2]→L[ℝ] ℝ) :=
      finiteDimensional_continuousMultilinearTwo E
    let J := EuclideanSpace.complexStructure n
    let pre : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
      ContinuousMultilinearMap.compContinuousLinearMapL
        (fun i => if i = 0 then ContinuousLinearMap.id ℝ E else J)
    let curry : (E [×2]→L[ℝ] ℝ) ≃ₗᵢ[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
      (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ).trans
        (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] ℝ))
    exact curry.toContinuousLinearMap.comp <|
      pre.comp (ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ)
  have formToMetricCLM_apply (α : E [⋀^Fin 2]→L[ℝ] ℝ) (v w : E) :
      formToMetricCLM α v w = α ![v, EuclideanSpace.complexStructure n w] := by
    simp [formToMetricCLM]
    apply congrArg α
    funext i
    fin_cases i <;> simp
  have hcoords (x₀ y : M)
      (hy : y ∈ (extChartAt I x₀).source) :
      ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun b => TangentSpace I b →L[ℝ] ℝ) x₀ y x₀ y (ω₀.innerAtCLM y) =
        formToMetricCLM (ω₀.toFormField.chartRep x₀ (extChartAt I x₀ y)) := by
    have hT : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      rw [← extChartAt_source (I := I) x₀]
      exact hy
    have hR : y ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀).baseSet := by
      simp
    ext v w
    rw [inCoordinates_apply_eq₂ (h₁x := hT) (h₂x := hT) (h₃x := hR)]
    rw [innerAtCLM_apply]
    rw [← Trivialization.symmL_apply (R := ℝ)
        (e := trivializationAt E (TangentSpace I) x₀) (b := y) hT v,
      ← Trivialization.symmL_apply (R := ℝ)
        (e := trivializationAt E (TangentSpace I) x₀) (b := y) hT w]
    rw [TangentBundle.symmL_trivializationAt_eq_core (by
      rw [← extChartAt_source (I := I) x₀]
      exact hy)]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]
    rw [KahlerForm.innerAt, formToMetricCLM_apply]
    simp only [FormField.chartRep, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [(extChartAt I x₀).left_inv hy]
    change (ω₀ y) ![
        tangentCoordChange I x₀ y y v,
        EuclideanSpace.complexStructure n (tangentCoordChange I x₀ y y w)] =
      (ω₀ y) (tangentCoordChange I x₀ y y ∘ ![v,
        EuclideanSpace.complexStructure n w])
    have hyBoth : y ∈ (extChartAt I x₀).source ∩ (extChartAt I y).source :=
      ⟨hy, mem_extChartAt_source y⟩
    have hJ : tangentCoordChange I x₀ y y (EuclideanSpace.complexStructure n w) =
        EuclideanSpace.complexStructure n (tangentCoordChange I x₀ y y w) := by
      change tangentCoordChange I x₀ y y (Complex.I • w) =
        Complex.I • tangentCoordChange I x₀ y y w
      exact tangentCoordChange_I_smul
        (E := E) (M := M) (x := x₀) (y := y) (z := y) hyBoth w
    have hvec : ![tangentCoordChange I x₀ y y v,
        EuclideanSpace.complexStructure n (tangentCoordChange I x₀ y y w)] =
        tangentCoordChange I x₀ y y ∘ ![v, EuclideanSpace.complexStructure n w] := by
      funext i
      fin_cases i
      · rfl
      · exact hJ.symm
    rw [hvec]
  intro x₀
  rw [contMDiffAt_section]
  let profile := fun z => formToMetricCLM (ω₀.toFormField.chartRep x₀ z)
  have hchart : ContMDiffAt I (𝓘(ℝ, E)) ∞ (extChartAt I x₀) x₀ :=
    contMDiffAt_extChartAt
  have hz : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (mem_extChartAt_source x₀)
  have hprof : ContDiffAt ℝ ∞ profile (extChartAt I x₀ x₀) :=
    (formToMetricCLM.contDiff.comp_contDiffOn (ω₀.isSmooth x₀)).contDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hz)
  have hcomp : ContMDiffAt I (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (profile ∘ extChartAt I x₀) x₀ :=
    hprof.contMDiffAt.comp x₀ hchart
  have heq : (fun x => (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x₀
        ⟨x, ω₀.innerAtCLM x⟩).2) =ᶠ[𝓝 x₀]
      (profile ∘ extChartAt I x₀) := by
    filter_upwards [(isOpen_extChartAt_source (I := I) x₀).mem_nhds
      (mem_extChartAt_source x₀)] with x hx
    change (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x₀
        ⟨x, ω₀.innerAtCLM x⟩).2 = profile (extChartAt I x₀ x)
    rw [hom_trivializationAt_apply]
    exact hcoords x₀ x hx
  exact hcomp.congr_of_eventuallyEq heq

@[no_expose]
noncomputable def toRiemannianMetric (ω₀ : KahlerForm n M) :
    CalabiYau.SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M := by
  let E := EuclideanSpace ℂ (Fin n)
  refine {
    inner := fun x => ω₀.innerAtCLM x
    symm := ?_
    pos := ?_
    isVonNBounded := ?_
    contMDiff := ?_ }
  · intro x v w
    rw [innerAtCLM_apply, innerAtCLM_apply]
    exact ω₀.innerAt_symm x v w
  · intro x v hv
    rw [innerAtCLM_apply]
    exact ω₀.innerAt_pos x hv
  · intro x
    simpa only [innerAtCLM_apply] using innerAt_isVonNBounded ω₀ x
  · exact innerAtCLM_section_contMDiff ω₀

/-- Pointwise evaluation of the real metric induced by a Kähler form. -/
theorem toRiemannianMetric_inner_apply (ω₀ : KahlerForm n M) (x : M)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) :
    ω₀.toRiemannianMetric.inner x v w = ω₀.innerAt x v w := by
  change ω₀.innerAtCLM x v w = ω₀.innerAt x v w
  exact innerAtCLM_apply ω₀ x v w

end KahlerForm