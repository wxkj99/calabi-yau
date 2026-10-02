module

public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Geometry.Kahler.Riemannian.Volume
public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient.ChartWeakDerivative.RealifiedMetricEllipticity

/-!
# Local derivative energy from Kähler gradient energy

On a compact subset of a real chart, the positive Kähler density and the inverse real metric are
uniformly coercive. Thus vanishing Kähler gradient energy forces each real coordinate derivative
of the chart pullback to vanish in local Euclidean `L²`. The constants in the comparison need not
be normalized to one: in complex dimension one the convention `ω = i dz ∧ dż` gives the real
metric `2 I` and `|∂f|² = |∇ₑ f|² / 4`. In dimension zero there is no coordinate index and hence no
instance of the conclusion to prove.
-/

@[expose] public section

open scoped Manifold ContDiff ENNReal Topology
open MeasureTheory Filter

namespace KahlerForm

private noncomputable def chartLocal_complexChartBasisVolume (n : ℕ) : ℝ≥0∞ :=
  MeasureTheory.volume
    (↑(CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))).parallelepiped :
      Set (EuclideanSpace ℂ (Fin n)))

/-- The canonical complex chart volume pushes forward to a finite positive scalar multiple of
real Euclidean volume under realification. The scalar is retained because the chart-model basis is
not assumed to have unit parallelepiped measure. -/
private theorem chartLocal_map_toEuclidean_complexVolume (n : ℕ) :
    Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      chartLocal_complexChartBasisVolume n • (MeasureTheory.volume : Measure
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := by
  classical
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))
  have hvol : (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      chartLocal_complexChartBasisVolume n • b.addHaar := by
    rw [MeasureTheory.Measure.addHaarMeasure_unique (MeasureTheory.volume) b.parallelepiped]
    rw [Module.Basis.addHaar, chartLocal_complexChartBasisVolume]
  rw [hvol, MeasureTheory.Measure.map_smul]
  congr 1
  have hmap : Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n))) b.addHaar =
      (b.map (toEuclidean (E := EuclideanSpace ℂ (Fin n))).toLinearEquiv).addHaar :=
    Module.Basis.map_addHaar b (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
  rw [hmap]
  have hcancel : b.map (toEuclidean (E := EuclideanSpace ℂ (Fin n))).toLinearEquiv =
      (EuclideanSpace.basisFun (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) ℝ).toBasis := by
    refine Module.Basis.eq_of_apply_eq ?_
    intro i
    have hb_i : (EuclideanSpace.basisFun (Fin (Module.finrank ℝ
        (EuclideanSpace ℂ (Fin n)))) ℝ).toBasis i = EuclideanSpace.single i (1 : ℝ) := by
      simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply
        (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))]
    rw [Module.Basis.map_apply, CalabiYau.Tensor.Coordinates.chartModelBasis_apply, hb_i]
    simp
  rw [hcancel]
  exact (EuclideanSpace.basisFun (Fin (Module.finrank ℝ
    (EuclideanSpace ℂ (Fin n)))) ℝ).addHaar_eq_volume

private lemma chartLocal_volume_density_lower_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K,
      c ≤ ω₀.volumeDensityInChart a
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y) := by
  classical
  let c₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let g : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) → ℝ :=
    fun y ↦ ω₀.volumeDensityInChart a
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)
  have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart a z).det) c₀.target := by
    simp_rw [Matrix.det_apply]
    exact continuousOn_finsetSum Finset.univ fun σ _ ↦
      continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun i _ ↦
        (ω₀.contDiffOn_metricInChart a (σ i) i).continuousOn
  have hden : ContinuousOn (ω₀.volumeDensityInChart a) c₀.target := by
    change ContinuousOn (fun z ↦ (2 : ℝ) ^ n * (ω₀.metricInChart a z).det.re) c₀.target
    have hre : ContinuousOn (fun z ↦ (ω₀.metricInChart a z).det.re) c₀.target :=
      Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _)
    exact continuousOn_const.mul hre
  have hKtarget : K ⊆
      (toEuclidean (E := EuclideanSpace ℂ (Fin n))) '' c₀.target := by
    simpa [Sobolev.Chart.chartTargetEuclid, c₀] using hK
  have hcont : ContinuousOn g K := by
    apply hden.comp (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm.continuous.continuousOn
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hKtarget hy
    have hsymm : (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y = z := by
      rw [← hzy]
      exact (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm_apply_apply z
    simpa [g, hsymm] using hz
  by_cases hne : K.Nonempty
  · obtain ⟨y₀, hy₀, hmin⟩ := hKcompact.exists_isMinOn hne hcont
    have hpos : 0 < g y₀ := by
      apply ω₀.volumeDensityInChart_pos a
      obtain ⟨z, hz, hzy⟩ := hKtarget hy₀
      have hsymm : (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y₀ = z := by
        rw [← hzy]
        exact (toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm_apply_apply z
      have hz' : z ∈ c₀.target := by simpa [c₀] using hz
      rw [hsymm]
      exact hz'
    refine ⟨g y₀ / 2, by linarith, ?_⟩
    intro y hy
    have hle : g y₀ ≤ g y := hmin hy
    dsimp [g] at hpos ⊢
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    exact (hne ⟨y, hy⟩).elim

private theorem riemannian_inner_sq_le
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    (g.inner x u v) ^ 2 ≤ g.inner x u u * g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · have hc : 0 < g.inner x v v := g.pos x v hv
    let t : ℝ := g.inner x u v / g.inner x v v
    have hnonneg : 0 ≤ g.inner x (u - t • v) (u - t • v) :=
      CalabiYau.metric_inner_self_nonneg g x (u - t • v)
    have hexpand : g.inner x (u - t • v) (u - t • v) =
        g.inner x u u - t * g.inner x v u - t * g.inner x u v +
          t ^ 2 * g.inner x v v := by
      simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul]
      ring
    rw [hexpand] at hnonneg
    rw [g.symm x v u] at hnonneg
    dsimp [t] at hnonneg
    have hcne : g.inner x v v ≠ 0 := ne_of_gt hc
    field_simp [hcne] at hnonneg
    nlinarith

private theorem chartCoordinate_fderiv_eq_partialDeriv
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (a : M) (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).target)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) :
    fderiv ℝ
      (fun w => u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm w)))
      ((toEuclidean (E := EuclideanSpace ℂ (Fin n))) z)
      (EuclideanSpace.single i 1) =
    CalabiYau.Tensor.Coordinates.partialDeriv i
      (CalabiYau.Tensor.Coordinates.scalarOnE
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) a u) z := by
  let e := toEuclidean (E := EuclideanSpace ℂ (Fin n))
  let S := CalabiYau.Tensor.Coordinates.scalarOnE
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) a u
  have hS : DifferentiableAt ℝ S z := by
    have hcont := CalabiYau.Tensor.Coordinates.scalarOnE_contDiffOn
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) a hu
    have hAt : ContDiffAt ℝ ∞ S z :=
      (hcont z hz).contDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) a).mem_nhds hz)
    exact hAt.differentiableAt (by norm_num)
  have hS' : DifferentiableAt ℝ S (e.symm (e z)) := by
    simpa [e] using hS
  have hcomp := fderiv_comp (f := e.symm) (g := S) (x := e z)
    hS' e.symm.differentiableAt
  change fderiv ℝ (S ∘ e.symm) (e z) (EuclideanSpace.single i 1) = _
  rw [hcomp]
  have hlin : fderiv ℝ (e.symm : _ → _) (e z) = e.symm.toContinuousLinearMap :=
    e.symm.toContinuousLinearMap.fderiv
  rw [hlin]
  simp only [e.symm_apply_apply, ContinuousLinearMap.comp_apply]
  change fderiv ℝ S z (e.symm (EuclideanSpace.single i 1)) = _
  rw [CalabiYau.Tensor.Coordinates.partialDeriv,
    CalabiYau.Tensor.Coordinates.chartModelBasis_apply]

private theorem map_toEuclidean_volume_eq_positive_smul (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      ENNReal.ofReal c •
        (MeasureTheory.volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := by
  let E := EuclideanSpace ℂ (Fin n)
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e := toEuclidean (E := E)
  let o : E ≃ₗᵢ[ℝ] V := (stdOrthonormalBasis ℝ E).repr
  let L : V ≃ₗ[ℝ] V := o.symm.toLinearEquiv.trans e.toLinearEquiv
  have hdet : LinearMap.det (L : V →ₗ[ℝ] V) ≠ 0 := by
    calc
      LinearMap.det (L : V →ₗ[ℝ] V) = (LinearEquiv.det L : ℝ) :=
        (LinearEquiv.coe_det L).symm
      _ ≠ 0 := Units.ne_zero _
  have hL : Measure.map (L : V →ₗ[ℝ] V)
      (MeasureTheory.volume : Measure V) =
        ENNReal.ofReal |(LinearMap.det (L : V →ₗ[ℝ] V))⁻¹| •
          (MeasureTheory.volume : Measure V) :=
    MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (μ := (MeasureTheory.volume : Measure V)) hdet
  have ho : MeasurePreserving o
      (MeasureTheory.volume : Measure E) (MeasureTheory.volume : Measure V) :=
    o.measurePreserving
  have heq : (e : E → V) = fun z => L (o z) := by
    funext z
    simp [L, o]
  have hmap : Measure.map e (MeasureTheory.volume : Measure E) =
      ENNReal.ofReal |(LinearMap.det (L : V →ₗ[ℝ] V))⁻¹| •
        (MeasureTheory.volume : Measure V) := by
    rw [heq]
    have hcomp : Measure.map (fun z : E => L (o z))
        (MeasureTheory.volume : Measure E) =
        (Measure.map o (MeasureTheory.volume : Measure E)).map L := by
      exact (Measure.map_map
        (μ := (MeasureTheory.volume : Measure E)) (f := o) (g := L)
        (LinearMap.continuous_of_finiteDimensional (L : V →ₗ[ℝ] V)).measurable
        o.continuous.measurable).symm
    rw [hcomp, ho.map_eq]
    exact hL
  refine ⟨|(LinearMap.det (L : V →ₗ[ℝ] V))⁻¹|, ?_, ?_⟩
  · exact abs_pos.mpr (inv_ne_zero hdet)
  · simpa [E, V, e] using hmap

private theorem chartLocal_volumeDensity_lower_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M)
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K,
      c ≤ ω₀.volumeDensityInChart a
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y) := by
  let e := toEuclidean (E := EuclideanSpace ℂ (Fin n))
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let Z := e.symm '' K
  have hdet : ContinuousOn (fun z : EuclideanSpace ℂ (Fin n) =>
      (ω₀.metricInChart a z).det) c.target := by
    classical
    simp_rw [Matrix.det_apply]
    exact continuousOn_finsetSum Finset.univ fun σ _ =>
      continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun j _ =>
        (ω₀.contDiffOn_metricInChart a (σ j) j).continuousOn
  have hden : ContinuousOn (ω₀.volumeDensityInChart a) c.target := by
    unfold volumeDensityInChart
    have hre : ContinuousOn
        (fun z : EuclideanSpace ℂ (Fin n) =>
          RCLike.re ((ω₀.metricInChart a z).det)) c.target := by
      exact Complex.continuous_re.continuousOn.comp hdet (fun _ _ => Set.mem_univ _)
    exact continuousOn_const.mul hre
  have hZcompact : IsCompact Z := hKcompact.image e.symm.continuous
  have hZsubset : Z ⊆ c.target := by
    rintro z ⟨y, hy, rfl⟩
    have hy' : y ∈ Sobolev.Chart.chartTargetEuclid
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a := hK hy
    change y ∈ e '' c.target at hy'
    rcases hy' with ⟨w, hw, hwy⟩
    rw [← hwy]
    simpa using hw
  have hdenZ : ContinuousOn (ω₀.volumeDensityInChart a) Z := hden.mono hZsubset
  by_cases hKne : K.Nonempty
  · have hZne : Z.Nonempty := by
      rcases hKne with ⟨y, hy⟩
      exact ⟨e.symm y, y, hy, rfl⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hZcompact.exists_isMinOn hZne hdenZ
    have hz₀target : z₀ ∈ c.target := hZsubset hz₀
    refine ⟨ω₀.volumeDensityInChart a z₀,
      ω₀.volumeDensityInChart_pos a hz₀target, ?_⟩
    intro y hy
    exact hmin ⟨y, hy, rfl⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro y hy
    exact (hKne ⟨y, hy⟩).elim

private theorem chartVolume_lintegral_coordinate
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (x : M) {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂ω₀.chartVolume x =
      ∫⁻ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
        ENNReal.ofReal (ω₀.volumeDensityInChart x z) *
          f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let μ : Measure (EuclideanSpace ℂ (Fin n)) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict c.target
  let d : EuclideanSpace ℂ (Fin n) → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart x z)
  have hsymm : AEMeasurable c.symm μ := by
    exact (continuousOn_extChartAt_symm x).aemeasurable
      (isOpen_extChartAt_target x).measurableSet
  have hden : ContinuousOn (ω₀.volumeDensityInChart x) c.target := by
    change ContinuousOn
      (fun z ↦ (2 : ℝ) ^ n * (ω₀.metricInChart x z).det.re) c.target
    have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart x z).det) c.target := by
      classical
      simp_rw [Matrix.det_apply]
      exact continuousOn_finsetSum Finset.univ fun σ _ ↦
        continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun j _ ↦
          (ω₀.contDiffOn_metricInChart x (σ j) j).continuousOn
    exact continuousOn_const.mul
      (Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _))
  have hdcont : ContinuousOn d c.target :=
    ENNReal.continuous_ofReal.continuousOn.comp hden (fun _ _ ↦ Set.mem_univ _)
  have hd : AEMeasurable d μ := hdcont.aemeasurable (isOpen_extChartAt_target x).measurableSet
  have hsymm' : AEMeasurable c.symm (μ.withDensity d) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous μ d)
  have hfg : AEMeasurable (fun z ↦ f (c.symm z)) μ :=
    (hf.aemeasurable : AEMeasurable f (μ.map c.symm)).comp_aemeasurable hsymm
  calc
    ∫⁻ y, f y ∂ω₀.chartVolume x = ∫⁻ z, f (c.symm z) ∂μ.withDensity d := by
      rw [chartVolume, MeasureTheory.lintegral_map' hf.aemeasurable hsymm']
    _ = ∫⁻ z, d z * f (c.symm z) ∂μ :=
      MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀ hd hfg
    _ = ∫⁻ z in c.target, d z * f (c.symm z) ∂MeasureTheory.volume := rfl

private theorem chartLocal_derivative_sq_integral_le_chart_energy_of_density_lower_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M)
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))
    (hDensity : ∃ c : ℝ, 0 < c ∧ ∀ y ∈ K,
      c ≤ ω₀.volumeDensityInChart a
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f' : M → ℝ),
        (hf' : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f') →
        ∫ y in K,
        (fderiv ℝ
          (fun z => f' ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
          (EuclideanSpace.single i 1)) ^ 2
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) ≤
        C * ∫ y in K,
          ω₀.gradNormSq f'
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
              ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) *
            ω₀.volumeDensityInChart a
              ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := by
  obtain ⟨C₀, hC₀, hpoint⟩ :=
    chartLocal_derivative_sq_le_gradNormSq ω₀ a K hKcompact hK i
  obtain ⟨c, hc, hcK⟩ := hDensity
  refine ⟨C₀ / c, div_nonneg hC₀ hc.le, ?_⟩
  intro f' hf'
  let e := toEuclidean (E := EuclideanSpace ℂ (Fin n))
  let cchart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let d : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) → ℝ :=
    fun y => fderiv ℝ
      (fun z => f' (cchart.symm (e.symm z))) y (EuclideanSpace.single i 1)
  let q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) → ℝ :=
    fun y => ω₀.gradNormSq f' (cchart.symm (e.symm y)) *
      ω₀.volumeDensityInChart a (e.symm y)
  have hpointwise : ∀ y ∈ K, d y ^ 2 ≤ C₀ / c * q y := by
    intro y hy
    have hgrad := hpoint f' hf' y hy
    have hgrad_nonneg : 0 ≤ ω₀.gradNormSq f' (cchart.symm (e.symm y)) :=
      ω₀.gradNormSq_nonneg f' _
    have hden := hcK y hy
    dsimp [d, q, e, cchart]
    calc
      _ ≤ C₀ * ω₀.gradNormSq f'
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) := hgrad
      _ ≤ C₀ / c * (ω₀.gradNormSq f'
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) *
          ω₀.volumeDensityInChart a
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) := by
        have hratio : 1 ≤ ω₀.volumeDensityInChart a
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y) / c := by
          apply (le_div_iff₀ hc).2
          simpa using hden
        have hmul : ω₀.gradNormSq f'
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
              ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) ≤
            ω₀.gradNormSq f'
              ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
                ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) *
              (ω₀.volumeDensityInChart a
                ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y) / c) := by
          calc
            _ = _ * 1 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hratio hgrad_nonneg
        calc
          _ = C₀ * ω₀.gradNormSq f'
              ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
                ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hmul hC₀
          _ = _ := by ring
  have hdcont : ContinuousOn d K := by
    let E := EuclideanSpace ℂ (Fin n)
    let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    let I := 𝓘(ℝ, E)
    let e := toEuclidean (E := E)
    let cchart := extChartAt I a
    let S := CalabiYau.Tensor.Coordinates.scalarOnE (I := I) a f'
    let F : V → ℝ := fun y => S (e.symm y)
    let U : Set V := e.symm ⁻¹' cchart.target
    have hUopen : IsOpen U := by
      dsimp [U, cchart]
      exact (isOpen_extChartAt_target (I := I) a).preimage e.symm.continuous
    have hKU : K ⊆ U := by
      intro y hy
      have hy' := hK hy
      change y ∈ e '' cchart.target at hy'
      rcases hy' with ⟨z, hz, hzy⟩
      have hz' : e.symm y = z := by
        calc
          e.symm y = e.symm (e z) := (congrArg e.symm hzy).symm
          _ = z := e.symm_apply_apply z
      change e.symm y ∈ cchart.target
      rw [hz']
      exact hz
    have hS : ContDiffOn ℝ ∞ S cchart.target :=
      CalabiYau.Tensor.Coordinates.scalarOnE_contDiffOn (I := I) a hf'
    have he : ContDiffOn ℝ ∞ (fun y : V => e.symm y) U := by
      exact e.symm.contDiff.contDiffOn
    have hF : ContDiffOn ℝ ∞ F U := by
      dsimp [F]
      exact hS.comp he (by intro y hy; exact hy)
    have htop : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
      change ((⊤ : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact le_rfl
    have hfd : ContDiffOn ℝ ∞ (fderiv ℝ F) U :=
      hF.fderiv_of_isOpen hUopen htop
    have hcomp : ContinuousOn
        (fun y : V => fderiv ℝ F y (EuclideanSpace.single i 1)) K := by
      have hD : ContDiffOn ℝ ∞
          (fun y : V => fderiv ℝ F y (EuclideanSpace.single i 1)) U :=
        hfd.clm_apply contDiffOn_const
      exact hD.continuousOn.mono hKU
    have hdeq : d = fun y : V => fderiv ℝ F y (EuclideanSpace.single i 1) := by
      funext y
      rfl
    rw [hdeq]
    exact hcomp
  have hqcont : ContinuousOn q K := by
    let e := toEuclidean (E := EuclideanSpace ℂ (Fin n))
    let cchart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
    have htarget : ∀ y ∈ K, e.symm y ∈ cchart.target := by
      intro y hy
      have hy' := hK hy
      change y ∈ e '' cchart.target at hy'
      rcases hy' with ⟨z, hz, hzy⟩
      have hz' : e.symm y = z := by
        calc
          e.symm y = e.symm (e z) := (congrArg e.symm hzy).symm
          _ = z := e.symm_apply_apply z
      rw [hz']
      exact hz
    have hdet : ContinuousOn (fun z : EuclideanSpace ℂ (Fin n) =>
        (ω₀.metricInChart a z).det) cchart.target := by
      classical
      simp_rw [Matrix.det_apply]
      exact continuousOn_finsetSum Finset.univ fun σ _ =>
        continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun j _ =>
          (ω₀.contDiffOn_metricInChart a (σ j) j).continuousOn
    have hden : ContinuousOn (ω₀.volumeDensityInChart a) cchart.target := by
      unfold volumeDensityInChart
      have hre : ContinuousOn
          (fun z : EuclideanSpace ℂ (Fin n) =>
            RCLike.re ((ω₀.metricInChart a z).det)) cchart.target := by
        exact Complex.continuous_re.continuousOn.comp hdet (fun _ _ => Set.mem_univ _)
      exact continuousOn_const.mul hre
    have hgrad : ContinuousOn (fun y => ω₀.gradNormSq f'
        (cchart.symm (e.symm y))) K := by
      have hgradAll : ContinuousOn (ω₀.gradNormSq f') Set.univ :=
        (ω₀.contMDiff_gradNormSq hf').continuous.continuousOn
      have hcoord : ContinuousOn (fun y => cchart.symm (e.symm y)) K := by
        exact (continuousOn_extChartAt_symm a).comp
          e.symm.continuous.continuousOn htarget
      exact hgradAll.comp hcoord (by intro y hy; simp)
    have hdenK : ContinuousOn (fun y => ω₀.volumeDensityInChart a (e.symm y)) K :=
      hden.comp e.symm.continuous.continuousOn htarget
    dsimp [q]
    exact hgrad.mul hdenK
  have hdint : IntegrableOn (fun y => d y ^ 2) K
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ
        (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := by
    exact (hdcont.pow 2).integrableOn_compact hKcompact
  have hRcont : ContinuousOn (fun y => C₀ / c * q y) K :=
    continuousOn_const.mul hqcont
  have hRint : IntegrableOn (fun y => C₀ / c * q y) K
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ
        (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := by
    exact hRcont.integrableOn_compact hKcompact
  have hmono : ∀ᵐ y ∂((MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K),
      d y ^ 2 ≤ C₀ / c * q y := by
    filter_upwards [ae_restrict_mem hKcompact.measurableSet] with y hy
    exact hpointwise y hy
  change ∫ y, d y ^ 2 ∂((MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K) ≤
    C₀ / c * ∫ y, q y ∂((MeasureTheory.volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K)
  calc
    ∫ y, d y ^ 2 ∂((MeasureTheory.volume : Measure
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K) ≤
      ∫ y, C₀ / c * q y ∂((MeasureTheory.volume : Measure
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K) :=
      integral_mono_ae hdint hRint hmono
    _ = C₀ / c * ∫ y, q y ∂((MeasureTheory.volume : Measure
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K) := by
      rw [integral_const_mul]

private theorem chartLocal_weighted_energy_le_global_energy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M)
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f' : M → ℝ),
        (hf' : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f') →
        ∫ y in K,
          ω₀.gradNormSq f'
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
              ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) *
            ω₀.volumeDensityInChart a
              ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) ≤
        C * ∫ x, ω₀.gradNormSq f' x ∂ω₀.volume := by
  obtain ⟨jac, hjac, hmapVolume⟩ := map_toEuclidean_volume_eq_positive_smul n
  let E := EuclideanSpace ℂ (Fin n)
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let e := toEuclidean (E := E)
  let eMeas : E ≃ᵐ V := e.toHomeomorph.toMeasurableEquiv
  refine ⟨jac⁻¹, inv_nonneg.mpr hjac.le, ?_⟩
  intro f' hf'
  let cchart := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a
  let q : V → ℝ := fun y =>
    ω₀.gradNormSq f' (cchart.symm (e.symm y)) * ω₀.volumeDensityInChart a (e.symm y)
  let F : E → ℝ := fun z =>
    ω₀.gradNormSq f' (cchart.symm z) * ω₀.volumeDensityInChart a z
  let Z : Set E := e.symm '' K
  have hZimage : e '' Z = K := by
    simp [Z, e]
  have hZcompact : IsCompact Z := hKcompact.image e.symm.continuous
  let J : ℝ≥0∞ := ENNReal.ofReal jac
  have hJreal : J.toReal = jac := by
    simp [J, ENNReal.toReal_ofReal, hjac.le]
  have heq : (eMeas : E → V) = e := rfl
  have hmapMeas : Measure.map eMeas (MeasureTheory.volume : Measure E) =
      J • (MeasureTheory.volume : Measure V) := by
    rw [heq]
    simpa [J] using hmapVolume
  have hPres : MeasurePreserving eMeas
      (MeasureTheory.volume : Measure E) (J • (MeasureTheory.volume : Measure V)) :=
    ⟨eMeas.measurable, hmapMeas⟩
  have hchange : jac * ∫ y in K, q y
        ∂(MeasureTheory.volume : Measure V) =
      ∫ z in Z, F z ∂(MeasureTheory.volume : Measure E) := by
    have hraw := hPres.setIntegral_image_emb eMeas.measurableEmbedding q Z
    rw [heq] at hraw
    rw [hZimage, Measure.restrict_smul, integral_smul_measure,
      hJreal, smul_eq_mul] at hraw
    have hcongr : ∫ z in Z, q (e z) ∂(MeasureTheory.volume : Measure E) =
        ∫ z in Z, F z ∂(MeasureTheory.volume : Measure E) := by
      exact setIntegral_congr_fun hZcompact.measurableSet (fun z hz => by
        simp [q, F, e, cchart])
    exact hraw.trans hcongr
  let source := (chartAt E a).source
  let target := cchart.target
  let g : M → ℝ := fun x => ω₀.gradNormSq f' x
  let gENN : M → ℝ≥0∞ := fun x => ENNReal.ofReal (g x)
  have hgCont : Continuous g := (ω₀.contMDiff_gradNormSq hf').continuous
  have hgENN : Measurable gENN := ENNReal.measurable_ofReal.comp hgCont.measurable
  have hsourceMeas : MeasurableSet source := (chartAt E a).open_source.measurableSet
  have htargetMeas : MeasurableSet target :=
    (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) a).measurableSet
  have hsymmSource {z : E} (hz : z ∈ target) : cchart.symm z ∈ source := by
    have hs := cchart.map_target hz
    rw [extChartAt_source] at hs
    exact hs
  let gcut : M → ℝ≥0∞ := source.indicator gENN
  have hgcut : Measurable gcut := hgENN.indicator hsourceMeas
  have hchartSet :
      ∫⁻ x in source, gENN x ∂ω₀.chartVolume a =
        ∫⁻ z in target,
          ENNReal.ofReal (ω₀.volumeDensityInChart a z) * gENN (cchart.symm z)
          ∂(MeasureTheory.volume : Measure E) := by
    have hformula := chartVolume_lintegral_coordinate ω₀ a hgcut
    rw [lintegral_indicator hsourceMeas] at hformula
    calc
      _ = ∫⁻ z in target,
          ENNReal.ofReal (ω₀.volumeDensityInChart a z) * gcut (cchart.symm z)
          ∂(MeasureTheory.volume : Measure E) := hformula
      _ = _ := setLIntegral_congr_fun htargetMeas (fun z hz => by
        simp [gcut, hsymmSource hz])
  have hchartGlobal :
      ∫⁻ x in source, gENN x ∂ω₀.chartVolume a =
        ∫⁻ x in source, gENN x ∂ω₀.volume := by
    rw [ω₀.chartVolume_restrict_chartSource_eq_volume_restrict a]
  have hsourceGlobal :
      ∫⁻ x in source, gENN x ∂ω₀.volume ≤ ∫⁻ x, gENN x ∂ω₀.volume := by
    rw [← lintegral_indicator hsourceMeas gENN]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ source <;> simp [hx, gENN]
  have hcoordGlobal :
      ∫⁻ z in target,
        ENNReal.ofReal (ω₀.volumeDensityInChart a z) * gENN (cchart.symm z)
        ∂(MeasureTheory.volume : Measure E) ≤
      ∫⁻ x, gENN x ∂ω₀.volume := by
    calc
      _ = ∫⁻ x in source, gENN x ∂ω₀.chartVolume a := hchartSet.symm
      _ = _ := hchartGlobal
      _ ≤ _ := hsourceGlobal
  have hZsubset : Z ⊆ target := by
    rintro z ⟨y, hy, rfl⟩
    have hy' := hK hy
    change y ∈ e '' target at hy'
    rcases hy' with ⟨w, hw, hwy⟩
    have hz' : e.symm y = w := by
      calc
        e.symm y = e.symm (e w) := (congrArg e.symm hwy).symm
        _ = w := e.symm_apply_apply w
    rw [hz']
    exact hw
  have hdet : ContinuousOn (fun z : E => (ω₀.metricInChart a z).det) target := by
    classical
    simp_rw [Matrix.det_apply]
    exact continuousOn_finsetSum Finset.univ fun σ _ =>
      continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun j _ =>
        (ω₀.contDiffOn_metricInChart a (σ j) j).continuousOn
  have hdensity : ContinuousOn (ω₀.volumeDensityInChart a) target := by
    unfold volumeDensityInChart
    have hre : ContinuousOn (fun z : E => (ω₀.metricInChart a z).det.re) target :=
      Complex.continuous_re.continuousOn.comp hdet (fun _ _ => Set.mem_univ _)
    exact continuousOn_const.mul hre
  have hgradAll : ContinuousOn g Set.univ := hgCont.continuousOn
  have hcoord : ContinuousOn (fun z : E => cchart.symm z) Z :=
    (continuousOn_extChartAt_symm a).mono hZsubset
  have hFcont : ContinuousOn F Z := by
    dsimp [F]
    exact (hgradAll.comp hcoord (by intro z hz; simp)).mul (hdensity.mono hZsubset)
  have hFnonneg : 0 ≤ᵐ[(MeasureTheory.volume : Measure E).restrict Z] F := by
    apply (ae_restrict_iff' hZcompact.measurableSet).2
    exact Filter.Eventually.of_forall fun z hz =>
      mul_nonneg (ω₀.gradNormSq_nonneg f' (cchart.symm z))
        (le_of_lt (ω₀.volumeDensityInChart_pos a (hZsubset hz)))
  have hFint : IntegrableOn F Z (MeasureTheory.volume : Measure E) :=
    hFcont.integrableOn_compact hZcompact
  have hFofReal : ENNReal.ofReal (∫ z in Z, F z ∂(MeasureTheory.volume : Measure E)) =
      ∫⁻ z in Z, ENNReal.ofReal (F z) ∂(MeasureTheory.volume : Measure E) := by
    exact ofReal_integral_eq_lintegral_ofReal hFint hFnonneg
  have hFtarget : ∀ z ∈ target,
      ENNReal.ofReal (F z) =
        ENNReal.ofReal (ω₀.volumeDensityInChart a z) * gENN (cchart.symm z) := by
    intro z hz
    have hden : 0 ≤ ω₀.volumeDensityInChart a z :=
      (ω₀.volumeDensityInChart_pos a hz).le
    have hF : F z = ω₀.volumeDensityInChart a z * g (cchart.symm z) := by
      simp [F, g]
      ring
    rw [hF, ENNReal.ofReal_mul hden]
  have hFlin : ENNReal.ofReal (∫ z in Z, F z ∂(MeasureTheory.volume : Measure E)) ≤
      ∫⁻ x, gENN x ∂ω₀.volume := by
    calc
      _ = ∫⁻ z in Z, ENNReal.ofReal (F z) ∂(MeasureTheory.volume : Measure E) := hFofReal
      _ ≤ ∫⁻ z in target, ENNReal.ofReal (F z) ∂(MeasureTheory.volume : Measure E) :=
        lintegral_mono_set hZsubset
      _ = ∫⁻ z in target,
            ENNReal.ofReal (ω₀.volumeDensityInChart a z) * gENN (cchart.symm z)
              ∂(MeasureTheory.volume : Measure E) :=
        setLIntegral_congr_fun htargetMeas (fun z hz => hFtarget z hz)
      _ ≤ _ := hcoordGlobal
  have hglobalInt : Integrable g ω₀.volume :=
    hgCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hglobalNonneg : 0 ≤ᵐ[ω₀.volume] g :=
    Filter.Eventually.of_forall fun x => ω₀.gradNormSq_nonneg f' x
  have hglobalOfReal : ENNReal.ofReal (∫ x, g x ∂ω₀.volume) =
      ∫⁻ x, gENN x ∂ω₀.volume :=
    ofReal_integral_eq_lintegral_ofReal hglobalInt hglobalNonneg
  have hcomplexLe : ∫ z in Z, F z ∂(MeasureTheory.volume : Measure E) ≤
      ∫ x, g x ∂ω₀.volume := by
    apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hglobalNonneg)).mp
    exact hFlin.trans_eq hglobalOfReal.symm
  have hprod : (∫ y in K, q y ∂(MeasureTheory.volume : Measure V)) * jac ≤
      ∫ x, g x ∂ω₀.volume := by
    calc
      _ = jac * ∫ y in K, q y ∂(MeasureTheory.volume : Measure V) := by ring
      _ ≤ _ := hchange.trans_le hcomplexLe
  have hlocalLe : ∫ y in K, q y ∂(MeasureTheory.volume : Measure V) ≤
      jac⁻¹ * ∫ x, g x ∂ω₀.volume := by
    have hdiv : ∫ y in K, q y ∂(MeasureTheory.volume : Measure V) ≤
        (∫ x, g x ∂ω₀.volume) / jac :=
      (le_div_iff₀ hjac).2 hprod
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  simpa [q, g, cchart, e] using hlocalLe

/-- Local coercivity of the chart expression: on a compact subset of a chart, the square of any
one real coordinate derivative is controlled in Euclidean integral by the global Kähler gradient
energy. This is the compact-set ellipticity and volume-density comparison; its constants may depend
on the chart, compact set, and coordinate index. -/
private theorem chartLocal_derivative_sq_integral_le_grad_energy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M)
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f' : M → ℝ),
        (hf' : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f') →
        ∫ y in K,
        (fderiv ℝ
          (fun z => f' ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
          (EuclideanSpace.single i 1)) ^ 2
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) ≤
        C * ∫ x, ω₀.gradNormSq f' x ∂ω₀.volume := by
  obtain ⟨C₁, hC₁, hlocal⟩ :=
    chartLocal_derivative_sq_integral_le_chart_energy_of_density_lower_bound
      ω₀ a K hKcompact hK i
      (chartLocal_volume_density_lower_bound ω₀ a K hKcompact hK)
  obtain ⟨C₂, hC₂, hglobal⟩ :=
    chartLocal_weighted_energy_le_global_energy ω₀ a K hKcompact hK
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro f' hf'
  calc
    _ ≤ C₁ * ∫ y in K,
          ω₀.gradNormSq f'
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
              ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) *
            ω₀.volumeDensityInChart a
              ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := hlocal f' hf'
    _ ≤ C₁ * (C₂ * ∫ x, ω₀.gradNormSq f' x ∂ω₀.volume) :=
      mul_le_mul_of_nonneg_left (hglobal f' hf') hC₁
    _ = C₁ * C₂ * ∫ x, ω₀.gradNormSq f' x ∂ω₀.volume := by ring

private theorem chartLocal_derivative_memLp
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) :
    MemLp
      (fun y => fderiv ℝ
        (fun z => f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
          ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
        (EuclideanSpace.single i 1))
      (ENNReal.ofReal 2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ
        (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let E := EuclideanSpace ℂ (Fin n)
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let c := extChartAt I a
  let Ω := Sobolev.Chart.chartTargetEuclid (I := I) (M := M) a
  let μ := (MeasureTheory.volume : Measure V).restrict K
  have : IsFiniteMeasure μ := by
    dsimp [μ]
    rw [MeasureTheory.isFiniteMeasure_restrict]
    exact hKcompact.measure_lt_top.ne
  have hΩopen : IsOpen Ω := by
    simpa [Ω] using Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) a
  have hKΩ : K ⊆ Ω := hK
  let F : V → ℝ := fun y => f (c.symm ((toEuclidean (E := E)).symm y))
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F Ω := by
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (f ∘ c.symm) c.target := by
      exact (hf.contMDiffOn (s := Set.univ)).comp
        (contMDiffOn_extChartAt_symm a) (fun _ _ => Set.mem_univ _)
    have hcomp' : ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ c.symm) c.target := hcomp.contDiffOn
    change ContDiffOn ℝ (⊤ : ℕ∞)
      ((f ∘ c.symm) ∘ (toEuclidean (E := E)).symm) Ω
    apply hcomp'.comp ((toEuclidean (E := E)).symm.contDiff.contDiffOn)
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hz' : z ∈ c.target := by simpa [c] using hz
    have hyz : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]
      exact (toEuclidean (E := E)).symm_apply_apply z
    rw [hyz]
    exact hz'
  have hDcontOn : ContinuousOn
      (fun y => fderiv ℝ F y (EuclideanSpace.single i 1)) Ω :=
    (hF.continuousOn_fderiv_of_isOpen hΩopen (by simp)).clm_apply continuous_const.continuousOn
  have hDcont : ContinuousOn
      (fun y => fderiv ℝ F y (EuclideanSpace.single i 1)) K := hDcontOn.mono hKΩ
  have hDae : AEStronglyMeasurable
      (fun y => fderiv ℝ F y (EuclideanSpace.single i 1)) μ :=
    hDcont.aestronglyMeasurable_of_isCompact hKcompact hKcompact.measurableSet
  have hnormcont : ContinuousOn
      (fun y => ‖fderiv ℝ F y (EuclideanSpace.single i 1)‖) K :=
    continuous_norm.comp_continuousOn hDcont
  obtain ⟨C, hC⟩ := (hKcompact.image_of_continuousOn hnormcont).bddAbove
  have hbound : ∀ᵐ y ∂μ,
      ‖fderiv ℝ F y (EuclideanSpace.single i 1)‖ ≤ max C 0 := by
    filter_upwards [ae_restrict_mem hKcompact.measurableSet] with y hy
    exact le_trans (hC ⟨y, hy, rfl⟩) (le_max_left _ _)
  have hmem : MemLp (fun y => fderiv ℝ F y (EuclideanSpace.single i 1))
      (ENNReal.ofReal 2) μ := MemLp.of_bound hDae (max C 0) hbound
  simpa [F, μ, I, E, V, c] using hmem

private theorem chartLocal_l2_tendsto_of_sq_integral_tendsto
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (g : ℕ → α → ℝ)
    (hg : ∀ k, MemLp (g k) (ENNReal.ofReal 2) μ)
    (hSq : Tendsto (fun k => ∫ x, (g k x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (g k) (ENNReal.ofReal 2) μ) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun k => Real.sqrt (∫ x, (g k x) ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp hSq
  have hp0 : (ENNReal.ofReal 2) ≠ 0 := by norm_num
  have hptop : (ENNReal.ofReal 2) ≠ (⊤ : ℝ≥0∞) := by norm_num
  have hEq : ∀ k, eLpNorm (g k) (ENNReal.ofReal 2) μ =
      ENNReal.ofReal (Real.sqrt (∫ x, (g k x) ^ 2 ∂μ)) := by
    intro k
    have h := (hg k).eLpNorm_eq_integral_rpow_norm hp0 hptop
    have htwo : ((ENNReal.ofReal 2).toReal) = (2 : ℝ) := by norm_num
    rw [htwo] at h
    convert h using 1 ; simp [Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
  have hcont := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  convert hcont using 1
  · funext k
    exact hEq k
  · norm_num

private theorem chartLocal_derivative_l2_tendsto_of_integral_sq_le_energy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (f : ℕ → M → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f k))
    (hEnergy : Tendsto
      (fun k => ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume) atTop (𝓝 0))
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))
    (hcoercive : ∃ C : ℝ, 0 ≤ C ∧ ∀ k,
      ∫ y in K,
        (fderiv ℝ
          (fun z => f k ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
          (EuclideanSpace.single i 1)) ^ 2
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ
            (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) ≤
        C * ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume) :
    Tendsto
      (fun k => eLpNorm
        (fun y => fderiv ℝ
          (fun z => f k ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
          (EuclideanSpace.single i 1))
        (ENNReal.ofReal 2)
        ((MeasureTheory.volume : Measure (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := hcoercive
  let μ := (MeasureTheory.volume : Measure (EuclideanSpace ℝ
    (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K
  let D : ℕ → EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) → ℝ := fun k y =>
    fderiv ℝ
      (fun z => f k ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
      (EuclideanSpace.single i 1)
  let Q : ℕ → ℝ := fun k => ∫ y, (D k y) ^ 2 ∂μ
  have hQnonneg : ∀ k, 0 ≤ Q k := by
    intro k
    dsimp [Q]
    exact integral_nonneg fun y => sq_nonneg _
  have hboundQ : ∀ k,
      Q k ≤ C * ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume := by
    intro k
    simpa [Q, D, μ] using hbound k
  have hCenergy : Tendsto
      (fun k => C * ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hEnergy)
  have hSq : Tendsto Q atTop (𝓝 0) :=
    squeeze_zero hQnonneg hboundQ hCenergy
  have hDmem : ∀ k, MemLp (D k) (ENNReal.ofReal 2) μ := by
    intro k
    simpa [D, μ] using chartLocal_derivative_memLp (f k) (hf k) a K hKcompact hK i
  simpa [D, μ] using chartLocal_l2_tendsto_of_sq_integral_tendsto μ D hDmem hSq

/-- If the global Kähler gradient energies of a smooth sequence tend to zero, each real coordinate
derivative of its chart pullback tends to zero in Euclidean `L²` on every compact subset of the
chart target. The assertion uses the realification of the complex chart, so it includes both real
coordinate directions for each complex coordinate. -/
theorem chartLocal_derivative_l2_tendsto_of_grad_energy_tendsto
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (f : ℕ → M → ℝ)
    (hf : ∀ k, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f k))
    (hEnergy : Tendsto
      (fun k => ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume) atTop (𝓝 0))
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) :
    Tendsto
      (fun k => eLpNorm
        (fun y => fderiv ℝ
          (fun z => f k ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
          (EuclideanSpace.single i 1))
        (ENNReal.ofReal 2)
        ((MeasureTheory.volume : Measure (EuclideanSpace ℝ
          (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))).restrict K))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hcoercive⟩ :=
    chartLocal_derivative_sq_integral_le_grad_energy ω₀ a K hKcompact hK i
  apply chartLocal_derivative_l2_tendsto_of_integral_sq_le_energy
    ω₀ f hf hEnergy a K hKcompact hK i
  refine ⟨C, hC, ?_⟩
  intro k
  exact hcoercive (f k) (hf k)

end KahlerForm
