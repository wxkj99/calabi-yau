module

public import CalabiYau.MongeAmpere.Operator
import CalabiYau.Geometry.Complex.Forms.Positive
import CalabiYau.MongeAmpere.Estimates.C0.SubsolutionIteration

public section

open scoped Manifold ContDiff Interval ComplexOrder MatrixOrder
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
private theorem interval_product_integrable_of_continuous_bounded
    (ω₀ : KahlerForm n M) {f : ℝ → M → ℝ} (hf : Continuous (Function.uncurry f))
    (hbound : ∃ C : ℝ, ∀ s ∈ Set.uIoc (0 : ℝ) 1, ∀ x,
      f s x ∈ Set.Icc (-C) C) :
    MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod ω₀.volume) := by
  let μ := (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod ω₀.volume
  obtain ⟨C, hC⟩ := hbound
  have hvol : MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) < ⊤ := by
    have hsubset : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
      simpa using (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 1))
    calc
      MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) ≤ MeasureTheory.volume (Set.Icc 0 1) :=
        MeasureTheory.measure_mono hsubset
      _ = ENNReal.ofReal (1 - 0) := by rw [Real.volume_Icc]
      _ < ⊤ := ENNReal.ofReal_lt_top
  let : Fact (MeasureTheory.volume (Set.uIoc (0 : ℝ) 1) < ⊤) := ⟨hvol⟩
  have : MeasureTheory.IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hfmeas : AEMeasurable (Function.uncurry f) μ := hf.measurable.aemeasurable
  have hset : MeasurableSet {z : ℝ × M | Function.uncurry f z ∈ Set.Icc (-C) C} :=
    isClosed_Icc.measurableSet.preimage hf.measurable
  have hboundAE : ∀ᵐ z ∂μ, Function.uncurry f z ∈ Set.Icc (-C) C := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hs
    exact Filter.Eventually.of_forall fun x ↦ hC s hs x
  exact MeasureTheory.Integrable.of_mem_Icc (-C) C hfmeas hboundAE

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
private theorem interval_product_integrable_of_continuous
    (ω₀ : KahlerForm n M) {f : ℝ → M → ℝ} (hf : Continuous (Function.uncurry f)) :
    MeasureTheory.Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)).prod ω₀.volume) := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ :=
    (hcompact.image_of_continuousOn hf.continuousOn).isBounded.exists_norm_le
  have hsubset : Set.uIoc (0 : ℝ) 1 ⊆ Set.Icc 0 1 := by
    simpa using (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 1))
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1, ∀ x,
      f s x ∈ Set.Icc (-C) C := by
    intro s hs x
    have hs' := hsubset hs
    have himage : Function.uncurry f (s, x) ∈
        Function.uncurry f '' (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
      ⟨(s, x), ⟨hs', Set.mem_univ x⟩, rfl⟩
    have hnorm := hC (f s x) himage
    have habs : |f s x| ≤ C := by simpa [Real.norm_eq_abs] using hnorm
    exact abs_le.mp habs
  exact interval_product_integrable_of_continuous_bounded ω₀ hf ⟨C, hbound⟩

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
private theorem interval_integral_swap (ω₀ : KahlerForm n M) {f : ℝ → M → ℝ}
    (hf : Continuous (Function.uncurry f)) :
    (∫ s in (0 : ℝ)..1, ∫ x, f s x ∂ω₀.volume) =
      ∫ x, ∫ s in (0 : ℝ)..1, f s x ∂MeasureTheory.volume ∂ω₀.volume := by
  exact MeasureTheory.intervalIntegral_integral_swap
    (interval_product_integrable_of_continuous ω₀ hf)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
private theorem integral_weighted_mongeAmpere_segment
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (g : M → ℝ)
    (hF : Continuous (Function.uncurry fun (s : ℝ) (x : M) =>
      g x * (ContinuousAlternatingMap.relDet (ω₀ x)
          (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) *
        ContinuousAlternatingMap.relTrace
          (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) (mddbar n φ x)))) :
    ∫ x, g x * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume =
      ∫ s in (0 : ℝ)..1, ∫ x,
        g x * (ContinuousAlternatingMap.relDet (ω₀ x)
            (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) *
          ContinuousAlternatingMap.relTrace
            (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) (mddbar n φ x))
        ∂ω₀.volume ∂MeasureTheory.volume := by
  let F : ℝ → M → ℝ := fun (s : ℝ) (x : M) =>
    g x * (ContinuousAlternatingMap.relDet (ω₀ x)
        (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) *
      ContinuousAlternatingMap.relTrace
        (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) (mddbar n φ x))
  have hpoint : ∀ x, g x * (ω₀.mongeAmpere φ x - 1) =
      ∫ s in (0 : ℝ)..1, F s x ∂MeasureTheory.volume := by
    intro x
    rw [mongeAmpere_sub_one_eq_integral hφ x]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    have hclamp : max 0 (min 1 s) = s := by
      rw [min_eq_right hs01.2, max_eq_right hs01.1]
    simp [F, hclamp]
  calc
    ∫ x, g x * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume =
        ∫ x, ∫ s in (0 : ℝ)..1, F s x ∂MeasureTheory.volume ∂ω₀.volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ s in (0 : ℝ)..1, ∫ x, F s x ∂ω₀.volume ∂MeasureTheory.volume :=
      (interval_integral_swap ω₀ (by simpa [F] using hF)).symm

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem continuous_coeffMatrix :
    Continuous (ContinuousAlternatingMap.coeffMatrix :
      (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
  have hEval (v : Fin 2 → EuclideanSpace ℂ (Fin n)) :
      Continuous (fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ => α v) := by
    change Continuous (fun α => ContinuousAlternatingMap.toContinuousMultilinearMap α v)
    exact (continuous_eval_const v).comp
      ContinuousAlternatingMap.continuous_toContinuousMultilinearMap
  apply continuous_matrix
  intro j k
  simp only [ContinuousAlternatingMap.coeffMatrix, Matrix.of_apply]
  let v₁ : Fin 2 → EuclideanSpace ℂ (Fin n) :=
    ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]
  let v₂ : Fin 2 → EuclideanSpace ℂ (Fin n) :=
    ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]
  have h₁ : Continuous (fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ =>
      (α v₁ : ℂ)) :=
    Complex.continuous_ofReal.comp (hEval v₁)
  have h₂ : Continuous (fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ =>
      (α v₂ : ℂ)) :=
    Complex.continuous_ofReal.comp (hEval v₂)
  exact (h₁.sub (continuous_const.mul h₂)).div_const (2 : ℂ)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem continuousAt_relTrace_of_isPositive
    {α β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hα : α.IsPositive) :
    ContinuousAt (fun p : (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) ×
      (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) =>
        ContinuousAlternatingMap.relTrace p.1 p.2) (α, β) := by
  have hcoeff : Continuous (ContinuousAlternatingMap.coeffMatrix :
      (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
    exact continuous_coeffMatrix
  have hαcoeff : ContinuousAt (fun p => ContinuousAlternatingMap.coeffMatrix p.1) (α, β) :=
    hcoeff.continuousAt.comp continuousAt_fst
  have hβcoeff : ContinuousAt (fun p => ContinuousAlternatingMap.coeffMatrix p.2) (α, β) :=
    hcoeff.continuousAt.comp continuousAt_snd
  have hdet_pos : 0 < RCLike.re (ContinuousAlternatingMap.coeffMatrix α).det :=
    (RCLike.pos_iff.mp ((ContinuousAlternatingMap.isPositive_iff.mp hα).2.det_pos)).1
  have hdet_ne : (ContinuousAlternatingMap.coeffMatrix α).det ≠ 0 := by
    intro h
    rw [h] at hdet_pos
    norm_num at hdet_pos
  have hdetAt : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A.det)
      (ContinuousAlternatingMap.coeffMatrix α) := by
    fun_prop
  have hAdjAt : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate)
      (ContinuousAlternatingMap.coeffMatrix α) := by
    fun_prop
  have hinvDetAt : ContinuousAt
      (fun A : Matrix (Fin n) (Fin n) ℂ => Ring.inverse A.det)
      (ContinuousAlternatingMap.coeffMatrix α) := by
    have hinvAt : ContinuousAt (fun z : ℂ => Ring.inverse z)
        (ContinuousAlternatingMap.coeffMatrix α).det := by
      simpa only [Ring.inverse_eq_inv] using continuousAt_inv₀ hdet_ne
    exact hinvAt.comp hdetAt
  have hinvMatrix : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹)
      (ContinuousAlternatingMap.coeffMatrix α) := by
    change ContinuousAt
      (fun A : Matrix (Fin n) (Fin n) ℂ => Ring.inverse A.det • A.adjugate)
      (ContinuousAlternatingMap.coeffMatrix α)
    exact hinvDetAt.smul hAdjAt
  have hαcoeff : ContinuousAt ContinuousAlternatingMap.coeffMatrix α := hcoeff.continuousAt
  have hβcoeff : ContinuousAt ContinuousAlternatingMap.coeffMatrix β := hcoeff.continuousAt
  have hαcoeffPair : ContinuousAt (fun p => ContinuousAlternatingMap.coeffMatrix p.1)
      (α, β) := ContinuousAt.comp' hαcoeff continuousAt_fst
  have hinvCoeff : ContinuousAt (fun p => (ContinuousAlternatingMap.coeffMatrix p.1)⁻¹)
      (α, β) := ContinuousAt.comp' hinvMatrix hαcoeffPair
  have hβcoeffPair : ContinuousAt (fun p => ContinuousAlternatingMap.coeffMatrix p.2)
      (α, β) := ContinuousAt.comp' hβcoeff continuousAt_snd
  have hmul : ContinuousAt (fun p =>
      (ContinuousAlternatingMap.coeffMatrix p.1)⁻¹ * ContinuousAlternatingMap.coeffMatrix p.2)
      (α, β) := hinvCoeff.mul hβcoeffPair
  let mat := (ContinuousAlternatingMap.coeffMatrix α)⁻¹ *
    ContinuousAlternatingMap.coeffMatrix β
  have htrace : ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℂ => A.trace) mat := by
    fun_prop
  have hreal : ContinuousAt (fun z : ℂ => RCLike.re z) mat.trace :=
    RCLike.continuous_re.continuousAt
  have htracePair : ContinuousAt (fun p =>
      ((ContinuousAlternatingMap.coeffMatrix p.1)⁻¹ *
        ContinuousAlternatingMap.coeffMatrix p.2).trace) (α, β) :=
    ContinuousAt.comp' htrace hmul
  change ContinuousAt (fun p => RCLike.re
    ((ContinuousAlternatingMap.coeffMatrix p.1)⁻¹ *
      ContinuousAlternatingMap.coeffMatrix p.2).trace) (α, β)
  exact ContinuousAt.comp' hreal htracePair

private theorem continuousOn_path_metricInChart
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    ContinuousOn
      (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        (ω₀.perturb ((max 0 (min 1 p.1)) • φ)
          (hφ.smul (le_max_left _ _)
            (max_le_iff.mpr ⟨by norm_num, min_le_left (1 : ℝ) p.1⟩))).metricInChart x p.2)
      (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let τ : ℝ → ℝ := fun s => max 0 (min 1 s)
  have hτ : Continuous τ := by
    change Continuous (fun s : ℝ => max 0 (min 1 s))
    fun_prop
  have hτ₀ (s : ℝ) : 0 ≤ τ s := le_max_left _ _
  have hτ₁ (s : ℝ) : τ s ≤ 1 :=
    max_le_iff.mpr ⟨by norm_num, min_le_left (1 : ℝ) s⟩
  have hpot (s : ℝ) : ω₀.IsPotential (τ s • φ) := hφ.smul (hτ₀ s) (hτ₁ s)
  have hHsmul (s : ℝ) {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ c.target) :
      complexHessian ((τ s • φ) ∘ c.symm) z =
        τ s • complexHessian (φ ∘ c.symm) z := by
    change (ddbar ((τ s • φ) ∘ c.symm) z).coeffMatrix =
      τ s • (ddbar (φ ∘ c.symm) z).coeffMatrix
    rw [← chartRep_mddbar (hpot s).1 x hz, ← chartRep_mddbar hφ.1 x hz]
    rw [mddbar_smul hφ.1, FormField.chartRep_smul]
    simp [ContinuousAlternatingMap.coeffMatrix_smul]
  have hGcont : ContinuousOn (ω₀.metricInChart x) c.target := by
    refine continuousOn_pi' ?_
    intro j
    refine continuousOn_pi' ?_
    intro k
    exact (ω₀.contDiffOn_metricInChart x j k).continuousOn
  have hHcont : ContinuousOn
      (fun z => complexHessian (φ ∘ c.symm) z) c.target := by
    have hrep : ContDiffOn ℝ ∞ ((mddbar n φ).chartRep x) c.target :=
      isSmooth_mddbar hφ.1 x
    have hcoeff : Continuous
        (fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ => α.coeffMatrix) := by
      fun_prop [ContinuousAlternatingMap.coeffMatrix]
    have hc : ContinuousOn
        (fun z => ((mddbar n φ).chartRep x z).coeffMatrix) c.target :=
      hcoeff.continuousOn.comp hrep.continuousOn (fun _ _ => Set.mem_univ _)
    refine hc.congr ?_
    intro z hz
    change (ddbar (φ ∘ c.symm) z).coeffMatrix = _
    rw [← chartRep_mddbar hφ.1 x hz]
  have hG : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
      ω₀.metricInChart x p.2) (Set.univ ×ˢ c.target) :=
    hGcont.comp continuousOn_snd (fun _ hp => hp.2)
  have hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
      complexHessian (φ ∘ c.symm) p.2) (Set.univ ×ˢ c.target) :=
    hHcont.comp continuousOn_snd (fun _ hp => hp.2)
  have hτ' : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) => τ p.1)
      (Set.univ ×ˢ c.target) :=
    hτ.continuousOn.comp continuousOn_fst (fun _ _ => Set.mem_univ _)
  have hpath : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
      ω₀.metricInChart x p.2 + τ p.1 • complexHessian (φ ∘ c.symm) p.2)
      (Set.univ ×ˢ c.target) := hG.add (hτ'.smul hH)
  refine hpath.congr ?_
  rintro ⟨s, z⟩ ⟨_, hz⟩
  change (ω₀.perturb (τ s • φ) (hpot s)).metricInChart x z = _
  rw [KahlerForm.metricInChart_perturb (hpot s) x hz]
  rw [hHsmul s hz]

private theorem continuousOn_path_chart_integrand
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    ContinuousOn
      (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
        RCLike.re ((ω₀.perturb ((max 0 (min 1 p.1)) • φ)
          (hφ.smul (le_max_left _ _)
            (max_le_iff.mpr ⟨by norm_num, min_le_left (1 : ℝ) p.1⟩))).metricInChart x p.2).det /
        RCLike.re (ω₀.metricInChart x p.2).det *
          RCLike.re (((ω₀.perturb ((max 0 (min 1 p.1)) • φ)
            (hφ.smul (le_max_left _ _)
              (max_le_iff.mpr ⟨by norm_num, min_le_left (1 : ℝ) p.1⟩))).metricInChart x p.2)⁻¹ *
            complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) p.2).trace)
      (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let S : Set (ℝ × EuclideanSpace ℂ (Fin n)) := Set.univ ×ˢ c.target
  let τ : ℝ → ℝ := fun s => max 0 (min 1 s)
  let A : ℝ × EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun p => (ω₀.perturb (τ p.1 • φ)
      (hφ.smul (le_max_left _ _) (max_le_iff.mpr ⟨by norm_num, min_le_left 1 p.1⟩))).metricInChart x p.2
  have hA : ContinuousOn A S := by
    change ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
      (ω₀.perturb (τ p.1 • φ)
        (hφ.smul (le_max_left _ _) (max_le_iff.mpr ⟨by norm_num, min_le_left 1 p.1⟩))).metricInChart x p.2)
      (Set.univ ×ˢ c.target)
    simpa only [τ] using continuousOn_path_metricInChart ω₀ hφ x
  have hG : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
      ω₀.metricInChart x p.2) S := by
    have hg : ContinuousOn (ω₀.metricInChart x) c.target := by
      refine continuousOn_pi' ?_
      intro j
      refine continuousOn_pi' ?_
      intro k
      exact (ω₀.contDiffOn_metricInChart x j k).continuousOn
    exact hg.comp continuousOn_snd (fun _ hp => hp.2)
  have hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℂ (Fin n) =>
      complexHessian (φ ∘ c.symm) p.2) S := by
    have hh : ContinuousOn (fun z => complexHessian (φ ∘ c.symm) z) c.target := by
      have hrep : ContDiffOn ℝ ∞ ((mddbar n φ).chartRep x) c.target := isSmooth_mddbar hφ.1 x
      have hcoeff : Continuous
          (fun α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ => α.coeffMatrix) := by
        fun_prop [ContinuousAlternatingMap.coeffMatrix]
      have hc : ContinuousOn (fun z => ((mddbar n φ).chartRep x z).coeffMatrix) c.target :=
        hcoeff.continuousOn.comp hrep.continuousOn (fun _ _ => Set.mem_univ _)
      refine hc.congr ?_
      intro z hz
      change (ddbar (φ ∘ c.symm) z).coeffMatrix = _
      rw [← chartRep_mddbar hφ.1 x hz]
    exact hh.comp continuousOn_snd (fun _ hp => hp.2)
  have hdetA : ContinuousOn (fun p => (A p).det) S := by fun_prop
  have hAdj : ContinuousOn (fun p => (A p).adjugate) S := by fun_prop
  have hdetAinv : ContinuousOn (fun p => ((A p).det)⁻¹) S := by
    apply hdetA.inv₀
    rintro ⟨s, z⟩ ⟨_, hz⟩
    have hpos := (ω₀.perturb (τ s • φ)
      (hφ.smul (le_max_left _ _) (max_le_iff.mpr ⟨by norm_num, min_le_left 1 s⟩))).posDef_metricInChart x hz
    exact ((Matrix.isUnit_iff_isUnit_det (A (s, z))).1 (by simpa [A] using hpos.isUnit)).ne_zero
  have hAinv : ContinuousOn (fun p => (A p)⁻¹) S := by
    have h := hdetAinv.smul hAdj
    convert h using 1
    ext p i j
    simp [Matrix.inv_def]
  have htrace : ContinuousOn (fun p => RCLike.re ((A p)⁻¹ *
      complexHessian (φ ∘ c.symm) p.2).trace) S := by
    have hm := hAinv.mul hH
    fun_prop
  have hnum : ContinuousOn (fun p => RCLike.re (A p).det) S := by fun_prop
  have hden : ContinuousOn (fun p => RCLike.re (ω₀.metricInChart x p.2).det) S := by fun_prop
  have hdenNe : ∀ p ∈ S, RCLike.re (ω₀.metricInChart x p.2).det ≠ 0 := by
    rintro ⟨s, z⟩ ⟨_, hz⟩
    have h := ω₀.volumeDensityInChart_pos x hz
    dsimp [KahlerForm.volumeDensityInChart] at h
    exact ne_of_gt ((mul_pos_iff_of_pos_left (by positivity : 0 < (2 : ℝ) ^ n)).mp h)
  have hdenInv : ContinuousOn (fun p => (RCLike.re (ω₀.metricInChart x p.2).det)⁻¹) S :=
    hden.inv₀ hdenNe
  have hratio : ContinuousOn (fun p => RCLike.re (A p).det *
      (RCLike.re (ω₀.metricInChart x p.2).det)⁻¹) S := hnum.mul hdenInv
  change ContinuousOn (fun p =>
      RCLike.re (A p).det / RCLike.re (ω₀.metricInChart x p.2).det *
        RCLike.re ((A p)⁻¹ * complexHessian (φ ∘ c.symm) p.2).trace) S
  have hprod := hratio.mul htrace
  refine hprod.congr ?_
  intro p hp
  simp only [div_eq_mul_inv, Pi.mul_apply]

private theorem continuous_path_segment_integrand
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) :
    Continuous (Function.uncurry fun (s : ℝ) (y : M) =>
      ContinuousAlternatingMap.relDet (ω₀ y)
        (ω₀ y + (max 0 (min 1 s)) • mddbar n φ y) *
      ContinuousAlternatingMap.relTrace
        (ω₀ y + (max 0 (min 1 s)) • mddbar n φ y) (mddbar n φ y)) := by
  let τ : ℝ → ℝ := fun s => max 0 (min 1 s)
  let ωs (s : ℝ) := ω₀.perturb (τ s • φ)
    (hφ.smul (le_max_left _ _) (max_le_iff.mpr ⟨by norm_num, min_le_left 1 s⟩))
  let Q (x₀ : M) : (ℝ × EuclideanSpace ℂ (Fin n)) → ℝ := fun p =>
    RCLike.re ((ωs p.1).metricInChart x₀ p.2).det /
      RCLike.re (ω₀.metricInChart x₀ p.2).det *
        RCLike.re (((ωs p.1).metricInChart x₀ p.2)⁻¹ *
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) p.2).trace
  have hQcont (x₀ : M) : ContinuousOn (Q x₀)
      (Set.univ ×ˢ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) := by
    simpa [Q, τ, ωs] using continuousOn_path_chart_integrand ω₀ hφ x₀
  have hFchart (s : ℝ) (x₀ y : M) (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source) :
      (ContinuousAlternatingMap.relDet (ω₀ y) (ω₀ y + τ s • mddbar n φ y) *
        ContinuousAlternatingMap.relTrace (ω₀ y + τ s • mddbar n φ y) (mddbar n φ y)) =
        Q x₀ (s, extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) := by
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
    have hyE : y ∈ c.source := by simpa [c, extChartAt_source] using hy
    have hz : c y ∈ c.target := c.map_source hyE
    have hs0 : 0 ≤ τ s := le_max_left _ _
    have hs1 : τ s ≤ 1 := max_le_iff.mpr ⟨by norm_num, min_le_left 1 s⟩
    have hpot : ω₀.IsPotential (τ s • φ) := hφ.smul hs0 hs1
    have hma := ω₀.mongeAmpere_eq_inChart hpot.1 x₀ hy
    have hlap := (ωs s).laplacian_eq_inChart hφ.1 x₀ hy
    have hH : complexHessian ((τ s • φ) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) =
        τ s • complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) := by
      change (ddbar ((τ s • φ) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).coeffMatrix =
        τ s • (ddbar (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)).coeffMatrix
      rw [← chartRep_mddbar hpot.1 x₀ hz, ← chartRep_mddbar hφ.1 x₀ hz]
      rw [mddbar_smul hφ.1, FormField.chartRep_smul]
      simp [ContinuousAlternatingMap.coeffMatrix_smul]
    have hmetric : (ωs s).metricInChart x₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) =
        ω₀.metricInChart x₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) +
          τ s • complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) := by
      rw [KahlerForm.metricInChart_perturb (hpot) x₀ hz, hH]
    have hMApoint : ω₀.mongeAmpere (τ s • φ) y =
        ContinuousAlternatingMap.relDet (ω₀ y) (ω₀ y + τ s • mddbar n φ y) := by
      simp [KahlerForm.mongeAmpere, mddbar_smul hφ.1]
    have hLapPoint : (ωs s).laplacian φ y =
        ContinuousAlternatingMap.relTrace (ω₀ y + τ s • mddbar n φ y) (mddbar n φ y) := by
      simp [KahlerForm.laplacian, ωs, KahlerForm.perturb_apply, mddbar_smul hφ.1]
    calc
      _ = ω₀.mongeAmpere (τ s • φ) y * (ωs s).laplacian φ y := by rw [hMApoint, hLapPoint]
      _ = Q x₀ (s, c y) := by
        rw [hma, hlap]
        simp only [Q]
        rw [hmetric, hH]
  rw [continuous_iff_continuousAt]
  intro p
  rcases p with ⟨s₀, x₀⟩
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  have hqOpen : IsOpen (Set.univ ×ˢ c.target) :=
    (isOpen_prod_iff' (s := (Set.univ : Set ℝ)) (t := c.target)).2
      (Or.inl ⟨isOpen_univ, isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩)
  have hqmem : Set.univ ×ˢ c.target ∈ nhds (s₀, c x₀) :=
    hqOpen.mem_nhds ⟨Set.mem_univ _, mem_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩
  have hq : ContinuousAt (Q x₀) (s₀, c x₀) := (hQcont x₀).continuousAt hqmem
  have hcomp : ContinuousAt (fun p : ℝ × M => Q x₀ (p.1, c p.2)) (s₀, x₀) :=
    hq.comp₂ continuousAt_fst
      ((continuousAt_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀).comp continuousAt_snd)
  have hsourceOpen : IsOpen (Set.univ ×ˢ c.source) :=
    (isOpen_prod_iff' (s := (Set.univ : Set ℝ)) (t := c.source)).2
      (Or.inl ⟨isOpen_univ, isOpen_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩)
  have hsource : Set.univ ×ˢ c.source ∈ nhds (s₀, x₀) :=
    hsourceOpen.mem_nhds ⟨Set.mem_univ _, mem_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀⟩
  have heq : Function.uncurry (fun (s : ℝ) (y : M) =>
      ContinuousAlternatingMap.relDet (ω₀ y) (ω₀ y + τ s • mddbar n φ y) *
        ContinuousAlternatingMap.relTrace (ω₀ y + τ s • mddbar n φ y) (mddbar n φ y)) =ᶠ[nhds (s₀, x₀)]
      (fun p : ℝ × M => Q x₀ (p.1, c p.2)) := by
    filter_upwards [hsource] with p hp
    rcases p with ⟨s, y⟩
    have hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
      simpa [c, extChartAt_source] using hp.2
    exact hFchart s x₀ y hy
  exact hcomp.congr_of_eventuallyEq heq

private theorem segment_weighted_trace_lower_bound
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
    (hn : 1 ≤ n) {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) (x : M)
    {β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ} (hβ : β.IsNonneg) :
    (1 - s) ^ (n - 1) * ContinuousAlternatingMap.relTrace (ω₀ x) β ≤
      ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
        ContinuousAlternatingMap.relTrace (ω₀ x + s • mddbar n φ x) β := by
  let c : ℝ := 1 - s
  let α := ω₀ x + s • mddbar n φ x
  have hc : 0 < c := by dsimp [c]; linarith
  have hω : (ω₀ x).IsPositive := ω₀.isPositive x
  have hbase : (c • ω₀ x).IsPositive := hω.smul hc
  have hend : (ω₀ x + mddbar n φ x).IsPositive := by
    simpa [KahlerForm.perturb_apply] using hφ.2 x
  have hscaled : (s • (ω₀ x + mddbar n φ x)).IsPositive := hend.smul hs₀
  have halpha : (α - c • ω₀ x).IsNonneg := by
    have heq : α - c • ω₀ x = s • (ω₀ x + mddbar n φ x) := by
      ext v
      dsimp [α, c]
      simp [sub_eq_add_neg]
      ring
    rw [heq]
    exact hscaled.isNonneg
  have hmono := ContinuousAlternatingMap.relTrace_le_relDet_mul_relTrace hbase halpha hβ
  have htrace := ContinuousAlternatingMap.relTrace_smul_left (α := β) hω hc
  have hdet := ContinuousAlternatingMap.relDet_smul_left (α := α) hω hc
  rw [htrace, hdet] at hmono
  have hcPow : 0 < c ^ n := pow_pos hc n
  have hscaledMono := mul_le_mul_of_nonneg_left hmono (le_of_lt hcPow)
  have hpow : c ^ n * c⁻¹ = c ^ (n - 1) := by
    rw [← Nat.sub_add_cancel hn, pow_succ]
    simp [hc.ne']
  calc
    c ^ (n - 1) * ContinuousAlternatingMap.relTrace (ω₀ x) β =
        c ^ n * (c⁻¹ * ContinuousAlternatingMap.relTrace (ω₀ x) β) := by rw [← hpow]; ring
    _ ≤ c ^ n * ((c ^ n)⁻¹ * ContinuousAlternatingMap.relDet (ω₀ x) α *
        ContinuousAlternatingMap.relTrace α β) := hscaledMono
    _ = ContinuousAlternatingMap.relDet (ω₀ x) α *
        ContinuousAlternatingMap.relTrace α β := by
      field_simp [pow_ne_zero n hc.ne']
    _ = ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
        ContinuousAlternatingMap.relTrace (ω₀ x + s • mddbar n φ x) β := rfl

variable [MeasurableSpace M] [T2Space M] [CompactSpace M] in
private theorem integral_segment_trace_density_lower_bound
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (hn : 1 ≤ n)
    {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) (g : M → ℝ)
    {β : M → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hg : ∀ x, 0 ≤ g x) (hβ : ∀ x, (β x).IsNonneg)
    (hI₀ : Integrable (fun x => g x * ContinuousAlternatingMap.relTrace (ω₀ x) (β x))
      ω₀.volume)
    (hIs : Integrable (fun x => g x *
      (ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
        ContinuousAlternatingMap.relTrace (ω₀ x + s • mddbar n φ x) (β x))) ω₀.volume) :
    (1 - s) ^ (n - 1) *
        ∫ x, g x * ContinuousAlternatingMap.relTrace (ω₀ x) (β x) ∂ω₀.volume ≤
      ∫ x, g x *
        (ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
          ContinuousAlternatingMap.relTrace (ω₀ x + s • mddbar n φ x) (β x)) ∂ω₀.volume := by
  have hIweighted : Integrable (fun x => (1 - s) ^ (n - 1) *
      (g x * ContinuousAlternatingMap.relTrace (ω₀ x) (β x))) ω₀.volume :=
    hI₀.const_mul _
  have hpoint : ∀ x,
      (1 - s) ^ (n - 1) *
        (g x * ContinuousAlternatingMap.relTrace (ω₀ x) (β x)) ≤
      g x * (ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
        ContinuousAlternatingMap.relTrace (ω₀ x + s • mddbar n φ x) (β x)) := by
    intro x
    calc
      (1 - s) ^ (n - 1) *
          (g x * ContinuousAlternatingMap.relTrace (ω₀ x) (β x)) =
        g x * ((1 - s) ^ (n - 1) * ContinuousAlternatingMap.relTrace (ω₀ x) (β x)) := by ring
      _ ≤ g x * (ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
          ContinuousAlternatingMap.relTrace (ω₀ x + s • mddbar n φ x) (β x)) :=
        mul_le_mul_of_nonneg_left
          (segment_weighted_trace_lower_bound ω₀ hφ hn hs₀ hs₁ x (hβ x)) (hg x)
  have hmono := MeasureTheory.integral_mono_ae hIweighted hIs
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hmono
  exact hmono

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
private theorem segment_gradNormSq_integral_lower_bound
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (hn : 1 ≤ n)
    {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) (g : M → ℝ)
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) :
    (1 - s) ^ (n - 1) * ∫ x, g x * ω₀.gradNormSq φ x ∂ω₀.volume ≤
      ∫ x, g x * (ω₀.mongeAmpere (s • φ) x *
        (ω₀.perturb (s • φ) (hφ.smul hs₀.le hs₁.le)).gradNormSq φ x)
        ∂ω₀.volume := by
  have hpot : ω₀.IsPotential (s • φ) := hφ.smul (le_of_lt hs₀) hs₁.le
  let ωs := ω₀.perturb (s • φ) hpot
  have hMAcont : Continuous (ω₀.mongeAmpere (s • φ)) :=
    (ω₀.contMDiff_mongeAmpere hpot.1).continuous
  have hgrad0 : Continuous (ω₀.gradNormSq φ) :=
    (ω₀.contMDiff_gradNormSq hφ.1).continuous
  have hgradS : Continuous (ωs.gradNormSq φ) :=
    (ωs.contMDiff_gradNormSq hφ.1).continuous
  have hI0 : Integrable (fun x => g x *
      ContinuousAlternatingMap.relTrace (ω₀ x) (mdWedgeDBar n φ x)) ω₀.volume := by
    apply integrable_of_continuous_volume ω₀
    change Continuous (fun x => g x * ω₀.gradNormSq φ x)
    exact hg.mul hgrad0
  have hMApoint : ∀ x, ContinuousAlternatingMap.relDet (ω₀ x)
      (ω₀ x + s • mddbar n φ x) = ω₀.mongeAmpere (s • φ) x := by
    intro x
    simp [KahlerForm.mongeAmpere, mddbar_smul hφ.1 s]
  have hgradPoint : ∀ x, ContinuousAlternatingMap.relTrace
      (ω₀ x + s • mddbar n φ x) (mdWedgeDBar n φ x) = ωs.gradNormSq φ x := by
    intro x
    simp [KahlerForm.gradNormSq, ωs, KahlerForm.perturb_apply, mddbar_smul hφ.1 s]
  have hIs : Integrable (fun x => g x *
      (ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
        ContinuousAlternatingMap.relTrace (ω₀ x + s • mddbar n φ x) (mdWedgeDBar n φ x)))
      ω₀.volume := by
    have hcont : Continuous (fun x => g x *
        (ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
          ContinuousAlternatingMap.relTrace (ω₀ x + s • mddbar n φ x)
            (mdWedgeDBar n φ x))) := by
      have hfun : (fun x => g x *
          (ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + s • mddbar n φ x) *
            ContinuousAlternatingMap.relTrace (ω₀ x + s • mddbar n φ x)
              (mdWedgeDBar n φ x))) =
          fun x => g x * (ω₀.mongeAmpere (s • φ) x * ωs.gradNormSq φ x) := by
        funext x
        rw [hMApoint x, hgradPoint x]
      rw [hfun]
      exact hg.mul (hMAcont.mul hgradS)
    exact integrable_of_continuous_volume ω₀ hcont
  have htrace := integral_segment_trace_density_lower_bound ω₀ hφ hn hs₀ hs₁ g hg0
    (fun x => isNonneg_mdWedgeDBar φ x) hI0 hIs
  simpa [KahlerForm.gradNormSq, KahlerForm.mongeAmpere, KahlerForm.perturb_apply,
    mddbar_smul hφ.1 s, ωs] using htrace

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem interval_integral_one_sub_pow_lower (hn : 1 ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ ∫ s in (0 : ℝ)..1, (1 - s) ^ (n - 1) := by
  have hcont : Continuous (fun s : ℝ => (1 - s) ^ (n - 1)) := by fun_prop
  have hfi01 : IntervalIntegrable (fun s : ℝ => (1 - s) ^ (n - 1))
      (MeasureTheory.volume : Measure ℝ) 0 1 := hcont.intervalIntegrable _ _
  have hfi02 : IntervalIntegrable (fun s : ℝ => (1 - s) ^ (n - 1))
      (MeasureTheory.volume : Measure ℝ) 0 (1 / 2) := hcont.intervalIntegrable _ _
  have hfi21 : IntervalIntegrable (fun s : ℝ => (1 - s) ^ (n - 1))
      (MeasureTheory.volume : Measure ℝ) (1 / 2) 1 := hcont.intervalIntegrable _ _
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hfi02 hfi21
  have hpos21 : 0 ≤ ∫ s in (1 / 2 : ℝ)..1, (1 - s) ^ (n - 1) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro s hs
    exact pow_nonneg (by linarith [hs.2]) _
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ) ^ (n - 1))
      (MeasureTheory.volume : Measure ℝ) 0 (1 / 2) := continuous_const.intervalIntegrable _ _
  have hpow : ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
      (1 / 2 : ℝ) ^ (n - 1) ≤ (1 - s) ^ (n - 1) := by
    intro s hs
    apply pow_le_pow_left₀ (by norm_num : 0 ≤ (1 / 2 : ℝ))
    linarith [hs.2]
  have hhalf := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hconst hfi02 hpow
  rw [← hsplit]
  have hconstInt : (∫ s in (0 : ℝ)..(1 / 2), (1 / 2 : ℝ) ^ (n - 1)) =
      (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (n - 1) := by
    rw [intervalIntegral.integral_const]
    norm_num
  rw [hconstInt] at hhalf
  have hpow' : (1 / 2 : ℝ) * (1 / 2) ^ (n - 1) = (1 / 2 : ℝ) ^ n := by
    calc
      (1 / 2 : ℝ) * (1 / 2) ^ (n - 1) = (1 / 2 : ℝ) ^ (n - 1) * (1 / 2) := by ring
      _ = (1 / 2 : ℝ) ^ n := by
        rw [← pow_succ]
        congr 1
        omega
  nlinarith

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
private theorem integral_mongeAmpere_weighted_laplacian_eq_energy
    (ω₀ : KahlerForm n M) {ψ φ : M → ℝ} (hψ : ω₀.IsPotential ψ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ∫ x, ω₀.mongeAmpere ψ x *
        (deriv F (φ x) * (ω₀.perturb ψ hψ).laplacian φ x) ∂ω₀.volume =
      -∫ x, ω₀.mongeAmpere ψ x *
        (deriv (deriv F) (φ x) * (ω₀.perturb ψ hψ).gradNormSq φ x) ∂ω₀.volume := by
  let ωψ := ω₀.perturb ψ hψ
  have henergy := integral_deriv_comp_laplacian_eq_neg_energy ωψ hφ hF
  have hρmeas : Measurable (fun x => ENNReal.ofReal (ω₀.mongeAmpere ψ x)) :=
    ENNReal.measurable_ofReal.comp (ω₀.contMDiff_mongeAmpere hψ.1).continuous.measurable
  have hρtop : ∀ᵐ x ∂ω₀.volume, ENNReal.ofReal (ω₀.mongeAmpere ψ x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [ω₀.volume_perturb hψ] at henergy
  rw [integral_withDensity_eq_integral_toReal_smul hρmeas hρtop] at henergy
  rw [integral_withDensity_eq_integral_toReal_smul hρmeas hρtop] at henergy
  have htoReal : ∀ x,
      (ENNReal.ofReal (ω₀.mongeAmpere ψ x)).toReal = ω₀.mongeAmpere ψ x := by
    intro x
    exact ENNReal.toReal_ofReal (le_of_lt (ω₀.mongeAmpere_pos hψ x))
  simpa only [htoReal, smul_eq_mul, mul_assoc] using henergy

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
private theorem integral_mongeAmpere_segment_weighted_energy
    (ω₀ : KahlerForm n M) {ψ φ : M → ℝ} (hψ : ω₀.IsPotential ψ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ∫ x, ω₀.mongeAmpere ψ x *
        (deriv F (-φ x) * (ω₀.perturb ψ hψ).laplacian φ x) ∂ω₀.volume =
      ∫ x, ω₀.mongeAmpere ψ x *
        (deriv (deriv F) (-φ x) * (ω₀.perturb ψ hψ).gradNormSq φ x) ∂ω₀.volume := by
  let ωψ := ω₀.perturb ψ hψ
  let u : M → ℝ := fun x => -φ x
  have hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u := by
    simpa [u, Function.comp_def] using (contDiff_neg.contMDiff.comp hφ)
  have henergy := integral_mongeAmpere_weighted_laplacian_eq_energy ω₀ hψ hu hF
  have hlap : ωψ.laplacian u = fun x => -ωψ.laplacian φ x := by
    funext x
    have h2le : (2 : ℕ∞ω) ≤ ∞ :=
      WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
    have hneg2 : ContDiff ℝ 2 (fun t : ℝ => -t) := contDiff_neg.of_le h2le
    have h := ωψ.laplacian_comp hφ hneg2 x
    simpa [u, Function.comp_def] using h
  have hgrad : ωψ.gradNormSq u = ωψ.gradNormSq φ := by
    funext x
    have hneg : ContDiff ℝ ∞ (fun t : ℝ => -t) := contDiff_neg
    have hchain := gradNormSq_comp ωψ hφ hneg x
    simpa [u, Function.comp_def] using hchain
  have henergy' := henergy
  rw [hlap, hgrad] at henergy'
  have hleft :
      (∫ x, ω₀.mongeAmpere ψ x *
        (deriv F (-φ x) * (-ωψ.laplacian φ x)) ∂ω₀.volume) =
      -(∫ x, ω₀.mongeAmpere ψ x *
        (deriv F (-φ x) * ωψ.laplacian φ x) ∂ω₀.volume) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  rw [hleft] at henergy'
  have hresult :
      ∫ x, ω₀.mongeAmpere ψ x * (deriv F (-φ x) * ωψ.laplacian φ x) ∂ω₀.volume =
        ∫ x, ω₀.mongeAmpere ψ x *
          (deriv (deriv F) (-φ x) * ωψ.gradNormSq φ x) ∂ω₀.volume := by
    linarith
  simpa [ωψ] using hresult

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
private theorem segment_weighted_energy_lower_bound
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (hn : 1 ≤ n)
    {s : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hconv : ∀ x, 0 ≤ deriv (deriv F) (-φ x)) :
    (1 - s) ^ (n - 1) *
        ∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume ≤
      ∫ x, ω₀.mongeAmpere (s • φ) x *
        (deriv F (-φ x) * (ω₀.perturb (s • φ)
          (hφ.smul hs₀.le hs₁.le)).laplacian φ x) ∂ω₀.volume := by
  have hpot : ω₀.IsPotential (s • φ) := hφ.smul hs₀.le hs₁.le
  let ωs := ω₀.perturb (s • φ) hpot
  have hF' : ContDiff ℝ ∞ (deriv F) := contDiff_infty_iff_deriv.mp hF |>.2
  have hF'' : ContDiff ℝ ∞ (deriv (deriv F)) :=
    contDiff_infty_iff_deriv.mp hF' |>.2
  let g : M → ℝ := fun x => deriv (deriv F) (-φ x)
  have hg : Continuous g := by
    change Continuous (deriv (deriv F) ∘ (fun x => -φ x))
    exact hF''.continuous.comp ((contDiff_neg.contMDiff.comp hφ.1).continuous)
  have htrace := segment_gradNormSq_integral_lower_bound ω₀ hφ hn hs₀ hs₁ g hg hconv
  have henergy := integral_mongeAmpere_segment_weighted_energy ω₀ hpot hφ.1 hF
  have henergy' :
      ∫ x, g x * (ω₀.mongeAmpere (s • φ) x * ωs.gradNormSq φ x) ∂ω₀.volume =
        ∫ x, ω₀.mongeAmpere (s • φ) x *
          (deriv F (-φ x) * ωs.laplacian φ x) ∂ω₀.volume := by
    calc
      ∫ x, g x * (ω₀.mongeAmpere (s • φ) x * ωs.gradNormSq φ x) ∂ω₀.volume =
          ∫ x, ω₀.mongeAmpere (s • φ) x *
            (deriv (deriv F) (-φ x) * ωs.gradNormSq φ x) ∂ω₀.volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            dsimp [g]
            ring
      _ = ∫ x, ω₀.mongeAmpere (s • φ) x *
            (deriv F (-φ x) * ωs.laplacian φ x) ∂ω₀.volume := henergy.symm
  have htrace' := htrace.trans_eq henergy'
  simpa [ωs] using htrace'

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem normalized_mongeAmpere_energy_bound
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (hn : 1 ≤ n)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hconv : ∀ x, 0 ≤ deriv (deriv F) (-φ x)) :
    (1 / 2 : ℝ) ^ n *
        ∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume ≤
      ∫ x, deriv F (-φ x) * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume := by
  have hF' : ContDiff ℝ ∞ (deriv F) := contDiff_infty_iff_deriv.mp hF |>.2
  have hF'' : ContDiff ℝ ∞ (deriv (deriv F)) :=
    contDiff_infty_iff_deriv.mp hF' |>.2
  let g : M → ℝ := fun x => deriv F (-φ x)
  have hg : Continuous g := by
    change Continuous (deriv F ∘ (fun x => -φ x))
    exact hF'.continuous.comp ((contDiff_neg.contMDiff.comp hφ.1).continuous)
  let Q : ℝ × M → ℝ := fun p => g p.2 *
    (ContinuousAlternatingMap.relDet (ω₀ p.2)
        (ω₀ p.2 + (max 0 (min 1 p.1)) • mddbar n φ p.2) *
      ContinuousAlternatingMap.relTrace
        (ω₀ p.2 + (max 0 (min 1 p.1)) • mddbar n φ p.2) (mddbar n φ p.2))
  have hQcont : Continuous Q := by
    have hg' : Continuous (fun p : ℝ × M => g p.2) := hg.comp continuous_snd
    have hpath := continuous_path_segment_integrand ω₀ hφ
    change Continuous (fun p : ℝ × M => g p.2 *
      (ContinuousAlternatingMap.relDet (ω₀ p.2)
          (ω₀ p.2 + (max 0 (min 1 p.1)) • mddbar n φ p.2) *
        ContinuousAlternatingMap.relTrace
          (ω₀ p.2 + (max 0 (min 1 p.1)) • mddbar n φ p.2) (mddbar n φ p.2)))
    exact hg'.mul hpath
  have hFjoint : Continuous (Function.uncurry fun (s : ℝ) (x : M) =>
      g x * (ContinuousAlternatingMap.relDet (ω₀ x)
          (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) *
        ContinuousAlternatingMap.relTrace
          (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) (mddbar n φ x))) := by
    change Continuous Q
    exact hQcont
  have hsegment := integral_weighted_mongeAmpere_segment ω₀ hφ g hFjoint
  let L : ℝ → ℝ := fun s => ∫ x, g x *
    (ContinuousAlternatingMap.relDet (ω₀ x)
        (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) *
      ContinuousAlternatingMap.relTrace
        (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) (mddbar n φ x))
    ∂ω₀.volume
  have hProd := interval_product_integrable_of_continuous ω₀ hFjoint
  have hLinterval : IntervalIntegrable L (MeasureTheory.volume : Measure ℝ) 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    change Integrable (fun s : ℝ => ∫ x, g x *
      (ContinuousAlternatingMap.relDet (ω₀ x)
          (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) *
        ContinuousAlternatingMap.relTrace
          (ω₀ x + (max 0 (min 1 s)) • mddbar n φ x) (mddbar n φ x))
      ∂ω₀.volume) ((MeasureTheory.volume : Measure ℝ).restrict (Set.Ioc 0 1))
    simpa [L, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hProd.integral_prod_left
  have hI0 : 0 ≤ ∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (hconv x) (ω₀.gradNormSq_nonneg φ x)
  have hcoefInt : IntervalIntegrable (fun s : ℝ => (1 - s) ^ (n - 1) *
      (∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume))
      (MeasureTheory.volume : Measure ℝ) 0 1 := by
    have hcoefCont : Continuous (fun s : ℝ => (1 - s) ^ (n - 1) *
        (∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume)) := by fun_prop
    exact hcoefCont.intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    hcoefInt hLinterval (by
      intro s hs
      have hs₀ : 0 < s := hs.1
      have hs₁ : s < 1 := hs.2
      simpa [L, g, min_eq_right hs₁.le, max_eq_right hs₀.le,
        KahlerForm.mongeAmpere, KahlerForm.laplacian, KahlerForm.perturb_apply,
        mddbar_smul hφ.1 s, mul_assoc, mul_comm, mul_left_comm] using
        segment_weighted_energy_lower_bound ω₀ hφ hn hs₀ hs₁ hF hconv)
  have hmass := interval_integral_one_sub_pow_lower hn
  have hconst : (∫ s in (0 : ℝ)..1, (1 - s) ^ (n - 1) *
      (∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume)) =
      (∫ s in (0 : ℝ)..1, (1 - s) ^ (n - 1)) *
        ∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume := by
    rw [intervalIntegral.integral_mul_const]
  have hmassI0 := mul_le_mul_of_nonneg_right hmass hI0
  have hfinal : (1 / 2 : ℝ) ^ n *
      ∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume ≤
      ∫ s in (0 : ℝ)..1, L s := by
    calc
      _ ≤ (∫ s in (0 : ℝ)..1, (1 - s) ^ (n - 1)) *
          ∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume := hmassI0
      _ = ∫ s in (0 : ℝ)..1, (1 - s) ^ (n - 1) *
          (∫ x, deriv (deriv F) (-φ x) * ω₀.gradNormSq φ x ∂ω₀.volume) := hconst.symm
      _ ≤ ∫ s in (0 : ℝ)..1, L s := hmono
  rw [← hsegment] at hfinal
  simpa [g] using hfinal

end KahlerForm
