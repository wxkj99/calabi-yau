module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smooth residual outputs and chart cancellation

The fixed background determinant and the fixed path terms cancel only in sequence differences.
The upper bound on α is explicit: a smooth nonconstant function need not be α-Hölder for α>1.
Following Székelyhidi §3.1, Lemma 3.3; the compact
Hölder product convention is GT §4.1, (4.7). The Hölder product convention is cited from the stated reference.
-/

public section

open scoped Manifold ContDiff NNReal ENNReal Topology ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory
open Filter Set

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

private theorem contMDiff_log_of_positive_smooth
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (hpos : ∀ x, 0 < f x) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun x ↦ Real.log (f x)) := by
  intro y
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  simp only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ]
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let e := extChartAt I y
  let z := e y
  have hz : z ∈ e.target := mem_extChartAt_target y
  have hfon : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f Set.univ :=
    contMDiffOn_univ.mpr hf
  have hcoordM : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (f ∘ e.symm) e.target :=
    hfon.comp (contMDiffOn_extChartAt_symm y) (by intro u hu; exact Set.mem_univ _)
  have hcoord : ContDiffOn ℝ ∞ (f ∘ e.symm) e.target := hcoordM.contDiffOn
  have hposCoord : ∀ z ∈ e.target, 0 < (f ∘ e.symm) z := by
    intro z hz
    exact hpos (e.symm z)
  have hmaps : Set.MapsTo (f ∘ e.symm) e.target {0}ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact (hposCoord z hz).ne'
  have hlog : ContDiffOn ℝ ∞ (Real.log ∘ (f ∘ e.symm)) e.target :=
    Real.contDiffOn_log.comp hcoord hmaps
  have hlog' : ContDiffOn ℝ ∞ ((fun x ↦ Real.log (f x)) ∘ e.symm) e.target := by
    convert hlog using 1
    rfl
  have htarget : e.target ∈ 𝓝 z := by
    change (extChartAt I y).target ∈ 𝓝 z
    exact (isOpen_extChartAt_target y).mem_nhds hz
  exact hlog'.contDiffAt htarget

/-- Smooth positive approximants have genuine smooth order-zero residual outputs, with the exact
chart formula for their differences on every point of the compact piece. -/
private theorem contMDiff_add_fun {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] {f g : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f + g) := by
  have hadd : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 + p.2) := contDiff_fst.add contDiff_snd
  convert hadd.comp_contMDiff (hf.prodMk_space hg) using 1
  ext x
  rfl

private theorem contMDiff_smul_fun {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) (c : ℝ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (c • f) := by
  have hmul : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_fst.mul contDiff_snd
  change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun x ↦ c * f x)
  simpa [Function.comp_def, smul_eq_mul] using
    hmul.comp_contMDiff (contMDiff_const.prodMk_space hf)

private theorem exists_smoothCore_uncentered_residual_one
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (v : SmoothChartHolderCore P.finiteChartCover 2 α) (δ : ℝ)
    (hpositive : ω₀.IsC2Potential (φ + fun x => v.smoothMap x)) :
    ∃ g : SmoothChartHolderCore P.finiteChartCover 0 α,
      g.smoothMap = uncenteredContinuityPathResidual ω₀ F t φ hsol v.smoothMap δ ∧
      HasFiniteChartHolderGauge P.finiteChartCover 0 α g.smoothMap := by
  classical
  let u : M → ℝ := fun x => v.smoothMap x
  have ha : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u := by
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v.smoothMap
    exact v.smoothMap.contMDiff
  have htotal : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (φ + u) :=
    contMDiff_add_fun hsol.1.1 ha
  have htotalPotential : ω₀.IsPotential (φ + u) := ⟨htotal, hpositive.2⟩
  have hnum : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (ω₀.mongeAmpere (φ + u)) := ω₀.contMDiff_mongeAmpere htotalPotential.1
  have hden : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
      ∞ (ω₀.mongeAmpere φ) := ω₀.contMDiff_mongeAmpere hsol.1.1
  have hnumPos : ∀ x, 0 < ω₀.mongeAmpere (φ + v.smoothMap) x :=
    fun x => ω₀.mongeAmpere_pos htotalPotential x
  have hdenPos : ∀ x, 0 < ω₀.mongeAmpere φ x := fun x => ω₀.mongeAmpere_pos hsol.1 x
  have hlogNum := contMDiff_log_of_positive_smooth hnum hnumPos
  have hlogDen := contMDiff_log_of_positive_smooth hden hdenPos
  have hlogRatio : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x => Real.log (ω₀.mongeAmpere (φ + v.smoothMap) x) -
        Real.log (ω₀.mongeAmpere φ x)) := hlogNum.sub hlogDen
  have hlogRatioEq : (fun x => Real.log (ω₀.mongeAmpere (φ + v.smoothMap) x) -
      Real.log (ω₀.mongeAmpere φ x)) =
      (fun x => Real.log (ω₀.mongeAmpere (φ + v.smoothMap) x /
        ω₀.mongeAmpere φ x)) := by
    funext x
    rw [Real.log_div (hnumPos x).ne' (hdenPos x).ne']
  have hlogRatio' : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x => Real.log (ω₀.mongeAmpere (φ + v.smoothMap) x /
        ω₀.mongeAmpere φ x)) := by
    rw [← hlogRatioEq]
    exact hlogRatio
  have hdeltaF := contMDiff_smul_fun hF δ
  have hpath : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x => δ * F x + (ω₀.pathConstant F (t + δ) - ω₀.pathConstant F t)) := by
    have hconst : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (fun _ : M => ω₀.pathConstant F (t + δ) - ω₀.pathConstant F t) := contMDiff_const
    convert contMDiff_add_fun hdeltaF hconst using 1
  have hres : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (uncenteredContinuityPathResidual ω₀ F t φ hsol v.smoothMap δ) := by
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      ((fun x => Real.log (ω₀.mongeAmpere (φ + v.smoothMap) x /
        ω₀.mongeAmpere φ x)) -
        (fun x => δ * F x + (ω₀.pathConstant F (t + δ) - ω₀.pathConstant F t)))
    exact hlogRatio'.sub hpath
  let gmap : ContMDiffMap (𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (modelWithCornersSelf ℝ ℝ) M ℝ ∞ :=
    ⟨uncenteredContinuityPathResidual ω₀ F t φ hsol v.smoothMap δ, hres⟩
  let g : SmoothChartHolderCore P.finiteChartCover 0 α :=
    (smoothChartHolderCoreEquivSmoothMap P.finiteChartCover 0 α).symm gmap
  have hgmap : g.smoothMap =
      uncenteredContinuityPathResidual ω₀ F t φ hsol v.smoothMap δ := rfl
  have hα : α ≤ 1 := by exact_mod_cast le_of_lt hα₁
  have hcharts : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 0 α
      ({(g.smoothMap : M → ℝ)} : Set (M → ℝ)) :=
    HolderBoundedInCharts.singleton g.smoothMap.contMDiff hα
  have hfinite : HasFiniteChartHolderGauge P.finiteChartCover 0 α g.smoothMap := by
    change finiteChartHolderGauge P.finiteChartCover 0 α g.smoothMap < ⊤
    apply lt_top_iff_ne_top.mpr
    unfold finiteChartHolderGauge
    apply iSup_ne_top
    intro i
    obtain ⟨C, hC⟩ := hcharts (P.finiteChartCover.base i)
      (P.finiteChartCover.piece i) (P.finiteChartCover.isCompact_piece i)
      (P.finiteChartCover.piece_in_target i)
    have hbound := hC g.smoothMap (Set.mem_singleton _)
    have hholder : HolderWith C α ((P.finiteChartCover.piece i).domRestrict
        (iteratedFDeriv ℝ 0 (g.smoothMap ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm))) := by
      simpa [Function.comp_def] using hbound.2.holderWith
    have hle := CalabiYau.Schauder.eContDiffHolderGaugeOn_le
      (fun _ : ℕ => C) C hbound.1 hholder
    have hsum : (∑ j ∈ Finset.range (0 + 1), (C : ℝ≥0∞)) ≠ ⊤ := by
      apply ENNReal.sum_ne_top.mpr
      intro j hj
      exact ENNReal.coe_ne_top
    have htotalFinite : (∑ j ∈ Finset.range (0 + 1), (C : ℝ≥0∞)) + C ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hsum, ENNReal.coe_ne_top⟩
    exact ne_top_of_le_ne_top htotalFinite hle
  exact ⟨g, hgmap, hfinite⟩

private theorem smooth_output_chart_metric_hessian_decomposition
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (φ u : M → ℝ)
    (hφ : ω₀.IsPotential φ) (hplus : ω₀.IsC2Potential (φ + u))
    (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ω₀.metricInChart x z + complexHessian
        ((φ + u) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z =
      (ω₀.perturb φ hφ).metricInChart x z + complexHessian
        (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hbound : (2 : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hφ2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ := hφ.1.of_le hbound
  have hu2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 u := by
    have h := hplus.1.sub hφ2
    have heq : (φ + u) - φ = u := by funext y; simp
    rw [← heq]
    exact h
  have hφChart : ContDiffOn ℝ 2 (φ ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hφ2).2 x 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have huChart : ContDiffOn ℝ 2 (u ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hu2).2 x 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hφAt : ContDiffAt ℝ 2 (φ ∘ e.symm) z :=
    hφChart.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)
  have huAt : ContDiffAt ℝ 2 (u ∘ e.symm) z :=
    huChart.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)
  have hsum : complexHessian ((φ + u) ∘ e.symm) z =
      complexHessian (φ ∘ e.symm) z + complexHessian (u ∘ e.symm) z := by
    have hfun : (φ + u) ∘ e.symm = (φ ∘ e.symm) + (u ∘ e.symm) := by
      funext w
      rfl
    unfold complexHessian
    rw [hfun, ddbar_add hφAt huAt, ContinuousAlternatingMap.coeffMatrix_add]
  rw [ω₀.metricInChart_perturb hφ x hz, hsum]
  abel

private theorem smooth_output_chart_log_ma_difference
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₀ : KahlerForm n M) (φ u v : M → ℝ)
    (hφ : ω₀.IsPotential φ)
    (hu : ω₀.IsC2Potential (φ + u)) (hv : ω₀.IsC2Potential (φ + v))
    (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    Real.log (ω₀.mongeAmpere (φ + u) ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) -
      Real.log (ω₀.mongeAmpere (φ + v) ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) =
    Real.log (RCLike.re (((ω₀.perturb φ hφ).metricInChart x z +
      complexHessian (u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).det)) -
      Real.log (RCLike.re (((ω₀.perturb φ hφ).metricInChart x z +
      complexHessian (v ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).det)) := by
  classical
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  let gbase := ω₀.metricInChart x z
  let g := (ω₀.perturb φ hφ).metricInChart x z
  let A := g + complexHessian (u ∘ e.symm) z
  let B := g + complexHessian (v ∘ e.symm) z
  have hyx : y ∈ e.source := e.map_target hz
  have hyChart : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [e, extChartAt_source] using hyx
  have hzy : e y = z := e.right_inv hz
  have hmaU := mongeAmpere_eq_inChart_of_contMDiff_two
    (ω₀ := ω₀) hu.1 x (y := y) hyChart
  have hmaV := mongeAmpere_eq_inChart_of_contMDiff_two
    (ω₀ := ω₀) hv.1 x (y := y) hyChart
  rw [hzy] at hmaU hmaV
  rw [smooth_output_chart_metric_hessian_decomposition ω₀ φ u hφ hu x hz] at hmaU
  rw [smooth_output_chart_metric_hessian_decomposition ω₀ φ v hφ hv x hz] at hmaV
  have hmaU' : ω₀.mongeAmpere (φ + u) y = RCLike.re A.det / RCLike.re gbase.det := by
    simpa [A, g, gbase, e] using hmaU
  have hmaV' : ω₀.mongeAmpere (φ + v) y = RCLike.re B.det / RCLike.re gbase.det := by
    simpa [B, g, gbase, e] using hmaV
  have hbase : 0 < RCLike.re gbase.det :=
    (RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hz).det_pos).1
  have hMAU : 0 < ω₀.mongeAmpere (φ + u) y := by
    change 0 < ContinuousAlternatingMap.relDet (ω₀ y) (ω₀ y + mddbar n (φ + u) y)
    exact ContinuousAlternatingMap.relDet_pos (ω₀.isPositive y) (hu.2 y)
  have hMAV : 0 < ω₀.mongeAmpere (φ + v) y := by
    change 0 < ContinuousAlternatingMap.relDet (ω₀ y) (ω₀ y + mddbar n (φ + v) y)
    exact ContinuousAlternatingMap.relDet_pos (ω₀.isPositive y) (hv.2 y)
  have hAdet : RCLike.re A.det ≠ 0 := by
    intro hzero
    have h := hMAU
    rw [hmaU', hzero] at h
    simp at h
  have hBdet : RCLike.re B.det ≠ 0 := by
    intro hzero
    have h := hMAV
    rw [hmaV', hzero] at h
    simp at h
  have hlogU : Real.log (ω₀.mongeAmpere (φ + u) y) =
      Real.log (RCLike.re A.det) - Real.log (RCLike.re gbase.det) := by
    rw [hmaU', Real.log_div hAdet hbase.ne']
  have hlogV : Real.log (ω₀.mongeAmpere (φ + v) y) =
      Real.log (RCLike.re B.det) - Real.log (RCLike.re gbase.det) := by
    rw [hmaV', Real.log_div hBdet hbase.ne']
  have htarget : Real.log (ω₀.mongeAmpere (φ + u) y) -
      Real.log (ω₀.mongeAmpere (φ + v) y) =
      Real.log (RCLike.re A.det) - Real.log (RCLike.re B.det) := by
    rw [hlogU, hlogV]
    ring
  simpa [e, y, A, B, g] using htarget

theorem exists_smoothCore_uncenteredResidual_outputs
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (δ : ℝ) (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hpositive : ∀ j, ω₀.IsC2Potential (φ + fun x => (v j).smoothMap x)) :
    ∃ g : ℕ → SmoothChartHolderCore P.finiteChartCover 0 α,
      (∀ j x, g j x = uncenteredContinuityPathResidual
        ω₀ F t φ hsol (fun y => (v j).smoothMap y) δ x) ∧
      (∀ j k i z, z ∈ P.finiteChartCover.piece i →
        (-g j + g k)
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
              (P.finiteChartCover.base i)).symm z) =
          Real.log (RCLike.re
            (smoothCorePerturbedChartMatrix (ω₀.perturb φ hsol.1)
              P.finiteChartCover α (v k) i z).det) -
          Real.log (RCLike.re
            (smoothCorePerturbedChartMatrix (ω₀.perturb φ hsol.1)
              P.finiteChartCover α (v j) i z).det)) := by
  classical
  let g : ℕ → SmoothChartHolderCore P.finiteChartCover 0 α := fun j =>
    Classical.choose (exists_smoothCore_uncentered_residual_one ω₀ F hF t φ hsol α hα₁
      (v j) δ (hpositive j))
  have hgspec (j : ℕ) :
      (g j).smoothMap = uncenteredContinuityPathResidual ω₀ F t φ hsol
        (v j).smoothMap δ ∧
      HasFiniteChartHolderGauge P.finiteChartCover 0 α (g j).smoothMap :=
    Classical.choose_spec (exists_smoothCore_uncentered_residual_one ω₀ F hF t φ hsol α hα₁
      (v j) δ (hpositive j))
  refine ⟨g, ?_, ?_⟩
  · intro j x
    exact congrFun (hgspec j).1 x
  · intro j k i z hz
    let x := P.finiteChartCover.base i
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let y := e.symm z
    let uk : M → ℝ := fun p => (v k).smoothMap p
    let uj : M → ℝ := fun p => (v j).smoothMap p
    have hzChart : z ∈ e.target :=
      P.finiteChartCover.piece_in_target i hz
    have huSmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (φ + uk) := by
      apply contMDiff_add_fun hsol.1.1
      change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (v k).smoothMap
      exact (v k).smoothMap.contMDiff
    have hvSmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (φ + uj) := by
      apply contMDiff_add_fun hsol.1.1
      change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (v j).smoothMap
      exact (v j).smoothMap.contMDiff
    have hpotU : ω₀.IsPotential (φ + uk) := ⟨huSmooth, (hpositive k).2⟩
    have hpotV : ω₀.IsPotential (φ + uj) := ⟨hvSmooth, (hpositive j).2⟩
    have hbasePos : 0 < ω₀.mongeAmpere φ y := ω₀.mongeAmpere_pos hsol.1 y
    have huPos : 0 < ω₀.mongeAmpere (φ + uk) y := ω₀.mongeAmpere_pos hpotU y
    have hvPos : 0 < ω₀.mongeAmpere (φ + uj) y := ω₀.mongeAmpere_pos hpotV y
    have hratio :
        Real.log (ω₀.mongeAmpere (φ + uk) y / ω₀.mongeAmpere φ y) -
          Real.log (ω₀.mongeAmpere (φ + uj) y / ω₀.mongeAmpere φ y) =
        Real.log (ω₀.mongeAmpere (φ + uk) y) -
          Real.log (ω₀.mongeAmpere (φ + uj) y) := by
      rw [Real.log_div huPos.ne' hbasePos.ne', Real.log_div hvPos.ne' hbasePos.ne']
      ring
    have hres : -(g j).smoothMap y + (g k).smoothMap y =
        Real.log (ω₀.mongeAmpere (φ + uk) y / ω₀.mongeAmpere φ y) -
          Real.log (ω₀.mongeAmpere (φ + uj) y / ω₀.mongeAmpere φ y) := by
      rw [congrFun (hgspec j).1 y, congrFun (hgspec k).1 y]
      simp [uncenteredContinuityPathResidual, uk, uj]
    have hdet := smooth_output_chart_log_ma_difference ω₀ φ uk uj hsol.1
      (hpositive k) (hpositive j) x hzChart
    have hdet' :
        Real.log (ω₀.mongeAmpere (φ + uk) y) -
          Real.log (ω₀.mongeAmpere (φ + uj) y) =
        Real.log (RCLike.re
          (smoothCorePerturbedChartMatrix (ω₀.perturb φ hsol.1)
            P.finiteChartCover α (v k) i z).det) -
        Real.log (RCLike.re
          (smoothCorePerturbedChartMatrix (ω₀.perturb φ hsol.1)
            P.finiteChartCover α (v j) i z).det) := by
      simpa [smoothCorePerturbedChartMatrix, uk, uj, x, e, y] using hdet
    change (-g j + g k).smoothMap y = _
    calc
      (-g j + g k).smoothMap y = -(g j).smoothMap y + (g k).smoothMap y := by
        change ((smoothChartHolderCoreEquivSmoothMap P.finiteChartCover 0 α)
          (-g j + g k)) y = _
        rfl
      _ = Real.log (ω₀.mongeAmpere (φ + uk) y) -
          Real.log (ω₀.mongeAmpere (φ + uj) y) := hres.trans hratio
      _ = _ := hdet'

end KahlerForm
