module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.Basic

/-!
# Pointwise identification of the logarithmic residual limit

The limiting matrix is exactly the metric plus the Hessian of the evaluated C² carrier. Its
strict positivity makes determinant and logarithm continuity applicable. No continuity of log
at zero, positivity-of-approximants-only passage, or big-to-little Hölder assertion is used.
-/

public section

open scoped Manifold ContDiff NNReal Topology ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- Smooth residual outputs converge pointwise to the residual of the actual positive C² limit.
F is fixed, so this scalar passage needs no smoothness assumption on F. -/
theorem smoothCore_uncenteredResidual_outputs_tendsto
    (ω₀ : KahlerForm n M) (F : M → ℝ) (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (u : P.C2) (δ : ℝ) (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hv : Filter.Tendsto
      (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) Filter.atTop
      (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)))
    (hpositiveLimit : ω₀.IsC2Potential (φ + P.evalC2 u))
    (hclose : ∀ j i z, z ∈ P.finiteChartCover.piece i →
      ‖smoothCorePerturbedChartMatrix (ω₀.perturb φ hsol.1) P.finiteChartCover α (v j) i z -
        evaluatedPerturbedChartMatrix (ω₀.perturb φ hsol.1) α u i z‖ ≤
          ((n + 1 : ℝ≥0) : ℝ) *
            ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
              (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖)
    (g : ℕ → SmoothChartHolderCore P.finiteChartCover 0 α)
    (houtput : ∀ j x, g j x = uncenteredContinuityPathResidual
      ω₀ F t φ hsol (fun y => (v j).smoothMap y) δ x) :
    ∀ x, Filter.Tendsto (fun j => g j x) Filter.atTop
      (𝓝 (uncenteredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ x)) := by
  classical
  let ω₁ := ω₀.perturb φ hsol.1
  let ψ : M → ℝ := P.evalC2 u
  have hφ₂ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ :=
    hsol.1.1.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ := by
    have h := hpositiveLimit.1.sub hφ₂
    have hEq : (φ + P.evalC2 u) - φ = P.evalC2 u := by funext x; simp
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u)
    rw [← hEq]
    exact h
  have hcocycle (f : M → ℝ)
      (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f) (y : M) :
      ω₀.mongeAmpere (φ + f) y =
        ω₀.mongeAmpere φ y * ω₁.mongeAmpere f y := by
    change ContinuousAlternatingMap.relDet (ω₀ y) (ω₀ y + mddbar n (φ + f) y) =
      ContinuousAlternatingMap.relDet (ω₀ y) (ω₀ y + mddbar n φ y) *
        ContinuousAlternatingMap.relDet (ω₁ y) (ω₁ y + mddbar n f y)
    rw [mddbar_add_of_contMDiff_two hφ₂ hf]
    simpa [ω₁, KahlerForm.perturb, add_assoc] using
      (ContinuousAlternatingMap.relDet_mul_relDet (ω₀.isPositive y) (hsol.1.2 y)).symm
  have hMApos (y : M) : 0 < ω₁.mongeAmpere ψ y := by
    change 0 < ContinuousAlternatingMap.relDet (ω₁ y) (ω₁ y + mddbar n ψ y)
    apply ContinuousAlternatingMap.relDet_pos (ω₁.isPositive y)
    have h := hpositiveLimit.2 y
    have h' : ((ω₀.toFormField + mddbar n (φ + ψ)) y).IsPositive := by
      simpa [ψ] using h
    rw [mddbar_add_of_contMDiff_two hφ₂ hψ] at h'
    simpa [ω₁, KahlerForm.perturb, add_assoc] using h'
  have hinputnorm : Filter.Tendsto
      (fun j => ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
        (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖)
      Filter.atTop (𝓝 0) := by
    have hsub : Filter.Tendsto
        (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
          (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2))
        Filter.atTop (𝓝 0) := by
      simpa using hv.sub_const (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)
    have hnorm : Filter.Tendsto
        (fun w : LittleHolder P.finiteChartCover 2 α P.normedDataC2 => ‖w‖)
        (𝓝 (0 : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_norm.tendsto
        (0 : LittleHolder P.finiteChartCover 2 α P.normedDataC2))
    convert hnorm.comp hsub using 1 ; rfl
  intro x
  let cover := P.finiteChartCover
  obtain ⟨i, z, hz, hzx⟩ := cover.interior_covers x
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  let y := e.symm z
  have hzPiece : z ∈ cover.piece i := interior_subset hz
  have hzTarget : z ∈ e.target := cover.piece_in_target i hzPiece
  have hySource : y ∈ e.source := e.map_target hzTarget
  have hzy : e y = z := e.right_inv hzTarget
  have hyx : y = x := by
    calc
      y = e.symm z := rfl
      _ = x := hzx
  have hsource : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).source := by
    simpa only [e, extChartAt_source] using hySource
  let A : ℕ → Matrix (Fin n) (Fin n) ℂ := fun j =>
    smoothCorePerturbedChartMatrix ω₁ cover α (v j) i z
  let A_limit : Matrix (Fin n) (Fin n) ℂ := evaluatedPerturbedChartMatrix ω₁ α u i z
  have hA : Filter.Tendsto A Filter.atTop (𝓝 A_limit) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    let C : ℝ := ((n + 1 : ℝ≥0) : ℝ)
    have hC : 0 ≤ C := by positivity
    have hsmall : ∀ᶠ j in Filter.atTop,
        ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
          (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖ < ε / (C + 1) :=
      hinputnorm.eventually (isOpen_Iio.mem_nhds (div_pos hε (by linarith [hC])))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
    refine ⟨N, fun j hj => ?_⟩
    rw [dist_eq_norm]
    calc
      ‖A j - A_limit‖ ≤ C *
          ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
            (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖ := by
        simpa [A, A_limit, C] using hclose j i z hzPiece
      _ < ε := by
        have hh := hN j hj
        have hCplus : 0 < C + 1 := by linarith
        calc
          C * ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
              (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖ ≤
            (C + 1) * ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
              (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖ := by
                gcongr ; linarith [hC]
          _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hh hCplus
          _ = ε := mul_div_cancel₀ ε hCplus.ne'
  let d : ℝ := RCLike.re (ω₁.metricInChart (cover.base i) z).det
  have hd : 0 < d := by
    dsimp [d]
    exact (RCLike.pos_iff.mp (ω₁.posDef_metricInChart (cover.base i) hzTarget).det_pos).1
  have hdet : Filter.Tendsto (fun j => RCLike.re (A j).det) Filter.atTop
      (𝓝 (RCLike.re A_limit.det)) := by
    have hdet0 : Continuous (fun B : Matrix (Fin n) (Fin n) ℂ => B.det) :=
      continuous_id.matrix_det
    exact (RCLike.continuous_re.continuousAt.tendsto).comp
      ((hdet0.continuousAt.tendsto).comp hA)
  have hratio : Filter.Tendsto (fun j => RCLike.re (A j).det / d) Filter.atTop
      (𝓝 (RCLike.re A_limit.det / d)) := by
    exact ((continuous_id.div_const d).continuousAt.tendsto).comp hdet
  have hrpos : 0 < RCLike.re A_limit.det / d := by
    have hchart := ω₁.mongeAmpere_eq_inChart_of_contMDiff_two hψ
      (cover.base i) hsource
    rw [hzy] at hchart
    have hAeq : ω₁.mongeAmpere ψ y = RCLike.re A_limit.det / d := by
      simpa [A_limit, d, evaluatedPerturbedChartMatrix] using hchart
    rw [← hAeq]
    exact hMApos y
  have hlog : Filter.Tendsto (fun j => Real.log (RCLike.re (A j).det / d)) Filter.atTop
      (𝓝 (Real.log (RCLike.re A_limit.det / d))) := by
    have hcont : ContinuousAt (fun B : Matrix (Fin n) (Fin n) ℂ =>
        Real.log (RCLike.re B.det / d)) A_limit := by
      have hratioCont : ContinuousAt (fun B : Matrix (Fin n) (Fin n) ℂ =>
          RCLike.re B.det / d) A_limit := by fun_prop
      have hlogCont : ContinuousAt Real.log (RCLike.re A_limit.det / d) :=
        Real.continuousAt_log hrpos.ne'
      exact ContinuousAt.comp (f := fun B : Matrix (Fin n) (Fin n) ℂ =>
        RCLike.re B.det / d) (g := Real.log) hlogCont hratioCont
    exact hcont.tendsto.comp hA
  have hψj (j : ℕ) : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
      (fun y => (v j).smoothMap y) := by
    have hcore : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (v j).smoothMap :=
      (v j).smoothMap.contMDiff
    exact hcore.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hMAj (j : ℕ) : ω₁.mongeAmpere (fun y => (v j).smoothMap y) y =
      RCLike.re (A j).det / d := by
    have hchart := ω₁.mongeAmpere_eq_inChart_of_contMDiff_two (hψj j)
      (cover.base i) hsource
    rw [hzy] at hchart
    simpa [A, d, smoothCorePerturbedChartMatrix] using hchart
  have hratioj (j : ℕ) :
      ω₀.mongeAmpere (φ + fun y => (v j).smoothMap y) y /
        ω₀.mongeAmpere φ y = RCLike.re (A j).det / d := by
    rw [hcocycle (fun y => (v j).smoothMap y) (hψj j) y, hMAj j]
    have hden : ω₀.mongeAmpere φ y ≠ 0 :=
      (ω₀.mongeAmpere_pos hsol.1 y).ne'
    field_simp
  have hratioLimit : ω₀.mongeAmpere (φ + ψ) y / ω₀.mongeAmpere φ y =
      RCLike.re A_limit.det / d := by
    rw [hcocycle ψ hψ y]
    have hchart := ω₁.mongeAmpere_eq_inChart_of_contMDiff_two hψ
      (cover.base i) hsource
    rw [hzy] at hchart
    have hAeq : ω₁.mongeAmpere ψ y = RCLike.re A_limit.det / d := by
      simpa [A_limit, d, evaluatedPerturbedChartMatrix] using hchart
    rw [hAeq]
    have hden : ω₀.mongeAmpere φ y ≠ 0 :=
      (ω₀.mongeAmpere_pos hsol.1 y).ne'
    field_simp
  let p : ℝ := δ * F y + (ω₀.pathConstant F (t + δ) - ω₀.pathConstant F t)
  have hseq (j : ℕ) : g j y = Real.log (RCLike.re (A j).det / d) - p := by
    rw [houtput j y]
    simp only [uncenteredContinuityPathResidual]
    rw [hratioj j]
  have hlimit : uncenteredContinuityPathResidual ω₀ F t φ hsol ψ δ y =
      Real.log (RCLike.re A_limit.det / d) - p := by
    simp only [uncenteredContinuityPathResidual]
    rw [hratioLimit]
  have hseqfun : (fun j => g j y) =
      (fun j => Real.log (RCLike.re (A j).det / d) - p) := funext hseq
  have ht : Filter.Tendsto (fun j => g j y) Filter.atTop
      (𝓝 (uncenteredContinuityPathResidual ω₀ F t φ hsol ψ δ y)) := by
    rw [hseqfun, hlimit]
    exact hlog.sub_const p
  simpa [hyx] using ht

end KahlerForm
