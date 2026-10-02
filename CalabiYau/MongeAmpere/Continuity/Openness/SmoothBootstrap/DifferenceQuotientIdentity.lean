module

public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.ChartLogDetEquation
public import CalabiYau.Mathlib.Analysis.Matrix.PosDef.LogDet
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact equation for translated Monge–Ampère quotients

For a fixed nonzero step, the log-determinant fundamental-theorem-of-calculus identity gives the
linear equation with the segment-average inverse coefficient.  The translated difference quotient
itself remains `C²`; no regularity is asserted for the limiting first derivative here.
-/

@[expose] public section

open scoped ComplexOrder Manifold ContDiff NNReal Topology Matrix.Norms.Elementwise
open Matrix Set MeasureTheory

namespace KahlerForm

private theorem posDef_segment {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hC : C.PosDef) {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    (A + s • (C - A)).PosDef := by
  have hcomb : A + s • (C - A) = (1 - s) • A + s • C := by
    ext i j
    simp
    ring
  rw [hcomb]
  by_cases hs0 : s = 0
  · simp [hs0]
    exact hA
  · by_cases hs1 : s = 1
    · simp [hs1]
      exact hC
    · have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
      have hpos : 0 < 1 - s := sub_pos.mpr hslt
      exact (hA.smul hpos).add_posSemidef (hC.posSemidef.smul hs.1)

private theorem complexHessian_translate {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z c : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f (z + c)) :
    complexHessian (fun w ↦ f (w + c)) z = complexHessian f (z + c) := by
  let ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun w ↦ w + c
  have hψ : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w := by
    filter_upwards with w
    exact differentiableAt_id.add_const c
  have hψderiv : fderiv ℂ ψ z = ContinuousLinearMap.id ℂ _ := by
    dsimp [ψ]
    simp
  change (ddbar (f ∘ ψ) z).coeffMatrix =
    (ddbar f (z + c)).coeffMatrix
  rw [ddbar_comp_holomorphic hψ hf, hψderiv]
  rw [(isOneOne_ddbar hf).coeffMatrix_compContinuousLinearMap
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n)))]
  have hclm : EuclideanSpace.clmMatrix
      (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) = 1 := by
    ext i j
    simp [EuclideanSpace.clmMatrix, Matrix.one_apply]
  simp [hclm]

private theorem logDet_segment_secant {n : ℕ} (A C : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hC : C.PosDef) :
    Real.log (RCLike.re C.det) - Real.log (RCLike.re A.det) =
      ∫ s in (0 : ℝ)..1,
        RCLike.re ((A + s • (C - A))⁻¹ * (C - A)).trace := by
  let D : Matrix (Fin n) (Fin n) ℂ := C - A
  let P : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s ↦ A + s • D
  let F : ℝ → ℝ := fun s ↦ Real.log (RCLike.re (P s).det)
  let F' : ℝ → ℝ := fun s ↦ RCLike.re ((P s)⁻¹ * D).trace
  have hP : ∀ s ∈ Set.uIcc (0 : ℝ) 1, (P s).PosDef := by
    intro s hs
    change (A + s • (C - A)).PosDef
    exact posDef_segment A C hA hC (by simpa [uIcc, Icc] using hs)
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (F' s) s := by
    intro s hs
    have hPs := hP s hs
    have h0 := Matrix.PosDef.hasDerivAt_log_det_add_smul hPs D
    have hshift : HasDerivAt (fun t : ℝ ↦ t - s) 1 s := by
      simpa using (hasDerivAt_id s).sub_const s
    have hcomp := h0.comp_of_eq s hshift (by simp)
    have hpath (t : ℝ) : P s + (t - s) • D = P t := by
      dsimp [P]
      module
    have heq :
        (fun t : ℝ ↦ Real.log (RCLike.re (P s + (t - s) • D).det)) = F := by
      funext t
      rw [hpath]
    change HasDerivAt
      (fun t : ℝ ↦ Real.log (RCLike.re (P s + (t - s) • D).det))
      (RCLike.re ((P s)⁻¹ * D).trace * 1) s at hcomp
    rw [heq] at hcomp
    simpa [F, F', one_mul] using hcomp
  have hcont : ContinuousOn F' (Set.uIcc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
    intro s
    have hs : (s : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := s.property
    have hPs := hP s hs
    have hdetunit : IsUnit (P s).det := (ne_of_gt hPs.det_pos).isUnit
    have hInv : ContinuousAt (fun t : ℝ ↦ (P t)⁻¹) s := by
      apply (Matrix.contDiffAt_inv hdetunit).continuousAt.comp
      fun_prop
    have hF' : ContinuousAt F' s := by
      dsimp [F']
      fun_prop
    exact hF'.comp continuousAt_subtype_val
  have hint : IntervalIntegrable F' MeasureTheory.volume 0 1 := hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hFend : F 1 - F 0 =
      Real.log (RCLike.re C.det) - Real.log (RCLike.re A.det) := by
    simp [F, P, D]
  rw [← hFend]
  exact hFTC.symm

private theorem inverse_segment_entries_intervalIntegrable {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hC : C.PosDef) :
    ∀ i j, IntervalIntegrable
      (fun s ↦ (A + s • (C - A))⁻¹ i j) MeasureTheory.volume 0 1 := by
  intro i j
  let P : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s ↦ A + s • (C - A)
  have hdetCont : ContinuousOn (fun s : ℝ ↦ (P s).det) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hdetNe : ∀ s ∈ Set.Icc (0 : ℝ) 1, (P s).det ≠ 0 := by
    intro s hs
    have hpos := posDef_segment A C hA hC hs
    exact ne_of_gt hpos.det_pos
  have hdetInv : ContinuousOn (fun s : ℝ ↦ ((P s).det)⁻¹) (Set.Icc (0 : ℝ) 1) :=
    hdetCont.inv₀ hdetNe
  have hAdj : ContinuousOn (fun s : ℝ ↦ (P s).adjugate i j) (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hformula (s : ℝ) : (P s)⁻¹ i j = ((P s).det)⁻¹ * (P s).adjugate i j := by
    rw [Matrix.inv_def]
    simp [smul_eq_mul, Ring.inverse_eq_inv]
  have hentry := hdetInv.mul hAdj
  have hcontinuous : ContinuousOn (fun s : ℝ ↦ (P s)⁻¹ i j) (Set.Icc (0 : ℝ) 1) := by
    refine hentry.congr ?_
    intro s hs
    exact hformula s
  exact hcontinuous.intervalIntegrable_of_Icc (by norm_num)

private theorem trace_intervalIntegral_matrix_mul {n : ℕ}
    (F : ℝ → Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, IntervalIntegrable (fun s ↦ F s i j) MeasureTheory.volume 0 1) :
    (let I : Matrix (Fin n) (Fin n) ℂ := fun i j ↦ ∫ s in (0 : ℝ)..1, F s i j
     (I * D).trace) =
      ∫ s in (0 : ℝ)..1, (F s * D).trace := by
  classical
  change (∑ i, ∑ j, (∫ s in (0 : ℝ)..1, F s i j) * D j i) =
    ∫ s in (0 : ℝ)..1, ∑ i, ∑ j, F s i j * D j i
  calc
    (∑ i, ∑ j, (∫ s in (0 : ℝ)..1, F s i j) * D j i) =
        ∑ i, ∫ s in (0 : ℝ)..1, ∑ j, F s i j * D j i := by
      congr 1
      funext i
      simpa only [intervalIntegral.integral_mul_const] using
        (intervalIntegral.integral_finsetSum
          (s := Finset.univ)
          (f := fun j s ↦ F s i j * D j i)
          (fun j hj ↦ (hF i j).mul_const (D j i))).symm
    _ = ∫ s in (0 : ℝ)..1, ∑ i, ∑ j, F s i j * D j i := by
      exact (intervalIntegral.integral_finsetSum
        (s := Finset.univ)
        (f := fun i s ↦ ∑ j, F s i j * D j i)
        (fun i hi ↦ by
          have hsum := IntervalIntegrable.sum Finset.univ
            (fun j hj ↦ (hF i j).mul_const (D j i))
          have heq : (∑ j, fun s : ℝ ↦ F s i j * D j i) =
              (fun s ↦ ∑ j, F s i j * D j i) := by
            funext s
            simp
          rw [← heq]
          exact hsum)).symm

private theorem re_trace_intervalIntegral_matrix_mul {n : ℕ}
    (F : ℝ → Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, IntervalIntegrable (fun s ↦ F s i j) MeasureTheory.volume 0 1) :
    (let I : Matrix (Fin n) (Fin n) ℂ := fun i j ↦ ∫ s in (0 : ℝ)..1, F s i j
     RCLike.re (I * D).trace) =
      ∫ s in (0 : ℝ)..1, RCLike.re (F s * D).trace := by
  have htrace : IntervalIntegrable (fun s : ℝ ↦ (F s * D).trace)
      MeasureTheory.volume 0 1 := by
    change IntervalIntegrable (fun s ↦ ∑ i, ∑ j, F s i j * D j i)
      MeasureTheory.volume 0 1
    have hrow (i : Fin n) :
        IntervalIntegrable (fun s : ℝ ↦ ∑ j, F s i j * D j i)
          MeasureTheory.volume 0 1 := by
      have hsum := IntervalIntegrable.sum Finset.univ
        (fun j hj ↦ (hF i j).mul_const (D j i))
      have heq : (∑ j, fun s : ℝ ↦ F s i j * D j i) =
          (fun s ↦ ∑ j, F s i j * D j i) := by
        funext s
        simp
      rw [← heq]
      exact hsum
    have hsum := IntervalIntegrable.sum Finset.univ (fun i hi ↦ hrow i)
    have heq : (∑ i, fun s : ℝ ↦ ∑ j, F s i j * D j i) =
        (fun s ↦ ∑ i, ∑ j, F s i j * D j i) := by
      funext s
      simp
    rw [← heq]
    exact hsum
  calc
    RCLike.re (let I : Matrix (Fin n) (Fin n) ℂ := fun i j ↦ ∫ s in (0 : ℝ)..1, F s i j
      (I * D).trace) = RCLike.re (∫ s in (0 : ℝ)..1, (F s * D).trace) := by
        exact congrArg RCLike.re (trace_intervalIntegral_matrix_mul F D hF)
    _ = ∫ s in (0 : ℝ)..1, RCLike.re (F s * D).trace := by
      exact (RCLike.reCLM).intervalIntegral_comp_comm htrace |>.symm

private noncomputable def matrixSegmentAverageInverse {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ ∫ s in (0 : ℝ)..1, (A + s • (C - A))⁻¹ i j

private theorem logDet_segment_secant_avgInverse {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hC : C.PosDef) :
    Real.log (RCLike.re C.det) - Real.log (RCLike.re A.det) =
      RCLike.re (matrixSegmentAverageInverse A C * (C - A)).trace := by
  have hF := inverse_segment_entries_intervalIntegrable A C hA hC
  calc
    Real.log (RCLike.re C.det) - Real.log (RCLike.re A.det) =
        ∫ s in (0 : ℝ)..1, RCLike.re ((A + s • (C - A))⁻¹ * (C - A)).trace :=
      logDet_segment_secant A C hA hC
    _ = RCLike.re (matrixSegmentAverageInverse A C * (C - A)).trace := by
      exact (re_trace_intervalIntegral_matrix_mul
        (fun s ↦ (A + s • (C - A))⁻¹) (C - A) hF).symm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The matrix of the perturbed Kähler form in the chart based at `x`. -/
noncomputable def chartBootstrapMatrix (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (z : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  ω₀.metricInChart x z +
    complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z

/-- Averaged inverse of the positive matrices on the segment from `B(z)` to `B(z + h v)`.
The integral is entrywise because `Matrix` has no normed-group structure in this development. -/
noncomputable def averagedChartInverse (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (v : EuclideanSpace ℂ (Fin n)) (h : ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun j l ↦ ∫ s in (0 : ℝ)..1,
    (chartBootstrapMatrix ω₀ φ x z + s •
      (chartBootstrapMatrix ω₀ φ x (z + h • v) - chartBootstrapMatrix ω₀ φ x z))⁻¹ j l

/-- Matrix difference quotient, interpreted entrywise over `ℂ`. -/
noncomputable def chartMatrixDifferenceQuotient {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (h : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j l ↦ (B j l - A j l) / (h : ℂ)

section

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

private theorem logDet_segment_differenceQuotient {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hC : C.PosDef) (h : ℝ) :
    (Real.log (RCLike.re C.det) - Real.log (RCLike.re A.det)) / h =
      RCLike.re (matrixSegmentAverageInverse A C *
        chartMatrixDifferenceQuotient A C h).trace := by
  have hsec := logDet_segment_secant_avgInverse A C hA hC
  have hDQ : chartMatrixDifferenceQuotient A C h =
      (h⁻¹ : ℂ) • (C - A) := by
    ext i j
    simp [chartMatrixDifferenceQuotient, div_eq_mul_inv, smul_eq_mul, mul_comm]
  calc
    (Real.log (RCLike.re C.det) - Real.log (RCLike.re A.det)) / h =
        h⁻¹ * (Real.log (RCLike.re C.det) - Real.log (RCLike.re A.det)) := by
      simp [div_eq_mul_inv, mul_comm]
    _ = h⁻¹ * RCLike.re (matrixSegmentAverageInverse A C * (C - A)).trace := by
      rw [hsec]
    _ = RCLike.re ((h⁻¹ : ℂ) *
        (matrixSegmentAverageInverse A C * (C - A)).trace) := by
      simp [RCLike.mul_re]
    _ = RCLike.re (matrixSegmentAverageInverse A C *
        ((h⁻¹ : ℂ) • (C - A))).trace := by
      congr 1
      simp [Matrix.trace_smul]
    _ = RCLike.re (matrixSegmentAverageInverse A C *
        chartMatrixDifferenceQuotient A C h).trace := by
      rw [← hDQ]

private theorem complexHessian_differenceQuotient {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z c : EuclideanSpace ℂ (Fin n))
    (h : ℝ) (hfz : ContDiffAt ℝ 2 f z) (hfc : ContDiffAt ℝ 2 f (z + c)) :
    complexHessian (fun w ↦ (f (w + c) - f w) / h) z =
      chartMatrixDifferenceQuotient (complexHessian f z) (complexHessian f (z + c)) h := by
  have hshift : ContDiffAt ℝ 2 (fun w ↦ f (w + c)) z := by
    have hc : ContDiffAt ℝ 2 (fun w : EuclideanSpace ℂ (Fin n) ↦ w + c) z := by
      fun_prop
    exact hfc.comp z hc
  let g : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ f (w + c) - f w
  have htranslate : (ddbar (fun w ↦ f (w + c)) z).coeffMatrix =
      complexHessian f (z + c) := by
    simpa [complexHessian] using complexHessian_translate f z c hfc
  have hsub : complexHessian g z =
      complexHessian f (z + c) - complexHessian f z := by
    change (ddbar ((fun w ↦ f (w + c)) - f) z).coeffMatrix = _
    rw [ddbar_sub hshift hfz, ContinuousAlternatingMap.coeffMatrix_sub, htranslate]
    simp [complexHessian]
  have hquot : (fun w ↦ (f (w + c) - f w) / h) = (h⁻¹ : ℝ) • g := by
    funext w
    simp [g, div_eq_mul_inv, smul_eq_mul, mul_comm]
  have hsmul : complexHessian ((h⁻¹ : ℝ) • g) z =
      (h⁻¹ : ℝ) • complexHessian g z := by
    change (ddbar ((h⁻¹ : ℝ) • g) z).coeffMatrix =
      (h⁻¹ : ℝ) • (ddbar g z).coeffMatrix
    rw [ddbar_smul (hshift.sub hfz) h⁻¹, ContinuousAlternatingMap.coeffMatrix_smul]
  rw [hquot, hsmul, hsub]
  ext i j
  simp [chartMatrixDifferenceQuotient, div_eq_mul_inv, mul_comm]

end

private theorem translatedPotentialQuotient_contDiffOn
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (x : M) (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUtarget : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) (h : ℝ)
    (htranslated : ∀ z ∈ U, z + h • v ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ContDiffOn ℝ 2
      (fun z ↦
        ((φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) (z + h • v) -
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) / h) U := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f : EuclideanSpace ℂ (Fin n) → ℝ := φ ∘ e.symm
  let T : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun z ↦ z + h • v
  have hf : ContDiffOn ℝ 2 f e.target := by
    have hφOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ Set.univ :=
      contMDiffOn_univ.mpr hφ.1.1
    have hchart := hφOn.comp (contMDiffOn_extChartAt_symm x)
      (by intro z hz; simp)
    exact hchart.contDiffOn
  have hT : ContDiff ℝ 2 T := by
    dsimp [T]
    fun_prop
  have htranslated' : Set.MapsTo T U e.target := by
    intro z hz
    exact htranslated z hz
  have hshift : ContDiffOn ℝ 2 (f ∘ T) U :=
    hf.comp hT.contDiffOn htranslated'
  have hbase : ContDiffOn ℝ 2 f U :=
    hf.mono ((subset_closure : U ⊆ closure U).trans hUtarget)
  have hq : ContDiffOn ℝ 2 (fun z ↦ (f (T z) - f z) / h) U := by
    have hdiff := hshift.sub hbase
    have hconst : ContDiffOn ℝ 2 (fun _ : EuclideanSpace ℂ (Fin n) ↦ (h : ℝ)⁻¹) U :=
      contDiffOn_const
    simpa [div_eq_mul_inv] using hdiff.mul hconst
  simpa [e, f, T] using hq

/-- The known forcing term after moving the metric difference to the right of the linear equation.
The first quotient is that of the prescribed log-volume data and background log volume; the second
term removes the background metric Hessian from the averaged trace. -/
noncomputable def chartDifferenceQuotientRhs (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (x : M) (v : EuclideanSpace ℂ (Fin n)) (h : ℝ) :
    EuclideanSpace ℂ (Fin n) → ℝ := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let g (z : EuclideanSpace ℂ (Fin n)) := ω₀.metricInChart x z
  let A (z : EuclideanSpace ℂ (Fin n)) := averagedChartInverse ω₀ φ x v h z
  exact fun z ↦
    (G (e.symm (z + h • v)) - G (e.symm z) +
      Real.log (RCLike.re (g (z + h • v)).det) - Real.log (RCLike.re (g z).det)) / h -
      RCLike.re (A z * chartMatrixDifferenceQuotient (g z) (g (z + h • v)) h).trace

/-- Exact local difference-quotient equation: the log-determinant secant equals contraction with
its averaged inverse, the translated quotient is `C²`, and the equation for that quotient has the
explicit metric/data forcing. -/
def HasExactDifferenceQuotientData (ω₀ : KahlerForm n M) (G φ : M → ℝ) : Prop :=
  ∀ x : M,
    ∀ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → IsCompact (closure U) →
      closure U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target →
      ∀ v : EuclideanSpace ℂ (Fin n), ∀ h : ℝ, h ≠ 0 →
        (∀ z ∈ U, z + h • v ∈
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) →
          let B z := chartBootstrapMatrix ω₀ φ x z
          let A z := averagedChartInverse ω₀ φ x v h z
          let q z :=
            ((φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) (z + h • v) -
              (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) / h
          ContDiffOn ℝ 2 q U ∧
            (∀ z ∈ U,
              (Real.log (RCLike.re (B (z + h • v)).det) -
                Real.log (RCLike.re (B z).det)) / h =
                RCLike.re (A z * chartMatrixDifferenceQuotient (B z) (B (z + h • v)) h).trace) ∧
            ∀ z ∈ U, complexEllipticOp A q z =
              chartDifferenceQuotientRhs ω₀ G φ x v h z

private theorem chartMatrix_logDet_differenceQuotient
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    (x : M) (z : EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) (h : ℝ)
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hz' : z + h • v ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (Real.log (RCLike.re
        (chartBootstrapMatrix ω₀ φ x (z + h • v)).det) -
      Real.log (RCLike.re (chartBootstrapMatrix ω₀ φ x z).det)) / h =
      RCLike.re ((averagedChartInverse ω₀ φ x v h z) *
        chartMatrixDifferenceQuotient (chartBootstrapMatrix ω₀ φ x z)
          (chartBootstrapMatrix ω₀ φ x (z + h • v)) h).trace := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let g (w : EuclideanSpace ℂ (Fin n)) := ω₀.metricInChart x w
  let B (w : EuclideanSpace ℂ (Fin n)) := chartBootstrapMatrix ω₀ φ x w
  have hEq₀ := hEquation x z hz
  have hEq₁ := hEquation x (z + h • v) hz'
  have hB₀herm : (B z).IsHermitian := by
    simpa [B, chartBootstrapMatrix] using hEq₀.1
  have hB₁herm : (B (z + h • v)).IsHermitian := by
    simpa [B, chartBootstrapMatrix] using hEq₁.1
  have hB₀quad : ∀ w : Fin n → ℂ, w ≠ 0 →
      0 < RCLike.re (star w ⬝ᵥ (B z *ᵥ w)) := by
    simpa [B, chartBootstrapMatrix] using hEq₀.2.1
  have hB₁quad : ∀ w : Fin n → ℂ, w ≠ 0 →
      0 < RCLike.re (star w ⬝ᵥ (B (z + h • v) *ᵥ w)) := by
    simpa [B, chartBootstrapMatrix] using hEq₁.2.1
  have hB₀pos : (B z).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hB₀herm
    intro w hw
    exact RCLike.lt_iff_re_im.mpr
      ⟨hB₀quad w hw, (hB₀herm.im_star_dotProduct_mulVec_self w).symm⟩
  have hB₁pos : (B (z + h • v)).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hB₁herm
    intro w hw
    exact RCLike.lt_iff_re_im.mpr
      ⟨hB₁quad w hw, (hB₁herm.im_star_dotProduct_mulVec_self w).symm⟩
  have hAvg : averagedChartInverse ω₀ φ x v h z =
      matrixSegmentAverageInverse (B z) (B (z + h • v)) := by
    ext i j
    rfl
  rw [hAvg]
  simpa [B, g, e, chartBootstrapMatrix] using
    (logDet_segment_differenceQuotient (B z) (B (z + h • v)) hB₀pos hB₁pos h)

/-- The `C²` Monge–Ampère equation yields its exact nonzero difference-quotient equation and
`C²` regularity of each quotient. -/
theorem solvesMongeAmpereC2_hasExactDifferenceQuotientData
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ) :
    HasExactDifferenceQuotientData ω₀ G φ := by
  intro x U hU hUcompact hUtarget v h hne htranslated
  refine ⟨translatedPotentialQuotient_contDiffOn ω₀ hφ x U hUtarget v h htranslated, ?_⟩
  have hsecantAll : ∀ z ∈ U,
      (Real.log (RCLike.re
          (chartBootstrapMatrix ω₀ φ x (z + h • v)).det) -
        Real.log (RCLike.re (chartBootstrapMatrix ω₀ φ x z).det)) / h =
        RCLike.re ((averagedChartInverse ω₀ φ x v h z) *
          chartMatrixDifferenceQuotient (chartBootstrapMatrix ω₀ φ x z)
            (chartBootstrapMatrix ω₀ φ x (z + h • v)) h).trace := by
    intro z hz
    exact chartMatrix_logDet_differenceQuotient ω₀ hEquation x z v h
      (hUtarget ((subset_closure : U ⊆ closure U) hz)) (htranslated z hz)
  refine ⟨hsecantAll, ?_⟩
  intro z hz
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f : EuclideanSpace ℂ (Fin n) → ℝ := φ ∘ e.symm
  let g₀ := ω₀.metricInChart x z
  let g₁ := ω₀.metricInChart x (z + h • v)
  let H₀ := complexHessian f z
  let H₁ := complexHessian f (z + h • v)
  let B₀ := chartBootstrapMatrix ω₀ φ x z
  let B₁ := chartBootstrapMatrix ω₀ φ x (z + h • v)
  let A₀ := averagedChartInverse ω₀ φ x v h z
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦
    (f (w + h • v) - f w) / h
  have hztarget : z ∈ e.target :=
    hUtarget ((subset_closure : U ⊆ closure U) hz)
  have hz'target : z + h • v ∈ e.target := htranslated z hz
  have hEquation₀ := hEquation x z hztarget
  have hEquation₁ := hEquation x (z + h • v) hz'target
  have hB₀herm : B₀.IsHermitian := by
    simpa [B₀, chartBootstrapMatrix, f, e] using hEquation₀.1
  have hB₁herm : B₁.IsHermitian := by
    simpa [B₁, chartBootstrapMatrix, f, e] using hEquation₁.1
  have hB₀quad : ∀ w : Fin n → ℂ, w ≠ 0 →
      0 < RCLike.re (star w ⬝ᵥ (B₀ *ᵥ w)) := by
    simpa [B₀, chartBootstrapMatrix, f, e] using hEquation₀.2.1
  have hB₁quad : ∀ w : Fin n → ℂ, w ≠ 0 →
      0 < RCLike.re (star w ⬝ᵥ (B₁ *ᵥ w)) := by
    simpa [B₁, chartBootstrapMatrix, f, e] using hEquation₁.2.1
  have hB₀pos : B₀.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hB₀herm
    intro w hw
    exact RCLike.lt_iff_re_im.mpr
      ⟨hB₀quad w hw, (hB₀herm.im_star_dotProduct_mulVec_self w).symm⟩
  have hB₁pos : B₁.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hB₁herm
    intro w hw
    exact RCLike.lt_iff_re_im.mpr
      ⟨hB₁quad w hw, (hB₁herm.im_star_dotProduct_mulVec_self w).symm⟩
  have hlog₀ : Real.log (RCLike.re B₀.det) =
      G (e.symm z) + Real.log (RCLike.re g₀.det) := by
    simpa [B₀, g₀, chartBootstrapMatrix, f, e] using hEquation₀.2.2
  have hlog₁ : Real.log (RCLike.re B₁.det) =
      G (e.symm (z + h • v)) + Real.log (RCLike.re g₁.det) := by
    simpa [B₁, g₁, chartBootstrapMatrix, f, e] using hEquation₁.2.2
  have hlogSecant := hsecantAll z hz
  have hHessian₀ : ContDiffOn ℝ 2 f e.target := by
    have hφOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ Set.univ :=
      contMDiffOn_univ.mpr hφ.1.1
    have hchart := hφOn.comp (contMDiffOn_extChartAt_symm x)
      (by intro w hw; simp)
    exact hchart.contDiffOn
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  have hfz : ContDiffAt ℝ 2 f z :=
    (hHessian₀ z hztarget).contDiffAt (hopen.mem_nhds hztarget)
  have hfz' : ContDiffAt ℝ 2 f (z + h • v) :=
    (hHessian₀ (z + h • v) hz'target).contDiffAt (hopen.mem_nhds hz'target)
  have hHessianQ : complexHessian q z =
      chartMatrixDifferenceQuotient H₀ H₁ h := by
    exact complexHessian_differenceQuotient f z (h • v) h hfz hfz'
  have hDQsplit : chartMatrixDifferenceQuotient B₀ B₁ h =
      chartMatrixDifferenceQuotient g₀ g₁ h +
        chartMatrixDifferenceQuotient H₀ H₁ h := by
    ext i j
    simp [chartMatrixDifferenceQuotient, B₀, B₁, g₀, g₁, H₀, H₁,
      chartBootstrapMatrix, f, e]
    ring
  have htraceSplit : RCLike.re (A₀ * chartMatrixDifferenceQuotient B₀ B₁ h).trace =
      RCLike.re (A₀ * chartMatrixDifferenceQuotient g₀ g₁ h).trace +
        RCLike.re (A₀ * chartMatrixDifferenceQuotient H₀ H₁ h).trace := by
    rw [hDQsplit, Matrix.mul_add, Matrix.trace_add]
    simp
  have hoperator : complexEllipticOp (fun _ ↦ A₀) q z =
      RCLike.re (A₀ * chartMatrixDifferenceQuotient H₀ H₁ h).trace := by
    simp [complexEllipticOp, hHessianQ]
  have hlogIdentity : Real.log (RCLike.re B₁.det) - Real.log (RCLike.re B₀.det) =
      G (e.symm (z + h • v)) - G (e.symm z) +
        Real.log (RCLike.re g₁.det) - Real.log (RCLike.re g₀.det) := by
    rw [hlog₁, hlog₀]
    ring
  have hforce : complexEllipticOp (fun _ ↦ A₀) q z =
      (G (e.symm (z + h • v)) - G (e.symm z) +
        Real.log (RCLike.re g₁.det) - Real.log (RCLike.re g₀.det)) / h -
        RCLike.re (A₀ * chartMatrixDifferenceQuotient g₀ g₁ h).trace := by
    have htraceH : RCLike.re (A₀ * chartMatrixDifferenceQuotient H₀ H₁ h).trace =
        RCLike.re (A₀ * chartMatrixDifferenceQuotient B₀ B₁ h).trace -
          RCLike.re (A₀ * chartMatrixDifferenceQuotient g₀ g₁ h).trace := by
      linarith [htraceSplit]
    rw [hoperator, htraceH, ← hlogSecant, hlogIdentity]
  simpa [complexEllipticOp, chartDifferenceQuotientRhs, A₀, g₀, g₁, e, q, f] using hforce

end KahlerForm
