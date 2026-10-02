module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.Basic
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.ChartMatrixControl
import CalabiYau.LinearAlgebra.Hermitian.LogDetDeriv

/-!
# Common positive matrix-segment controls near the actual positive limit

Compactness of the strictly positive C² limit gives a finite inverse bound; uniform matrix
closeness gives a common tail. All matrix norms are Frobenius. The compact Elementwise inverse estimate requires an explicit finite-dimensional norm/continuity bridge.
The α<1 hypothesis is used for the compact smooth-background Hölder bound. Spatial chart pieces
need not be convex: only the positive matrix segments are integrated.
-/

public section

open scoped Manifold ContDiff NNReal Topology ComplexOrder
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The entrywise formula for the Frobenius norm, kept explicit while using matrix inverse
continuity in Mathlib's elementwise matrix topology. -/
private noncomputable def finiteFrobeniusNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ (2 : ℕ))

section ElementwiseInverse

open scoped Matrix.Norms.Elementwise

/-- In the Frobenius matrix norm, the elementwise inverse-continuity neighborhood gives a finite
uniform inverse bound. The explicit sum-of-squares estimate is the norm bridge; no silent
identification of Mathlib's two matrix norm instances is used. -/
private theorem frobenius_inverse_norm_eventually_bounded
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : Matrix (Fin n) (Fin n) ℂ in 𝓝 A,
      finiteFrobeniusNorm (B⁻¹) ≤ K := by
  have hcont : ContinuousAt (fun B : Matrix (Fin n) (Fin n) ℂ => B⁻¹) A :=
    (Matrix.contDiffAt_inv (hA.det_pos.ne').isUnit).continuousAt
  have hnear : ∀ᶠ B : Matrix (Fin n) (Fin n) ℂ in 𝓝 A,
      dist (B⁻¹) A⁻¹ < 1 :=
    hcont.eventually (Metric.ball_mem_nhds _ (by norm_num))
  let C : ℝ := ‖A⁻¹‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨(n : ℝ) * C + 1, by positivity, ?_⟩
  filter_upwards [hnear] with B hB
  have hdiff : ‖B⁻¹ - A⁻¹‖ < 1 := by simpa [dist_eq_norm] using hB
  have hentry (i j : Fin n) : ‖B⁻¹ i j‖ ≤ C := by
    calc
      ‖B⁻¹ i j‖ = ‖(B⁻¹ - A⁻¹) i j + A⁻¹ i j‖ := by congr 1; simp
      _ ≤ ‖(B⁻¹ - A⁻¹) i j‖ + ‖A⁻¹ i j‖ := norm_add_le _ _
      _ ≤ ‖B⁻¹ - A⁻¹‖ + ‖A⁻¹‖ :=
        add_le_add (Matrix.norm_entry_le_entrywise_sup_norm _)
          (Matrix.norm_entry_le_entrywise_sup_norm A⁻¹)
      _ ≤ C := by dsimp [C]; linarith
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n, ‖B⁻¹ i j‖ ^ (2 : ℕ)) ≤
        (n : ℝ) ^ 2 * C ^ 2 := by
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, C ^ (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        simpa [pow_two] using
          (mul_le_mul (hentry i j) (hentry i j) (norm_nonneg _) hC.le)
      _ = (n : ℝ) ^ 2 * C ^ 2 := by simp [Finset.sum_const]; ring
  have hbound : finiteFrobeniusNorm (B⁻¹) ≤ (n : ℝ) * C := by
    dsimp [finiteFrobeniusNorm]
    calc
      Real.sqrt (∑ i : Fin n, ∑ j : Fin n, ‖B⁻¹ i j‖ ^ (2 : ℕ)) ≤
          Real.sqrt ((n : ℝ) ^ 2 * C ^ 2) := Real.sqrt_le_sqrt hsum
      _ = (n : ℝ) * C := by
        rw [show (n : ℝ) ^ 2 * C ^ 2 = ((n : ℝ) * C) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  exact hbound.trans (by linarith)

/-- Compact families of positive matrices have a common finite Frobenius inverse bound. The
inverse is continuous in Mathlib's elementwise matrix topology, while the finite sum-of-squares
function records the Frobenius bound explicitly. -/
private theorem compact_frobenius_inverse_bound
    {n : ℕ} {X : Type*} [TopologicalSpace X] {s : Set X}
    (f : X → Matrix (Fin n) (Fin n) ℂ) (hcompact : IsCompact s)
    (hf : ContinuousOn f s) (hpos : ∀ x ∈ s, (f x).PosDef) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ s, finiteFrobeniusNorm ((f x)⁻¹) ≤ K := by
  have hinv : ContinuousOn (fun x => (f x)⁻¹) s := by
    intro x hx
    have hcont := (Matrix.contDiffAt_inv (hpos x hx).det_pos.ne'.isUnit).continuousAt
    exact hcont.comp_continuousWithinAt (hf.continuousWithinAt hx)
  have hnormContinuous : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
      finiteFrobeniusNorm A) := by
    unfold finiteFrobeniusNorm
    fun_prop
  have hnorm : ContinuousOn (fun x => finiteFrobeniusNorm ((f x)⁻¹)) s := by
    intro x hx
    exact hnormContinuous.continuousAt.comp_continuousWithinAt (hinv.continuousWithinAt hx)
  obtain ⟨B, hB₀, hB⟩ := (hcompact.bddAbove_image hnorm).exists_ge 0
  refine ⟨B + 1, by linarith, ?_⟩
  intro x hx
  have hb := hB (finiteFrobeniusNorm ((f x)⁻¹)) ⟨x, hx, rfl⟩
  linarith

end ElementwiseInverse

section FrobeniusNorm

open scoped Matrix.Norms.Frobenius

/-- In the Frobenius norm instance, the explicit finite sum above is exactly the matrix norm. -/
private theorem finiteFrobeniusNorm_eq_norm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : finiteFrobeniusNorm A = ‖A‖ := by
  rw [Matrix.frobenius_norm_def]
  simp [finiteFrobeniusNorm, Real.sqrt_eq_rpow]

end FrobeniusNorm

section FrobeniusTail

open scoped Matrix.Norms.Frobenius

/-- The positive-definite cone is convex along a closed affine segment, including both endpoints. -/
private theorem affine_segment_posDef {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((1 - s) • A + s • B).PosDef := by
  by_cases hs0 : s = 0
  · simpa [hs0] using hA
  · by_cases hs1 : s = 1
    · simpa [hs1] using hB
    · have hleft : 0 < 1 - s :=
        lt_of_le_of_ne (sub_nonneg.mpr hs.2) (by intro h; apply hs1; linarith)
      have hright : 0 < s :=
        lt_of_le_of_ne hs.1 (by intro h; apply hs0; linarith)
      exact (hA.smul hleft).add (hB.smul hright)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- A positive smooth core perturbation gives the positive chart matrix on every chart target. -/
private theorem smoothCore_chart_matrix_posDef
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (v : SmoothChartHolderCore P.finiteChartCover 2 α)
    (hpositive : ω₀.IsC2Potential (φ + fun x => v.smoothMap x))
    (i : P.finiteChartCover.ι) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      (P.finiteChartCover.base i)).target) :
    (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α v i z).PosDef := by
  let ω₁ := ω₀.perturb φ hφ
  have hφ₂ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ :=
    hφ.1.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hv₂ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 v.smoothMap := by
    exact v.smoothMap.contMDiff.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hpot : ω₁.IsPotential v.smoothMap := by
    refine ⟨v.smoothMap.contMDiff, ?_⟩
    have hform : ω₁.toFormField + mddbar n v.smoothMap =
        ω₀.toFormField + mddbar n (φ + (v.smoothMap : M → ℝ)) := by
      change (ω₀.toFormField + mddbar n φ) + mddbar n v.smoothMap = _
      rw [add_assoc, ← mddbar_add_of_contMDiff_two hφ₂ hv₂]
    change (ω₁.toFormField + mddbar n v.smoothMap).IsPositive
    rw [hform]
    exact hpositive.2
  have hnew := (ω₁.perturb v.smoothMap hpot).posDef_metricInChart
    (P.finiteChartCover.base i) hz
  rw [KahlerForm.metricInChart_perturb hpot (P.finiteChartCover.base i) hz] at hnew
  simpa [ω₁, smoothCorePerturbedChartMatrix] using hnew

/-- Every pairwise affine segment of positive smooth chart matrices remains positive. -/
private theorem smoothCore_chartMatrix_segments_posDef
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hpositive : ∀ j, ω₀.IsC2Potential (φ + fun x => (v j).smoothMap x))
    (j k : ℕ) (i : P.finiteChartCover.ι) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ P.finiteChartCover.piece i) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z +
      s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z -
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z)).PosDef := by
  have hfirst := smoothCore_chart_matrix_posDef ω₀ φ hφ α (v j)
    (by simpa [Pi.add_apply] using hpositive j) i z
    (P.finiteChartCover.piece_in_target i hz)
  have hsecond := smoothCore_chart_matrix_posDef ω₀ φ hφ α (v k)
    (by simpa [Pi.add_apply] using hpositive k) i z
    (P.finiteChartCover.piece_in_target i hz)
  have heq :
      smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z +
        s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z -
          smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z) =
      (1 - s) • smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z +
        s • smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z := by
    module
  rw [heq]
  exact affine_segment_posDef _ _ s hfirst hsecond hs

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem c2Potential_chartRep_isPositive
    (θ : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hθ : ∀ x, (θ x).IsPositive) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (θ.chartRep x z).IsPositive := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  have hyx : y ∈ e.source := e.map_target hz
  have hyyℝ : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyx
  have hyyℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyℝ
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v) ⟨⟨hyxℂ, hyyℂ⟩, hyxℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxℂ
  have hAB : ∀ v, A (B v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v) ⟨⟨hyyℂ, hyxℂ⟩, hyyℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyℂ
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toLinearEquiv :=
        { toFun := A
          invFun := B
          left_inv := hBA
          right_inv := hAB
          map_add' := A.map_add
          map_smul' := A.map_smul }
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
    tangentCoordChange_real_eq ⟨hyx, hyyℝ⟩
  have hchart : θ.chartRep x z = (θ y).compContinuousLinearMap (A.restrictScalars ℝ) := by
    calc
      θ.chartRep x z = (θ y).compContinuousLinearMap
          (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) := rfl
      _ = (θ y).compContinuousLinearMap (A.restrictScalars ℝ) := by rw [hAreal]
  have hARestrict : (AEquiv.restrictScalars ℝ :
      EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) = A.restrictScalars ℝ := by
    ext v
    rfl
  rw [hchart]
  exact (hθ y).compContinuousLinearMap AEquiv

private theorem evaluated_chart_matrix_posDef
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (hpositiveLimit : ω₀.IsC2Potential (φ + P.evalC2 u))
    (i : P.finiteChartCover.ι) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ P.finiteChartCover.piece i) :
    (evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z).PosDef := by
  let ψ : M → ℝ := P.evalC2 u
  let ω₁ := ω₀.perturb φ hφ
  let x := P.finiteChartCover.base i
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hφ₂ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ :=
    hφ.1.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hψ₂ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ := by
    have h := hpositiveLimit.1.sub hφ₂
    have hEq : (φ + P.evalC2 u) - φ = P.evalC2 u := by funext y; simp
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u)
    rw [← hEq]
    exact h
  have hzTarget : z ∈ e.target := P.finiteChartCover.piece_in_target i hz
  have hψchart : ContDiffOn ℝ 2 (ψ ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hψ₂).2 x 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hφchart : ContDiffOn ℝ 2 (φ ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hφ₂).2 x 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hψAt : ContDiffAt ℝ 2 (ψ ∘ e.symm) z :=
    hψchart.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hzTarget)
  have hφAt : ContDiffAt ℝ 2 (φ ∘ e.symm) z :=
    hφchart.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hzTarget)
  have hsumAt : ContDiffAt ℝ 2 ((φ + ψ) ∘ e.symm) z := by
    simpa [Function.comp_def] using hφAt.add hψAt
  have hddadd : ddbar ((φ + ψ) ∘ e.symm) z =
      ddbar (φ ∘ e.symm) z + ddbar (ψ ∘ e.symm) z := by
    rw [show (φ + ψ) ∘ e.symm = (φ ∘ e.symm) + (ψ ∘ e.symm) by rfl]
    exact ddbar_add hφAt hψAt
  have hform : (ω₀.toFormField + mddbar n (φ + ψ)).chartRep x z =
      (ω₀.toFormField + mddbar n φ).chartRep x z + ddbar (ψ ∘ e.symm) z := by
    rw [FormField.chartRep_add, FormField.chartRep_add]
    simp only [Pi.add_apply]
    rw [chartRep_mddbar_of_contMDiff_two (hφ₂.add hψ₂) x hzTarget,
      chartRep_mddbar_of_contMDiff_two hφ₂ x hzTarget]
    rw [hddadd]
    abel
  have hpos := c2Potential_chartRep_isPositive
    (ω₀.toFormField + mddbar n (φ + ψ)) (fun y => hpositiveLimit.2 y) x hzTarget
  have hbase :
      ((ω₀.toFormField + mddbar n φ).chartRep x z).coeffMatrix = ω₁.metricInChart x z := rfl
  have hmatrix :
      ((ω₀.toFormField + mddbar n (φ + ψ)).chartRep x z).coeffMatrix =
        evaluatedPerturbedChartMatrix ω₁ α u i z := by
    rw [hform, ContinuousAlternatingMap.coeffMatrix_add, hbase]
    change ω₁.metricInChart x z + complexHessian (ψ ∘ e.symm) z =
      ω₁.metricInChart x z + complexHessian (ψ ∘ e.symm) z
    rfl
  rw [← hmatrix]
  exact (ContinuousAlternatingMap.isPositive_iff.mp hpos).2

private theorem continuousOn_complexHessian_of_contDiffOn_two
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : ContDiffOn ℝ 2 f U) :
    ContinuousOn (fun z => complexHessian f z) U := by
  have hfirst : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have hsecond : ContinuousOn (fun z => fderiv ℝ (fderiv ℝ f) z) U :=
    hfirst.continuousOn_fderiv_of_isOpen hU (by norm_num)
  refine continuousOn_pi' ?_
  intro j
  refine continuousOn_pi' ?_
  intro k
  have hformula : ∀ z ∈ U, complexHessian f z j k =
      ((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) : ℂ) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) +
        Complex.I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) -
          fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
            (EuclideanSpace.single k 1))) / 4 := by
    intro z hz
    exact complexHessian_apply (hf.contDiffAt (hU.mem_nhds hz)) j k
  have hcont : ContinuousOn (fun z : EuclideanSpace ℂ (Fin n) =>
      ((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1) : ℂ) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) +
        Complex.I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) -
          fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
            (EuclideanSpace.single k 1))) / 4) U := by
    fun_prop
  exact hcont.congr hformula

omit [ConnectedSpace M] in
private theorem evaluated_limit_chart_matrix_continuousOn
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (hpositiveLimit : ω₀.IsC2Potential (φ + P.evalC2 u))
    (i : P.finiteChartCover.ι) :
    ContinuousOn (fun z => evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z)
      (P.finiteChartCover.piece i) := by
  let ψ : M → ℝ := P.evalC2 u
  let ω₁ := ω₀.perturb φ hφ
  let x := P.finiteChartCover.base i
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hφ₂ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ :=
    hφ.1.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hψ₂ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ := by
    have h := hpositiveLimit.1.sub hφ₂
    have hEq : (φ + P.evalC2 u) - φ = P.evalC2 u := by funext y; simp
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u)
    rw [← hEq]
    exact h
  have hψchart : ContDiffOn ℝ 2 (ψ ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hψ₂).2 x 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hHcont : ContinuousOn (fun z => complexHessian (ψ ∘ e.symm) z) e.target :=
    continuousOn_complexHessian_of_contDiffOn_two (isOpen_extChartAt_target x) hψchart
  have hmetricEntry (j k : Fin n) :
      ContDiffOn ℝ ∞ (fun z => ω₁.metricInChart x z j k) e.target :=
    ω₁.contDiffOn_metricInChart x j k
  have hmetric : ContinuousOn (ω₁.metricInChart x) e.target := by
    refine continuousOn_pi' ?_
    intro j
    refine continuousOn_pi' ?_
    intro k
    exact (hmetricEntry j k).continuousOn
  have hL : ContinuousOn (fun z =>
      ω₁.metricInChart x z + complexHessian (ψ ∘ e.symm) z) e.target := hmetric.add hHcont
  have hL' : ContinuousOn
      (fun z => evaluatedPerturbedChartMatrix ω₁ α u i z) e.target := by
    simpa [evaluatedPerturbedChartMatrix, ω₁, ψ, x, e] using hL
  exact hL'.mono (P.finiteChartCover.piece_in_target i)

open scoped Matrix.Norms.Elementwise in
private theorem evaluated_limit_chart_inverse_bound
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (hpositiveLimit : ω₀.IsC2Potential (φ + P.evalC2 u))
    (i : P.finiteChartCover.ι) :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ P.finiteChartCover.piece i,
      finiteFrobeniusNorm
        ((evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z)⁻¹) ≤ K := by
  classical
  exact compact_frobenius_inverse_bound
    (fun z => evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z)
    (P.finiteChartCover.isCompact_piece i)
    (evaluated_limit_chart_matrix_continuousOn ω₀ φ hφ α u hpositiveLimit i)
    (fun z hz => evaluated_chart_matrix_posDef ω₀ φ hφ α u hpositiveLimit i z hz)

private theorem evaluated_limit_uniform_inverse_bound
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (hpositiveLimit : ω₀.IsC2Potential (φ + P.evalC2 u)) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ i z, z ∈ P.finiteChartCover.piece i →
      ‖(evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z)⁻¹‖ ≤ (K : ℝ) := by
  classical
  let b : P.finiteChartCover.ι → ℝ := fun i =>
    Classical.choose (evaluated_limit_chart_inverse_bound ω₀ φ hφ α u hpositiveLimit i)
  have hb (i : P.finiteChartCover.ι) :
      0 < b i ∧ ∀ z ∈ P.finiteChartCover.piece i,
        finiteFrobeniusNorm
          ((evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z)⁻¹) ≤ b i := by
    exact Classical.choose_spec (evaluated_limit_chart_inverse_bound ω₀ φ hφ α u hpositiveLimit i)
  have hsum_nonneg : 0 ≤ ∑ i : P.finiteChartCover.ι, b i :=
    Finset.sum_nonneg (fun i hi => (hb i).1.le)
  let K : ℝ≥0 := ⟨(∑ i : P.finiteChartCover.ι, b i) + 1, by linarith⟩
  have hKpos : 0 < K := by
    apply NNReal.coe_pos.mpr
    change 0 < (∑ i : P.finiteChartCover.ι, b i) + 1
    linarith
  refine ⟨K, hKpos, ?_⟩
  intro i z hz
  have hsum : b i ≤ ∑ j : P.finiteChartCover.ι, b j :=
    Finset.single_le_sum (fun j hj => (hb j).1.le) (Finset.mem_univ i)
  have hbound : finiteFrobeniusNorm
      ((evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z)⁻¹) ≤ (K : ℝ) := by
    calc
      _ ≤ b i := (hb i).2 z hz
      _ ≤ (K : ℝ) := by
        change b i ≤ (∑ j : P.finiteChartCover.ι, b j) + 1
        linarith
  simpa only [finiteFrobeniusNorm_eq_norm] using hbound

private theorem pair_segment_close_of_uniform_displacement
    {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (v : ℕ → V) (u : V) (A : ℕ → Z → W) (Alim : Z → W)
    (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η)
    (hv : Filter.Tendsto v Filter.atTop (𝓝 u))
    (hclose : ∀ j z, ‖A j z - Alim z‖ ≤ C * ‖v j - u‖)
    (S : Set Z) :
    ∃ N : ℕ, ∀ j k, N ≤ j → N ≤ k → ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ S,
      ‖(1 - θ) • A j z + θ • A k z - Alim z‖ ≤ η := by
  let δ : ℝ := η / (C + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hsmall : ∀ᶠ j in Filter.atTop, ‖v j - u‖ < δ := by
    have h := Metric.tendsto_nhds.mp hv δ hδ
    simpa [dist_eq_norm] using h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  have hCδ : C * δ ≤ η := by
    dsimp [δ]
    have hden : 0 < C + 1 := by linarith
    have heq : (C + 1) * (η / (C + 1)) = η := by field_simp
    nlinarith
  refine ⟨N, ?_⟩
  intro j k hj hk θ hθ z hz
  have hθ₀ : 0 ≤ θ := hθ.1
  have hθ₁ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
  have hjclose : C * ‖v j - u‖ ≤ η := by
    have hj' : ‖v j - u‖ < δ := hN j hj
    calc
      C * ‖v j - u‖ ≤ C * δ := mul_le_mul_of_nonneg_left hj'.le hC
      _ ≤ η := hCδ
  have hkclose : C * ‖v k - u‖ ≤ η := by
    have hk' : ‖v k - u‖ < δ := hN k hk
    calc
      C * ‖v k - u‖ ≤ C * δ := mul_le_mul_of_nonneg_left hk'.le hC
      _ ≤ η := hCδ
  have hrewrite :
      (1 - θ) • A j z + θ • A k z - Alim z =
        (1 - θ) • (A j z - Alim z) + θ • (A k z - Alim z) := by
    module
  calc
    ‖(1 - θ) • A j z + θ • A k z - Alim z‖ =
        ‖(1 - θ) • (A j z - Alim z) + θ • (A k z - Alim z)‖ := by rw [hrewrite]
    _ ≤ ‖(1 - θ) • (A j z - Alim z)‖ + ‖θ • (A k z - Alim z)‖ := norm_add_le _ _
    _ = (1 - θ) * ‖A j z - Alim z‖ + θ * ‖A k z - Alim z‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ₁,
        Real.norm_eq_abs, abs_of_nonneg hθ₀]
    _ ≤ (1 - θ) * (C * ‖v j - u‖) + θ * (C * ‖v k - u‖) := by
      gcongr
      · exact hclose j z
      · exact hclose k z
    _ ≤ (1 - θ) * η + θ * η := add_le_add
      (mul_le_mul_of_nonneg_left hjclose hθ₁)
      (mul_le_mul_of_nonneg_left hkclose hθ₀)
    _ = η := by ring

omit [ConnectedSpace M] in
private theorem smoothCore_chartMatrix_segment_close_limit
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hv : Filter.Tendsto
      (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) Filter.atTop
      (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)))
    (hclose : ∀ j i z, z ∈ P.finiteChartCover.piece i →
      ‖smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z -
        evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z‖ ≤
          ((n + 1 : ℝ≥0) : ℝ) *
            ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
              (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j k, N ≤ j → N ≤ k → ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ z ∈ P.finiteChartCover.piece i,
        ‖(smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z +
          s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z -
            smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z)) -
          evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z‖ < ε := by
  let : NormedAddCommGroup (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 2 α P.normedDataC2
  let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 2 α P.normedDataC2
  let V := LittleHolder P.finiteChartCover 2 α P.normedDataC2
  let pts := {p : Σ i : P.finiteChartCover.ι, EuclideanSpace ℂ (Fin n) |
    p.2 ∈ P.finiteChartCover.piece p.1}
  let A : ℕ → pts → Matrix (Fin n) (Fin n) ℂ := fun j p =>
    smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) p.1.1 p.1.2
  let L : pts → Matrix (Fin n) (Fin n) ℂ := fun p =>
    evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u p.1.1 p.1.2
  let c : ℝ := ((n + 1 : ℝ≥0) : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hv' : Filter.Tendsto (fun j : ℕ => (v j : V)) Filter.atTop
      (𝓝 (u : V)) := hv
  have hclose' : ∀ j p, ‖A j p - L p‖ ≤ c *
      ‖(v j : V) - (u : V)‖ := by
    intro j p
    exact hclose j p.1.1 p.1.2 p.2
  obtain ⟨N, hN⟩ := pair_segment_close_of_uniform_displacement
    (fun j : ℕ => (v j : V)) (u : V) A L c (ε / 2) hc (half_pos hε)
    hv' hclose' Set.univ
  refine ⟨N, ?_⟩
  intro j k hj hk i s hs z hz
  have h := hN j k hj hk s hs ⟨⟨i, z⟩, hz⟩ (Set.mem_univ _)
  let Aj := smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
    P.finiteChartCover α (v j) i z
  let Ak := smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
    P.finiteChartCover α (v k) i z
  let Li := evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z
  have hdecomp : Aj + s • (Ak - Aj) - Li =
      (1 - s) • Aj + s • Ak - Li := by module
  rw [hdecomp]
  have hbound : ‖(1 - s) • Aj + s • Ak - Li‖ ≤ ε / 2 := by
    simpa [A, L, Aj, Ak, Li] using h
  exact lt_of_le_of_lt hbound (by linarith)

private theorem frobenius_inverse_bound_of_close_positive {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (K δ : ℝ) (hAinv : ‖A⁻¹‖ ≤ K) (hclose : ‖B - A‖ ≤ δ)
    (hsmall : K * δ ≤ 1 / 2) : ‖B⁻¹‖ ≤ 2 * K := by
  have hAunit : IsUnit A.det := (hA.det_pos.ne').isUnit
  have hBunit : IsUnit B.det := (hB.det_pos.ne').isUnit
  have hAinvA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAunit
  have hBinvB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBunit
  have hid : B⁻¹ = A⁻¹ + A⁻¹ * (A - B) * B⁻¹ := by
    calc
      B⁻¹ = (A⁻¹ * A) * B⁻¹ := by rw [hAinvA]; simp
      _ = A⁻¹ * ((A - B) + B) * B⁻¹ := by noncomm_ring
      _ = A⁻¹ * (A - B) * B⁻¹ + A⁻¹ * B * B⁻¹ := by noncomm_ring
      _ = A⁻¹ * (A - B) * B⁻¹ + A⁻¹ * (B * B⁻¹) := by
        congr 1
        exact Matrix.mul_assoc A⁻¹ B B⁻¹
      _ = A⁻¹ * (A - B) * B⁻¹ + A⁻¹ := by rw [hBinvB, Matrix.mul_one]
      _ = A⁻¹ + A⁻¹ * (A - B) * B⁻¹ := by abel
  have hmul : ‖A⁻¹ * (A - B) * B⁻¹‖ ≤
      (‖A⁻¹‖ * ‖A - B‖) * ‖B⁻¹‖ := by
    calc
      ‖A⁻¹ * (A - B) * B⁻¹‖ ≤ ‖A⁻¹ * (A - B)‖ * ‖B⁻¹‖ :=
        Matrix.frobenius_norm_mul _ _
      _ ≤ (‖A⁻¹‖ * ‖A - B‖) * ‖B⁻¹‖ := by
        exact mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
  have hrev : ‖A - B‖ ≤ δ := by rw [norm_sub_rev]; exact hclose
  have hKnonneg : 0 ≤ K := (norm_nonneg _).trans hAinv
  have hmul' : ‖A⁻¹ * (A - B) * B⁻¹‖ ≤ (K * δ) * ‖B⁻¹‖ := by
    calc
      _ ≤ (‖A⁻¹‖ * ‖A - B‖) * ‖B⁻¹‖ := hmul
      _ ≤ (K * δ) * ‖B⁻¹‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hAinv hrev (norm_nonneg _) hKnonneg) (norm_nonneg _)
  have hbound : ‖B⁻¹‖ ≤ K + (K * δ) * ‖B⁻¹‖ := by
    calc
      ‖B⁻¹‖ = ‖A⁻¹ + A⁻¹ * (A - B) * B⁻¹‖ := congrArg norm hid
      _ ≤ ‖A⁻¹‖ + ‖A⁻¹ * (A - B) * B⁻¹‖ := norm_add_le _ _
      _ ≤ K + (K * δ) * ‖B⁻¹‖ := add_le_add hAinv hmul'
  nlinarith [norm_nonneg (B⁻¹)]

private theorem affine_segment_holder_with_bound
    {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {r H D : ℝ≥0} {sset : Set X} (A B : X → Y) (a : ℝ)
    (hA : HolderOnWith H r A sset)
    (hD : HolderOnWith D r (fun x => B x - A x) sset)
    (ha : ‖a‖₊ ≤ 1) :
    HolderOnWith (H + D) r (fun x => A x + a • (B x - A x)) sset := by
  have hA' : HolderWith H r (fun x : sset => A x) := by
    apply holderOnWith_univ.mp
    intro x _ y _
    exact hA x x.2 y y.2
  have hD' : HolderWith D r (fun x : sset => B x - A x) := by
    apply holderOnWith_univ.mp
    intro x _ y _
    exact hD x x.2 y y.2
  have hmul : HolderWith (D * ‖a‖₊) r (fun x : sset => a • (B x - A x)) := hD'.smul a
  have hmul' : HolderWith D r (fun x : sset => a • (B x - A x)) := hmul.mono (by
    calc
      D * ‖a‖₊ ≤ D * 1 := mul_le_mul_of_nonneg_left ha D.coe_nonneg
      _ = D := by simp)
  have hsum : HolderWith (H + D) r
      (fun x : sset => A x + a • (B x - A x)) := hA'.add hmul'
  intro x hx y hy
  exact hsum ⟨x, hx⟩ ⟨y, hy⟩

private theorem convergent_displacement_nnnorm_bounded0
    {E : Type*} [NormedAddCommGroup E] (v : ℕ → E) (v₀ : E)
    (hv : Filter.Tendsto v Filter.atTop (𝓝 v₀)) :
    ∃ C : ℝ≥0, ∀ j, ‖v j - v₀‖₊ ≤ C := by
  have hbdd : Bornology.IsBounded (Set.range v) := Metric.isBounded_range_of_tendsto v hv
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall v₀).mp hbdd
  have hCnonneg : 0 ≤ C := by
    have hmem := hC (Set.mem_range_self 0)
    exact le_trans dist_nonneg hmem
  refine ⟨C.toNNReal, ?_⟩
  intro j
  apply NNReal.coe_le_coe.mp
  change ‖v j - v₀‖ ≤ (C.toNNReal : ℝ)
  rw [Real.coe_toNNReal', max_eq_left hCnonneg]
  have hmem := hC (Set.mem_range_self j)
  rw [Metric.mem_closedBall, dist_eq_norm] at hmem
  simpa [dist_eq_norm] using hmem

omit [ConnectedSpace M] in
private theorem holder_tail_from_base
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hv : Filter.Tendsto
      (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) Filter.atTop
      (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)))
    (H₀ : ℝ≥0)
    (hbase : ∀ i, HolderOnWith H₀ α
      (fun z => smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
        P.finiteChartCover α (v 0) i z) (P.finiteChartCover.piece i))
    (hdiffHolder : ∀ j k i, HolderOnWith
      (2 * (n + 1 : ℝ≥0) *
        ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
          (v k : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖₊) α
      (fun z =>
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z -
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z)
      (P.finiteChartCover.piece i)) :
    ∃ N : ℕ, ∃ H : ℝ≥0,
      ∀ j k, N ≤ j → N ≤ k → ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HolderOnWith H α
          (fun z => smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
            P.finiteChartCover α (v j) i z +
            s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
              P.finiteChartCover α (v k) i z -
              smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
                P.finiteChartCover α (v j) i z))
          (P.finiteChartCover.piece i) := by
  let : NormedAddCommGroup (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 2 α P.normedDataC2
  let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 2 α P.normedDataC2
  let V := LittleHolder P.finiteChartCover 2 α P.normedDataC2
  let f : ℕ → V := fun j => v j
  obtain ⟨Cdisp, hdisp⟩ := convergent_displacement_nnnorm_bounded0 f (u : V) hv
  let R : ℝ≥0 := Cdisp + ‖(u : V) - (v 0 : V)‖₊
  let D : ℝ≥0 := 4 * (n + 1 : ℝ≥0) * R
  have hRdiff : ∀ j, ‖(v j : V) - (v 0 : V)‖₊ ≤ R := by
    intro j
    have htri : ‖(v j : V) - (v 0 : V)‖₊ ≤
        ‖(v j : V) - (u : V)‖₊ + ‖(u : V) - (v 0 : V)‖₊ := by
      calc
        _ = ‖((v j : V) - (u : V)) + ((u : V) - (v 0 : V))‖₊ := by congr 1; abel
        _ ≤ _ := nnnorm_add_le _ _
    exact htri.trans (add_le_add (by simpa [f] using hdisp j) le_rfl)
  have hdiff0bound : ∀ j,
      2 * (n + 1 : ℝ≥0) * ‖(v j : V) - (v 0 : V)‖₊ ≤ D := by
    intro j
    dsimp [D]
    calc
      _ ≤ 2 * (n + 1 : ℝ≥0) * R :=
        mul_le_mul_of_nonneg_left (hRdiff j) (by positivity)
      _ ≤ 2 * (n + 1 : ℝ≥0) * (2 * R) := by
        apply mul_le_mul_of_nonneg_left
        · rw [two_mul]
          exact le_add_self
        · positivity
      _ = 4 * (n + 1 : ℝ≥0) * R := by ring
  have hdiffbound : ∀ j k,
      2 * (n + 1 : ℝ≥0) * ‖(v j : V) - (v k : V)‖₊ ≤ D := by
    intro j k
    have htri : ‖(v j : V) - (v k : V)‖₊ ≤ R + R := by
      calc
        ‖(v j : V) - (v k : V)‖₊ =
            ‖((v j : V) - (v 0 : V)) + ((v 0 : V) - (v k : V))‖₊ := by
          congr 1; abel
        _ ≤ ‖(v j : V) - (v 0 : V)‖₊ + ‖(v 0 : V) - (v k : V)‖₊ := nnnorm_add_le _ _
        _ ≤ R + R := by
          gcongr
          · exact hRdiff j
          · have hrev : ‖(v 0 : V) - (v k : V)‖₊ = ‖(v k : V) - (v 0 : V)‖₊ := by
              rw [← neg_sub, nnnorm_neg]
            rw [hrev]
            exact hRdiff k
    dsimp [D]
    calc
      _ ≤ 2 * (n + 1 : ℝ≥0) * (R + R) := by gcongr
      _ = _ := by ring
  refine ⟨0, H₀ + 2 * D, ?_⟩
  intro j k _hj _hk i s hs
  let A : ℕ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun l z =>
    smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v l) i z
  have hAj0 : HolderOnWith D α (fun z => A j z - A 0 z)
      (P.finiteChartCover.piece i) :=
    (hdiffHolder j 0 i).mono_const (hdiff0bound j)
  have hAk0 : HolderOnWith D α (fun z => A k z - A 0 z)
      (P.finiteChartCover.piece i) :=
    (hdiffHolder k 0 i).mono_const (hdiff0bound k)
  have hDjk : HolderOnWith D α (fun z => A k z - A j z)
      (P.finiteChartCover.piece i) :=
    (hdiffHolder k j i).mono_const (hdiffbound k j)
  have hbase' : HolderWith H₀ α (fun z : P.finiteChartCover.piece i => A 0 z.1) := by
    apply holderOnWith_univ.mp
    intro x _ y _
    exact (hbase i) x x.2 y y.2
  have hAj0' : HolderWith D α
      (fun z : P.finiteChartCover.piece i => A j z.1 - A 0 z.1) := by
    apply holderOnWith_univ.mp
    intro x _ y _
    exact hAj0 x x.2 y y.2
  have hAk0' : HolderWith D α
      (fun z : P.finiteChartCover.piece i => A k z.1 - A 0 z.1) := by
    apply holderOnWith_univ.mp
    intro x _ y _
    exact hAk0 x x.2 y y.2
  have hAj : HolderOnWith (H₀ + D) α (A j) (P.finiteChartCover.piece i) := by
    have h := hbase'.add hAj0'
    have heq : (fun z : P.finiteChartCover.piece i => A 0 z.1) +
        (fun z => A j z.1 - A 0 z.1) = (fun z => A j z.1) := by
      ext z
      simp
    have h' : HolderWith (H₀ + D) α (fun z : P.finiteChartCover.piece i => A j z.1) :=
      heq ▸ h
    intro x hx y hy
    exact h' ⟨x, hx⟩ ⟨y, hy⟩
  have hAk : HolderOnWith (H₀ + D) α (A k) (P.finiteChartCover.piece i) := by
    have h := hbase'.add hAk0'
    have heq : (fun z : P.finiteChartCover.piece i => A 0 z.1) +
        (fun z => A k z.1 - A 0 z.1) = (fun z => A k z.1) := by
      ext z
      simp
    have h' : HolderWith (H₀ + D) α (fun z : P.finiteChartCover.piece i => A k z.1) :=
      heq ▸ h
    intro x hx y hy
    exact h' ⟨x, hx⟩ ⟨y, hy⟩
  have hsNorm : ‖s‖₊ ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hseg := affine_segment_holder_with_bound (A j) (A k) s hAj hDjk hsNorm
  simpa [A, two_mul, add_assoc] using hseg

private theorem complexHessian_entry_contDiffAt_one_forCore
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (j k : Fin n) :
    ContDiffAt ℝ 1 (fun x => complexHessian u x j k) z := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) z :=
    hD1.fderiv_right (by norm_num)
  have hQ (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffAt ℝ 1 (fun x => fderiv ℝ (fderiv ℝ u) x v w) z := by
    have hv : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) => v) z := contDiffAt_const
    have hw : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) => w) z := contDiffAt_const
    exact (hD2.clm_apply hv).clm_apply hw
  let q : EuclideanSpace ℂ (Fin n) → ℂ := fun x =>
    ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) : ℂ) +
      fderiv ℝ (fderiv ℝ u) x (Complex.I • EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1) +
      Complex.I * (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1) -
      fderiv ℝ (fderiv ℝ u) x (Complex.I • EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1))) / 4
  have hq : ContDiffAt ℝ 1 q z := by
    dsimp [q]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEq : (fun x => complexHessian u x j k) =ᶠ[𝓝 z] q := by
    filter_upwards [hnear] with x hx
    exact complexHessian_apply (hx.of_le (by norm_num)) j k
  exact hq.congr_of_eventuallyEq hEq

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem smoothCore_chartMatrix_contDiffAt_one
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (v : SmoothChartHolderCore P.finiteChartCover 2 α) (i : P.finiteChartCover.ι)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ P.finiteChartCover.piece i) :
    ContDiffAt ℝ 1
      (fun z => smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
        P.finiteChartCover α v i z) z := by
  let x := P.finiteChartCover.base i
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f : EuclideanSpace ℂ (Fin n) → ℝ := v.smoothMap ∘ e.symm
  have hzTarget : z ∈ e.target := P.finiteChartCover.piece_in_target i hz
  have hf : ContDiffAt ℝ 3 f z := by
    have he : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hzTarget)
    have hv : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        v.smoothMap (e.symm z) := v.smoothMap.contMDiff (e.symm z)
    have hcomp : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (v.smoothMap ∘ e.symm) z := hv.comp_of_eq he rfl
    have hcomp' : ContDiffAt ℝ ∞ (v.smoothMap ∘ e.symm) z :=
      (contMDiffAt_iff_contDiffAt).mp hcomp
    change ContDiffAt ℝ 3 (v.smoothMap ∘ e.symm) z
    exact hcomp'.of_le (WithTop.coe_le_coe.mpr (by norm_num : (3 : ℕ∞) ≤ ⊤))
  let ω₁ := ω₀.perturb φ hφ
  have hmetricEntry (j k : Fin n) :
      ContDiffAt ℝ 1 (fun y => ω₁.metricInChart x y j k) z := by
    have hcont : ContDiffOn ℝ ∞ (fun y => ω₁.metricInChart x y j k) e.target :=
      ω₁.contDiffOn_metricInChart x j k
    have hAt := hcont.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hzTarget)
    exact hAt.of_le (WithTop.coe_le_coe.mpr (by norm_num : (1 : ℕ∞) ≤ ⊤))
  let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun y =>
    smoothCorePerturbedChartMatrix ω₁ P.finiteChartCover α v i y
  have hAEntry (j k : Fin n) : ContDiffAt ℝ 1 (fun y => A y j k) z := by
    change ContDiffAt ℝ 1
      (fun y => ω₁.metricInChart x y j k + complexHessian f y j k) z
    exact (hmetricEntry j k).add (complexHessian_entry_contDiffAt_one_forCore hf j k)
  have hA_eq : (fun y => A y) = fun y =>
      Finset.univ.sum (fun j : Fin n => Finset.univ.sum (fun k : Fin n =>
        (RCLike.re (A y j k) : ℝ) • Matrix.single j k (1 : ℂ) +
          (RCLike.im (A y j k) : ℝ) • Matrix.single j k Complex.I)) := by
    funext y
    calc
      A y = Finset.univ.sum (fun j : Fin n => Finset.univ.sum
          (fun k : Fin n => Matrix.single j k (A y j k))) := Matrix.matrix_eq_sum_single _
      _ = Finset.univ.sum (fun j : Fin n => Finset.univ.sum (fun k : Fin n =>
          (RCLike.re (A y j k) : ℝ) • Matrix.single j k (1 : ℂ) +
            (RCLike.im (A y j k) : ℝ) • Matrix.single j k Complex.I)) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        ext a b
        simp [Matrix.single_apply]
        by_cases hja : j = a <;> by_cases hkb : k = b <;>
          simp [hja, hkb, Complex.re_add_im]
  have hterm (j k : Fin n) : ContDiffAt ℝ 1
      (fun y => (RCLike.re (A y j k) : ℝ) • Matrix.single j k (1 : ℂ) +
        (RCLike.im (A y j k) : ℝ) • Matrix.single j k Complex.I) z := by
    have hre : ContDiffAt ℝ 1 (fun y => RCLike.re (A y j k)) z := by
      exact RCLike.reCLM.contDiff.comp_contDiffAt z (hAEntry j k)
    have him : ContDiffAt ℝ 1 (fun y => RCLike.im (A y j k)) z := by
      exact RCLike.imCLM.contDiff.comp_contDiffAt z (hAEntry j k)
    exact (hre.smul_const _).add (him.smul_const _)
  have hinner (j : Fin n) : ContDiffAt ℝ 1
      (fun y => Finset.univ.sum (fun k : Fin n =>
        (RCLike.re (A y j k) : ℝ) • Matrix.single j k (1 : ℂ) +
          (RCLike.im (A y j k) : ℝ) • Matrix.single j k Complex.I)) z := by
    apply ContDiffAt.sum (s := Finset.univ)
    intro k hk
    exact hterm j k
  have hsum : ContDiffAt ℝ 1
      (fun y => Finset.univ.sum (fun j : Fin n => Finset.univ.sum (fun k : Fin n =>
        (RCLike.re (A y j k) : ℝ) • Matrix.single j k (1 : ℂ) +
          (RCLike.im (A y j k) : ℝ) • Matrix.single j k Complex.I))) z := by
    apply ContDiffAt.sum (s := Finset.univ)
    intro j hj
    exact hinner j
  rw [hA_eq]
  exact hsum

private theorem exists_smoothCore_chartMatrix_anchor_holder
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (v : SmoothChartHolderCore P.finiteChartCover 2 α) :
    ∃ H₀ : ℝ≥0, ∀ i, HolderOnWith H₀ α
      (fun z => smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
        P.finiteChartCover α v i z) (P.finiteChartCover.piece i) := by
  have hpieces : ∀ i, ∃ C : ℝ≥0, HolderOnWith C α
      (fun z => smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
        P.finiteChartCover α v i z) (P.finiteChartCover.piece i) := by
    intro i
    let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun z =>
      smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α v i z
    have hlocal : LocallyLipschitzOn (P.finiteChartCover.piece i) g := by
      intro z hz
      obtain ⟨C, t, ht, hLip⟩ :=
        (smoothCore_chartMatrix_contDiffAt_one ω₀ φ hφ α v i hz).exists_lipschitzOnWith
      refine ⟨C, P.finiteChartCover.piece i ∩ t, inter_mem_nhdsWithin _ ht, ?_⟩
      exact hLip.mono Set.inter_subset_right
    obtain ⟨L, hL⟩ :=
      LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
        (P.finiteChartCover.isCompact_piece i) hlocal
    have hL₁ : LipschitzOnWith L g (P.finiteChartCover.piece i) := hL
    have hLholder : HolderOnWith L 1 g (P.finiteChartCover.piece i) :=
      hL₁.holderOnWith
    obtain ⟨C, hC⟩ := HolderOnWith.exists_holderOnWith_of_le
      (r := (1 : ℝ≥0)) ⟨L, hLholder⟩ (le_of_lt hα₁)
        (P.finiteChartCover.isCompact_piece i).isBounded
    exact ⟨C, by simpa [g] using hC⟩
  classical
  let C₀ : P.finiteChartCover.ι → ℝ≥0 := fun i => Classical.choose (hpieces i)
  let C : ℝ≥0 := ∑ i, C₀ i
  refine ⟨C, ?_⟩
  intro i
  have hle : C₀ i ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (f := C₀) (s := Finset.univ)
      (fun k hk => by positivity) (Finset.mem_univ i)
  exact (Classical.choose_spec (hpieces i)).mono_const hle

private theorem exists_smoothCore_chartMatrix_segment_holder_tail
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hv : Filter.Tendsto
      (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) Filter.atTop
      (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)))
    (_hpositiveLimit : ω₀.IsC2Potential (φ + P.evalC2 u))
    (hdiffHolder : ∀ j k i, HolderOnWith
      (2 * (n + 1 : ℝ≥0) *
        ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
          (v k : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖₊) α
      (fun z =>
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z -
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z)
      (P.finiteChartCover.piece i)) :
    ∃ N : ℕ, ∃ H : ℝ≥0,
      ∀ j k, N ≤ j → N ≤ k → ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HolderOnWith H α
          (fun z => smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
            P.finiteChartCover α (v j) i z +
            s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
              P.finiteChartCover α (v k) i z -
              smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
                P.finiteChartCover α (v j) i z))
          (P.finiteChartCover.piece i) := by
  obtain ⟨H₀, hbase⟩ :=
    exists_smoothCore_chartMatrix_anchor_holder ω₀ φ hφ α hα₁ (v 0)
  exact holder_tail_from_base ω₀ φ hφ α u v hv H₀ hbase hdiffHolder

end FrobeniusTail

end KahlerForm

open scoped Matrix.Norms.Frobenius

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- One tail, one finite Frobenius inverse bound and one spatial Hölder bound for every pairwise
segment. The two matrix-control hypotheses are exactly projections of ChartMatrixControl. -/
theorem exists_smoothCore_chartMatrix_common_tail
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hv : Filter.Tendsto
      (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) Filter.atTop
      (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)))
    (hpositive : ∀ j, ω₀.IsC2Potential (φ + fun x => (v j).smoothMap x))
    (hpositiveLimit : ω₀.IsC2Potential (φ + P.evalC2 u))
    (hdiffHolder : ∀ j k i, HolderOnWith
      (2 * (n + 1 : ℝ≥0) *
        ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
          (v k : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖₊) α
      (fun z =>
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z -
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z)
      (P.finiteChartCover.piece i))
    (hclose : ∀ j i z, z ∈ P.finiteChartCover.piece i →
      ‖smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z -
        evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z‖ ≤
          ((n + 1 : ℝ≥0) : ℝ) *
            ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
              (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖) :
    ∃ N : ℕ, ∃ K H : ℝ≥0,
      ∀ j k, N ≤ j → N ≤ k → ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∀ z ∈ P.finiteChartCover.piece i,
          (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z +
            s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
              P.finiteChartCover α (v k) i z -
              smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
                P.finiteChartCover α (v j) i z)).PosDef ∧
          ‖(smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z +
            s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
              P.finiteChartCover α (v k) i z -
              smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
                P.finiteChartCover α (v j) i z))⁻¹‖ ≤ (K : ℝ)) ∧
        HolderOnWith H α
          (fun z => smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
            P.finiteChartCover α (v j) i z +
            s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
              P.finiteChartCover α (v k) i z -
              smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ)
                P.finiteChartCover α (v j) i z))
          (P.finiteChartCover.piece i) := by
  have hsegment : ∀ j k, ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ P.finiteChartCover.piece i,
      (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z +
        s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z -
          smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z)).PosDef := by
    intro j k i s hs z hz
    exact smoothCore_chartMatrix_segments_posDef ω₀ φ hφ α v hpositive j k i z hz s hs
  obtain ⟨K₀, hK₀, hlimitInv⟩ :=
    evaluated_limit_uniform_inverse_bound ω₀ φ hφ α u hpositiveLimit
  let c : ℝ := (K₀ : ℝ)
  let δ : ℝ := 1 / (2 * (c + 1))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : c * δ ≤ 1 / 2 := by
    dsimp [δ]
    calc
      c * (1 / (2 * (c + 1))) ≤ (c + 1) * (1 / (2 * (c + 1))) := by
        gcongr
        linarith
      _ = 1 / 2 := by field_simp
  obtain ⟨Nclose, hNclose⟩ :=
    smoothCore_chartMatrix_segment_close_limit ω₀ φ hφ α u v hv hclose δ hδ
  obtain ⟨Nholder, H, hHolder⟩ :=
    exists_smoothCore_chartMatrix_segment_holder_tail ω₀ φ hφ α hα₁ u v hv
      hpositiveLimit hdiffHolder
  let K : ℝ≥0 := ⟨2 * c, by positivity⟩
  refine ⟨max Nclose Nholder, K, H, ?_⟩
  intro j k hj hk i s hs
  constructor
  · intro z hz
    refine ⟨hsegment j k i s hs z hz, ?_⟩
    let A := evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z
    let B := smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z +
      s • (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z -
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z)
    have hApos : A.PosDef :=
      evaluated_chart_matrix_posDef ω₀ φ hφ α u hpositiveLimit i z hz
    have hAinv : ‖A⁻¹‖ ≤ c := by
      simpa [A, c] using hlimitInv i z hz
    have hBclose : ‖B - A‖ ≤ δ :=
      (hNclose j k (le_trans (le_max_left _ _) hj) (le_trans (le_max_left _ _) hk)
        i s hs z hz).le
    have hBinv := frobenius_inverse_bound_of_close_positive A B hApos
      (hsegment j k i s hs z hz) c δ hAinv hBclose hsmall
    change ‖B⁻¹‖ ≤ 2 * c
    exact hBinv
  · exact hHolder j k (le_trans (le_max_right _ _) hj)
      (le_trans (le_max_right _ _) hk) i s hs

end KahlerForm
