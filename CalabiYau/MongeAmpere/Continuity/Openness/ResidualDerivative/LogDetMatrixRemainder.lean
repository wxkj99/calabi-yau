module

public import CalabiYau.LinearAlgebra.Hermitian.LogDetDeriv
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fixed-base matrix log-determinant Taylor remainder

For one positive definite base matrix, the change in the first-order log-determinant remainder is
controlled by the Frobenius norms of the two perturbations and their difference. The inverse bounds
are stated on the whole segment where the resolvent identity is used.
-/

@[expose] public section

open scoped ComplexOrder ContDiff Matrix.Norms.Frobenius

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The first-order Taylor remainder of `B ↦ log (re det B)` at a positive definite base `A`. -/
noncomputable def logDetTaylorRemainder (A H : Matrix ι ι 𝕜) : ℝ :=
  Real.log (RCLike.re (A + H).det) - Real.log (RCLike.re A.det) -
    RCLike.re (A⁻¹ * H).trace

/-- The real part of `trace (U * V)` is bounded by the product of the Frobenius norms. -/
theorem abs_re_trace_mul_le_frobenius (U V : Matrix ι ι 𝕜) :
    |RCLike.re (U * V).trace| ≤ ‖U‖ * ‖V‖ := by
  let f : ι × ι → ℝ := fun ij => ‖U ij.1 ij.2‖
  let g : ι × ι → ℝ := fun ij => ‖V ij.2 ij.1‖
  have htrace : RCLike.re (U * V).trace =
      ∑ ij : ι × ι, RCLike.re (U ij.1 ij.2 * V ij.2 ij.1) := by
    simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ι × ι)) f g
  have hf : 0 ≤ ∑ ij : ι × ι, f ij * g ij :=
    Finset.sum_nonneg fun ij hij => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hff : 0 ≤ ∑ ij : ι × ι, f ij ^ 2 :=
    Finset.sum_nonneg fun ij hij => sq_nonneg _
  have hgg : 0 ≤ ∑ ij : ι × ι, g ij ^ 2 :=
    Finset.sum_nonneg fun ij hij => sq_nonneg _
  have hsum : (∑ ij : ι × ι, f ij * g ij) ≤
      Real.sqrt (∑ ij : ι × ι, f ij ^ 2) * Real.sqrt (∑ ij : ι × ι, g ij ^ 2) := by
    have hsqrt := Real.sqrt_le_sqrt hcs
    rw [Real.sqrt_mul] at hsqrt
    · rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hf] at hsqrt
      exact hsqrt
    · exact hff
  have hfnorm : Real.sqrt (∑ ij : ι × ι, f ij ^ 2) = ‖U‖ := by
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    congr 1
    simp only [Fintype.sum_prod_type, f]
    simp only [Real.rpow_two, pow_two]
  have hgnorm : Real.sqrt (∑ ij : ι × ι, g ij ^ 2) = ‖V‖ := by
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    congr 1
    simp only [Fintype.sum_prod_type, g]
    rw [Finset.sum_comm]
    simp only [Real.rpow_two, pow_two]
  calc
    |RCLike.re (U * V).trace| =
        |∑ ij : ι × ι, RCLike.re (U ij.1 ij.2 * V ij.2 ij.1)| := by rw [htrace]
    _ ≤ ∑ ij : ι × ι, |RCLike.re (U ij.1 ij.2 * V ij.2 ij.1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ij : ι × ι, f ij * g ij := by
      apply Finset.sum_le_sum
      intro ij hij
      calc
        |RCLike.re (U ij.1 ij.2 * V ij.2 ij.1)| ≤
            ‖U ij.1 ij.2 * V ij.2 ij.1‖ := RCLike.abs_re_le_norm _
        _ = f ij * g ij := by simp [f, g, norm_mul]
    _ ≤ Real.sqrt (∑ ij : ι × ι, f ij ^ 2) * Real.sqrt (∑ ij : ι × ι, g ij ^ 2) := hsum
    _ = ‖U‖ * ‖V‖ := by rw [hfnorm, hgnorm]

private theorem abs_re_resolvent_trace_le_frobenius (A Z D B : Matrix ι ι 𝕜) (μ M d : ℝ)
    (hμ : 0 < μ) (hA : A.PosDef) (hBpd : B.PosDef)
    (hAinv : ‖A⁻¹‖ ≤ Real.sqrt (Fintype.card ι : ℝ) / μ)
    (hBinv : ‖B⁻¹‖ ≤ Real.sqrt (Fintype.card ι : ℝ) / μ)
    (hZ : ‖Z‖ ≤ M) (hD : ‖D‖ ≤ d)
    (hB : B = A + Z) :
    |RCLike.re ((B⁻¹ - A⁻¹) * D).trace| ≤
      ((Fintype.card ι : ℝ) / μ ^ 2) * M * d := by
  have hAunit : IsUnit A.det := (ne_of_gt hA.det_pos).isUnit
  have hBunit : IsUnit B.det := (ne_of_gt hBpd.det_pos).isUnit
  have hAiA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAunit
  have hBBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBunit
  have hres : B⁻¹ - A⁻¹ = -(A⁻¹ * Z * B⁻¹) := by
    calc
      B⁻¹ - A⁻¹ = A⁻¹ * A * B⁻¹ - A⁻¹ * (B * B⁻¹) := by rw [hAiA, hBBi]; simp
      _ = A⁻¹ * (A - B) * B⁻¹ := by noncomm_ring
      _ = -(A⁻¹ * Z * B⁻¹) := by rw [hB]; noncomm_ring
  have htrace : RCLike.re ((B⁻¹ - A⁻¹) * D).trace =
      -RCLike.re ((A⁻¹ * Z) * (B⁻¹ * D)).trace := by
    rw [hres]
    simp [Matrix.trace_neg, Matrix.mul_assoc]
  have hM : 0 ≤ M := le_trans (norm_nonneg Z) hZ
  have hd : 0 ≤ d := le_trans (norm_nonneg D) hD
  have hU : ‖A⁻¹ * Z‖ ≤ Real.sqrt (Fintype.card ι : ℝ) / μ * M := by
    calc
      ‖A⁻¹ * Z‖ ≤ ‖A⁻¹‖ * ‖Z‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ (Real.sqrt (Fintype.card ι : ℝ) / μ) * M :=
        mul_le_mul hAinv hZ (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hμ.le)
  have hV : ‖B⁻¹ * D‖ ≤ Real.sqrt (Fintype.card ι : ℝ) / μ * d := by
    calc
      ‖B⁻¹ * D‖ ≤ ‖B⁻¹‖ * ‖D‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ (Real.sqrt (Fintype.card ι : ℝ) / μ) * d :=
        mul_le_mul hBinv hD (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hμ.le)
  have hsqrt : (Real.sqrt (Fintype.card ι : ℝ)) ^ 2 = (Fintype.card ι : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  calc
    |RCLike.re ((B⁻¹ - A⁻¹) * D).trace| =
        |RCLike.re ((A⁻¹ * Z) * (B⁻¹ * D)).trace| := by rw [htrace, abs_neg]
    _ ≤ ‖A⁻¹ * Z‖ * ‖B⁻¹ * D‖ := abs_re_trace_mul_le_frobenius _ _
    _ ≤ (Real.sqrt (Fintype.card ι : ℝ) / μ * M) *
        (Real.sqrt (Fintype.card ι : ℝ) / μ * d) :=
      mul_le_mul hU hV (norm_nonneg _) (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hμ.le) hM)
    _ = (Real.sqrt (Fintype.card ι : ℝ) / μ) ^ 2 * M * d := by ring
    _ = ((Fintype.card ι : ℝ) / μ ^ 2) * M * d := by rw [div_pow, hsqrt]

open scoped Matrix.Norms.Elementwise in
private theorem continuousOn_trace_resolvent_path (A X Y : Matrix ι ι 𝕜)
    (hsegment : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (A + (1 - s) • Y + s • X).PosDef) :
    ContinuousOn
      (fun s : ℝ => RCLike.re
        ((A + (1 - s) • Y + s • X)⁻¹ * (X - Y)).trace)
      (Set.Icc (0 : ℝ) 1) := by
  let B : ℝ → Matrix ι ι 𝕜 := fun s => A + (1 - s) • Y + s • X
  have hBcont : Continuous B := by
    dsimp [B]
    fun_prop
  intro s hs
  have hBs : (B s).PosDef := by simpa [B] using hsegment s hs
  have hunit : IsUnit (B s).det := (ne_of_gt hBs.det_pos).isUnit
  have hInv : ContinuousAt (fun t : ℝ => (B t)⁻¹) s := by
    exact (Matrix.contDiffAt_inv hunit).continuousAt.comp hBcont.continuousAt
  have hmat : ContinuousAt (fun t : ℝ => (B t)⁻¹ * (X - Y)) s :=
    hInv.mul continuousAt_const
  have htrace : ContinuousAt
      (fun t : ℝ => RCLike.re ((B t)⁻¹ * (X - Y)).trace) s := by
    exact RCLike.continuous_re.continuousAt.comp
      (continuous_id.matrix_trace.continuousAt.comp hmat)
  exact htrace.continuousWithinAt

theorem logDetTaylorRemainder_sub_bound (A X Y : Matrix ι ι 𝕜) (μ : ℝ)
    (hμ : 0 < μ) (hA : A.PosDef)
    (hAinv : ‖A⁻¹‖ ≤ Real.sqrt (Fintype.card ι : ℝ) / μ)
    (hsegment : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (A + (1 - s) • Y + s • X).PosDef)
    (hsegmentInv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(A + (1 - s) • Y + s • X)⁻¹‖ ≤ Real.sqrt (Fintype.card ι : ℝ) / μ) :
    |logDetTaylorRemainder A X - logDetTaylorRemainder A Y| ≤
      ((Fintype.card ι : ℝ) / μ ^ 2) * max ‖X‖ ‖Y‖ * ‖X - Y‖ := by
  let B : ℝ → Matrix ι ι 𝕜 := fun s => A + (1 - s) • Y + s • X
  let D : Matrix ι ι 𝕜 := X - Y
  let F : ℝ → ℝ := fun s => Real.log (RCLike.re (B s).det)
  let T : ℝ → ℝ := fun s => RCLike.re ((B s)⁻¹ * D).trace
  let K : ℝ := RCLike.re (A⁻¹ * D).trace
  let Q : ℝ → ℝ := fun s => T s - K
  let C : ℝ := ((Fintype.card ι : ℝ) / μ ^ 2) * max ‖X‖ ‖Y‖ * ‖D‖
  have h_affine (s t : ℝ) : B (s + t) = B s + t • D := by
    dsimp [B, D]
    module
  have hFderiv (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt F (T s) s := by
    have hBs : (B s).PosDef := by simpa [B] using hsegment s hs
    have hlog := Matrix.PosDef.hasDerivAt_log_det_add_smul hBs D
    have hshift : HasDerivAt (fun t : ℝ => t - s) 1 s := by
      simpa using (hasDerivAt_id s).sub_const s
    have hline : (fun t : ℝ => B s + (t - s) • D) = fun t => B t := by
      funext t
      rw [← h_affine s (t - s)]
      congr 1; ring
    have hlogAt : HasDerivAt
        (fun t : ℝ => Real.log (RCLike.re (B s + (t - s) • D).det))
        (RCLike.re ((B s)⁻¹ * D).trace) s := by
      simpa [Function.comp_def] using hlog.comp_of_eq s hshift (by simp)
    have hFline : F =
        (fun t : ℝ => Real.log (RCLike.re (B s + (t - s) • D).det)) := by
      funext t
      dsimp [F]
      rw [← congrFun hline t]
    rw [hFline]
    simpa [T] using hlogAt
  have hTcontinuous : ContinuousOn T (Set.Icc (0 : ℝ) 1) := by
    simpa [T, B, D] using continuousOn_trace_resolvent_path A X Y hsegment
  have hQcontinuous : ContinuousOn Q (Set.Icc (0 : ℝ) 1) := by
    dsimp [Q]
    exact hTcontinuous.sub continuousOn_const
  have hTint : IntervalIntegrable T MeasureTheory.volume (0 : ℝ) 1 :=
    hTcontinuous.intervalIntegrable_of_Icc zero_le_one
  have hKint : IntervalIntegrable (fun _ : ℝ => K) MeasureTheory.volume 0 1 := by
    exact intervalIntegrable_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (f := F) (f' := T)
    (fun s hs => by
      apply hFderiv s
      simpa [Set.uIcc_of_le zero_le_one] using hs)
    hTint
  have hQFTC : (∫ s in (0 : ℝ)..1, Q s) = (F 1 - F 0) - K := by
    calc
      (∫ s in (0 : ℝ)..1, Q s) =
          (∫ s in (0 : ℝ)..1, T s) - ∫ s in (0 : ℝ)..1, (fun _ : ℝ => K) s := by
        simp only [Q, intervalIntegral.integral_sub hTint hKint]
      _ = (F 1 - F 0) - K := by rw [hFTC]; simp [intervalIntegral.integral_const]
  have hnormH (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      ‖(1 - s) • Y + s • X‖ ≤ max ‖X‖ ‖Y‖ := by
    have hs0 := hs.1
    have hs1 := hs.2
    have hcoeff0 : 0 ≤ 1 - s := by linarith
    have hcoeff1 : 0 ≤ s := hs0
    calc
      ‖(1 - s) • Y + s • X‖ ≤ ‖(1 - s) • Y‖ + ‖s • X‖ := norm_add_le _ _
      _ = (1 - s) * ‖Y‖ + s * ‖X‖ := by
        simp [norm_smul, abs_of_nonneg hcoeff0, abs_of_nonneg hcoeff1]
      _ ≤ (1 - s) * max ‖X‖ ‖Y‖ + s * max ‖X‖ ‖Y‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_max_right ‖X‖ ‖Y‖) hcoeff0)
          (mul_le_mul_of_nonneg_left (le_max_left ‖X‖ ‖Y‖) hcoeff1)
      _ = max ‖X‖ ‖Y‖ := by ring
  have hQbound (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : |Q s| ≤ C := by
    have hBs : (B s).PosDef := by simpa [B] using hsegment s hs
    have hBinv : ‖(B s)⁻¹‖ ≤ Real.sqrt (Fintype.card ι : ℝ) / μ := hsegmentInv s hs
    have hZ : ‖(1 - s) • Y + s • X‖ ≤ max ‖X‖ ‖Y‖ := hnormH s hs
    have hB : B s = A + ((1 - s) • Y + s • X) := by
      dsimp [B]
      rw [add_assoc]
    have hres := abs_re_resolvent_trace_le_frobenius A ((1 - s) • Y + s • X) D (B s)
      μ (max ‖X‖ ‖Y‖) ‖D‖ hμ hA hBs hAinv hBinv hZ le_rfl hB
    have hEq : Q s = RCLike.re (((B s)⁻¹ - A⁻¹) * D).trace := by
      simp [Q, T, K, Matrix.sub_mul, Matrix.trace_sub, map_sub, D]
    rw [hEq]
    simpa [C, D] using hres
  have hQint : IntervalIntegrable Q MeasureTheory.volume (0 : ℝ) 1 :=
    hQcontinuous.intervalIntegrable_of_Icc zero_le_one
  have hQnorm : ‖∫ s in (0 : ℝ)..1, Q s‖ ≤ C := by
    calc
      ‖∫ s in (0 : ℝ)..1, Q s‖ ≤ C * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
          rw [Real.norm_eq_abs]
          have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
            rw [Set.uIoc_of_le zero_le_one] at hs
            exact ⟨hs.1.le, hs.2⟩
          exact hQbound s hs')
      _ = C := by norm_num
  have hEndpoint : logDetTaylorRemainder A X - logDetTaylorRemainder A Y =
      (F 1 - F 0) - K := by
    simp [F, K, B, D, logDetTaylorRemainder, Matrix.mul_sub, Matrix.trace_sub, map_sub]
    ring
  rw [hEndpoint, ← hQFTC]
  simpa [C, D, Real.norm_eq_abs] using hQnorm

end Matrix
