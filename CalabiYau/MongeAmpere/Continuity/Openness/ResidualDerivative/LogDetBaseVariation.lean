module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetMatrixRemainder
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Change of base in the log-determinant Taylor remainder

The chartwise Hölder seminorm also compares remainders at distinct base matrices. This requires a
separate third-order control in the base variable; the statement uses a uniform inverse bound on the
whole positive rectangle and does not assume an unverified dimension-dependent constant.
-/

@[expose] public section

open scoped ComplexOrder ContDiff NNReal Matrix.Norms.Frobenius
open Filter Topology

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*} [RCLike 𝕜]

private theorem inv_sub_inv_norm_bound (P Q : Matrix ι ι 𝕜) (M : ℝ)
    (hP : P.PosDef) (hQ : Q.PosDef) (hPinv : ‖P⁻¹‖ ≤ M) (hQinv : ‖Q⁻¹‖ ≤ M) :
    ‖P⁻¹ - Q⁻¹‖ ≤ M ^ 2 * ‖P - Q‖ := by
  have hres : P⁻¹ - Q⁻¹ = P⁻¹ * (Q - P) * Q⁻¹ :=
    Matrix.inv_sub_inv (iff_of_true hP.isUnit hQ.isUnit)
  have hM : 0 ≤ M := le_trans (norm_nonneg _) hPinv
  rw [hres]
  calc
    ‖P⁻¹ * (Q - P) * Q⁻¹‖ ≤ ‖P⁻¹‖ * ‖Q - P‖ * ‖Q⁻¹‖ := by
      calc
        ‖P⁻¹ * (Q - P) * Q⁻¹‖ ≤ ‖P⁻¹ * (Q - P)‖ * ‖Q⁻¹‖ := Matrix.frobenius_norm_mul _ _
        _ ≤ (‖P⁻¹‖ * ‖Q - P‖) * ‖Q⁻¹‖ := mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
        _ = ‖P⁻¹‖ * ‖Q - P‖ * ‖Q⁻¹‖ := by ring
    _ ≤ M * ‖Q - P‖ * M := by
      calc
        ‖P⁻¹‖ * ‖Q - P‖ * ‖Q⁻¹‖ ≤ M * ‖Q - P‖ * ‖Q⁻¹‖ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hPinv (norm_nonneg _)) (norm_nonneg _)
        _ ≤ M * ‖Q - P‖ * M := by
          exact mul_le_mul_of_nonneg_left hQinv (mul_nonneg hM (norm_nonneg _))
    _ = M ^ 2 * ‖P - Q‖ := by rw [norm_sub_rev]; ring

private theorem inv_sub_inv_eq (P Q : Matrix ι ι 𝕜) (hP : P.PosDef) (hQ : Q.PosDef) :
    P⁻¹ - Q⁻¹ = P⁻¹ * (Q - P) * Q⁻¹ :=
  Matrix.inv_sub_inv (iff_of_true hP.isUnit hQ.isUnit)

open scoped Matrix.Norms.Elementwise in
private theorem remainder_eq_integral (P H : Matrix ι ι 𝕜)
    (hpath : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → (P + t • H).PosDef) :
    logDetTaylorRemainder P H =
      ∫ t in (0 : ℝ)..1,
        (RCLike.re ((P + t • H)⁻¹ * H).trace - RCLike.re (P⁻¹ * H).trace) := by
  let B : ℝ → Matrix ι ι 𝕜 := fun t => P + t • H
  let F : ℝ → ℝ := fun t => Real.log (RCLike.re (B t).det)
  let T : ℝ → ℝ := fun t => RCLike.re ((B t)⁻¹ * H).trace
  let K : ℝ := RCLike.re (P⁻¹ * H).trace
  have hBcont : Continuous B := by dsimp [B]; fun_prop
  have hFderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt F (T t) t := by
    have hBt : (B t).PosDef := hpath t ht
    have hlog := Matrix.PosDef.hasDerivAt_log_det_add_smul hBt H
    have hshift : HasDerivAt (fun x : ℝ => x - t) 1 t := by simpa using (hasDerivAt_id t).sub_const t
    have hline : (fun x : ℝ => B t + (x - t) • H) = fun x => B x := by
      funext x
      dsimp [B]
      module
    have hlogAt : HasDerivAt (fun x : ℝ => Real.log (RCLike.re (B t + (x - t) • H).det))
        (RCLike.re ((B t)⁻¹ * H).trace) t := by
      simpa [Function.comp_def] using hlog.comp_of_eq t hshift (by simp)
    have hFline : F = fun x => Real.log (RCLike.re (B t + (x - t) • H).det) := by
      funext x
      dsimp [F]
      rw [← congrFun hline x]
    rw [hFline]
    simpa [T] using hlogAt
  have hTcont : ContinuousOn T (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have hBt : (B t).PosDef := hpath t ht
    have hunit : IsUnit (B t).det := (ne_of_gt hBt.det_pos).isUnit
    have hInv : ContinuousAt (fun x : ℝ => (B x)⁻¹) t :=
      (Matrix.contDiffAt_inv hunit).continuousAt.comp hBcont.continuousAt
    have hmul : ContinuousAt (fun x : ℝ => (B x)⁻¹ * H) t := hInv.mul continuousAt_const
    exact (RCLike.continuous_re.continuousAt).comp
      (continuous_id.matrix_trace.continuousAt.comp hmul) |>.continuousWithinAt
  have hTint : IntervalIntegrable T MeasureTheory.volume (0 : ℝ) 1 :=
    hTcont.intervalIntegrable_of_Icc zero_le_one
  have hKint : IntervalIntegrable (fun _ : ℝ => K) MeasureTheory.volume 0 1 := intervalIntegrable_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (f := F) (f' := T)
    (fun t ht => hFderiv t (by simpa [Set.uIcc_of_le zero_le_one] using ht)) hTint
  have hconst : (∫ t in (0 : ℝ)..1, (fun _ : ℝ => K) t) = K := by
    simp [intervalIntegral.integral_const]
  have hEq : (∫ t in (0 : ℝ)..1, (T t - K)) = (F 1 - F 0) - K := by
    rw [intervalIntegral.integral_sub hTint hKint, hFTC, hconst]
  have hEndpoints : logDetTaylorRemainder P H = (F 1 - F 0) - K := by
    simp [F, K, B, logDetTaylorRemainder]
  rw [hEndpoints]
  exact hEq.symm

open scoped Matrix.Norms.Elementwise in
private theorem continuousOn_remainder_integrand (P H : Matrix ι ι 𝕜)
    (hpath : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → (P + t • H).PosDef) :
    ContinuousOn (fun t : ℝ => RCLike.re ((P + t • H)⁻¹ * H).trace -
      RCLike.re (P⁻¹ * H).trace) (Set.Icc (0 : ℝ) 1) := by
  let B : ℝ → Matrix ι ι 𝕜 := fun t => P + t • H
  have hBcont : Continuous B := by dsimp [B]; fun_prop
  have hcont : ContinuousOn (fun t : ℝ => RCLike.re ((B t)⁻¹ * H).trace)
      (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have hBt := hpath t ht
    have hunit : IsUnit (B t).det := (ne_of_gt hBt.det_pos).isUnit
    have hInv : ContinuousAt (fun x : ℝ => (B x)⁻¹) t :=
      (Matrix.contDiffAt_inv hunit).continuousAt.comp hBcont.continuousAt
    have hmul : ContinuousAt (fun x : ℝ => (B x)⁻¹ * H) t := hInv.mul continuousAt_const
    exact (RCLike.continuous_re.continuousAt).comp
      (continuous_id.matrix_trace.continuousAt.comp hmul) |>.continuousWithinAt
  exact hcont.sub continuousOn_const

/-- Uniform two-base control for the first-order log-determinant remainder. A common inverse bound
on the rectangle swept out by the two bases and the perturbation yields a finite quadratic
remainder constant depending only on the dimension and that inverse bound. -/
theorem exists_logDetTaylorRemainder_baseVariation_bound (Mbound : ℝ≥0)
    (hMbound : 0 < Mbound) :
    ∃ C : ℝ≥0, ∀ A B H : Matrix ι ι 𝕜,
      (∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
        (A + (1 - s) • (B - A) + t • H).PosDef) →
      (∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
        ‖(A + (1 - s) • (B - A) + t • H)⁻¹‖ ≤ Mbound) →
      |logDetTaylorRemainder A H - logDetTaylorRemainder B H| ≤
        C * ‖A - B‖ * ‖H‖ ^ 2 := by
  let C : ℝ≥0 := 2 * Mbound ^ 3
  refine ⟨C, ?_⟩
  intro A B H hpath hinv
  let M : ℝ := (Mbound : ℝ)
  let D : Matrix ι ι 𝕜 := B - A
  let PA : ℝ → Matrix ι ι 𝕜 := fun t => A + t • H
  let PB : ℝ → Matrix ι ι 𝕜 := fun t => B + t • H
  have hpathA (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : (PA t).PosDef := by
    simpa [PA] using hpath 1 t (by norm_num) ht
  have hpathB (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : (PB t).PosDef := by
    simpa [PB] using hpath 0 t (by norm_num) ht
  have hinvA (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖(PA t)⁻¹‖ ≤ M := by
    have h := hinv 1 t (by norm_num) ht
    simpa [PA, M] using h
  have hinvB (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖(PB t)⁻¹‖ ≤ M := by
    have h := hinv 0 t (by norm_num) ht
    simpa [PB, M] using h
  have hbaseA : A.PosDef := by simpa [PA] using hpathA 0 (by norm_num)
  have hbaseB : B.PosDef := by simpa [PB] using hpathB 0 (by norm_num)
  have hAinv : ‖A⁻¹‖ ≤ M := by simpa [PA, M] using hinvA 0 (by norm_num)
  have hBinv : ‖B⁻¹‖ ≤ M := by simpa [PB, M] using hinvB 0 (by norm_num)
  have hIA : IntervalIntegrable
      (fun t : ℝ => RCLike.re ((PA t)⁻¹ * H).trace - RCLike.re (A⁻¹ * H).trace)
      MeasureTheory.volume 0 1 := by
    exact (continuousOn_remainder_integrand A H hpathA).intervalIntegrable_of_Icc zero_le_one
  have hIB : IntervalIntegrable
      (fun t : ℝ => RCLike.re ((PB t)⁻¹ * H).trace - RCLike.re (B⁻¹ * H).trace)
      MeasureTheory.volume 0 1 := by
    exact (continuousOn_remainder_integrand B H hpathB).intervalIntegrable_of_Icc zero_le_one
  have hRA := remainder_eq_integral A H hpathA
  have hRB := remainder_eq_integral B H hpathB
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      |(RCLike.re ((PA t)⁻¹ * H).trace - RCLike.re (A⁻¹ * H).trace) -
        (RCLike.re ((PB t)⁻¹ * H).trace - RCLike.re (B⁻¹ * H).trace)| ≤
      2 * M ^ 3 * ‖D‖ * ‖H‖ ^ 2 := by
    let PAₜ : Matrix ι ι 𝕜 := PA t
    let PBₜ : Matrix ι ι 𝕜 := PB t
    have hPA : PAₜ.PosDef := by simpa [PAₜ] using hpathA t ht
    have hPB : PBₜ.PosDef := by simpa [PBₜ] using hpathB t ht
    have hPAinv : ‖PAₜ⁻¹‖ ≤ M := by simpa [PAₜ] using hinvA t ht
    have hPBinv : ‖PBₜ⁻¹‖ ≤ M := by simpa [PBₜ] using hinvB t ht
    have hDA : ‖PAₜ⁻¹ - A⁻¹‖ ≤ M ^ 2 * ‖H‖ := by
      have h := inv_sub_inv_norm_bound PAₜ A M hPA hbaseA hPAinv hAinv
      have hnorm : ‖PAₜ - A‖ ≤ ‖H‖ := by
        dsimp [PAₜ, PA]
        calc
          ‖A + t • H - A‖ = ‖t • H‖ := by congr 1; abel
          _ = |t| * ‖H‖ := norm_smul _ _
          _ ≤ ‖H‖ := by
            rw [abs_of_nonneg ht.1]
            calc
              t * ‖H‖ ≤ 1 * ‖H‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg H)
              _ = ‖H‖ := by ring
      exact h.trans (mul_le_mul_of_nonneg_left hnorm (sq_nonneg M))
    have hDB : ‖PBₜ⁻¹ - B⁻¹‖ ≤ M ^ 2 * ‖H‖ := by
      have h := inv_sub_inv_norm_bound PBₜ B M hPB hbaseB hPBinv hBinv
      have hnorm : ‖PBₜ - B‖ ≤ ‖H‖ := by
        dsimp [PBₜ, PB]
        calc
          ‖B + t • H - B‖ = ‖t • H‖ := by congr 1; abel
          _ = |t| * ‖H‖ := norm_smul _ _
          _ ≤ ‖H‖ := by
            rw [abs_of_nonneg ht.1]
            calc
              t * ‖H‖ ≤ 1 * ‖H‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg H)
              _ = ‖H‖ := by ring
      exact h.trans (mul_le_mul_of_nonneg_left hnorm (sq_nonneg M))
    have hshift : PBₜ - PAₜ = D := by
      dsimp [PBₜ, PAₜ, PB, PA, D]
      module
    have hresPath : PAₜ⁻¹ - PBₜ⁻¹ = PAₜ⁻¹ * D * PBₜ⁻¹ := by
      rw [inv_sub_inv_eq PAₜ PBₜ hPA hPB, hshift]
    have hresBase : A⁻¹ - B⁻¹ = A⁻¹ * D * B⁻¹ := by
      simpa [D] using inv_sub_inv_eq A B hbaseA hbaseB
    have hmix : (PAₜ⁻¹ - PBₜ⁻¹) - (A⁻¹ - B⁻¹) =
        (PAₜ⁻¹ - A⁻¹) * D * PBₜ⁻¹ + A⁻¹ * D * (PBₜ⁻¹ - B⁻¹) := by
      rw [hresPath, hresBase]
      noncomm_ring
    have htrace :
        (RCLike.re (PAₜ⁻¹ * H).trace - RCLike.re (A⁻¹ * H).trace) -
          (RCLike.re (PBₜ⁻¹ * H).trace - RCLike.re (B⁻¹ * H).trace) =
        RCLike.re ((((PAₜ⁻¹ - A⁻¹) * D * PBₜ⁻¹ +
          A⁻¹ * D * (PBₜ⁻¹ - B⁻¹)) * H).trace) := by
      calc
        _ = RCLike.re (((PAₜ⁻¹ - PBₜ⁻¹) - (A⁻¹ - B⁻¹)) * H).trace := by
          simp [Matrix.sub_mul, Matrix.trace_sub, map_sub]; ring
        _ = _ := by rw [hmix]
    have hX : ‖(PAₜ⁻¹ - A⁻¹) * D * PBₜ⁻¹‖ ≤ M ^ 3 * ‖H‖ * ‖D‖ := by
      calc
        ‖(PAₜ⁻¹ - A⁻¹) * D * PBₜ⁻¹‖ ≤ ‖PAₜ⁻¹ - A⁻¹‖ * ‖D‖ * ‖PBₜ⁻¹‖ := by
          calc
            _ ≤ ‖(PAₜ⁻¹ - A⁻¹) * D‖ * ‖PBₜ⁻¹‖ := Matrix.frobenius_norm_mul _ _
            _ ≤ (‖PAₜ⁻¹ - A⁻¹‖ * ‖D‖) * ‖PBₜ⁻¹‖ :=
              mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
            _ = _ := by ring
        _ ≤ (M ^ 2 * ‖H‖) * ‖D‖ * M := by
          calc
            _ ≤ (M ^ 2 * ‖H‖) * ‖D‖ * ‖PBₜ⁻¹‖ := by gcongr
            _ ≤ (M ^ 2 * ‖H‖) * ‖D‖ * M := by
              exact mul_le_mul_of_nonneg_left hPBinv
                (mul_nonneg (mul_nonneg (sq_nonneg M) (norm_nonneg _)) (norm_nonneg _))
        _ = M ^ 3 * ‖H‖ * ‖D‖ := by ring
    have hY : ‖A⁻¹ * D * (PBₜ⁻¹ - B⁻¹)‖ ≤ M ^ 3 * ‖D‖ * ‖H‖ := by
      calc
        ‖A⁻¹ * D * (PBₜ⁻¹ - B⁻¹)‖ ≤ ‖A⁻¹‖ * ‖D‖ * ‖PBₜ⁻¹ - B⁻¹‖ := by
          calc
            _ ≤ ‖A⁻¹ * D‖ * ‖PBₜ⁻¹ - B⁻¹‖ := Matrix.frobenius_norm_mul _ _
            _ ≤ (‖A⁻¹‖ * ‖D‖) * ‖PBₜ⁻¹ - B⁻¹‖ :=
              mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
            _ = _ := by ring
        _ ≤ M * ‖D‖ * (M ^ 2 * ‖H‖) := by
          calc
            _ ≤ M * ‖D‖ * ‖PBₜ⁻¹ - B⁻¹‖ := by gcongr
            _ ≤ M * ‖D‖ * (M ^ 2 * ‖H‖) := by
              exact mul_le_mul_of_nonneg_left hDB
                (mul_nonneg (show 0 ≤ M by
                  change 0 ≤ (Mbound : ℝ)
                  exact_mod_cast hMbound.le) (norm_nonneg _))
        _ = M ^ 3 * ‖D‖ * ‖H‖ := by ring
    have htraceBound :
        |RCLike.re ((((PAₜ⁻¹ - A⁻¹) * D * PBₜ⁻¹ +
          A⁻¹ * D * (PBₜ⁻¹ - B⁻¹)) * H).trace)| ≤
          M ^ 3 * ‖H‖ * ‖D‖ * ‖H‖ + M ^ 3 * ‖D‖ * ‖H‖ * ‖H‖ := by
      calc
        _ ≤ |RCLike.re (((PAₜ⁻¹ - A⁻¹) * D * PBₜ⁻¹) * H).trace| +
            |RCLike.re ((A⁻¹ * D * (PBₜ⁻¹ - B⁻¹)) * H).trace| := by
          rw [Matrix.add_mul, Matrix.trace_add, map_add]
          exact abs_add_le _ _
        _ ≤ ‖(PAₜ⁻¹ - A⁻¹) * D * PBₜ⁻¹‖ * ‖H‖ +
            ‖A⁻¹ * D * (PBₜ⁻¹ - B⁻¹)‖ * ‖H‖ :=
          add_le_add (abs_re_trace_mul_le_frobenius _ _) (abs_re_trace_mul_le_frobenius _ _)
        _ ≤ M ^ 3 * ‖H‖ * ‖D‖ * ‖H‖ + M ^ 3 * ‖D‖ * ‖H‖ * ‖H‖ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hX (norm_nonneg _))
            (mul_le_mul_of_nonneg_right hY (norm_nonneg _))
    rw [← htrace] at htraceBound
    calc
      _ ≤ M ^ 3 * ‖H‖ * ‖D‖ * ‖H‖ + M ^ 3 * ‖D‖ * ‖H‖ * ‖H‖ := htraceBound
      _ = 2 * M ^ 3 * ‖D‖ * ‖H‖ ^ 2 := by ring
  have hdiff : logDetTaylorRemainder A H - logDetTaylorRemainder B H =
      ∫ t in (0 : ℝ)..1,
        ((RCLike.re ((PA t)⁻¹ * H).trace - RCLike.re (A⁻¹ * H).trace) -
          (RCLike.re ((PB t)⁻¹ * H).trace - RCLike.re (B⁻¹ * H).trace)) := by
    rw [hRA, hRB, intervalIntegral.integral_sub hIA hIB]
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ =>
      (RCLike.re ((PA t)⁻¹ * H).trace - RCLike.re (A⁻¹ * H).trace) -
        (RCLike.re ((PB t)⁻¹ * H).trace - RCLike.re (B⁻¹ * H).trace))
    (C := 2 * M ^ 3 * ‖D‖ * ‖H‖ ^ 2)
    (fun t ht => by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at ht
        exact ⟨ht.1.le, ht.2⟩
      simpa [Real.norm_eq_abs] using hpoint t ht')
  have hBound :
      |∫ t in (0 : ℝ)..1,
        ((RCLike.re ((PA t)⁻¹ * H).trace - RCLike.re (A⁻¹ * H).trace) -
          (RCLike.re ((PB t)⁻¹ * H).trace - RCLike.re (B⁻¹ * H).trace))| ≤
        2 * M ^ 3 * ‖D‖ * ‖H‖ ^ 2 := by
    simpa [Real.norm_eq_abs] using hIntegral
  have hCoeff : 2 * M ^ 3 = (C : ℝ) := by simp [C, M]
  have hDnorm : ‖D‖ = ‖A - B‖ := by
    dsimp [D]
    exact norm_sub_rev B A
  rw [hdiff]
  calc
    |∫ t in (0 : ℝ)..1,
        ((RCLike.re ((PA t)⁻¹ * H).trace - RCLike.re (A⁻¹ * H).trace) -
          (RCLike.re ((PB t)⁻¹ * H).trace - RCLike.re (B⁻¹ * H).trace))| ≤
        2 * M ^ 3 * ‖D‖ * ‖H‖ ^ 2 := hBound
    _ = (C : ℝ) * ‖A - B‖ * ‖H‖ ^ 2 := by rw [← hCoeff, hDnorm]

end Matrix
