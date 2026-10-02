module

public import CalabiYau.LinearAlgebra.Hermitian.LogDetDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.MetricSpace.Holder

open MeasureTheory
open scoped ComplexOrder Matrix.Norms.Frobenius NNReal Topology

namespace Matrix

private theorem logdet_line_integral
    {n : Type*} [Fintype n] [DecidableEq n]
    (A H : Matrix n n ℂ)
    (hpos : ∀ s ∈ Set.Icc (0 : ℝ) 1, (A + s • H).PosDef) :
    Real.log (RCLike.re (A + (1 : ℝ) • H).det) -
        Real.log (RCLike.re A.det) =
      ∫ s in (0 : ℝ)..1, RCLike.re (((A + s • H)⁻¹ * H).trace) := by
  let f : ℝ → ℝ := fun s => Real.log (RCLike.re (A + s • H).det)
  let fp : ℝ → ℝ := fun s => RCLike.re (((A + s • H)⁻¹ * H).trace)
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f (fp x) x := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    have hlog := (hpos x hx').hasDerivAt_log_det_add_smul H
    have hshift : HasDerivAt (fun y : ℝ => y - x) 1 x := by
      simpa using (hasDerivAt_id x).sub_const x
    have hcomp := HasDerivAt.comp_of_eq x hlog hshift (by simp)
    have hfun : (fun y : ℝ =>
        (fun t : ℝ => Real.log (RCLike.re (A + x • H + t • H).det)) (y - x)) = f := by
      funext y
      dsimp [f]
      rw [show A + x • H + (y - x) • H = A + y • H by module]
    have hfun' : ((fun t : ℝ => Real.log (RCLike.re (A + x • H + t • H).det)) ∘
        (fun y : ℝ => y - x)) =ᶠ[nhds x] f :=
      Filter.Eventually.of_forall (fun y => congrFun hfun y)
    have hcomp' := hcomp.congr_of_eventuallyEq hfun'.symm
    simpa [fp] using hcomp'
  have hfpDiff : ∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ fp x := by
    intro x hx
    have htrace := (hpos x hx).hasDerivAt_trace_inv_add_smul_mul H
    have hshift : HasDerivAt (fun y : ℝ => y - x) 1 x := by
      simpa using (hasDerivAt_id x).sub_const x
    have hcomp := HasDerivAt.comp_of_eq x htrace hshift (by simp)
    have hfun : (fun y : ℝ =>
        (fun t : ℝ => RCLike.re (((A + x • H + t • H)⁻¹ * H).trace)) (y - x)) = fp := by
      funext y
      dsimp [fp]
      rw [show A + x • H + (y - x) • H = A + y • H by module]
    have hfun' : (fun t : ℝ => RCLike.re (((A + x • H + t • H)⁻¹ * H).trace)) ∘
        (fun y : ℝ => y - x) =ᶠ[nhds x] fp :=
      Filter.Eventually.of_forall (fun y => congrFun hfun y)
    have hcomp' := hcomp.congr_of_eventuallyEq hfun'.symm
    exact hcomp'.differentiableAt
  have hint : IntervalIntegrable fp MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    exact (hfpDiff x hx').continuousAt.continuousWithinAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [f, fp] using hftc.symm

open scoped Matrix.Norms.Frobenius in
private theorem inverse_sub_inverse_resolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι] {𝕜 : Type*} [RCLike 𝕜]
    (A B : Matrix ι ι 𝕜) (hA : A.PosDef) (hB : B.PosDef) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ :=
  Matrix.inv_sub_inv (iff_of_true hA.isUnit hB.isUnit)

open scoped Matrix.Norms.Frobenius in
private theorem abs_re_trace_mul_le_frobenius
    {ι : Type*} [Fintype ι] {𝕜 : Type*} [RCLike 𝕜]
    (U V : Matrix ι ι 𝕜) :
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
    simp only [Fintype.sum_prod_type, f, Real.rpow_two, pow_two]
  have hgnorm : Real.sqrt (∑ ij : ι × ι, g ij ^ 2) = ‖V‖ := by
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    congr 1
    simp only [Fintype.sum_prod_type, g, Real.rpow_two, pow_two]
    rw [Finset.sum_comm]
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

open scoped Matrix.Norms.Frobenius in
/-- The spatial increment of the log-determinant path integrand, with the same denominator
margin on both paths. The resolvent difference is taken before estimating, so fixed-denominator
cancellation is retained. -/
private theorem logdet_path_integrand_spatial_increment_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝕜 : Type*} [RCLike 𝕜]
    (P Q E F : Matrix ι ι 𝕜) (s K H ε ρ : ℝ)
    (hP : (P + s • E).PosDef) (hQ : (Q + s • F).PosDef)
    (hPinv : ‖(P + s • E)⁻¹‖ ≤ K)
    (hQinv : ‖(Q + s • F)⁻¹‖ ≤ K)
    (hF : ‖F‖ ≤ ε) (hEF : ‖E - F‖ ≤ 2 * ε * ρ)
    (hpath : ‖(P + s • E) - (Q + s • F)‖ ≤ H * ρ)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hρ : 0 ≤ ρ) :
    |RCLike.re (((P + s • E)⁻¹ * E).trace) -
      RCLike.re (((Q + s • F)⁻¹ * F).trace)| ≤ (2 * K + K ^ 2 * H) * ε * ρ := by
  let A := P + s • E
  let B := Q + s • F
  have hres : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ :=
    inverse_sub_inverse_resolvent A B hP hQ
  have htrace : RCLike.re (A⁻¹ * E).trace - RCLike.re (B⁻¹ * F).trace =
      RCLike.re (A⁻¹ * (E - F) + (A⁻¹ - B⁻¹) * F).trace := by
    calc
      _ = RCLike.re ((A⁻¹ * E - B⁻¹ * F).trace) := by
        rw [Matrix.trace_sub, map_sub]
      _ = RCLike.re (A⁻¹ * (E - F) + (A⁻¹ - B⁻¹) * F).trace := by
        congr 2
        noncomm_ring
  have hAinv' : ‖A⁻¹‖ ≤ K := by simpa [A] using hPinv
  have hBinv' : ‖B⁻¹‖ ≤ K := by simpa [B] using hQinv
  have hBA : ‖B - A‖ ≤ H * ρ := by
    calc
      ‖B - A‖ = ‖A - B‖ := norm_sub_rev _ _
      _ = ‖(P + s • E) - (Q + s • F)‖ := by simp [A, B]
      _ ≤ H * ρ := hpath
  have hresnorm : ‖A⁻¹ - B⁻¹‖ ≤ K ^ 2 * H * ρ := by
    rw [hres]
    calc
      ‖A⁻¹ * (B - A) * B⁻¹‖ ≤ ‖A⁻¹‖ * ‖B - A‖ * ‖B⁻¹‖ := by
        calc
          ‖A⁻¹ * (B - A) * B⁻¹‖ ≤ ‖A⁻¹ * (B - A)‖ * ‖B⁻¹‖ := Matrix.frobenius_norm_mul _ _
          _ ≤ (‖A⁻¹‖ * ‖B - A‖) * ‖B⁻¹‖ :=
            mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _)
          _ = ‖A⁻¹‖ * ‖B - A‖ * ‖B⁻¹‖ := by ring
      _ ≤ K * (H * ρ) * K := by
        calc
          _ ≤ K * (H * ρ) * ‖B⁻¹‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact mul_le_mul hAinv' hBA (norm_nonneg _) hK
          _ ≤ K * (H * ρ) * K := by
            exact mul_le_mul_of_nonneg_left hBinv'
              (mul_nonneg hK (mul_nonneg hH hρ))
      _ = K ^ 2 * H * ρ := by ring
  have hterm₁ : |RCLike.re (A⁻¹ * (E - F)).trace| ≤ K * (2 * ε * ρ) := by
    calc
      _ ≤ ‖A⁻¹‖ * ‖E - F‖ := abs_re_trace_mul_le_frobenius _ _
      _ ≤ K * (2 * ε * ρ) := by gcongr
  have hterm₂ : |RCLike.re ((A⁻¹ - B⁻¹) * F).trace| ≤ (K ^ 2 * H * ρ) * ε := by
    calc
      _ ≤ ‖A⁻¹ - B⁻¹‖ * ‖F‖ := abs_re_trace_mul_le_frobenius _ _
      _ ≤ (K ^ 2 * H * ρ) * ε := by gcongr
  rw [htrace]
  calc
    |RCLike.re (A⁻¹ * (E - F) + (A⁻¹ - B⁻¹) * F).trace| ≤
        |RCLike.re (A⁻¹ * (E - F)).trace| +
          |RCLike.re ((A⁻¹ - B⁻¹) * F).trace| := by
      rw [Matrix.trace_add, map_add]
      exact abs_add_le _ _
    _ ≤ K * (2 * ε * ρ) + (K ^ 2 * H * ρ) * ε := add_le_add hterm₁ hterm₂
    _ = (2 * K + K ^ 2 * H) * ε * ρ := by ring

open scoped Matrix.Norms.Frobenius in
private theorem path_trace_intervalIntegrable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P E : Matrix ι ι ℂ)
    (hpath : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (P + s • E).PosDef) :
    IntervalIntegrable (fun s : ℝ => RCLike.re (((P + s • E)⁻¹ * E).trace))
      MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  intro s hs
  let f : ℝ → ℝ := fun y => RCLike.re (((P + y • E)⁻¹ * E).trace)
  let g : ℝ → ℝ := fun t => RCLike.re (((P + s • E + t • E)⁻¹ * E).trace)
  have htrace := (hpath s hs).hasDerivAt_trace_inv_add_smul_mul E
  have hshift : HasDerivAt (fun y : ℝ => y - s) 1 s := by
    simpa using (hasDerivAt_id s).sub_const s
  have hcomp := htrace.comp_of_eq s hshift (by simp)
  have hfun : (fun y : ℝ => g (y - s)) = f := by
    funext y
    dsimp [g, f]
    rw [show P + s • E + (y - s) • E = P + y • E by module]
  have hfun' : g ∘ (fun y : ℝ => y - s) =ᶠ[nhds s] f :=
    Filter.Eventually.of_forall (fun y => congrFun hfun y)
  have hcomp' := hcomp.congr_of_eventuallyEq hfun'.symm
  exact hcomp'.differentiableAt.continuousAt.continuousWithinAt

open scoped Matrix.Norms.Frobenius in
/-- A finite-dimensional mixed increment estimate for log-determinant outputs. The two FTC paths
share the same denominator controls; the fixed-denominator cancellation is used in the integrand
before the estimate is integrated. -/
public theorem logdet_segment_output_spatial_increment_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P Q E F : Matrix ι ι ℂ) (K H ε ρ : ℝ)
    (hPpath : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (P + s • E).PosDef)
    (hQpath : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (Q + s • F).PosDef)
    (hPinv : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖(P + s • E)⁻¹‖ ≤ K)
    (hQinv : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖(Q + s • F)⁻¹‖ ≤ K)
    (hF : ‖F‖ ≤ ε) (hEF : ‖E - F‖ ≤ 2 * ε * ρ)
    (hpath : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ‖(P + s • E) - (Q + s • F)‖ ≤ H * ρ)
    (hK : 0 ≤ K) (hH : 0 ≤ H) (hρ : 0 ≤ ρ) :
    |(Real.log (RCLike.re (P + E).det) - Real.log (RCLike.re P.det)) -
      (Real.log (RCLike.re (Q + F).det) - Real.log (RCLike.re Q.det))| ≤
        (2 * K + K ^ 2 * H) * ε * ρ := by
  have hIE := path_trace_intervalIntegrable P E hPpath
  have hIF := path_trace_intervalIntegrable Q F hQpath
  have hFTC₁ := logdet_line_integral P E hPpath
  have hFTC₂ := logdet_line_integral Q F hQpath
  have hFTC₁' : Real.log (RCLike.re (P + E).det) - Real.log (RCLike.re P.det) =
      ∫ s in (0 : ℝ)..1, RCLike.re (((P + s • E)⁻¹ * E).trace) := by
    simpa using hFTC₁
  have hFTC₂' : Real.log (RCLike.re (Q + F).det) - Real.log (RCLike.re Q.det) =
      ∫ s in (0 : ℝ)..1, RCLike.re (((Q + s • F)⁻¹ * F).trace) := by
    simpa using hFTC₂
  have hdiff :
      (Real.log (RCLike.re (P + E).det) - Real.log (RCLike.re P.det)) -
        (Real.log (RCLike.re (Q + F).det) - Real.log (RCLike.re Q.det)) =
        ∫ s in (0 : ℝ)..1,
          (RCLike.re (((P + s • E)⁻¹ * E).trace) -
            RCLike.re (((Q + s • F)⁻¹ * F).trace)) := by
    rw [hFTC₁', hFTC₂', intervalIntegral.integral_sub hIE hIF]
  have hIntBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun s : ℝ =>
      RCLike.re (((P + s • E)⁻¹ * E).trace) -
        RCLike.re (((Q + s • F)⁻¹ * F).trace))
    (C := (2 * K + K ^ 2 * H) * ε * ρ)
    (fun s hs => by
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le zero_le_one] at hs
        exact ⟨hs.1.le, hs.2⟩
      simpa [Real.norm_eq_abs] using logdet_path_integrand_spatial_increment_bound
        P Q E F s K H ε ρ (hPpath s hs') (hQpath s hs') (hPinv s hs') (hQinv s hs')
        hF hEF (hpath s hs') hK hH hρ)
  have hbound : |∫ s in (0 : ℝ)..1,
      (RCLike.re (((P + s • E)⁻¹ * E).trace) -
        RCLike.re (((Q + s • F)⁻¹ * F).trace))| ≤ (2 * K + K ^ 2 * H) * ε * ρ := by
    simpa [Real.norm_eq_abs] using hIntBound
  rw [hdiff]
  exact hbound

/-- Sup norm and mixed spatial increment control on positive matrix segments.
The matrix norm in every hypothesis is Frobenius. -/
public theorem logdet_difference_c0alpha_control
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [PseudoMetricSpace X] {s : Set X} {α K H ε : ℝ≥0}
    (A B : X → Matrix ι ι ℂ)
    (hsegment : ∀ x ∈ s, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (A x + t • (B x - A x)).PosDef ∧
      ‖(A x + t • (B x - A x))⁻¹‖ ≤ (K : ℝ))
    (hsegmentHolder : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HolderOnWith H α (fun x => A x + t • (B x - A x)) s)
    (hsup : ∀ x ∈ s, ‖B x - A x‖ ≤ (ε : ℝ))
    (hdiffHolder : HolderOnWith (2 * ε) α (fun x => B x - A x) s) :
    (∀ x ∈ s, ‖Real.log (RCLike.re (B x).det) -
      Real.log (RCLike.re (A x).det)‖ ≤ (K * ε : ℝ)) ∧
    HolderOnWith ((2 * K + K ^ 2 * H) * ε) α
      (fun x => Real.log (RCLike.re (B x).det) -
        Real.log (RCLike.re (A x).det)) s := by
  constructor
  · intro x hx
    have hFTC := logdet_line_integral (A x) (B x - A x)
      (fun t ht => (hsegment x hx t ht).1)
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => RCLike.re
        (((A x + t • (B x - A x))⁻¹ * (B x - A x)).trace))
      (C := (K * ε : ℝ)) (fun t ht => by
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
          rw [Set.uIoc_of_le zero_le_one] at ht
          exact ⟨ht.1.le, ht.2⟩
        calc
          _ = |RCLike.re (((A x + t • (B x - A x))⁻¹ * (B x - A x)).trace)| :=
            Real.norm_eq_abs _
          _ ≤ ‖(A x + t • (B x - A x))⁻¹‖ * ‖B x - A x‖ :=
            abs_re_trace_mul_le_frobenius _ _
          _ ≤ (K : ℝ) * ε := by
            exact mul_le_mul (hsegment x hx t ht').2 (hsup x hx)
              (norm_nonneg _) K.coe_nonneg)
    have heq : A x + (1 : ℝ) • (B x - A x) = B x := by module
    rw [heq] at hFTC
    rw [hFTC]
    simpa using hb
  · intro x hx y hy
    have hb := logdet_segment_output_spatial_increment_bound
      (A x) (A y) (B x - A x) (B y - A y)
      K H ε (dist x y ^ (α : ℝ))
      (fun t ht => (hsegment x hx t ht).1)
      (fun t ht => (hsegment y hy t ht).1)
      (fun t ht => (hsegment x hx t ht).2)
      (fun t ht => (hsegment y hy t ht).2) (hsup y hy)
      (by simpa [dist_eq_norm, NNReal.coe_mul] using hdiffHolder.dist_le hx hy)
      (fun t ht => by simpa [dist_eq_norm] using (hsegmentHolder t ht).dist_le hx hy)
      K.coe_nonneg H.coe_nonneg (Real.rpow_nonneg (dist_nonneg) _)
    have heqx : A x + (B x - A x) = B x := by module
    have heqy : A y + (B y - A y) = B y := by module
    rw [heqx, heqy] at hb
    have hdist : dist
        (Real.log (RCLike.re (B x).det) - Real.log (RCLike.re (A x).det))
        (Real.log (RCLike.re (B y).det) - Real.log (RCLike.re (A y).det)) ≤
        (((2 * K + K ^ 2 * H) * ε : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
      rw [Real.dist_eq]
      exact_mod_cast hb
    rw [edist_dist, edist_dist]
    calc
      _ ≤ ENNReal.ofReal
          ((((2 * K + K ^ 2 * H) * ε : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ)) :=
        ENNReal.ofReal_le_ofReal hdist
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]

end Matrix
