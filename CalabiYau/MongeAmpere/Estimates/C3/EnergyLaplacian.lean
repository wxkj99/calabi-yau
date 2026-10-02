module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.DerivativeSquares
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivativeBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound

/-!
# Calabi's energy Laplacian inequality

Székelyhidi, §3.3, Lemma 3.9, equations (3.11)–(3.15), p. 45, gives a lower bound for the
Laplacian of the squared difference of the two Kähler connections. For the CY equation,
`Ric(ωφ) = Ric(ω₀) - i∂∂̄G`; the uniform `C³` bound on `G` controls the derivatives of Ricci
appearing there. The metric comparison controls all remaining contractions.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- A five-covariant tensor contraction is controlled by the column norms of its frame matrix.
This is the abstract norm-transfer step used after controlling the tensor in an intrinsic metric
norm; it does not normalize chart-coordinate entries to be at most one. -/
private theorem c3_tensor5_frame_sum_bound
    (P : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (L D : ℝ) (hL : 0 ≤ L)
    (hcol : ∀ j, ∑ i : Fin n, ‖P i j‖ ^ 2 ≤ L ^ 2)
    (hT : ∀ a b c d e, ‖T a b c d e‖ ≤ D)
    (s p q j k : Fin n) :
    ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
      P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
        (n : ℝ) ^ 5 * L ^ 5 * D := by
  have hentry (i j : Fin n) : ‖P i j‖ ≤ L := by
    have hsq : ‖P i j‖ ^ 2 ≤ L ^ 2 := by
      calc
        ‖P i j‖ ^ 2 ≤ ∑ a : Fin n, ‖P a j‖ ^ 2 :=
          Finset.single_le_sum (fun a ha => sq_nonneg ‖P a j‖) (Finset.mem_univ i)
        _ ≤ L ^ 2 := hcol j
    nlinarith [sq_nonneg (‖P i j‖ - L)]
  have hterm (a b c d e : Fin n) :
      ‖P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
        L ^ 5 * D := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_star, norm_star]
    have hprod : ‖P a s‖ * ‖P b p‖ * ‖P c q‖ * ‖P d j‖ * ‖P e k‖ ≤ L ^ 5 := by
      calc
        ‖P a s‖ * ‖P b p‖ * ‖P c q‖ * ‖P d j‖ * ‖P e k‖ ≤
            L * L * L * L * L := by
          gcongr <;> exact hentry _ _
        _ = L ^ 5 := by ring
    calc
      (‖P a s‖ * ‖P b p‖ * ‖P c q‖ * ‖P d j‖ * ‖P e k‖) * ‖T a b c d e‖ ≤
          L ^ 5 * ‖T a b c d e‖ := mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ ≤ L ^ 5 * D := mul_le_mul_of_nonneg_left (hT a b c d e) (by positivity)
  calc
    ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
        P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ ≤
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
        ‖P a s * P b p * star (P c q) * P d j * star (P e k) * T a b c d e‖ := by
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro a ha
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro b hb
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro c hc
      apply le_trans (norm_sum_le _ _)
      apply Finset.sum_le_sum
      intro d hd
      exact norm_sum_le _ _
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
        L ^ 5 * D := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact hterm a b c d e
    _ = (n : ℝ) ^ 5 * L ^ 5 * D := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Full three-slot Ricci-derivative action bound. The factor `n^3` counts
all tensor components; the preceding one-slot estimate only counts one sum. -/
private theorem c3_frame_ricci_derivative_action_bound_three_slot
    {n : ℕ} (T V : Fin n → Fin n → Fin n → ℂ)
    (E L D : ℝ) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hT : ∀ i j k, ‖T i j k‖ ≤ L * Real.sqrt E)
    (hV : ∀ i j k, ‖V i j k‖ ≤ D * (1 + Real.sqrt E)) :
    ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
      (n : ℝ)^3 * L * D * (Real.sqrt E + E) := by
  have hs : Real.sqrt E * Real.sqrt E = E := by
    calc
      Real.sqrt E * Real.sqrt E = (Real.sqrt E) ^ 2 := by ring
      _ = E := Real.sq_sqrt hE
  have hterm (i j k : Fin n) :
      ‖T i j k * V i j k‖ ≤ L * D * (Real.sqrt E + E) := by
    rw [norm_mul]
    calc
      ‖T i j k‖ * ‖V i j k‖ ≤
          (L * Real.sqrt E) * (D * (1 + Real.sqrt E)) :=
        mul_le_mul (hT i j k) (hV i j k) (norm_nonneg _) (mul_nonneg hL (Real.sqrt_nonneg E))
      _ = L * D * (Real.sqrt E + Real.sqrt E * Real.sqrt E) := by ring
      _ = L * D * (Real.sqrt E + E) := by rw [hs]
  have hsum :
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := by
    calc
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
          ∑ i : Fin n, ‖∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖∑ k : Fin n, T i j k * V i j k‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact norm_sum_le _ _
  calc
    ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := hsum
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, L * D * (Real.sqrt E + E) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact hterm i j k
    _ = (n : ℝ)^3 * L * D * (Real.sqrt E + E) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- In a unitary frame, a nonnegative tensor energy controls each component. -/
private theorem c3_frame_tensor_component_bound_of_energy_sum
    {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k‖ ^ 2 ≤ E) :
    ∀ i j k, ‖T i j k‖ ≤ Real.sqrt E := by
  intro i j k
  have hk : ‖T i j k‖ ^ 2 ≤ ∑ l : Fin n, ‖T i j l‖ ^ 2 :=
    Finset.single_le_sum (fun l hl => sq_nonneg ‖T i j l‖) (Finset.mem_univ k)
  have hj : ∑ l : Fin n, ‖T i j l‖ ^ 2 ≤
      ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 := by
    calc
      ∑ l : Fin n, ‖T i j l‖ ^ 2 =
          (fun b : Fin n => ∑ l : Fin n, ‖T i b l‖ ^ 2) j := rfl
      _ ≤ ∑ b : Fin n, (fun b : Fin n => ∑ l : Fin n, ‖T i b l‖ ^ 2) b :=
        Finset.single_le_sum
          (fun b hb => Finset.sum_nonneg fun l hl => sq_nonneg ‖T i b l‖)
          (Finset.mem_univ j)
      _ = ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 := by rfl
  have hi : ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 ≤
      ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2 := by
    calc
      ∑ b : Fin n, ∑ l : Fin n, ‖T i b l‖ ^ 2 =
          (fun a : Fin n => ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2) i := rfl
      _ ≤ ∑ a : Fin n, (fun a : Fin n => ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2) a :=
        Finset.single_le_sum
          (fun a ha => Finset.sum_nonneg fun b hb =>
            Finset.sum_nonneg fun l hl => sq_nonneg ‖T a b l‖)
          (Finset.mem_univ i)
      _ = ∑ a : Fin n, ∑ b : Fin n, ∑ l : Fin n, ‖T a b l‖ ^ 2 := by rfl
  have hsq : ‖T i j k‖ ^ 2 ≤ E := hk.trans (hj.trans (hi.trans henergy))
  have hsqrt : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hnorm : 0 ≤ ‖T i j k‖ := norm_nonneg _
  nlinarith [Real.sq_sqrt hE]

/-- The full three-slot Ricci action is controlled by its component energy
and the pointwise growth bound for the contracted Ricci derivative. -/
private theorem c3_frame_ricci_derivative_action_bound_of_energy_sum
    {n : ℕ} (T V : Fin n → Fin n → Fin n → ℂ)
    (E D : ℝ) (hE : 0 ≤ E)
    (henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k‖ ^ 2 ≤ E)
    (hV : ∀ i j k, ‖V i j k‖ ≤ D * (1 + Real.sqrt E)) :
    ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
      (n : ℝ)^3 * D * (Real.sqrt E + E) := by
  have hs : Real.sqrt E * Real.sqrt E = E := by
    calc
      Real.sqrt E * Real.sqrt E = (Real.sqrt E) ^ 2 := by ring
      _ = E := Real.sq_sqrt hE
  have hT := c3_frame_tensor_component_bound_of_energy_sum T E hE henergy
  have hterm (i j k : Fin n) :
      ‖T i j k * V i j k‖ ≤ D * (Real.sqrt E + E) := by
    rw [norm_mul]
    calc
      ‖T i j k‖ * ‖V i j k‖ ≤ Real.sqrt E * (D * (1 + Real.sqrt E)) :=
        mul_le_mul (hT i j k) (hV i j k) (norm_nonneg _) (Real.sqrt_nonneg E)
      _ = D * (Real.sqrt E + Real.sqrt E * Real.sqrt E) := by ring
      _ = D * (Real.sqrt E + E) := by rw [hs]
  have hsum :
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := by
    calc
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
          ∑ i : Fin n, ‖∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖∑ k : Fin n, T i j k * V i j k‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact norm_sum_le _ _
  calc
    ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, T i j k * V i j k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ‖T i j k * V i j k‖ := hsum
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, D * (Real.sqrt E + E) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact hterm i j k
    _ = (n : ℝ)^3 * D * (Real.sqrt E + E) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Absorb the square-root energy error by the energy and a uniform constant.
This is the scalar Young inequality used after the Ricci-derivative action is
bounded by `C * (sqrt E + E)`. -/
private theorem c3_linear_sqrt_energy_absorbed
    (E K : ℝ) (hE : 0 ≤ E) :
    K * Real.sqrt E ≤ E + K ^ 2 / 4 := by
  have hsq : 0 ≤ (Real.sqrt E - K / 2) ^ 2 := sq_nonneg _
  have hroot : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE
  nlinarith

private theorem c3PartialBar_mul {n : ℕ}
    {u v : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    c3PartialBar (fun w ↦ u w * v w) z j =
      c3PartialBar u z j * v z + u z * c3PartialBar v z j := by
  unfold c3PartialBar
  rw [fderiv_fun_mul hu hv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem wirtingerDerivInChart_mul {n : ℕ}
    {u v : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    wirtingerDerivInChart (fun w ↦ u w * v w) z j =
      wirtingerDerivInChart u z j * v z + u z * wirtingerDerivInChart v z j := by
  unfold wirtingerDerivInChart
  rw [fderiv_fun_mul hu hv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem wirtingerDerivInChart_add {n : ℕ}
    {u v : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    wirtingerDerivInChart (fun w ↦ u w + v w) z j = wirtingerDerivInChart u z j + wirtingerDerivInChart v z j := by
  unfold wirtingerDerivInChart
  rw [fderiv_fun_add hu hv]
  simp only [_root_.add_apply]
  ring

private theorem c3PartialBar_differentiable_at {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    DifferentiableAt ℝ (fun w ↦ c3PartialBar f w j) z := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
    (hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num)
  have hDx : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ f w (EuclideanSpace.single j 1)) z := by
    exact (ContDiffAt.clm_apply hdf contDiffAt_const).differentiableAt (by norm_num)
  have hDy : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) z := by
    exact (ContDiffAt.clm_apply hdf contDiffAt_const).differentiableAt (by norm_num)
  change DifferentiableAt ℝ
    (fun w ↦ (fderiv ℝ f w (EuclideanSpace.single j 1) +
      Complex.I * fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) / 2) z
  fun_prop

private theorem wirtingerDerivInChart_differentiable_at {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    DifferentiableAt ℝ (fun w ↦ wirtingerDerivInChart f w j) z := by
  have hdf : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
    (hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num)
  have hDx : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ f w (EuclideanSpace.single j 1)) z := by
    exact (ContDiffAt.clm_apply hdf contDiffAt_const).differentiableAt (by norm_num)
  have hDy : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) z := by
    exact (ContDiffAt.clm_apply hdf contDiffAt_const).differentiableAt (by norm_num)
  change DifferentiableAt ℝ
    (fun w ↦ (fderiv ℝ f w (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ f w (Complex.I • EuclideanSpace.single j 1)) / 2) z
  fun_prop

/-- The mixed Wirtinger derivative, taken as `∂z` after `∂bar`. -/
private noncomputable def c3MixedZBar (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  wirtingerDerivInChart (fun w ↦ c3PartialBar f w j) z j

private theorem c3_partialBar_star_of_fderiv_star
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : fderiv ℝ (fun w ↦ star (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z)) :
    c3PartialBar (fun w ↦ star (f w)) z j = star (wirtingerDerivInChart f z j) := by
  unfold c3PartialBar wirtingerDerivInChart
  rw [hstar]
  simp [ContinuousLinearEquiv.coe_coe]

private theorem c3_partialZ_star_of_fderiv_star
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : fderiv ℝ (fun w ↦ star (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z)) :
    wirtingerDerivInChart (fun w ↦ star (f w)) z j = star (c3PartialBar f z j) := by
  unfold c3PartialBar wirtingerDerivInChart
  rw [hstar]
  simp [ContinuousLinearEquiv.coe_coe]
  ring

/-- The two real directional derivatives in the Hessian of a real-C² function commute. -/
private theorem c3_real_second_derivative_commute {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (x u v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fderiv ℝ f) x u v = fderiv ℝ (fderiv ℝ f) x v u := by
  have hs := ContDiffAt.isSymmSndFDerivAt (hf.contDiffAt (x := x)) (by norm_num)
  exact hs u v

private theorem c3_second_directional_fderiv {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (x u v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u =
      fderiv ℝ (fderiv ℝ f) x u v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.contDiffAt (x := x)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hc := fderiv_clm_apply hD (differentiableAt_const v)
  rw [hc]
  simp [ContinuousLinearMap.flip_apply]

private theorem c3_partialBar_deriv_apply {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z u : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    fderiv ℝ (fun y ↦ c3PartialBar f y j) z u =
      (fderiv ℝ (fderiv ℝ f) z u (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ (fderiv ℝ f) z u (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  have he : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hie : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hs : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    he.add (hie.const_mul Complex.I)
  unfold c3PartialBar
  rw [show (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) / 2) =
      (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) * (2 : ℂ)⁻¹) by
        funext y; rw [div_eq_mul_inv]]
  rw [fderiv_mul_const hs (2 : ℂ)⁻¹]
  rw [fderiv_fun_add he (hie.const_mul Complex.I)]
  rw [fderiv_const_mul hie Complex.I]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [c3_second_directional_fderiv f hf z u (EuclideanSpace.single j 1),
    c3_second_directional_fderiv f hf z u (Complex.I • EuclideanSpace.single j 1)]
  ring

private theorem c3_partialZ_deriv_apply {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z u : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    fderiv ℝ (fun y ↦ wirtingerDerivInChart f y j) z u =
      (fderiv ℝ (fderiv ℝ f) z u (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ (fderiv ℝ f) z u (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  have he : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hie : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf.contDiffAt (x := z)).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hs : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    he.sub (hie.const_mul Complex.I)
  unfold wirtingerDerivInChart
  rw [show (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) / 2) =
      (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) * (2 : ℂ)⁻¹) by
        funext y; rw [div_eq_mul_inv]]
  rw [fderiv_mul_const hs (2 : ℂ)⁻¹]
  rw [fderiv_fun_sub he (hie.const_mul Complex.I)]
  rw [fderiv_const_mul hie Complex.I]
  simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  rw [c3_second_directional_fderiv f hf z u (EuclideanSpace.single j 1),
    c3_second_directional_fderiv f hf z u (Complex.I • EuclideanSpace.single j 1)]
  ring

private theorem c3_mixedWirtinger_commute {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    wirtingerDerivInChart (fun w ↦ c3PartialBar f w j) z j =
      c3PartialBar (fun w ↦ wirtingerDerivInChart f w j) z j := by
  change (fderiv ℝ (fun w ↦ c3PartialBar f w j) z (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ (fun w ↦ c3PartialBar f w j) z
        (Complex.I • EuclideanSpace.single j 1)) / 2 =
    (fderiv ℝ (fun w ↦ wirtingerDerivInChart f w j) z (EuclideanSpace.single j 1) +
      Complex.I * fderiv ℝ (fun w ↦ wirtingerDerivInChart f w j) z
        (Complex.I • EuclideanSpace.single j 1)) / 2
  rw [c3_partialBar_deriv_apply f hf z (EuclideanSpace.single j 1) j,
    c3_partialBar_deriv_apply f hf z (Complex.I • EuclideanSpace.single j 1) j,
    c3_partialZ_deriv_apply f hf z (EuclideanSpace.single j 1) j,
    c3_partialZ_deriv_apply f hf z (Complex.I • EuclideanSpace.single j 1) j]
  have hcomm := c3_real_second_derivative_commute f hf z
    (EuclideanSpace.single j 1) (Complex.I • EuclideanSpace.single j 1)
  rw [hcomm]
  ring

/-- The two cross terms in the mixed derivative of a complex squared norm combine
into twice their real Hermitian pairing. -/
private theorem c3_real_star_cross (u v : ℂ) :
    RCLike.re (star u * v + star v * u) = 2 * RCLike.re (star u * v) := by
  change (star u * v + star v * u).re = 2 * (star u * v).re
  simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The algebraic product rule for a complex-valued mixed two-jet of a norm square:
its two first-jet contributions are the squared norms of the holomorphic and
antiholomorphic first derivatives. -/
private theorem c3_mixed_normSq_jet_algebra (f z b h : ℂ) :
    RCLike.re (h * star f + z * star z + b * star b + f * star h) =
      2 * RCLike.re (star f * h) + ‖z‖ ^ 2 + ‖b‖ ^ 2 := by
  have hcross := c3_real_star_cross f h
  have hnorm (w : ℂ) : RCLike.re (w * star w) = ‖w‖ ^ 2 := by
    have hw : (Complex.normSq w : ℂ) = w * star w := by
      simpa [mul_comm] using Complex.normSq_eq_conj_mul_self (z := w)
    calc
      RCLike.re (w * star w) = RCLike.re (Complex.normSq w : ℂ) := by rw [← hw]
      _ = Complex.normSq w := by simp
      _ = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq _
  change (h * star f + z * star z + b * star b + f * star h).re = _
  simp only [Complex.add_re]
  change RCLike.re (h * star f) + RCLike.re (z * star z) +
      RCLike.re (b * star b) + RCLike.re (f * star h) = _
  have hc : RCLike.re (h * star f + f * star h) =
      2 * RCLike.re (star f * h) := by
    convert hcross using 1
    simp [mul_comm]
  have hadd : RCLike.re (h * star f + f * star h) =
      RCLike.re (h * star f) + RCLike.re (f * star h) := by
    change (h * star f + f * star h).re = _
    exact Complex.add_re _ _
  rw [hnorm z, hnorm b, ← hc, hadd]
  abel_nf

private theorem c3_mixed_normSq_hessian_of_star_bridge
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : ∀ (g : EuclideanSpace ℂ (Fin n) → ℂ) (x : EuclideanSpace ℂ (Fin n)),
      DifferentiableAt ℝ g x →
        HasFDerivAt (fun w ↦ star (g w))
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x)) x) :
    RCLike.re (c3MixedZBar (fun w ↦ f w * star (f w)) z j) =
      ‖wirtingerDerivInChart f z j‖ ^ 2 + ‖c3PartialBar f z j‖ ^ 2 +
        2 * RCLike.re (star (f z) * c3MixedZBar f z j) := by
  let a : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wirtingerDerivInChart f x j
  let b : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar f x j
  let u : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ b x * star (f x)
  let v : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * star (a x)
  have hfdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hstarF (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun w ↦ star (f w))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f x)) x :=
    hstar f x (hfdiff x)
  have haDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ a x :=
    wirtingerDerivInChart_differentiable_at f hf x j
  have hbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ b x :=
    c3PartialBar_differentiable_at f hf x j
  have hstarA (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun w ↦ star (a w))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ a x)) x :=
    hstar a x (haDiff x)
  have hbar : (fun x ↦ c3PartialBar (fun w ↦ f w * star (f w)) x j) =
      (fun x ↦ u x + v x) := by
    funext x
    rw [c3PartialBar_mul (hfdiff x) (hstarF x).differentiableAt j]
    rw [c3_partialBar_star_of_fderiv_star f x j (hstarF x).fderiv]
  have hmix : c3MixedZBar (fun w ↦ f w * star (f w)) z j =
      wirtingerDerivInChart (fun x ↦ u x + v x) z j := by
    unfold c3MixedZBar
    rw [hbar]
  rw [hmix, wirtingerDerivInChart_add (u := u) (v := v)
    ((hbDiff z).mul (hstarF z).differentiableAt)
    ((hfdiff z).mul (hstarA z).differentiableAt) j]
  change RCLike.re (wirtingerDerivInChart (fun x ↦ b x * star (f x)) z j +
      wirtingerDerivInChart (fun x ↦ f x * star (a x)) z j) = _
  rw [wirtingerDerivInChart_mul (u := b) (v := fun x ↦ star (f x))
      (hbDiff z) (hstarF z).differentiableAt j,
    wirtingerDerivInChart_mul (u := f) (v := fun x ↦ star (a x))
      (hfdiff z) (hstarA z).differentiableAt j]
  rw [c3_partialZ_star_of_fderiv_star f z j (hstarF z).fderiv,
    c3_partialZ_star_of_fderiv_star a z j (hstarA z).fderiv,
    c3_mixedWirtinger_commute f hf z j]
  have hlast : c3PartialBar a z j = c3MixedZBar f z j :=
    (c3_mixedWirtinger_commute f hf z j).symm
  rw [hlast]
  have halpha : c3MixedZBar f z j = wirtingerDerivInChart b z j := rfl
  rw [halpha]
  have hjet := c3_mixed_normSq_jet_algebra
    (f z) (a z) (b z) (wirtingerDerivInChart b z j)
  simpa [a, b, add_assoc, add_left_comm, add_comm] using hjet

/-- For an arbitrary real-C² complex-valued function, the diagonal mixed derivative
of its squared norm has two first-derivative squares and the mixed-jet remainder. -/
private theorem c3_mixed_normSq_hessian
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (hf : ContDiff ℝ 2 f) (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    RCLike.re (c3MixedZBar (fun w ↦ f w * star (f w)) z j) =
      ‖wirtingerDerivInChart f z j‖ ^ 2 + ‖c3PartialBar f z j‖ ^ 2 +
        2 * RCLike.re (star (f z) * c3MixedZBar f z j) := by
  apply c3_mixed_normSq_hessian_of_star_bridge f hf z j
  intro g x hg
  have hconj : HasFDerivAt (fun w : ℂ ↦ star w)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) (g x) :=
    Complex.conjCLE.hasFDerivAt (x := g x)
  exact hconj.comp x hg.hasFDerivAt

/-- Jet-level Leibniz expansion for a varying Hermitian weight times a complex
squared norm. The first-jet terms of the weight are retained explicitly; its mixed
second jet is not discarded at a normal frame. -/
private theorem c3_weighted_normSq_mixed_jet_algebra
    (w wz wb wzb f z b h : ℂ) :
    RCLike.re (wzb * f * star f + wz * (b * star f + f * star z) +
      wb * (z * star f + f * star b) +
      w * (h * star f + b * star b + z * star z + f * star h)) =
      RCLike.re (wzb * f * star f + wz * b * star f + wz * f * star z +
        wb * z * star f + wb * f * star b + w * h * star f +
        w * b * star b + w * z * star z + w * f * star h) := by
  congr 1
  ring

/-- Actual mixed-jet Leibniz formula for a varying complex weight multiplying the
squared norm of a real-C² function. No first or second weight derivatives are
suppressed; this is the scalar contraction needed before summing a tensor norm. -/
private theorem c3_weighted_normSq_mixed_hessian_of_star_bridge
    (w f : EuclideanSpace ℂ (Fin n) → ℂ)
    (hw : ContDiff ℝ 2 w) (hf : ContDiff ℝ 2 f)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : ∀ (g : EuclideanSpace ℂ (Fin n) → ℂ) (x : EuclideanSpace ℂ (Fin n)),
      DifferentiableAt ℝ g x →
        HasFDerivAt (fun y ↦ star (g y))
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x)) x) :
    RCLike.re (c3MixedZBar (fun x ↦ w x * (f x * star (f x))) z j) =
      RCLike.re
        (c3MixedZBar w z j * (f z * star (f z)) +
          c3PartialBar w z j *
            (wirtingerDerivInChart f z j * star (f z) + f z * star (c3PartialBar f z j)) +
          wirtingerDerivInChart w z j *
            (c3PartialBar f z j * star (f z) + f z * star (wirtingerDerivInChart f z j)) +
          w z * c3MixedZBar (fun x ↦ f x * star (f x)) z j) := by
  let q : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * star (f x)
  let a : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wirtingerDerivInChart f x j
  let b : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar f x j
  let wz : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wirtingerDerivInChart w x j
  let wb : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar w x j
  let u : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wb x * q x
  let v : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ w x * c3PartialBar q x j
  have hwdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ w x :=
    (hw.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hfdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hstarW (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (w y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ w x)) x :=
    hstar w x (hwdiff x)
  have hstarF (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (f y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f x)) x :=
    hstar f x (hfdiff x)
  have haDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ a x :=
    wirtingerDerivInChart_differentiable_at f hf x j
  have hbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ b x :=
    c3PartialBar_differentiable_at f hf x j
  have hwzDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ wz x :=
    wirtingerDerivInChart_differentiable_at w hw x j
  have hwbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ wb x :=
    c3PartialBar_differentiable_at w hw x j
  have hstarA (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (a y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ a x)) x :=
    hstar a x (haDiff x)
  have hqDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ q x :=
    (hfdiff x).mul (hstarF x).differentiableAt
  have hbarQ : (fun x ↦ c3PartialBar q x j) =
      (fun x ↦ b x * star (f x) + f x * star (a x)) := by
    funext x
    rw [c3PartialBar_mul (hfdiff x) (hstarF x).differentiableAt j]
    rw [c3_partialBar_star_of_fderiv_star f x j (hstarF x).fderiv]
  have hZQ : (fun x ↦ wirtingerDerivInChart q x j) =
      (fun x ↦ a x * star (f x) + f x * star (b x)) := by
    funext x
    rw [wirtingerDerivInChart_mul (u := f) (v := fun y ↦ star (f y))
      (hfdiff x) (hstarF x).differentiableAt j]
    rw [c3_partialZ_star_of_fderiv_star f x j (hstarF x).fderiv]
  have hbarQDiff (x : EuclideanSpace ℂ (Fin n)) :
      DifferentiableAt ℝ (fun y ↦ c3PartialBar q y j) x := by
    rw [hbarQ]
    apply DifferentiableAt.add
    · exact (hbDiff x).mul (hstarF x).differentiableAt
    · exact (hfdiff x).mul (hstarA x).differentiableAt
  have hmixWQ : c3MixedZBar (fun x ↦ w x * q x) z j =
      wirtingerDerivInChart (fun x ↦ u x + v x) z j := by
    unfold c3MixedZBar
    change wirtingerDerivInChart (fun x ↦ c3PartialBar (fun y ↦ w y * q y) x j) z j = _
    rw [show (fun x ↦ c3PartialBar (fun y ↦ w y * q y) x j) =
        (fun x ↦ u x + v x) by
      funext x
      rw [c3PartialBar_mul (hwdiff x) (hqDiff x) j]]
  rw [hmixWQ, wirtingerDerivInChart_add (u := u) (v := v)
    ((hwbDiff z).mul (hqDiff z)) ((hwdiff z).mul (hbarQDiff z)) j]
  change RCLike.re
      (wirtingerDerivInChart (fun x ↦ wb x * q x) z j +
        wirtingerDerivInChart (fun x ↦ w x * c3PartialBar q x j) z j) = _
  rw [wirtingerDerivInChart_mul (u := wb) (v := q) (hwbDiff z) (hqDiff z) j,
    wirtingerDerivInChart_mul (u := w) (v := fun x ↦ c3PartialBar q x j)
      (hwdiff z) (hbarQDiff z) j]
  have hbarQz := congrFun hbarQ z
  have hZQz := congrFun hZQ z
  rw [show wirtingerDerivInChart wb z j = c3MixedZBar w z j by rfl,
    show wirtingerDerivInChart (fun x ↦ c3PartialBar q x j) z j = c3MixedZBar q z j by rfl,
    hbarQz, hZQz]
  congr 1
  ring

/-- Bilinear mixed-jet Leibniz formula for a varying scalar weight and two
independent component fields. This preserves off-diagonal tensor-norm terms
`w * F * star U`, including both first jets and the mixed second jet of `w`. -/
private theorem c3_weighted_pair_mixed_hessian_of_star_bridge
    (w f u : EuclideanSpace ℂ (Fin n) → ℂ)
    (hw : ContDiff ℝ 2 w) (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hstar : ∀ (g : EuclideanSpace ℂ (Fin n) → ℂ) (x : EuclideanSpace ℂ (Fin n)),
      DifferentiableAt ℝ g x →
        HasFDerivAt (fun y ↦ star (g y))
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ g x)) x) :
    RCLike.re (c3MixedZBar (fun x ↦ w x * (f x * star (u x))) z j) =
      RCLike.re
        (c3MixedZBar w z j * (f z * star (u z)) +
          c3PartialBar w z j *
            (wirtingerDerivInChart f z j * star (u z) + f z * star (c3PartialBar u z j)) +
          wirtingerDerivInChart w z j *
            (c3PartialBar f z j * star (u z) + f z * star (wirtingerDerivInChart u z j)) +
          w z *
            (c3MixedZBar f z j * star (u z) +
              c3PartialBar f z j * star (c3PartialBar u z j) +
              wirtingerDerivInChart f z j * star (wirtingerDerivInChart u z j) +
              f z * star (c3MixedZBar u z j))) := by
  let p : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * star (u x)
  let a : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wirtingerDerivInChart f x j
  let b : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar f x j
  let c : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wirtingerDerivInChart u x j
  let d : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar u x j
  let wz : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wirtingerDerivInChart w x j
  let wb : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ c3PartialBar w x j
  let v : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ w x * c3PartialBar p x j
  let r : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ wb x * p x
  let s : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ b x * star (u x)
  let t : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * star (c x)
  have hwdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ w x :=
    (hw.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hfdiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hudiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ u x :=
    (hu.contDiffAt (x := x)).differentiableAt (by norm_num)
  have hstarW (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (w y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ w x)) x :=
    hstar w x (hwdiff x)
  have hstarU (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (u y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ u x)) x :=
    hstar u x (hudiff x)
  have haDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ a x :=
    wirtingerDerivInChart_differentiable_at f hf x j
  have hbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ b x :=
    c3PartialBar_differentiable_at f hf x j
  have hcDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ c x :=
    wirtingerDerivInChart_differentiable_at u hu x j
  have hdDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ d x :=
    c3PartialBar_differentiable_at u hu x j
  have hwbDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ wb x :=
    c3PartialBar_differentiable_at w hw x j
  have hstarC (x : EuclideanSpace ℂ (Fin n)) :
      HasFDerivAt (fun y ↦ star (c y))
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ c x)) x :=
    hstar c x (hcDiff x)
  have hpDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ p x :=
    (hfdiff x).mul (hstarU x).differentiableAt
  have hbarP : (fun x ↦ c3PartialBar p x j) =
      (fun x ↦ s x + t x) := by
    funext x
    rw [c3PartialBar_mul (hfdiff x) (hstarU x).differentiableAt j]
    rw [c3_partialBar_star_of_fderiv_star u x j (hstarU x).fderiv]
  have hZP : (fun x ↦ wirtingerDerivInChart p x j) =
      (fun x ↦ a x * star (u x) + f x * star (d x)) := by
    funext x
    rw [wirtingerDerivInChart_mul (u := f) (v := fun y ↦ star (u y))
      (hfdiff x) (hstarU x).differentiableAt j]
    rw [c3_partialZ_star_of_fderiv_star u x j (hstarU x).fderiv]
  have hsDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ s x :=
    (hbDiff x).mul (hstarU x).differentiableAt
  have htDiff (x : EuclideanSpace ℂ (Fin n)) : DifferentiableAt ℝ t x :=
    (hfdiff x).mul (hstarC x).differentiableAt
  have hbarPDiff (x : EuclideanSpace ℂ (Fin n)) :
      DifferentiableAt ℝ (fun y ↦ c3PartialBar p y j) x := by
    rw [hbarP]
    exact (hsDiff x).add (htDiff x)
  have hbarWP : (fun x ↦ c3PartialBar (fun y ↦ w y * p y) x j) =
      (fun x ↦ wb x * p x + w x * c3PartialBar p x j) := by
    funext x
    exact c3PartialBar_mul (hwdiff x) (hpDiff x) j
  have hmixedWP : c3MixedZBar (fun x ↦ w x * p x) z j =
      wirtingerDerivInChart (fun x ↦ r x + v x) z j := by
    unfold c3MixedZBar
    change wirtingerDerivInChart (fun x ↦ c3PartialBar (fun y ↦ w y * p y) x j) z j = _
    rw [hbarWP]
  rw [hmixedWP, wirtingerDerivInChart_add (u := r) (v := v)
    ((hwbDiff z).mul (hpDiff z)) ((hwdiff z).mul (hbarPDiff z)) j]
  change RCLike.re
      (wirtingerDerivInChart (fun x ↦ wb x * p x) z j +
        wirtingerDerivInChart (fun x ↦ w x * c3PartialBar p x j) z j) = _
  rw [wirtingerDerivInChart_mul (u := w) (v := fun x ↦ c3PartialBar p x j)
      (hwdiff z) (hbarPDiff z) j,
    wirtingerDerivInChart_mul (u := wb) (v := p) (hwbDiff z) (hpDiff z) j]
  have hbarPz := congrFun hbarP z
  have hZPz := congrFun hZP z
  rw [show wirtingerDerivInChart wb z j = c3MixedZBar w z j by rfl,
    hbarPz, hZPz]
  have hbarPderiv : wirtingerDerivInChart (fun x ↦ c3PartialBar p x j) z j =
      wirtingerDerivInChart (fun x ↦ s x + t x) z j := by
    have hfun : (fun x ↦ c3PartialBar p x j) = (fun x ↦ s x + t x) := hbarP
    rw [hfun]
  rw [hbarPderiv, wirtingerDerivInChart_add (u := s) (v := t) (hsDiff z) (htDiff z) j]
  rw [wirtingerDerivInChart_mul (u := b) (v := fun x ↦ star (u x))
      (hbDiff z) (hstarU z).differentiableAt j,
    wirtingerDerivInChart_mul (u := f) (v := fun x ↦ star (c x))
      (hfdiff z) (hstarC z).differentiableAt j]
  rw [show wirtingerDerivInChart b z j = c3MixedZBar f z j by rfl,
    c3_partialZ_star_of_fderiv_star u z j (hstarU z).fderiv,
    c3_partialZ_star_of_fderiv_star c z j (hstarC z).fderiv,
    show c3PartialBar c z j = c3MixedZBar u z j by
      exact (c3_mixedWirtinger_commute u hu z j).symm]
  congr 1; ring

/-- Uniform CY form of Calabi's pointwise inequality `Δ_{ωφ} E ≥ -C E - C`.
Here `E = |Γ(gφ)-Γ(g₀)|²_{gφ}` uses the normalization in `CalabiEnergy`. -/
theorem exists_uniform_calabi_energy_laplacian_lower (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : (M → ℝ) × (M → ℝ)) (hp : p ∈ S) x,
      -(C * calabiEnergy ω₀ p.2 x + C) ≤
        (ω₀.perturb p.2 (hS p hp).2.1).laplacian (calabiEnergy ω₀ p.2) x := by
  obtain ⟨a, ha, haction⟩ := exists_uniform_c3BochnerRicciAction_bound ω₀ S hS hG hMetric
  obtain ⟨j, hj, hricci⟩ := exists_uniform_c3BochnerRicciDerivative_bound ω₀ S hS hG hMetric
  obtain ⟨K, hK, hcurv⟩ := ω₀.exists_uniform_reference_curvature_component_bound
  obtain ⟨A, hA, hderiv⟩ := ω₀.exists_uniform_c3ReferenceCurvatureCovariantDerivative_bound
  obtain ⟨r, hr, href⟩ := exists_uniform_c3BochnerReference_bound ω₀ S
    (fun p hp ↦ (hS p hp).2.1) hMetric K hK hcurv A hA hderiv
  refine ⟨a + 4 * (r + j) + 1, by positivity, ?_⟩
  intro p hp x
  have hpot := (hS p hp).2.1
  have hE := calabiEnergy_nonneg ω₀ hpot x
  have hbochner := calabiEnergy_laplacian_eq_bochner ω₀ hpot x
  have hconnection := c3BochnerConnectionTerm_eq_reference_sub_ricci ω₀ hpot x
  have hpositive := c3ConnectionDifference_derivativeSquares_nonneg ω₀ hpot x
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) (mem_extChartAt_target x)
  have hD : 0 ≤ c3BochnerDerivativeSquares ω₀ p.2 x := by
    dsimp only [c3BochnerDerivativeSquares, c3TensorCovariantZ, c3PerturbedMetricInChart]
    exact hpositive
  have hAlo := neg_le_of_abs_le (haction p hp x)
  have hRlo := neg_le_of_abs_le (href p hp x)
  have hJhi := le_of_abs_le (hricci p hp x)
  have hroot : Real.sqrt (calabiEnergy ω₀ p.2 x) ≤ calabiEnergy ω₀ p.2 x + 1 := by
    nlinarith [sq_nonneg (Real.sqrt (calabiEnergy ω₀ p.2 x) - 1), Real.sq_sqrt hE]
  have hscaled := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 2 * (r + j) by positivity)
  have hC : 2 * (r + j) ≤ a + 4 * (r + j) + 1 := by linarith
  have hprod : a * calabiEnergy ω₀ p.2 x +
      2 * (r + j) * (calabiEnergy ω₀ p.2 x + Real.sqrt (calabiEnergy ω₀ p.2 x)) ≤
      (a + 4 * (r + j) + 1) * calabiEnergy ω₀ p.2 x + (a + 4 * (r + j) + 1) := by
    nlinarith
  rw [hbochner, hconnection]
  nlinarith

end KahlerForm
