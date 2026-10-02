module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
import CalabiYau.MongeAmpere.Estimates.C2.MongeAmpereRicci
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound.UniformEndomorphismBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound.TensorContraction

/-!
# Uniform Ricci commutator contraction for a general Monge–Ampère family

Székelyhidi, §3.3, proof of Lemma 3.9, printed p. 45, the Ricci commutator
and (3.15). Instead of the Einstein specialization (3.11), use
`Ric(ωφ) = Ric(ω₀) - i∂∂̄G`. The fixed reference Ricci tensor and uniform
second derivatives of `G`, together with two-sided metric comparison,
control this quadratic action on the connection-difference tensor.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

open scoped ComplexOrder MatrixOrder

private theorem trace_bound_matrix_psd
    (Ω α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hω : Ω.IsPositive) (hα : α.IsNonneg) {B : ℝ}
    (htr : relTrace Ω α ≤ B) :
    ((B : ℂ) • Ω.coeffMatrix - α.coeffMatrix).PosSemidef := by
  have hΩn : Ω.IsNonneg := by
    refine ⟨hω.1, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst v
      have hz : (![0, Complex.I • (0 : EuclideanSpace ℂ (Fin n))] : Fin 2 →
          EuclideanSpace ℂ (Fin n)) = 0 := by
        funext i
        fin_cases i <;> simp
      rw [hz, ContinuousAlternatingMap.map_zero]
    · exact le_of_lt (hω.2 v hv)
  have hgap : 0 ≤ B - relTrace Ω α := sub_nonneg.mpr htr
  have hfirst : ((B - relTrace Ω α) • Ω).IsNonneg := by
    refine ⟨hΩn.1.smul _, ?_⟩
    intro v
    rw [ContinuousAlternatingMap.smul_apply]
    exact mul_nonneg hgap (hΩn.2 v)
  have htrace := isNonneg_relTrace_smul_sub hω hα
  have hsum : ((B - relTrace Ω α) • Ω + (relTrace Ω α • Ω - α)).IsNonneg := by
    refine ⟨hfirst.1.add htrace.1, ?_⟩
    intro v
    rw [ContinuousAlternatingMap.add_apply]
    exact add_nonneg (hfirst.2 v) (htrace.2 v)
  have hdecomp : B • Ω - α =
      (B - relTrace Ω α) • Ω + (relTrace Ω α • Ω - α) := by
    ext v
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply]
    module
  have hmatrix := (isNonneg_iff (α := B • Ω - α)).mp (hdecomp ▸ hsum)
  have hcoe : (B • Ω).coeffMatrix = (B : ℂ) • Ω.coeffMatrix := by
    rw [coeffMatrix_smul]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) B Ω.coeffMatrix
  have hmatrix₂ := hmatrix.2
  rw [coeffMatrix_sub] at hmatrix₂
  rw [hcoe] at hmatrix₂
  exact hmatrix₂

private theorem frame_reference_diagonal_le
    (g₀ g : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (B : ℝ) (hD : ((B : ℂ) • g - g₀).PosSemidef)
    (hP : P.transpose * g * P.map star = 1) (j : Fin n) :
    RCLike.re ((P.transpose * g₀ * P.map star) j j) ≤ B := by
  have hconj : Matrix.conjTranspose (P.map star) = P.transpose := by
    ext i k
    simp [Matrix.conjTranspose, Matrix.transpose]
  have htransformed := hD.conjTranspose_mul_mul_same (P.map star)
  rw [hconj] at htransformed
  have hdiag := htransformed.diag_nonneg (i := j)
  have hmatrix : P.transpose * ((B : ℂ) • g - g₀) * P.map star =
      (B : ℂ) • (P.transpose * g * P.map star) - P.transpose * g₀ * P.map star := by
    ext i k
    simp [Matrix.mul_sub, Matrix.sub_mul]
  rw [hmatrix, hP] at hdiag
  have hreal := (RCLike.le_iff_re_im.mp hdiag).1
  have hbound : 0 ≤ B - RCLike.re ((P.transpose * g₀ * P.map star) j j) := by
    simpa [Matrix.sub_apply, Matrix.smul_apply] using hreal
  linarith

omit [T2Space M] [CompactSpace M] in
private theorem c3_reference_frame_diagonal_le
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ) (x : M)
    {B : ℝ} (htr : relTrace (ω₀ x + mddbar n φ x) (ω₀ x) ≤ B)
    (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.transpose * c3PerturbedMetricInChart ω₀ φ x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star = 1)
    (j : Fin n) :
    RCLike.re ((P.transpose * ω₀.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star) j j) ≤ B := by
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    mem_extChartAt_target x
  have hmetric : (ω₀.perturb φ hφ).metricInChart x z =
      c3PerturbedMetricInChart ω₀ φ x z := by
    rw [metricInChart_perturb hφ x hz]
    rfl
  have htrace : relTrace ((ω₀.perturb φ hφ) x) (ω₀ x) ≤ B := by
    simpa [perturb_apply] using htr
  have hα : (ω₀ x).IsNonneg := by
    refine ⟨(ω₀.isPositive x).1, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst v
      have hv0 : (![0, Complex.I • (0 : EuclideanSpace ℂ (Fin n))] : Fin 2 →
          EuclideanSpace ℂ (Fin n)) = 0 := by
        funext i
        fin_cases i <;> simp
      rw [hv0, ContinuousAlternatingMap.map_zero]
    · exact le_of_lt ((ω₀.isPositive x).2 v hv)
  have hmat := trace_bound_matrix_psd ((ω₀.perturb φ hφ) x) (ω₀ x)
    ((ω₀.perturb φ hφ).isPositive x) hα htrace
  have hself : ω₀.metricInChart x z = (ω₀ x).coeffMatrix := by
    simpa [z] using ω₀.metricInChart_self x
  have hpertSelf : (ω₀.perturb φ hφ).metricInChart x z =
      ((ω₀.perturb φ hφ) x).coeffMatrix := by
    simpa [z] using (ω₀.perturb φ hφ).metricInChart_self x
  have hmat' : ((B : ℂ) • c3PerturbedMetricInChart ω₀ φ x z -
      ω₀.metricInChart x z).PosSemidef := by
    rw [← hmetric, hpertSelf, hself]
    exact hmat
  exact frame_reference_diagonal_le _ _ _ B hmat' hP j

private theorem c3_normalized_frame_upper {n : ℕ}
    (g B P : Matrix (Fin n) (Fin n) ℂ)
    (_hBP : B * P = 1) (hPB : P * B = 1)
    (hNorm : P.transpose * g * P.map star = 1) :
    ∀ i a, g i a = ∑ r, B r i * star (B r a) := by
  have hTranspose : B.transpose * P.transpose = 1 := by
    rw [← Matrix.transpose_mul, hPB, Matrix.transpose_one]
  have hConj : P.map star * B.map star = 1 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.map star) hPB
    simpa [Matrix.map_mul] using h
  have hG : g = B.transpose * B.map star := by
    calc
      g = 1 * g * 1 := by simp
      _ = (B.transpose * P.transpose) * g * (P.map star * B.map star) := by
        rw [hTranspose, hConj]
      _ = B.transpose * (P.transpose * g * P.map star) * B.map star := by
        noncomm_ring
      _ = B.transpose * 1 * B.map star := by rw [hNorm]
      _ = B.transpose * B.map star := by simp
  intro i a
  rw [hG, Matrix.mul_apply]
  simp [Matrix.transpose_apply, Matrix.map_apply]

private theorem c3_normalized_frame_lower {n : ℕ}
    (g B P : Matrix (Fin n) (Fin n) ℂ)
    (hBP : B * P = 1) (hPB : P * B = 1)
    (hNorm : P.transpose * g * P.map star = 1) :
    ∀ b j, g⁻¹ b j = ∑ r, P j r * star (P b r) := by
  have hUpper := c3_normalized_frame_upper g B P hBP hPB hNorm
  have hG : g = B.transpose * B.map star := by
    ext i a
    exact hUpper i a
  have hTranspose : P.transpose * B.transpose = 1 := by
    rw [← Matrix.transpose_mul, hBP, Matrix.transpose_one]
  have hConj : P.map star * B.map star = 1 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.map star) hPB
    simpa [Matrix.map_mul] using h
  have hInv : g⁻¹ = P.map star * P.transpose := by
    apply Matrix.inv_eq_left_inv
    rw [hG]
    calc
      P.map star * P.transpose * (B.transpose * B.map star) =
          P.map star * (P.transpose * B.transpose) * B.map star := by noncomm_ring
      _ = P.map star * 1 * B.map star := by rw [hTranspose]
      _ = P.map star * B.map star := by simp
      _ = 1 := hConj
  intro b j
  rw [hInv, Matrix.mul_apply]
  simp only [Matrix.map_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro r hr
  ring

private noncomputable def c3TensorFrameTransform {n : ℕ}
    (B P : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ) :
    Fin n → Fin n → Fin n → ℂ := fun i j k ↦
      ∑ a, ∑ b, ∑ c, B i a * P b j * P c k * T a b c

private theorem c3_star_sum {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    star (∑ i, f i) = ∑ i, star (f i) := by
  change starRingEnd ℂ (∑ i, f i) = _
  exact map_sum (starRingEnd ℂ) f Finset.univ

private theorem c3_fintype_mul_sum {ι : Type*} [Fintype ι] (a : ℂ) (f : ι → ℂ) :
    a * (∑ i, f i) = ∑ i, a * f i := by
  exact map_sum (AddMonoidHom.mulLeft a) f Finset.univ

private theorem c3_fintype_sum_mul {ι : Type*} [Fintype ι] (f : ι → ℂ) (a : ℂ) :
    (∑ i, f i) * a = ∑ i, f i * a := by
  exact map_sum (AddMonoidHom.mulRight a) f Finset.univ

set_option maxHeartbeats 1000000 in
private theorem c3Pair_eq_frame_components {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n))
    (B P : Matrix (Fin n) (Fin n) ℂ)
    (T U : Fin n → Fin n → Fin n → ℂ)
    (hUpper : ∀ i a, g i a = ∑ r, B r i * star (B r a))
    (hLower : ∀ b j, g⁻¹ b j = ∑ r, P j r * star (P b r)) :
    c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ g) z T U =
      ∑ i, ∑ j, ∑ k,
        c3TensorFrameTransform B P T i j k *
          star (c3TensorFrameTransform B P U i j k) := by
  classical
  unfold c3Pair c3TensorFrameTransform
  simp_rw [hUpper, hLower]
  simp_rw [c3_fintype_mul_sum, c3_fintype_sum_mul, c3_star_sum]
  let ι := Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × Fin n)))))) )
  let e : ι ≃ ι := {
    toFun := fun p ↦
      (p.2.2.2.2.2.2.2.2,
        (p.2.2.2.2.2.2.2.1,
          (p.2.2.2.2.2.2.1,
            (p.1, (p.2.1, (p.2.2.1,
              (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2.1))))))))
    invFun := fun p ↦
      (p.2.2.2.1,
        (p.2.2.2.2.1,
          (p.2.2.2.2.2.1,
            (p.2.2.2.2.2.2.1,
              (p.2.2.2.2.2.2.2.1,
                (p.2.2.2.2.2.2.2.2,
                  (p.2.2.1, (p.2.1, p.1))))))))
    left_inv := by intro p; simp [ι]
    right_inv := by intro p; simp [ι] }
  let f : ι → ℂ := fun p ↦
    B p.2.2.2.2.2.2.2.2 p.1 * star (B p.2.2.2.2.2.2.2.2 p.2.2.2.1) *
      (P p.2.1 p.2.2.2.2.2.2.2.1 * star (P p.2.2.2.2.1 p.2.2.2.2.2.2.2.1)) *
      (P p.2.2.1 p.2.2.2.2.2.2.1 * star (P p.2.2.2.2.2.1 p.2.2.2.2.2.2.1)) *
      T p.1 p.2.1 p.2.2.1 * star (U p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1)
  let g : ι → ℂ := fun p ↦
    B p.1 p.2.2.2.1 * P p.2.2.2.2.1 p.2.1 * P p.2.2.2.2.2.1 p.2.2.1 *
      T p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 *
        star (B p.1 p.2.2.2.2.2.2.1 * P p.2.2.2.2.2.2.2.1 p.2.1 *
          P p.2.2.2.2.2.2.2.2 p.2.2.1 *
          U p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2)
  have hsum : (∑ p : ι, f p) = ∑ p : ι, g p :=
    Fintype.sum_equiv e f g (by
      intro p
      change f p = g (p.2.2.2.2.2.2.2.2,
        (p.2.2.2.2.2.2.2.1, (p.2.2.2.2.2.2.1,
          (p.1, (p.2.1, (p.2.2.1,
            (p.2.2.2.1, (p.2.2.2.2.1, p.2.2.2.2.2.1))))))))
      simp only [f, g, ι, star_mul]
      ac_rfl)
  simpa only [ι, f, g, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    c3_fintype_mul_sum, c3_fintype_sum_mul, c3_star_sum] using hsum

private theorem c3RicciTensorAction_norm_le
    {n : ℕ} (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (i j k : Fin n) :
    ‖c3RicciTensorAction g T z i j k‖ ≤
      (∑ r, ‖c3RicciEndomorphism g z i r‖ * ‖T r j k‖) +
      (∑ r, ‖c3RicciEndomorphism g z r j‖ * ‖T i r k‖) +
      (∑ r, ‖c3RicciEndomorphism g z r k‖ * ‖T i j r‖) := by
  unfold c3RicciTensorAction
  calc
    ‖-(∑ r, c3RicciEndomorphism g z i r * T r j k) +
        ∑ r, c3RicciEndomorphism g z r j * T i r k +
        ∑ r, c3RicciEndomorphism g z r k * T i j r‖ ≤
      ‖∑ r, c3RicciEndomorphism g z i r * T r j k‖ +
        ‖∑ r, c3RicciEndomorphism g z r j * T i r k‖ +
        ‖∑ r, c3RicciEndomorphism g z r k * T i j r‖ := by
          calc
            ‖-(∑ r, c3RicciEndomorphism g z i r * T r j k) +
                ∑ r, c3RicciEndomorphism g z r j * T i r k +
                ∑ r, c3RicciEndomorphism g z r k * T i j r‖ ≤
              ‖-(∑ r, c3RicciEndomorphism g z i r * T r j k) +
                ∑ r, c3RicciEndomorphism g z r j * T i r k‖ +
                ‖∑ r, c3RicciEndomorphism g z r k * T i j r‖ := norm_add_le _ _
            _ ≤ (‖∑ r, c3RicciEndomorphism g z i r * T r j k‖ +
                ‖∑ r, c3RicciEndomorphism g z r j * T i r k‖) +
                ‖∑ r, c3RicciEndomorphism g z r k * T i j r‖ := by
              gcongr
              simpa [norm_neg] using norm_add_le
                (-(∑ r, c3RicciEndomorphism g z i r * T r j k))
                (∑ r, c3RicciEndomorphism g z r j * T i r k)
    _ ≤ (∑ r, ‖c3RicciEndomorphism g z i r‖ * ‖T r j k‖) +
        (∑ r, ‖c3RicciEndomorphism g z r j‖ * ‖T i r k‖) +
        (∑ r, ‖c3RicciEndomorphism g z r k‖ * ‖T i j r‖) := by
          gcongr
          · calc
              ‖∑ r, c3RicciEndomorphism g z i r * T r j k‖ ≤
                  ∑ r, ‖c3RicciEndomorphism g z i r * T r j k‖ := norm_sum_le _ _
              _ = ∑ r, ‖c3RicciEndomorphism g z i r‖ * ‖T r j k‖ := by
                    simp_rw [norm_mul]
          · calc
              ‖∑ r, c3RicciEndomorphism g z r j * T i r k‖ ≤
                  ∑ r, ‖c3RicciEndomorphism g z r j * T i r k‖ := norm_sum_le _ _
              _ = ∑ r, ‖c3RicciEndomorphism g z r j‖ * ‖T i r k‖ := by
                    simp_rw [norm_mul]
          · calc
              ‖∑ r, c3RicciEndomorphism g z r k * T i j r‖ ≤
                  ∑ r, ‖c3RicciEndomorphism g z r k‖ * ‖T i j r‖ := by
                    calc
                      ‖∑ r, c3RicciEndomorphism g z r k * T i j r‖ ≤
                          ∑ r, ‖c3RicciEndomorphism g z r k * T i j r‖ := norm_sum_le _ _
                      _ = ∑ r, ‖c3RicciEndomorphism g z r k‖ * ‖T i j r‖ := by
                        simp_rw [norm_mul]

private theorem c3Pair_real_abs_le_component_sum {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (A T : Fin n → Fin n → Fin n → ℂ) :
    |(c3Pair g z A T).re| ≤
      ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        ‖g z i a‖ * ‖(g z)⁻¹ b j‖ * ‖(g z)⁻¹ c k‖ *
          ‖A i j k‖ * ‖T a b c‖ := by
  unfold c3Pair
  calc
    |(∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k * A i j k * star (T a b c)).re| ≤
      ‖∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k * A i j k * star (T a b c)‖ :=
      Complex.abs_re_le_norm _
    _ ≤
      ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        ‖g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k * A i j k * star (T a b c)‖ := by
      let ι := Fin n × (Fin n × (Fin n × (Fin n × (Fin n × Fin n))))
      let f : ι → ℂ := fun p ↦
        g z p.1 p.2.2.2.1 * (g z)⁻¹ p.2.2.2.2.1 p.2.1 *
          (g z)⁻¹ p.2.2.2.2.2 p.2.2.1 * A p.1 p.2.1 p.2.2.1 *
            star (T p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      have hsum : ‖∑ p : ι, f p‖ ≤ ∑ p : ι, ‖f p‖ := norm_sum_le _ _
      simpa only [ι, f, Fintype.sum_prod_type] using hsum
    _ = ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        ‖g z i a‖ * ‖(g z)⁻¹ b j‖ * ‖(g z)⁻¹ c k‖ *
          ‖A i j k‖ * ‖T a b c‖ := by
      simp_rw [norm_mul, norm_star]

private def tensorCycleEquiv {n : ℕ} :
    (Fin n × (Fin n × Fin n)) ≃ (Fin n × (Fin n × Fin n)) where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun p := (p.2.1, p.2.2, p.1)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

private theorem tensor_energy_perm {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ‖T k i j‖ ^ 2) =
      ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2 := by
  let f : Fin n × (Fin n × Fin n) → ℝ := fun p ↦ ‖T p.2.2 p.1 p.2.1‖ ^ 2
  let g : Fin n × (Fin n × Fin n) → ℝ := fun p ↦ ‖T p.1 p.2.1 p.2.2‖ ^ 2
  have h := Fintype.sum_equiv tensorCycleEquiv f g (by intro p; rfl)
  simpa only [Fintype.sum_prod_type, f, g] using h

private theorem tensor_sum_const {n : ℕ} (r : ℝ) :
    (∑ _ : Fin n, r) = (n : ℝ) * r := by
  calc
    _ = ∑ i ∈ (Finset.univ : Finset (Fin n)), r := by simp
    _ = _ := by rw [Finset.sum_const]; simp [nsmul_eq_mul]

private theorem tensor_cross_sum_le {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ r, ‖T r j k‖ * ‖T i j k‖) ≤
      (n : ℝ) * (∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2) := by
  let ι := Fin n × (Fin n × (Fin n × Fin n))
  let f : ι → ℝ := fun p ↦ ‖T p.2.2.2 p.2.1 p.2.2.1‖
  let g : ι → ℝ := fun p ↦ ‖T p.1 p.2.1 p.2.2.1‖
  let E : ℝ := ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2
  have hcs : (∑ p : ι, f p * g p) ^ 2 ≤
      (∑ p : ι, f p ^ 2) * ∑ p : ι, g p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hsum : ∑ p : ι, f p * g p =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖T r j k‖ * ‖T i j k‖ := by
    simp only [ι, f, g, Fintype.sum_prod_type]
  have hf : ∑ p : ι, f p ^ 2 = (n : ℝ) * E := by
    simp only [ι, f, Fintype.sum_prod_type]
    calc
      _ = ∑ i : Fin n, ∑ j, ∑ k, ∑ r, ‖T r j k‖ ^ 2 := rfl
      _ = ∑ i : Fin n, E := by
        apply Fintype.sum_congr
        intro i
        simpa [E] using tensor_energy_perm T
      _ = ∑ i : Fin n, E := rfl
      _ = (n : ℝ) * E := tensor_sum_const E
  have hg : ∑ p : ι, g p ^ 2 = (n : ℝ) * E := by
    simp only [ι, g, Fintype.sum_prod_type]
    calc
      _ = ∑ i : Fin n, ∑ j, ∑ k, ∑ r, ‖T i j k‖ ^ 2 := rfl
      _ = ∑ i : Fin n, ∑ j, ∑ k, (n : ℝ) * ‖T i j k‖ ^ 2 := by
        apply Fintype.sum_congr
        intro i
        apply Fintype.sum_congr
        intro j
        apply Fintype.sum_congr
        intro k
        exact tensor_sum_const (‖T i j k‖ ^ 2)
      _ = (n : ℝ) * E := by simp [E, ← Finset.mul_sum]
  rw [hsum, hf, hg] at hcs
  have hnonneg : 0 ≤ ∑ i, ∑ j, ∑ k, ∑ r, ‖T r j k‖ * ‖T i j k‖ :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ Finset.sum_nonneg fun k _ ↦
      Finset.sum_nonneg fun r _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcs' : (∑ i, ∑ j, ∑ k, ∑ r, ‖T r j k‖ * ‖T i j k‖) ^ 2 ≤
      ((n : ℝ) * E) ^ 2 := by
    nlinarith [hcs]
  exact (sq_le_sq₀ hnonneg (mul_nonneg hn hE)).mp hcs'

private def tensorSwap12Equiv {n : ℕ} :
    (Fin n × (Fin n × Fin n)) ≃ (Fin n × (Fin n × Fin n)) where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv := by intro p; simp
  right_inv := by intro p; simp

private theorem tensor_energy_swap12 {n : ℕ} (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ‖T j i k‖ ^ 2) =
      ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2 := by
  let f : Fin n × (Fin n × Fin n) → ℝ := fun p ↦ ‖T p.2.1 p.1 p.2.2‖ ^ 2
  let g : Fin n × (Fin n × Fin n) → ℝ := fun p ↦ ‖T p.1 p.2.1 p.2.2‖ ^ 2
  have h := Fintype.sum_equiv tensorSwap12Equiv f g (by intro p; rfl)
  simpa only [Fintype.sum_prod_type, f, g] using h

private theorem tensor_cross_sum_le_second {n : ℕ}
    (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ r, ‖T i r k‖ * ‖T i j k‖) ≤
      (n : ℝ) * (∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2) := by
  let ι := Fin n × (Fin n × (Fin n × Fin n))
  let e : ι ≃ ι := {
    toFun := fun p ↦ (p.2.1, p.1, p.2.2.1, p.2.2.2)
    invFun := fun p ↦ (p.2.1, p.1, p.2.2.1, p.2.2.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp }
  let U : Fin n → Fin n → Fin n → ℂ := fun i j k ↦ T j i k
  let f : ι → ℝ := fun p ↦ ‖T p.2.1 p.2.2.2 p.2.2.1‖ * ‖T p.2.1 p.1 p.2.2.1‖
  let g : ι → ℝ := fun p ↦ ‖T p.1 p.2.2.2 p.2.2.1‖ * ‖T p.1 p.2.1 p.2.2.1‖
  have hsum : (∑ p : ι, f p) = ∑ p : ι, g p :=
    Fintype.sum_equiv e f g (by intro p; rfl)
  have h := tensor_cross_sum_le U
  have henergy : (∑ i, ∑ j, ∑ k, ‖U i j k‖ ^ 2) =
      ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2 := by
    simpa [U] using tensor_energy_swap12 T
  rw [henergy] at h
  have hf : (∑ p : ι, f p) =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖U r j k‖ * ‖U i j k‖ := by
    simp only [ι, f, U, Fintype.sum_prod_type]
  have hg : (∑ p : ι, g p) =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖T i r k‖ * ‖T i j k‖ := by
    simp only [ι, g, Fintype.sum_prod_type]
  rw [← hf, hsum, hg] at h
  exact h

private theorem tensor_cross_sum_le_third {n : ℕ}
    (T : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ r, ‖T i j r‖ * ‖T i j k‖) ≤
      (n : ℝ) * (∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2) := by
  let ι := Fin n × (Fin n × (Fin n × Fin n))
  let e : ι ≃ ι := {
    toFun := fun p ↦ (p.2.1, p.2.2.1, p.1, p.2.2.2)
    invFun := fun p ↦ (p.2.2.1, p.1, p.2.1, p.2.2.2)
    left_inv := by intro p; simp
    right_inv := by intro p; simp }
  let U : Fin n → Fin n → Fin n → ℂ := fun i j k ↦ T j k i
  let f : ι → ℝ := fun p ↦ ‖T p.2.1 p.2.2.1 p.2.2.2‖ * ‖T p.2.1 p.2.2.1 p.1‖
  let g : ι → ℝ := fun p ↦ ‖T p.1 p.2.1 p.2.2.2‖ * ‖T p.1 p.2.1 p.2.2.1‖
  have hsum : (∑ p : ι, f p) = ∑ p : ι, g p :=
    Fintype.sum_equiv e f g (by intro p; rfl)
  have h := tensor_cross_sum_le U
  have henergy : (∑ i, ∑ j, ∑ k, ‖U i j k‖ ^ 2) =
      ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2 := by
    simpa [U] using (tensor_energy_perm (fun i j k ↦ T j k i)).symm
  rw [henergy] at h
  have hf : (∑ p : ι, f p) =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖U r j k‖ * ‖U i j k‖ := by
    simp only [ι, f, U, Fintype.sum_prod_type]
  have hg : (∑ p : ι, g p) =
      ∑ i, ∑ j, ∑ k, ∑ r, ‖T i j r‖ * ‖T i j k‖ := by
    simp only [ι, g, Fintype.sum_prod_type]
  rw [← hf, hsum, hg] at h
  exact h

private def algebraicRicciAction {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) (i j k : Fin n) : ℂ :=
  -(∑ r, A i r * T r j k) +
    ∑ r, A r j * T i r k +
    ∑ r, A r k * T i j r

private theorem algebraicRicciAction_norm_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (K : ℝ) (hA : ∀ i j, ‖A i j‖ ≤ K) (i j k : Fin n) :
    ‖algebraicRicciAction A T i j k‖ ≤
      K * (∑ r, ‖T r j k‖) + K * (∑ r, ‖T i r k‖) + K * (∑ r, ‖T i j r‖) := by
  unfold algebraicRicciAction
  calc
    ‖-(∑ r, A i r * T r j k) + ∑ r, A r j * T i r k +
        ∑ r, A r k * T i j r‖ ≤
      ‖∑ r, A i r * T r j k‖ + ‖∑ r, A r j * T i r k‖ +
        ‖∑ r, A r k * T i j r‖ := by
      calc
        _ ≤ ‖-(∑ r, A i r * T r j k) + ∑ r, A r j * T i r k‖ +
            ‖∑ r, A r k * T i j r‖ := norm_add_le _ _
        _ ≤ _ := by
          simpa [norm_neg] using norm_add_le
            (-(∑ r, A i r * T r j k)) (∑ r, A r j * T i r k)
    _ ≤ (∑ r, ‖A i r‖ * ‖T r j k‖) +
        (∑ r, ‖A r j‖ * ‖T i r k‖) +
        (∑ r, ‖A r k‖ * ‖T i j r‖) := by
      gcongr
      · calc
          ‖∑ r, A i r * T r j k‖ ≤ ∑ r, ‖A i r * T r j k‖ := norm_sum_le _ _
          _ = _ := by simp_rw [norm_mul]
      · calc
          ‖∑ r, A r j * T i r k‖ ≤ ∑ r, ‖A r j * T i r k‖ := norm_sum_le _ _
          _ = _ := by simp_rw [norm_mul]
      · calc
          ‖∑ r, A r k * T i j r‖ ≤ ∑ r, ‖A r k * T i j r‖ := norm_sum_le _ _
          _ = _ := by simp_rw [norm_mul]
    _ ≤ K * (∑ r, ‖T r j k‖) + K * (∑ r, ‖T i r k‖) +
        K * (∑ r, ‖T i j r‖) := by
      calc
        _ ≤ (∑ r, K * ‖T r j k‖) + (∑ r, K * ‖T i r k‖) +
            (∑ r, K * ‖T i j r‖) := by
          apply add_le_add
          · apply add_le_add
            · exact Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_right (hA i r) (norm_nonneg _)
            · exact Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_right (hA r j) (norm_nonneg _)
          · exact Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_right (hA r k) (norm_nonneg _)
        _ = _ := by simp_rw [← Finset.mul_sum]

private theorem algebraicRicciAction_pair_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (K : ℝ) (hK : 0 ≤ K) (hA : ∀ i j, ‖A i j‖ ≤ K) :
    |(∑ i, ∑ j, ∑ k, algebraicRicciAction A T i j k * star (T i j k)).re| ≤
      (3 * (n : ℝ) * K) * (∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2) := by
  let E : ℝ := ∑ i, ∑ j, ∑ k, ‖T i j k‖ ^ 2
  have hcross1 := tensor_cross_sum_le T
  have hcross2 := tensor_cross_sum_le_second T
  have hcross3 := tensor_cross_sum_le_third T
  have hsum_norm :
      |(∑ i, ∑ j, ∑ k, algebraicRicciAction A T i j k * star (T i j k)).re| ≤
        ∑ i, ∑ j, ∑ k, ‖algebraicRicciAction A T i j k‖ * ‖T i j k‖ := by
    calc
      _ ≤ ‖∑ i, ∑ j, ∑ k,
          algebraicRicciAction A T i j k * star (T i j k)‖ := Complex.abs_re_le_norm _
      _ ≤ ∑ i, ∑ j, ∑ k,
          ‖algebraicRicciAction A T i j k * star (T i j k)‖ := by
        let ι := Fin n × (Fin n × Fin n)
        let f : ι → ℂ := fun p ↦
          algebraicRicciAction A T p.1 p.2.1 p.2.2 * star (T p.1 p.2.1 p.2.2)
        have h := norm_sum_le (Finset.univ : Finset ι) f
        simpa only [ι, f, Fintype.sum_prod_type] using h
      _ = _ := by simp_rw [norm_mul, norm_star]
  have hpoint i j k :
      ‖algebraicRicciAction A T i j k‖ * ‖T i j k‖ ≤
        K * (∑ r, ‖T r j k‖ * ‖T i j k‖) +
        K * (∑ r, ‖T i r k‖ * ‖T i j k‖) +
        K * (∑ r, ‖T i j r‖ * ‖T i j k‖) := by
    calc
      _ ≤ (K * (∑ r, ‖T r j k‖) + K * (∑ r, ‖T i r k‖) +
          K * (∑ r, ‖T i j r‖)) * ‖T i j k‖ :=
        mul_le_mul_of_nonneg_right (algebraicRicciAction_norm_le A T K hA i j k)
          (norm_nonneg _)
      _ = _ := by
        calc
          _ = K * ((∑ r, ‖T r j k‖) * ‖T i j k‖) +
              K * ((∑ r, ‖T i r k‖) * ‖T i j k‖) +
              K * ((∑ r, ‖T i j r‖) * ‖T i j k‖) := by ring
          _ = _ := by rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  let ι := Fin n × (Fin n × Fin n)
  have htotalFlat :
      (∑ p : ι, ‖algebraicRicciAction A T p.1 p.2.1 p.2.2‖ * ‖T p.1 p.2.1 p.2.2‖) ≤
        (3 * (n : ℝ) * K) * E := by
    calc
      _ ≤ (∑ p : ι, (K * (∑ r : Fin n, ‖T r p.2.1 p.2.2‖ * ‖T p.1 p.2.1 p.2.2‖) + K * (∑ r : Fin n, ‖T p.1 r p.2.2‖ * ‖T p.1 p.2.1 p.2.2‖) + K * (∑ r : Fin n, ‖T p.1 p.2.1 r‖ * ‖T p.1 p.2.1 p.2.2‖))) := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpoint p.1 p.2.1 p.2.2
      _ = K * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ r : Fin n, ‖T r j k‖ * ‖T i j k‖) +
          K * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ r : Fin n, ‖T i r k‖ * ‖T i j k‖) +
          K * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ r : Fin n, ‖T i j r‖ * ‖T i j k‖) := by
        simp only [ι, Fintype.sum_prod_type]
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ K * ((n : ℝ) * E) + K * ((n : ℝ) * E) + K * ((n : ℝ) * E) := by
        gcongr
      _ = (3 * (n : ℝ) * K) * E := by ring
  have htotal :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖algebraicRicciAction A T i j k‖ * ‖T i j k‖) ≤
        (3 * (n : ℝ) * K) * E := by
    simpa only [ι, Fintype.sum_prod_type] using htotalFlat
  exact hsum_norm.trans (by simpa [E] using htotal)

/-- Only the quadratic Ricci action is estimated; this is not a bound on
all of `Δ E`. The forcing family is general, not restricted to Einstein metrics. -/
theorem exists_uniform_c3BochnerRicciAction_bound (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ x,
      |c3BochnerRicciActionTerm ω₀ p.2 x| ≤ C * calabiEnergy ω₀ p.2 x := by
  classical
  let : PartialOrder ℂ := Complex.partialOrder
  obtain ⟨R, hR, hframe⟩ :=
    exists_uniform_c3RicciEndomorphism_frame_bound ω₀ S hS hG hMetric
  refine ⟨3 * (n : ℝ) * R, mul_nonneg (mul_nonneg (by norm_num)
    (Nat.cast_nonneg n)) hR, ?_⟩
  intro p hp x
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := c3PerturbedMetricInChart ω₀ p.2 x
  let T := c3ConnectionDifferenceInChart ω₀ p.2 x z
  obtain ⟨P, hP, hA⟩ := hframe p hp x
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source
      (mem_extChartAt_source x)
  have hg : (g z).PosDef := by
    have hpos := (ω₀.perturb p.2 (hS p hp).2.1).posDef_metricInChart x hz
    rw [ω₀.metricInChart_perturb (hS p hp).2.1 x hz] at hpos
    exact hpos
  have hbound := c3RicciTensorAction_pair_bound_of_unitary_frame g z T P R
    hg hP hR hA
  simpa only [c3BochnerRicciActionTerm, calabiEnergy, calabiEnergyInChart,
    c3Pair, c3PerturbedMetricInChart, RCLike.re_eq_complex_re, z, g, T] using hbound

end KahlerForm
