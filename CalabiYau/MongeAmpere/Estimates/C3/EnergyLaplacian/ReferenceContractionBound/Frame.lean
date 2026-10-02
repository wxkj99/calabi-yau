module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Basic

/-!
# Frame for the reference-curvature contraction

Székelyhidi, An Introduction to Extremal Kähler Metrics, §3.3, proof of Lemma 3.9, terms following (3.15), printed p. 45; finite tensor contraction algebra implementing that proof.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal BigOperators ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

theorem referenceContraction_simdiag
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (eigen : Fin n → ℝ),
      P.conjTranspose * A * P = 1 ∧
      P.conjTranspose * B * P = Matrix.diagonal (RCLike.ofReal ∘ eigen) ∧
      ∀ i, 0 < eigen i := by
  let S := CFC.sqrt A⁻¹
  have hSle : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ S := by
    change (0 : Matrix (Fin n) (Fin n) ℂ) ≤ CFC.sqrt A⁻¹
    exact CFC.sqrt_nonneg _
  have hSps : S.PosSemidef := by simpa using (Matrix.le_iff.mp hSle)
  have hS : S.conjTranspose = S := hSps.isHermitian.eq
  let R := CFC.sqrt A
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hRunit : IsUnit R := isUnit_of_mul_isUnit_left (hRR ▸ hA.isUnit)
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRunit
  have hSR : S = R⁻¹ := hA.posSemidef.inv_sqrt.symm
  have hSAS : S * A * S = 1 := by
    rw [hSR, ← hRR, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv R hRdet,
      Matrix.mul_one, Matrix.nonsing_inv_mul R hRdet]
  have hSunit : IsUnit S := by
    rw [hSR]
    exact Matrix.isUnit_nonsing_inv_iff.mpr hRunit
  have hSInjective : Function.Injective S.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hSunit
  have hCpos : (S * B * S).PosDef := by
    simpa [Matrix.star_eq_conjTranspose, hS] using hB.conjTranspose_mul_mul_same hSInjective
  have hC : (S * B * S).IsHermitian := by
    simpa only [hS] using Matrix.isHermitian_conjTranspose_mul_mul S hB.isHermitian
  let U := hC.eigenvectorUnitary
  let V : Matrix (Fin n) (Fin n) ℂ := U
  have hVstarV : star V * V = 1 := by
    change star (U : Matrix (Fin n) (Fin n) ℂ) * (U : Matrix (Fin n) (Fin n) ℂ) = 1
    exact Unitary.coe_star_mul_self U
  have hVdet : star V.det * V.det = 1 := by
    have hVstarV' : V.conjTranspose * V = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using hVstarV
    have h := congrArg Matrix.det hVstarV'
    simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] using h
  have hVdetNe : V.det ≠ 0 := by
    intro hzero
    simp [hzero] at hVdet
  have hVunit : IsUnit V :=
    (Matrix.isUnit_iff_isUnit_det V).mpr (isUnit_iff_ne_zero.mpr hVdetNe)
  have hVInjective : Function.Injective V.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hVunit
  have hCspec : star V * (S * B * S) * V =
      Matrix.diagonal (RCLike.ofReal ∘ hC.eigenvalues) := by
    have h := hC.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    exact h
  have hDiagPos :
      (Matrix.diagonal (RCLike.ofReal ∘ hC.eigenvalues) : Matrix (Fin n) (Fin n) ℂ).PosDef := by
    rw [← hCspec]
    simpa [Matrix.star_eq_conjTranspose] using hCpos.conjTranspose_mul_mul_same hVInjective
  let eigen := hC.eigenvalues
  refine ⟨S * V, eigen, ?_, ?_, ?_⟩
  · have h1 : star V * (S * A * S) * V = 1 := by
      rw [hSAS, Matrix.mul_one]
      exact hVstarV
    rw [Matrix.conjTranspose_mul, hS, ← Matrix.star_eq_conjTranspose]
    simpa only [Matrix.mul_assoc] using h1
  · rw [Matrix.conjTranspose_mul, hS, ← Matrix.star_eq_conjTranspose]
    simpa only [Matrix.mul_assoc] using hCspec
  · intro i
    have hi := (Matrix.posDef_diagonal_iff.mp hDiagPos) i
    simpa [eigen] using hi

theorem referenceContraction_simdiag_trace_id
    {n : ℕ} (A B P : Matrix (Fin n) (Fin n) ℂ) (eigen : Fin n → ℝ)
    (hPA : P.conjTranspose * A * P = 1)
    (hPB : P.conjTranspose * B * P = Matrix.diagonal (RCLike.ofReal ∘ eigen))
    (heigen : ∀ i, 0 < eigen i) :
    RCLike.re ((A⁻¹ * B).trace) = ∑ i, eigen i ∧
    RCLike.re ((B⁻¹ * A).trace) = ∑ i, (eigen i)⁻¹ := by
  have hPdet : IsUnit P.det := by
    have hdet : star P.det * A.det * P.det = 1 := by
      have h := congrArg Matrix.det hPA
      simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] using h
    have hPne : P.det ≠ 0 := by
      intro hzero
      simp [hzero] at hdet
    exact isUnit_iff_ne_zero.mpr hPne
  have hPinv : P⁻¹ = P.conjTranspose * A := Matrix.inv_eq_left_inv hPA
  have hAinv : A⁻¹ = P * P.conjTranspose := by
    apply Matrix.inv_eq_left_inv
    calc
      (P * P.conjTranspose) * A = P * (P.conjTranspose * A) := by simp [Matrix.mul_assoc]
      _ = P * P⁻¹ := by rw [← hPinv]
      _ = 1 := Matrix.mul_nonsing_inv P hPdet
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (RCLike.ofReal ∘ eigen)
  have hPB' : P.conjTranspose * B = D * P⁻¹ := by
    calc
      P.conjTranspose * B = P.conjTranspose * B * 1 := by simp
      _ = P.conjTranspose * B * (P * P⁻¹) := by
        rw [Matrix.mul_nonsing_inv P hPdet, Matrix.mul_one]
      _ = (P.conjTranspose * B * P) * P⁻¹ := by simp [Matrix.mul_assoc]
      _ = D * P⁻¹ := by rw [hPB]
  have hTraceForward : (A⁻¹ * B).trace = ∑ i, RCLike.ofReal (eigen i) := by
    rw [hAinv]
    calc
      (P * P.conjTranspose * B).trace = (P * (P.conjTranspose * B)).trace := by simp [Matrix.mul_assoc]
      _ = (P * (D * P⁻¹)).trace := by rw [hPB']
      _ = ((D * P⁻¹) * P).trace := Matrix.trace_mul_comm _ _
      _ = D.trace := by simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet]
      _ = ∑ i, RCLike.ofReal (eigen i) := by simp [D, Matrix.trace_diagonal]
  let Dinv : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => RCLike.ofReal ((eigen i)⁻¹))
  have hDD : Dinv * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    change RCLike.ofReal ((eigen i)⁻¹) * RCLike.ofReal (eigen i) = 1
    rw [← RCLike.ofReal_mul]
    exact congrArg RCLike.ofReal (inv_mul_cancel₀ (ne_of_gt (heigen i)))
  have hBinv : B⁻¹ = P * Dinv * P.conjTranspose := by
    apply Matrix.inv_eq_left_inv
    calc
      (P * Dinv * P.conjTranspose) * B = P * Dinv * (P.conjTranspose * B) := by
        simp [Matrix.mul_assoc]
      _ = P * Dinv * (D * P⁻¹) := by rw [hPB']
      _ = P * ((Dinv * D) * P⁻¹) := by simp [Matrix.mul_assoc]
      _ = P * (1 * P⁻¹) := by rw [hDD]
      _ = 1 := by simp [Matrix.mul_nonsing_inv P hPdet]
  have hTraceReverse : (B⁻¹ * A).trace = ∑ i, RCLike.ofReal ((eigen i)⁻¹) := by
    rw [hBinv]
    calc
      (P * Dinv * P.conjTranspose * A).trace = (P * Dinv * (P.conjTranspose * A)).trace := by
        simp [Matrix.mul_assoc]
      _ = (P * Dinv * P⁻¹).trace := by rw [← hPinv]
      _ = (P * (Dinv * P⁻¹)).trace := by simp [Matrix.mul_assoc]
      _ = ((Dinv * P⁻¹) * P).trace := Matrix.trace_mul_comm _ _
      _ = Dinv.trace := by simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet]
      _ = ∑ i, RCLike.ofReal ((eigen i)⁻¹) := by simp [Dinv, Matrix.trace_diagonal]
  constructor
  · rw [hTraceForward, ← RCLike.ofReal_sum, RCLike.ofReal_re]
  · rw [hTraceReverse, ← RCLike.ofReal_sum, RCLike.ofReal_re]

omit [T2Space M] [CompactSpace M] in
theorem exists_trace_controlled_reference_frame
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ) (x : M) (B : ℝ)
    (hforward : relTrace (ω₀ x) (ω₀ x + mddbar n φ x) ≤ B)
    (hreverse : relTrace (ω₀ x + mddbar n φ x) (ω₀ x) ≤ B) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (eigen : Fin n → ℝ),
      IsReferenceOrthonormalFrame ω₀ x P ∧
      Matrix.transpose P *
        (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) * P.map star =
        Matrix.diagonal (RCLike.ofReal ∘ eigen) ∧
      (∀ i, 0 < eigen i) ∧ ∑ i, eigen i ≤ B ∧ ∑ i, (eigen i)⁻¹ ≤ B := by
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := ω₀.metricInChart x z
  let h := g + complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    mem_extChartAt_target x
  have hG : g.PosDef := by
    change (ω₀.metricInChart x z).PosDef
    exact ω₀.posDef_metricInChart x hz
  have hH : h.PosDef := by
    change (ω₀.metricInChart x z + complexHessian
      (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).PosDef
    rw [← ω₀.metricInChart_perturb hφ x hz]
    exact (ω₀.perturb φ hφ).posDef_metricInChart x hz
  obtain ⟨Q, eigen, hQG, hQH, heigen⟩ := referenceContraction_simdiag hG hH
  let P := Q.map star
  have hPtranspose : P.transpose = Q.conjTranspose := by
    ext i j
    simp [P, Matrix.conjTranspose]
  have hPmap : P.map star = Q := by
    ext i j
    simp [P]
  have hFrame : IsReferenceOrthonormalFrame ω₀ x P := by
    change P.transpose * g * P.map star = 1
    rw [hPtranspose, hPmap]
    exact hQG
  have hDiag : P.transpose * h * P.map star = Matrix.diagonal (RCLike.ofReal ∘ eigen) := by
    rw [hPtranspose, hPmap]
    exact hQH
  have hbaseCoeff : (ω₀ x).coeffMatrix = g := by
    change (ω₀ x).coeffMatrix = ω₀.metricInChart x z
    exact (ω₀.metricInChart_self x).symm
  have hpertCoeff : ((ω₀.perturb φ hφ) x).coeffMatrix = h := by
    rw [← (ω₀.perturb φ hφ).metricInChart_self x, ω₀.metricInChart_perturb hφ x hz]
  have hMatrixForward : RCLike.re ((g⁻¹ * h).trace) ≤ B := by
    have hh := hforward
    rw [← ω₀.perturb_apply hφ x, ContinuousAlternatingMap.relTrace,
      hbaseCoeff, hpertCoeff] at hh
    simpa [g, h] using hh
  have hMatrixReverse : RCLike.re ((h⁻¹ * g).trace) ≤ B := by
    have hh := hreverse
    rw [← ω₀.perturb_apply hφ x, ContinuousAlternatingMap.relTrace,
      hpertCoeff, hbaseCoeff] at hh
    simpa [g, h] using hh
  have htr := referenceContraction_simdiag_trace_id g h Q eigen hQG hQH heigen
  refine ⟨P, eigen, hFrame, ?_, heigen, ?_, ?_⟩
  · simpa [h, g, z] using hDiag
  · calc
      ∑ i, eigen i = RCLike.re ((g⁻¹ * h).trace) := htr.1.symm
      _ ≤ B := hMatrixForward
  · calc
      ∑ i, (eigen i)⁻¹ = RCLike.re ((h⁻¹ * g).trace) := htr.2.symm
      _ ≤ B := hMatrixReverse

theorem referenceContraction_eigenvalue_bounds {n : ℕ}
    (d : Fin n → ℝ) (B : ℝ) (hB : 0 < B)
    (hd : ∀ i, 0 < d i)
    (hupper : ∑ i : Fin n, d i ≤ B)
    (hlower : ∑ i : Fin n, (d i)⁻¹ ≤ B) :
    ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B := by
  intro i
  have hsum_upper : d i ≤ ∑ j : Fin n, d j :=
    Finset.single_le_sum (fun j hj => le_of_lt (hd j)) (Finset.mem_univ i)
  have hsum_lower : (d i)⁻¹ ≤ ∑ j : Fin n, (d j)⁻¹ :=
    Finset.single_le_sum (fun j hj => inv_nonneg.mpr (le_of_lt (hd j)))
      (Finset.mem_univ i)
  constructor
  · have hrecip : (d i)⁻¹ ≤ B := hsum_lower.trans hlower
    have hmul : 1 ≤ d i * B := by
      calc
        1 = (d i)⁻¹ * d i := by field_simp [(hd i).ne']
        _ ≤ B * d i := mul_le_mul_of_nonneg_right hrecip (le_of_lt (hd i))
        _ = d i * B := mul_comm _ _
    simpa [one_div] using (div_le_iff₀ hB).2 hmul
  · exact hsum_upper.trans hupper

end KahlerForm
