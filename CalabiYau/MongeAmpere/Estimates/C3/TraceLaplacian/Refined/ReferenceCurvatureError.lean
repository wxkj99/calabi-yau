module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.TraceMatrixJets
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound

/-!
# Reference-curvature contraction in a normalized frame

The trace-Hessian formula contracts the curvature of the fixed reference metric
against two inverse perturbed metrics. Coordinate components alone are not
uniform under changes of chart. A reference-metric orthonormal frame gives the
invariant components below; a finite-sum inequality bounds the contracted error
once a uniform component bound and inverse-metric bounds are supplied. The
uniform frame bound below uses compactness and the independent Kähler
chart-curvature transformation law; the existing K `ReferenceBound` supplies the compactness input.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.2,
Lemma 3.8 and §3.3, Lemma 3.10, pp. 41–46. The sign convention is
`R = -∂∂̄g` at a reference-normal center.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

/-- The mixed Kähler curvature component, with the sign convention
`R_{p q j k} = -g_{a k} ∂̄q Γᵃ_{p j}`. At a normal center where
`∂g = 0`, this is `-∂ₚ∂̄q g_{j k}`. -/
noncomputable def c3RefinedTraceReferenceCurvatureInChart
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p q j k : Fin n) : ℂ :=
  -∑ a : Fin n, g z a k * c3RefinedTracePartialBar
    (fun w ↦ c3ChristoffelInChart g w a p j) z q

/-- Column-oriented matrix of a reference-metric orthonormal frame at the chart center. -/
def c3RefinedTraceReferenceOrthonormalFrameMatrix (ω₀ : KahlerForm n M) (x : M)
    (P : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Matrix.transpose P *
    ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star = 1

/-- Curvature tensor component in a reference-orthonormal frame. The frame is
column-oriented; antiholomorphic slots use conjugated frame coefficients. -/
noncomputable def c3RefinedTraceReferenceCurvatureInFrame (ω₀ : KahlerForm n M) (x : M)
    (P : Matrix (Fin n) (Fin n) ℂ) (p q j k : Fin n) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d,
    P a p * star (P b q) * P c j * star (P d k) *
      c3RefinedTraceReferenceCurvatureInChart (fun z ↦ ω₀.metricInChart x z)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d

/-- Signed reference-curvature error in the refined trace Hessian. The first
contraction is `h⁻¹ · (g⁻¹ h g⁻¹) · R`, the second is the double reference trace
`g⁻¹ · g⁻¹ · R`. In a reference-normal frame with `h = diag λ`, this is precisely
`∑ₚⱼ (λⱼ / λₚ - 1) R_{p p̄ j j̄}`. The inverse indices are reversed in
`(h⁻¹) q p` and `(g⁻¹ h g⁻¹) k j`; no raw coordinate-component bound is claimed. -/
noncomputable def c3RefinedTraceReferenceCurvatureSignedError (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M) : ℝ := by
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := ω₀.metricInChart x z
  let h := g + complexHessian (φ ∘ (extChartAt
    𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z
  exact RCLike.re <| ∑ p : Fin n, ∑ q : Fin n,
    ∑ j : Fin n, ∑ k : Fin n,
      ((h⁻¹ q p * (g⁻¹ * h * g⁻¹) k j - g⁻¹ q p * g⁻¹ k j) *
        c3RefinedTraceReferenceCurvatureInChart (fun w ↦ ω₀.metricInChart x w) z p q j k)

private theorem c3RefinedTrace_eigenvalue_ratio_bound
    {n : ℕ} (B : ℝ) (hB : 0 < B) (eigen : Fin n → ℝ)
    (heigen : ∀ i, 0 < eigen i)
    (hsum : ∑ i, eigen i ≤ B)
    (hinvsum : ∑ i, (eigen i)⁻¹ ≤ B) (p j : Fin n) :
    |eigen j / eigen p - 1| ≤ B ^ 2 + 1 := by
  have hj : eigen j ≤ B := by
    have hsingle : eigen j ≤ ∑ i, eigen i :=
      Finset.single_le_sum (fun i hi => le_of_lt (heigen i)) (Finset.mem_univ j)
    exact hsingle.trans hsum
  have hpInv : (eigen p)⁻¹ ≤ B := by
    have hsingle : (eigen p)⁻¹ ≤ ∑ i, (eigen i)⁻¹ :=
      Finset.single_le_sum (fun i hi => le_of_lt (inv_pos.mpr (heigen i)))
        (Finset.mem_univ p)
    exact hsingle.trans hinvsum
  have hratio_nonneg : 0 ≤ eigen j / eigen p :=
    div_nonneg (le_of_lt (heigen j)) (le_of_lt (heigen p))
  have hratio : eigen j / eigen p ≤ B ^ 2 := by
    rw [div_eq_mul_inv]
    calc
      eigen j * (eigen p)⁻¹ ≤ B * B := mul_le_mul hj hpInv (le_of_lt (inv_pos.mpr (heigen p)))
        (le_of_lt hB)
      _ = B ^ 2 := by ring
  rw [abs_le]
  constructor <;> nlinarith

private theorem c3RefinedTrace_weightedCurvature_term_bound
    {n : ℕ} (B C : ℝ) (hB : 0 < B) (_hC : 0 ≤ C)
    (eigen : Fin n → ℝ) (heigen : ∀ i, 0 < eigen i)
    (hsum : ∑ i, eigen i ≤ B) (hinvsum : ∑ i, (eigen i)⁻¹ ≤ B)
    (curv : Fin n → Fin n → ℂ)
    (hcurv : ∀ p j, ‖curv p j‖ ≤ C) (p j : Fin n) :
    ‖((eigen j / eigen p - 1 : ℝ) : ℂ) * curv p j‖ ≤ (B ^ 2 + 1) * C := by
  rw [norm_mul, Complex.norm_real]
  have hweight := c3RefinedTrace_eigenvalue_ratio_bound B hB eigen heigen hsum hinvsum p j
  exact mul_le_mul hweight (hcurv p j) (norm_nonneg _) (by positivity)

private theorem c3RefinedTrace_normalized_curvature_sum_bound
    {n : ℕ} (B C : ℝ) (hB : 0 < B) (_hC : 0 ≤ C)
    (eigen : Fin n → ℝ) (heigen : ∀ i, 0 < eigen i)
    (hsum : ∑ i, eigen i ≤ B) (hinvsum : ∑ i, (eigen i)⁻¹ ≤ B)
    (curv : Fin n → Fin n → ℂ)
    (hcurv : ∀ p j, ‖curv p j‖ ≤ C) :
    |RCLike.re (∑ p, ∑ j,
      ((eigen j / eigen p - 1 : ℝ) : ℂ) * curv p j)| ≤
        (n : ℝ) ^ 2 * (B ^ 2 + 1) * C := by
  let term : Fin n → Fin n → ℂ := fun p j =>
    ((eigen j / eigen p - 1 : ℝ) : ℂ) * curv p j
  have hterm (p j : Fin n) : ‖term p j‖ ≤ (B ^ 2 + 1) * C := by
    exact c3RefinedTrace_weightedCurvature_term_bound B C hB _hC eigen heigen
      hsum hinvsum curv hcurv p j
  have hnorm : ‖∑ p, ∑ j, term p j‖ ≤ ∑ p, ∑ j, ‖term p j‖ := by
    calc
      ‖∑ p, ∑ j, term p j‖ ≤ ∑ p, ‖∑ j, term p j‖ :=
        norm_sum_le Finset.univ (fun p : Fin n => ∑ j, term p j)
      _ ≤ ∑ p, ∑ j, ‖term p j‖ := by
        apply Finset.sum_le_sum
        intro p hp
        exact norm_sum_le Finset.univ (fun j : Fin n => term p j)
  have hsum_le : ∑ p : Fin n, ∑ j : Fin n, ‖term p j‖ ≤
      ∑ p : Fin n, ∑ j : Fin n, ((B ^ 2 + 1) * C) := by
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_le_sum
    intro j hj
    exact hterm p j
  have hre : |RCLike.re (∑ p, ∑ j, term p j)| ≤ ‖∑ p, ∑ j, term p j‖ :=
    Complex.abs_re_le_norm _
  rw [show (∑ p, ∑ j,
      ((eigen j / eigen p - 1 : ℝ) : ℂ) * curv p j) = ∑ p, ∑ j, term p j by
        rfl]
  calc
    |RCLike.re (∑ p, ∑ j, term p j)| ≤ ‖∑ p, ∑ j, term p j‖ := hre
    _ ≤ ∑ p, ∑ j, ‖term p j‖ := hnorm
    _ ≤ ∑ p, ∑ j, ((B ^ 2 + 1) * C) := hsum_le
    _ = (n : ℝ) ^ 2 * (B ^ 2 + 1) * C := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

open scoped ComplexOrder MatrixOrder in
private theorem c3RefinedTrace_exists_positive_simultaneous_diagonalization
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
  have hSps : S.PosSemidef := by
    simpa using (Matrix.le_iff.mp hSle)
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

private theorem c3RefinedTrace_diagonalized_matrix_trace_identities
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
  have h1 : P * (P.conjTranspose * A) = 1 := mul_eq_one_comm.1 hPA
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
      (P * Dinv * P.conjTranspose * A).trace = (P * Dinv * (P.conjTranspose * A)).trace := by simp [Matrix.mul_assoc]
      _ = (P * Dinv * P⁻¹).trace := by rw [← hPinv]
      _ = (P * (Dinv * P⁻¹)).trace := by simp [Matrix.mul_assoc]
      _ = ((Dinv * P⁻¹) * P).trace := Matrix.trace_mul_comm _ _
      _ = Dinv.trace := by simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPdet]
      _ = ∑ i, RCLike.ofReal ((eigen i)⁻¹) := by simp [Dinv, Matrix.trace_diagonal]
  constructor
  · rw [hTraceForward, ← RCLike.ofReal_sum, RCLike.ofReal_re]
  · rw [hTraceReverse, ← RCLike.ofReal_sum, RCLike.ofReal_re]

omit [T2Space M] [CompactSpace M] in
private theorem c3RefinedTrace_relTrace_eq_chart_matrix_trace
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ) (x : M) :
    relTrace (ω₀ x) (ω₀ x + mddbar n φ x) =
      RCLike.re ((((ω₀.metricInChart x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))⁻¹) *
        (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))).trace) := by
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    change extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x ∈ _
    exact mem_extChartAt_target x
  have hcoeffω : (ω₀.toFormField.chartRep x z).coeffMatrix = ω₀.metricInChart x z := rfl
  have hcoeffα : ((ω₀.toFormField + mddbar n φ).chartRep x z).coeffMatrix =
      ω₀.metricInChart x z + complexHessian (φ ∘ (extChartAt
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
    change ((ω₀.toFormField.chartRep x z + (mddbar n φ).chartRep x z).coeffMatrix) = _
    rw [ContinuousAlternatingMap.coeffMatrix_add, hcoeffω, chartRep_mddbar hφ.1 x hz]
    rfl
  have hcoeffω' : (ω₀ x).coeffMatrix = ω₀.metricInChart x z := by
    simpa [z] using (ω₀.metricInChart_self x).symm
  have hcoeffα' : ((ω₀ x + mddbar n φ x).coeffMatrix) =
      ω₀.metricInChart x z + complexHessian (φ ∘ (extChartAt
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
    change ((ω₀.toFormField + mddbar n φ) x).coeffMatrix = _
    rw [← FormField.chartRep_self (ω₀.toFormField + mddbar n φ) x]
    exact hcoeffα
  rw [ContinuousAlternatingMap.relTrace]
  change RCLike.re (((ω₀ x).coeffMatrix)⁻¹ *
    (ω₀ x + mddbar n φ x).coeffMatrix).trace = _
  rw [hcoeffω', hcoeffα']

private theorem c3RefinedTrace_curvatureInChart_eq_chartCurvature_at
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z)
    (hdet : IsUnit (g z).det)
    (p q j k : Fin n) :
    c3RefinedTraceReferenceCurvatureInChart g z p q j k = chartCurvature g z p q j k := by
  have hInv : (g z)⁻¹ * g z = 1 := Matrix.nonsing_inv_mul (g z) hdet
  have hInvEntry (l k : Fin n) :
      ∑ a, (g z)⁻¹ l a * g z a k = if l = k then 1 else 0 := by
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A l k) hInv
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have hcontract (l : Fin n) :
      ∑ a, g z a k * (g z)⁻¹ l a = if l = k then 1 else 0 := by
    calc
      ∑ a, g z a k * (g z)⁻¹ l a = ∑ a, (g z)⁻¹ l a * g z a k := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = ((g z)⁻¹ * g z) l k := by simp [Matrix.mul_apply]
      _ = if l = k then 1 else 0 := hInvEntry l k
  have hbarGamma (a : Fin n) :
      c3RefinedTracePartialBar (fun w => c3ChristoffelInChart g w a p j) z q =
        -(∑ l, (g z)⁻¹ l a * chartCurvature g z p q j l) := by
    have hcurv := chartChristoffel_bar_eq_curvature_at g z hg hdet a p j q
    simpa [c3RefinedTracePartialBar, c3ChristoffelInChart, c3PartialZ,
      chartPartialBarComplex, chartPartialZComplex] using hcurv
  unfold c3RefinedTraceReferenceCurvatureInChart
  rw [Finset.sum_congr rfl (fun a ha => by rw [hbarGamma a])]
  calc
    -∑ a : Fin n, g z a k * (-(∑ l : Fin n, (g z)⁻¹ l a * chartCurvature g z p q j l)) =
        ∑ l : Fin n, (∑ a : Fin n, g z a k * (g z)⁻¹ l a) * chartCurvature g z p q j l := by
          calc
            -∑ a : Fin n, g z a k * (-(∑ l : Fin n, (g z)⁻¹ l a * chartCurvature g z p q j l)) =
                -(-∑ a : Fin n, g z a k * (∑ l : Fin n, (g z)⁻¹ l a * chartCurvature g z p q j l)) := by
                  congr 1
                  calc
                    ∑ a : Fin n, g z a k * (-(∑ l : Fin n, (g z)⁻¹ l a * chartCurvature g z p q j l)) =
                        ∑ a : Fin n, -(g z a k * (∑ l : Fin n, (g z)⁻¹ l a * chartCurvature g z p q j l)) := by
                          apply Finset.sum_congr rfl
                          intro a ha
                          ring
                    _ = -∑ a : Fin n, g z a k * (∑ l : Fin n, (g z)⁻¹ l a * chartCurvature g z p q j l) := by
                          rw [Finset.sum_neg_distrib]
            _ = ∑ a : Fin n, g z a k * (∑ l : Fin n, (g z)⁻¹ l a * chartCurvature g z p q j l) := by simp
            _ = ∑ a : Fin n, ∑ l : Fin n,
                  (g z a k * (g z)⁻¹ l a) * chartCurvature g z p q j l := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro l hl
                  ring
            _ = ∑ l : Fin n, ∑ a : Fin n,
                  (g z a k * (g z)⁻¹ l a) * chartCurvature g z p q j l := by
                  rw [Finset.sum_comm]
            _ = ∑ l : Fin n, (∑ a : Fin n, g z a k * (g z)⁻¹ l a) *
                  chartCurvature g z p q j l := by
                  apply Finset.sum_congr rfl
                  intro l hl
                  rw [← Finset.sum_mul]
    _ = ∑ l, (if l = k then 1 else 0) * chartCurvature g z p q j l := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hcontract l]
    _ = chartCurvature g z p q j k := by simp

omit [T2Space M] [CompactSpace M] in
open scoped ComplexOrder MatrixOrder in
private theorem c3RefinedTrace_referenceFrame_curvature_eq
    (ω₀ : KahlerForm n M) (x : M) (P : Matrix (Fin n) (Fin n) ℂ)
    (p q j k : Fin n) :
    c3RefinedTraceReferenceCurvatureInFrame ω₀ x P p q j k =
      referenceCurvatureComponent ω₀ x P p q j k := by
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    change extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x ∈ _
    exact mem_extChartAt_target x
  have hg : ∀ a b, ContDiffAt ℝ ∞ (fun w => g w a b) z := by
    intro a b
    exact (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)
  have hdet : IsUnit (g z).det :=
    (Matrix.isUnit_iff_isUnit_det (g z)).mp (ω₀.posDef_metricInChart x hz).isUnit
  have hcurv (a b c d : Fin n) :
      c3RefinedTraceReferenceCurvatureInChart g z a b c d = chartCurvature g z a b c d :=
    c3RefinedTrace_curvatureInChart_eq_chartCurvature_at g z hg hdet a b c d
  change (∑ a, ∑ b, ∑ c, ∑ d,
      P a p * star (P b q) * P c j * star (P d k) *
        c3RefinedTraceReferenceCurvatureInChart g z a b c d) =
    ∑ a, ∑ b, ∑ c, ∑ d,
      P a p * star (P b q) * P c j * star (P d k) *
        chartCurvature (fun w ↦ ω₀.metricInChart x w)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  rw [hcurv a b c d]

omit [T2Space M] [CompactSpace M] in
open scoped ComplexOrder MatrixOrder in
private theorem c3RefinedTrace_exists_traceControlledReferenceFrame
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ) (x : M) (B : ℝ)
    (hforward : relTrace (ω₀ x) (ω₀ x + mddbar n φ x) ≤ B)
    (hreverse : relTrace (ω₀ x + mddbar n φ x) (ω₀ x) ≤ B) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (eigen : Fin n → ℝ),
      c3RefinedTraceReferenceOrthonormalFrameMatrix ω₀ x P ∧
      Matrix.transpose P *
        (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) * P.map star =
          Matrix.diagonal (RCLike.ofReal ∘ eigen) ∧
      (∀ i, 0 < eigen i) ∧ ∑ i, eigen i ≤ B ∧ ∑ i, (eigen i)⁻¹ ≤ B := by
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := ω₀.metricInChart x z
  let h := g + complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    change extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x ∈ _
    exact mem_extChartAt_target x
  have hG : g.PosDef := by
    change (ω₀.metricInChart x z).PosDef
    exact ω₀.posDef_metricInChart x hz
  have hH : h.PosDef := by
    change (ω₀.metricInChart x z + complexHessian
      (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z).PosDef
    rw [← ω₀.metricInChart_perturb hφ x hz]
    exact (ω₀.perturb φ hφ).posDef_metricInChart x hz
  obtain ⟨Q, eigen, hQG, hQH, heigen⟩ :=
    c3RefinedTrace_exists_positive_simultaneous_diagonalization hG hH
  let P := Q.map star
  have hPtranspose : P.transpose = Q.conjTranspose := by
    ext i j
    simp [P, Matrix.conjTranspose]
  have hPmap : P.map star = Q := by
    ext i j
    simp [P]
  have hNorm : c3RefinedTraceReferenceOrthonormalFrameMatrix ω₀ x P := by
    change P.transpose * g * P.map star = 1
    rw [hPtranspose, hPmap]
    exact hQG
  have hDiag : P.transpose * h * P.map star = Matrix.diagonal (RCLike.ofReal ∘ eigen) := by
    rw [hPtranspose, hPmap]
    exact hQH
  have hbaseCoeff : (ω₀ x).coeffMatrix = g := by
    change (ω₀ x).coeffMatrix = ω₀.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)
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
  have htr := c3RefinedTrace_diagonalized_matrix_trace_identities g h Q eigen hQG hQH heigen
  refine ⟨P, eigen, hNorm, ?_, heigen, ?_, ?_⟩
  · simpa [h, g, z] using hDiag
  · calc
      ∑ i, eigen i = RCLike.re ((g⁻¹ * h).trace) := htr.1.symm
      _ ≤ B := hMatrixForward
  · calc
      ∑ i, (eigen i)⁻¹ = RCLike.re ((h⁻¹ * g).trace) := htr.2.symm
      _ ≤ B := hMatrixReverse

private lemma transfer_pullback_metric_inverse {n : ℕ}
    (A B G : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    (A.transpose * G * A.map star)⁻¹ = B.map star * G⁻¹ * B.transpose := by
  have hinvA : A⁻¹ = B := by
    calc
      A⁻¹ = 1 * A⁻¹ := by simp
      _ = (B * A) * A⁻¹ := by rw [hBA]
      _ = B * (A * A⁻¹) := by rw [Matrix.mul_assoc]
      _ = B := by
        rw [Matrix.mul_nonsing_inv A (Matrix.isUnit_det_of_left_inverse hBA), mul_one]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  rw [← Matrix.transpose_nonsing_inv, hinvA]
  have hABstar : A.map star * B.map star = 1 := by
    ext a b
    have hij := congrArg star (congrFun (congrFun hAB a) b)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using hij
  have hBAstar : B.map star * A.map star = 1 := by
    ext a b
    have hij := congrArg star (congrFun (congrFun hBA a) b)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using hij
  have hs : IsUnit (A.map star).det := Matrix.isUnit_det_of_right_inverse hABstar
  have hinvstar : (A.map star)⁻¹ = B.map star := by
    calc
      (A.map star)⁻¹ = 1 * (A.map star)⁻¹ := by simp
      _ = (B.map star * A.map star) * (A.map star)⁻¹ := by rw [hBAstar]
      _ = B.map star * (A.map star * (A.map star)⁻¹) := by rw [Matrix.mul_assoc]
      _ = B.map star := by rw [Matrix.mul_nonsing_inv _ hs, mul_one]
  rw [hinvstar]
  rw [← Matrix.mul_assoc]

private lemma transfer_pullback_double_inverse {n : ℕ}
    (A B G H : Matrix (Fin n) (Fin n) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    (A.transpose * G * A.map star)⁻¹ * (A.transpose * H * A.map star) *
        (A.transpose * G * A.map star)⁻¹ =
      B.map star * (G⁻¹ * H * G⁻¹) * B.transpose := by
  rw [transfer_pullback_metric_inverse A B G hAB hBA]
  have htranspose : B.transpose * A.transpose = 1 := by
    rw [← Matrix.transpose_mul, hAB]
    simp
  have hstar : A.map star * B.map star = 1 := by
    ext a b
    have hij := congrArg star (congrFun (congrFun hAB a) b)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using hij
  calc
    _ = B.map star * (G⁻¹ * (B.transpose * A.transpose) * H *
          (A.map star * B.map star) * G⁻¹) * B.transpose := by
        simp only [Matrix.mul_assoc]
    _ = B.map star * (G⁻¹ * H * G⁻¹) * B.transpose := by
        rw [htranspose, hstar]
        simp only [Matrix.mul_one, Matrix.mul_assoc]

private lemma transfer_pullback_contract_pair {n : ℕ}
    (A B X : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1)
    (T : Matrix (Fin n) (Fin n) ℂ) :
    ∑ q : Fin n, ∑ p : Fin n,
      (B.map star * X * B.transpose) q p *
        (∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * T a b) =
      ∑ a : Fin n, ∑ b : Fin n, X b a * T a b := by
  classical
  have hABstar : A.map star * B.map star = 1 := by
    ext a b
    have h := congrArg star (congrFun (congrFun hAB a) b)
    simpa [Matrix.mul_apply, Matrix.one_apply, star_sum, star_mul, mul_comm] using h
  have htranspose : B.transpose * A.transpose = 1 := by
    rw [← Matrix.transpose_mul, hAB]
    simp
  have hTP (p q : Fin n) :
      (A.transpose * T * A.map star) p q =
        ∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * T a b := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    calc
      ∑ b : Fin n, (∑ a : Fin n, A a p * T a b) * star (A b q) =
          ∑ b : Fin n, ∑ a : Fin n, A a p * T a b * star (A b q) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_mul Finset.univ
          (fun a : Fin n ↦ A a p * T a b) (star (A b q))
      _ = ∑ a : Fin n, ∑ b : Fin n, A a p * T a b * star (A b q) :=
        Finset.sum_comm
      _ = ∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * T a b := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        ring
  have htrace :
      ((B.map star * X * B.transpose) * (A.transpose * T * A.map star)).trace =
        ∑ q : Fin n, ∑ p : Fin n,
          (B.map star * X * B.transpose) q p * (A.transpose * T * A.map star) p q := by
    simp [Matrix.trace, Matrix.mul_apply]
  calc
    ∑ q : Fin n, ∑ p : Fin n,
        (B.map star * X * B.transpose) q p *
          (∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * T a b) =
        ((B.map star * X * B.transpose) * (A.transpose * T * A.map star)).trace := by
      rw [htrace]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      rw [← hTP p q]
    _ = ((B.map star * X) * (B.transpose * A.transpose) * T * A.map star).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = ((B.map star * X) * T * A.map star).trace := by
      rw [htranspose]
      simp
    _ = (B.map star * ((X * T) * A.map star)).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = (((X * T) * A.map star) * B.map star).trace := Matrix.trace_mul_comm _ _
    _ = ((X * T) * (A.map star * B.map star)).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = (X * T).trace := by rw [hABstar]; simp
    _ = ∑ a : Fin n, ∑ b : Fin n, X b a * T a b := by
      simp only [Matrix.trace]
      rw [Finset.sum_comm]
      rfl

private lemma transfer_sum_four_reorder {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n, F p q j k) =
      ∑ j : Fin n, ∑ k : Fin n, ∑ q : Fin n, ∑ p : Fin n, F p q j k := by
  calc
    (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n, F p q j k) =
        ∑ q : Fin n, ∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n, F p q j k :=
      Finset.sum_comm
    _ = ∑ q : Fin n, ∑ j : Fin n, ∑ p : Fin n, ∑ k : Fin n, F p q j k := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ q : Fin n, ∑ p : Fin n, ∑ k : Fin n, F p q j k :=
      Finset.sum_comm
    _ = ∑ j : Fin n, ∑ q : Fin n, ∑ k : Fin n, ∑ p : Fin n, F p q j k := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ q : Fin n, ∑ p : Fin n, F p q j k := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm

private lemma transfer_curvature_split {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (p q j k : Fin n) :
    ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
      A a p * star (A b q) * A c j * star (A d k) * R a b c d =
    ∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) *
      (∑ c : Fin n, ∑ d : Fin n, A c j * star (A d k) * R a b c d) := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  calc
    ∑ c : Fin n, ∑ d : Fin n,
        A a p * star (A b q) * A c j * star (A d k) * R a b c d =
      ∑ c : Fin n, ∑ d : Fin n,
        (A a p * star (A b q)) * (A c j * star (A d k) * R a b c d) := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ∑ c : Fin n, (A a p * star (A b q)) *
          ∑ d : Fin n, A c j * star (A d k) * R a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [← Finset.mul_sum]
    _ = (A a p * star (A b q)) *
          ∑ c : Fin n, ∑ d : Fin n, A c j * star (A d k) * R a b c d := by
      rw [← Finset.mul_sum]

private lemma transfer_sum_four_block_swap {n : ℕ}
    (F : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, F a b j k) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n, F a b j k := by
  calc
    (∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n, F a b j k) =
        ∑ k : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n, F a b j k :=
      Finset.sum_comm
    _ = ∑ k : Fin n, ∑ a : Fin n, ∑ j : Fin n, ∑ b : Fin n, F a b j k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑ a : Fin n, ∑ k : Fin n, ∑ j : Fin n, ∑ b : Fin n, F a b j k :=
      Finset.sum_comm
    _ = ∑ a : Fin n, ∑ k : Fin n, ∑ b : Fin n, ∑ j : Fin n, F a b j k := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_comm
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ k : Fin n, ∑ j : Fin n, F a b j k := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n, F a b j k := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm

private lemma transfer_contract_four {n : ℕ}
    (A B X Y : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (B.map star * X * B.transpose) q p * (B.map star * Y * B.transpose) k j *
        (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          A a p * star (A b q) * A c j * star (A d k) * R a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        X b a * Y d c * R a b c d := by
  classical
  let XF := B.map star * X * B.transpose
  let YF := B.map star * Y * B.transpose
  let Tjk : Fin n → Fin n → Fin n → Fin n → ℂ := fun j k a b =>
    ∑ c : Fin n, ∑ d : Fin n, A c j * star (A d k) * R a b c d
  have hsplit (p q j k : Fin n) :
      (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        A a p * star (A b q) * A c j * star (A d k) * R a b c d) =
      ∑ a : Fin n, ∑ b : Fin n, A a p * star (A b q) * Tjk j k a b := by
    simpa [Tjk] using transfer_curvature_split A R p q j k
  have hpair1 (j k : Fin n) :
      ∑ q : Fin n, ∑ p : Fin n,
        XF q p * (∑ a : Fin n, ∑ b : Fin n,
          A a p * star (A b q) * Tjk j k a b) =
      ∑ a : Fin n, ∑ b : Fin n, X b a * Tjk j k a b := by
    let W : Matrix (Fin n) (Fin n) ℂ := fun a b => Tjk j k a b
    simpa [XF, W] using transfer_pullback_contract_pair A B X hAB W
  have hpair2 (a b : Fin n) :
      ∑ j : Fin n, ∑ k : Fin n, YF k j * Tjk j k a b =
      ∑ c : Fin n, ∑ d : Fin n, Y d c * R a b c d := by
    let W : Matrix (Fin n) (Fin n) ℂ := fun c d => R a b c d
    rw [Finset.sum_comm]
    simpa [YF, Tjk, W] using transfer_pullback_contract_pair A B Y hAB W
  calc
    _ = ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        XF q p * YF k j * (∑ a : Fin n, ∑ b : Fin n,
          A a p * star (A b q) * Tjk j k a b) := by
      simp_rw [XF, YF, hsplit]
    _ = ∑ j : Fin n, ∑ k : Fin n, YF k j *
        (∑ q : Fin n, ∑ p : Fin n,
          XF q p * (∑ a : Fin n, ∑ b : Fin n,
            A a p * star (A b q) * Tjk j k a b)) := by
      rw [transfer_sum_four_reorder]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      calc
        ∑ q : Fin n, ∑ p : Fin n,
            XF q p * YF k j * (∑ a : Fin n, ∑ b : Fin n,
              A a p * star (A b q) * Tjk j k a b) =
          ∑ q : Fin n, ∑ p : Fin n,
            YF k j * (XF q p * (∑ a : Fin n, ∑ b : Fin n,
              A a p * star (A b q) * Tjk j k a b)) := by
          apply Finset.sum_congr rfl
          intro q hq
          apply Finset.sum_congr rfl
          intro p hp
          ring
        _ = ∑ q : Fin n, YF k j *
              (∑ p : Fin n, XF q p * (∑ a : Fin n, ∑ b : Fin n,
                A a p * star (A b q) * Tjk j k a b)) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [← Finset.mul_sum]
        _ = YF k j *
              (∑ q : Fin n, ∑ p : Fin n,
                XF q p * (∑ a : Fin n, ∑ b : Fin n,
                  A a p * star (A b q) * Tjk j k a b)) := by
          rw [← Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ k : Fin n, YF k j *
          (∑ a : Fin n, ∑ b : Fin n, X b a * Tjk j k a b) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [hpair1 j k]
    _ = ∑ j : Fin n, ∑ k : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          X b a * YF k j * Tjk j k a b := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      calc
        YF k j * (∑ a : Fin n, ∑ b : Fin n, X b a * Tjk j k a b) =
            ∑ a : Fin n, ∑ b : Fin n, YF k j * (X b a * Tjk j k a b) := by
          calc
            _ = ∑ a : Fin n, YF k j * (∑ b : Fin n, X b a * Tjk j k a b) :=
              Finset.mul_sum Finset.univ _ _
            _ = ∑ a : Fin n, ∑ b : Fin n,
                  YF k j * (X b a * Tjk j k a b) := by
              apply Finset.sum_congr rfl
              intro a ha
              exact Finset.mul_sum Finset.univ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          X b a * YF k j * Tjk j k a b := by
      exact transfer_sum_four_block_swap
        (fun a b j k => X b a * YF k j * Tjk j k a b)
    _ = ∑ a : Fin n, ∑ b : Fin n, X b a *
          (∑ j : Fin n, ∑ k : Fin n, YF k j * Tjk j k a b) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      calc
        ∑ j : Fin n, ∑ k : Fin n, X b a * YF k j * Tjk j k a b =
            ∑ j : Fin n, ∑ k : Fin n, X b a * (YF k j * Tjk j k a b) := by
          apply Finset.sum_congr rfl
          intro j hj
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = ∑ j : Fin n, X b a * (∑ k : Fin n, YF k j * Tjk j k a b) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact (Finset.mul_sum Finset.univ _ _).symm
        _ = X b a * (∑ j : Fin n, ∑ k : Fin n, YF k j * Tjk j k a b) :=
          (Finset.mul_sum Finset.univ _ _).symm
    _ = ∑ a : Fin n, ∑ b : Fin n, X b a *
          (∑ c : Fin n, ∑ d : Fin n, Y d c * R a b c d) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [hpair2 a b]
    _ = ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          X b a * Y d c * R a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      ring

private theorem c3RefinedTraceTransfer_diagonalContraction
    {n : ℕ} (g h : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (eigen : Fin n → ℝ) (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hframe : P.transpose * g * P.map star = 1)
    (hdiag : P.transpose * h * P.map star = Matrix.diagonal (RCLike.ofReal ∘ eigen))
    (heigen : ∀ i, 0 < eigen i) :
    RCLike.re (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      ((h⁻¹ q p * (g⁻¹ * h * g⁻¹) k j - g⁻¹ q p * g⁻¹ k j) * R p q j k)) =
      ∑ p : Fin n, ∑ j : Fin n,
        (eigen j / eigen p - 1) * RCLike.re
          (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
            P a p * star (P b p) * P c j * star (P d j) * R a b c d) := by
  let Q := P.map star
  have hQt : Q.conjTranspose = P.transpose := by
    ext i j
    simp [Q, Matrix.conjTranspose]
  have hQnorm : Q.conjTranspose * g * Q = 1 := by rw [hQt]; exact hframe
  have hQdet : IsUnit Q.det := by
    have hdet : star Q.det * g.det * Q.det = 1 := by
      have hh := congrArg Matrix.det hQnorm
      simpa only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] using hh
    have hne : Q.det ≠ 0 := by
      intro hzero
      simp [hzero] at hdet
    exact isUnit_iff_ne_zero.mpr hne
  have hQdetP : Q.det = star P.det := by
    dsimp [Q]
    simpa using ((starRingEnd ℂ).map_det P).symm
  have hPdetNe : P.det ≠ 0 := by
    intro hzero
    have hQne : Q.det ≠ 0 := isUnit_iff_ne_zero.mp hQdet
    apply hQne
    rw [hQdetP, hzero]
    simp
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr hPdetNe
  let Pinv := P⁻¹
  have hPinvP : P * Pinv = 1 := by exact Matrix.mul_nonsing_inv P hPdet
  have hPInvP : Pinv * P = 1 := by exact Matrix.nonsing_inv_mul P hPdet
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (RCLike.ofReal ∘ eigen)
  let Dinv : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal
    (fun i => RCLike.ofReal ((eigen i)⁻¹))
  have hDinvD : Dinv * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    change RCLike.ofReal ((eigen i)⁻¹) * RCLike.ofReal (eigen i) = 1
    rw [← RCLike.ofReal_mul]
    exact congrArg RCLike.ofReal (inv_mul_cancel₀ (ne_of_gt (heigen i)))
  have hDinvEq : D⁻¹ = Dinv := Matrix.inv_eq_left_inv hDinvD
  have hFrameInvH : Dinv = Pinv.map star * h⁻¹ * Pinv.transpose := by
    have hh := transfer_pullback_metric_inverse P Pinv h hPinvP hPInvP
    rw [hdiag, hDinvEq] at hh
    exact hh
  have hFrameInvG : (1 : Matrix (Fin n) (Fin n) ℂ) =
      Pinv.map star * g⁻¹ * Pinv.transpose := by
    have hh := transfer_pullback_metric_inverse P Pinv g hPinvP hPInvP
    rw [hframe] at hh
    simpa using hh
  have hFrameCross : D = Pinv.map star * (g⁻¹ * h * g⁻¹) * Pinv.transpose := by
    have hh := transfer_pullback_double_inverse P Pinv g h hPinvP hPInvP
    rw [hframe, hdiag] at hh
    simpa [D] using hh
  let F : Fin n → Fin n → Fin n → Fin n → ℂ := fun p q j k =>
    ∑ a, ∑ b, ∑ c, ∑ d,
      P a p * star (P b q) * P c j * star (P d k) * R a b c d
  have hfirst := transfer_contract_four P Pinv h⁻¹ (g⁻¹ * h * g⁻¹) hPinvP R
  have hsecond := transfer_contract_four P Pinv g⁻¹ g⁻¹ hPinvP R
  have hFirstFrame :
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        Dinv q p * D k j * F p q j k =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        h⁻¹ b a * (g⁻¹ * h * g⁻¹) d c * R a b c d := by
    rw [← hFrameInvH, ← hFrameCross] at hfirst
    simpa [F, D] using hfirst
  have hSecondFrame :
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (1 : Matrix (Fin n) (Fin n) ℂ) q p * (1 : Matrix (Fin n) (Fin n) ℂ) k j * F p q j k =
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
        g⁻¹ b a * g⁻¹ d c * R a b c d := by
    simp_rw [← hFrameInvG] at hsecond
    simpa [F] using hsecond
  have hOriginalComplex :
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ((h⁻¹ q p * (g⁻¹ * h * g⁻¹) k j - g⁻¹ q p * g⁻¹ k j) * R p q j k) =
      (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        Dinv q p * D k j * F p q j k) -
      (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (1 : Matrix (Fin n) (Fin n) ℂ) q p * (1 : Matrix (Fin n) (Fin n) ℂ) k j * F p q j k) := by
    calc
      _ = ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (h⁻¹ q p * (g⁻¹ * h * g⁻¹) k j * R p q j k -
            g⁻¹ q p * g⁻¹ k j * R p q j k) := by
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro q hq
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          h⁻¹ q p * (g⁻¹ * h * g⁻¹) k j * R p q j k) -
          (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          g⁻¹ q p * g⁻¹ k j * R p q j k) := by
            simp_rw [Finset.sum_sub_distrib]
      _ = (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          Dinv q p * D k j * F p q j k) -
          (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (1 : Matrix (Fin n) (Fin n) ℂ) q p * (1 : Matrix (Fin n) (Fin n) ℂ) k j * F p q j k) := by
            rw [hFirstFrame.symm, hSecondFrame.symm]
  have hFirstDiagonal :
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        Dinv q p * D k j * F p q j k =
      ∑ p : Fin n, ∑ j : Fin n,
        RCLike.ofReal (eigen j / eigen p) * F p p j j := by
    simp [Dinv, D, F, Matrix.diagonal, Finset.sum_ite_eq', RCLike.ofReal_mul,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hSecondDiagonal :
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (1 : Matrix (Fin n) (Fin n) ℂ) q p * (1 : Matrix (Fin n) (Fin n) ℂ) k j * F p q j k =
      ∑ p : Fin n, ∑ j : Fin n, F p p j j := by
    simp [Matrix.one_apply]
  have hOriginalDiagonal :
      ∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ((h⁻¹ q p * (g⁻¹ * h * g⁻¹) k j - g⁻¹ q p * g⁻¹ k j) * R p q j k) =
      ∑ p : Fin n, ∑ j : Fin n,
        (RCLike.ofReal (eigen j / eigen p) - 1) * F p p j j := by
    rw [hOriginalComplex, hFirstDiagonal, hSecondDiagonal]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hRealDiag :
      RCLike.re (∑ p : Fin n, ∑ j : Fin n,
        (RCLike.ofReal (eigen j / eigen p) - 1) * F p p j j) =
      ∑ p : Fin n, ∑ j : Fin n,
        (eigen j / eigen p - 1) * RCLike.re (F p p j j) := by
    change Complex.re (∑ p : Fin n, ∑ j : Fin n,
      (RCLike.ofReal (eigen j / eigen p) - 1) * F p p j j) = _
    simp_rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.mul_re]
  have hRealDiagonal :
      RCLike.re (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ((h⁻¹ q p * (g⁻¹ * h * g⁻¹) k j - g⁻¹ q p * g⁻¹ k j) * R p q j k)) =
      ∑ p : Fin n, ∑ j : Fin n,
        (eigen j / eigen p - 1) * RCLike.re (F p p j j) := by
    calc
      _ = RCLike.re (∑ p : Fin n, ∑ j : Fin n,
          (RCLike.ofReal (eigen j / eigen p) - 1) * F p p j j) :=
        congrArg RCLike.re hOriginalDiagonal
      _ = _ := hRealDiag
  exact hRealDiagonal

omit [T2Space M] [CompactSpace M] in
private theorem c3RefinedTrace_signedError_eq_referenceFrame_sum
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (P : Matrix (Fin n) (Fin n) ℂ) (eigen : Fin n → ℝ)
    (hP : c3RefinedTraceReferenceOrthonormalFrameMatrix ω₀ x P)
    (hDiag : Matrix.transpose P *
        (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) * P.map star =
          Matrix.diagonal (RCLike.ofReal ∘ eigen))
    (heigen : ∀ i, 0 < eigen i) :
    c3RefinedTraceReferenceCurvatureSignedError ω₀ φ x =
      ∑ p : Fin n, ∑ j : Fin n,
        (eigen j / eigen p - 1) *
          RCLike.re (c3RefinedTraceReferenceCurvatureInFrame ω₀ x P p p j j) := by
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := ω₀.metricInChart x z
  let h := g + complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z
  let R : Fin n → Fin n → Fin n → Fin n → ℂ := fun a b c d ↦
    c3RefinedTraceReferenceCurvatureInChart (fun w ↦ ω₀.metricInChart x w) z a b c d
  unfold c3RefinedTraceReferenceCurvatureSignedError
  change RCLike.re (∑ p : Fin n, ∑ q : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      ((h⁻¹ q p * (g⁻¹ * h * g⁻¹) k j - g⁻¹ q p * g⁻¹ k j) * R p q j k)) =
    ∑ p : Fin n, ∑ j : Fin n,
      (eigen j / eigen p - 1) * RCLike.re
        (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n,
          P a p * star (P b p) * P c j * star (P d j) * R a b c d)
  exact c3RefinedTraceTransfer_diagonalContraction g h P eigen R hP hDiag heigen

omit [T2Space M] in
/-- Under two-sided metric comparison, the signed bisectional-curvature error
has a uniform absolute bound. In reference-orthonormal coordinates this follows
from the existing K reference-frame curvature bound, the eigenvalue bounds,
and finite summation of the normalized signed coefficients; the tensor law ensures the
scalar above has the same value in the original point-selected chart. -/
@[deprecated "unused hypothesis `hsol`; will be removed" (since := "2026-10-02")]
theorem c3RefinedTrace_exists_uniform_referenceCurvature_error_bound
    (ω₀ : KahlerForm n M) (B : ℝ) (hB : 0 < B) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ (G φ : M → ℝ) (hsol : ω₀.SolvesMongeAmpere G φ) (x : M),
        relTrace (ω₀ x) (ω₀ x + mddbar n φ x) ≤ B →
        relTrace (ω₀ x + mddbar n φ x) (ω₀ x) ≤ B →
        |c3RefinedTraceReferenceCurvatureSignedError ω₀ φ x| ≤ R := by
  obtain ⟨C, hCnonneg, hCbound⟩ :=
    exists_uniform_reference_curvature_component_bound ω₀
  refine ⟨(n : ℝ) ^ 2 * (B ^ 2 + 1) * C, ?_, ?_⟩
  · positivity
  · intro G φ hsol x hforward hreverse
    obtain ⟨P, eigen, hP, hDiag, heigen, hsum, hinvsum⟩ :=
      c3RefinedTrace_exists_traceControlledReferenceFrame ω₀ φ hsol.1 x B hforward hreverse
    have hframeCurv (p j : Fin n) :
        ‖c3RefinedTraceReferenceCurvatureInFrame ω₀ x P p p j j‖ ≤ C := by
      rw [c3RefinedTrace_referenceFrame_curvature_eq ω₀ x P p p j j]
      exact hCbound x P
        (by simpa [c3RefinedTraceReferenceOrthonormalFrameMatrix,
          referenceOrthonormalFrameMatrix] using hP) p p j j
    have hsumBound := c3RefinedTrace_normalized_curvature_sum_bound B C hB hCnonneg
      eigen heigen hsum hinvsum
      (fun p j ↦ c3RefinedTraceReferenceCurvatureInFrame ω₀ x P p p j j)
      hframeCurv
    have hrealSum :
        RCLike.re (∑ p : Fin n, ∑ j : Fin n,
          ((eigen j / eigen p - 1 : ℝ) : ℂ) *
            c3RefinedTraceReferenceCurvatureInFrame ω₀ x P p p j j) =
          ∑ p : Fin n, ∑ j : Fin n,
            (eigen j / eigen p - 1) *
              RCLike.re (c3RefinedTraceReferenceCurvatureInFrame ω₀ x P p p j j) := by
      change Complex.re (∑ p : Fin n, ∑ j : Fin n,
        ((eigen j / eigen p - 1 : ℝ) : ℂ) *
          c3RefinedTraceReferenceCurvatureInFrame ω₀ x P p p j j) = _
      simp_rw [Complex.re_sum]
      simp
    have hframeIdentity := c3RefinedTrace_signedError_eq_referenceFrame_sum
      ω₀ φ x P eigen hP hDiag heigen
    rw [hframeIdentity, ← hrealSum]
    exact hsumBound

end KahlerForm
