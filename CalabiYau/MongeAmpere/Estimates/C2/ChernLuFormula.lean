module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Kahler.Ricci
public import CalabiYau.Geometry.Complex.Forms.Positive
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.FirstDerivativeSymmetry
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.BisectionalBound
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.RelativeTrace
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.LaplacianExpansion
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.RicciExpansion
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.SecondDerivativeSymmetry
import CalabiYau.Geometry.Kahler.Laplacian.Cofactor
import CalabiYau.LinearAlgebra.Hermitian.NormalJet
import CalabiYau.LinearAlgebra.Hermitian.SimultaneousDiagonalization

/-!
# The Chern–Lu trace formula

This is the local differential-geometric estimate used in the Aubin–Yau `C²` proof. Its proof
uses holomorphic normal coordinates for the reference metric, diagonalizes the perturbed metric
at the point, expands the Laplacian of the trace, and absorbs the first-derivative terms by
Cauchy–Schwarz. Compactness supplies a uniform lower bound for the reference bisectional
curvature.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
private theorem exists_kahler_chart_normal_jet
    (ω₀ : KahlerForm n M) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hG : ω₀.metricInChart x z = 1) :
    ∃ C : Fin n → Fin n → Fin n → ℂ,
      (∀ a i k, C a i k = C a k i) ∧
      (∀ i k j, chartPartialZComplex
        (fun w ↦ ω₀.metricInChart x w k j) z i +
          ∑ a, (ω₀.metricInChart x z) a j * C a i k = 0) := by
  let G := ω₀.metricInChart x z
  let D : Fin n → Fin n → Fin n → ℂ := fun i k j ↦
    chartPartialZComplex (fun w ↦ ω₀.metricInChart x w k j) z i
  have hD : ∀ i k j, D i k j = D k i j := by
    intro i k j
    exact kahler_chart_metric_symmetry (ω₀ := ω₀) x hz i k j
  have hInv : G.transpose * (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [show G = 1 by exact hG]
    simp
  obtain ⟨C, hC, hcancel⟩ := Matrix.exists_symmetric_normal_jet G 1 hInv D hD
  refine ⟨C, hC, ?_⟩
  intro i k j
  simpa [D, G] using hcancel i k j

omit [T2Space M] [CompactSpace M] in
private theorem exists_kahler_simultaneous_normalization
    (ω₀ ω₁ : KahlerForm n M) (x : M) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ) (eigenvalue : Fin n → ℝ),
      Matrix.conjTranspose P * (ω₀ x).coeffMatrix * P = 1 ∧
      Matrix.conjTranspose P * (ω₁ x).coeffMatrix * P =
        Matrix.diagonal (RCLike.ofReal ∘ eigenvalue) ∧
      (∀ j, 0 < eigenvalue j) ∧
      relTrace (ω₀ x) (ω₁ x) = ∑ j, eigenvalue j ∧
      relTrace (ω₁ x) (ω₀ x) = ∑ j, (eigenvalue j)⁻¹ := by
  let A := (ω₀ x).coeffMatrix
  let B := (ω₁ x).coeffMatrix
  have hA : A.PosDef := (ContinuousAlternatingMap.isPositive_iff.mp
    (ω₀.isPositive x)).2
  have hB : B.PosDef := (ContinuousAlternatingMap.isPositive_iff.mp
    (ω₁.isPositive x)).2
  obtain ⟨P, eigenvalue, hPA, hPB⟩ :=
    Matrix.PosDef.exists_simultaneous_diagonalization hA hB.isHermitian
  have heigenvalue : ∀ j, 0 < eigenvalue j :=
    (Matrix.posDef_iff_forall_pos_of_conjTranspose_mul_mul_eq hPA hPB).1 hB
  have hTrace : RCLike.re (A⁻¹ * B).trace = ∑ j, eigenvalue j :=
    Matrix.re_trace_inv_mul_eq_sum_of_conjTranspose_mul_mul_eq hPA hPB
  have hReverseTrace : RCLike.re (B⁻¹ * A).trace = ∑ j, (eigenvalue j)⁻¹ :=
    Matrix.re_trace_inv_mul_eq_sum_inv_of_conjTranspose_mul_mul_eq hPA hPB
      (fun j ↦ (heigenvalue j).ne')
  refine ⟨P, eigenvalue, hPA, hPB, heigenvalue, ?_, ?_⟩
  · change RCLike.re (A⁻¹ * B).trace = _
    exact hTrace
  · change RCLike.re (B⁻¹ * A).trace = _
    exact hReverseTrace

omit [T2Space M] [CompactSpace M] in
private theorem exists_normalized_first_jet_array
    (G H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hG0 : G z = 1)
    (hGsym : ∀ i k j, chartPartialZComplex (fun w ↦ G w k j) z i =
      chartPartialZComplex (fun w ↦ G w i j) z k)
    (hHsym : ∀ i k j, chartPartialZComplex (fun w ↦ H w k j) z i =
      chartPartialZComplex (fun w ↦ H w i j) z k) :
    ∃ (C : Fin n → Fin n → Fin n → ℂ)
      (T : Fin n → Fin n → Fin n → ℂ),
      (∀ a i k, C a i k = C a k i) ∧
      (∀ i k j, chartPartialZComplex (fun w ↦ G w k j) z i +
        ∑ a, (G z) a j * C a i k = 0) ∧
      (∀ i j k, T i j k = chartPartialZComplex (fun w ↦ H w j k) z i +
        ∑ a, (H z) a k * C a i j) ∧
      (∀ i j k, T i j k = T j i k) := by
  let D : Fin n → Fin n → Fin n → ℂ := fun i k j ↦
    chartPartialZComplex (fun w ↦ G w k j) z i
  have hD : ∀ i k j, D i k j = D k i j := hGsym
  have hInv : (G z).transpose * (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [hG0]
    simp
  obtain ⟨C, hC, hcancel⟩ :=
    Matrix.exists_symmetric_normal_jet (G z) 1 hInv D hD
  let T : Fin n → Fin n → Fin n → ℂ := fun i j k ↦
    chartPartialZComplex (fun w ↦ H w j k) z i +
      ∑ a, (H z) a k * C a i j
  refine ⟨C, T, hC, ?_, ?_, ?_⟩
  · intro i k j
    simpa [D] using hcancel i k j
  · intro i j k
    rfl
  · intro i j k
    simp [T, hHsym i j k, hC]

omit [T2Space M] [CompactSpace M] in
/-- The normal-coordinate curvature expression reduces to the negative mixed second derivative
when both complex first derivatives of the chart metric vanish. -/
private theorem chernLuChartCurvature_eq_neg_second_of_firstDeriv_eq_zero
    (ω₀ : KahlerForm n M) (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hZ : ∀ p j k, chartPartialZComplex
      (fun w ↦ ω₀.metricInChart x w j k) z p = 0)
    (hBar : ∀ p j k,
      (fderiv ℝ (fun w ↦ (ω₀.metricInChart x w j k)) z
          (EuclideanSpace.single p 1) +
        Complex.I * fderiv ℝ (fun w ↦ (ω₀.metricInChart x w j k)) z
          (Complex.I • EuclideanSpace.single p 1)) / 2 = 0) :
    let dbar : (EuclideanSpace ℂ (Fin n) → ℂ) →
        EuclideanSpace ℂ (Fin n) → Fin n → ℂ := fun f w q ↦
      (fderiv ℝ f w (EuclideanSpace.single q 1) +
        Complex.I * fderiv ℝ f w (Complex.I • EuclideanSpace.single q 1)) / 2
    let G := ω₀.metricInChart x
    let curvature : Fin n → Fin n → Fin n → Fin n → ℂ := fun p q j k ↦
      -chartPartialZComplex (fun w ↦ dbar (fun v ↦ G v j k) w q) z p +
        ∑ a, ∑ b, (G z)⁻¹ b a *
          chartPartialZComplex (fun w ↦ G w j b) z p *
          dbar (fun w ↦ G w a k) z q
    ∀ p q j k, curvature p q j k =
      -chartPartialZComplex
        (fun w ↦ dbar (fun v ↦ G v j k) w q) z p := by
  dsimp only
  intro p q j k
  have hBar' (i a b : Fin n) :
      (fderiv ℝ (fun w ↦ ω₀.metricInChart x w a b) z (EuclideanSpace.single i 1) +
        Complex.I * fderiv ℝ (fun w ↦ ω₀.metricInChart x w a b) z
          (Complex.I • EuclideanSpace.single i 1)) / 2 = 0 := hBar i a b
  simp [hZ, hBar']
/-!
The first-derivative cancellation in the normal-coordinate proof is a weighted
Cauchy--Schwarz inequality: the inverse metric weights the squared norm of the
contraction, while the metric weights the squared norm of the derivative terms.
-/

private theorem weighted_sum_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u weights : ι → ℝ) (hweights : ∀ i, 0 < weights i) :
    (∑ i, u i) ^ 2 ≤ (∑ i, (weights i)⁻¹) * ∑ i, weights i * (u i) ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i ↦ (Real.sqrt (weights i))⁻¹) (fun i ↦ Real.sqrt (weights i) * u i)
  have hsqrt : ∀ i, Real.sqrt (weights i) ≠ 0 :=
    fun i ↦ (Real.sqrt_pos.2 (hweights i)).ne'
  have hsum :
      (∑ i, (Real.sqrt (weights i))⁻¹ * (Real.sqrt (weights i) * u i)) = ∑ i, u i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [← mul_assoc, inv_mul_cancel₀ (hsqrt i), one_mul]
  have hleft : (∑ i, ((Real.sqrt (weights i))⁻¹) ^ 2) = ∑ i, (weights i)⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [inv_pow, Real.sq_sqrt (hweights i).le]
  have hright :
      (∑ i, (Real.sqrt (weights i) * u i) ^ 2) = ∑ i, weights i * (u i) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hweights i).le]
  rw [hsum, hleft, hright] at hcs
  exact hcs

/-- Weighted Cauchy--Schwarz for a finite complex sum, in the form used for the diagonal
first-derivative terms of the Chern--Lu calculation. -/
private theorem complex_sum_norm_sq_le_weighted
    {ι : Type*} (s : Finset ι) (weights : ι → ℝ) (z : ι → ℂ)
    (hweights : ∀ i ∈ s, 0 < weights i) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, weights i) * ∑ i ∈ s, ‖z i‖ ^ 2 / weights i := by
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := s)
    (r := fun i ↦ ‖z i‖) (f := weights) (g := fun i ↦ ‖z i‖ ^ 2 / weights i)
    (fun i hi ↦ (hweights i hi).le)
    (fun i hi ↦ div_nonneg (sq_nonneg _) (hweights i hi).le)
    (fun i hi ↦ by
      rw [div_eq_mul_inv]
      field_simp [(hweights i hi).ne']
      exact le_rfl)
  have hnorm : ‖∑ i ∈ s, z i‖ ≤ ∑ i ∈ s, ‖z i‖ := norm_sum_le s z
  have hnorm_sq : ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm _
  exact hnorm_sq.trans hCS

/-- The diagonal gradient term in Székelyhidi's equation (3.6) is absorbed by the full
weighted squared norm of the symmetric Kähler first derivatives. -/
private theorem diagonal_gradient_absorption [NeZero n]
    (eigenvalue : Fin n → ℝ) (heigenvalue : ∀ j, 0 < eigenvalue j)
    (T : Fin n → Fin n → Fin n → ℂ)
    (hT : ∀ i j k, T i j k = T j i k) :
    (∑ p, ‖∑ j, T p j j‖ ^ 2 /
        (eigenvalue p * ∑ j, eigenvalue j)) ≤
      ∑ a, ∑ b, ∑ c, ‖T a b c‖ ^ 2 / (eigenvalue b * eigenvalue c) := by
  classical
  have hsum_pos : 0 < ∑ j : Fin n, eigenvalue j :=
    Finset.sum_pos (fun j _ ↦ heigenvalue j) Finset.univ_nonempty
  have hpoint (p : Fin n) :
      ‖∑ j : Fin n, T p j j‖ ^ 2 /
          (eigenvalue p * ∑ j : Fin n, eigenvalue j) ≤
        ∑ j : Fin n, ‖T p j j‖ ^ 2 / (eigenvalue p * eigenvalue j) := by
    have hCS := complex_sum_norm_sq_le_weighted Finset.univ eigenvalue
      (fun j ↦ T p j j) (fun j _ ↦ heigenvalue j)
    have hden : 0 < eigenvalue p * ∑ j : Fin n, eigenvalue j :=
      mul_pos (heigenvalue p) hsum_pos
    calc
      _ ≤ ((∑ j : Fin n, eigenvalue j) *
            ∑ j : Fin n, ‖T p j j‖ ^ 2 / eigenvalue j) /
            (eigenvalue p * ∑ j : Fin n, eigenvalue j) :=
        div_le_div_of_nonneg_right hCS hden.le
      _ = (eigenvalue p)⁻¹ *
            ∑ j : Fin n, ‖T p j j‖ ^ 2 / eigenvalue j := by
        field_simp [ne_of_gt (heigenvalue p), ne_of_gt hsum_pos]
      _ = ∑ j : Fin n, (eigenvalue p)⁻¹ * (‖T p j j‖ ^ 2 / eigenvalue j) :=
        by rw [Finset.mul_sum]
      _ = ∑ j : Fin n, ‖T p j j‖ ^ 2 / (eigenvalue p * eigenvalue j) := by
        apply Finset.sum_congr rfl
        intro j hj
        field_simp [ne_of_gt (heigenvalue p), ne_of_gt (heigenvalue j)]
  have hsum_pointwise := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) ↦ hpoint p)
  have hsymmetry :
      (∑ p : Fin n, ∑ j : Fin n, ‖T p j j‖ ^ 2 /
          (eigenvalue p * eigenvalue j)) =
        ∑ a : Fin n, ∑ b : Fin n, ‖T a b a‖ ^ 2 /
          (eigenvalue b * eigenvalue a) := by
    calc
      _ = ∑ p : Fin n, ∑ j : Fin n, ‖T j p j‖ ^ 2 /
            (eigenvalue p * eigenvalue j) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro j hj
          rw [hT p j j]
      _ = ∑ j : Fin n, ∑ p : Fin n, ‖T j p j‖ ^ 2 /
            (eigenvalue p * eigenvalue j) := Finset.sum_comm
      _ = _ := by rfl
  have hsub (a b : Fin n) :
      ‖T a b a‖ ^ 2 / (eigenvalue b * eigenvalue a) ≤
        ∑ c : Fin n, ‖T a b c‖ ^ 2 / (eigenvalue b * eigenvalue c) := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun c : Fin n ↦ ‖T a b c‖ ^ 2 / (eigenvalue b * eigenvalue c))
      (fun c _ ↦ div_nonneg (sq_nonneg _) (mul_nonneg (heigenvalue b).le (heigenvalue c).le))
      (Finset.mem_univ a)
  calc
    _ ≤ ∑ p : Fin n, ∑ j : Fin n,
          ‖T p j j‖ ^ 2 / (eigenvalue p * eigenvalue j) := hsum_pointwise
    _ = ∑ a : Fin n, ∑ b : Fin n,
          ‖T a b a‖ ^ 2 / (eigenvalue b * eigenvalue a) := hsymmetry
    _ ≤ ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          ‖T a b c‖ ^ 2 / (eigenvalue b * eigenvalue c) :=
      Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hsub a b

/-- A uniform lower bound for each bisectional-curvature entry gives the weighted lower bound
used after diagonalizing the varying metric. -/
private theorem weighted_bisectional_sum_lower_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (curvature : ι → κ → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hcurvature : ∀ i j, -B ≤ curvature i j) :
    -B * (∑ i, a i) * (∑ j, b j) ≤
      ∑ i, ∑ j, a i * b j * curvature i j := by
  calc
    -B * (∑ i, a i) * (∑ j, b j) =
        ∑ i, ∑ j, a i * b j * (-B) := by
      have hprod : (∑ i, a i) * (∑ j, b j) = ∑ i, ∑ j, a i * b j :=
        Fintype.sum_mul_sum a b
      calc
        -B * (∑ i, a i) * (∑ j, b j) =
            -B * ((∑ i, a i) * (∑ j, b j) : ℝ) := by ring
        _ = -B * (∑ i, ∑ j, a i * b j) := by rw [hprod]
        _ = ∑ i, ∑ j, a i * b j * (-B) := by
          simp_rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
    _ ≤ ∑ i, ∑ j, a i * b j * curvature i j := by
      refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
      exact mul_le_mul_of_nonneg_left (hcurvature i j) (mul_nonneg (ha i) (hb j))

/-- Pointwise finite-dimensional core of Yau's Laplacian estimate. The symmetric second
derivative terms cancel after swapping indices; the curvature contraction is bounded below by
the uniform bisectional bound, and the first-derivative term is absorbed by weighted
Cauchy--Schwarz. -/
private theorem yau_diagonal_trace_estimate [NeZero n]
    (lambda : Fin n → ℝ) (curvature : Fin n → Fin n → ℝ)
    (T : Fin n → Fin n → Fin n → ℂ) (H : Fin n → Fin n → ℝ) (B : ℝ)
    (hlambda : ∀ p, 0 < lambda p)
    (hcurvature : ∀ p j, -B ≤ curvature p j)
    (hT : ∀ i j k, T i j k = T j i k)
    (hH : ∀ p j, H p j = H j p) :
    ((∑ p, ∑ j, H p j / lambda p) +
        ∑ p, ∑ j, (lambda p)⁻¹ * lambda j * curvature p j) /
        (∑ j, lambda j) -
      (∑ p, ‖∑ j, T p j j‖ ^ 2 /
        (lambda p * ∑ j, lambda j)) /
        (∑ j, lambda j) ≥
      ((∑ p, ∑ j, H p j / lambda j) -
          ∑ p, ∑ j, ∑ k, ‖T p j k‖ ^ 2 / (lambda j * lambda k)) /
          (∑ j, lambda j) -
        B * (∑ p, (lambda p)⁻¹) := by
  classical
  let u : ℝ := ∑ j, lambda j
  let v : ℝ := ∑ p, (lambda p)⁻¹
  let c : ℝ := ∑ p, ∑ j, (lambda p)⁻¹ * lambda j * curvature p j
  let q : ℝ := ∑ p, ∑ j, ∑ k, ‖T p j k‖ ^ 2 / (lambda j * lambda k)
  let g : ℝ := ∑ p, ‖∑ j, T p j j‖ ^ 2 / (lambda p * u)
  have hu : 0 < u := by
    dsimp [u]
    exact Finset.sum_pos (fun j _ ↦ hlambda j) Finset.univ_nonempty
  have hsumH : (∑ p, ∑ j, H p j / lambda p) =
      ∑ p, ∑ j, H p j / lambda j := by
    calc
      (∑ p, ∑ j, H p j / lambda p) =
          ∑ p, ∑ j, H j p / lambda p := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro j hj
        rw [hH]
      _ = ∑ j, ∑ p, H j p / lambda p := Finset.sum_comm
      _ = ∑ p, ∑ j, H p j / lambda j := by rw [Finset.sum_comm]
  have hgrad : g ≤ q := by
    dsimp [g, q, u]
    exact diagonal_gradient_absorption lambda hlambda T hT
  have hcurv := weighted_bisectional_sum_lower_bound
    (fun p ↦ (lambda p)⁻¹) lambda curvature B
    (fun p ↦ inv_nonneg.mpr (hlambda p).le)
    (fun j ↦ (hlambda j).le) hcurvature
  have hcurv_div : -B * v ≤ c / u := by
    apply (le_div_iff₀ hu).2
    simpa [v, u, c, mul_assoc, mul_left_comm, mul_comm] using hcurv
  change ((∑ p, ∑ j, H p j / lambda p) + c) / u - g / u ≥
    ((∑ p, ∑ j, H p j / lambda j) - q) / u - B * v
  rw [hsumH]
  have hcancel : (q - g) / u + (c / u + B * v) ≥ 0 := by
    have hqg : 0 ≤ (q - g) / u := by
      exact div_nonneg (sub_nonneg.mpr hgrad) hu.le
    have hcv : 0 ≤ c / u + B * v := by
      linarith [hcurv_div]
    linarith
  have halgebra : (∑ p, ∑ j, H p j / lambda j + c) / u - g / u -
      ((∑ p, ∑ j, H p j / lambda j - q) / u - B * v) =
        (q - g) / u + (c / u + B * v) := by
    field_simp [ne_of_gt hu]
    ring
  linarith [halgebra, hcancel]

omit [T2Space M] [CompactSpace M] in
/-- The Ricci term of a varying Kähler metric, traced against the reference metric,
is the reference Ricci trace minus the reference Laplacian of the log relative volume.
This is the Ricci/Laplacian bridge used in Yau's formulation of the trace estimate. -/
private theorem relTrace_ricciForm_eq_reference_sub_laplacian
    (ω₀ ω₁ : KahlerForm n M) (x : M) :
    relTrace (ω₀ x) (ω₁.ricciForm x) =
      relTrace (ω₀ x) (ω₀.ricciForm x) -
        ω₀.laplacian (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x := by
  have hforms := congrArg (fun η : FormField (EuclideanSpace ℂ (Fin n)) M 2 ↦
      relTrace (ω₀ x) (η x)) (KahlerForm.ricciForm_sub_ricciForm ω₀ ω₁)
  change relTrace (ω₀ x) (ω₀.ricciForm x - ω₁.ricciForm x) = _ at hforms
  rw [ContinuousAlternatingMap.relTrace_sub] at hforms
  have hlap :
      ω₀.laplacian (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x =
        relTrace (ω₀ x)
          (mddbar n (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x) := rfl
  linarith

/-- Compactness gives a uniform signed curvature bound and normal-coordinate data realizing the
Laplacian and Ricci expansions at every point. The finite-dimensional estimate below closes the
remaining analytic cancellation. The signed curvature array is chosen so that its contraction
enters the trace Laplacian with a plus sign. -/
private theorem exists_yau_normal_data (ω₀ : KahlerForm n M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ω₁ : KahlerForm n M) x,
      ∃ (lambda : Fin n → ℝ) (curvature : Fin n → Fin n → ℝ)
        (first : Fin n → Fin n → Fin n → ℂ) (second : Fin n → Fin n → ℝ),
        (∀ p, 0 < lambda p) ∧
        (∀ p j, -B ≤ curvature p j) ∧
        (∀ i j k, first i j k = first j i k) ∧
        (∀ p j, second p j = second j p) ∧
        relTrace (ω₀ x) (ω₁ x) = ∑ j, lambda j ∧
        relTrace (ω₁ x) (ω₀ x) = ∑ p, (lambda p)⁻¹ ∧
        ω₁.laplacian (fun y ↦ Real.log (relTrace (ω₀ y) (ω₁ y))) x =
          ((∑ p, ∑ j, second p j / lambda p) +
              ∑ p, ∑ j, (lambda p)⁻¹ * lambda j * curvature p j) /
              (∑ j, lambda j) -
            (∑ p, ‖∑ j, first p j j‖ ^ 2 /
              (lambda p * ∑ j, lambda j)) /
              (∑ j, lambda j) ∧
        -(relTrace (ω₀ x) (ω₀.ricciForm x) -
            ω₀.laplacian (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x) =
          (∑ p, ∑ j, second p j / lambda j) -
            ∑ p, ∑ j, ∑ k, ‖first p j k‖ ^ 2 / (lambda j * lambda k) := by
  obtain ⟨B, hB, hcurvatureBound⟩ :=
    exists_normalFrame_bisectional_lower_bound (ω₀ := ω₀)
  refine ⟨B, hB, fun ω₁ x ↦ ?_⟩
  obtain ⟨F⟩ := exists_yau_normal_frame ω₀ ω₁ x
  let lambda : Fin n → ℝ := F.eigenvalue
  let curvature : Fin n → Fin n → ℝ :=
    normalFrameBisectionalCurvature ω₀ ω₁ x F
  let first : Fin n → Fin n → Fin n → ℂ := normalFrameFirstDerivative F
  let second : Fin n → Fin n → ℝ := normalFrameSecondReal ω₀ ω₁ x F
  have hlambda : ∀ p, 0 < lambda p := by
    intro p
    exact F.eigenvalue_pos p
  have hcurvature : ∀ p j, -B ≤ curvature p j := by
    intro p j
    exact hcurvatureBound ω₁ x F p j
  have hfirst : ∀ i j k, first i j k = first j i k := by
    simpa [first] using normalFrame_first_derivative_symmetric ω₀ ω₁ x F
  have hsecond : ∀ p j, second p j = second j p := by
    simpa [second] using normalFrame_second_derivative_symmetric ω₀ ω₁ x F
  rcases normalFrame_relative_trace_eq_sums ω₀ ω₁ x F with
    ⟨htrace, hreverse⟩
  have htrace' : relTrace (ω₀ x) (ω₁ x) = ∑ j, lambda j := by
    simpa [lambda] using htrace
  have hreverse' : relTrace (ω₁ x) (ω₀ x) = ∑ p, (lambda p)⁻¹ := by
    simpa [lambda] using hreverse
  have hlaplacianExpansion := normalFrame_laplacian_log_relative_trace ω₀ ω₁ x F
  have hlaplacian :
      ω₁.laplacian (fun y ↦ Real.log (relTrace (ω₀ y) (ω₁ y))) x =
        ((∑ p, ∑ j, second p j / lambda p) +
            ∑ p, ∑ j, (lambda p)⁻¹ * lambda j * curvature p j) /
            (∑ j, lambda j) -
          (∑ p, ‖∑ j, first p j j‖ ^ 2 /
              (lambda p * ∑ j, lambda j)) /
            (∑ j, lambda j) := by
    simpa [lambda, curvature, first, second] using hlaplacianExpansion
  have hricciExpansion :=
    normalFrame_ricci_relative_determinant_expansion ω₀ ω₁ x F
  have hricci :
      -(relTrace (ω₀ x) (ω₀.ricciForm x) -
          ω₀.laplacian (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x) =
        (∑ p, ∑ j, second p j / lambda j) -
          ∑ p, ∑ j, ∑ k, ‖first p j k‖ ^ 2 /
            (lambda j * lambda k) := by
    simpa [lambda, first, second] using hricciExpansion
  exact ⟨lambda, curvature, first, second, hlambda, hcurvature, hfirst, hsecond,
    htrace', hreverse', hlaplacian, hricci⟩

/-- Yau's relative-volume form of the Chern--Lu estimate. The Laplacian bridge above converts
this form to the varying-metric Ricci formulation in the public theorem. -/
private theorem laplacian_log_relTrace_ge_chernLu_yau
    (ω₀ : KahlerForm n M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ω₁ : KahlerForm n M) x,
      ω₁.laplacian (fun y ↦ Real.log (relTrace (ω₀ y) (ω₁ y))) x ≥
        -(relTrace (ω₀ x) (ω₀.ricciForm x) -
            ω₀.laplacian (fun y ↦ Real.log (relDet (ω₀ y) (ω₁ y))) x) /
            relTrace (ω₀ x) (ω₁ x) -
          B * relTrace (ω₁ x) (ω₀ x) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨0, le_rfl, fun ω₁ x ↦ ?_⟩
    simp [KahlerForm.laplacian, ContinuousAlternatingMap.relTrace]
  · have : NeZero n := ⟨hn⟩
    obtain ⟨B, hB, hdata⟩ := exists_yau_normal_data ω₀
    refine ⟨B, hB, fun ω₁ x ↦ ?_⟩
    obtain ⟨lambda, curvature, first, second, hlambda, hcurvature, hfirst, hsecond,
      htrace, hreverse, hlaplacian, hricci⟩ := hdata ω₁ x
    rw [hlaplacian, hricci, htrace, hreverse]
    exact yau_diagonal_trace_estimate lambda curvature first second B
      hlambda hcurvature hfirst hsecond

/-- Chern–Lu's pointwise estimate for the trace of one Kähler metric against another. The
curvature constant is uniform on the compact manifold; the Ricci term is the Ricci form of the
varying metric, traced against the reference metric. -/
theorem laplacian_log_relTrace_ge_chernLu
    (ω₀ : KahlerForm n M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ω₁ : KahlerForm n M) x,
      ω₁.laplacian (fun y ↦ Real.log (relTrace (ω₀ y) (ω₁ y))) x ≥
        -(relTrace (ω₀ x) (ω₁.ricciForm x)) /
            relTrace (ω₀ x) (ω₁ x) -
          B * relTrace (ω₁ x) (ω₀ x) := by
  obtain ⟨B, hB, hCL⟩ := laplacian_log_relTrace_ge_chernLu_yau ω₀
  refine ⟨B, hB, fun ω₁ x ↦ ?_⟩
  have hRicci := relTrace_ricciForm_eq_reference_sub_laplacian ω₀ ω₁ x
  rw [hRicci]
  exact hCL ω₁ x

end KahlerForm
