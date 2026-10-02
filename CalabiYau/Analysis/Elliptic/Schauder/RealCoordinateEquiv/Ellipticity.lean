module

public import CalabiYau.Analysis.Elliptic.Schauder
public import CalabiYau.Analysis.Elliptic.Schauder.Realification
public import CalabiYau.Analysis.Elliptic.Schauder.RealCoordinateEquiv

/-!
# Ellipticity of the realified Schauder symbol

Uniform complex ellipticity becomes real ellipticity with the Hessian normalization factor `1/4`.
Order-zero coefficient bounds also give a dimension-dependent upper bound for the real quadratic
symbol. The real coordinates retain the order `(j,0) = Re zⱼ`, `(j,1) = Im zⱼ`.
-/

@[expose] public section

open Set Matrix
open scoped NNReal

private theorem realQuadratic_le_card_mul_entryBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hB : ∀ i j, |B i j| ≤ K) (x : ι → ℝ) :
    dotProduct x (B *ᵥ x) ≤
      (Fintype.card ι : ℝ) * K * ∑ i, x i ^ 2 := by
  classical
  let S : ℝ := ∑ i, |x i|
  have hrow (i : ι) : |∑ j, B i j * x j| ≤ K * S := by
    calc
      |∑ j, B i j * x j| ≤ ∑ j, |B i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, K * |x j| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hB i j) (abs_nonneg _)
      _ = K * S := by simp [S, Finset.mul_sum]
  calc
    dotProduct x (B *ᵥ x) = ∑ i, x i * ∑ j, B i j * x j := by
      simp [dotProduct, Matrix.mulVec]
    _ ≤ ∑ i, |x i| * (K * S) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        x i * ∑ j, B i j * x j ≤ |x i * ∑ j, B i j * x j| := le_abs_self _
        _ = |x i| * |∑ j, B i j * x j| := abs_mul _ _
        _ ≤ |x i| * (K * S) :=
          mul_le_mul_of_nonneg_left (hrow i) (abs_nonneg _)
    _ = K * S ^ 2 := by
      dsimp [S]
      rw [← Finset.sum_mul]
      ring
    _ ≤ (Fintype.card ι : ℝ) * K * ∑ i, x i ^ 2 := by
      have hcs : (∑ i, |x i|) ^ 2 ≤
          (Fintype.card ι : ℝ) * ∑ i, x i ^ 2 := by
        simpa [sq_abs, mul_comm] using
          (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
            (fun i : ι => |x i|) (fun _ => (1 : ℝ)))
      calc
        K * (∑ i, |x i|) ^ 2 ≤
            K * ((Fintype.card ι : ℝ) * ∑ i, x i ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hK
        _ = (Fintype.card ι : ℝ) * K * ∑ i, x i ^ 2 := by ring

private theorem quarter_abs_re_le_norm (z : ℂ) :
    (4⁻¹ : ℝ) * |z.re| ≤ ‖z‖ := by
  calc
    (4⁻¹ : ℝ) * |z.re| ≤ |z.re| := by nlinarith [abs_nonneg z.re]
    _ ≤ ‖z‖ := Complex.abs_re_le_norm z

private theorem quarter_abs_im_le_norm (z : ℂ) :
    (4⁻¹ : ℝ) * |z.im| ≤ ‖z‖ := by
  calc
    (4⁻¹ : ℝ) * |z.im| ≤ |z.im| := by nlinarith [abs_nonneg z.im]
    _ ≤ ‖z‖ := Complex.abs_im_le_norm z

private theorem realPrincipalCoefficient_entry_bound {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (K : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ K) :
    ∀ p q, |realPrincipalCoefficient A p q| ≤ K := by
  classical
  intro p q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [realPrincipalCoefficient, Matrix.smul_apply, smul_eq_mul,
      Matrix.realify_apply, Matrix.transpose_apply] <;>
    first
    | exact (quarter_abs_re_le_norm (A j i)).trans (hA j i)
    | exact (quarter_abs_im_le_norm (A j i)).trans (hA j i)

private theorem realPrincipalCoefficient_isSymm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (realPrincipalCoefficient A).IsSymm := by
  change ((1 / 4 : ℝ) • Matrix.realify A.transpose)ᵀ =
    (1 / 4 : ℝ) • Matrix.realify A.transpose
  rw [Matrix.transpose_smul]
  rw [Matrix.IsHermitian.isSymm_realify (Matrix.IsHermitian.transpose hA)]

/-- Uniform complex ellipticity and order-zero coefficient bounds give the realified symbol's
positive definiteness, its exact `λ/4` lower bound, and a dimension-times-`K` upper bound. The
coordinate dimension is `card (Fin n × Fin 2)`, and the result includes `n = 0`. -/
theorem realPrincipalCoefficient_ellipticity {n : ℕ}
    {α lam K : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (hLam : 0 < lam) (hEll : IsUniformlyEllipticOn A lam U)
    (hHolder : ∀ j l, HolderBoundOn 0 α K U fun z ↦ A z j l) :
    ∀ z ∈ U,
      (realPrincipalCoefficient (A z)).PosDef ∧
      ∀ x : Fin n × Fin 2 → ℝ,
        ((lam : ℝ) / 4) * ∑ p, x p ^ 2 ≤
            dotProduct x (Matrix.mulVec (realPrincipalCoefficient (A z)) x) ∧
          dotProduct x (Matrix.mulVec (realPrincipalCoefficient (A z)) x) ≤
            (Fintype.card (Fin n × Fin 2) : ℝ) * (K : ℝ) * ∑ p, x p ^ 2 := by
  intro z hz
  rcases hEll z hz with ⟨hHerm, hComplexLower⟩
  have hEntry (j l : Fin n) : ‖A z j l‖ ≤ (K : ℝ) := by
    have h := (hHolder j l).1 0 (by omega) z hz
    simpa only [norm_iteratedFDeriv_zero] using h
  have hRealEntry : ∀ p q, |realPrincipalCoefficient (A z) p q| ≤ (K : ℝ) :=
    realPrincipalCoefficient_entry_bound (A z) (K : ℝ) hEntry
  have hSymm : (realPrincipalCoefficient (A z)).IsSymm :=
    realPrincipalCoefficient_isSymm (A z) hHerm
  have hLower (x : Fin n × Fin 2 → ℝ) :
      ((lam : ℝ) / 4) * ∑ p, x p ^ 2 ≤
        dotProduct x (Matrix.mulVec (realPrincipalCoefficient (A z)) x) :=
    realPrincipalCoefficient_lower_bound (A z) (lam : ℝ) hComplexLower x
  have hPosDef : (realPrincipalCoefficient (A z)).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hSymm
    intro x hx
    have hex : ∃ p, x p ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    obtain ⟨p, hp⟩ := hex
    have hsum : 0 < ∑ q, x q ^ 2 := by
      apply Finset.sum_pos'
      · intro q hq
        exact sq_nonneg (x q)
      · exact ⟨p, Finset.mem_univ p, sq_pos_of_ne_zero hp⟩
    have hscale : 0 < ((lam : ℝ) / 4) := by positivity
    have hprod : 0 < ((lam : ℝ) / 4) * ∑ q, x q ^ 2 := mul_pos hscale hsum
    have hdotPre := lt_of_lt_of_le hprod (hLower x)
    have hdot : @LT.lt ℝ Real.partialOrder.toLT 0
        (dotProduct x (Matrix.mulVec (realPrincipalCoefficient (A z)) x)) := by
      rw [Real.partialOrder.lt_iff_le_not_ge]
      exact ⟨le_of_lt hdotPre, fun hrev => (not_le_of_gt hdotPre) hrev⟩
    change @LT.lt ℝ Real.partialOrder.toLT 0
      (dotProduct (star x) (Matrix.mulVec (realPrincipalCoefficient (A z)) x))
    simpa only [star_trivial] using hdot
  have hUpper (x : Fin n × Fin 2 → ℝ) :
      dotProduct x (Matrix.mulVec (realPrincipalCoefficient (A z)) x) ≤
        (Fintype.card (Fin n × Fin 2) : ℝ) * (K : ℝ) * ∑ p, x p ^ 2 :=
    realQuadratic_le_card_mul_entryBound (realPrincipalCoefficient (A z))
      (K : ℝ) (NNReal.coe_nonneg K) hRealEntry x
  exact ⟨hPosDef, fun x => ⟨hLower x, hUpper x⟩⟩

end
