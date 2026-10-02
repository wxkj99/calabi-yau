module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
public import CalabiYau.Geometry.Complex.Forms.ComplexHessian

/-!
# Interior Schauder estimates for complex elliptic operators (hypothesis)

For a Hermitian-matrix-valued function `A` on a domain of `ℂⁿ`, the operator

  `L_A u = re tr (A · (∂²u/∂zⱼ∂z̄ₖ)) = ∑ A_{kj} u_{jk̄}`

is a real second-order operator, uniformly elliptic when `A ≥ λ > 0`. The Laplacian of a Kähler
form in a chart is `L_A` with `A = g⁻¹`, and differentiating the Monge–Ampère equation produces
`L_A` with `A = (g + φ_{jk̄})⁻¹`.

`InteriorSchauderEstimate n` is classical interior Schauder theory for these operators,
**regularity and estimate** (Gilbarg–Trudinger, Theorem 6.17 for regularity, Theorem 6.2 and
Problem 6.1 for the estimate): for `0 < α < 1`, `V ⋐ U`, ellipticity `λ` and a `C^{k,α}(U)`
bound `K` on `C^k` coefficients, there is `C = C(n, k, α, λ, K, U, V)` such that every
`u ∈ C²(U)` with `L_A u ∈ C^k(U)` satisfies `u ∈ C^{k+2}(U)` and

  `‖u‖_{C^{k+2,α}(V)} ≤ C (‖L_A u‖_{C^{k,α}(U)} + ‖u‖_{C⁰(U)})`.

The regularity half is what bootstraps the `C^{2,α}` solution produced by the implicit function
theorem (openness) to a smooth one; the a priori estimate for smooth data is
`InteriorSchauderEstimate.holderBoundOn_of_contDiffOn`. It is
**not proved here**; it is an explicit hypothesis of the higher-order estimates and of the
openness step. Track S (extracted Euclidean Schauder theory) is expected to prove
`∀ n, InteriorSchauderEstimate n`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open Set Matrix

/-- The operator `L_A u = re tr (A · (u_{jk̄}))` on `ℂⁿ`. -/
noncomputable def complexEllipticOp {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  RCLike.re (A z * complexHessian u z).trace

/-- `A` is uniformly elliptic with constant `λ` on `U`: Hermitian with `v* A v ≥ λ |v|²`. -/
def IsUniformlyEllipticOn {n : ℕ} (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (lam : ℝ≥0) (U : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ z ∈ U, (A z).IsHermitian ∧
    ∀ v : Fin n → ℂ, (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ RCLike.re (star v ⬝ᵥ (A z *ᵥ v))

/-- Interior Schauder regularity and estimate for the operators `L_A` on `ℂⁿ`, with the
dependence of the constant made explicit by the order of quantifiers. -/
def InteriorSchauderEstimate (n : ℕ) : Prop :=
  ∀ (k : ℕ) (α : ℝ≥0), 0 < α → α < 1 →
    ∀ (lam K : ℝ≥0), 0 < lam →
      ∀ U V : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → IsCompact (closure V) → closure V ⊆ U →
        ∃ C : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
          (u : EuclideanSpace ℂ (Fin n) → ℝ),
          (∀ j l, ContDiffOn ℝ k (fun z ↦ A z j l) U) → ContDiffOn ℝ 2 u U →
          IsUniformlyEllipticOn A lam U →
          (∀ j l, HolderBoundOn k α K U fun z ↦ A z j l) →
          ∀ K₀ K₁ : ℝ≥0, ContDiffOn ℝ k (complexEllipticOp A u) U →
            HolderBoundOn k α K₁ U (complexEllipticOp A u) → (∀ z ∈ U, |u z| ≤ K₀) →
            ContDiffOn ℝ (k + 2 : ℕ) u U ∧ HolderBoundOn (k + 2) α (C * (K₁ + K₀)) V u

/-- The a priori estimate for smooth coefficients and smooth solutions. -/
theorem InteriorSchauderEstimate.holderBoundOn_of_contDiffOn {n : ℕ}
    (h : InteriorSchauderEstimate n) :
    ∀ (k : ℕ) (α : ℝ≥0), 0 < α → α < 1 →
      ∀ (lam K : ℝ≥0), 0 < lam →
        ∀ U V : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → IsCompact (closure V) →
          closure V ⊆ U →
          ∃ C : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
            (u : EuclideanSpace ℂ (Fin n) → ℝ),
            (∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A z j l) U) → ContDiffOn ℝ ∞ u U →
            IsUniformlyEllipticOn A lam U →
            (∀ j l, HolderBoundOn k α K U fun z ↦ A z j l) →
            ∀ K₀ K₁ : ℝ≥0, HolderBoundOn k α K₁ U (complexEllipticOp A u) →
              (∀ z ∈ U, |u z| ≤ K₀) → HolderBoundOn (k + 2) α (C * (K₁ + K₀)) V u := by
  intro k α hα₀ hα₁ lam K hlam U V hU hV hVU
  obtain ⟨C, hC⟩ := h k α hα₀ hα₁ lam K hlam U V hU hV hVU
  refine ⟨C, ?_⟩
  intro A u hA hu hEll hAHolder K₀ K₁ hLuHolder huBound
  apply (hC A u ?_ ?_ hEll hAHolder K₀ K₁ ?_ hLuHolder huBound).2
  · intro j l
    exact (hA j l).of_le (WithTop.coe_le_coe.mpr le_top)
  · exact hu.of_le (WithTop.coe_le_coe.mpr le_top)
  · have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) U := by
      exact hu.fderiv_of_isOpen hU (WithTop.coe_le_coe.mpr le_top)
    have hD₂u : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ u)) U := by
      exact hDu.fderiv_of_isOpen hU (WithTop.coe_le_coe.mpr le_top)
    have hD₂eval (v w : EuclideanSpace ℂ (Fin n)) :
        ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fderiv ℝ u) z v w) U := by
      have hv : ContDiffOn ℝ ∞ (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) U := contDiffOn_const
      have hw : ContDiffOn ℝ ∞ (fun _ : EuclideanSpace ℂ (Fin n) ↦ w) U := contDiffOn_const
      exact (hD₂u.clm_apply hv).clm_apply hw
    have hEntry (j l : Fin n) :
        ContDiffOn ℝ ∞ (fun z ↦ complexHessian u z j l) U := by
      have hFormula : ContDiffOn ℝ ∞ (fun z ↦
          ((fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) : ℂ) +
            fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
              (Complex.I • EuclideanSpace.single l 1) +
            Complex.I * (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1)
              (Complex.I • EuclideanSpace.single l 1) -
            fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
                (EuclideanSpace.single l 1))) / 4) U := by
        simp only [← Complex.ofRealCLM_apply]
        fun_prop
      apply hFormula.congr
      intro z hz
      rw [complexHessian_apply
        (((hu z hz).contDiffAt (hU.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top))]
    have hSum : ContDiffOn ℝ ∞ (fun z ↦
        ∑ i, ∑ j, Complex.reCLM (A z i j * complexHessian u z j i)) U := by
      fun_prop
    have hOp : ContDiffOn ℝ ∞
        (fun z ↦ RCLike.re ((A z * complexHessian u z).trace)) U := by
      change ContDiffOn ℝ ∞
        (fun z ↦ Complex.reCLM ((A z * complexHessian u z).trace)) U
      apply hSum.congr
      intro z hz
      simp [Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]
    change ContDiffOn ℝ k
      (fun z ↦ RCLike.re ((A z * complexHessian u z).trace)) U
    exact hOp.of_le (WithTop.coe_le_coe.mpr le_top)

/-- The Euclidean Laplacian case `A = 1` is included. -/
theorem isUniformlyEllipticOn_one {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) :
    IsUniformlyEllipticOn (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) 1 U := by
  intro z hz
  constructor
  · simp [Matrix.IsHermitian]
  · intro v
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Complex.normSq_apply,
      ← Complex.normSq_eq_norm_sq]

/-- `L_1 u = ∑ⱼ u_{jj̄} = ¼ Δ_{ℝ²ⁿ} u`. -/
theorem complexEllipticOp_one {n : ℕ} {u : EuclideanSpace ℂ (Fin n) → ℝ}
    {z : EuclideanSpace ℂ (Fin n)} (hu : ContDiffAt ℝ 2 u z) :
    complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) u z =
      (∑ j, (iteratedFDeriv ℝ 2 u z ![EuclideanSpace.single j 1, EuclideanSpace.single j 1] +
        iteratedFDeriv ℝ 2 u z ![Complex.I • EuclideanSpace.single j 1,
          Complex.I • EuclideanSpace.single j 1])) / 4 := by
  change RCLike.re (((1 : Matrix (Fin n) (Fin n) ℂ) * complexHessian u z).trace) = _
  simp only [Matrix.one_mul, Matrix.trace]
  simp_rw [Matrix.diag_apply, complexHessian_apply hu]
  simp [Complex.add_re, Complex.mul_re, iteratedFDeriv_two_apply]
  rw [← Finset.sum_div]
