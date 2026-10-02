module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.TraceMatrixJets

/-!
# Holomorphic normal coordinates for the reference metric

At any point choose a local holomorphic change `F` from the point-selected
coordinate chart, whose Jacobian is invertible, such that the pulled-back
reference metric is the identity with zero first holomorphic derivatives and
the pulled-back positive perturbed metric is diagonal. This is only the
normal-coordinate *existence* step. The equation, Kähler symmetries and the
transport of Laplacian, curvature and energy are separate children.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.2,
Lemma 3.8, pp. 41–43, and §3.3, Lemma 3.10, pp. 45–46; Yau (1978), §3.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Pull back the reference metric by the complex Jacobian of a holomorphic
coordinate map `F`; the matrix convention is `Jᵀ g conj(J)`. -/
noncomputable def c3RefinedTracePulledReferenceMetric (ω₀ : KahlerForm n M) (x : M)
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (w : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  let J := EuclideanSpace.clmMatrix (fderiv ℂ F w)
  J.transpose * ω₀.metricInChart x (F w) * J.map star

/-- Pull back the positive perturbed metric with the *same* Jacobian as the
reference metric. This prevents independent, incompatible diagonalizations. -/
noncomputable def c3RefinedTracePulledPerturbedMetric (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M)
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (w : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  let J := EuclideanSpace.clmMatrix (fderiv ℂ F w)
  let h := ω₀.metricInChart x (F w) + complexHessian
    (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) (F w)
  J.transpose * h * J.map star

/-- A concrete local holomorphic chart change to a reference-normal,
perturbed-diagonal frame. The pullback metrics are *defined* from `F` above;
this record does not postulate unrelated matrices or the desired inequality.
Reference normalization does not bound the entries of the Jacobian by one:
in dimension one, `g₀ = 1/100` and `J = 10` already give `Jᵀg₀conj(J) = 1`.
Transport arguments must cancel the Jacobians tensorially, or use explicit
reference-ellipticity bounds on fixed compact chart pieces. -/
structure C3RefinedTraceNormalCoordinateFrame (ω₀ : KahlerForm n M) (φ : M → ℝ)
    (x : M) where
  center : EuclideanSpace ℂ (Fin n)
  domain : Set (EuclideanSpace ℂ (Fin n))
  open_domain : IsOpen domain
  center_mem : center ∈ domain
  coord : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)
  holomorphic : ContDiffOn ℂ ∞ coord domain
  in_chart : coord '' domain ⊆
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  center_eq : coord center = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  jacobian_unit : ∀ w ∈ domain,
    IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ coord w)).det
  eigenvalue : Fin n → ℝ
  eigenvalue_pos : ∀ i, 0 < eigenvalue i
  reference_normal : c3RefinedTracePulledReferenceMetric ω₀ x coord center = 1
  reference_first : ∀ i j p,
    c3PartialZ (fun w ↦ c3RefinedTracePulledReferenceMetric ω₀ x coord w i j) center p = 0
  perturbed_diagonal : c3RefinedTracePulledPerturbedMetric ω₀ φ x coord center =
    Matrix.diagonal (fun i ↦ (eigenvalue i : ℂ))

open scoped ComplexOrder MatrixOrder

set_option maxHeartbeats 800000 in
/-- A Kähler reference metric admits holomorphic normal coordinates at each
point; a constant unitary rotation simultaneously diagonalizes the positive
perturbed metric at that point. No global or uniformly sized normal chart is
claimed. The zero-dimensional case uses the unique empty frame. -/
theorem exists_c3RefinedTrace_normalCoordinateFrame (ω₀ : KahlerForm n M)
    (G φ : M → ℝ) (hsol : ω₀.SolvesMongeAmpere G φ) (x : M) :
    Nonempty (C3RefinedTraceNormalCoordinateFrame ω₀ φ x) := by
  have c3RefinedTracePulledPerturbedMetric_posDef
      (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
      (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
      (w : EuclideanSpace ℂ (Fin n)) (hφ : ω₀.IsPotential φ)
      (hw : F w ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (hJ : IsUnit ((EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star)) :
      (c3RefinedTracePulledPerturbedMetric ω₀ φ x F w).PosDef := by
    let H := ω₀.metricInChart x (F w) + complexHessian
      (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) (F w)
    have hH : H.PosDef := by
      have h := (ω₀.perturb φ hφ).posDef_metricInChart x hw
      rw [KahlerForm.metricInChart_perturb hφ x hw] at h
      exact h
    let J := EuclideanSpace.clmMatrix (fderiv ℂ F w)
    change (J.transpose * H * J.map star).PosDef
    have htranspose : J.transpose = star (J.map star) := by
      ext i j
      simp [J, Matrix.transpose, Matrix.map_apply]
    rw [htranspose]
    exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hJ).2 hH

  have c3RefinedTrace_exists_posDef_congruence_identity {n : ℕ}
      (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
      ∃ P : Matrix (Fin n) (Fin n) ℂ, star P * A * P = 1 ∧ IsUnit P := by
    classical
    let h := hA.isHermitian
    let U : Matrix (Fin n) (Fin n) ℂ := h.eigenvectorUnitary
    let d : Fin n → ℝ := h.eigenvalues
    let s : Fin n → ℂ := fun i ↦ (((Real.sqrt (d i))⁻¹ : ℝ) : ℂ)
    let S : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal s
    let P : Matrix (Fin n) (Fin n) ℂ := U * S
    have hd (i : Fin n) : 0 < d i := hA.eigenvalues_pos i
    have hs (i : Fin n) : s i ≠ 0 := by
      change (((Real.sqrt (d i))⁻¹ : ℝ) : ℂ) ≠ 0
      exact_mod_cast (inv_ne_zero (Real.sqrt_ne_zero'.2 (hd i)))
    have hdiag : star U * A * U = Matrix.diagonal (fun i ↦ (d i : ℂ)) := by
      have h' := h.conjStarAlgAut_star_eigenvectorUnitary
      rw [Unitary.conjStarAlgAut_star_apply] at h'
      simpa [h, U, d, Function.comp_def] using h'
    have hSstar : star S = S := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [S, Matrix.diagonal, s]
      · simp [S, Matrix.diagonal, hij, Ne.symm hij]
    have hDS : star S * Matrix.diagonal (fun i ↦ (d i : ℂ)) * S = 1 := by
      rw [hSstar]
      change (Matrix.diagonal s * Matrix.diagonal (fun i ↦ (d i : ℂ))) *
        Matrix.diagonal s = 1
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      change (((Real.sqrt (d i))⁻¹ : ℝ) : ℂ) * (d i : ℂ) *
        (((Real.sqrt (d i))⁻¹ : ℝ) : ℂ) = 1
      have hscalar : (Real.sqrt (d i))⁻¹ * d i * (Real.sqrt (d i))⁻¹ = 1 := by
        have hroot := Real.sqrt_ne_zero'.2 (hd i)
        field_simp
        rw [Real.sq_sqrt (le_of_lt (hd i))]
      exact_mod_cast hscalar
    have hnorm : star P * A * P = 1 := by
      dsimp [P]
      rw [star_mul]
      calc
        (star S * star U) * A * (U * S) = star S * (star U * A * U) * S := by
          simp only [Matrix.mul_assoc]
        _ = star S * Matrix.diagonal (fun i ↦ (d i : ℂ)) * S := by rw [hdiag]
        _ = 1 := hDS
    have hdetU : U.det ≠ 0 := by
      have hu : U * star U = 1 := by
        simp [U]
      have hu' := congrArg Matrix.det hu
      have hu'' : U.det * (star U).det = 1 := by
        simpa only [Matrix.det_mul, Matrix.det_one] using hu'
      intro hz
      rw [hz] at hu''
      simp at hu''
    have hdetS : S.det ≠ 0 := by
      rw [Matrix.det_diagonal]
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact hs i
    have hdetP : P.det ≠ 0 := by
      change (U * S).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero hdetU hdetS
    refine ⟨P, hnorm, ?_⟩
    exact (Matrix.isUnit_iff_isUnit_det P).2 (isUnit_iff_ne_zero.mpr hdetP)

  have c3RefinedTrace_exists_simultaneous_normalization {n : ℕ}
      (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hB : B.PosDef) :
      ∃ (J : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ),
        J.transpose * A * J.map star = 1 ∧
        J.transpose * B * J.map star = Matrix.diagonal (fun i ↦ (d i : ℂ)) ∧
        (∀ i, 0 < d i) ∧ IsUnit J := by
    classical
    obtain ⟨P, hPnorm, hPunit⟩ := c3RefinedTrace_exists_posDef_congruence_identity A hA
    let J₀ : Matrix (Fin n) (Fin n) ℂ := P.map star
    have hJ₀transpose : J₀.transpose = star P := by
      ext i j
      simp [J₀, Matrix.transpose, Matrix.map_apply]
    have hJ₀bar : J₀.map star = P := by
      ext i j
      simp [J₀, Matrix.map_apply]
    have hJ₀norm : J₀.transpose * A * J₀.map star = 1 := by
      rw [hJ₀transpose, hJ₀bar]
      exact hPnorm
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPunit
    have hJ₀det : IsUnit J₀.det := by
      have hmapdet : J₀.det = star P.det := by
        dsimp [J₀]
        simpa using ((starRingEnd ℂ).map_det P).symm
      rw [hmapdet]
      exact IsUnit.map (starRingEnd ℂ) hPdet
    have hJ₀unit : IsUnit J₀ := (Matrix.isUnit_iff_isUnit_det J₀).mpr hJ₀det
    let B₀ : Matrix (Fin n) (Fin n) ℂ := J₀.transpose * B * J₀.map star
    have hB₀pos : B₀.PosDef := by
      change (J₀.transpose * B * J₀.map star).PosDef
      rw [hJ₀transpose, hJ₀bar]
      exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hPunit).2 hB
    let hb := hB₀pos.isHermitian
    let V : Matrix (Fin n) (Fin n) ℂ := hb.eigenvectorUnitary
    let d : Fin n → ℝ := hb.eigenvalues
    have hdiag : star V * B₀ * V = Matrix.diagonal (fun i ↦ (d i : ℂ)) := by
      have h' := hb.conjStarAlgAut_star_eigenvectorUnitary
      rw [Unitary.conjStarAlgAut_star_apply] at h'
      simpa [hb, V, d, Function.comp_def] using h'
    have hdpos (i : Fin n) : 0 < d i := hB₀pos.eigenvalues_pos i
    let J : Matrix (Fin n) (Fin n) ℂ := J₀ * V.map star
    have hJtranspose : J.transpose = star V * J₀.transpose := by
      dsimp [J]
      rw [Matrix.transpose_mul]
      congr 1
    have hJbar : J.map star = J₀.map star * V := by
      dsimp [J]
      rw [Matrix.map_mul]
      congr 1
      ext i j
      simp [Matrix.map_apply]
    have hnorm : J.transpose * A * J.map star = 1 := by
      rw [hJtranspose, hJbar]
      calc
        star V * J₀.transpose * A * (J₀.map star * V) =
            star V * (J₀.transpose * A * J₀.map star) * V := by
              simp only [Matrix.mul_assoc]
        _ = star V * 1 * V := by rw [hJ₀norm]
        _ = 1 := by
          rw [Matrix.mul_one]
          exact Unitary.coe_star_mul_self hb.eigenvectorUnitary
    have hdiagJ : J.transpose * B * J.map star = Matrix.diagonal (fun i ↦ (d i : ℂ)) := by
      rw [hJtranspose, hJbar]
      calc
        star V * J₀.transpose * B * (J₀.map star * V) = star V * B₀ * V := by
          simp [B₀, Matrix.mul_assoc]
        _ = Matrix.diagonal (fun i ↦ (d i : ℂ)) := hdiag
    have hVunit : IsUnit V := by
      apply isUnit_iff_exists_inv.mpr
      exact ⟨star V, by exact Unitary.coe_mul_star_self hb.eigenvectorUnitary⟩
    have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hVunit
    have hVbarDet : IsUnit (V.map star).det := by
      have hmapdet : star V.det = (V.map star).det := by
        simpa using (starRingEnd ℂ).map_det V
      rw [← hmapdet]
      exact IsUnit.map (starRingEnd ℂ) hVdet
    have hVbarUnit : IsUnit (V.map star) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hVbarDet
    have hJunit : IsUnit J := by
      dsimp [J]
      exact hJ₀unit.mul hVbarUnit
    exact ⟨J, d, hnorm, hdiagJ, hdpos, hJunit⟩

  have c3Refined_extDeriv_zero_apply
      {n : ℕ} {α : EuclideanSpace ℂ (Fin n) →
        EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
      {z : EuclideanSpace ℂ (Fin n)} (hα : ContDiffAt ℝ 1 α z)
      (hclosed : extDeriv α z = 0) (u v w : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun y ↦ α y ![v, w]) z u -
        fderiv ℝ (fun y ↦ α y ![u, w]) z v +
        fderiv ℝ (fun y ↦ α y ![u, v]) z w = 0 := by
    have hdiff := hα.differentiableAt (by norm_num)
    have heval := congrArg (fun β : EuclideanSpace ℂ (Fin n) [⋀^Fin 3]→L[ℝ] ℝ => β ![u, v, w]) hclosed
    rw [extDeriv_apply hdiff ![u, v, w]] at heval
    simp [Fin.sum_univ_succ] at heval
    have hr₁ : Fin.removeNth (1 : Fin 3) ![u, v, w] = ![u, w] := by
      ext i
      fin_cases i <;> rfl
    have hr₂ : Fin.removeNth (2 : Fin 3) ![u, v, w] = ![u, v] := by
      ext i
      fin_cases i <;> rfl
    rw [hr₁, hr₂] at heval
    linarith

  have c3Refined_fderiv_coeffMatrix_entry
      {n : ℕ} {α : EuclideanSpace ℂ (Fin n) →
        EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
      {z : EuclideanSpace ℂ (Fin n)} (hα : ContDiffAt ℝ 1 α z) (j k : Fin n) :
      fderiv ℝ (fun y ↦ (α y).coeffMatrix j k) z =
        (1 / 2 : ℝ) •
          (Complex.ofRealCLM.comp
              (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
                Complex.I • EuclideanSpace.single k 1]) z) -
            Complex.I • Complex.ofRealCLM.comp
              (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
                EuclideanSpace.single k 1]) z)) := by
    have hdiff : DifferentiableAt ℝ α z := hα.differentiableAt (by norm_num)
    have hA : DifferentiableAt ℝ
        (fun y ↦ α y ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]) z :=
      hdiff.continuousAlternatingMap_apply_const _
    have hB : DifferentiableAt ℝ
        (fun y ↦ α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]) z :=
      hdiff.continuousAlternatingMap_apply_const _
    have hAcast : (fun y ↦ ((α y ![EuclideanSpace.single j 1,
        Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ)) =
        Complex.ofRealCLM ∘ (fun y ↦ α y ![EuclideanSpace.single j 1,
          Complex.I • EuclideanSpace.single k 1]) := rfl
    have hBcast : (fun y ↦ ((α y ![EuclideanSpace.single j 1,
        EuclideanSpace.single k 1] : ℝ) : ℂ)) =
        Complex.ofRealCLM ∘ (fun y ↦ α y ![EuclideanSpace.single j 1,
          EuclideanSpace.single k 1]) := rfl
    change fderiv ℝ (fun y ↦
      (((α y ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
        Complex.I * (α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2) z = _
    have hAcomplex : DifferentiableAt ℝ
        (fun y ↦ ((α y ![EuclideanSpace.single j 1,
          Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ)) z := by
      rw [hAcast]
      exact Complex.ofRealCLM.differentiableAt.comp z hA
    have hBcomplex : DifferentiableAt ℝ
        (fun y ↦ ((α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ) : ℂ)) z := by
      rw [hBcast]
      exact Complex.ofRealCLM.differentiableAt.comp z hB
    have hAderiv : fderiv ℝ
        (fun y ↦ ((α y ![EuclideanSpace.single j 1,
          Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ)) z =
        Complex.ofRealCLM.comp
        (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
            Complex.I • EuclideanSpace.single k 1]) z) := by
      rw [hAcast]
      exact (Complex.ofRealCLM.hasFDerivAt.comp z hA.hasFDerivAt).fderiv
    have hBderiv : fderiv ℝ
        (fun y ↦ ((α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ) : ℂ)) z =
        Complex.ofRealCLM.comp
        (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
            EuclideanSpace.single k 1]) z) := by
      rw [hBcast]
      exact (Complex.ofRealCLM.hasFDerivAt.comp z hB.hasFDerivAt).fderiv
    have hnum : DifferentiableAt ℝ
        (fun y ↦ ((α y ![EuclideanSpace.single j 1,
          Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
            Complex.I * (α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) z :=
      hAcomplex.sub (hBcomplex.const_mul Complex.I)
    rw [show (fun y ↦
        (((α y ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
          Complex.I * (α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2) =
        (fun y ↦ (2 : ℂ)⁻¹ *
          (((α y ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
            Complex.I * (α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ))) by
      funext y
      simp only [div_eq_mul_inv]
      ring]
    rw [fderiv_const_mul hnum (2 : ℂ)⁻¹]
    rw [fderiv_fun_sub hAcomplex (hBcomplex.const_mul Complex.I)]
    rw [fderiv_const_mul hBcomplex Complex.I, hAderiv, hBderiv]
    have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [hhalf]
    rw [show ((2 : ℂ)⁻¹) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) by norm_num]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) ((2 : ℝ)⁻¹)
      (Complex.ofRealCLM.comp
        (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
          Complex.I • EuclideanSpace.single k 1]) z) -
        Complex.I • Complex.ofRealCLM.comp
          (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
            EuclideanSpace.single k 1]) z))).symm

  have c3Refined_closed_oneOne_partial_identity
      {n : ℕ} {α : EuclideanSpace ℂ (Fin n) →
        EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
      {z : EuclideanSpace ℂ (Fin n)} (hα : ContDiffAt ℝ 1 α z)
      (hclosed : extDeriv α z = 0)
      (hone : ∀ᶠ y in nhds z, (α y).IsOneOne)
      (u v w : EuclideanSpace ℂ (Fin n)) :
      let D := fun (d a b : EuclideanSpace ℂ (Fin n)) ↦
        fderiv ℝ (fun y ↦ α y ![a, b]) z d
      ((D u v (Complex.I • w) - D v u (Complex.I • w) : ℝ) -
        Complex.I * (D u v w - D v u w : ℝ) -
        Complex.I * (D (Complex.I • u) v (Complex.I • w) -
          D (Complex.I • v) u (Complex.I • w) : ℝ) -
        (D (Complex.I • u) v w - D (Complex.I • v) u w : ℝ)) = 0 := by
    dsimp only
    let D := fun (d a b : EuclideanSpace ℂ (Fin n)) ↦
      fderiv ℝ (fun y ↦ α y ![a, b]) z d
    have hA := c3Refined_extDeriv_zero_apply
      hα hclosed u v (Complex.I • w)
    have hB := c3Refined_extDeriv_zero_apply
      hα hclosed u v w
    have hC := c3Refined_extDeriv_zero_apply
      hα hclosed (Complex.I • u) (Complex.I • v) w
    have hE := c3Refined_extDeriv_zero_apply
      hα hclosed (Complex.I • u) (Complex.I • v) (Complex.I • w)
    have hJ (d a b : EuclideanSpace ℂ (Fin n)) :
        D d (Complex.I • a) (Complex.I • b) = D d a b := by
      have heq : (fun y ↦ α y ![Complex.I • a, Complex.I • b]) =ᶠ[nhds z]
          fun y ↦ α y ![a, b] := by
        filter_upwards [hone] with y hy
        exact hy a b
      exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L d) heq.fderiv_eq
    have hSwap (d a b : EuclideanSpace ℂ (Fin n)) :
        D d (Complex.I • a) b = -D d a (Complex.I • b) := by
      have heq : (fun y ↦ α y ![Complex.I • a, b]) =ᶠ[nhds z]
          fun y ↦ -(α y ![a, Complex.I • b]) := by
        filter_upwards [hone] with y hy
        have h := hy (Complex.I • a) b
        have hI : Complex.I • (Complex.I • a) = -a := by simp [smul_smul]
        rw [hI] at h
        have hNeg : α y ![-a, Complex.I • b] = -α y ![a, Complex.I • b] := by
          have hm := (α y).map_smul_univ ![(-1 : ℝ), 1] ![a, Complex.I • b]
          have ht : (fun i : Fin 2 ↦ ![(-1 : ℝ), 1] i • ![a, Complex.I • b] i) =
              ![-a, Complex.I • b] := by
            ext i
            fin_cases i <;> simp
          rw [ht] at hm
          simpa using hm
        rw [hNeg] at h
        linarith
      have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L d) heq.fderiv_eq
      simpa [D, fderiv_neg] using h
    have hA' : D u v (Complex.I • w) - D v u (Complex.I • w) =
        -D (Complex.I • w) u v := by linarith [hA]
    have hB' : D u v w - D v u w = -D w u v := by linarith [hB]
    have hC' : D (Complex.I • u) v (Complex.I • w) -
        D (Complex.I • v) u (Complex.I • w) = D w u v := by
      have h := hC
      change D (Complex.I • u) (Complex.I • v) w -
        D (Complex.I • v) (Complex.I • u) w + D w (Complex.I • u) (Complex.I • v) = 0 at h
      rw [hSwap (Complex.I • u) v w, hSwap (Complex.I • v) u w, hJ w u v] at h
      linarith
    have hE' : D (Complex.I • u) v w - D (Complex.I • v) u w =
        -D (Complex.I • w) u v := by
      have h := hE
      change D (Complex.I • u) (Complex.I • v) (Complex.I • w) -
        D (Complex.I • v) (Complex.I • u) (Complex.I • w) +
          D (Complex.I • w) (Complex.I • u) (Complex.I • v) = 0 at h
      rw [hJ (Complex.I • u) v w, hJ (Complex.I • v) u w,
        hJ (Complex.I • w) u v] at h
      linarith
    rw [hA', hB', hC', hE']
    push_cast
    ring

  have c3Refined_chartPartialZ_coeffMatrix_symm
      {n : ℕ} {α : EuclideanSpace ℂ (Fin n) →
        EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
      {z : EuclideanSpace ℂ (Fin n)} (hα : ContDiffAt ℝ 1 α z)
      (hclosed : extDeriv α z = 0) (hone : ∀ᶠ y in nhds z, (α y).IsOneOne)
      (i j k : Fin n) :
      c3PartialZ (fun y ↦ (α y).coeffMatrix j k) z i =
        c3PartialZ (fun y ↦ (α y).coeffMatrix i k) z j := by
    let D := fun (d a b : EuclideanSpace ℂ (Fin n)) ↦
      fderiv ℝ (fun y ↦ α y ![a, b]) z d
    have h := c3Refined_closed_oneOne_partial_identity hα hclosed hone
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
    unfold c3PartialZ
    rw [c3Refined_fderiv_coeffMatrix_entry hα j k,
      c3Refined_fderiv_coeffMatrix_entry hα i k]
    simp only [_root_.sub_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    push_cast at h ⊢
    simp only [Complex.ofRealCLM_apply, div_eq_mul_inv] at h ⊢
    norm_num [one_div] at h ⊢
    ring_nf at h ⊢
    simp [Complex.I_sq] at h ⊢
    linear_combination h / 2

  have c3Refined_chartRep_isOneOne (ω₀ : KahlerForm n M) (x : M)
      {z : EuclideanSpace ℂ (Fin n)}
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      (ω₀.toFormField.chartRep x z).IsOneOne := by
    let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z
    have hyx : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source :=
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_target hz
    have hyyℝ : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
      mem_extChartAt_source y
    have hyxℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
      simpa only [← extChartAt_real_eq] using hyx
    have hyyℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
      simpa only [← extChartAt_real_eq] using hyyℝ
    let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
    let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
    have hBA : ∀ v, B (A v) = v := by
      intro v
      dsimp [A, B]
      calc
        tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
            (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y v) =
            tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v :=
          tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (w := x) (x := y) (y := x) (z := y) (v := v)
            ⟨⟨hyxℂ, hyyℂ⟩, hyxℂ⟩
        _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (x := x) (z := y) (v := v) hyxℂ
    have hAB : ∀ v, A (B v) = v := by
      intro v
      dsimp [A, B]
      calc
        tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
            (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y v) =
            tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v :=
          tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (w := y) (x := x) (y := y) (z := y) (v := v)
            ⟨⟨hyyℂ, hyxℂ⟩, hyyℂ⟩
        _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (x := y) (z := y) (v := v) (by simp)
    let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
      { toLinearEquiv :=
          { toFun := A
            invFun := B
            left_inv := hBA
            right_inv := hAB
            map_add' := A.map_add
            map_smul' := A.map_smul }
        continuous_toFun := A.continuous
        continuous_invFun := B.continuous }
    have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
        (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
      tangentCoordChange_real_eq ⟨hyx, hyyℝ⟩
    have hchart : ω₀.toFormField.chartRep x z =
        (ω₀.toFormField y).compContinuousLinearMap (A.restrictScalars ℝ) := by
      change (ω₀.toFormField y).compContinuousLinearMap
        (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
      rw [hAreal]
    rw [hchart]
    have hpos := (ω₀.isPositive y).compContinuousLinearMap AEquiv
    have hAeq :
        (AEquiv : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) = A := rfl
    rw [hAeq] at hpos
    exact hpos.1

  have c3Refined_kahler_chart_metric_symmetry (ω₀ : KahlerForm n M) (x : M)
      {z : EuclideanSpace ℂ (Fin n)}
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (i j k : Fin n) :
      c3PartialZ (fun w ↦ ω₀.metricInChart x w j k) z i =
        c3PartialZ (fun w ↦ ω₀.metricInChart x w i k) z j := by
    let α := ω₀.toFormField.chartRep x
    have hαtop : ContDiffAt ℝ ∞ α z :=
      (ω₀.isSmooth x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)
    have hle : (1 : ℕ∞ω) ≤ ∞ := by
      change ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    have hα := hαtop.of_le hle
    have hclosed : extDeriv α z = 0 := by
      have hclosed0 : ω₀.toFormField.extDeriv = 0 := ω₀.isClosed
      have hzero := congrArg (fun β ↦ β.chartRep x z) hclosed0
      rw [FormField.chartRep_extDeriv ω₀.isSmooth x hz, FormField.chartRep_zero] at hzero
      exact hzero
    have hone : ∀ᶠ y in nhds z, (α y).IsOneOne := by
      filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
      exact c3Refined_chartRep_isOneOne ω₀ x hy
    have hsymm := c3Refined_chartPartialZ_coeffMatrix_symm hα hclosed hone i j k
    simpa [α, metricInChart] using hsymm

  have c3Refined_exists_symmetric_normal_jet {n : ℕ}
      (g gInv : Matrix (Fin n) (Fin n) ℂ) (hInv : g.transpose * gInv = 1)
      (D : Fin n → Fin n → Fin n → ℂ)
      (hD : ∀ i k j, D i k j = D k i j) :
      ∃ C : Fin n → Fin n → Fin n → ℂ,
        (∀ a i k, C a i k = C a k i) ∧
        (∀ i k j, D i k j + ∑ a, g a j * C a i k = 0) := by
    classical
    let C : Fin n → Fin n → Fin n → ℂ := fun a i k ↦ -∑ l, gInv a l * D i k l
    refine ⟨C, ?_, ?_⟩
    · intro a i k
      simp [C, hD i k]
    · intro i k j
      let d : Fin n → ℂ := fun l ↦ D i k l
      have hC : (fun a ↦ C a i k) = -(gInv.mulVec d) := by
        funext a
        simp [C, d, Matrix.mulVec, dotProduct]
      have hInvD : g.transpose.mulVec (gInv.mulVec d) = d := by
        calc
          g.transpose.mulVec (gInv.mulVec d) = (g.transpose * gInv).mulVec d := by
            rw [← Matrix.mulVec_mulVec]
          _ = (1 : Matrix (Fin n) (Fin n) ℂ).mulVec d := by rw [hInv]
          _ = d := Matrix.one_mulVec d
      have hvec : g.transpose.mulVec (fun a ↦ C a i k) = -d := by
        rw [hC, Matrix.mulVec_neg, hInvD]
      have hcoord := congrFun hvec j
      have hsum : (∑ a, g a j * C a i k) = -D i k j := by
        simpa [Matrix.mulVec, Matrix.transpose_apply, dotProduct, d] using hcoord
      rw [hsum]
      exact add_neg_cancel _

  let c3RefinedContinuousBilinearJet {n : ℕ}
      (C : Fin n → Fin n → Fin n → ℂ) :
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) := by
    classical
    let B : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
      { toFun := fun u =>
          { toFun := fun v => WithLp.toLp 2 (fun a => ∑ p : Fin n, ∑ j : Fin n,
              C a p j * u p * v j)
            map_add' := by
              intro v w
              ext a
              change (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * (v j + w j)) =
                (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j) +
                  ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * w j
              simp_rw [mul_add]
              simp only [Finset.sum_add_distrib]
            map_smul' := by
              intro z v
              ext a
              change (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * (z * v j)) =
                z * ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j
              simp_rw [mul_assoc]
              simp_rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p hp
              apply Finset.sum_congr rfl
              intro j hj
              ring }
        map_add' := by
          intro u v
          ext w a
          change (∑ p : Fin n, ∑ j : Fin n, C a p j * (u p + v p) * w j) =
            (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * w j) +
              ∑ p : Fin n, ∑ j : Fin n, C a p j * v p * w j
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        map_smul' := by
          intro z u
          ext v a
          change (∑ p : Fin n, ∑ j : Fin n, C a p j * (z * u p) * v j) =
            z * ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j
          simp_rw [mul_assoc]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro j hj
          ring }
    let B1 : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      { toFun := fun u => LinearMap.toContinuousLinearMap (B u)
        map_add' := by
          intro u v
          ext w a
          change (∑ p : Fin n, ∑ j : Fin n, C a p j * (u p + v p) * w j) =
            (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * w j) +
              ∑ p : Fin n, ∑ j : Fin n, C a p j * v p * w j
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        map_smul' := by
          intro z u
          ext v a
          change (∑ p : Fin n, ∑ j : Fin n, C a p j * (z * u p) * v j) =
            z * ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j
          simp_rw [mul_assoc]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro j hj
          ring }
    exact LinearMap.toContinuousLinearMap B1

  have c3RefinedContinuousBilinearJet_apply {n : ℕ}
      (C : Fin n → Fin n → Fin n → ℂ) (u v : EuclideanSpace ℂ (Fin n)) :
      c3RefinedContinuousBilinearJet C u v = WithLp.toLp 2 (fun a =>
        ∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j) := rfl

  have c3Refined_exists_symmetric_bilinear_jet {n : ℕ}
      (C : Fin n → Fin n → Fin n → ℂ)
      (hC : ∀ a p j, C a p j = C a j p) :
      ∃ Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
          EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        (∀ u v, Q u v = Q v u) ∧
        ∀ p j a, Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) a = C a p j := by
    refine ⟨c3RefinedContinuousBilinearJet C, ?_, ?_⟩
    · intro u v
      ext a
      rw [c3RefinedContinuousBilinearJet_apply, c3RefinedContinuousBilinearJet_apply]
      change (∑ p : Fin n, ∑ j : Fin n, C a p j * u p * v j) =
        ∑ p : Fin n, ∑ j : Fin n, C a p j * v p * u j
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      rw [hC a p j]
      ring
    · intro p j a
      rw [c3RefinedContinuousBilinearJet_apply]
      simp

  have c3Refined_exists_quadratic_pullback_jet_cancellation {n : ℕ}
      (G J : Matrix (Fin n) (Fin n) ℂ) (D : Fin n → Fin n → Fin n → ℂ)
      (hNorm : J.transpose * G * J.map star = 1)
      (hD : ∀ p a b, D p a b = D a p b) :
      ∃ Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
          EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        (∀ u v, Q u v = Q v u) ∧
        ∀ p j k,
          (∑ a, ∑ b,
            Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) a *
              G a b * star (J b k)) +
            ∑ a, ∑ b, ∑ c,
              J a j * star (J b k) * J c p * D c a b = 0 := by
    classical
    let B := G * J.map star
    have hBJ : B.transpose * J = 1 := by
      have h : J.transpose * B = 1 := by simpa [B, Matrix.mul_assoc] using hNorm
      have ht := congrArg Matrix.transpose h
      simpa [B, Matrix.transpose_mul] using ht
    let T : Fin n → Fin n → Fin n → ℂ := fun p j k ↦
      ∑ c, ∑ a, ∑ b, J c p * J a j * star (J b k) * D c a b
    have hTsym (p j k : Fin n) : T p j k = T j p k := by
      dsimp [T]
      calc
        (∑ c, ∑ a, ∑ b, J c p * J a j * star (J b k) * D c a b) =
            ∑ a, ∑ c, ∑ b, J c p * J a j * star (J b k) * D c a b :=
          Finset.sum_comm
        _ = ∑ c, ∑ a, ∑ b, J c j * J a p * star (J b k) * D c a b := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          rw [hD]
          ring
    obtain ⟨C, hC, hsolve⟩ := c3Refined_exists_symmetric_normal_jet B J hBJ T hTsym
    obtain ⟨Q, hQ, hQcoeff⟩ := c3Refined_exists_symmetric_bilinear_jet C hC
    refine ⟨Q, hQ, ?_⟩
    intro p j k
    have hTval : T p j k =
        ∑ a, ∑ b, ∑ c, J a j * star (J b k) * J c p * D c a b := by
      dsimp [T]
      calc
        (∑ c, ∑ a, ∑ b, J c p * J a j * star (J b k) * D c a b) =
            ∑ a, ∑ c, ∑ b, J c p * J a j * star (J b k) * D c a b :=
          Finset.sum_comm
        _ = ∑ a, ∑ b, ∑ c, J c p * J a j * star (J b k) * D c a b := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro c hc
          simp only [Complex.star_def]
          ring
    have hBval : (∑ a, B a k * C a p j) =
        ∑ a, ∑ b, Q (EuclideanSpace.single p 1)
          (EuclideanSpace.single j 1) a * G a b * star (J b k) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hQcoeff]
      change (G * J.map star) a k * C a p j = _
      simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      simp only [Complex.star_def]
      ring
    have hs := hsolve p j k
    rw [hTval, hBval] at hs
    exact (add_comm _ _).trans hs

  let c3RefinedQuadraticChartMap {n : ℕ}
      (z₀ : EuclideanSpace ℂ (Fin n))
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
      EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
    fun v ↦ z₀ + A v + (1 / 2 : ℂ) • Q v v

  have c3RefinedQuadraticChartMap_fderiv {n : ℕ}
      (z₀ : EuclideanSpace ℂ (Fin n))
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (hQ : ∀ u v, Q u v = Q v u)
      (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℂ (c3RefinedQuadraticChartMap z₀ A Q) v = A + Q v := by
    have hquad := Q.hasFDerivAt_of_bilinear
      (hasFDerivAt_id v) (hasFDerivAt_id v)
    have hdf : HasFDerivAt (c3RefinedQuadraticChartMap z₀ A Q)
        (0 + A + (1 / 2 : ℂ) •
          (Q.precompR (EuclideanSpace ℂ (Fin n)) v
            (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) +
          Q.precompL (EuclideanSpace ℂ (Fin n))
            (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) v)) v := by
      convert (((hasFDerivAt_const z₀ v).add A.hasFDerivAt).add
        (hquad.const_smul (1 / 2 : ℂ))) using 1
      all_goals rfl
    rw [hdf.fderiv]
    ext w
    simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply]
    simp [hQ]
    ring

  have c3RefinedQuadraticChartMap_contDiff {n : ℕ}
      (z₀ : EuclideanSpace ℂ (Fin n))
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
      ContDiff ℂ ∞ (c3RefinedQuadraticChartMap z₀ A Q) := by
    have hQdiag : ContDiff ℂ ∞ (fun v : EuclideanSpace ℂ (Fin n) ↦ Q v v) := by
      let Qr := Q.bilinearRestrictScalars ℂ
      have hQr : ContDiff ℂ ∞
          (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) ↦ Qr p.1 p.2) :=
        Qr.isBoundedBilinearMap.contDiff
      exact hQr.comp (contDiff_id.prodMk contDiff_id)
    have hlinear : ContDiff ℂ ∞
        (fun v : EuclideanSpace ℂ (Fin n) ↦ z₀ + A v) := contDiff_const.add A.contDiff
    have hcoef : ContDiff ℂ ∞ (fun _ : EuclideanSpace ℂ (Fin n) ↦ (1 / 2 : ℂ)) :=
      contDiff_const
    have hquad : ContDiff ℂ ∞ (fun v ↦ (1 / 2 : ℂ) • Q v v) := hcoef.smul hQdiag
    change ContDiff ℂ ∞ (fun v ↦ (z₀ + A v) + (1 / 2 : ℂ) • Q v v)
    exact hlinear.add hquad

  have c3RefinedQuadraticChartMap_differentiable {n : ℕ}
      (z₀ : EuclideanSpace ℂ (Fin n))
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
      Differentiable ℂ (c3RefinedQuadraticChartMap z₀ A Q) := by
    have hquad : Differentiable ℂ (fun v : EuclideanSpace ℂ (Fin n) ↦ Q v v) :=
      Q.differentiable.clm_apply differentiable_id
    have hcoef : Differentiable ℂ (fun _ : EuclideanSpace ℂ (Fin n) ↦ (1 / 2 : ℂ)) :=
      differentiable_const _
    have hlinear : Differentiable ℂ (fun v : EuclideanSpace ℂ (Fin n) ↦ z₀ + A v) :=
      (differentiable_const z₀).add A.differentiable
    have hquad' : Differentiable ℂ
        (fun v : EuclideanSpace ℂ (Fin n) ↦ (1 / 2 : ℂ) • Q v v) := hcoef.smul hquad
    change Differentiable ℂ (fun v ↦ (z₀ + A v) + (1 / 2 : ℂ) • Q v v)
    exact hlinear.add hquad'

  have c3Refined_exists_quadratic_local_inverse_kernel {n : ℕ}
      (z₀ : EuclideanSpace ℂ (Fin n))
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (hQ : ∀ u v, Q u v = Q v u)
      (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U) (hz₀ : z₀ ∈ U)
      (hJ : IsUnit (EuclideanSpace.clmMatrix A).det) :
      ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ 0 ∈ V ∧
        (∀ v ∈ V, c3RefinedQuadraticChartMap z₀ A Q v ∈ U) ∧
        ContDiffOn ℂ ∞ (c3RefinedQuadraticChartMap z₀ A Q) V ∧
        (∀ v ∈ V, IsUnit
          (EuclideanSpace.clmMatrix
            (fderiv ℂ (c3RefinedQuadraticChartMap z₀ A Q) v)).det) := by
    let f := c3RefinedQuadraticChartMap z₀ A Q
    have hf : ContDiff ℂ ∞ f := c3RefinedQuadraticChartMap_contDiff z₀ A Q
    have hf0 : f 0 = z₀ := by simp [f, c3RefinedQuadraticChartMap]
    have hdetCont : Continuous (fun v : EuclideanSpace ℂ (Fin n) ↦
        (EuclideanSpace.clmMatrix (fderiv ℂ f v)).det) := by
      have hentry (i j : Fin n) : Continuous (fun v : EuclideanSpace ℂ (Fin n) ↦
          EuclideanSpace.clmMatrix (fderiv ℂ f v) i j) := by
        rw [show (fun v ↦ EuclideanSpace.clmMatrix (fderiv ℂ f v) i j) =
            fun v ↦ EuclideanSpace.clmMatrix (A + Q v) i j by
          funext v
          rw [show f = c3RefinedQuadraticChartMap z₀ A Q by rfl]
          exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) ↦
            EuclideanSpace.clmMatrix L i j) (c3RefinedQuadraticChartMap_fderiv z₀ A Q hQ v)]
        change Continuous (fun v ↦ ((A + Q v) (EuclideanSpace.single j 1)).ofLp i)
        let ev : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) →L[ℂ]
            EuclideanSpace ℂ (Fin n) :=
          ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin n)) (EuclideanSpace.single j 1)
        have hq : Continuous (fun v ↦ (Q v) (EuclideanSpace.single j 1)) :=
          ev.continuous.comp Q.continuous
        have hcoord : Continuous (fun y : EuclideanSpace ℂ (Fin n) ↦ y.ofLp i) := by
          change Continuous (fun y : PiLp 2 (fun _ : Fin n ↦ ℂ) ↦ y i)
          exact PiLp.continuous_apply (p := 2) (β := fun _ : Fin n ↦ ℂ) i
        have hq' : Continuous (fun v ↦ ((Q v) (EuclideanSpace.single j 1)).ofLp i) :=
          hcoord.comp hq
        exact continuous_const.add hq'
      have hmat : Continuous (fun v : EuclideanSpace ℂ (Fin n) ↦
          EuclideanSpace.clmMatrix (fderiv ℂ f v)) := by
        change Continuous (fun v i j ↦ EuclideanSpace.clmMatrix (fderiv ℂ f v) i j)
        exact continuous_pi_iff.mpr (fun i ↦ continuous_pi_iff.mpr (fun j ↦ hentry i j))
      fun_prop
    let V := f ⁻¹' U ∩ {v | (EuclideanSpace.clmMatrix (fderiv ℂ f v)).det ≠ 0}
    have hVopen : IsOpen V := by
      dsimp [V]
      have hne : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
      exact (hU.preimage hf.continuous).inter (hne.preimage hdetCont)
    have hdet0 : (EuclideanSpace.clmMatrix (fderiv ℂ f 0)).det ≠ 0 := by
      rw [c3RefinedQuadraticChartMap_fderiv z₀ A Q hQ 0]
      simpa using hJ.ne_zero
    have hzero : 0 ∈ V := by
      simp only [V, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
      exact ⟨by simpa [f, hf0] using hz₀, hdet0⟩
    refine ⟨V, hVopen, hzero, ?_, ?_, ?_⟩
    · intro v hv
      exact hv.1
    · exact hf.contDiffOn
    · intro v hv
      exact isUnit_iff_ne_zero.mpr hv.2

  have c3PartialZ_mul {n : ℕ}
      {u v : EuclideanSpace ℂ (Fin n) → ℂ} {z : EuclideanSpace ℂ (Fin n)}
      (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) (j : Fin n) :
      c3PartialZ (fun w ↦ u w * v w) z j =
        c3PartialZ u z j * v z + u z * c3PartialZ v z j := by
    unfold c3PartialZ
    rw [fderiv_fun_mul hu hv]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring

  have c3PartialZ_star_zero {n : ℕ}
      (f : EuclideanSpace ℂ (Fin n) → ℂ)
      (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
      (hf : DifferentiableAt ℂ f z) :
      c3PartialZ (fun w ↦ star (f w)) z p = 0 := by
    have hreal : HasFDerivAt f ((fderiv ℂ f z).restrictScalars ℝ) z :=
      hf.hasFDerivAt.restrictScalars ℝ
    have hconj : HasFDerivAt (Complex.conjCLE : ℂ → ℂ)
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) (f z) :=
      Complex.conjCLE.hasFDerivAt (x := f z)
    have hcomp := hconj.comp z hreal
    have hstar : fderiv ℝ (fun w ↦ star (f w)) z =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ f z).restrictScalars ℝ) := by
      simpa [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using hcomp.fderiv
    have hI : ((fderiv ℂ f z).restrictScalars ℝ)
        (Complex.I • EuclideanSpace.single p (1 : ℂ)) =
        Complex.I * ((fderiv ℂ f z).restrictScalars ℝ)
          (EuclideanSpace.single p (1 : ℂ)) := by
      change fderiv ℂ f z (Complex.I • EuclideanSpace.single p (1 : ℂ)) = _
      exact (fderiv ℂ f z).map_smul Complex.I _
    unfold c3PartialZ
    rw [hstar]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hI]
    simp
    rw [← mul_assoc, Complex.I_mul_I]
    ring

  have c3PartialZ_directional_smul {n : ℕ}
      (D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ) (c : ℂ)
      (v : EuclideanSpace ℂ (Fin n)) :
      D (c • v) - Complex.I * D (Complex.I • (c • v)) =
        c * (D v - Complex.I * D (Complex.I • v)) := by
    have hc₁ : c • v = c.re • v + c.im • (Complex.I • v) := by
      calc
        c • v = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) • v :=
          congrArg (fun z : ℂ => z • v) (Complex.re_add_im c).symm
        _ = c.re • v + c.im • (Complex.I • v) := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c.re,
            RCLike.real_smul_eq_coe_smul (K := ℂ) c.im]
          rw [add_smul, smul_smul]
          rfl
    have hc₂ : Complex.I • (c • v) = -c.im • v + c.re • (Complex.I • v) := by
      have hscalar : Complex.I * c = ((-c.im : ℝ) : ℂ) + (c.re : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      calc
        Complex.I • (c • v) = (Complex.I * c) • v := by rw [smul_smul]
        _ = (((-c.im : ℝ) : ℂ) + (c.re : ℂ) * Complex.I) • v := by rw [hscalar]
        _ = -c.im • v + c.re • (Complex.I • v) := by
          rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (-c.im),
            RCLike.real_smul_eq_coe_smul (K := ℂ) c.re]
          rw [add_smul, smul_smul]
          rfl
    rw [hc₂, hc₁]
    simp only [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    ring_nf
    simp only [Complex.I_sq]
    push_cast
    linear_combination

  have c3PartialZ_comp {n : ℕ}
      (F : EuclideanSpace ℂ (Fin n) → ℂ)
      (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
      (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
      (hF : DifferentiableAt ℝ F (ψ z)) (hψ : DifferentiableAt ℂ ψ z) :
      c3PartialZ (fun w ↦ F (ψ w)) z p =
        ∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p * c3PartialZ F (ψ z) a := by
    have hψR : HasFDerivAt ψ ((fderiv ℂ ψ z).restrictScalars ℝ) z :=
      hψ.hasFDerivAt.restrictScalars ℝ
    have hψreal : fderiv ℝ ψ z = (fderiv ℂ ψ z).restrictScalars ℝ := by
      simpa using hψ.fderiv_restrictScalars ℝ
    have hcomp := fderiv_comp (f := ψ) (g := F) (x := z) hF hψR.differentiableAt
    have hcomp' : fderiv ℝ (fun w ↦ F (ψ w)) z =
        (fderiv ℝ F (ψ z)).comp (fderiv ℝ ψ z) := by
      simpa [Function.comp_def] using hcomp
    let D := fderiv ℝ F (ψ z)
    let L := fderiv ℂ ψ z
    let A := EuclideanSpace.clmMatrix L
    let e := EuclideanSpace.single p (1 : ℂ)
    have hvec : L e = ∑ a, (A a p) • EuclideanSpace.single a (1 : ℂ) := by
      ext a
      simp [A, e, EuclideanSpace.clmMatrix, Pi.single_apply]
    unfold c3PartialZ
    rw [hcomp', hψreal]
    simp only [ContinuousLinearMap.comp_apply]
    change (D (L e) - Complex.I * D (L (Complex.I • e))) / 2 = _
    rw [map_smul, hvec]
    simp only [_root_.map_sum, Finset.smul_sum]
    have hsum :
        (∑ a, D ((A a p) • EuclideanSpace.single a (1 : ℂ))) -
          Complex.I * ∑ a, D (Complex.I • ((A a p) • EuclideanSpace.single a (1 : ℂ))) =
        ∑ a, (D ((A a p) • EuclideanSpace.single a (1 : ℂ)) -
          Complex.I * D (Complex.I • ((A a p) • EuclideanSpace.single a (1 : ℂ)))) := by
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
    rw [hsum]
    simp_rw [c3PartialZ_directional_smul]
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring

  have c3PartialZ_sum {n : ℕ}
      (F : (Fin n × Fin n) → EuclideanSpace ℂ (Fin n) → ℂ)
      (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
      (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
      c3PartialZ (fun w ↦ ∑ i, F i w) z p = ∑ i, c3PartialZ (F i) z p := by
    unfold c3PartialZ
    have hfd : fderiv ℝ (fun w ↦ ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
      simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi ↦ hF i)
    rw [hfd]
    simp only [_root_.sum_apply]
    have hsum :
        (∑ i, fderiv ℝ (F i) z (EuclideanSpace.single p 1)) -
          Complex.I * ∑ i, fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single p 1) =
        ∑ i, (fderiv ℝ (F i) z (EuclideanSpace.single p 1) -
          Complex.I * fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single p 1)) := by
      rw [Finset.mul_sum, Finset.sum_sub_distrib]
    rw [hsum]
    simp only [div_eq_mul_inv, Finset.sum_mul]

  have c3Pullback_summand {n : ℕ}
      (u v : EuclideanSpace ℂ (Fin n) → ℂ)
      (F : EuclideanSpace ℂ (Fin n) → ℂ)
      (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
      (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
      (hu : DifferentiableAt ℂ u z) (hv : DifferentiableAt ℂ v z)
      (hF : DifferentiableAt ℝ F (ψ z)) (hψ : DifferentiableAt ℂ ψ z) :
      c3PartialZ (fun w ↦ u w * F (ψ w) * star (v w)) z p =
        c3PartialZ u z p * F (ψ z) * star (v z) +
          u z * (∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p *
            c3PartialZ F (ψ z) a) * star (v z) := by
    have hψR : HasFDerivAt ψ ((fderiv ℂ ψ z).restrictScalars ℝ) z :=
      hψ.hasFDerivAt.restrictScalars ℝ
    have hcompDiff : DifferentiableAt ℝ (fun w ↦ F (ψ w)) z :=
      (hF.hasFDerivAt.comp z hψR).differentiableAt
    have huR : DifferentiableAt ℝ u z := hu.hasFDerivAt.restrictScalars ℝ |>.differentiableAt
    have hvStar : DifferentiableAt ℝ (fun w ↦ star (v w)) z := by
      have hvr : HasFDerivAt v ((fderiv ℂ v z).restrictScalars ℝ) z :=
        hv.hasFDerivAt.restrictScalars ℝ
      exact (Complex.conjCLE.hasFDerivAt (x := v z)).comp z hvr |>.differentiableAt
    have hleft : DifferentiableAt ℝ (fun w ↦ u w * F (ψ w)) z := huR.mul hcompDiff
    rw [c3PartialZ_mul hleft hvStar p,
      c3PartialZ_mul huR hcompDiff p,
      c3PartialZ_star_zero v z p hv,
      c3PartialZ_comp F ψ z p hF hψ]
    ring

  have c3Pullback_entry_derivative {n : ℕ}
      (J : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
      (z : EuclideanSpace ℂ (Fin n)) (p j k : Fin n)
      (hJ : ∀ r s, DifferentiableAt ℂ (fun w ↦ J w r s) z)
      (hG : ∀ r s, DifferentiableAt ℝ (fun w ↦ G w r s) (ψ z))
      (hψ : DifferentiableAt ℂ ψ z) :
      c3PartialZ
          (fun w ↦ ((J w).transpose * G (ψ w) * (J w).map star) j k) z p =
        ∑ r, ∑ s,
          (c3PartialZ (fun w ↦ J w r j) z p * G (ψ z) r s * star (J z s k) +
            J z r j * (∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p *
              c3PartialZ (fun w ↦ G w r s) (ψ z) a) * star (J z s k)) := by
    let T (rs : Fin n × Fin n) (w : EuclideanSpace ℂ (Fin n)) : ℂ :=
      (J w rs.1 j * star (J w rs.2 k)) * G (ψ w) rs.1 rs.2
    have hentry (w : EuclideanSpace ℂ (Fin n)) :
        ((J w).transpose * G (ψ w) * (J w).map star) j k =
          ∑ r, ∑ s, (J w r j * star (J w s k)) * G (ψ w) r s := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      ring
    have hTdiff (rs : Fin n × Fin n) : DifferentiableAt ℝ (T rs) z := by
      have hJ1 : DifferentiableAt ℝ (fun w ↦ J w rs.1 j) z :=
        (hJ rs.1 j).hasFDerivAt.restrictScalars ℝ |>.differentiableAt
      have hJ2 : DifferentiableAt ℝ (fun w ↦ star (J w rs.2 k)) z := by
        have h := (hJ rs.2 k).hasFDerivAt.restrictScalars ℝ
        have hc := Complex.conjCLE.hasFDerivAt (x := J z rs.2 k)
        simpa [Function.comp_def, Complex.star_def, Complex.conjCLE_apply] using
          (hc.comp z h).differentiableAt
      have hGcomp : DifferentiableAt ℝ (fun w ↦ G (ψ w) rs.1 rs.2) z := by
        have hψR := hψ.hasFDerivAt.restrictScalars ℝ
        exact (hG rs.1 rs.2).comp z hψR.differentiableAt
      exact (hJ1.mul hJ2).mul hGcomp
    have hfun :
        (fun w ↦ ((J w).transpose * G (ψ w) * (J w).map star) j k) =
          fun w ↦ ∑ rs : Fin n × Fin n, T rs w := by
      funext w
      rw [hentry w]
      simp only [T, Fintype.sum_prod_type]
    rw [hfun]
    rw [c3PartialZ_sum T z p hTdiff]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    simp only [T]
    have hT_eq : (fun w ↦ (J w r j * star (J w s k)) * G (ψ w) r s) =
        fun w ↦ J w r j * G (ψ w) r s * star (J w s k) := by
      funext w
      ring
    rw [hT_eq]
    exact c3Pullback_summand
      (u := fun w ↦ J w r j) (v := fun w ↦ J w s k)
      (F := fun w ↦ G w r s) ψ z p (hJ r j) (hJ s k) (hG r s) hψ

  have c3Quadratic_jacobian_entry_formula {n : ℕ}
      (z₀ : EuclideanSpace ℂ (Fin n))
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (hQ : ∀ u v, Q u v = Q v u)
      (a j : Fin n) (z : EuclideanSpace ℂ (Fin n)) :
      EuclideanSpace.clmMatrix (fderiv ℂ (c3RefinedQuadraticChartMap z₀ A Q) z) a j =
        (A (EuclideanSpace.single j 1)) a +
          ((EuclideanSpace.proj a).comp
            ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin n))
              (EuclideanSpace.single j 1)).comp Q)) z := by
    rw [c3RefinedQuadraticChartMap_fderiv z₀ A Q hQ z]
    simp [EuclideanSpace.clmMatrix, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply]

  have c3Quadratic_jacobian_entry_partial {n : ℕ}
      (z₀ : EuclideanSpace ℂ (Fin n))
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (hQ : ∀ u v, Q u v = Q v u)
      (a j p : Fin n) :
      c3PartialZ
        (fun w ↦ EuclideanSpace.clmMatrix
          (fderiv ℂ (c3RefinedQuadraticChartMap z₀ A Q) w) a j) 0 p =
        Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) a := by
    let ej := EuclideanSpace.single j (1 : ℂ)
    let L : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
      (EuclideanSpace.proj a).comp
        ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin n)) ej).comp Q)
    have hentry (w : EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace.clmMatrix (fderiv ℂ (c3RefinedQuadraticChartMap z₀ A Q) w) a j =
          (A ej) a + L w := by
      rw [c3Quadratic_jacobian_entry_formula z₀ A Q hQ a j w]
    have hfun :
        (fun w ↦ EuclideanSpace.clmMatrix
          (fderiv ℂ (c3RefinedQuadraticChartMap z₀ A Q) w) a j) =
          fun w ↦ (A ej) a + L w := by
      funext w
      exact hentry w
    have hfd : fderiv ℝ (fun w : EuclideanSpace ℂ (Fin n) ↦ (A ej) a + L w) 0 =
        L.restrictScalars ℝ := by
      rw [fderiv_const_add]
      simpa using L.differentiableAt.fderiv_restrictScalars ℝ
    have hI : (L.restrictScalars ℝ)
        (Complex.I • EuclideanSpace.single p (1 : ℂ)) =
        Complex.I * (L.restrictScalars ℝ) (EuclideanSpace.single p (1 : ℂ)) := by
      change L (Complex.I • EuclideanSpace.single p (1 : ℂ)) = _
      exact L.map_smul Complex.I _
    unfold c3PartialZ
    rw [hfun, hfd]
    simp only
    rw [hI]
    simp
    rw [← mul_assoc, Complex.I_mul_I]
    ring_nf
    change (Q (EuclideanSpace.single p (1 : ℂ))
      (EuclideanSpace.single j (1 : ℂ))) a = _
    rfl

  have c3Refined_chartPartialZ_quadratic_pullback_metric
      (ω₀ : KahlerForm n M) (x : M) (z₀ : EuclideanSpace ℂ (Fin n))
      (hz₀ : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
        EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (hQ : ∀ u v, Q u v = Q v u) (p j k : Fin n) :
      c3PartialZ
          (fun v ↦ c3RefinedTracePulledReferenceMetric ω₀ x
            (c3RefinedQuadraticChartMap z₀ A Q) v j k) 0 p =
        (∑ a, ∑ b,
            Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) a *
              (ω₀.metricInChart x z₀) a b * star (EuclideanSpace.clmMatrix A b k)) +
          ∑ a, ∑ b, ∑ c,
            (EuclideanSpace.clmMatrix A a j) * star (EuclideanSpace.clmMatrix A b k) *
              (EuclideanSpace.clmMatrix A c p) *
                c3PartialZ (fun w ↦ ω₀.metricInChart x w a b) z₀ c := by
    let ψ := c3RefinedQuadraticChartMap z₀ A Q
    let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun z ↦ ω₀.metricInChart x z
    let J : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun z ↦ EuclideanSpace.clmMatrix (fderiv ℂ ψ z)
    have hGentry (a b : Fin n) : DifferentiableAt ℝ (fun z ↦ G z a b) z₀ := by
      have hcont := (ω₀.contDiffOn_metricInChart x a b).contDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hz₀)
      exact hcont.differentiableAt (by norm_num)
    have hψ : DifferentiableAt ℂ ψ 0 := by
      have hf : Differentiable ℂ ψ := by
        simpa [ψ] using c3RefinedQuadraticChartMap_differentiable z₀ A Q
      exact hf.differentiableAt
    have hJentry (a b : Fin n) : DifferentiableAt ℂ (fun z ↦ J z a b) 0 := by
      let L : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
        (EuclideanSpace.proj a).comp
          ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin n))
            (EuclideanSpace.single b 1)).comp Q)
      have hformula : (fun z ↦ J z a b) = fun z ↦
          (A (EuclideanSpace.single b 1)) a + L z := by
        funext z
        exact c3Quadratic_jacobian_entry_formula z₀ A Q hQ a b z
      rw [hformula]
      exact (differentiableAt_const _).add L.differentiableAt
    have hGcomp (a b : Fin n) : DifferentiableAt ℝ (fun z ↦ G z a b) (ψ 0) := by
      have hψ0 : ψ 0 = z₀ := by simp [ψ, c3RefinedQuadraticChartMap]
      rw [hψ0]
      exact hGentry a b
    have hPull := c3Pullback_entry_derivative J G ψ 0 p j k hJentry hGcomp hψ
    have hderiv0 : fderiv ℂ ψ 0 = A := by
      simpa [ψ] using c3RefinedQuadraticChartMap_fderiv z₀ A Q hQ 0
    have hJ0 : J 0 = EuclideanSpace.clmMatrix A := by
      change EuclideanSpace.clmMatrix (fderiv ℂ ψ 0) = _
      rw [hderiv0]
    have hJpartial (a b : Fin n) :
        c3PartialZ (fun z ↦ J z a b) 0 p =
          Q (EuclideanSpace.single p 1) (EuclideanSpace.single b 1) a :=
      c3Quadratic_jacobian_entry_partial z₀ A Q hQ a b p
    have hψ0 : ψ 0 = z₀ := by simp [ψ, c3RefinedQuadraticChartMap]
    rw [show (fun v ↦ c3RefinedTracePulledReferenceMetric ω₀ x ψ v j k) =
        fun v ↦ ((J v).transpose * G (ψ v) * (J v).map star) j k by
          funext v
          rfl]
    have hPull' : c3PartialZ
        (fun w ↦ ((J w).transpose * G (ψ w) * (J w).map star) j k) 0 p =
        ∑ r, ∑ s,
          (c3PartialZ (fun w ↦ J w r j) 0 p * G (ψ 0) r s * star (J 0 s k) +
            J 0 r j * (∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ 0)) a p *
              c3PartialZ (fun w ↦ G w r s) (ψ 0) a) * star (J 0 s k)) := by
      simpa using hPull
    rw [hPull']
    simp_rw [hJpartial]
    rw [hderiv0, hJ0, hψ0]
    simp only [G]
    let qterm : Fin n → Fin n → ℂ := fun a b ↦
      (Q (EuclideanSpace.single p 1) (EuclideanSpace.single j 1)).ofLp a *
        (ω₀.metricInChart x z₀) a b * star (EuclideanSpace.clmMatrix A b k)
    let aterm : Fin n → Fin n → ℂ := fun a b ↦
      (EuclideanSpace.clmMatrix A a j *
        (∑ c, EuclideanSpace.clmMatrix A c p *
          c3PartialZ (fun w ↦ ω₀.metricInChart x w a b) z₀ c)) *
        star (EuclideanSpace.clmMatrix A b k)
    let cterm : Fin n → Fin n → Fin n → ℂ := fun a b c ↦
      EuclideanSpace.clmMatrix A a j * star (EuclideanSpace.clmMatrix A b k) *
        EuclideanSpace.clmMatrix A c p *
          c3PartialZ (fun w ↦ ω₀.metricInChart x w a b) z₀ c
    have hsplit : ∑ a, ∑ b, (qterm a b + aterm a b) =
        (∑ a, ∑ b, qterm a b) + (∑ a, ∑ b, aterm a b) := by
      calc
        _ = ∑ a, ((∑ b, qterm a b) + (∑ b, aterm a b)) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact Finset.sum_add_distrib
        _ = _ := by rw [Finset.sum_add_distrib]
    have hterm (a b : Fin n) : aterm a b = ∑ c, cterm a b c := by
      dsimp [aterm, cterm]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c hc
      simp only [starRingEnd_apply]
      ring_nf
    have hsumTerm : ∑ a, ∑ b, aterm a b = ∑ a, ∑ b, ∑ c, cterm a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hterm a b
    rw [hsplit, hsumTerm]

  classical
  let z₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  have hz₀ : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    simp [z₀]
  let G₀ := ω₀.metricInChart x z₀
  let H₀ := G₀ + complexHessian
    (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z₀
  have hG₀ : G₀.PosDef := by
    exact ω₀.posDef_metricInChart x hz₀
  have hH₀ : H₀.PosDef := by
    have h := (ω₀.perturb φ hsol.1).posDef_metricInChart x hz₀
    rw [KahlerForm.metricInChart_perturb hsol.1 x hz₀] at h
    exact h
  obtain ⟨J, eigenvalue, hnormal, hdiagonal, heigenvalue, hJunit⟩ :=
    c3RefinedTrace_exists_simultaneous_normalization G₀ H₀ hG₀ hH₀
  let D : Fin n → Fin n → Fin n → ℂ := fun p a b ↦
    c3PartialZ (fun w ↦ ω₀.metricInChart x w a b) z₀ p
  have hD : ∀ p a b, D p a b = D a p b := by
    intro p a b
    exact c3Refined_kahler_chart_metric_symmetry ω₀ x hz₀ p a b
  obtain ⟨Q, hQ, _hcancel⟩ :=
    c3Refined_exists_quadratic_pullback_jet_cancellation G₀ J D hnormal hD
  have hdetJ : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJunit
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let L : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    Matrix.toLinearEquiv b J hdetJ
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    L.toContinuousLinearEquivOfContinuous L.toLinearMap.continuous_of_finiteDimensional
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    AEquiv.toContinuousLinearMap
  have hAmatrix : EuclideanSpace.clmMatrix A = J := by
    ext a j
    change (Matrix.toLin b b J (EuclideanSpace.single j (1 : ℂ))) a = J a j
    have hb : EuclideanSpace.single j (1 : ℂ) = b j := by
      simp [b, EuclideanSpace.basisFun_apply]
    rw [hb, Matrix.toLin_self]
    simp [b, EuclideanSpace.basisFun_apply, Pi.single_apply]
  let F := c3RefinedQuadraticChartMap z₀ A Q
  have hF₀ : F 0 = z₀ := by simp [F, c3RefinedQuadraticChartMap]
  have hFderiv₀ : fderiv ℂ F 0 = A := by
    simpa [F] using c3RefinedQuadraticChartMap_fderiv z₀ A Q hQ 0
  have hJframe : EuclideanSpace.clmMatrix (fderiv ℂ F 0) = J := by
    rw [hFderiv₀, hAmatrix]
  have hdetA : IsUnit (EuclideanSpace.clmMatrix A).det := by
    rw [hAmatrix]
    exact hdetJ
  have hReference : c3RefinedTracePulledReferenceMetric ω₀ x F 0 = 1 := by
    change (EuclideanSpace.clmMatrix (fderiv ℂ F 0)).transpose *
      ω₀.metricInChart x (F 0) * (EuclideanSpace.clmMatrix (fderiv ℂ F 0)).map star = 1
    rw [hF₀, hJframe]
    simpa [G₀] using hnormal
  have hPerturbedDiagonal :
      c3RefinedTracePulledPerturbedMetric ω₀ φ x F 0 =
        Matrix.diagonal (fun i ↦ (eigenvalue i : ℂ)) := by
    change (EuclideanSpace.clmMatrix (fderiv ℂ F 0)).transpose *
      (ω₀.metricInChart x (F 0) +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) (F 0)) *
      (EuclideanSpace.clmMatrix (fderiv ℂ F 0)).map star = _
    rw [hF₀, hJframe]
    simpa [H₀, G₀] using hdiagonal
  obtain ⟨V, hVopen, hVzero, hVchart, hVsmooth, hVjacobian⟩ :=
    c3Refined_exists_quadratic_local_inverse_kernel z₀ A Q hQ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
      (isOpen_extChartAt_target x) hz₀ hdetA
  refine ⟨{
    center := 0
    domain := V
    open_domain := hVopen
    center_mem := hVzero
    coord := F
    holomorphic := hVsmooth
    in_chart := ?_
    center_eq := hF₀
    jacobian_unit := hVjacobian
    eigenvalue := eigenvalue
    eigenvalue_pos := heigenvalue
    reference_normal := hReference
    reference_first := by
      intro i j p
      have hchain := c3Refined_chartPartialZ_quadratic_pullback_metric
        ω₀ x z₀ hz₀ A Q hQ p i j
      rw [hAmatrix] at hchain
      have hcancel := _hcancel p i j
      rw [hchain]
      simpa [G₀, D] using hcancel
    perturbed_diagonal := hPerturbedDiagonal
  }⟩
  intro y hy
  rcases hy with ⟨v, hv, rfl⟩
  exact hVchart v hv

end KahlerForm
