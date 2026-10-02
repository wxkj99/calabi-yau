module

public import CalabiYau.Geometry.Kahler.Riemannian.Laplacian.ComplexTrace.InverseGramContraction
public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor
public import CalabiYau.Geometry.Kahler.Riemannian.Volume.GramHaarNormalization
public import CalabiYau.Geometry.Manifold.Tensor.Coordinates.PartialDerivative

/-!
# Transport of the real weighted divergence to the complex cofactor divergence

For a positive `(1,1)`-form in a complex chart the real inverse-Gram
contraction is the complex antiholomorphic gradient. Taking its real
divergence gives twice the real part of its holomorphic divergence. The
constant `J = (complexChartBasisVolume n).toReal` records the Jacobian of
the *actual* real chart-model basis, and must not be replaced by `1`.

The form is locally `C¹` and the real function locally `C²`: positivity
alone does not permit differentiating a vector field built from `fderiv u`.
Kähler closedness is used only in the subsequent cofactor cancellation.

Source: Ballmann, *Lectures on Kähler Manifolds*, §5, Exercise 5.51(1),
printed p. 75 (his Laplacian is minus divergence); Székelyhidi,
*An Introduction to Extremal Kähler Metrics*, §§1.1, 1.3.
-/

@[expose] public section

open scoped Topology

namespace KahlerForm

variable {n : ℕ}

private noncomputable def chartDivAlt
    (V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  LinearMap.trace ℝ (EuclideanSpace ℂ (Fin n)) (fderiv ℝ V z).toLinearMap

private theorem chart_basis_coordinates_eq_trace
    {V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z : EuclideanSpace ℂ (Fin n)} (hV : DifferentiableAt ℝ V z) :
    (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
      CalabiYau.Tensor.Coordinates.partialDeriv i
        (fun w ↦ ((CalabiYau.Tensor.Coordinates.chartModelBasis
          (EuclideanSpace ℂ (Fin n))).repr (V w)) i) z) = chartDivAlt V z := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let d := Fin (Module.finrank ℝ E)
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let e : E →L[ℝ] (d → ℝ) :=
    (EuclideanSpace.equiv d ℝ).toContinuousLinearMap.comp
      (toEuclidean (E := E)).toContinuousLinearMap
  have hVcoord : DifferentiableAt ℝ (fun w ↦ e (V w)) z :=
    e.differentiableAt.comp z hV
  have hcomp : fderiv ℝ (fun w ↦ e (V w)) z = e.comp (fderiv ℝ V z) :=
    (e.hasFDerivAt.comp z hV.hasFDerivAt).fderiv
  have hrepr (v : E) (i : d) : (b.repr v) i = e v i := by
    simp [b, e, CalabiYau.Tensor.Coordinates.chartModelBasis,
      Module.Basis.map_repr, EuclideanSpace.equiv]
  rw [chartDivAlt, LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [CalabiYau.Tensor.Coordinates.partialDeriv]
  rw [show (fun w ↦ (b.repr (V w)) i) = fun w ↦ e (V w) i by
    funext w
    exact hrepr (V w) i]
  have hcoord := fderiv_apply hVcoord i
  rw [hcomp] at hcoord
  have hdiag := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ => L (b i)) hcoord
  simpa [b, e, CalabiYau.Tensor.Coordinates.chartModelBasis,
    ContinuousLinearMap.comp_apply, hrepr] using hdiag

private theorem chart_divergence_eq_wirtinger
    {V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z : EuclideanSpace ℂ (Fin n)} (hV : DifferentiableAt ℝ V z) :
    chartDivAlt V z =
      2 * ∑ j, RCLike.re (chartPartialZComplex (fun w ↦ V w j) z j) := by
  classical
  let bfun : Module.Basis (Σ j : Fin n, Fin 2) ℝ (Fin n → ℂ) :=
    Pi.basis (fun _ : Fin n ↦ Complex.basisOneI)
  let b : Module.Basis (Σ j : Fin n, Fin 2) ℝ (EuclideanSpace ℂ (Fin n)) :=
    bfun.map ((EuclideanSpace.equiv (Fin n) ℂ).toLinearEquiv.symm.restrictScalars ℝ)
  rw [chartDivAlt, LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  rw [Fintype.sum_sigma]
  simp only [Fin.sum_univ_two]
  have hs0 (j k : Fin n) :
      (Finsupp.sigmaFinsuppLEquivPiFinsupp ℝ
        (Finsupp.single (⟨j, 0⟩ : Σ _ : Fin n, Fin 2) (1 : ℝ))) k =
        Finsupp.single 0 (if k = j then 1 else 0) := by
    ext a
    simp [Finsupp.sigmaFinsuppLEquivPiFinsupp_apply, Finsupp.single_apply, eq_comm]
    by_cases hkj : j = k
    · subst k
      simp
    · simp [hkj]
  have hs1 (j k : Fin n) :
      (Finsupp.sigmaFinsuppLEquivPiFinsupp ℝ
        (Finsupp.single (⟨j, 1⟩ : Σ _ : Fin n, Fin 2) (1 : ℝ))) k =
        Finsupp.single 1 (if k = j then 1 else 0) := by
    ext a
    simp [Finsupp.sigmaFinsuppLEquivPiFinsupp_apply, Finsupp.single_apply, eq_comm]
    by_cases hkj : j = k
    · subst k
      simp
    · simp [hkj]
  have h0 (j : Fin n) : b ⟨j, 0⟩ = EuclideanSpace.single j 1 := by
    ext k
    simp [b, bfun, Pi.basis, Complex.basisOneI, EuclideanSpace.equiv,
      Finsupp.linearCombination_apply,
      Finsupp.sum, hs0]
    by_cases hkj : k = j <;> simp [hkj]
  have h1 (j : Fin n) : b ⟨j, 1⟩ = Complex.I • EuclideanSpace.single j 1 := by
    ext k
    simp [b, bfun, Pi.basis, Complex.basisOneI, EuclideanSpace.equiv,
      Finsupp.linearCombination_apply,
      Finsupp.sum, hs1]
    by_cases hkj : k = j <;> simp [hkj]
  simp_rw [h0, h1]
  let e : EuclideanSpace ℂ (Fin n) →L[ℝ] (Fin n → ℂ) :=
    (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap.restrictScalars ℝ
  have hVcoord : DifferentiableAt ℝ (fun w ↦ (V w).ofLp) z := by
    change DifferentiableAt ℝ (fun w ↦ e (V w)) z
    exact e.differentiableAt.comp z hV
  have hcomp : fderiv ℝ (fun w ↦ (V w).ofLp) z =
      e.comp (fderiv ℝ V z) := by
    change fderiv ℝ (fun w ↦ e (V w)) z = _
    exact (e.hasFDerivAt.comp z hV.hasFDerivAt).fderiv
  have hcomp_apply (j : Fin n) (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (V w).ofLp j) z d = (fderiv ℝ V z d).ofLp j := by
    have h := fderiv_apply hVcoord j
    rw [hcomp] at h
    simpa [e, EuclideanSpace.equiv] using
      congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
  simp [b, bfun, Pi.basis, Complex.basisOneI, EuclideanSpace.equiv,
    hcomp_apply, chartPartialZComplex]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem chart_basis_flux_divergence
    {V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z : EuclideanSpace ℂ (Fin n)} (hV : DifferentiableAt ℝ V z) :
    (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
      CalabiYau.Tensor.Coordinates.partialDeriv i
        (fun w ↦ ((CalabiYau.Tensor.Coordinates.chartModelBasis
          (EuclideanSpace ℂ (Fin n))).repr (V w)) i) z) =
      2 * ∑ j, RCLike.re (chartPartialZComplex (fun w ↦ V w j) z j) := by
  rw [chart_basis_coordinates_eq_trace hV, chart_divergence_eq_wirtinger hV]

private theorem coeff_det_real
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hα : α.IsPositive) : (α.coeffMatrix.det).im = 0 := by
  have hpos := (ContinuousAlternatingMap.isPositive_iff (α := α)).mp hα
  have hH := hpos.1.isHermitian_coeffMatrix
  have hdet : star α.coeffMatrix.det = α.coeffMatrix.det := by
    rw [← Matrix.det_conjTranspose, hH.eq]
  have him := congrArg Complex.im hdet
  have him' : -α.coeffMatrix.det.im = α.coeffMatrix.det.im := by simpa using him
  linarith

private theorem formGram_flux_coordinates
    (α : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hpos : (α z).IsPositive)
    (hcontract : ContinuousAlternatingMap.ComplexChartInverseGramContraction
      (α z) (fderiv ℝ u z))
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) :
    (α z).coeffMatrix.det.re *
        ∑ j : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
          (ContinuousAlternatingMap.complexChartModelGram (α z))⁻¹ i j *
            CalabiYau.Tensor.Coordinates.partialDeriv j u z =
      ((CalabiYau.Tensor.Coordinates.chartModelBasis
        (EuclideanSpace ℂ (Fin n))).repr
          ((α z).coeffMatrix.det • ∑ j : Fin n,
            (∑ k : Fin n, (α z).coeffMatrix⁻¹ k j * chartPartialBar u z k) •
              EuclideanSpace.single j (1 : ℂ))) i := by
  classical
  have hdet := coeff_det_real hpos
  have hc := hcontract
  change (∑ i' : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
      (∑ j' : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
        (ContinuousAlternatingMap.complexChartModelGram (α z))⁻¹ i' j' *
          fderiv ℝ u z
            (CalabiYau.Tensor.Coordinates.chartModelBasis
              (EuclideanSpace ℂ (Fin n)) j')) •
        CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) i') =
      ∑ j' : Fin n,
        (∑ k : Fin n, (α z).coeffMatrix⁻¹ k j' *
          (((fderiv ℝ u z (EuclideanSpace.single k 1) : ℂ) +
            Complex.I * (fderiv ℝ u z (Complex.I • EuclideanSpace.single k 1) : ℂ)) / 2)) •
          EuclideanSpace.single j' (1 : ℂ) at hc
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis
    (EuclideanSpace ℂ (Fin n))
  have hcoord := congrArg (fun v : EuclideanSpace ℂ (Fin n) => (b.repr v) i) hc
  have hd : (α z).coeffMatrix.det = ((α z).coeffMatrix.det.re : ℝ) := by
    exact Complex.ext rfl hdet
  have hleft : (b.repr
      (∑ i' : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
        (∑ j' : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
          (ContinuousAlternatingMap.complexChartModelGram (α z))⁻¹ i' j' *
            fderiv ℝ u z (b j')) • b i')) i =
      ∑ j' : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
        (ContinuousAlternatingMap.complexChartModelGram (α z))⁻¹ i j' *
          fderiv ℝ u z (b j') := by
    simpa using congrFun (b.repr_sum_self
      (fun i' => ∑ j' : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
        (ContinuousAlternatingMap.complexChartModelGram (α z))⁻¹ i' j' *
          fderiv ℝ u z (b j'))) i
  have hcoordB : (b.repr
      (∑ i' : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
        (∑ j' : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
          (ContinuousAlternatingMap.complexChartModelGram (α z))⁻¹ i' j' *
            fderiv ℝ u z (b j')) • b i')) i =
      (b.repr
        (∑ j' : Fin n,
          (∑ k : Fin n, (α z).coeffMatrix⁻¹ k j' *
            (((fderiv ℝ u z (EuclideanSpace.single k 1) : ℂ) +
              Complex.I * (fderiv ℝ u z (Complex.I • EuclideanSpace.single k 1) : ℂ)) / 2)) •
            EuclideanSpace.single j' (1 : ℂ))) i := by
    simpa [b] using hcoord
  rw [hleft] at hcoordB
  rw [hd]
  simp only [CalabiYau.Tensor.Coordinates.partialDeriv]
  rw [hcoordB]
  let Y : EuclideanSpace ℂ (Fin n) :=
    ∑ j' : Fin n,
      (∑ k : Fin n, (α z).coeffMatrix⁻¹ k j' * chartPartialBar u z k) •
        EuclideanSpace.single j' (1 : ℂ)
  change (α z).coeffMatrix.det.re * (b.repr Y) i =
    (b.repr ((↑(α z).coeffMatrix.det.re : ℂ) • Y)) i
  have hscalar : ((↑(α z).coeffMatrix.det.re : ℂ) • Y) =
      (α z).coeffMatrix.det.re • Y := by
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ)
      (α z).coeffMatrix.det.re Y).symm
  rw [hscalar]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- The real divergence with density `J · 2^n · det G` equals twice the
real part of the holomorphic divergence of the complex cofactor flux. -/
theorem formGram_weighted_divergence_eq_complex_cofactor
    (α : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hα : ContDiffAt ℝ 1 α z) (hu : ContDiffAt ℝ 2 u z)
    (hpos : ∀ᶠ w in 𝓝 z, (α w).IsPositive)
    (hcontract : ∀ᶠ w in 𝓝 z,
      ContinuousAlternatingMap.ComplexChartInverseGramContraction
        (α w) (fderiv ℝ u w)) :
    let J := (CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal
    let G := fun w : EuclideanSpace ℂ (Fin n) => (α w).coeffMatrix
    (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
      CalabiYau.Tensor.Coordinates.partialDeriv i
        (fun w : EuclideanSpace ℂ (Fin n) =>
          J * (2 : ℝ) ^ n * (G w).det.re *
            ∑ j : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
              ((α w).complexChartModelGram)⁻¹ i j *
                CalabiYau.Tensor.Coordinates.partialDeriv j u w) z) =
      2 * J * (2 : ℝ) ^ n *
        RCLike.re (∑ k : Fin n, ∑ j : Fin n,
          chartPartialZComplex
            (fun w : EuclideanSpace ℂ (Fin n) =>
              (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j) := by
  classical
  let J : ℝ := (CalabiYau.RiemannianVolume.complexChartBasisVolume n).toReal
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => (α w).coeffMatrix
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis
    (EuclideanSpace ℂ (Fin n))
  let Q (w : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
    ∑ j : Fin n,
      (∑ k : Fin n, (G w)⁻¹ k j * chartPartialBar u w k) •
        EuclideanSpace.single j (1 : ℂ)
  let V (w : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
    (G w).det • Q w
  let C : ℝ := J * (2 : ℝ) ^ n
  have hcoeff (a b : Fin n) :
      DifferentiableAt ℝ (fun w => (α w).coeffMatrix a b) z := by
    have hαdiff : DifferentiableAt ℝ α z := hα.differentiableAt (by norm_num)
    have hA0 : DifferentiableAt ℝ
        (fun w => α w ![EuclideanSpace.single a 1,
          Complex.I • EuclideanSpace.single b 1]) z :=
      hαdiff.continuousAlternatingMap_apply_const _
    have hB0 : DifferentiableAt ℝ
        (fun w => α w ![EuclideanSpace.single a 1,
          EuclideanSpace.single b 1]) z :=
      hαdiff.continuousAlternatingMap_apply_const _
    let A := fun w => ((α w ![EuclideanSpace.single a 1,
      Complex.I • EuclideanSpace.single b 1] : ℝ) : ℂ)
    let B := fun w => ((α w ![EuclideanSpace.single a 1,
      EuclideanSpace.single b 1] : ℝ) : ℂ)
    have hA : DifferentiableAt ℝ A z := by
      change DifferentiableAt ℝ
        (Complex.ofRealCLM ∘ fun w => α w ![EuclideanSpace.single a 1,
          Complex.I • EuclideanSpace.single b 1]) z
      exact Complex.ofRealCLM.differentiableAt.comp z hA0
    have hB : DifferentiableAt ℝ B z := by
      change DifferentiableAt ℝ
        (Complex.ofRealCLM ∘ fun w => α w ![EuclideanSpace.single a 1,
          EuclideanSpace.single b 1]) z
      exact Complex.ofRealCLM.differentiableAt.comp z hB0
    change DifferentiableAt ℝ (fun w => (A w - Complex.I * B w) / 2) z
    have hfun : (fun w => (A w - Complex.I * B w) / 2) =
        fun w => (2 : ℂ)⁻¹ * (A w - Complex.I * B w) := by
      funext w
      simp only [div_eq_mul_inv]
      ring
    rw [hfun]
    exact (hA.sub (hB.const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
  have hposZ : (α z).IsPositive := hpos.self_of_nhds
  open scoped ComplexOrder MatrixOrder in
  have hposMatrix : (G z).PosDef := by
    exact (ContinuousAlternatingMap.isPositive_iff.mp hposZ).2
  have hunit : IsUnit (G z) := hposMatrix.isUnit
  have hdetDiff : DifferentiableAt ℝ (fun w => (G w).det) z := by
    simp_rw [Matrix.det_apply]
    fun_prop
  have hdetUnit : IsUnit (G z).det :=
    (Matrix.isUnit_iff_isUnit_det (A := G z)).mp hunit
  have hinvDetDiff : DifferentiableAt ℝ (fun w => (G w).det⁻¹) z :=
    (differentiableAt_inv hdetUnit.ne_zero).comp z hdetDiff
  have hadjEntry (k j : Fin n) :
      DifferentiableAt ℝ (fun w => (G w).adjugate k j) z := by
    let row : Fin n → ℂ := Pi.single k (1 : ℂ)
    have hrow (a b : Fin n) :
        DifferentiableAt ℝ (fun w => ((G w).updateRow j row) a b) z := by
      have hUpd : (fun w => ((G w).updateRow j row) a b) =
          fun w => if a = j then row b else G w a b := by
        funext w
        exact Matrix.updateRow_apply
      rw [hUpd]
      by_cases h : a = j
      · simp [h]
      · simp [h]
        exact hcoeff a b
    have hdetUpdate : DifferentiableAt ℝ (fun w => ((G w).updateRow j row).det) z := by
      simp only [Matrix.det_apply]
      apply DifferentiableAt.fun_sum (u := Finset.univ)
      intro σ hσ
      have hp := HasFDerivAt.finsetProd (u := Finset.univ)
        (g := fun i w => ((G w).updateRow j row) (σ i) i)
        (fun i hi => (hrow (σ i) i).hasFDerivAt)
      have hp' : DifferentiableAt ℝ
          (fun w => ∏ i : Fin n, ((G w).updateRow j row) (σ i) i) z := by
        have hp' := hp.differentiableAt
        simpa using hp'
      fun_prop
    rw [show (fun w => (G w).adjugate k j) =
        fun w => ((G w).updateRow j row).det by
      funext w
      simpa [row] using (Matrix.adjugate_apply (G w) k j)]
    exact hdetUpdate
  have hbar (k : Fin n) :
      DifferentiableAt ℝ (fun w => chartPartialBar u w k) z := by
    have hfd : DifferentiableAt ℝ (fderiv ℝ u) z :=
      (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    let A := fun w => (fderiv ℝ u w (EuclideanSpace.single k 1) : ℂ)
    let B := fun w => (fderiv ℝ u w (Complex.I • EuclideanSpace.single k 1) : ℂ)
    have hA : DifferentiableAt ℝ A z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        (hfd.clm_apply (differentiableAt_const _)))
    have hB : DifferentiableAt ℝ B z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        (hfd.clm_apply (differentiableAt_const _)))
    have hfun : (fun w => chartPartialBar u w k) =
        fun w => (2 : ℂ)⁻¹ * (A w + Complex.I * B w) := by
      funext w
      simp [chartPartialBar, A, B, div_eq_mul_inv]
      ring
    rw [hfun]
    exact (hA.add (hB.const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
  have hinv (k j : Fin n) :
      DifferentiableAt ℝ (fun w => (G w)⁻¹ k j) z := by
    have hformula : (fun w => (G w)⁻¹ k j) =
        fun w => (G w).det⁻¹ * (G w).adjugate k j := by
      funext w
      simp [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [hformula]
    exact hinvDetDiff.mul (hadjEntry k j)
  have hterm (k j : Fin n) :
      DifferentiableAt ℝ
        (fun w => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z :=
    (hdetDiff.mul (hinv k j)).mul (hbar k)
  have hVcomponent (j : Fin n) :
      (fun w => V w j) = fun w =>
        ∑ k : Fin n, (G w).det * (G w)⁻¹ k j * chartPartialBar u w k := by
    funext w
    simp [V, Q, Pi.single_apply, Finset.mul_sum, mul_assoc]
  have hVcoord (j : Fin n) : DifferentiableAt ℝ (fun w => V w j) z := by
    rw [hVcomponent j]
    exact DifferentiableAt.fun_sum (u := Finset.univ) (fun k hk => hterm k j)
  have hV : DifferentiableAt ℝ V z := by
    let e : EuclideanSpace ℂ (Fin n) →L[ℝ] (Fin n → ℂ) :=
      (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap.restrictScalars ℝ
    let eInv : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
      (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ
    have hVpi : DifferentiableAt ℝ (fun w => e (V w)) z := by
      change DifferentiableAt ℝ (fun w => (V w).ofLp) z
      exact differentiableAt_pi.2 hVcoord
    have h := eInv.differentiableAt.comp z hVpi
    have hEq : (fun w => eInv (e (V w))) = V := by
      funext w
      simp [e, eInv, EuclideanSpace.equiv]
    change DifferentiableAt ℝ (fun w => eInv (e (V w))) z at h
    rw [hEq] at h
    exact h
  let d := Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))
  let F (i : d) : EuclideanSpace ℂ (Fin n) → ℝ := fun w =>
    C * (G w).det.re *
      ∑ j : d, (ContinuousAlternatingMap.complexChartModelGram (α w))⁻¹ i j *
        CalabiYau.Tensor.Coordinates.partialDeriv j u w
  let H (i : d) : EuclideanSpace ℂ (Fin n) → ℝ := fun w =>
    C * (b.repr (V w)) i
  have hflux (i : d) : F i =ᶠ[𝓝 z] H i := by
    filter_upwards [hpos, hcontract] with w hwpos hwcontract
    have hpoint := formGram_flux_coordinates α u w hwpos hwcontract i
    have hpoint' :
        (G w).det.re *
          ∑ j : d, (ContinuousAlternatingMap.complexChartModelGram (α w))⁻¹ i j *
            CalabiYau.Tensor.Coordinates.partialDeriv j u w =
        (b.repr (V w)) i := by
      simpa [G, V, Q, b] using hpoint
    dsimp [F, H]
    calc
      C * (G w).det.re *
          ∑ j : d, (ContinuousAlternatingMap.complexChartModelGram (α w))⁻¹ i j *
            CalabiYau.Tensor.Coordinates.partialDeriv j u w =
        C * ((G w).det.re *
          ∑ j : d, (ContinuousAlternatingMap.complexChartModelGram (α w))⁻¹ i j *
            CalabiYau.Tensor.Coordinates.partialDeriv j u w) := by ring
      _ = C * (b.repr (V w)) i := by rw [hpoint']
  have hderiv (i : d) :
      CalabiYau.Tensor.Coordinates.partialDeriv i (F i) z =
        CalabiYau.Tensor.Coordinates.partialDeriv i (H i) z := by
    have hf := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (hflux i)
    simpa [F, H, CalabiYau.Tensor.Coordinates.partialDeriv, b] using
      congrArg (fun D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ => D (b i)) hf
  let eCoord : EuclideanSpace ℂ (Fin n) →L[ℝ] (d → ℝ) :=
    (EuclideanSpace.equiv d ℝ).toContinuousLinearMap.comp
      (toEuclidean (E := EuclideanSpace ℂ (Fin n))).toContinuousLinearMap
  have hreprCoord (v : EuclideanSpace ℂ (Fin n)) (i : d) :
      (b.repr v) i = eCoord v i := by
    simp [b, eCoord, CalabiYau.Tensor.Coordinates.chartModelBasis,
      Module.Basis.map_repr, EuclideanSpace.equiv]
  have hEV : DifferentiableAt ℝ (fun w => eCoord (V w)) z :=
    eCoord.differentiableAt.comp z hV
  have hreprDiff (i : d) :
      DifferentiableAt ℝ (fun w => (b.repr (V w)) i) z := by
    have hEq : (fun w => (b.repr (V w)) i) = fun w => eCoord (V w) i := by
      funext w
      exact hreprCoord (V w) i
    rw [hEq]
    exact (differentiableAt_pi.1 hEV) i
  have hscale (i : d) :
      CalabiYau.Tensor.Coordinates.partialDeriv i (H i) z =
        C * CalabiYau.Tensor.Coordinates.partialDeriv i
          (fun w => (b.repr (V w)) i) z := by
    simp only [H, CalabiYau.Tensor.Coordinates.partialDeriv]
    rw [fderiv_const_mul (hreprDiff i) C]
    simp
  have hsumScale :
      (∑ i : d, CalabiYau.Tensor.Coordinates.partialDeriv i (H i) z) =
        C * ∑ i : d, CalabiYau.Tensor.Coordinates.partialDeriv i
          (fun w => (b.repr (V w)) i) z := by
    calc
      _ = ∑ i : d, C * CalabiYau.Tensor.Coordinates.partialDeriv i
          (fun w => (b.repr (V w)) i) z := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hscale i
      _ = _ := by rw [← Finset.mul_sum]
  have hpartialSum (j : Fin n) :
      chartPartialZComplex (fun w => V w j) z j =
        ∑ k : Fin n,
          chartPartialZComplex
            (fun w => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j := by
    rw [hVcomponent j]
    have hfdSum :
        fderiv ℝ (fun w => ∑ k : Fin n,
          (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z =
          ∑ k : Fin n, fderiv ℝ
            (fun w => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z :=
      fderiv_fun_sum (u := Finset.univ) (fun k hk => hterm k j)
    have h1 := congrArg (fun D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ =>
      D (EuclideanSpace.single j (1 : ℂ))) hfdSum
    have h2 := congrArg (fun D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ =>
      D (Complex.I • EuclideanSpace.single j (1 : ℂ))) hfdSum
    unfold chartPartialZComplex
    rw [h1, h2]
    rw [_root_.sum_apply, _root_.sum_apply]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  have hrealSum :
      (∑ j : Fin n, RCLike.re
        (chartPartialZComplex (fun w => V w j) z j)) =
        RCLike.re (∑ k : Fin n, ∑ j : Fin n,
          chartPartialZComplex
            (fun w => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j) := by
    calc
      _ = ∑ j : Fin n, RCLike.re (∑ k : Fin n,
          chartPartialZComplex
            (fun w => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hpartialSum j]
      _ = RCLike.re (∑ j : Fin n, ∑ k : Fin n,
          chartPartialZComplex
            (fun w => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j) := by
        change (∑ j : Fin n,
          (∑ k : Fin n, chartPartialZComplex
            (fun w => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j).re) =
          (∑ j : Fin n, ∑ k : Fin n, chartPartialZComplex
            (fun w => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j).re
        rw [Complex.re_sum]
      _ = _ := by congr 1; rw [Finset.sum_comm]
  change (∑ i : d, CalabiYau.Tensor.Coordinates.partialDeriv i (F i) z) = _
  calc
    _ = ∑ i : d, CalabiYau.Tensor.Coordinates.partialDeriv i (H i) z := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hderiv i
    _ = C * (2 * ∑ j : Fin n, RCLike.re
        (chartPartialZComplex (fun w => V w j) z j)) := by
      rw [hsumScale, chart_basis_flux_divergence hV]
    _ = 2 * J * (2 : ℝ) ^ n * RCLike.re
        (∑ k : Fin n, ∑ j : Fin n,
          chartPartialZComplex
            (fun w => (G w).det * (G w)⁻¹ k j * chartPartialBar u w k) z j) := by
      rw [hrealSum]
      dsimp [C]
      ring

end KahlerForm
