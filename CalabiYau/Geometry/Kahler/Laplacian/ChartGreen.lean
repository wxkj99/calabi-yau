module
public import CalabiYau.Geometry.Kahler.Basic
public import CalabiYau.Geometry.Kahler.Volume
public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Map
import CalabiYau.Geometry.Kahler.Laplacian.EuclideanDivergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
@[expose] public section
open scoped Manifold ContDiff ComplexOrder
open Set MeasureTheory ContinuousAlternatingMap
namespace KahlerForm
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  (ω₀ : KahlerForm n M)
variable {ω₀}
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem chart_integral_by_parts
    (x : M) (χ u v : EuclideanSpace ℂ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hχcompact : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
        (2 ^ n * RCLike.re (ω₀.metricInChart x z).det) * χ z * u z *
          RCLike.re ((ω₀.metricInChart x z)⁻¹ * complexHessian v z).trace
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      -∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
          (2 ^ n * RCLike.re (ω₀.metricInChart x z).det) * χ z *
            chartGradientPair (ω₀.metricInChart x) u v z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) -
    ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
        (2 ^ n * RCLike.re (ω₀.metricInChart x z).det) * u z *
          chartGradientPair (ω₀.metricInChart x) χ v z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
  have hdiv := kahler_chart_cofactor_divergence (ω₀ := ω₀) x
  let G := ω₀.metricInChart x
  have hdetReal (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      (G z).det.im = 0 := by
    have hstar : star (G z).det = (G z).det := by
      calc
        star (G z).det = (Matrix.conjTranspose (G z)).det :=
          (Matrix.det_conjTranspose (G z)).symm
        _ = (G z).det := congrArg Matrix.det (ω₀.posDef_metricInChart x hz).isHermitian.eq
    have him := congrArg Complex.im hstar
    have him' : -(G z).det.im = (G z).det.im := by simpa using him
    linarith
  have htrace (V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
      (z : EuclideanSpace ℂ (Fin n)) (hV : DifferentiableAt ℝ V z) :
      chartDivergence V z =
        2 * ∑ j, RCLike.re (chartPartialZComplex (fun w ↦ V w j) z j) := by
    classical
    let bfun : Module.Basis (Σ j : Fin n, Fin 2) ℝ (Fin n → ℂ) :=
      Pi.basis (fun _ : Fin n ↦ Complex.basisOneI)
    let b : Module.Basis (Σ j : Fin n, Fin 2) ℝ (EuclideanSpace ℂ (Fin n)) :=
      bfun.map ((EuclideanSpace.equiv (Fin n) ℂ).toLinearEquiv.symm.restrictScalars ℝ)
    rw [chartDivergence, LinearMap.trace_eq_matrix_trace ℝ b]
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
  have hv2 (z : EuclideanSpace ℂ (Fin n)) : ContDiffAt ℝ 2 v z := by
    have hle : (2 : ℕ∞ω) ≤ ∞ := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    exact (hv.contDiffAt (x := z)).of_le hle
  have hfdv (z : EuclideanSpace ℂ (Fin n)) :
      DifferentiableAt ℝ (fderiv ℝ v) z := by
    exact (hv2 z).fderiv_right (m := 1) (by norm_num) |>.differentiableAt (by norm_num)
  have hsecond (z d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ v w e) z d = fderiv ℝ (fderiv ℝ v) z d e := by
    rw [fderiv_clm_apply (hfdv z) (differentiableAt_const e)]
    simp
  have hsecondComplex (z d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ v w e : ℂ)) z d =
        (fderiv ℝ (fderiv ℝ v) z d e : ℂ) := by
    have hreal := (hfdv z).clm_apply (differentiableAt_const e)
    have h := (Complex.ofRealCLM.hasFDerivAt.comp z hreal.hasFDerivAt).fderiv
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
    change fderiv ℝ (Complex.ofRealCLM ∘ (fun w ↦ fderiv ℝ v w e)) z d = _
    simpa [hsecond] using h'
  have hbarDeriv (z d : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
      fderiv ℝ (fun w ↦ chartPartialBar v w k) z d =
        ((fderiv ℝ (fderiv ℝ v) z d (EuclideanSpace.single k 1) : ℂ) +
          Complex.I * fderiv ℝ (fderiv ℝ v) z d (Complex.I • EuclideanSpace.single k 1)) / 2 := by
    let A := fun w ↦ (fderiv ℝ v w (EuclideanSpace.single k 1) : ℂ)
    let B := fun w ↦ (fderiv ℝ v w (Complex.I • EuclideanSpace.single k 1) : ℂ)
    have hA : DifferentiableAt ℝ A z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        ((hfdv z).clm_apply (differentiableAt_const _)))
    have hB : DifferentiableAt ℝ B z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        ((hfdv z).clm_apply (differentiableAt_const _)))
    have hnum : DifferentiableAt ℝ (fun w ↦ A w + Complex.I * B w) z :=
      hA.add (hB.const_mul Complex.I)
    have hfun : (fun w ↦ chartPartialBar v w k) =
        fun w ↦ (2 : ℂ)⁻¹ * (A w + Complex.I * B w) := by
      funext w
      simp [chartPartialBar, A, B, div_eq_mul_inv]
      ring
    rw [hfun, fderiv_const_mul hnum (2 : ℂ)⁻¹, fderiv_fun_add hA (hB.const_mul Complex.I),
      fderiv_const_mul hB Complex.I]
    dsimp [A, B]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hsecondComplex z d (EuclideanSpace.single k 1),
      hsecondComplex z d (Complex.I • EuclideanSpace.single k 1)]
    ring
  have hpartial (z : EuclideanSpace ℂ (Fin n)) (j k : Fin n) :
      chartPartialZComplex (fun w ↦ chartPartialBar v w k) z j = complexHessian v z j k := by
    change ((fderiv ℝ (fun w ↦ chartPartialBar v w k) z (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ (fun w ↦ chartPartialBar v w k) z
        (Complex.I • EuclideanSpace.single j 1)) / 2) = _
    rw [hbarDeriv z (EuclideanSpace.single j 1) k,
      hbarDeriv z (Complex.I • EuclideanSpace.single j 1) k,
      complexHessian_apply (hv2 z) j k]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hGentry (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z := by
    intro a b
    have hle : (1 : ℕ∞ω) ≤ ∞ := by
      change ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    exact ((ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).of_le hle
  have hdetContDiffAt (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      ContDiffAt ℝ 1 (fun w ↦ (G w).det) z := by
    have hentry := hGentry z hz
    simp_rw [Matrix.det_apply]
    fun_prop
  have hfdContDiffAt (z : EuclideanSpace ℂ (Fin n)) :
      ContDiffAt ℝ 1 (fderiv ℝ v) z := by
    have hle : (2 : ℕ∞ω) ≤ ∞ := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    exact (hv.contDiffAt (x := z)).fderiv_right (m := 1) hle
  have hbarContDiffAt (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
      ContDiffAt ℝ 1 (fun w ↦ chartPartialBar v w k) z := by
    let A := fun w ↦ (fderiv ℝ v w (EuclideanSpace.single k 1) : ℂ)
    let B := fun w ↦ (fderiv ℝ v w (Complex.I • EuclideanSpace.single k 1) : ℂ)
    have hAreal : ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ v w (EuclideanSpace.single k 1)) z :=
      (hfdContDiffAt z).clm_apply contDiffAt_const
    have hBreal : ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ v w (Complex.I • EuclideanSpace.single k 1)) z :=
      (hfdContDiffAt z).clm_apply contDiffAt_const
    have hA : ContDiffAt ℝ 1 A z :=
      ContDiffAt.comp z Complex.ofRealCLM.contDiff.contDiffAt hAreal
    have hB : ContDiffAt ℝ 1 B z :=
      ContDiffAt.comp z Complex.ofRealCLM.contDiff.contDiffAt hBreal
    have hfun : (fun w ↦ chartPartialBar v w k) =
        fun w ↦ (2 : ℂ)⁻¹ * (A w + Complex.I * B w) := by
      funext w
      simp [chartPartialBar, A, B, div_eq_mul_inv]
      ring
    rw [hfun]
    have hIB : ContDiffAt ℝ 1 (fun w ↦ Complex.I * B w) z := contDiffAt_const.mul hB
    exact contDiffAt_const.mul (hA.add hIB)
  have hGunit (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) : IsUnit (G z) :=
    (ω₀.posDef_metricInChart x hz).isUnit
  have hdetDiff (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      DifferentiableAt ℝ (fun w ↦ (G w).det) z := by
    have hG := hGentry z hz
    simp_rw [Matrix.det_apply]
    fun_prop
  have hbarDiff (z : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
      DifferentiableAt ℝ (fun w ↦ chartPartialBar v w k) z := by
    let A := fun w ↦ (fderiv ℝ v w (EuclideanSpace.single k 1) : ℂ)
    let B := fun w ↦ (fderiv ℝ v w (Complex.I • EuclideanSpace.single k 1) : ℂ)
    have hA : DifferentiableAt ℝ A z :=
      Complex.ofRealCLM.differentiableAt.comp z
        ((hfdv z).clm_apply (differentiableAt_const _))
    have hB : DifferentiableAt ℝ B z :=
      Complex.ofRealCLM.differentiableAt.comp z
        ((hfdv z).clm_apply (differentiableAt_const _))
    have hfun : (fun w ↦ chartPartialBar v w k) =
        fun w ↦ (2 : ℂ)⁻¹ * (A w + Complex.I * B w) := by
      funext w
      simp [chartPartialBar, A, B, div_eq_mul_inv]
      ring
    rw [hfun]
    exact (hA.add (hB.const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
  let C (z : EuclideanSpace ℂ (Fin n)) (k j : Fin n) := (G z).det * (G z)⁻¹ k j
  let q (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :=
    ∑ k, C z k j * chartPartialBar v z k
  have hCdiff (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (k j : Fin n) : DifferentiableAt ℝ (fun w ↦ C w k j) z := by
    exact (hdetDiff z hz).mul
      (chartInv_differentiableAt (hGentry z hz) (hGunit z hz) k j)
  have hCcontDiffAt (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (k j : Fin n) : ContDiffAt ℝ 1 (fun w ↦ C w k j) z := by
    have hdetUnit : IsUnit ((G z).det) :=
      (Matrix.isUnit_iff_isUnit_det (A := G z)).mp (hGunit z hz)
    have hinvDet : ContDiffAt ℝ 1 (fun w ↦ Ring.inverse ((G w).det)) z := by
      have hring : ContDiffAt ℝ 1 Ring.inverse ((G z).det) :=
        contDiffAt_ringInverse ℝ hdetUnit.unit
      exact hring.comp z (hdetContDiffAt z hz)
    have hadj (a b : Fin n) : ContDiffAt ℝ 1 (fun w ↦ (G w).adjugate a b) z := by
      simp_rw [Matrix.adjugate_apply]
      have hupdate (p q : Fin n) :
          ContDiffAt ℝ 1
            (fun w ↦ (G w).updateRow b (Pi.single a (1 : ℂ)) p q) z := by
        by_cases hp : p = b
        · simp [Matrix.updateRow_apply, hp]
          fun_prop
        · simpa [Matrix.updateRow_apply, hp] using hGentry z hz p q
      simp_rw [Matrix.det_apply]
      fun_prop
    have hform : (fun w ↦ (G w)⁻¹ k j) =
        fun w ↦ Ring.inverse ((G w).det) * (G w).adjugate k j := by
      funext w
      simp [Matrix.inv_def, smul_eq_mul]
    have hinv : ContDiffAt ℝ 1 (fun w ↦ (G w)⁻¹ k j) z := by
      rw [hform]
      exact hinvDet.mul (hadj k j)
    change ContDiffAt ℝ 1 (fun w ↦ (G w).det * (G w)⁻¹ k j) z
    exact (hdetContDiffAt z hz).mul hinv
  have hCpartial (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (k j : Fin n) :
      chartPartialZComplex (fun w ↦ C w k j) z j =
        (G z).det *
          (Matrix.trace ((G z)⁻¹ * Matrix.of (fun a b ↦
            chartPartialZComplex (fun w ↦ G w a b) z j)) * (G z)⁻¹ k j -
            (((G z)⁻¹ * (Matrix.of (fun a b ↦
              chartPartialZComplex (fun w ↦ G w a b) z j) * (G z)⁻¹)) k j)) := by
    simpa [C] using chartCofactor_partial_formula (hGentry z hz) (hGunit z hz) k j
  have hqDiff (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (j : Fin n) : DifferentiableAt ℝ (fun w ↦ q w j) z := by
    apply DifferentiableAt.fun_sum (u := Finset.univ)
    intro k hk
    exact (hCdiff z hz k j).mul (hbarDiff z k)
  have hqContDiffAt (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (j : Fin n) : ContDiffAt ℝ 1 (fun w ↦ q w j) z := by
    apply ContDiffAt.sum (s := Finset.univ)
    intro k hk
    exact (hCcontDiffAt z hz k j).mul (hbarContDiffAt z k)
  let einv : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℂ).symm.toContinuousLinearMap.restrictScalars ℝ
  let W (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
    einv (fun j ↦ ((2 : ℝ) ^ n / 2 : ℂ) * q z j)
  let a (z : EuclideanSpace ℂ (Fin n)) : ℝ := χ z * u z
  let F (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) := a z • W z
  have ha : ContDiff ℝ 1 a := by
    change ContDiff ℝ 1 (fun z ↦ χ z * u z)
    exact hχ.of_le (by norm_num) |>.mul (hu.of_le (by norm_num))
  have hWcontDiffAt (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      ContDiffAt ℝ 1 W z := by
    have hpi : ContDiffAt ℝ 1 (fun w j ↦ ((2 : ℝ) ^ n / 2 : ℂ) * q w j) z := by
      rw [contDiffAt_pi]
      intro j
      exact contDiffAt_const.mul (hqContDiffAt z hz j)
    change ContDiffAt ℝ 1 (fun w ↦ einv (fun j ↦ ((2 : ℝ) ^ n / 2 : ℂ) * q w j)) z
    exact einv.contDiff.contDiffAt.comp z hpi
  have hFcont : ContDiff ℝ 1 F := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
    · change ContDiffAt ℝ 1 (fun w ↦ a w • W w) z
      exact ha.contDiffAt.smul (hWcontDiffAt z hz)
    · have hnotχ : z ∉ tsupport χ := by
        intro hzχ
        exact hz (hχsupport hzχ)
      have hnotA : z ∉ tsupport a := by
        intro hzA
        exact hnotχ ((tsupport_mul_subset_left (f := χ) (g := u)) hzA)
      have hzero : (fun w ↦ F w) =ᶠ[nhds z] fun _ ↦ (0 : EuclideanSpace ℂ (Fin n)) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq).mp hnotA] with w hw
        simp [F, a, hw]
      exact (contDiffAt_const : ContDiffAt ℝ 1
        (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : EuclideanSpace ℂ (Fin n))) z)
        |>.congr_of_eventuallyEq hzero
  have hFsupport (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ tsupport F) : z ∈ tsupport χ := by
    exact (tsupport_mul_subset_left (f := χ) (g := u))
      ((tsupport_smul_subset_left (f := a) (g := W)) hz)
  have hFcompact : HasCompactSupport F := by
    apply HasCompactSupport.intro hχcompact.isCompact
    intro z hz
    have hnotA : z ∉ tsupport a := by
      intro hzA
      exact hz ((tsupport_mul_subset_left (f := χ) (g := u)) hzA)
    have ha0 : a z = 0 := by
      by_contra hne
      exact hnotA (subset_tsupport _ hne)
    simp [F, ha0]
  have hWcoord (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      (W z).ofLp j = ((2 : ℝ) ^ n / 2 : ℂ) * q z j := by
    simp [W, einv, EuclideanSpace.equiv]
  have hWfun (j : Fin n) : (fun w ↦ (W w).ofLp j) =
      fun w ↦ ((2 : ℝ) ^ n / 2 : ℂ) * q w j := by
    funext w
    exact hWcoord w j
  have hFpartial (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) (j : Fin n) :
      chartPartialZComplex (fun w ↦ (F w).ofLp j) z j =
        chartPartialZComplex (fun w ↦ (a w : ℂ)) z j *
            (((2 : ℝ) ^ n / 2 : ℂ) * q z j) +
          (a z : ℂ) * ((2 : ℝ) ^ n / 2 : ℂ) *
            chartPartialZComplex (fun w ↦ q w j) z j := by
    have haDiff : DifferentiableAt ℝ (fun w ↦ (a w : ℂ)) z :=
      Complex.ofRealCLM.differentiableAt.comp z
        (ha.contDiffAt.differentiableAt (by norm_num))
    have hqCoordDiff : DifferentiableAt ℝ (fun w ↦ q w j) z := hqDiff z hz j
    have hWcoordDiff : DifferentiableAt ℝ (fun w ↦ (W w).ofLp j) z := by
      rw [hWfun]
      simpa [mul_comm] using
        (hqCoordDiff.const_mul ((2 : ℝ) ^ n / 2 : ℂ))
    calc
      _ = chartPartialZComplex (fun w ↦ (a w : ℂ)) z j * (W z).ofLp j +
          (a z : ℂ) * chartPartialZComplex (fun w ↦ (W w).ofLp j) z j := by
        have hmul := chartPartialZComplex_mul haDiff hWcoordDiff j
        simpa [F] using hmul
      _ = _ := by
        rw [hWcoord z j, hWfun]
        simp [chartPartialZComplex, fderiv_const_mul hqCoordDiff]
        ring
  have hFdivQ (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      chartDivergence F z =
        2 * ∑ j, RCLike.re
          (chartPartialZComplex (fun w ↦ (a w : ℂ)) z j *
              (((2 : ℝ) ^ n / 2 : ℂ) * q z j) +
            (a z : ℂ) * ((2 : ℝ) ^ n / 2 : ℂ) *
              chartPartialZComplex (fun w ↦ q w j) z j) := by
    have hFd : DifferentiableAt ℝ F z := (hFcont.contDiffAt).differentiableAt (by norm_num)
    rw [htrace F z hFd]
    simp_rw [hFpartial z hz]
  have hcastDeriv (z d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (a w : ℂ)) z d = (fderiv ℝ a z d : ℂ) := by
    have hdiff := (ha.contDiffAt (x := z)).differentiableAt (by norm_num)
    have h := (Complex.ofRealCLM.hasFDerivAt.comp z hdiff.hasFDerivAt).fderiv
    change fderiv ℝ (Complex.ofRealCLM ∘ a) z d = _
    simpa using congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
  have hrealPartial (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      chartPartialZComplex (fun w ↦ (a w : ℂ)) z j = chartPartialZ a z j := by
    simp [chartPartialZComplex, chartPartialZ, hcastDeriv]
  have hdetEqReal (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      (G z).det = (RCLike.re (G z).det : ℂ) := by
    apply Complex.ext
    · rfl
    · simp [hdetReal z hz]
  have hgradContract (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      ∑ j, chartPartialZ f z j * q z j =
        (G z).det *
          Matrix.trace ((G z)⁻¹ *
            Matrix.vecMulVec (chartPartialZ f z) (chartPartialBar v z)) := by
    simp_rw [q, C]
    calc
      _ = ∑ j, ∑ k, chartPartialZ f z j *
          ((G z).det * (G z)⁻¹ k j * chartPartialBar v z k) := by
        simp [Finset.mul_sum]
      _ = ∑ j, ∑ k, (G z).det *
          ((G z)⁻¹ k j * chartPartialZ f z j * chartPartialBar v z k) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ∑ j, (G z).det * ∑ k,
          (G z)⁻¹ k j * chartPartialZ f z j * chartPartialBar v z k := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.mul_sum]
      _ = (G z).det * ∑ j, ∑ k,
          (G z)⁻¹ k j * chartPartialZ f z j * chartPartialBar v z k := by
        rw [← Finset.mul_sum]
      _ = (G z).det *
          Matrix.trace ((G z)⁻¹ *
            Matrix.vecMulVec (chartPartialZ f z) (chartPartialBar v z)) := by
        congr 1
        simp [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have hcastPartial (f : EuclideanSpace ℂ (Fin n) → ℝ)
      (hf : ContDiff ℝ 1 f) (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      chartPartialZComplex (fun w ↦ (f w : ℂ)) z j = chartPartialZ f z j := by
    have hcastDeriv (d : EuclideanSpace ℂ (Fin n)) :
        fderiv ℝ (fun w ↦ (f w : ℂ)) z d = (fderiv ℝ f z d : ℂ) := by
      have hdiff := (hf.contDiffAt (x := z)).differentiableAt (by norm_num)
      have h := (Complex.ofRealCLM.hasFDerivAt.comp z hdiff.hasFDerivAt).fderiv
      change fderiv ℝ (Complex.ofRealCLM ∘ f) z d = _
      simpa using congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
    simp [chartPartialZComplex, chartPartialZ, hcastDeriv]
  have hgradSplit (z : EuclideanSpace ℂ (Fin n)) :
      chartGradientPair G a v z =
        χ z * chartGradientPair G u v z + u z * chartGradientPair G χ v z := by
    have hχdiff : DifferentiableAt ℝ (fun w ↦ (χ w : ℂ)) z :=
      Complex.ofRealCLM.differentiableAt.comp z
        ((hχ.contDiffAt (x := z)).differentiableAt (by norm_num))
    have hudiff : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z :=
      Complex.ofRealCLM.differentiableAt.comp z
        ((hu.contDiffAt (x := z)).differentiableAt (by norm_num))
    have hmul (j : Fin n) :
        chartPartialZ a z j =
          χ z * chartPartialZ u z j + u z * chartPartialZ χ z j := by
      rw [← hcastPartial a (hχ.of_le (by norm_num) |>.mul (hu.of_le (by norm_num))) z j]
      have hfun : (fun w ↦ (a w : ℂ)) =
          fun w ↦ (χ w : ℂ) * (u w : ℂ) := by
        funext w
        simp [a]
      rw [hfun, chartPartialZComplex_mul hχdiff hudiff j,
        hcastPartial u (hu.of_le (by norm_num)) z j,
        hcastPartial χ (hχ.of_le (by norm_num)) z j]
      ring
    have hmat : Matrix.vecMulVec (chartPartialZ a z) (chartPartialBar v z) =
        (χ z : ℂ) • Matrix.vecMulVec (chartPartialZ u z) (chartPartialBar v z) +
          (u z : ℂ) • Matrix.vecMulVec (chartPartialZ χ z) (chartPartialBar v z) := by
      ext i j
      change chartPartialZ a z i * chartPartialBar v z j = _
      rw [hmul i]
      simp [Matrix.vecMulVec]
      ring
    simp only [chartGradientPair]
    rw [hmat]
    simp [Matrix.mul_add, Matrix.trace_add, Complex.mul_re]
  have hweightedGrad (f : EuclideanSpace ℂ (Fin n) → ℝ)
      (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      RCLike.re (G z).det * chartGradientPair G f v z =
        RCLike.re (∑ j, chartPartialZ f z j * q z j) := by
    have h := congrArg RCLike.re (hgradContract f z hz)
    rw [hdetEqReal z hz] at h
    simpa [chartGradientPair, Complex.mul_re] using h.symm
  have hqpartial (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (j : Fin n) :
      chartPartialZComplex (fun w ↦ q w j) z j =
        ∑ k, (chartPartialZComplex (fun w ↦ C w k j) z j * chartPartialBar v z k +
          C z k j * complexHessian v z j k) := by
    have htermDiff (k : Fin n) :
        DifferentiableAt ℝ (fun w ↦ C w k j * chartPartialBar v w k) z :=
      (hCdiff z hz k j).mul (hbarDiff z k)
    have hderivSum :
        fderiv ℝ (fun w ↦ ∑ k, C w k j * chartPartialBar v w k) z =
          ∑ k, fderiv ℝ (fun w ↦ C w k j * chartPartialBar v w k) z := by
      rw [fderiv_fun_sum (u := Finset.univ) (by intro k hk; exact htermDiff k)]
    have hsum : chartPartialZComplex (fun w ↦ q w j) z j =
        ∑ k, chartPartialZComplex (fun w ↦ C w k j * chartPartialBar v w k) z j := by
      unfold chartPartialZComplex q
      rw [hderivSum]
      simp only [_root_.sum_apply]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [chartPartialZComplex_mul (hCdiff z hz k j) (hbarDiff z k) j, hpartial z j k]
  have hcofactorZero (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (k : Fin n) :
      ∑ j, chartPartialZComplex (fun w ↦ C w k j) z j = 0 := by
    simpa [C] using hdiv z hz k
  have hqdiv (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      ∑ j, chartPartialZComplex (fun w ↦ q w j) z j =
        (G z).det * ((G z)⁻¹ * complexHessian v z).trace := by
    let dC := fun k j ↦ chartPartialZComplex (fun w ↦ C w k j) z j
    let H := complexHessian v z
    have hcoef : (∑ k, (∑ j, dC k j) * chartPartialBar v z k) = 0 := by
      simp_rw [dC, hcofactorZero z hz]
      simp
    have hmatrix : Matrix.trace ((G z)⁻¹ * H) =
        ∑ k, ∑ j, (G z)⁻¹ k j * H j k := by
      simp [Matrix.trace, Matrix.mul_apply]
    calc
      _ = (∑ k, ∑ j, dC k j * chartPartialBar v z k) +
          ∑ j, ∑ k, C z k j * H j k := by
        simp_rw [hqpartial z hz]
        simp_rw [Finset.sum_add_distrib]
        rw [Finset.sum_comm]
      _ = (∑ k, (∑ j, dC k j) * chartPartialBar v z k) +
          ∑ j, ∑ k, C z k j * H j k := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.sum_mul]
      _ = ∑ j, ∑ k, C z k j * H j k := by rw [hcoef, zero_add]
      _ = (G z).det * ∑ k, ∑ j, (G z)⁻¹ k j * H j k := by
        simp_rw [C]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc]
        simp_rw [← Finset.mul_sum]
      _ = (G z).det * Matrix.trace ((G z)⁻¹ * H) := by rw [hmatrix]
      _ = _ := by simp [H]
  have hFdivExact (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      chartDivergence F z =
        (2 : ℝ) ^ n * RCLike.re (G z).det * a z *
            RCLike.re (((G z)⁻¹ * complexHessian v z).trace) +
          (2 : ℝ) ^ n * RCLike.re (G z).det * chartGradientPair G a v z := by
    let s : ℝ := (2 : ℝ) ^ n / 2
    have hsum :
        ∑ j ∈ Finset.univ, RCLike.re
          (chartPartialZ a z j * ((s : ℂ) * q z j) +
            (a z : ℂ) * (s : ℂ) * chartPartialZComplex (fun w ↦ q w j) z j) =
          RCLike.re ((s : ℂ) * (∑ j, chartPartialZ a z j * q z j) +
            (a z : ℂ) * (s : ℂ) * (∑ j, chartPartialZComplex (fun w ↦ q w j) z j)) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum, Complex.mul_re]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hscaleC : ((2 : ℝ) ^ n / 2 : ℂ) = (s : ℂ) := by simp [s]
    rw [hFdivQ z hz]
    simp_rw [hrealPartial z]
    simp_rw [hscaleC]
    rw [hsum, hgradContract a z hz, hqdiv z hz, hdetEqReal z hz]
    simp [chartGradientPair, Complex.mul_re]
    ring
  have hweightedHessian (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      RCLike.re (G z).det * RCLike.re (((G z)⁻¹ * complexHessian v z).trace) =
        RCLike.re (∑ j, chartPartialZComplex (fun w ↦ q w j) z j) := by
    rw [hqdiv z hz, hdetEqReal z hz]
    simp
  have hFdivThree (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
      chartDivergence F z =
        (2 : ℝ) ^ n * a z * RCLike.re (∑ j, chartPartialZComplex (fun w ↦ q w j) z j) +
          (2 : ℝ) ^ n * χ z * RCLike.re (∑ j, chartPartialZ u z j * q z j) +
          (2 : ℝ) ^ n * u z * RCLike.re (∑ j, chartPartialZ χ z j * q z j) := by
    rw [hFdivExact z hz]
    calc
      _ = (2 : ℝ) ^ n * a z *
            (RCLike.re (G z).det * RCLike.re (((G z)⁻¹ * complexHessian v z).trace)) +
          (2 : ℝ) ^ n * RCLike.re (G z).det *
            (χ z * chartGradientPair G u v z + u z * chartGradientPair G χ v z) := by
        rw [hgradSplit z]
        ring
      _ = (2 : ℝ) ^ n * a z *
            (RCLike.re (G z).det * RCLike.re (((G z)⁻¹ * complexHessian v z).trace)) +
          (2 : ℝ) ^ n * χ z * (RCLike.re (G z).det * chartGradientPair G u v z) +
          (2 : ℝ) ^ n * u z * (RCLike.re (G z).det * chartGradientPair G χ v z) := by
        ring
      _ = _ := by
        rw [hweightedHessian z hz, ← hweightedGrad u z hz, ← hweightedGrad χ z hz]
  let J0 (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
    (2 : ℝ) ^ n * a z * RCLike.re (∑ j, chartPartialZComplex (fun w ↦ q w j) z j)
  let J1 (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
    (2 : ℝ) ^ n * χ z * RCLike.re (∑ j, chartPartialZ u z j * q z j)
  let J2 (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
    (2 : ℝ) ^ n * u z * RCLike.re (∑ j, chartPartialZ χ z j * q z j)
  have hJ0Compact : HasCompactSupport J0 := by
    apply HasCompactSupport.intro hχcompact.isCompact
    intro z hz
    have hnotA : z ∉ tsupport a := fun hzA ↦
      hz ((tsupport_mul_subset_left (f := χ) (g := u)) hzA)
    have ha0 : a z = 0 := by
      by_contra hne
      exact hnotA (subset_tsupport _ hne)
    simp [J0, ha0]
  have hJ1Compact : HasCompactSupport J1 := by
    apply HasCompactSupport.intro hχcompact.isCompact
    intro z hz
    have hχ0 : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [J1, hχ0]
  have hJ2Compact : HasCompactSupport J2 := by
    apply HasCompactSupport.intro hχcompact.isCompact
    intro z hz
    have hfd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hz
    simp [J2, chartPartialZ, hfd]
  have hsumContAt {β : Type} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
      (s : Finset (Fin n)) (g : Fin n → EuclideanSpace ℂ (Fin n) → β)
      (z : EuclideanSpace ℂ (Fin n))
      (hg : ∀ i ∈ s, ContinuousAt (g i) z) :
      ContinuousAt (fun w ↦ ∑ i ∈ s, g i w) z := by
    classical
    revert hg
    induction s using Finset.induction_on with
    | empty =>
        intro hg
        simpa using (continuousAt_const : ContinuousAt (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : β)) z)
    | @insert i s hi ih =>
        intro hg
        have hfun : (fun w ↦ Finset.sum (insert i s) (fun j ↦ g j w)) =
            fun w ↦ g i w + Finset.sum s (fun j ↦ g j w) := by
          funext w
          rw [Finset.sum_insert hi]
        rw [hfun]
        exact (hg i (Finset.mem_insert_self _ _)).add
          (ih fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))
  have hqPartialContinuousAt (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) (j : Fin n) :
      ContinuousAt (fun w ↦ chartPartialZComplex (fun y ↦ q y j) w j) z := by
    have hfd := (hqContDiffAt z hz j).continuousAt_fderiv (by norm_num)
    have hdir (d : EuclideanSpace ℂ (Fin n)) :
        ContinuousAt (fun w ↦ fderiv ℝ (fun y ↦ q y j) w d) z :=
      hfd.clm_apply continuousAt_const
    unfold chartPartialZComplex
    fun_prop
  have hpartialZContinuousAt (f : EuclideanSpace ℂ (Fin n) → ℝ)
      (hf : ContDiff ℝ ∞ f) (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      ContinuousAt (fun w ↦ chartPartialZ f w j) z := by
    have hle : (2 : ℕ∞ω) ≤ ∞ := by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top
    have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) z :=
      (hf.contDiffAt (x := z)).fderiv_right (m := 1) hle
    have hcont := hfd.continuousAt
    have hdir (d : EuclideanSpace ℂ (Fin n)) :
        ContinuousAt (fun w ↦ fderiv ℝ f w d) z := hcont.clm_apply continuousAt_const
    unfold chartPartialZ
    fun_prop
  have hJ0At (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) : ContinuousAt J0 z := by
    have hsum : ContinuousAt (fun w ↦ ∑ j, chartPartialZComplex (fun y ↦ q y j) w j) z := by
      simpa using hsumContAt (β := ℂ) Finset.univ
        (fun j w ↦ chartPartialZComplex (fun y ↦ q y j) w j) z
        (fun j hj ↦ hqPartialContinuousAt z hz j)
    change ContinuousAt (fun w ↦ (2 : ℝ) ^ n * a w *
      RCLike.re (∑ j, chartPartialZComplex (fun y ↦ q y j) w j)) z
    change ContinuousAt (fun w ↦ (2 : ℝ) ^ n * (χ w * u w) *
      RCLike.re (∑ j, chartPartialZComplex (fun y ↦ q y j) w j)) z
    have hχcont := (hχ.contDiffAt (x := z)).continuousAt
    have hucont := (hu.contDiffAt (x := z)).continuousAt
    fun_prop
  have hJ1At (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) : ContinuousAt J1 z := by
    have hsum : ContinuousAt (fun w ↦ ∑ j, chartPartialZ u w j * q w j) z := by
      simpa using hsumContAt (β := ℂ) Finset.univ (fun j w ↦ chartPartialZ u w j * q w j) z
        (fun j hj ↦ (hpartialZContinuousAt u hu z j).mul ((hqContDiffAt z hz j).continuousAt))
    change ContinuousAt (fun w ↦ (2 : ℝ) ^ n * χ w *
      RCLike.re (∑ j, chartPartialZ u w j * q w j)) z
    have hχcont := (hχ.contDiffAt (x := z)).continuousAt
    fun_prop
  have hJ2At (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) : ContinuousAt J2 z := by
    have hsum : ContinuousAt (fun w ↦ ∑ j, chartPartialZ χ w j * q w j) z := by
      simpa using hsumContAt (β := ℂ) Finset.univ (fun j w ↦ chartPartialZ χ w j * q w j) z
        (fun j hj ↦ (hpartialZContinuousAt χ hχ z j).mul ((hqContDiffAt z hz j).continuousAt))
    change ContinuousAt (fun w ↦ (2 : ℝ) ^ n * u w *
      RCLike.re (∑ j, chartPartialZ χ w j * q w j)) z
    have hucont := (hu.contDiffAt (x := z)).continuousAt
    fun_prop
  have hJ0Cont : Continuous J0 := by
    apply continuous_iff_continuousAt.2
    intro z
    by_cases hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
    · exact hJ0At z hz
    · have hnotχ : z ∉ tsupport χ := fun hzχ ↦ hz (hχsupport hzχ)
      have hnotA : z ∉ tsupport a := fun hzA ↦
        hnotχ ((tsupport_mul_subset_left (f := χ) (g := u)) hzA)
      have hzero : (fun w ↦ J0 w) =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq).mp hnotA] with w hw
        simp [J0, a, hw]
      exact (continuousAt_const : ContinuousAt (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : ℝ)) z)
        |>.congr_of_eventuallyEq hzero
  have hJ1Cont : Continuous J1 := by
    apply continuous_iff_continuousAt.2
    intro z
    by_cases hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
    · exact hJ1At z hz
    · have hzero : (fun w ↦ J1 w) =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq).mp
          (fun hzχ ↦ hz (hχsupport hzχ))] with w hw
        simp [J1, hw]
      exact (continuousAt_const : ContinuousAt (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : ℝ)) z)
        |>.congr_of_eventuallyEq hzero
  have hJ2Cont : Continuous J2 := by
    apply continuous_iff_continuousAt.2
    intro z
    by_cases hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
    · exact hJ2At z hz
    · have hnotχ : z ∉ tsupport χ := fun hzχ ↦ hz (hχsupport hzχ)
      have hzero : (fun w ↦ J2 w) =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hnotχ] with w hw
        have hfd := fderiv_of_notMem_tsupport (𝕜 := ℝ) hw
        simp [J2, chartPartialZ, hfd]
      exact (continuousAt_const : ContinuousAt (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : ℝ)) z)
        |>.congr_of_eventuallyEq hzero
  have hderivCont : Continuous (fderiv ℝ F) := by
    exact continuous_iff_continuousAt.mpr fun z ↦
      (hFcont.contDiffAt (x := z)).continuousAt_fderiv (by norm_num)
  have hFcoordDiff (z d : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      fderiv ℝ (fun w ↦ (F w).ofLp j) z d = (fderiv ℝ F z d).ofLp j := by
    let e : EuclideanSpace ℂ (Fin n) →L[ℝ] (Fin n → ℂ) :=
      (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap.restrictScalars ℝ
    have hFdiff : DifferentiableAt ℝ F z :=
      (hFcont.contDiffAt (x := z)).differentiableAt (by norm_num)
    have hFpi : DifferentiableAt ℝ (fun w ↦ (F w).ofLp) z := by
      change DifferentiableAt ℝ (fun w ↦ e (F w)) z
      exact e.differentiableAt.comp z hFdiff
    have hcomp : fderiv ℝ (fun w ↦ (F w).ofLp) z = e.comp (fderiv ℝ F z) := by
      change fderiv ℝ (fun w ↦ e (F w)) z = _
      exact (e.hasFDerivAt.comp z hFdiff.hasFDerivAt).fderiv
    have h := fderiv_apply hFpi j
    rw [hcomp] at h
    simpa [e, EuclideanSpace.equiv] using
      congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
  have hpartCont (j : Fin n) :
      Continuous (fun z ↦ chartPartialZComplex (fun w ↦ (F w).ofLp j) z j) := by
    have hdir (d : EuclideanSpace ℂ (Fin n)) :
        Continuous (fun z ↦ fderiv ℝ F z d |>.ofLp j) := by
      exact (continuous_apply j).comp
        ((EuclideanSpace.equiv (Fin n) ℂ).continuous.comp
          (hderivCont.clm_apply continuous_const))
    have hfun : (fun z ↦ chartPartialZComplex (fun w ↦ (F w).ofLp j) z j) =
        fun z ↦ (((fderiv ℝ F z (EuclideanSpace.single j 1)).ofLp j -
          Complex.I * (fderiv ℝ F z (Complex.I • EuclideanSpace.single j 1)).ofLp j) / 2) := by
      funext z
      simp [chartPartialZComplex, hFcoordDiff]
    rw [hfun]
    fun_prop
  have hdivCont : Continuous (chartDivergence F) := by
    have hfun : chartDivergence F = fun z ↦
        2 * ∑ j, RCLike.re (chartPartialZComplex (fun w ↦ (F w).ofLp j) z j) := by
      funext z
      exact htrace F z ((hFcont.contDiffAt (x := z)).differentiableAt (by norm_num))
    rw [hfun]
    exact continuous_const.mul (continuous_finsetSum Finset.univ fun j hj ↦
      Complex.continuous_re.comp (hpartCont j))
  have hdivZero (z : EuclideanSpace ℂ (Fin n)) (hnotF : z ∉ tsupport F) :
      chartDivergence F z = 0 := by
    rw [chartDivergence]
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnotF]
    simp
  have hdivCompact : HasCompactSupport (chartDivergence F) :=
    HasCompactSupport.intro hχcompact.isCompact (fun z hz ↦
      hdivZero z (fun hzF ↦ hz (hFsupport z hzF)))
  have hdivInt : Integrable (chartDivergence F)
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) :=
    hdivCont.integrable_of_hasCompactSupport hdivCompact
  have hJ0Int : Integrable J0
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) :=
    hJ0Cont.integrable_of_hasCompactSupport hJ0Compact
  have hJ1Int : Integrable J1
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) :=
    hJ1Cont.integrable_of_hasCompactSupport hJ1Compact
  have hJ2Int : Integrable J2
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) :=
    hJ2Cont.integrable_of_hasCompactSupport hJ2Compact
  have hpoint (z : EuclideanSpace ℂ (Fin n)) :
      chartDivergence F z = (J0 z + J1 z) + J2 z := by
    by_cases hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
    · simpa [J0, J1, J2] using hFdivThree z hz
    · have hnotχ : z ∉ tsupport χ := fun hzχ ↦ hz (hχsupport hzχ)
      have hnotA : z ∉ tsupport a := fun hzA ↦
        hnotχ ((tsupport_mul_subset_left (f := χ) (g := u)) hzA)
      have ha0 : a z = 0 := by
        by_contra hne
        exact hnotA (subset_tsupport _ hne)
      have hχ0 : χ z = 0 := image_eq_zero_of_notMem_tsupport hnotχ
      have hfdχ := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnotχ
      rw [hdivZero z (fun hzF ↦ hz (hχsupport (hFsupport z hzF)))]
      simp [J0, J1, J2, ha0, hχ0, chartPartialZ, hfdχ]
  have hdivAll :
      ∫ z, chartDivergence F z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) = 0 :=
    euclidean_integral_divergence_eq_zero hFcont hFcompact
  have hdivAllSum :
      ∫ z, ((J0 + J1) z) + J2 z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) = 0 := by
    calc
      _ = ∫ z, chartDivergence F z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z ↦ (hpoint z).symm)
      _ = 0 := hdivAll
  rw [integral_add (hJ0Int.add hJ1Int) hJ2Int] at hdivAllSum
  change (∫ z, J0 z + J1 z
    ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))) +
      ∫ z, J2 z ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) = 0 at hdivAllSum
  rw [integral_add hJ0Int hJ1Int] at hdivAllSum
  have hJ0outside (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∉ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) : J0 z = 0 := by
    have hnotχ : z ∉ tsupport χ := fun hzχ ↦ hz (hχsupport hzχ)
    have hnotA : z ∉ tsupport a := fun hzA ↦
      hnotχ ((tsupport_mul_subset_left (f := χ) (g := u)) hzA)
    have ha0 : a z = 0 := by
      by_contra hne
      exact hnotA (subset_tsupport _ hne)
    simp [J0, ha0]
  have hJ1outside (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∉ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) : J1 z = 0 := by
    have hχ0 : χ z = 0 := image_eq_zero_of_notMem_tsupport
      (fun hzχ ↦ hz (hχsupport hzχ))
    simp [J1, hχ0]
  have hJ2outside (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∉ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) : J2 z = 0 := by
    have hnotχ : z ∉ tsupport χ := fun hzχ ↦ hz (hχsupport hzχ)
    have hfdχ := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnotχ
    simp [J2, chartPartialZ, hfdχ]
  have hJ0set :
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target, J0 z
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      ∫ z, J0 z ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    exact hJ0outside
  have hJ1set :
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target, J1 z
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      ∫ z, J1 z ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    exact hJ1outside
  have hJ2set :
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target, J2 z
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      ∫ z, J2 z ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    exact hJ2outside
  have hJsum :
      (∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target, J0 z
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) +
       ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target, J1 z
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) +
       ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target, J2 z
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))) = 0 := by
    rw [hJ0set, hJ1set, hJ2set]
    exact hdivAllSum
  have hleft :
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
          (2 ^ n * RCLike.re (G z).det) * χ z * u z *
            RCLike.re ((G z)⁻¹ * complexHessian v z).trace
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
        ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target, J0 z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    apply setIntegral_congr_fun
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).measurableSet)
    intro z hz
    change (2 : ℝ) ^ n * RCLike.re (G z).det * χ z * u z *
        RCLike.re ((G z)⁻¹ * complexHessian v z).trace = J0 z
    calc
      _ = (2 : ℝ) ^ n * (χ z * u z) *
          (RCLike.re (G z).det * RCLike.re ((G z)⁻¹ * complexHessian v z).trace) := by ring
      _ = (2 : ℝ) ^ n * (χ z * u z) *
          RCLike.re (∑ j, chartPartialZComplex (fun w ↦ q w j) z j) := by
        rw [hweightedHessian z hz]
      _ = J0 z := by simp [J0, a]
  have hright1 :
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
          (2 ^ n * RCLike.re (G z).det) * χ z * chartGradientPair G u v z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
        ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target, J1 z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    apply setIntegral_congr_fun
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).measurableSet)
    intro z hz
    simp only [J1]
    rw [← hweightedGrad u z hz]
    ring
  have hright2 :
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
          (2 ^ n * RCLike.re (G z).det) * u z * chartGradientPair G χ v z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
        ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target, J2 z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    apply setIntegral_congr_fun
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).measurableSet)
    intro z hz
    simp only [J2]
    rw [← hweightedGrad χ z hz]
    ring
  rw [hleft, hright1, hright2]
  linarith
/-- Subtract the chart integration-by-parts formulas in both orders. The terms with
chartGradientPair χ remain as the cutoff-gradient residual. -/
theorem chart_integral_by_parts_comm (ω₀ : KahlerForm n M) (i : M)
    (χ u v : EuclideanSpace ℂ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hχcompact : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target) :
    (∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
      (2 ^ n * RCLike.re (ω₀.metricInChart i z).det) * χ z * u z *
        RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian v z).trace
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) -
     ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
      (2 ^ n * RCLike.re (ω₀.metricInChart i z).det) * χ z * v z *
        RCLike.re ((ω₀.metricInChart i z)⁻¹ * complexHessian u z).trace
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))) =
      (∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        (2 ^ n * RCLike.re (ω₀.metricInChart i z).det) * v z *
          chartGradientPair (ω₀.metricInChart i) χ u z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) -
       ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        (2 ^ n * RCLike.re (ω₀.metricInChart i z).det) * u z *
          chartGradientPair (ω₀.metricInChart i) χ v z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n)))) := by
  have hleft := chart_integral_by_parts (ω₀ := ω₀) i χ u v
    hχ hu hv hχcompact hχsupport
  have hright := chart_integral_by_parts (ω₀ := ω₀) i χ v u
    hχ hv hu hχcompact hχsupport
  have hpair :
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        (2 ^ n * RCLike.re (ω₀.metricInChart i z).det) * χ z *
          chartGradientPair (ω₀.metricInChart i) u v z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        (2 ^ n * RCLike.re (ω₀.metricInChart i z).det) * χ z *
          chartGradientPair (ω₀.metricInChart i) v u z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
    refine MeasureTheory.setIntegral_congr_fun
      (isOpen_extChartAt_target i).measurableSet ?_
    intro z hz
    have hs := ω₀.chartGradientPair_symm i u v hz
    change (2 ^ n * RCLike.re (ω₀.metricInChart i z).det) * χ z *
        chartGradientPair (ω₀.metricInChart i) u v z = _
    rw [hs]
  rw [hleft, hright, hpair]
  ring

/-- Change variables from a chart-volume measure with a smooth nonnegative weight to its
Euclidean chart integral. -/
theorem integral_chartVolume_withDensity (ω₀ : KahlerForm n M) (i : M)
    (r : M → ℝ)
    (hr : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ r)
    (hr_nonneg : ∀ y, 0 ≤ r y)
    (F : M → ℝ) (hF : Continuous F) :
    ∫ y, F y ∂(ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (r y)) =
      ∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        ω₀.volumeDensityInChart i z * r ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z) *
          F ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
  let ν : Measure (EuclideanSpace ℂ (Fin n)) :=
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict c.target
  let d : EuclideanSpace ℂ (Fin n) → ENNReal :=
    fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart i z)
  let ψ : M → ℝ := fun y ↦ r y * F y
  have hvolumeDensityCont : ContinuousOn (ω₀.volumeDensityInChart i) c.target := by
    change ContinuousOn (fun z ↦ (2 : ℝ)^n * (ω₀.metricInChart i z).det.re) _
    have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart i z).det) c.target := by
      classical
      simp_rw [Matrix.det_apply]
      exact continuousOn_finsetSum Finset.univ fun σ _ ↦
        continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun j _ ↦
          (ω₀.contDiffOn_metricInChart i (σ j) j).continuousOn
    exact continuousOn_const.mul <|
      Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _)
  have hsymm : AEMeasurable c.symm ν :=
    (continuousOn_extChartAt_symm i).aemeasurable
      (isOpen_extChartAt_target i).measurableSet
  have hdcont : ContinuousOn d c.target :=
    ENNReal.continuous_ofReal.continuousOn.comp hvolumeDensityCont (fun _ _ ↦ Set.mem_univ _)
  have hd : AEMeasurable d ν :=
    hdcont.aemeasurable (isOpen_extChartAt_target i).measurableSet
  have hsymm' : AEMeasurable c.symm (ν.withDensity d) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous ν d)
  have hrmeas : Measurable (fun y ↦ ENNReal.ofReal (r y)) :=
    ENNReal.measurable_ofReal.comp hr.continuous.measurable
  have hrtop : ∀ᵐ y ∂ω₀.chartVolume i, ENNReal.ofReal (r y) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hstart :
      ∫ y, F y ∂(ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (r y)) =
        ∫ y, r y * F y ∂ω₀.chartVolume i := by
    rw [integral_withDensity_eq_integral_toReal_smul hrmeas hrtop]
    congr 1
    funext y
    simp [ENNReal.toReal_ofReal, hr_nonneg y]
  calc
    ∫ y, F y ∂(ω₀.chartVolume i).withDensity (fun y ↦ ENNReal.ofReal (r y)) =
        ∫ y, ψ y ∂ω₀.chartVolume i := by simpa [ψ] using hstart
    _ = ∫ z, ψ (c.symm z) ∂(ν.withDensity d) := by
      rw [chartVolume]
      exact MeasureTheory.integral_map hsymm'
        ((hr.continuous.mul hF).aestronglyMeasurable)
    _ = ∫ z, (d z).toReal * ψ (c.symm z) ∂ν := by
      simpa only [smul_eq_mul] using
        integral_withDensity_eq_integral_toReal_smul₀ hd
          (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)
          (fun z ↦ ψ (c.symm z))
    _ = ∫ z in c.target, (d z).toReal * ψ (c.symm z)
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      simp [ν]
    _ = _ := by
      refine MeasureTheory.setIntegral_congr_fun
        (isOpen_extChartAt_target i).measurableSet ?_
      intro z hz
      have hden : (d z).toReal = ω₀.volumeDensityInChart i z := by
        simp [d, ENNReal.toReal_ofReal,
          le_of_lt (ω₀.volumeDensityInChart_pos i hz)]
      change (d z).toReal * ψ (c.symm z) = _
      rw [hden, show ψ (c.symm z) = r (c.symm z) * F (c.symm z) by rfl]
      ring

/-- A chart cutoff-gradient term is the global mixed polarization integrated against the
Kähler volume. The extension witness also supplies the two chart functions needed by the
coordinate Green formula. -/
theorem exists_chart_cutoff_extensions_with_residual (ω₀ : KahlerForm n M)
    (i : M) (r f g : M → ℝ)
    (hr : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ r)
    (hsource : tsupport r ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) i).source)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g)
    (hF : Continuous (fun y ↦ f y *
      ((relTrace (ω₀ y) (mdWedgeDBar n (r + g) y) -
        relTrace (ω₀ y) (mdWedgeDBar n r y) -
        relTrace (ω₀ y) (mdWedgeDBar n g y)) / 2)))
    (hG : Continuous (fun y ↦ g y *
      ((relTrace (ω₀ y) (mdWedgeDBar n (r + f) y) -
        relTrace (ω₀ y) (mdWedgeDBar n r y) -
        relTrace (ω₀ y) (mdWedgeDBar n f y)) / 2))) :
    ∃ (χ β : EuclideanSpace ℂ (Fin n) → ℝ)
      (O : Set (EuclideanSpace ℂ (Fin n)))
      (U V : EuclideanSpace ℂ (Fin n) → ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
        tsupport χ ⊆
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i) '' tsupport r ∧
      (∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        χ z = r ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) ∧
      ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
        tsupport β ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
      IsOpen O ∧
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i '' tsupport r) ⊆ O ∧
        O ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
        (∀ z ∈ O, β z = 1) ∧
      ContDiff ℝ ∞ U ∧
        EqOn U (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) O ∧
      ContDiff ℝ ∞ V ∧
        EqOn V (fun z ↦ g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) O ∧
      (∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        ω₀.volumeDensityInChart i z * U z *
          chartGradientPair (ω₀.metricInChart i) χ V z
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
       ∫ y, f y *
          ((relTrace (ω₀ y) (mdWedgeDBar n (r + g) y) -
            relTrace (ω₀ y) (mdWedgeDBar n r y) -
            relTrace (ω₀ y) (mdWedgeDBar n g y)) / 2)
          ∂ω₀.volume) ∧
      (∫ z in (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        ω₀.volumeDensityInChart i z * V z *
          chartGradientPair (ω₀.metricInChart i) χ U z
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
       ∫ y, g y *
          ((relTrace (ω₀ y) (mdWedgeDBar n (r + f) y) -
            relTrace (ω₀ y) (mdWedgeDBar n r y) -
            relTrace (ω₀ y) (mdWedgeDBar n f y)) / 2)
          ∂ω₀.volume) := by
  obtain ⟨χ, β, O, U, V, hχ, hχcompact, hχtarget, hχK, hχeq, hβ, hβcompact,
    hβtarget, hOopen, hOK, hOtarget, hβone, hU, hUEq, hV, hVEq⟩ :=
      exists_chart_cutoff_extensions i r f g hr hsource hf hg
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
  let P : (M → ℝ) → M → ℝ := fun v y ↦
    (relTrace (ω₀ y) (mdWedgeDBar n (r + v) y) -
      relTrace (ω₀ y) (mdWedgeDBar n r y) -
      relTrace (ω₀ y) (mdWedgeDBar n v y)) / 2
  have hcutoffResidual (A B : EuclideanSpace ℂ (Fin n) → ℝ) (u v : M → ℝ)
      (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
      (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v)
      (hUeq : EqOn A (fun z ↦ u (c.symm z)) O)
      (hVeq : EqOn B (fun z ↦ v (c.symm z)) O)
      (hF : Continuous (fun y ↦ u y * P v y)) :
      ∫ z in c.target, ω₀.volumeDensityInChart i z * A z *
          chartGradientPair (ω₀.metricInChart i) χ B z
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
        ∫ y, u y * P v y ∂ω₀.volume := by
    have hPzero : ∀ y ∉ (chartAt (EuclideanSpace ℂ (Fin n)) i).source, P v y = 0 := by
      intro y hy
      apply chartPolarization_zero_of_not_source ω₀ i r v hr hv
      intro hySupport
      exact hy (hsource hySupport)
    have hglobal :
        ∫ y, u y * P v y ∂ω₀.chartVolume i = ∫ y, u y * P v y ∂ω₀.volume := by
      let ν : Measure (EuclideanSpace ℂ (Fin n)) :=
        (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))).restrict c.target
      let d : EuclideanSpace ℂ (Fin n) → ENNReal :=
        fun z ↦ ENNReal.ofReal (ω₀.volumeDensityInChart i z)
      have hvolumeDensityCont : ContinuousOn (ω₀.volumeDensityInChart i) c.target := by
        change ContinuousOn (fun z ↦ (2 : ℝ)^n * (ω₀.metricInChart i z).det.re) _
        have hdet : ContinuousOn (fun z ↦ (ω₀.metricInChart i z).det) c.target := by
          classical
          simp_rw [Matrix.det_apply]
          exact continuousOn_finsetSum Finset.univ fun σ _ ↦
            continuousOn_const.smul <| continuousOn_finsetProd Finset.univ fun j _ ↦
              (ω₀.contDiffOn_metricInChart i (σ j) j).continuousOn
        exact continuousOn_const.mul <|
          Complex.continuous_re.continuousOn.comp hdet (fun _ _ ↦ Set.mem_univ _)
      have hsymm : AEMeasurable c.symm ν :=
        (continuousOn_extChartAt_symm i).aemeasurable
          (isOpen_extChartAt_target i).measurableSet
      have hdcont : ContinuousOn d c.target :=
        ENNReal.continuous_ofReal.continuousOn.comp hvolumeDensityCont
          (fun _ _ ↦ Set.mem_univ _)
      have hd : AEMeasurable d ν :=
        hdcont.aemeasurable (isOpen_extChartAt_target i).measurableSet
      have hsymm' : AEMeasurable c.symm (ν.withDensity d) :=
        hsymm.mono_ac (withDensity_absolutelyContinuous ν d)
      have haesource : ∀ᵐ y ∂ω₀.chartVolume i,
          y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
        have htargetAE : ∀ᵐ z ∂(ν.withDensity d), z ∈ c.target := by
          have hνtarget : ∀ᵐ z ∂ν, z ∈ c.target := by
            dsimp [ν]
            exact MeasureTheory.ae_restrict_mem
              (isOpen_extChartAt_target i).measurableSet
          rw [MeasureTheory.ae_withDensity_iff' hd]
          filter_upwards [hνtarget] with z hz _
          exact hz
        rw [chartVolume]
        exact (MeasureTheory.ae_map_iff hsymm'
          (chartAt (EuclideanSpace ℂ (Fin n)) i).open_source.measurableSet).2
          (htargetAE.mono fun z hz ↦ by
            have hz' : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target := by
              simpa [c] using hz
            have hsource' := c.map_target hz'
            rw [extChartAt_source] at hsource'
            exact hsource')
      have hrestrict : (ω₀.chartVolume i).restrict
          (chartAt (EuclideanSpace ℂ (Fin n)) i).source = ω₀.chartVolume i :=
        Measure.restrict_eq_self_of_ae_mem haesource
      calc
        _ = ∫ y, u y * P v y ∂(ω₀.chartVolume i).restrict
            (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by rw [hrestrict]
        _ = ∫ y, u y * P v y ∂ω₀.volume.restrict
            (chartAt (EuclideanSpace ℂ (Fin n)) i).source := by
          exact ω₀.integral_chartVolume_restrict_chartSource_eq_integral_volume_restrict i
            (fun y ↦ u y * P v y)
        _ = ∫ y in (chartAt (EuclideanSpace ℂ (Fin n)) i).source,
            u y * P v y ∂ω₀.volume := rfl
        _ = _ := MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy ↦ by simp [P, hPzero y hy])
    have hchange := integral_chartVolume_withDensity ω₀ i (fun _ ↦ (1 : ℝ))
      contMDiff_const (fun _ ↦ by norm_num) (fun y ↦ u y * P v y) hF
    have hcoord :
        ∫ y, u y * P v y ∂ω₀.chartVolume i =
          ∫ z in c.target, ω₀.volumeDensityInChart i z * u (c.symm z) * P v (c.symm z)
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      simpa [c, P, mul_assoc] using hchange
    have hpoint {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ c.target) :
        ω₀.volumeDensityInChart i z * A z *
            chartGradientPair (ω₀.metricInChart i) χ B z =
          ω₀.volumeDensityInChart i z * u (c.symm z) * P v (c.symm z) := by
      by_cases hzO : z ∈ O
      · have hUeq' : A =ᶠ[nhds z] fun w ↦ u (c.symm w) := by
          filter_upwards [hOopen.mem_nhds hzO] with w hw
          exact hUeq hw
        have hVeq' : B =ᶠ[nhds z] fun w ↦ v (c.symm w) := by
          filter_upwards [hOopen.mem_nhds hzO] with w hw
          exact hVeq hw
        have hχeq' : χ =ᶠ[nhds z] fun w ↦ r (c.symm w) := by
          filter_upwards [(isOpen_extChartAt_target i).mem_nhds hz] with w hw
          exact hχeq w hw
        have hfdU := hUeq'.fderiv_eq (𝕜 := ℝ)
        have hfdV := hVeq'.fderiv_eq (𝕜 := ℝ)
        have hfdχ := hχeq'.fderiv_eq (𝕜 := ℝ)
        have hpair : chartGradientPair (ω₀.metricInChart i) χ B z =
            chartGradientPair (ω₀.metricInChart i)
              (fun w ↦ r (c.symm w)) (fun w ↦ v (c.symm w)) z := by
          unfold chartGradientPair chartPartialZ chartPartialBar
          rw [hfdχ, hfdV]
        have hpol := ω₀.chartGradientPair_polarization_relTrace i r v hr hv hz
        have hpairP : P v (c.symm z) =
            chartGradientPair (ω₀.metricInChart i)
              (fun w ↦ r (c.symm w)) (fun w ↦ v (c.symm w)) z := by
          simpa only [P, c] using hpol.symm
        have hUval : A z = u (c.symm z) := hUeq hzO
        rw [hUval, hpair, hpairP]
      · have hzχ : z ∉ tsupport χ := by
          intro hzχ
          exact hzO (hOK (hχK hzχ))
        have hχzero : χ =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
          filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hzχ] with w hw
          by_contra hne
          exact hw (subset_tsupport _ hne)
        have hfdχ := hχzero.fderiv_eq (𝕜 := ℝ)
        have hpair : chartGradientPair (ω₀.metricInChart i) χ B z = 0 := by
          have hdz : chartPartialZ χ z = 0 := by
            funext j
            unfold chartPartialZ
            simp [hfdχ]
          unfold chartGradientPair
          rw [hdz]
          simp
        have hnotSupport : c.symm z ∉ tsupport r := by
          intro hy
          apply hzO
          apply hOK
          have hzImage : z ∈ c '' tsupport r := by
            refine ⟨c.symm z, hy, ?_⟩
            exact c.right_inv hz
          exact hzImage
        have hPz : P v (c.symm z) = 0 := by
          apply chartPolarization_zero_of_not_source ω₀ i r v hr hv
          exact hnotSupport
        simp [hpair, hPz]
    have hcoord' :
        ∫ z in c.target, ω₀.volumeDensityInChart i z * A z *
            chartGradientPair (ω₀.metricInChart i) χ B z
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
          ∫ z in c.target, ω₀.volumeDensityInChart i z * u (c.symm z) * P v (c.symm z)
            ∂(MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      refine MeasureTheory.setIntegral_congr_fun
        (isOpen_extChartAt_target i).measurableSet ?_
      intro z hz
      exact hpoint hz
    exact hcoord'.trans (hcoord.symm.trans hglobal)
  refine ⟨χ, β, O, U, V, hχ, hχcompact, hχtarget, hχK, hχeq, hβ, hβcompact,
    hβtarget, hOopen, hOK, hOtarget, hβone, hU, hUEq, hV, hVEq, ?_, ?_⟩
  · exact hcutoffResidual U V f g hf hg hUEq hVEq hF
  · exact hcutoffResidual V U g f hg hf hVEq hUEq hG

end KahlerForm
