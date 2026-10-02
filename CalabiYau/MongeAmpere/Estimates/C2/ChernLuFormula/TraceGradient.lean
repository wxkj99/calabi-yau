module

public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalFrameJets
import CalabiYau.MongeAmpere.Estimates.C2.NormalFrameGradient
import CalabiYau.MongeAmpere.Estimates.C2.RelativeTraceRegularity

/-!
# Normalized gradient term of the relative trace

This theorem computes the gradient contribution that the scalar chain rule for `log tr_{ω₀}ω₁`
subtracts.  At the center of a simultaneous normal frame, the first derivative of the trace is the
trace of the first derivative of the varying metric, namely `∑ⱼ Tₚⱼⱼ`.  The inverse varying metric
weights its squared norm by `λₚ⁻¹`.

The formula is stated already divided by the square of the trace.  This is exactly the normalized
quantity entering `Δ log u = (Δu)/u - |∂u|²/u²`, and records both powers of the trace denominator
without leaving algebraic assembly to the larger expansion theorem.  The denominator sum is the forward
relative trace supplied by the `RelativeTrace` theorem.

The eigenvalues are positive in every nonempty dimension because the varying form is positive.  In
dimension zero, both the trace and its gradient vanish; Lean's real division-by-zero convention
makes both displayed quotients zero.  In dimension one the expression reduces to the squared single
diagonal first derivative divided by `λ²`, as expected.  A flat constant metric has zero derivative,
and a linear pullback uses `J.transpose * G * J.map star` (with `J=i` preserving the one-dimensional
unit coefficient).
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder Topology
open ContinuousAlternatingMap Filter

namespace KahlerForm

private theorem normalized_gradient_denominator_algebra
    {n : ℕ} (eigen : Fin n → ℝ) (heigen : ∀ p, 0 < eigen p)
    (z : Fin n → ℂ) :
    (∑ p, ‖z p‖ ^ 2 / eigen p) / (∑ j, eigen j) ^ 2 =
      (∑ p, ‖z p‖ ^ 2 / (eigen p * ∑ j, eigen j)) / (∑ j, eigen j) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnonempty : Nonempty (Fin n) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr hnonempty
    have hsum : 0 < ∑ j, eigen j :=
      Finset.sum_pos (fun j hj => heigen j) huniv
    have hsumne : (∑ j, eigen j) ≠ 0 := ne_of_gt hsum
    have heigne : ∀ p, eigen p ≠ 0 := fun p => ne_of_gt (heigen p)
    rw [div_eq_mul_inv, div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    field_simp [hsumne, heigne p]

private theorem chartPartialZComplex_sum
    {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : ∀ i, DifferentiableAt ℝ (f i) z) :
    chartPartialZComplex (fun w ↦ ∑ i, f i w) z p =
      ∑ i, chartPartialZComplex (f i) z p := by
  unfold chartPartialZComplex
  have hfd : fderiv ℝ (fun w ↦ ∑ i, f i w) z = ∑ i, fderiv ℝ (f i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi ↦ hf i)
  rw [hfd]
  simp only [_root_.sum_apply]
  have hsum :
      (∑ i, fderiv ℝ (f i) z (EuclideanSpace.single p 1)) -
        Complex.I * ∑ i, fderiv ℝ (f i) z (Complex.I • EuclideanSpace.single p 1) =
      ∑ i, (fderiv ℝ (f i) z (EuclideanSpace.single p 1) -
        Complex.I * fderiv ℝ (f i) z (Complex.I • EuclideanSpace.single p 1)) := by
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem chartPartialZComplex_inverse_first_jet_zero
    {n : ℕ} {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (p : Fin n)
    (hG : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z)
    (hId : G z = 1) (hunit : IsUnit (G z))
    (hfirst : ∀ a b, chartPartialZComplex (fun w ↦ G w a b) z p = 0) :
    ∀ a b, chartPartialZComplex (fun w ↦ (G w)⁻¹ a b) z p = 0 := by
  have hGdiff : ∀ a b, DifferentiableAt ℝ (fun w ↦ G w a b) z := by
    intro a b
    exact (hG a b).differentiableAt (by norm_num)
  have hinvDiff : ∀ a b, DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ a b) z := by
    intro a b
    exact KahlerForm.chartInv_differentiableAt hG hunit a b
  have hdet : DifferentiableAt ℝ (fun w ↦ (G w).det) z := by
    simp_rw [Matrix.det_apply]
    fun_prop (disch := assumption)
  have hdetne : (G z).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero
  have hdet_eventually : ∀ᶠ w in 𝓝 z, (G w).det ≠ 0 :=
    hdet.continuousAt.eventually_ne hdetne
  have hunit_eventually : ∀ᶠ w in 𝓝 z, IsUnit (G w) := by
    filter_upwards [hdet_eventually] with w hw
    exact (Matrix.isUnit_iff_isUnit_det (A := G w)).mpr (isUnit_iff_ne_zero.mpr hw)
  intro a b
  have hprod : (fun w ↦ ∑ t : Fin n, G w a t * (G w)⁻¹ t b) =ᶠ[𝓝 z]
      fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
    filter_upwards [hunit_eventually] with w hw
    have hdetw : IsUnit (G w).det := (Matrix.isUnit_iff_isUnit_det _).mp hw
    have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A a b)
      (Matrix.mul_nonsing_inv (G w) hdetw)
    simpa [Matrix.mul_apply] using h
  have hjetprod : chartPartialZComplex
      (fun w ↦ ∑ t : Fin n, G w a t * (G w)⁻¹ t b) z p = 0 := by
    unfold chartPartialZComplex
    rw [hprod.fderiv_eq (𝕜 := ℝ)]
    simp
  have hsum := chartPartialZComplex_sum
    (fun t : Fin n ↦ fun w ↦ G w a t * (G w)⁻¹ t b) z p
    (fun t ↦ (hGdiff a t).mul (hinvDiff t b))
  rw [hsum] at hjetprod
  have hterm (t : Fin n) : chartPartialZComplex
      (fun w ↦ G w a t * (G w)⁻¹ t b) z p =
        (chartPartialZComplex (fun w ↦ G w a t) z p) * (G z)⁻¹ t b +
          G z a t * chartPartialZComplex (fun w ↦ (G w)⁻¹ t b) z p := by
    exact chartPartialZComplex_mul (hGdiff a t) (hinvDiff t b) p
  rw [show (∑ t : Fin n, chartPartialZComplex
      (fun w ↦ G w a t * (G w)⁻¹ t b) z p) =
      ∑ t : Fin n, ((chartPartialZComplex (fun w ↦ G w a t) z p) *
        (G z)⁻¹ t b + G z a t * chartPartialZComplex (fun w ↦ (G w)⁻¹ t b) z p) by
      apply Finset.sum_congr rfl
      intro t ht
      exact hterm t] at hjetprod
  have hfirstzero : ∑ t : Fin n, G z a t *
      chartPartialZComplex (fun w ↦ (G w)⁻¹ t b) z p = 0 := by
    simpa [hfirst, Matrix.mul_apply] using hjetprod
  simpa [hId, Matrix.one_apply] using hfirstzero

private theorem chartPartialZComplex_trace_mul_identity
    {n : ℕ} (A B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hA : ∀ i j, DifferentiableAt ℝ (fun w ↦ A w i j) z)
    (hB : ∀ i j, DifferentiableAt ℝ (fun w ↦ B w i j) z)
    (hAvalue : A z = 1)
    (hAderiv : ∀ i j, chartPartialZComplex (fun w ↦ A w i j) z p = 0) :
    chartPartialZComplex (fun w ↦ (A w * B w).trace) z p =
      ∑ i, chartPartialZComplex (fun w ↦ B w i i) z p := by
  have htrace : (fun w ↦ (A w * B w).trace) =
      fun w ↦ ∑ i, ∑ j, A w i j * B w j i := by
    funext w
    simp [Matrix.trace, Matrix.mul_apply]
  rw [htrace]
  have hInnerDiff (i : Fin n) : DifferentiableAt ℝ
      (fun w ↦ ∑ j, A w i j * B w j i) z := by
    apply DifferentiableAt.fun_sum
    intro j hj
    exact (hA i j).mul (hB j i)
  have houter := chartPartialZComplex_sum
    (fun i w ↦ ∑ j, A w i j * B w j i) z p hInnerDiff
  rw [houter]
  apply Finset.sum_congr rfl
  intro i hi
  have hinner := chartPartialZComplex_sum
    (fun j w ↦ A w i j * B w j i) z p (fun j ↦ (hA i j).mul (hB j i))
  rw [hinner]
  simp_rw [chartPartialZComplex_mul (hA i _) (hB _ i)]
  simp only [hAderiv, zero_mul, zero_add]
  simp [hAvalue, Matrix.one_apply]

private theorem chartPartialZ_eq_chartPartialZComplex_ofReal
    {n : ℕ} (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n)
    (hu : DifferentiableAt ℝ u z) :
    chartPartialZ u z j = chartPartialZComplex (fun w ↦ (u w : ℂ)) z j := by
  have hchain := fderiv_comp (f := u) (g := Complex.ofRealCLM) (x := z)
    Complex.ofRealCLM.hasFDerivAt.differentiableAt hu
  have hderiv (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (u w : ℂ)) z v = (fderiv ℝ u z v : ℂ) := by
    have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hchain
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using h
  simp [chartPartialZ, chartPartialZComplex, hderiv]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

open scoped Topology in
private theorem frame_jacobian_det_eventually_ne_zero
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ᶠ w in 𝓝 F.center, (holomorphicJacobianMatrix F.map w).det ≠ 0 := by
  let Jreal : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w =>
    Matrix.of fun i j => fderiv ℝ F.map w (EuclideanSpace.single j 1) i
  have hFat : ContDiffAt ℝ 1 F.map F.center :=
    (F.smooth_map.contDiffAt (F.isOpen_domain.mem_nhds F.center_mem)).of_le (by norm_num)
  have hFfd : ContinuousAt (fderiv ℝ F.map) F.center :=
    hFat.continuousAt_fderiv (by norm_num)
  have hJreal : ContinuousAt Jreal F.center := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    fun_prop (disch := assumption)
  have hJeq : ∀ᶠ w in 𝓝 F.center, holomorphicJacobianMatrix F.map w = Jreal w := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    have hhol : DifferentiableAt ℂ F.map w :=
      (F.holomorphic_map w hw).differentiableAt (F.isOpen_domain.mem_nhds hw)
    have hderiv : fderiv ℝ F.map w = (fderiv ℂ F.map w).restrictScalars ℝ :=
      hhol.fderiv_restrictScalars ℝ
    ext i j
    simp [holomorphicJacobianMatrix, Jreal, EuclideanSpace.clmMatrix, hderiv]
  have hdetcont : ContinuousAt (fun w ↦ (Jreal w).det) F.center := by
    fun_prop
  have hdetval : (Jreal F.center).det ≠ 0 := by
    have h := hJeq.self_of_nhds
    rw [← h]
    exact F.jacobian_det_ne_zero
  filter_upwards [hdetcont.eventually_ne hdetval, hJeq] with w hdet hmatrix
  rw [hmatrix]
  exact hdet

private noncomputable def tangentCoordChange_complex_equiv (x y : M)
    (hyx : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source) :
    EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := by
  let C := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let D := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hxy : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hCleft (v : EuclideanSpace ℂ (Fin n)) : D (C v) = v := by
    calc
      _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := by
        exact tangentCoordChange_comp
          (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) (w := x) (x := y) (y := x)
          (z := y) ⟨⟨hyx, hxy⟩, hyx⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) hyx
  have hCright (v : EuclideanSpace ℂ (Fin n)) : C (D v) = v := by
    calc
      _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := by
        exact tangentCoordChange_comp
          (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) (w := y) (x := x) (y := y)
          (z := y) ⟨⟨hxy, hyx⟩, hxy⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) hxy
  let eLin := LinearEquiv.ofBijective (C : EuclideanSpace ℂ (Fin n) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin n)) ⟨by
        intro v w h
        calc
          v = D (C v) := (hCleft v).symm
          _ = D (C w) := congrArg D h
          _ = w := hCleft w
      , by
        intro v
        exact ⟨D v, hCright v⟩⟩
  exact eLin.toContinuousLinearEquivOfContinuous
    eLin.toLinearMap.continuous_of_finiteDimensional

private theorem relTrace_eq_chartRep
    (ω₀ ω₁ : KahlerForm n M) (x : M)
    (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
      (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) =
    RCLike.re ((ω₀.metricInChart x z)⁻¹ * ω₁.metricInChart x z).trace := by
  let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z
  have hyxR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_target hz
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [extChartAt_real_eq, ← extChartAt_source] using hyxR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  let C := tangentCoordChange_complex_equiv x y hyxC
  have hCreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (C : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    change tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ
    exact tangentCoordChange_real_eq ⟨hyxC, hyyC⟩
  have hω₀ : (ω₀ y).IsOneOne := (ContinuousAlternatingMap.isPositive_iff.mp
    (ω₀.isPositive y)).1
  have hω₁ : (ω₁ y).IsOneOne := (ContinuousAlternatingMap.isPositive_iff.mp
    (ω₁.isPositive y)).1
  have hcomp := ContinuousAlternatingMap.relTrace_compContinuousLinearMap hω₀ hω₁ C
  have hrep₀ : ω₀.toFormField.chartRep x z =
      (ω₀ y).compContinuousLinearMap
        ((C : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    change (ω₀ y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hCreal]
  have hrep₁ : ω₁.toFormField.chartRep x z =
      (ω₁ y).compContinuousLinearMap
        ((C : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    change (ω₁ y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hCreal]
  rw [← hrep₀, ← hrep₁] at hcomp
  change ContinuousAlternatingMap.relTrace (ω₀.toFormField.chartRep x z)
    (ω₁.toFormField.chartRep x z) = _ at hcomp
  change ContinuousAlternatingMap.relTrace (ω₀.toFormField y) (ω₁.toFormField y) =
    ContinuousAlternatingMap.relTrace (ω₀.toFormField.chartRep x z)
      (ω₁.toFormField.chartRep x z)
  exact hcomp.symm

private noncomputable def complexJacobian_equiv_of_det
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hdet : (EuclideanSpace.clmMatrix A).det ≠ 0) :
    EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := by
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  have hC : EuclideanSpace.clmMatrix A =
      LinearMap.toMatrix b b (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
    ext i j
    simp [EuclideanSpace.clmMatrix, LinearMap.toMatrix_apply, b,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hUnit : IsUnit (LinearMap.toMatrix b b
      (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))).det := by
    rw [← hC]
    exact isUnit_iff_ne_zero.mpr hdet
  let eLin := LinearEquiv.ofIsUnitDet (v := b) (v' := b)
    (f := (A : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) hUnit
  exact eLin.toContinuousLinearEquivOfContinuous
    eLin.toLinearMap.continuous_of_finiteDimensional

private theorem relTrace_eq_pulledBack_frame_metric
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ F.domain)
    (hdet : (holomorphicJacobianMatrix F.map w).det ≠ 0) :
    relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w)))
      (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w))) =
    RCLike.re ((pulledBackMetricInChart ω₀ x F.map w)⁻¹ *
      pulledBackMetricInChart ω₁ x F.map w).trace := by
  let z := F.map w
  let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    F.maps_into_chart w hw
  have hchart := relTrace_eq_chartRep ω₀ ω₁ x z hz
  let J : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) := fderiv ℂ F.map w
  let A := complexJacobian_equiv_of_det J hdet
  have hyxR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_target hz
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [extChartAt_real_eq, ← extChartAt_source] using hyxR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  let Cclm := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let CEquiv := tangentCoordChange_complex_equiv x y hyxC
  have hCreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      Cclm.restrictScalars ℝ := by
    change tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ
    exact tangentCoordChange_real_eq ⟨hyxC, hyyC⟩
  have htype0 : ((ω₀.toFormField y).compContinuousLinearMap
      (Cclm.restrictScalars ℝ)).IsOneOne :=
    ((ContinuousAlternatingMap.isPositive_iff.mp (ω₀.isPositive y)).1).compContinuousLinearMap CEquiv
  have htype1 : ((ω₁.toFormField y).compContinuousLinearMap
      (Cclm.restrictScalars ℝ)).IsOneOne :=
    ((ContinuousAlternatingMap.isPositive_iff.mp (ω₁.isPositive y)).1).compContinuousLinearMap CEquiv
  have hrep0 : ω₀.toFormField.chartRep x z =
      (ω₀.toFormField y).compContinuousLinearMap (Cclm.restrictScalars ℝ) := by
    change (ω₀.toFormField y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hCreal]
  have hrep1 : ω₁.toFormField.chartRep x z =
      (ω₁.toFormField y).compContinuousLinearMap (Cclm.restrictScalars ℝ) := by
    change (ω₁.toFormField y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hCreal]
  have hrepType0 : (ω₀.toFormField.chartRep x z).IsOneOne := by
    rw [hrep0]
    exact htype0
  have hrepType1 : (ω₁.toFormField.chartRep x z).IsOneOne := by
    rw [hrep1]
    exact htype1
  have hcoeff0 : ((ω₀.toFormField.chartRep x z).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix =
      pulledBackMetricInChart ω₀ x F.map w := by
    rw [ContinuousAlternatingMap.IsOneOne.coeffMatrix_compContinuousLinearMap hrepType0 A]
    rfl
  have hcoeff1 : ((ω₁.toFormField.chartRep x z).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix =
      pulledBackMetricInChart ω₁ x F.map w := by
    rw [ContinuousAlternatingMap.IsOneOne.coeffMatrix_compContinuousLinearMap hrepType1 A]
    rfl
  have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap hrepType0 hrepType1 A
  change RCLike.re (((ω₀.toFormField.chartRep x z).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix⁻¹ *
        ((ω₁.toFormField.chartRep x z).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).coeffMatrix).trace =
    RCLike.re ((ω₀.toFormField.chartRep x z).coeffMatrix⁻¹ *
      (ω₁.toFormField.chartRep x z).coeffMatrix).trace at htrace
  rw [hcoeff0, hcoeff1] at htrace
  change RCLike.re ((pulledBackMetricInChart ω₀ x F.map w)⁻¹ *
      pulledBackMetricInChart ω₁ x F.map w).trace =
    RCLike.re ((ω₀.metricInChart x z)⁻¹ * ω₁.metricInChart x z).trace at htrace
  calc
    relTrace (ω₀ y) (ω₁ y) =
        RCLike.re ((ω₀.metricInChart x z)⁻¹ * ω₁.metricInChart x z).trace := hchart
    _ = RCLike.re ((pulledBackMetricInChart ω₀ x F.map w)⁻¹ *
        pulledBackMetricInChart ω₁ x F.map w).trace := htrace.symm

open scoped Topology in
private theorem normalFrame_relative_trace_eq_pulledBack_matrix_eventually
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ∀ᶠ w in 𝓝 F.center,
      relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w)))
        (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w))) =
      RCLike.re ((pulledBackMetricInChart ω₀ x F.map w)⁻¹ *
        pulledBackMetricInChart ω₁ x F.map w).trace := by
  have hdet := frame_jacobian_det_eventually_ne_zero ω₀ ω₁ x F
  filter_upwards [F.isOpen_domain.mem_nhds F.center_mem, hdet] with w hw hdet
  exact relTrace_eq_pulledBack_frame_metric ω₀ ω₁ x F w hw hdet

private theorem pulledBackMetric_hermitian
    (metric ω₀ ω₁ : KahlerForm n M) (x : M)
    (F : YauNormalFrame ω₀ ω₁ x) (w : EuclideanSpace ℂ (Fin n))
    (hw : w ∈ F.domain) :
    (pulledBackMetricInChart metric x F.map w).IsHermitian := by
  have hz : F.map w ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    F.maps_into_chart w hw
  have hG : (metric.metricInChart x (F.map w)).PosDef := metric.posDef_metricInChart x hz
  let J := holomorphicJacobianMatrix F.map w
  have h := Matrix.isHermitian_mul_mul_conjTranspose (B := J.transpose) hG.isHermitian
  simpa [pulledBackMetricInChart, J, Matrix.conjTranspose, Matrix.transpose_map] using h

open scoped Topology in
private theorem contDiffAt_pulledBackMetric_entry
    (metric ω₀ ω₁ : KahlerForm n M) (x : M)
    (F : YauNormalFrame ω₀ ω₁ x) (i j : Fin n) :
    ContDiffAt ℝ 1 (fun w ↦ pulledBackMetricInChart metric x F.map w i j) F.center := by
  let Jreal : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w =>
    Matrix.of fun a b => fderiv ℝ F.map w (EuclideanSpace.single b 1) a
  have hFat : ContDiffAt ℝ ∞ F.map F.center :=
    F.smooth_map.contDiffAt (F.isOpen_domain.mem_nhds F.center_mem)
  have hFderiv : ContDiffAt ℝ 1 (fderiv ℝ F.map) F.center :=
    hFat.fderiv_right <| WithTop.coe_le_coe.mpr
      (show (1 + 1 : ℕ∞) ≤ ⊤ from le_top)
  have hJrealEntry (a b : Fin n) :
      ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ F.map w (EuclideanSpace.single b 1) a) F.center := by
    have hEval : ContDiffAt ℝ 1
        (fun w ↦ fderiv ℝ F.map w (EuclideanSpace.single b 1)) F.center :=
      hFderiv.clm_apply contDiffAt_const
    have hcoord : ContDiffAt ℝ 1 (fun v : EuclideanSpace ℂ (Fin n) ↦
        ((EuclideanSpace.proj (𝕜 := ℂ) a).restrictScalars ℝ) v)
        (fderiv ℝ F.map F.center (EuclideanSpace.single b 1)) := by
      exact ((EuclideanSpace.proj (𝕜 := ℂ) a).restrictScalars ℝ).contDiff.contDiffAt.of_le
        (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))
    have hcomp := hcoord.comp F.center hEval
    simpa [Function.comp_def] using hcomp
  have hJeq : ∀ᶠ w in 𝓝 F.center, holomorphicJacobianMatrix F.map w = Jreal w := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem] with w hw
    have hhol : DifferentiableAt ℂ F.map w :=
      (F.holomorphic_map w hw).differentiableAt (F.isOpen_domain.mem_nhds hw)
    have hderiv : fderiv ℝ F.map w = (fderiv ℂ F.map w).restrictScalars ℝ :=
      hhol.fderiv_restrictScalars ℝ
    ext a b
    simp [holomorphicJacobianMatrix, Jreal, EuclideanSpace.clmMatrix, hderiv]
  have hJentry (a b : Fin n) :
      ContDiffAt ℝ 1 (fun w ↦ holomorphicJacobianMatrix F.map w a b) F.center := by
    have hreal : ContDiffAt ℝ 1 (fun w ↦ Jreal w a b) F.center := by
      simpa [Jreal, Matrix.of_apply] using hJrealEntry a b
    have hevent : (fun w ↦ holomorphicJacobianMatrix F.map w a b) =ᶠ[𝓝 F.center]
        fun w ↦ Jreal w a b := hJeq.mono fun w hw ↦ congrArg (fun J ↦ J a b) hw
    exact hreal.congr_of_eventuallyEq hevent
  have hbase (a b : Fin n) :
      ContDiffAt ℝ ∞ (fun w ↦ metric.metricInChart x (F.map w) a b) F.center := by
    have hchart := metric.contDiffOn_metricInChart x a b
    have hcomp : ContDiffOn ℝ ∞ (fun w ↦ metric.metricInChart x (F.map w) a b) F.domain :=
      hchart.comp F.smooth_map (fun w hw ↦ F.maps_into_chart w hw)
    exact hcomp.contDiffAt (F.isOpen_domain.mem_nhds F.center_mem)
  have hlevel : (↑(1 : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr (by norm_num : (1 : ℕ∞) ≤ ⊤)
  have hbase1 (a b : Fin n) :
      ContDiffAt ℝ 1 (fun w ↦ metric.metricInChart x (F.map w) a b) F.center :=
    (hbase a b).of_le hlevel
  have hJstar (a b : Fin n) :
      ContDiffAt ℝ 1 (fun w ↦ star (holomorphicJacobianMatrix F.map w a b)) F.center := by
    exact (Complex.conjCLE.contDiff.contDiffAt).of_le hlevel |>.comp F.center (hJentry a b)
  change ContDiffAt ℝ 1 (fun w ↦
    (Matrix.transpose (holomorphicJacobianMatrix F.map w) *
      metric.metricInChart x (F.map w) * (holomorphicJacobianMatrix F.map w).map star) i j) F.center
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  fun_prop (disch := assumption)

private theorem complex_trace_mul_hermitian_real
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re ((A * B).trace) = (A * B).trace := by
  have hAij (i j : Fin n) : star (A i j) = A j i := by
    have h := congrArg (fun C : Matrix (Fin n) (Fin n) ℂ ↦ C j i) hA.eq
    simpa [Matrix.conjTranspose_apply] using h
  have hBij (i j : Fin n) : star (B i j) = B j i := by
    have h := congrArg (fun C : Matrix (Fin n) (Fin n) ℂ ↦ C j i) hB.eq
    simpa [Matrix.conjTranspose_apply] using h
  have hstar : star ((A * B).trace) = (A * B).trace := by
    calc
      star ((A * B).trace) = ∑ i, ∑ j, star (A i j) * star (B j i) := by
        change star (∑ i, ∑ j, A i j * B j i) = _
        simp_rw [star_sum, star_mul]
        refine Finset.sum_congr rfl ?_
        intro i hi
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact mul_comm _ _
      _ = ∑ i, ∑ j, A j i * B i j := by simp_rw [hAij, hBij]
      _ = ∑ i, ∑ j, A i j * B j i := by rw [Finset.sum_comm]
  have him : ((A * B).trace).im = 0 := by
    have h := congrArg Complex.im hstar
    have h' : -((A * B).trace).im = ((A * B).trace).im := by simpa using h
    linarith
  apply Complex.ext
  · simp
  · simp [him]

open scoped Topology in
private theorem normalFrame_relative_trace_first_derivative
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x)
    (p : Fin n) :
    chartPartialZComplex
      (fun w ↦ (relTrace
        (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w)))
        (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w))) : ℂ))
      F.center p = ∑ j, normalFrameFirstDerivative F p j j := by
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ pulledBackMetricInChart ω₀ x F.map w
  let H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ pulledBackMetricInChart ω₁ x F.map w
  let u : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦
    relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w)))
      (ω₁ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (F.map w)))
  let s : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ ((G w)⁻¹ * H w).trace
  have hrel := normalFrame_relative_trace_eq_pulledBack_matrix_eventually ω₀ ω₁ x F
  have hdet := frame_jacobian_det_eventually_ne_zero ω₀ ω₁ x F
  have htraceReal : ∀ᶠ w in 𝓝 F.center, RCLike.re (s w) = s w := by
    filter_upwards [F.isOpen_domain.mem_nhds F.center_mem, hdet] with w hw hdet
    have hGherm : (G w).IsHermitian := by
      simpa [G] using pulledBackMetric_hermitian ω₀ ω₀ ω₁ x F w hw
    have hHherm : (H w).IsHermitian := by
      simpa [H] using pulledBackMetric_hermitian ω₁ ω₀ ω₁ x F w hw
    simpa [s] using complex_trace_mul_hermitian_real (G w)⁻¹ (H w) hGherm.inv hHherm
  have hcomplex : (fun w ↦ (u w : ℂ)) =ᶠ[𝓝 F.center] s := by
    filter_upwards [hrel, htraceReal] with w hrel' hreal'
    have hrel'' : u w = RCLike.re (s w) := by
      simpa [u, G, H, s] using hrel'
    exact (congrArg Complex.ofReal hrel'').trans hreal'
  have hGvalue : G F.center = 1 := by
    simpa [G] using F.reference_normalized
  have hGjet : ∀ i j,
      chartPartialZComplex (fun w ↦ G w i j) F.center p = 0 := by
    intro i j
    simpa [G] using F.reference_first_derivative_zero p i j
  have hG : ∀ i j, ContDiffAt ℝ 1 (fun w ↦ G w i j) F.center := by
    intro i j
    simpa [G] using contDiffAt_pulledBackMetric_entry ω₀ ω₀ ω₁ x F i j
  have hH : ∀ i j, ContDiffAt ℝ 1 (fun w ↦ H w i j) F.center := by
    intro i j
    simpa [H] using contDiffAt_pulledBackMetric_entry ω₁ ω₀ ω₁ x F i j
  have hGunit : IsUnit (G F.center) := by rw [hGvalue]; exact isUnit_one
  have hA : ∀ i j, DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ i j) F.center := by
    intro i j
    exact KahlerForm.chartInv_differentiableAt hG hGunit i j
  have hAvalue : (fun w ↦ (G w)⁻¹) F.center = 1 := by
    simp [G, hGvalue]
  have hAderiv : ∀ i j,
      chartPartialZComplex (fun w ↦ (G w)⁻¹ i j) F.center p = 0 :=
    chartPartialZComplex_inverse_first_jet_zero p hG hGvalue hGunit hGjet
  have hB : ∀ i j, DifferentiableAt ℝ (fun w ↦ H w i j) F.center := by
    intro i j
    exact (hH i j).differentiableAt (by norm_num)
  have htraceJet := chartPartialZComplex_trace_mul_identity
    (fun w ↦ (G w)⁻¹) H F.center p hA hB hAvalue hAderiv
  calc
    _ = chartPartialZComplex s F.center p := by
      unfold chartPartialZComplex
      rw [hcomplex.fderiv_eq (𝕜 := ℝ)]
    _ = ∑ j, chartPartialZComplex (fun w ↦ H w j j) F.center p := htraceJet
    _ = _ := by rfl

/-- The normalized Hermitian gradient-square term of the relative trace in a normal frame. -/
theorem normalFrame_normalized_relative_trace_gradient
    (ω₀ ω₁ : KahlerForm n M) (x : M) (F : YauNormalFrame ω₀ ω₁ x) :
    ω₁.gradNormSq (fun y ↦ relTrace (ω₀ y) (ω₁ y)) x /
        (relTrace (ω₀ x) (ω₁ x)) ^ 2 =
      (∑ p, ‖∑ j, normalFrameFirstDerivative F p j j‖ ^ 2 /
          (F.eigenvalue p * ∑ j, F.eigenvalue j)) /
        (∑ j, F.eigenvalue j) := by
  let u : M → ℝ := fun y ↦ relTrace (ω₀ y) (ω₁ y)
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let g : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ u (c.symm z)
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ g (F.map z)
  have hregular : ContDiffAt ℝ 1 (u ∘ c.symm) (c x) := by
    have h2 := contDiffAt_relativeTrace_inChart ω₀ ω₁ x
    have hlevel : (↑(1 : ℕ∞) : WithTop ℕ∞) ≤ (↑(2 : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_le_coe.mpr (by norm_num : (1 : ℕ∞) ≤ (2 : ℕ∞))
    simpa [u, c] using h2.of_le hlevel
  have hcenter : F.map F.center = c x := F.center_eq_chart_center
  have hregular' : ContDiffAt ℝ 1 (u ∘ c.symm) (F.map F.center) := by
    simpa [hcenter] using hregular
  have hgrad := normalFrame_gradNormSq_eq_firstDerivative_sum ω₀ ω₁ x F u hregular'
  have hg : DifferentiableAt ℝ g (c x) := by
    change DifferentiableAt ℝ (u ∘ c.symm) (c x)
    exact hregular.differentiableAt (by norm_num)
  have hmap : DifferentiableAt ℝ F.map F.center := by
    exact (F.holomorphic_map F.center F.center_mem).differentiableAt
      (F.isOpen_domain.mem_nhds F.center_mem) |>.hasFDerivAt.restrictScalars ℝ |>.differentiableAt
  have hq : DifferentiableAt ℝ q F.center := by
    have hg' : DifferentiableAt ℝ g (F.map F.center) := by
      simpa [hcenter] using hg
    exact hg'.comp F.center hmap
  have hpartial (p : Fin n) :
      chartPartialZ q F.center p = ∑ j, normalFrameFirstDerivative F p j j := by
    calc
      chartPartialZ q F.center p =
          chartPartialZComplex (fun w ↦ (q w : ℂ)) F.center p :=
        chartPartialZ_eq_chartPartialZComplex_ofReal q F.center p hq
      _ = ∑ j, normalFrameFirstDerivative F p j j := by
        simpa [q, g, u, c] using normalFrame_relative_trace_first_derivative ω₀ ω₁ x F p
  have hframe := relTrace_eq_pulledBack_frame_metric ω₀ ω₁ x F F.center
    F.center_mem F.jacobian_det_ne_zero
  have hleft : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hden : relTrace (ω₀ x) (ω₁ x) = ∑ j, F.eigenvalue j := by
    calc
      relTrace (ω₀ x) (ω₁ x) =
          RCLike.re ((pulledBackMetricInChart ω₀ x F.map F.center)⁻¹ *
            pulledBackMetricInChart ω₁ x F.map F.center).trace := by
        simpa [c, hleft, hcenter] using hframe
      _ = ∑ j, F.eigenvalue j := by
        simp [F.reference_normalized, F.varying_diagonal, Matrix.trace]
  have hnumeq :
      (∑ p, ‖chartPartialZ q F.center p‖ ^ 2 / F.eigenvalue p) =
        ∑ p, ‖∑ j, normalFrameFirstDerivative F p j j‖ ^ 2 / F.eigenvalue p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hpartial p]
  calc
    ω₁.gradNormSq u x / (relTrace (ω₀ x) (ω₁ x)) ^ 2 =
        (∑ p, ‖chartPartialZ q F.center p‖ ^ 2 / F.eigenvalue p) /
          (∑ j, F.eigenvalue j) ^ 2 := by
      rw [hgrad, hden]
      rfl
    _ = (∑ p, ‖∑ j, normalFrameFirstDerivative F p j j‖ ^ 2 /
          F.eigenvalue p) / (∑ j, F.eigenvalue j) ^ 2 := by rw [hnumeq]
    _ = (∑ p, ‖∑ j, normalFrameFirstDerivative F p j j‖ ^ 2 /
          (F.eigenvalue p * ∑ j, F.eigenvalue j)) / (∑ j, F.eigenvalue j) :=
      normalized_gradient_denominator_algebra F.eigenvalue F.eigenvalue_pos
        (fun p ↦ ∑ j, normalFrameFirstDerivative F p j j)

end KahlerForm
