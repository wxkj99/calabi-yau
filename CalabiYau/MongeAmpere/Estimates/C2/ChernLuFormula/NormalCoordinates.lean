module

public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor
public import CalabiYau.Geometry.Complex.Forms.Positive
public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.LinearAlgebra.Hermitian.SimultaneousDiagonalization
public import CalabiYau.LinearAlgebra.Hermitian.NormalJet
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates.HolomorphicPatch
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates.PullbackDerivative
public import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula.NormalCoordinates.JetCancellation

/-!
# Holomorphic normal coordinates for the Chern–Lu calculation

The local calculation in the Chern–Lu estimate uses a holomorphic coordinate map whose pulled
back reference metric is the identity with vanishing first derivatives, and whose pulled back
varying metric is diagonal at the center. The frame below records an actual local holomorphic map
into the manifold chart, not just the finite-dimensional normal-jet equation.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.2, Lemma 3.7,
pp. 41–42; Yau 1978, §2.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- A genuine holomorphic normal frame at `x` for the pair `(ω₀, ω₁)`. The map is defined on an
open neighborhood of its center and lands in the fixed complex manifold chart at `x`. -/
structure YauNormalFrame (ω₀ ω₁ : KahlerForm n M) (x : M) where
  domain : Set (EuclideanSpace ℂ (Fin n))
  isOpen_domain : IsOpen domain
  center : EuclideanSpace ℂ (Fin n)
  center_mem : center ∈ domain
  map : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)
  smooth_map : ContDiffOn ℝ ∞ map domain
  holomorphic_map : DifferentiableOn ℂ map domain
  maps_into_chart : ∀ z ∈ domain,
    map z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  center_eq_chart_center : map center =
    extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  jacobian_det_ne_zero : (holomorphicJacobianMatrix map center).det ≠ 0
  eigenvalue : Fin n → ℝ
  eigenvalue_pos : ∀ j, 0 < eigenvalue j
  reference_normalized : pulledBackMetricInChart ω₀ x map center = 1
  varying_diagonal : pulledBackMetricInChart ω₁ x map center =
    Matrix.diagonal (RCLike.ofReal ∘ eigenvalue)
  reference_first_derivative_zero : ∀ p j k,
    chartPartialZComplex (fun z ↦ pulledBackMetricInChart ω₀ x map z j k)
      center p = 0

/-- The first holomorphic derivatives of the varying metric coefficients in a normal frame. -/
noncomputable def normalFrameFirstDerivative {ω₀ ω₁ : KahlerForm n M} {x : M}
    (F : YauNormalFrame ω₀ ω₁ x) (p j k : Fin n) : ℂ :=
  chartPartialZComplex
    (fun z ↦ pulledBackMetricInChart ω₁ x F.map z j k) F.center p

/-- Every pair of positive Kähler forms admits a holomorphic normal frame at each point.

The proof glues three independent constructions: a holomorphic quadratic patch, the pullback
Wirtinger derivative formula, and cancellation of the finite reference normal jet. -/
theorem exists_yau_normal_frame (ω₀ ω₁ : KahlerForm n M) (x : M) :
    Nonempty (YauNormalFrame ω₀ ω₁ x) := by
  let z₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  have hz₀ : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    simpa [z₀] using mem_extChartAt_target x
  let G := ω₀.metricInChart x z₀
  let H := ω₁.metricInChart x z₀
  have hG : G.PosDef := by
    exact ω₀.posDef_metricInChart x (by simpa [z₀] using hz₀)
  have hH : H.PosDef := by
    exact ω₁.posDef_metricInChart x (by simpa [z₀] using hz₀)
  obtain ⟨P, eigenvalue, hPG, hPH⟩ :=
    Matrix.PosDef.exists_simultaneous_diagonalization hG hH.isHermitian
  have heigenvalue : ∀ j, 0 < eigenvalue j :=
    (Matrix.posDef_iff_forall_pos_of_conjTranspose_mul_mul_eq hPG hPH).1 hH
  let J : Matrix (Fin n) (Fin n) ℂ := P.map star
  have hJtranspose : J.transpose = P.conjTranspose := by
    ext i j
    simp [J, Matrix.conjTranspose]
  have hJconj : J.map star = P := by
    ext i j
    simp [J]
  have hNorm : J.transpose * G * J.map star = 1 := by
    rw [hJtranspose, hJconj]
    exact hPG
  have hDiag : J.transpose * H * J.map star =
      Matrix.diagonal (RCLike.ofReal ∘ eigenvalue) := by
    rw [hJtranspose, hJconj]
    exact hPH
  have hDetP : star P.det * G.det * P.det = 1 := by
    have h := congrArg Matrix.det hPG
    simpa [Matrix.det_mul, Matrix.det_conjTranspose, mul_assoc] using h
  have hPdet : P.det ≠ 0 := by
    intro hzero
    simp [hzero] at hDetP
  have hJdet : IsUnit J.det := by
    have hJdet_ne : J.det ≠ 0 := by
      have hmapdet : J.det = star P.det := by
        dsimp [J]
        simpa using ((starRingEnd ℂ).map_det P).symm
      rw [hmapdet]
      exact star_ne_zero.mpr hPdet
    exact isUnit_iff_ne_zero.mpr hJdet_ne
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let L : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    Matrix.toLinearEquiv b J hJdet
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    L.toContinuousLinearEquivOfContinuous L.toLinearMap.continuous_of_finiteDimensional
  have hA : EuclideanSpace.clmMatrix A.toContinuousLinearMap = J := by
    ext a j
    change (Matrix.toLin b b J (EuclideanSpace.single j 1)) a = J a j
    have hb : EuclideanSpace.single j (1 : ℂ) = b j := by
      simp [b, EuclideanSpace.basisFun_apply]
    rw [hb, Matrix.toLin_self]
    simp [b, EuclideanSpace.basisFun_apply, Pi.single_apply]
  let D : Fin n → Fin n → Fin n → ℂ := fun p a b ↦
    chartPartialZComplex (fun w ↦ ω₀.metricInChart x w a b) z₀ p
  have hD : ∀ p a b, D p a b = D a p b := by
    intro p a b
    simpa [D] using
      (kahler_chart_metric_symmetry (ω₀ := ω₀) x hz₀ p a b)
  obtain ⟨Q, hQ, hcancel⟩ :=
    exists_quadratic_pullback_jet_cancellation G J D hG.isHermitian hNorm hD
  let U := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  obtain ⟨V, hVopen, h0, hmap, hVsmooth, hVhol, hf0, hfDeriv⟩ :=
    exists_quadratic_chart_patch U z₀ (isOpen_extChartAt_target x) hz₀ A Q hQ
  let f := quadraticChartMap z₀ A.toContinuousLinearMap Q
  have hJframe : holomorphicJacobianMatrix f 0 = J := by
    change EuclideanSpace.clmMatrix (fderiv ℂ f 0) = J
    rw [hfDeriv]
    exact hA
  have hReference : pulledBackMetricInChart ω₀ x f 0 = 1 := by
    change Matrix.transpose (holomorphicJacobianMatrix f 0) *
      ω₀.metricInChart x (quadraticChartMap z₀ A.toContinuousLinearMap Q 0) *
        (holomorphicJacobianMatrix f 0).map star = 1
    rw [hf0, hJframe]
    simpa [G] using hNorm
  have hVarying : pulledBackMetricInChart ω₁ x f 0 =
      Matrix.diagonal (RCLike.ofReal ∘ eigenvalue) := by
    change Matrix.transpose (holomorphicJacobianMatrix f 0) *
      ω₁.metricInChart x (quadraticChartMap z₀ A.toContinuousLinearMap Q 0) *
        (holomorphicJacobianMatrix f 0).map star = _
    rw [hf0, hJframe]
    simpa [H] using hDiag
  have hFirst : ∀ p j k,
      chartPartialZComplex (fun z ↦ pulledBackMetricInChart ω₀ x f z j k) 0 p = 0 := by
    intro p j k
    have hchain := chartPartialZ_quadratic_pullback_metric ω₀ x z₀ hz₀
      A.toContinuousLinearMap Q hQ p j k
    rw [hchain, hA]
    simpa [D, G] using hcancel p j k
  refine ⟨{
    domain := V
    isOpen_domain := hVopen
    center := 0
    center_mem := h0
    map := f
    smooth_map := hVsmooth
    holomorphic_map := hVhol
    maps_into_chart := hmap
    center_eq_chart_center := hf0
    jacobian_det_ne_zero := by rw [hJframe]; exact hJdet.ne_zero
    eigenvalue := eigenvalue
    eigenvalue_pos := heigenvalue
    reference_normalized := hReference
    varying_diagonal := hVarying
    reference_first_derivative_zero := hFirst
  }⟩

end KahlerForm
