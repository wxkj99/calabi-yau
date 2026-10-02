module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy
public import CalabiYau.Geometry.Kahler.Curvature.ConnectionDerivative

/-!
# Antiholomorphic derivative of the connection difference

The curvature of a Kähler metric is the negative antiholomorphic derivative
of its holomorphic connection. Apply this to the perturbed and reference
metrics and subtract. This is the tensor identity used before the Bianchi
step in Székelyhidi, §3.3, proof of Lemma 3.9, p. 48 (author's PDF).
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- In holomorphic coordinates,
`∂̄q (Γ(gφ)ⁱⱼₖ - Γ(g₀)ⁱⱼₖ) =
  -(gφ⁻¹)ₗᵢ R(gφ)ⱼq̄ₖₗ̄ + (g₀⁻¹)ₗᵢ R(g₀)ⱼq̄ₖₗ̄`.
The inverse row is `l` and the column is `i`; no factor of two is introduced
because both Wirtinger derivatives contain their own `1/2`. -/
def ConnectionDifferenceCurvatureIdentity (ω₀ : KahlerForm n M) : Prop :=
    ∀ (φ : M → ℝ) (_hφ : ω₀.IsPotential φ) (x : M)
      (z : EuclideanSpace ℂ (Fin n))
      (_hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
      (i j k q : Fin n),
    let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun w ↦ ω₀.metricInChart x w
    let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun w ↦ g₀ w + complexHessian
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w
    chartPartialBarComplex
        (fun w ↦ connectionDifferenceInChart ω₀ φ x w i j k) z q =
      -(∑ l : Fin n, (gφ z)⁻¹ l i * chartCurvature gφ z j q k l) +
        ∑ l : Fin n, (g₀ z)⁻¹ l i * chartCurvature g₀ z j q k l

private theorem local_connection_differentiableAt
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun w ↦ g w a b) U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hdet : IsUnit (g z).det) (i j k : Fin n) :
    DifferentiableAt ℝ
      (fun w ↦ ∑ l, (g w)⁻¹ l i * chartPartialZComplex (fun v ↦ g v k l) w j) z := by
  have hentry (a b : Fin n) : ContDiffAt ℝ ∞ (fun w ↦ g w a b) z :=
    (hg a b).contDiffAt (hU.mem_nhds hz)
  have hinv (l : Fin n) : DifferentiableAt ℝ (fun w ↦ (g w)⁻¹ l i) z :=
    chartInv_differentiableAt (fun a b ↦ (hentry a b).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet) l i
  have hpart (l : Fin n) :
      DifferentiableAt ℝ (fun w ↦ chartPartialZComplex (fun v ↦ g v k l) w j) z := by
    have hfd : DifferentiableAt ℝ (fderiv ℝ (fun w ↦ g w k l)) z :=
      ((hentry k l).fderiv_right (m := ∞)
        (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt
        (by norm_num)
    have he : DifferentiableAt ℝ
        (fun w ↦ fderiv ℝ (fun v ↦ g v k l) w (EuclideanSpace.single j 1)) z :=
      hfd.clm_apply (differentiableAt_const _)
    have hie : DifferentiableAt ℝ
        (fun w ↦ fderiv ℝ (fun v ↦ g v k l) w
          (Complex.I • EuclideanSpace.single j 1)) z :=
      hfd.clm_apply (differentiableAt_const _)
    unfold chartPartialZComplex
    fun_prop (disch := assumption)
  exact DifferentiableAt.fun_sum (fun l hl ↦ (hinv l).mul (hpart l))

/-- The connection-difference curvature identity at every point of every
Kähler potential. This is an independent geometric input to the Bochner
estimate and does not assume the Monge–Ampère equation. -/
theorem c3ConnectionDifference_bar_derivative (ω₀ : KahlerForm n M) :
    ConnectionDifferenceCurvatureIdentity ω₀ := by
  intro φ hφ x z hz i j k q
  let U : Set (EuclideanSpace ℂ (Fin n)) :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w
  let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ g₀ w + complexHessian
      (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w
  let ωφ := ω₀.perturb φ hφ
  have hU : IsOpen U := isOpen_extChartAt_target x
  have heq : Set.EqOn gφ (fun w ↦ ωφ.metricInChart x w) U := by
    intro w hw
    simpa [gφ, g₀, ωφ] using (ω₀.metricInChart_perturb hφ x hw).symm
  have hg₀ : ∀ a b, ContDiffOn ℝ ∞ (fun w ↦ g₀ w a b) U := by
    intro a b
    exact ω₀.contDiffOn_metricInChart x a b
  have hgφ : ∀ a b, ContDiffOn ℝ ∞ (fun w ↦ gφ w a b) U := by
    intro a b
    exact (ωφ.contDiffOn_metricInChart x a b).congr
      (fun w hw ↦ congrArg (fun G : Matrix (Fin n) (Fin n) ℂ ↦ G a b) (heq hw))
  have hdet₀ : IsUnit (g₀ z).det :=
    (Matrix.isUnit_iff_isUnit_det (A := g₀ z)).mp (ω₀.posDef_metricInChart x hz).isUnit
  have hdetφ : IsUnit (gφ z).det := by
    rw [heq hz]
    exact (Matrix.isUnit_iff_isUnit_det (A := ωφ.metricInChart x z)).mp
      (ωφ.posDef_metricInChart x hz).isUnit
  have hcurv₀ := chartChristoffel_bar_eq_curvature_local g₀ U hU hg₀ z hz hdet₀ i j k q
  have hcurvφ := chartChristoffel_bar_eq_curvature_local gφ U hU hgφ z hz hdetφ i j k q
  have hdiff₀ := local_connection_differentiableAt g₀ U hU hg₀ z hz hdet₀ i j k
  have hdiffφ := local_connection_differentiableAt gφ U hU hgφ z hz hdetφ i j k
  change chartPartialBarComplex
      (fun w ↦ (∑ l, (gφ w)⁻¹ l i * chartPartialZComplex (fun v ↦ gφ v k l) w j) -
        ∑ l, (g₀ w)⁻¹ l i * chartPartialZComplex (fun v ↦ g₀ v k l) w j) z q = _
  rw [chartPartialBarComplex_sub _ _ z q hdiffφ hdiff₀, hcurvφ, hcurv₀]
  exact sub_neg_eq_add _ _

end KahlerForm
