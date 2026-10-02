module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.Basic
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.MetricDerivatives
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.FiniteJets
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.CurvatureExpansion
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.MetricJetSymmetries
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.JetCancellation

/-!
# Differential Bianchi identity for the actual perturbed chart metric

Székelyhidi, §3.3, proof of Lemma 3.9, the Bianchi calculation following
(3.15), printed p. 45. The identity follows from the metric jet symmetries and
finite-jet cancellation.

The lowered covariant derivative has argument order `(p,j,q,k,l)` and two
lower holomorphic connection corrections. The cyclic identity permutes these
slots to `(k,p,q,j,l)`, with the antiholomorphic slots `q,l` fixed. This is an
identity of the actual metric derivative, not a definitional equality of slots
and not an assumed finite-jet permutation. Smoothness, invertibility and the
neighborhood Kähler first-jet symmetry come from `ω₀.IsPotential φ` on the open
chart target. The finite representation stays behind this public endpoint.

No global simp or cyclic rewriting attribute is installed.
-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

/-- The holomorphic covariant curvature derivative of the actual perturbed metric
is cyclic in its three holomorphic slots. -/
theorem c3PerturbedCurvatureCovariantZ_permute
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
    (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (p j q k l : Fin n) :
    c3CurvatureCovariantZ (c3PerturbedMetricInChart ω₀ φ x) z p j q k l =
      c3CurvatureCovariantZ (c3PerturbedMetricInChart ω₀ φ x) z k p q j l := by
  let U : Set (EuclideanSpace ℂ (Fin n)) :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    c3PerturbedMetricInChart ω₀ φ x
  have hdata := c3PerturbedMetric_chart_data ω₀ hφ x
  have hU : IsOpen U := by simpa [U] using hdata.1
  have hg : ∀ a b, ContDiffOn ℝ ∞ (fun w => g w a b) U := by
    simpa [U, g] using hdata.2.1
  have hunit : ∀ w ∈ U, IsUnit (g w) := by
    simpa [U, g] using hdata.2.2.1
  have hK : ∀ w ∈ U, ∀ a b c,
      chartPartialZComplex (fun v => g v b c) w a =
        chartPartialZComplex (fun v => g v a c) w b := by
    simpa [U, g] using hdata.2.2.2
  have hExpand : ∀ a b c d e,
      chartPartialZComplex (fun w => chartCurvature g w b c d e) z a =
        c3JetCurvatureDerivative (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
          (c3MetricJetZBar g z) (c3MetricJetZZ g z) (c3MetricJetZZBar g z)
          a b c d e := by
    intro a b c d e
    exact c3Curvature_partialZ_eq_jet g U hU hg hunit z (by simpa [U] using hz)
      a b c d e
  have hcov := c3CurvatureCovariantZ_eq_jet_of_expansion g z hExpand p j q k l
  have hcov' := c3CurvatureCovariantZ_eq_jet_of_expansion g z hExpand k p q j l
  have hP : ∀ a b c, c3MetricJetZ g z a b c = c3MetricJetZ g z b a c := by
    intro a b c
    exact hK z (by simpa [U] using hz) a b c
  have hS : ∀ a b c d, c3MetricJetZBar g z a b c d =
      c3MetricJetZBar g z c b a d := by
    intro a b c d
    exact c3MetricJetZBar_permute_of_kahler g U hU hg hK z
      (by simpa [U] using hz) a b c d
  have hV : ∀ a b c d, c3MetricJetZZ g z a b c d =
      c3MetricJetZZ g z c a b d := by
    intro a b c d
    exact c3MetricJetZZ_permute_of_kahler g U hU hg hK z
      (by simpa [U] using hz) a b c d
  have hW : c3MetricJetZZBar g z p j q k l =
      c3MetricJetZZBar g z k p q j l := by
    exact c3MetricJetZZBar_permute_of_kahler g U hU hg hK z
      (by simpa [U] using hz) p j q k l
  have hMixed : ∀ a b c d e,
      c3JetMixed (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetZBar g z)
        a b c d e =
      c3JetMixed (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetZBar g z)
        d a c b e := by
    intro a b c d e
    exact c3JetMixed_permute (g z)⁻¹ (c3MetricJetZ g z)
      (c3MetricJetZBar g z) hP hS a b c d e
  have hQuartic : ∀ a b c d e,
      c3JetQuartic (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
        a b c d e =
      c3JetQuartic (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
        d a c b e := by
    intro a b c d e
    exact c3JetQuartic_permute (g z)⁻¹ (c3MetricJetZ g z)
      (c3MetricJetBar g z) hP a b c d e
  have hdiff := c3JetCovariantCurvature_sub_permuted
    (g z)⁻¹ (c3MetricJetZ g z) (c3MetricJetBar g z)
    (c3MetricJetZBar g z) (c3MetricJetZZ g z) (c3MetricJetZZBar g z)
    hV hMixed hQuartic p j q k l
  rw [hcov, hcov']
  apply sub_eq_zero.mp
  rw [hdiff, hW]
  ring

end KahlerForm
