module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ComponentIdentity
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ForcingBound
import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound
import CalabiYau.Geometry.Complex.Forms.Positive
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound.ReferenceRicciContraction
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound.NormalizedFrameExistence
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound.RelativeFrameTransfer
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciActionBound.RaisedIndexConversion

/-!
# Uniform raised Ricci coefficients in perturbed-unitary frames

This is the general Monge–Ampère adaptation of Székelyhidi, §3.3, the
Ricci commutator following (3.14), printed p. 45, using the Ricci identity
of Example 1.18, printed p. 11, rather than the Einstein specialization.
The adaptation, including its family-uniform frame comparison, is not a
verbatim theorem in that passage.

The matrix convention is `P.transpose * g * P.map star = 1`. We conjugate
the actual raised endomorphism by `P`; we do not differentiate a constant
identity metric. Compactness and the fixed reference metric are essential
for the uniform constant. Smoothness of the forcing is separate from its
chartwise Hölder bounds and is supplied explicitly by `hS`.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder
open ContinuousAlternatingMap

namespace KahlerForm

private theorem ricci_frame_trace_bound_matrix_psd {n : ℕ}
    (Ω α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hω : Ω.IsPositive) (hα : α.IsNonneg) {B : ℝ}
    (htr : relTrace Ω α ≤ B) :
    ((B : ℂ) • Ω.coeffMatrix - α.coeffMatrix).PosSemidef := by
  have hΩn : Ω.IsNonneg := by
    refine ⟨hω.1, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst v
      have hz : (![0, Complex.I • (0 : EuclideanSpace ℂ (Fin n))] : Fin 2 →
          EuclideanSpace ℂ (Fin n)) = 0 := by
        funext i
        fin_cases i <;> simp
      rw [hz, ContinuousAlternatingMap.map_zero]
    · exact le_of_lt (hω.2 v hv)
  have hgap : 0 ≤ B - relTrace Ω α := sub_nonneg.mpr htr
  have hfirst : ((B - relTrace Ω α) • Ω).IsNonneg := by
    refine ⟨hΩn.1.smul _, ?_⟩
    intro v
    rw [ContinuousAlternatingMap.smul_apply]
    exact mul_nonneg hgap (hΩn.2 v)
  have htrace := isNonneg_relTrace_smul_sub hω hα
  have hsum :
      ((B - relTrace Ω α) • Ω + (relTrace Ω α • Ω - α)).IsNonneg := by
    refine ⟨hfirst.1.add htrace.1, ?_⟩
    intro v
    rw [ContinuousAlternatingMap.add_apply]
    exact add_nonneg (hfirst.2 v) (htrace.2 v)
  have hdecomp : B • Ω - α =
      (B - relTrace Ω α) • Ω + (relTrace Ω α • Ω - α) := by
    ext v
    simp only [ContinuousAlternatingMap.sub_apply,
      ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply]
    module
  have hmatrix := (isNonneg_iff (α := B • Ω - α)).mp (hdecomp ▸ hsum)
  have hcoe : (B • Ω).coeffMatrix = (B : ℂ) • Ω.coeffMatrix := by
    rw [coeffMatrix_smul]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) B Ω.coeffMatrix
  have hmatrix₂ := hmatrix.2
  rw [coeffMatrix_sub] at hmatrix₂
  rw [hcoe] at hmatrix₂
  exact hmatrix₂

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] in
/-- One finite coefficient bound for the raised Ricci endomorphism, uniformly
in the family and the point, in a frame unitary for the perturbed metric. -/
theorem exists_uniform_c3RicciEndomorphism_frame_bound
    (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
        ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : HolderBoundedInCharts
      (EuclideanSpace ℂ (Fin n)) 3 0 (Prod.fst '' S))
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
        relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p ∈ S, ∀ x,
      let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
      let g := c3PerturbedMetricInChart ω₀ p.2 x
      ∃ P : Matrix (Fin n) (Fin n) ℂ,
        P.transpose * g z * P.map star = 1 ∧
          ∀ i j,
            ‖(P⁻¹ * Matrix.of (c3RicciEndomorphism g z) * P) i j‖ ≤ R := by
  classical
  obtain ⟨K, hK, hReference⟩ := exists_uniform_referenceRicciZero_frame_component_bound ω₀
  have hSmooth : ∀ G ∈ Prod.fst '' S,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G := by
    rintro G ⟨p, hp, rfl⟩
    exact (hS p hp).1
  obtain ⟨A, hA, hForcing⟩ := exists_uniform_c3ForcingFrameBound ω₀
    (Prod.fst '' S) hSmooth hG
  obtain ⟨B, hB, hTrace⟩ := hMetric
  refine ⟨(n : ℝ) * B * (K + A),
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hB.le) (add_nonneg hK hA), ?_⟩
  intro p hp x
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let g := c3PerturbedMetricInChart ω₀ p.2 x
  have hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source
      (mem_extChartAt_source x)
  obtain ⟨U, hU⟩ := exists_c3NormalizedFrameMatrix (ω₀.metricInChart x z)
    (ω₀.posDef_metricInChart x hz)
  have hUref : IsReferenceOrthonormalFrame ω₀ x U := hU
  have hg : (g z).PosDef := by
    have hpos := (ω₀.perturb p.2 (hS p hp).2.1).posDef_metricInChart x hz
    rw [ω₀.metricInChart_perturb (hS p hp).2.1 x hz] at hpos
    exact hpos
  obtain ⟨P, hP⟩ := exists_c3NormalizedFrameMatrix (g z) hg
  refine ⟨P, hP, ?_⟩
  have hComparison : ((B : ℂ) • g z - ω₀.metricInChart x z).PosSemidef := by
    have hbase : (ω₀ x).IsNonneg := by
      exact (isNonneg_iff (α := ω₀ x)).mpr
        ⟨(ω₀.isPositive x).1, ((isPositive_iff (α := ω₀ x)).mp (ω₀.isPositive x)).2.posSemidef⟩
    have hcomp := ricci_frame_trace_bound_matrix_psd
      ((ω₀.perturb p.2 (hS p hp).2.1) x) (ω₀ x)
      ((ω₀.perturb p.2 (hS p hp).2.1).isPositive x) hbase
      (by simpa only [perturb_apply] using (hTrace p hp x).2)
    have hmetric : g z = (ω₀.perturb p.2 (hS p hp).2.1).metricInChart x z :=
      (ω₀.metricInChart_perturb (hS p hp).2.1 x hz).symm
    rw [hmetric]
    change ((B : ℂ) •
      (ω₀.perturb p.2 (hS p hp).2.1).metricInChart x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) -
      ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)).PosSemidef
    rw [metricInChart_self, metricInChart_self]
    exact hcomp
  have hGmem : p.1 ∈ Prod.fst '' S := ⟨p, hp, rfl⟩
  have hRef : ∀ j l,
      ‖c3TwoCovariantFrame U (c3RicciInChart (ω₀.metricInChart x) z) j l‖ ≤ K :=
    hReference x U hUref
  have hHess := (hForcing p.1 hGmem x U hUref).1
  have hRic : c3RicciInChart g z =
      Matrix.of (c3RicciInChart (ω₀.metricInChart x) z) -
        c3ForcingHessianInChart p.1 x z := by
    funext j l
    exact c3RicciInChart_perturb_eq_of_solvesMongeAmpere ω₀
      (hS p hp).1 (hS p hp).2 x hz j l
  have hRicU : ∀ j l, ‖c3TwoCovariantFrame U (c3RicciInChart g z) j l‖ ≤ K + A := by
    intro j l
    have hsub : c3TwoCovariantFrame U
        (Matrix.of (c3RicciInChart (ω₀.metricInChart x) z) -
          c3ForcingHessianInChart p.1 x z) j l =
        c3TwoCovariantFrame U (c3RicciInChart (ω₀.metricInChart x) z) j l -
          c3TwoCovariantFrame U (c3ForcingHessianInChart p.1 x z) j l := by
      simp only [c3TwoCovariantFrame, Matrix.sub_apply, Matrix.of_apply,
        mul_sub, Finset.sum_sub_distrib]
    rw [hRic, hsub]
    exact (norm_sub_le _ _).trans (add_le_add (hRef j l) (hHess j l))
  have hTransfer := c3TwoCovariantFrame_bound_of_relative_matrix_comparison
    (ω₀.metricInChart x z) (g z) U P (c3RicciInChart g z) B (K + A)
    hU hP hB.le (add_nonneg hK hA) hComparison hRicU
  intro i j
  rw [c3RicciEndomorphism_normalizedFrame_apply g z P hP i j]
  exact hTransfer j i

end KahlerForm
