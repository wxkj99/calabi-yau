module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Complex.Schauder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.InverseHolderJets
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.MetricCoefficientJets
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.MetricInverseEntryBound

/-!
# Hölder coefficients for the perturbed inverse metric

The current potential bound on a compact OUTER buffer controls the complex Hessian coefficients
through order `r-2`. In particular the lower coefficient jets have one common Hölder bound on the
inner set, including points across nearby components. The Monge–Ampère determinant and the compact
positive reference metric give a uniform inverse-entry bound; higher-order inverse calculus then
gives the coefficient class needed by Schauder.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Uniform `C^{r-2,α}` bounds for the inverse perturbed-metric coefficients on the chart domain.
The determinant identity supplies the nondegeneracy needed to make the inverse bounds uniform.
The outer compact set supplies the geometric buffer for family-uniform lower-jet Hölder control;
a bound restricted to `closure U` does not suffice for nearby points separated by thin gaps.
Both the top-order bound and the lower-jet estimates are returned with the SAME constant, matching
the input of `exists_holderBoundOn_matrix_trace_product` used for the differentiated forcing.
-/
theorem exists_uniform_inverse_coefficient_holder
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    {x : M} {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {r : ℕ} (hr : 2 ≤ r) {Cφ CG : ℝ≥0}
    {U L : Set (EuclideanSpace ℂ (Fin n))}
    (hUopen : IsOpen U) (hUcompact : IsCompact (closure U))
    (hUtarget : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hLcompact : IsCompact L) (hBuffer : closure U ⊆ interior L)
    (hLtarget : L ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hCurrentOuter : ∀ p ∈ S,
      HolderBoundOn r α Cφ L
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm))
    (hGlocal : ∀ p ∈ S,
      HolderBoundOn (r + 2) 0 CG (closure U)
        (p.1 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)) :
    ∃ C : ℝ≥0, ∀ p ∈ S, ∀ i j,
      (∀ m < r - 2, HolderOnWith C α (iteratedFDeriv ℝ m (fun z ↦
        (ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ i j)) U) ∧
      HolderBoundOn (r - 2) α C U (fun z ↦
        (ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ i j) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let A : ((M → ℝ) × (M → ℝ)) → EuclideanSpace ℂ (Fin n) →
      Matrix (Fin n) (Fin n) ℂ := fun p z ↦
    ω₀.metricInChart x z + complexHessian (p.2 ∘ e.symm) z
  have hCurrent : ∀ p ∈ S,
      HolderBoundOn r α Cφ (closure U) (p.2 ∘ e.symm) := by
    intro p hp
    exact (hCurrentOuter p hp).mono_set (hBuffer.trans interior_subset)
  obtain ⟨CA, hMetricJets⟩ := exists_uniform_perturbed_metric_coefficient_jets
    ω₀ S (fun p hp ↦ (hS p hp).2) hα₀ hα₁ hr hUopen hLcompact hBuffer
    hLtarget hCurrentOuter
  obtain ⟨B, hInverseEntries⟩ := exists_uniform_perturbed_metric_inverse_entry_bound
    ω₀ S (fun p hp ↦ (hS p hp).2) hr hUcompact hUtarget hCurrent hGlocal
  have hW : IsOpen e.target := isOpen_extChartAt_target x
  have hUW : U ⊆ e.target := by
    intro z hz
    exact hUtarget (subset_closure hz)
  have hASmooth : ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ A p z i j) e.target := by
    intro p hp i j
    exact (hMetricJets p hp).1 i j
  have hUnit : ∀ p ∈ S, ∀ z ∈ e.target, IsUnit (A p z) := by
    intro p hp z hz
    exact (hMetricJets p hp).2.1 z hz
  have hA : ∀ p ∈ S, ∀ i j,
      (∀ m ≤ r - 2, ∀ z ∈ U,
        ‖iteratedFDeriv ℝ m (fun z ↦ A p z i j) z‖ ≤ CA) ∧
      (∀ m < r - 2, HolderOnWith CA α
        (iteratedFDeriv ℝ m (fun z ↦ A p z i j)) U) ∧
      HolderOnWith CA α (iteratedFDeriv ℝ (r - 2) (fun z ↦ A p z i j)) U := by
    intro p hp i j
    exact (hMetricJets p hp).2.2 i j
  have hInv : ∀ p ∈ S, ∀ z ∈ U, ∀ i j, ‖(A p z)⁻¹ i j‖ ≤ B := by
    intro p hp z hz i j
    exact hInverseEntries p hp z hz i j
  obtain ⟨CI, hInvJets⟩ := exists_holderBoundOn_matrix_inverse_entries
    S hα₀ hα₁ hW hUW A hASmooth hA hUnit hInv
  refine ⟨CI, ?_⟩
  intro p hp i j
  exact ⟨(hInvJets p hp i j).2.1,
    ⟨(hInvJets p hp i j).1, (hInvJets p hp i j).2.2⟩⟩

end KahlerForm

end
