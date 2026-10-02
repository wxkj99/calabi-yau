module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Complex.Schauder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.InverseCoefficientHolder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.DifferentiatedRhsHolder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.ApplyDirectionalSchauder

/-!
# Local Schauder continuation from the differentiated Monge–Ampère equation

This is the local analytic continuation used after the parent has selected nested chart domains,
obtained the current potential bounds, established uniform ellipticity, and differentiated the
log-determinant equation. The estimate controls each first coordinate derivative by interior
Schauder theory and reassembles those bounds into one additional Hölder order for the potential.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- The local Schauder continuation after ellipticity and the differentiated equation have been
established. The uniform `C^{r,α}` potential bound and the `C^{r+2,0}` chart bound on the right-hand
side data provide the coefficient and forcing estimates required by the order `r-2` interior
Schauder estimate. A compact outer buffer supplies uniform lower-jet Hölder bounds for inverse
coefficients on the inner domain; those bounds are passed to the forcing child's uniform
matrix trace-product step. The hypothesis `0 < lam` is required by Schauder.
-/
theorem exists_uniform_chart_holder_bound_succ_of_linearized
    (hSch : InteriorSchauderEstimate n)
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
    (hCurrent : ∀ p ∈ S,
      HolderBoundOn r α Cφ (closure U)
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm))
    (hGouter : ∀ p ∈ S,
      HolderBoundOn (r + 2) 0 CG L
        (p.1 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm))
    (hGlocal : ∀ p ∈ S,
      HolderBoundOn (r + 2) 0 CG (closure U)
        (p.1 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm))
    (K' : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K') (hKU : K' ⊆ U)
    (lam : ℝ≥0) (hlam : 0 < lam)
    (hUniformElliptic : ∀ p ∈ S, IsUniformlyEllipticOn
      (fun z ↦ (ω₀.metricInChart x z +
        complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹)
      lam U)
    (hLinearized : ∀ p ∈ S, ∀ z ∈ U, ∀ v : EuclideanSpace ℂ (Fin n),
      complexEllipticOp (fun _ ↦
        (ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹)
        (fun u ↦ fderiv ℝ
          (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) u v) z =
      fderiv ℝ (p.1 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v -
        RCLike.re (((ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ *
            (Matrix.of fun j k ↦
              fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v)).trace) +
        RCLike.re ((ω₀.metricInChart x z)⁻¹ *
          (Matrix.of fun j k ↦
            fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v)).trace) :
    ∃ C : ℝ≥0, ∀ p ∈ S,
      HolderBoundOn (r + 1) α C K'
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) := by
  obtain ⟨CA, hCoeffFull⟩ := exists_uniform_inverse_coefficient_holder
    ω₀ S hS hα₀ hα₁ hr hUopen hUcompact hUtarget hLcompact hBuffer hLtarget
    hCurrentOuter hGlocal
  have hCoeffLower : ∀ p ∈ S, ∀ j k, ∀ m < r - 2,
      HolderOnWith CA α (iteratedFDeriv ℝ m (fun z ↦
        (ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ j k)) U := by
    intro p hp j k m hm
    exact (hCoeffFull p hp j k).1 m hm
  have hCoeff : ∀ p ∈ S, ∀ j k,
      HolderBoundOn (r - 2) α CA U (fun z ↦
        (ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ j k) := by
    intro p hp j k
    exact (hCoeffFull p hp j k).2
  obtain ⟨CR, hRhs⟩ := exists_uniform_differentiated_rhs_holder
    ω₀ S hS hα₀ hα₁ hr hUopen hUcompact hUtarget hLcompact hBuffer hLtarget
    hGouter hCoeffLower hCoeff
  exact exists_uniform_chart_holder_bound_succ_of_schauder_data
    hSch ω₀ S hS hα₀ hα₁ hr hUopen hUcompact hUtarget hCurrent K' hK hKU lam
    hlam hUniformElliptic hCoeff hRhs hLinearized

end KahlerForm

end
