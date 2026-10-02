module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.Basic
public import CalabiYau.Mathlib.Geometry.Manifold.Holder
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ForcingChartBound
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.RicciDerivative.ForcingCovariance

/-!
# Compact-family forcing jets in reference frames

Székelyhidi, §3.3, p. 45: a uniform C3 forcing bound controls the general
Ricci derivative. Compactness supplies finitely many fixed charts; covariance
moves their estimates to the centre chart. This assembly has no placeholder.
-/

public section

open scoped Manifold ContDiff NNReal BigOperators

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

omit [T2Space M] in
/-- One finite coefficient for the forcing Hessian and its reference derivative,
uniform in the family, the point, and the reference-unitary frame. -/
theorem exists_uniform_c3ForcingFrameBound (ω₀ : KahlerForm n M)
    (F : Set (M → ℝ))
    (hF : ∀ G ∈ F, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hHolder : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) 3 0 F) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ G ∈ F, ∀ x P,
      IsReferenceOrthonormalFrame ω₀ x P →
        ForcingFrameBound ω₀ G x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) P A := by
  classical
  choose U hU hx hsource hbound using
    (fun x ↦ exists_local_c3ForcingFrameBound ω₀ F hF hHolder x)
  choose A hA hestimate using hbound
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
    U hU hcover
  refine ⟨∑ x ∈ t, A x, Finset.sum_nonneg (fun x _ ↦ hA x), ?_⟩
  intro G hG x P hP
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  obtain ⟨V, hV⟩ := ω₀.exists_reference_chart_overlap y x (hsource y hxy)
  have hQ := ω₀.referenceFrame_transition y x V hV P hP
  have hfixed := hestimate y G hG x hxy (referenceTransitionMatrix y x * P) hQ
  have hcenter := (forcingFrameBound_chart_transition ω₀ (hF G hG) y x
    (hsource y hxy) V hV P (A y)).mpr hfixed
  exact ForcingFrameBound.mono ω₀ G x
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) P hcenter
    (Finset.single_le_sum (fun z _ ↦ hA z) hyt)

end KahlerForm
