module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Assembly.DerivativeRepresentation
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Assembly.DerivativeSupport
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Euclidean.TopForm
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.PartitionRefinement

/-!
# Stokes from a finite restricted oriented chart formula

Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 16.11,
pp. 411–414: localize the primitive by a smooth partition of unity and apply
compactly supported Euclidean Stokes, then use linearity. The chart integral
convention is Proposition 16.4, pp. 404–405.

The linear functional and its chart formula are explicit intermediate data.
Unlike the full-canonical-chart formula, this formula is required only on
the selected restricted chart domains. Their orientation compatibility is
needed when constructing the formula, not as an extra assumption once the
formula is supplied. No orientation sign is extended across other components
of a canonical chart source.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin (m + 1) → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin (m + 1) → ℝ) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, Fin (m + 1) → ℝ) M]
  [T2Space M] [CompactSpace M]

/-- A primitive whose closed support lies in a restricted chart has an exact
form with zero signed chart integral. The zero extension uses the canonical
chart at `C.center`, but no support or sign assumption outside `C.domain`
is needed. In particular the restricted domain need not contain its center. -/
theorem signedChartIntegral_exteriorDerivative_eq_zero
    (C : OrientedLocalChart (m + 1) M)
    (α : DifferentialForm 𝓘(ℝ, Fin (m + 1) → ℝ) M m)
    (hα : closure {p : M | α p ≠ 0} ⊆ C.domain) :
    signedChartIntegral C (exteriorDerivative α) = 0 := by
  classical
  have hsource := hα.trans C.domain_subset
  obtain ⟨hsmooth, hcompact⟩ :=
    stokesChartRepresentation_contDiff_hasCompactSupport α C.center hsource
  have hcompactα : IsCompact (closure {p : M | α p ≠ 0}) :=
    IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (subset_univ _)
  have hcoeff (y : Fin (m + 1) → ℝ) :
      chartTopCoefficient C.center (exteriorDerivative α) y =
        stokesChartRepresentation (exteriorDerivative α) C.center y
          (fun j : Fin (m + 1) => Pi.single j (1 : ℝ)) := by
    simp only [chartTopCoefficient, stokesChartRepresentation]
    split_ifs <;> rfl
  unfold signedChartIntegral
  simp_rw [hcoeff, stokesChartRepresentation_exteriorDerivative α C.center hsource hcompactα]
  rw [ContinuousAlternatingMap.integral_extDeriv_standardBasis_eq_zero hsmooth hcompact]
  exact mul_zero _

/-- A linear top-form functional with the supported-form chart formula on a
finite subordinate restricted atlas satisfies Stokes. Constructing that
functional and formula is a separate input; local Stokes is proved, not
assumed. Only indices in `s` are used. `m = 0` is real dimension one, not the
real-dimension-zero case, which has no predecessor degree. Empty manifolds
and arbitrary index types are allowed. -/
theorem global_stokes_of_restricted_oriented_integral_formula {ι : Type*}
    (Φ : DifferentialForm 𝓘(ℝ, Fin (m + 1) → ℝ) M (m + 1) →ₗ[ℝ] ℝ)
    (C : ι → OrientedLocalChart (m + 1) M)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin (m + 1) → ℝ) M Set.univ)
    (s : Finset ι) (hs : ∀ p : M, ∑ i ∈ s, ρ i p = 1)
    (hρ : ∀ i ∈ s, tsupport (ρ i) ⊆ (C i).domain)
    (hchart : ∀ i ∈ s,
      ∀ γ : DifferentialForm 𝓘(ℝ, Fin (m + 1) → ℝ) M (m + 1),
      closure {p : M | γ p ≠ 0} ⊆ (C i).domain →
        Φ γ = signedChartIntegral (C i) γ)
    (η : DifferentialForm 𝓘(ℝ, Fin (m + 1) → ℝ) M m) :
    Φ (exteriorDerivative η) = 0 := by
  classical
  rw [← sum_smoothMulForm_eq ρ s hs η]
  change Φ (exteriorDerivativeLinearMap (IM := 𝓘(ℝ, Fin (m + 1) → ℝ))
    (M := M) m (∑ i ∈ s, smoothMulForm (ρ i) η)) = 0
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hα : closure {p : M | smoothMulForm (ρ i) η p ≠ 0} ⊆ (C i).domain :=
    ((smoothMulForm_closedSupport_subset (ρ i) η).trans Set.inter_subset_left).trans
      (hρ i hi)
  change Φ (exteriorDerivative (smoothMulForm (ρ i) η)) = 0
  rw [hchart i hi _ ((exteriorDerivative_closedSupport_subset _).trans hα)]
  exact signedChartIntegral_exteriorDerivative_eq_zero (C i) (smoothMulForm (ρ i) η) hα

end CalabiYau.DifferentialForm
