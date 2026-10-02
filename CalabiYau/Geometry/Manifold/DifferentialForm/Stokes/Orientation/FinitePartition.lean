module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Orientation.PositiveNeighborhood
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.LocalChart

/-!
# A finite partition subordinate to compatible positive chart pieces

Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 15.5,
p. 381, Proposition 15.6, p. 382, and equation (16.2), p. 405: a common smooth
nonvanishing reference form gives locally signed charts, compatible at every
point of every component of each overlap, and a finite subordinate partition.

This is a packaging corollary of the existing raw finite-partition theorem.
Center membership is an output of this covering construction, not a condition
on the general local-chart core. No integration functional, independence of
partitions, scalar measure identification, or global Stokes claim is made.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]
  [T2Space M] [CompactSpace M]

/-- Package the raw reference-form neighborhoods and finite partition into
positive oriented chart pieces with full restricted-overlap compatibility.
Closed partition supports lie in the selected open domains; canonical center
membership and the pointwise finite sum remain valid for the empty manifold. -/
theorem exists_finite_oriented_chart_partition
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0) :
    ∃ (C : M → OrientedLocalChart d M)
      (ρ : SmoothPartitionOfUnity M 𝓘(ℝ, Fin d → ℝ) M Set.univ)
      (s : Finset M),
      And (∀ x : M, And ((C x).center = x) (x ∈ (C x).domain))
        (And (∀ x : M, (C x).IsPositiveFor ν)
          (And (∀ x y : M, (C x).Compatible (C y))
            (And (ρ.IsSubordinate (fun x => (C x).domain))
              (∀ p : M, ∑ i ∈ s, ρ i p = 1)))) := by
  obtain ⟨V, σ, ρ, s, hV, hpos, hρ, hs⟩ :=
    exists_finite_orientation_form_chart_partition ν hν
  let C : M → OrientedLocalChart d M := fun x =>
    { center := x
      domain := V x
      sign := σ x
      isOpen_domain := (hV x).1
      domain_subset := (hV x).2.2 }
  have hC : ∀ x : M, (C x).IsPositiveFor ν := by
    intro x p hp
    exact hpos x p hp
  refine ⟨C, ρ, s, ?_, hC, ?_, ?_, hs⟩
  · intro x
    exact ⟨rfl, (hV x).2.1⟩
  · intro x y
    exact OrientedLocalChart.compatible_of_isPositiveFor
      (C x) (C y) ν (hC x) (hC y)
  · exact hρ

end CalabiYau.DifferentialForm
