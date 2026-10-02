module

public import CalabiYau.Geometry.Kahler.Basic

/-!
# The `∂∂̄`-lemma (hypothesis)

On a compact Kähler manifold, a smooth real `(1,1)`-form which is `d`-exact is `i∂∂̄` of a
smooth real function. This is the `∂∂̄`-lemma for real `(1,1)`-forms; its proof needs Hodge
theory on compact Kähler manifolds (the Kähler identities and the Hodge decomposition), the
subject of track H.

`SatisfiesDDBarLemma n M` states the conclusion as a property of `M`. It is **not proved here**:
the cohomological form of the Calabi conjecture takes it as an explicit hypothesis,
and track H is expected to prove, for compact `M`,

  `∀ ω₀ : KahlerForm n M, SatisfiesDDBarLemma n M`.

The converse (`i∂∂̄f` is exact) is `isExact_mddbar`. The consequence is that the
Kähler forms cohomologous to `ω₀` are exactly the `ω₀ + i∂∂̄φ` (`exists_perturb_eq_of_isExact`).
-/

@[expose] public section

open scoped Manifold ContDiff

variable (n : ℕ) (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The `∂∂̄`-lemma for real `(1,1)`-forms on `M`: every smooth, exact, real `(1,1)`-form is
`i∂∂̄f` for a smooth real function `f`. -/
def SatisfiesDDBarLemma : Prop :=
  ∀ α : FormField (EuclideanSpace ℂ (Fin n)) M 2, α.IsSmooth → α.IsOneOne → α.IsExact →
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f ∧ α = mddbar n f

variable {n M}

namespace KahlerForm

/-- Under the `∂∂̄`-lemma, the Kähler forms in the class `[ω₀]` are the `ω₀ + i∂∂̄φ`. -/
theorem exists_perturb_eq_of_isExact (hdd : SatisfiesDDBarLemma n M) (ω₀ ω₁ : KahlerForm n M)
    (h : (ω₁.toFormField - ω₀.toFormField).IsExact) :
    ∃ (φ : M → ℝ) (hφ : ω₀.IsPotential φ), ω₀.perturb φ hφ = ω₁ := by
  obtain ⟨f, hf, hdiff⟩ := hdd (ω₁.toFormField - ω₀.toFormField)
    (ω₁.isSmooth.sub ω₀.isSmooth)
    (fun x ↦ (ω₁.isOneOne x).sub (ω₀.isOneOne x)) h
  have hpotential : ω₀.IsPotential f := by
    refine ⟨hf, ?_⟩
    intro x
    have hsum : ω₀.toFormField x + mddbar n f x = ω₁.toFormField x := by
      have hx := congrArg (fun α : FormField (EuclideanSpace ℂ (Fin n)) M 2 => α x) hdiff
      dsimp at hx
      rw [← hx]
      abel
    change (ω₀.toFormField x + mddbar n f x).IsPositive
    rw [hsum]
    exact ω₁.isPositive x
  refine ⟨f, hpotential, ?_⟩
  apply KahlerForm.ext
  intro x
  rw [perturb_apply hpotential x]
  have hx := congrArg (fun α : FormField (EuclideanSpace ℂ (Fin n)) M 2 => α x) hdiff
  dsimp at hx
  rw [← hx]
  abel

/-- Conversely, `ω₀ + i∂∂̄φ` is cohomologous to `ω₀` (no hypothesis needed). -/
theorem isExact_perturb_sub {ω₀ : KahlerForm n M} {φ : M → ℝ} (hφ : ω₀.IsPotential φ) :
    ((ω₀.perturb φ hφ).toFormField - ω₀.toFormField).IsExact := by
  change ((ω₀.toFormField + mddbar n φ) - ω₀.toFormField).IsExact
  simpa only [add_sub_cancel_left] using isExact_mddbar hφ.1

end KahlerForm
