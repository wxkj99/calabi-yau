module

public import CalabiYau.Geometry.Complex.DDBar.Basic
public import CalabiYau.Geometry.Complex.DDBar.DDBarPotential

/-!
# The real `(1,1)` bridge

The complex theorem is stated on real/imaginary pairs of form fields. Applying it to a real form
with zero imaginary part and taking the first projection gives precisely the frozen real
`SatisfiesDDBarLemma` predicate.
-/

@[expose] public section

open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

namespace KahlerForm

/-- A Kähler form on a compact complex manifold supplies the metric needed by H5 and hence
satisfies the frozen real `(1,1)` `∂∂̄` predicate. -/
theorem satisfiesDDBarLemma_of_compact [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) : SatisfiesDDBarLemma n M := by
  intro α hαsmooth hαone hαexact
  let αc : ComplexFormField (EuclideanSpace ℂ (Fin n)) M 2 := (α, 0)
  have hαc_smooth : αc.IsSmooth := ⟨hαsmooth, FormField.isSmooth_zero⟩
  have hαc_one : αc.IsOneOne (complexTangentJ n) := by
    intro x u v
    exact ⟨hαone x u v, by simp [αc]⟩
  obtain ⟨β, hβsmooth, hβext⟩ := hαexact
  have hαc_exact : αc.IsExact := by
    refine ⟨(β, 0), ⟨hβsmooth, FormField.isSmooth_zero⟩, ?_⟩
    change (β.extDeriv, (0 : FormField (EuclideanSpace ℂ (Fin n)) M 1).extDeriv) =
      (α, 0)
    simp [hβext, FormField.extDeriv_zero]
  obtain ⟨f, hf, hEq⟩ :=
    exists_complexMddbar_eq_of_isExact (ω₀ := ω₀) hαc_smooth hαc_one hαc_exact
  refine ⟨f.1, hf.1, ?_⟩
  have hRe : α = mddbar n f.1 := congrArg Prod.fst hEq
  simpa [αc, complexMddbar] using hRe

end KahlerForm
