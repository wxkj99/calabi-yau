module

public import CalabiYau.Yau.CalabiConjecture

/-!
# Ricci-flat Kähler metrics

Special cases `ρ = 0` of the Calabi conjecture:

* if `Ric(ω₀) = i∂∂̄F` for a smooth `F`, then `ω₀ + i∂∂̄φ` is Ricci-flat for some Kähler
  potential `φ`, unique up to a constant (T2 with `ρ = 0`);
* if `c₁(M) = 0` in real cohomology, every Kähler class contains exactly one Ricci-flat Kähler
  form (T3 with `ρ = 0`).

As in `CalabiYau.Yau.CalabiConjecture`, existence is derived from
`KahlerForm.MongeAmpereSolvable` and, for the second statement, from the `∂∂̄`-lemma.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]

omit [ConnectedSpace M] in
/-- If `Ric(ω₀) = i∂∂̄F`, some `ω₀ + i∂∂̄φ` is Ricci-flat. -/
theorem exists_isRicciFlat_of_ricciForm_eq_mddbar (ω₀ : KahlerForm n M)
    (hMA : ω₀.MongeAmpereSolvable) {F : M → ℝ}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F) (h : ω₀.ricciForm = mddbar n F) :
    ∃ (φ : M → ℝ) (hφ : ω₀.IsPotential φ), (ω₀.perturb φ hφ).IsRicciFlat := by
  have hneg : mddbar n (-F) = -mddbar n F := by
    simpa using (mddbar_smul hF (-1))
  have hρ : (0 : FormField (EuclideanSpace ℂ (Fin n)) M 2) - ω₀.ricciForm =
      mddbar n (-F) := by
    rw [zero_sub, h]
    exact hneg.symm
  have hnegF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (-F) := hF.neg
  obtain ⟨φ, hφ, hRicci⟩ :=
    exists_ricciForm_eq_of_sub_eq_mddbar ω₀ hMA hnegF hρ
  exact ⟨φ, hφ, hRicci⟩

/-- If `c₁(M) = 0` in real cohomology, the Kähler class of `ω₀` contains a unique Ricci-flat
Kähler form. -/
theorem existsUnique_isRicciFlat_of_firstChernClass_eq_zero (ω₀ : KahlerForm n M)
    (hMA : ω₀.MongeAmpereSolvable) (hdd : SatisfiesDDBarLemma n M)
    (hc : (0 : FormField (EuclideanSpace ℂ (Fin n)) M 2).RepresentsFirstChernClass) :
    ∃ ω₁ : KahlerForm n M, (ω₁.toFormField - ω₀.toFormField).IsExact ∧ ω₁.IsRicciFlat ∧
      ∀ ω₂ : KahlerForm n M, (ω₂.toFormField - ω₀.toFormField).IsExact → ω₂.IsRicciFlat →
        ω₂ = ω₁ := by
  have hc' : ((2 * Real.pi)⁻¹ • (0 : FormField (EuclideanSpace ℂ (Fin n)) M 2)).RepresentsFirstChernClass := by
    simpa using hc
  obtain ⟨ω₁, hExact, hRicci⟩ :=
    exists_ricciForm_eq_of_representsFirstChernClass ω₀ hMA hdd
      FormField.isSmooth_zero (fun _ ↦ ContinuousAlternatingMap.isOneOne_zero) hc'
  refine ⟨ω₁, hExact, hRicci, ?_⟩
  intro ω₂ h₂Exact h₂Ricci
  have hDiff : (ω₁.toFormField - ω₂.toFormField).IsExact := by
    have h := hExact.sub h₂Exact
    convert h using 1; abel
  exact eq_of_ricciForm_eq_of_isExact hdd hDiff (h₂Ricci.trans hRicci.symm)

end KahlerForm
