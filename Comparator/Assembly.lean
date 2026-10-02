module

public import CalabiYau.MongeAmpere.Existence
public import CalabiYau.Yau.RicciFlat
import CalabiYau.MongeAmpere.Uniqueness
import Comparator.SobolevInequality
import Comparator.PoincareInequality
import Comparator.InteriorSchauderEstimate
import Comparator.PoissonSolvability
import Comparator.DDBarLemma

/-!
# Assembly of the Calabi–Yau theorem

The five global analytic inputs are stated separately in `Comparator`. This module assembles
those inputs with the conditional Monge–Ampère existence theorem, Calabi's uniqueness theorem,
and the conditional Ricci and cohomological theorems in `CalabiYau.Yau`. No global input is
silently assumed and none of the proofs below uses a placeholder.

For the potential and cohomological statements, the Borel measurable structure is installed
locally: the frozen target statements do not have measurable-space parameters. The T3 statement
retains its explicit closedness hypothesis even though the Chern-class condition already implies
closedness in the conditional existence theorem.
-/

@[expose] public section

open scoped Manifold ContDiff
open Set MeasureTheory

namespace CalabiYau

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

section Measurable

variable [MeasurableSpace M] [BorelSpace M]

/-- The four global analytic inputs supply the hypotheses of Yau's conditional continuity
argument for each background Kähler form. -/
theorem mongeAmpereSolvable_of_compact (ω₀ : KahlerForm n M) :
    ω₀.MongeAmpereSolvable := by
  obtain ⟨κ, C_S, hκ, hS⟩ := sobolevInequality_of_compact ω₀
  obtain ⟨C_P, _, hP⟩ := poincareInequality_of_compact ω₀
  exact KahlerForm.mongeAmpereSolvable
    (interiorSchauderEstimate_all n) (poissonSolvable_of_compact (n := n) (M := M))
    ω₀ hκ hS hP

/-- The complex Monge–Ampère target, assembled from global existence and Calabi uniqueness. -/
theorem complexMongeAmpere_assembled (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (hnorm : ∫ x, Real.exp (F x) ∂ω₀.volume = ω₀.volume.real univ) :
    ∃ φ : M → ℝ, ω₀.IsPotential φ ∧ (∀ x, ω₀.mongeAmpere φ x = Real.exp (F x)) ∧
      ∀ ψ : M → ℝ, ω₀.IsPotential ψ → (∀ x, ω₀.mongeAmpere ψ x = Real.exp (F x)) →
        ∃ c : ℝ, ∀ x, ψ x = φ x + c := by
  obtain ⟨φ, hsol⟩ := (mongeAmpereSolvable_of_compact ω₀) F hF hnorm
  refine ⟨φ, hsol.1, hsol.2, ?_⟩
  intro ψ hψ hψeq
  exact KahlerForm.SolvesMongeAmpere.eq_add_const hsol ⟨hψ, hψeq⟩

end Measurable

/-- The potential formulation of the Calabi conjecture, with the canonical Borel measure used
only inside the proof. -/
theorem calabiConjecture_of_sub_eq_mddbar_assembled (ω₀ : KahlerForm n M)
    (ρ : FormField (EuclideanSpace ℂ (Fin n)) M 2) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (hρ : ρ - ω₀.ricciForm = mddbar n F) :
    ∃ (φ : M → ℝ) (hφ : ω₀.IsPotential φ), (ω₀.perturb φ hφ).ricciForm = ρ ∧
      ∀ (ψ : M → ℝ) (hψ : ω₀.IsPotential ψ), (ω₀.perturb ψ hψ).ricciForm = ρ →
        ω₀.perturb ψ hψ = ω₀.perturb φ hφ := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  obtain ⟨φ, hφ, hRic⟩ := KahlerForm.exists_ricciForm_eq_of_sub_eq_mddbar ω₀
    (mongeAmpereSolvable_of_compact ω₀) hF hρ
  refine ⟨φ, hφ, hRic, ?_⟩
  intro ψ hψ hψRic
  exact KahlerForm.perturb_eq_of_ricciForm_eq hψ hφ (hψRic.trans hRic.symm)

/-- The Ricci-flat potential formulation, using the same global Monge–Ampère input. -/
theorem ricciFlat_of_ricciForm_eq_mddbar_assembled (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (h : ω₀.ricciForm = mddbar n F) :
    ∃ (φ : M → ℝ) (hφ : ω₀.IsPotential φ), (ω₀.perturb φ hφ).IsRicciFlat ∧
      ∀ (ψ : M → ℝ) (hψ : ω₀.IsPotential ψ), (ω₀.perturb ψ hψ).IsRicciFlat →
        ω₀.perturb ψ hψ = ω₀.perturb φ hφ := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  obtain ⟨φ, hφ, hRic⟩ := KahlerForm.exists_isRicciFlat_of_ricciForm_eq_mddbar ω₀
    (mongeAmpereSolvable_of_compact ω₀) hF h
  refine ⟨φ, hφ, hRic, ?_⟩
  intro ψ hψ hψRic
  have heq : (ω₀.perturb ψ hψ).ricciForm = (ω₀.perturb φ hφ).ricciForm := by
    change (ω₀.perturb ψ hψ).ricciForm = 0 at hψRic
    change (ω₀.perturb φ hφ).ricciForm = 0 at hRic
    exact hψRic.trans hRic.symm
  exact KahlerForm.perturb_eq_of_ricciForm_eq hψ hφ heq

/-- The cohomological Calabi conjecture, requiring the compact Kähler `∂∂̄` lemma for
existence and for uniqueness in the whole Kähler class. -/
theorem calabiConjecture_assembled (ω₀ : KahlerForm n M)
    (ρ : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hρs : ρ.IsSmooth) (hρ : ρ.IsOneOne) (hρc : ρ.IsClosed)
    (hc₁ : ((2 * Real.pi)⁻¹ • ρ).RepresentsFirstChernClass) :
    ∃ ω₁ : KahlerForm n M, (ω₁.toFormField - ω₀.toFormField).IsExact ∧ ω₁.ricciForm = ρ ∧
      ∀ ω₂ : KahlerForm n M, (ω₂.toFormField - ω₀.toFormField).IsExact →
        ω₂.ricciForm = ρ → ω₂ = ω₁ := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  have hdd : SatisfiesDDBarLemma n M := satisfiesDDBarLemma_of_compact ω₀
  obtain ⟨ω₁, hExact, hRic⟩ :=
    KahlerForm.exists_ricciForm_eq_of_representsFirstChernClass ω₀
      (mongeAmpereSolvable_of_compact ω₀) hdd hρs hρ hc₁
  refine ⟨ω₁, hExact, hRic, ?_⟩
  intro ω₂ h₂Exact h₂Ric
  have hDiff : (ω₁.toFormField - ω₂.toFormField).IsExact := by
    have h := hExact.sub h₂Exact
    convert h using 1 <;> abel
  exact KahlerForm.eq_of_ricciForm_eq_of_isExact hdd hDiff (h₂Ric.trans hRic.symm)

/-- The Ricci-flat cohomological consequence, with uniqueness in the whole Kähler class. -/
theorem ricciFlat_of_firstChernClass_eq_zero_assembled (ω₀ : KahlerForm n M)
    (hc₁ : (0 : FormField (EuclideanSpace ℂ (Fin n)) M 2).RepresentsFirstChernClass) :
    ∃ ω₁ : KahlerForm n M, (ω₁.toFormField - ω₀.toFormField).IsExact ∧ ω₁.IsRicciFlat ∧
      ∀ ω₂ : KahlerForm n M, (ω₂.toFormField - ω₀.toFormField).IsExact →
        ω₂.IsRicciFlat → ω₂ = ω₁ := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact KahlerForm.existsUnique_isRicciFlat_of_firstChernClass_eq_zero ω₀
    (mongeAmpereSolvable_of_compact ω₀) (satisfiesDDBarLemma_of_compact ω₀) hc₁

end CalabiYau
