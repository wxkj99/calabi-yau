module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Kahler.Ricci
import Comparator.Assembly

/-!
# The three target theorems

Standalone, unconditional statements of the deliverables T1–T3 of `docs/ROADMAP.md`, in terms of
the definitions of `CalabiYau.Geometry.Complex` and `CalabiYau.Geometry.Kahler` (which depend on
Mathlib only). The proofs are to be supplied by the project; nothing here may be changed without
review.

Setting, common to all statements: `M` is a compact connected (Hausdorff) complex manifold of
complex dimension `n`, i.e. a `ChartedSpace` over `ℂⁿ = EuclideanSpace ℂ (Fin n)` with complex
analytic transition maps (`IsManifold 𝓘(ℂ, ℂⁿ) ω M`); `ω₀` is a Kähler form on `M`
(`KahlerForm n M`: a smooth, closed, positive real `(1,1)`-form). Smoothness of real functions is
for the underlying real manifold, `ContMDiff 𝓘(ℝ, ℂⁿ) 𝓘(ℝ) ∞`. The Borel measure `ω₀.volume` is
`ω₀ⁿ / n!`.

Reading guide for the definitions:

* `mddbar n φ` is the real `(1,1)`-form `i∂∂̄φ`;
* `ω₀.IsPotential φ` means `φ` is smooth and `ω₀ + i∂∂̄φ > 0`, and `ω₀.perturb φ hφ` is the
  Kähler form `ω₀ + i∂∂̄φ`;
* `ω₀.mongeAmpere φ x = (ω₀ + i∂∂̄φ)ⁿ / ω₀ⁿ` at `x`, computed as
  `det(g_{jk̄} + φ_{jk̄}) / det g_{jk̄}` in holomorphic coordinates;
* `ω₀.ricciForm = -i∂∂̄ log det(g_{jk̄})` is the Ricci form;
* `FormField.IsExact` is `d`-exactness (by a smooth `1`-form), so `(α - β).IsExact` means
  `[α] = [β]` in de Rham cohomology;
* `γ.RepresentsFirstChernClass` means `[γ] = c₁(M)` in `H²(M; ℝ)`, with `c₁(M)` represented by
  `Ric(ω) / 2π` for any Kähler form `ω` (Chern–Weil).
-/

@[expose] public section

open scoped Manifold ContDiff
open Set MeasureTheory

namespace CalabiYau

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

/-- **T1 (Yau's theorem: the complex Monge–Ampère equation).** Let `(M, ω₀)` be a compact
connected Kähler manifold and `F` a smooth real function with `∫ e^F ω₀ⁿ = ∫ ω₀ⁿ`. Then there is
a smooth `φ`, unique up to an additive constant, with `ω₀ + i∂∂̄φ > 0` and
`(ω₀ + i∂∂̄φ)ⁿ = e^F ω₀ⁿ`. -/
theorem complexMongeAmpere [MeasurableSpace M] [BorelSpace M] (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (hnorm : ∫ x, Real.exp (F x) ∂ω₀.volume = ω₀.volume.real univ) :
    ∃ φ : M → ℝ, ω₀.IsPotential φ ∧ (∀ x, ω₀.mongeAmpere φ x = Real.exp (F x)) ∧
      ∀ ψ : M → ℝ, ω₀.IsPotential ψ → (∀ x, ω₀.mongeAmpere ψ x = Real.exp (F x)) →
        ∃ c : ℝ, ∀ x, ψ x = φ x + c := by
  exact complexMongeAmpere_assembled ω₀ F hF hnorm

/-- **T2 (the Calabi conjecture, potential form).** If `ρ - Ric(ω₀) = i∂∂̄F` for a smooth real
function `F`, there is a unique Kähler form `ω₀ + i∂∂̄φ` whose Ricci form is `ρ`. -/
theorem calabiConjecture_of_sub_eq_mddbar (ω₀ : KahlerForm n M)
    (ρ : FormField (EuclideanSpace ℂ (Fin n)) M 2) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (hρ : ρ - ω₀.ricciForm = mddbar n F) :
    ∃ (φ : M → ℝ) (hφ : ω₀.IsPotential φ), (ω₀.perturb φ hφ).ricciForm = ρ ∧
      ∀ (ψ : M → ℝ) (hψ : ω₀.IsPotential ψ), (ω₀.perturb ψ hψ).ricciForm = ρ →
        ω₀.perturb ψ hψ = ω₀.perturb φ hφ := by
  exact calabiConjecture_of_sub_eq_mddbar_assembled ω₀ ρ F hF hρ

/-- **T2, Ricci-flat case.** If `Ric(ω₀) = i∂∂̄F` for a smooth real function `F`, there is a unique
Ricci-flat Kähler form of the form `ω₀ + i∂∂̄φ`. -/
theorem ricciFlat_of_ricciForm_eq_mddbar (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (h : ω₀.ricciForm = mddbar n F) :
    ∃ (φ : M → ℝ) (hφ : ω₀.IsPotential φ), (ω₀.perturb φ hφ).IsRicciFlat ∧
      ∀ (ψ : M → ℝ) (hψ : ω₀.IsPotential ψ), (ω₀.perturb ψ hψ).IsRicciFlat →
        ω₀.perturb ψ hψ = ω₀.perturb φ hφ := by
  exact ricciFlat_of_ricciForm_eq_mddbar_assembled ω₀ F hF h

/-- **T3 (the Calabi conjecture, cohomological form).** If `ρ` is a smooth closed real
`(1,1)`-form with `[ρ] = 2π c₁(M)`, the Kähler class `[ω₀]` contains a unique Kähler form whose
Ricci form is `ρ`. -/
theorem calabiConjecture (ω₀ : KahlerForm n M) (ρ : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hρs : ρ.IsSmooth) (hρ : ρ.IsOneOne) (hρc : ρ.IsClosed)
    (hc₁ : ((2 * Real.pi)⁻¹ • ρ).RepresentsFirstChernClass) :
    ∃ ω₁ : KahlerForm n M, (ω₁.toFormField - ω₀.toFormField).IsExact ∧ ω₁.ricciForm = ρ ∧
      ∀ ω₂ : KahlerForm n M, (ω₂.toFormField - ω₀.toFormField).IsExact →
        ω₂.ricciForm = ρ → ω₂ = ω₁ := by
  exact calabiConjecture_assembled ω₀ ρ hρs hρ hρc hc₁

/-- **T3, Ricci-flat case.** If `c₁(M) = 0` in `H²(M; ℝ)`, every Kähler class contains a unique
Ricci-flat Kähler form. -/
theorem ricciFlat_of_firstChernClass_eq_zero (ω₀ : KahlerForm n M)
    (hc₁ : (0 : FormField (EuclideanSpace ℂ (Fin n)) M 2).RepresentsFirstChernClass) :
    ∃ ω₁ : KahlerForm n M, (ω₁.toFormField - ω₀.toFormField).IsExact ∧ ω₁.IsRicciFlat ∧
      ∀ ω₂ : KahlerForm n M, (ω₂.toFormField - ω₀.toFormField).IsExact →
        ω₂.IsRicciFlat → ω₂ = ω₁ := by
  exact ricciFlat_of_firstChernClass_eq_zero_assembled ω₀ hc₁

end CalabiYau
