module

public import CalabiYau.Analysis.Elliptic.Schauder.OperatorCommutator
public import CalabiYau.Analysis.Elliptic.Schauder.DerivativeHolder
public import CalabiYau.Analysis.Elliptic.Schauder.OperatorCommutator.HolderBound.CoefficientDirectionalDerivative
public import CalabiYau.Analysis.Elliptic.Schauder.OperatorCommutator.HolderBound.ComplexHessianEntry
public import CalabiYau.Analysis.Elliptic.Schauder.OperatorCommutator.HolderBound.TraceProduct

/-!
# Hölder bounds for the differentiated coefficient commutator

This module estimates the term `re tr ((Dₑ A) * complexHessian u)` on nested interior sets.
The coefficient bound is entrywise and the trace contracts `(Dₑ A)ᵢⱼ` with `H(u)ⱼᵢ`.
-/

@[expose] public section

open Set Matrix
open scoped NNReal

namespace CalabiYau.Schauder

/-- A finite-dimensional Hölder estimate for the first-order coefficient--Hessian commutator.
Convexity of the intermediate set `V` keeps line segments between points of `V` inside `U` and
lets bounds on the highest derivatives control lower-order differences across this localization,
including pairs of nearby points. The constant is chosen before `A`, `u`, `e`, and their Hölder
bound `H`; in particular it is uniform in
the data and the direction of norm at most one. -/
theorem exists_holderBoundOn_directional_commutator
    {n k : ℕ} {α K : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {U V W : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V) (hVconvex : Convex ℝ V)
    (hVU : closure V ⊆ U) (hWV : W ⊆ V) :
    ∃ Ccomm : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (u : EuclideanSpace ℂ (Fin n) → ℝ) (e : EuclideanSpace ℂ (Fin n)) (H : ℝ≥0),
      (∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U) →
      ContDiffOn ℝ (k + 2) u U →
      (∀ i j, HolderBoundOn (k + 1) α K U (fun z ↦ A z i j)) →
      HolderBoundOn (k + 2) α H V u →
      ‖e‖ ≤ 1 →
      HolderBoundOn k α (Ccomm * H) W
        (fun z ↦ RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) := by
  let Ccomm : ℝ≥0 :=
    8 * (2 : ℝ≥0) ^ k * (Fintype.card (Fin n × Fin n) : ℝ≥0) * 4 * K
  refine ⟨Ccomm, ?_⟩
  intro A u e H hACont huCont hA hu he
  have hVU : V ⊆ U := Set.Subset.trans subset_closure hVU
  have hCoeff := holderBoundOn_coefficient_directional_derivative
    hU hVU A e hACont hA he
  have hHessian := holderBoundOn_complexHessian_entry hU hVU huCont hu
  let F : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ fderiv ℝ A z e
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := complexHessian u
  have hF : ∀ i j,
      ContDiffOn ℝ k (fun z ↦ F z i j) V ∧ HolderBoundOn k α K V (fun z ↦ F z i j) := by
    intro i j
    simpa [F] using hCoeff i j
  have hG : ∀ i j,
      ContDiffOn ℝ k (fun z ↦ G z i j) V ∧ HolderBoundOn k α (4 * H) V (fun z ↦ G z i j) := by
    intro i j
    simpa [G] using hHessian i j
  have htrace := holderBoundOn_real_trace_product_convex hα₀ hα₁ hV hVconvex F G hF hG
  have hconst :
      8 * (2 : ℝ≥0) ^ k * (Fintype.card (Fin n × Fin n) : ℝ≥0) * K * (4 * H) =
        Ccomm * H := by
    dsimp [Ccomm]
    ring
  have htrace' : HolderBoundOn k α (Ccomm * H) V
      (fun z ↦ RCLike.re ((F z * G z).trace)) := by
    rw [← hconst]
    exact htrace
  have htraceW := htrace'.mono_set hWV
  simpa [F, G] using htraceW

end CalabiYau.Schauder
