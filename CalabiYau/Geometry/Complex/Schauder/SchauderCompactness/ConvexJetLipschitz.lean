module

public import CalabiYau.Geometry.Complex.Holder
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lipschitz and lower-exponent bounds for Schauder jets

On a convex set, the mean-value inequality turns the next-jet supremum bounds in
`HolderBoundOn` into Lipschitz bounds for the lower jets. Bounded diameter then lowers the
Hölder exponent with its explicit diameter factor. The arguments also cover empty and
subsingleton compact sets.
-/

@[expose] public section

open Set
open scoped ContDiff NNReal Topology

namespace CalabiYau.Schauder

private theorem edist_le_toNNReal_ediam_of_mem {E : Type*} [PseudoMetricSpace E]
    {K : Set E} (hK : IsCompact K) {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    edist x y ≤ ((Metric.ediam K).toNNReal : ENNReal) := by
  have htop : Metric.ediam K ≠ ⊤ := hK.isBounded.ediam_ne_top
  rw [ENNReal.coe_toNNReal htop]
  exact Metric.edist_le_ediam_of_mem hx hy

/-- Lower the exponent of any Lipschitz function on a compact set. The constant is the
Lipschitz constant times the explicit factor `diam(K)^(1-β)`. This statement does not require
`K` to have positive diameter, so it applies in particular to empty and singleton sets. -/
lemma holderOnWith_of_lipschitzOnWith_of_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (hK : IsCompact K) {f : E → F} {C β : ℝ≥0}
    (hLip : LipschitzOnWith C f K) (hβone : β ≤ 1) :
    HolderOnWith (C * (Metric.ediam K).toNNReal ^ ((1 : ℝ) - (β : ℝ))) β f K := by
  have hdiam : ∀ x ∈ K, ∀ y ∈ K,
      edist x y ≤ ((Metric.ediam K).toNNReal : ENNReal) := by
    intro x hx y hy
    exact edist_le_toNNReal_ediam_of_mem hK hx hy
  simpa using hLip.holderOnWith.of_le hdiam hβone

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A `HolderBoundOn 2` bound and smoothness on a neighborhood control both the function and its
first derivative Lipschitzly on a convex compact set. The constants are exactly the common
supremum bound; no positive-diameter assumption is needed. -/
theorem lipschitzOnWith_function_and_firstDerivative_of_holderBoundOn
    {K U : Set E} (hKconvex : Convex ℝ K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → F} {α C : ℝ≥0}
    (hsmooth : ContDiffOn ℝ 2 f U) (hbound : HolderBoundOn 2 α C K f) :
    LipschitzOnWith C f K ∧
      LipschitzOnWith C (fun x => iteratedFDeriv ℝ 1 f x) K := by
  have hdiff0 (x : E) (hx : x ∈ K) : DifferentiableAt ℝ f x :=
    (hsmooth.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by norm_num)
  have hdiff1lt : (↑(1 : ℕ) : ℕ∞ω) < (↑(2 : ℕ) : ℕ∞ω) := by
    exact_mod_cast (show (1 : ℕ) < 2 by norm_num)
  have hdiff1 (x : E) (hx : x ∈ K) :
      DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ 1 f y) x :=
    (hsmooth.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt_iteratedFDeriv hdiff1lt
  have hLip0 : LipschitzOnWith C f K := by
    apply hKconvex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact hdiff0
    · intro x hx
      have hb : ‖fderiv ℝ f x‖ ≤ (C : ℝ) := by
        simpa only [norm_iteratedFDeriv_one] using hbound.1 1 (by norm_num) x hx
      exact_mod_cast hb
  have hLip1 : LipschitzOnWith C (fun x => iteratedFDeriv ℝ 1 f x) K := by
    apply hKconvex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact hdiff1
    · intro x hx
      have hb : ‖fderiv ℝ (fun y => iteratedFDeriv ℝ 1 f y) x‖ ≤ (C : ℝ) := by
        rw [norm_fderiv_iteratedFDeriv]
        exact hbound.1 2 le_rfl x hx
      exact_mod_cast hb
  exact ⟨hLip0, hLip1⟩

end CalabiYau.Schauder
