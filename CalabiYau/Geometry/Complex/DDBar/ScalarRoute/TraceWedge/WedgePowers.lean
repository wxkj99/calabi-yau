module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.WedgeUnit

/-!
# Unnormalized powers of a real two-form

These are exterior powers, not powers divided by a factorial: `wedgePow ω 0`
is the scalar one and `wedgePow ω (k + 1)` places `ω` to the LEFT of
`wedgePow ω k`. In positive complex dimension, `mixedWedgeOfPos hn α ω`
is `α ∧ ωⁿ⁻¹`, with the mixed factor on the left.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, Lemma 4.7,
for the ordinary (unnormalized) powers of the Kähler form in the trace–wedge
identity. The continuous-form wedge and its factorial convention are in
`CalabiYau.Geometry.Manifold.Tensor.Alternating.Wedge`.
-/

@[expose] public section

namespace ContinuousAlternatingMap

/-- Raw wedge powers of a real two-form, including the nonzero degree-zero unit. -/
noncomputable def wedgePow {n : ℕ}
    (ω : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (k : ℕ) → EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ
  | 0 => constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n)) (Fin 0) 1
  | k + 1 => (ω ∧[ℝ] wedgePow ω k).domDomCongr
      (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1)))

/-- One mixed factor followed by `n - 1` background factors (`n > 0`). -/
noncomputable def mixedWedgeOfPos {n : ℕ} (hn : 0 < n)
    (α ω : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * n)]→L[ℝ] ℝ :=
  (α ∧[ℝ] wedgePow ω (n - 1)).domDomCongr
    (Fin.castOrderIso (by omega : 2 + 2 * (n - 1) = 2 * n))

end ContinuousAlternatingMap
