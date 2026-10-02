module

public import CalabiYau.Analysis.Elliptic.Schauder

/-!
# Fixed-order slice of the interior Schauder estimate

The predicate below is the exact k-slice of the frozen target. It exists only to make the k
induction explicit; it introduces no extra hypotheses or altered constants.
-/

open Set Matrix
open scoped Manifold ContDiff NNReal

@[expose] public section

/-- The exact order-k slice of `InteriorSchauderEstimate`. -/
def InteriorSchauderOrder (n k : ℕ) : Prop :=
  ∀ (α : ℝ≥0), 0 < α → α < 1 →
    ∀ (lam K : ℝ≥0), 0 < lam →
      ∀ U V : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → IsCompact (closure V) →
        closure V ⊆ U →
        ∃ C : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
          (u : EuclideanSpace ℂ (Fin n) → ℝ),
          (∀ j l, ContDiffOn ℝ k (fun z ↦ A z j l) U) → ContDiffOn ℝ 2 u U →
          IsUniformlyEllipticOn A lam U →
          (∀ j l, HolderBoundOn k α K U fun z ↦ A z j l) →
          ∀ K₀ K₁ : ℝ≥0, ContDiffOn ℝ k (complexEllipticOp A u) U →
            HolderBoundOn k α K₁ U (complexEllipticOp A u) →
            (∀ z ∈ U, |u z| ≤ K₀) →
            ContDiffOn ℝ (k + 2) u U ∧
              HolderBoundOn (k + 2) α (C * (K₁ + K₀)) V u

/-- The all-orders target is definitionally equivalent to all its fixed-order slices. -/
theorem interiorSchauderEstimate_iff_forall_order (n : ℕ) :
    InteriorSchauderEstimate n ↔ ∀ k, InteriorSchauderOrder n k := Iff.rfl

end
