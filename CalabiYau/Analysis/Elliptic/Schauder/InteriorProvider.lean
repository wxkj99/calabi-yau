module

public import CalabiYau.Analysis.Elliptic.Schauder
public import CalabiYau.Analysis.Elliptic.Schauder.InteriorProvider.Order
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity
public import CalabiYau.Analysis.Elliptic.Schauder.FirstOrderRegularity
public import CalabiYau.Analysis.Elliptic.Schauder.HigherOrder

/-!
# All-orders interior Schauder provider

The all-orders statement follows from the fixed-order slices: the base case at order zero, the
first-order bridge, and the higher-order successor step.
-/

@[expose] public section

/-- Interior Schauder regularity and estimates in every dimension and order. -/
theorem interiorSchauderEstimate_all : ∀ n, InteriorSchauderEstimate n := by
  intro n
  rw [interiorSchauderEstimate_iff_forall_order]
  intro k
  induction k with
  | zero =>
      exact interiorSchauderBaseRegularity n
  | succ k ih =>
      cases k with
      | zero =>
          exact first_order_regularity n ih
      | succ k =>
          exact interiorSchauderOrder_succ (by omega) ih

end
