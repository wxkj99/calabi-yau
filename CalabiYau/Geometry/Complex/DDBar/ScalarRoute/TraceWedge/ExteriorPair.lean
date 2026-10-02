module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.CoordinateBasis

/-!
# Exterior algebra identities for coordinate two-forms

The normalized real coordinate block `eta j = 2 dxⱼ ∧ dyⱼ` squares to zero,
and two-forms commute under the project's alternating wedge. These identities
supply the pairwise exterior algebra facts used in the diagonal trace–wedge
calculation.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, Lemma 4.7,
p. 60; the normalized wedge identities are in
`CalabiYau.Geometry.Manifold.Tensor.Alternating.Wedge`.
-/

@[expose] public section

namespace ContinuousAlternatingMap

private theorem reindex_zero {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {k l : ℕ} (e : Fin k ≃ Fin l) :
    ContinuousAlternatingMap.domDomCongr e (0 : M [⋀^Fin k]→L[ℝ] ℝ) = 0 := by
  ext x
  rfl

private theorem decomposable_wedge_square_zero {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    (u v : M [⋀^Fin 1]→L[ℝ] ℝ) :
    ((u ∧[ℝ] v) ∧[ℝ] (u ∧[ℝ] v)) = 0 := by
  have hvv : (v ∧[ℝ] v) = 0 := by
    exact ContinuousAlternatingMap.wedge_self_odd_zero v (by decide) (by norm_num)
  have hright : ((u ∧[ℝ] v) ∧[ℝ] v) = 0 := by
    have hh := ContinuousAlternatingMap.wedge_mul_assoc u v v
    rw [hvv] at hh
    have hz : (u ∧[ℝ] (0 : M [⋀^Fin 2]→L[ℝ] ℝ)) = 0 := by
      simpa using (ContinuousAlternatingMap.wedge_smul (0 : ℝ) u (v ∧[ℝ] v)
        (ContinuousLinearMap.mul ℝ ℝ))
    rw [hz] at hh
    simpa only [reindex_zero] using hh.symm
  have hmiddle : (v ∧[ℝ] (u ∧[ℝ] v)) = 0 := by
    have hh := ContinuousAlternatingMap.wedge_antisymm v (u ∧[ℝ] v)
    rw [hright] at hh
    simpa only [ContinuousAlternatingMap.domDomCongr_smul, reindex_zero, smul_zero] using hh
  have hh := ContinuousAlternatingMap.wedge_mul_assoc u v (u ∧[ℝ] v)
  rw [hmiddle] at hh
  have hz : (u ∧[ℝ] (0 : M [⋀^Fin 3]→L[ℝ] ℝ)) = 0 := by
    simpa using (ContinuousAlternatingMap.wedge_smul (0 : ℝ) u
      (v ∧[ℝ] (u ∧[ℝ] v)) (ContinuousLinearMap.mul ℝ ℝ))
  rw [hz] at hh
  simpa only [reindex_zero] using hh.symm

private theorem twice_decomposable_wedge_square_zero {M : Type*}
    [NormedAddCommGroup M] [NormedSpace ℝ M]
    (u v : M [⋀^Fin 1]→L[ℝ] ℝ) :
    (((2 : ℝ) • (u ∧[ℝ] v)) ∧[ℝ] ((2 : ℝ) • (u ∧[ℝ] v))) = 0 := by
  rw [ContinuousAlternatingMap.smul_wedge,
    ContinuousAlternatingMap.wedge_smul, decomposable_wedge_square_zero]
  simp

/-- Each real coordinate two-form has square zero. -/
theorem eta_wedge_self_zero {n : ℕ} (j : Fin n) :
    (eta j ∧[ℝ] eta j) = (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ) := by
  rw [eta]
  exact twice_decomposable_wedge_square_zero
    (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) (dx j))
    (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) (dy j))

/-- Coordinate two-forms commute, with no negative sign in degree two. -/
theorem eta_wedge_comm {n : ℕ} (i j : Fin n) :
    (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i) := by
  simpa [Fin.finAddCongr, show (-1 : ℝ) ^ (2 * 2) = 1 by norm_num] using
    (ContinuousAlternatingMap.wedge_antisymm (eta i) (eta j))

end ContinuousAlternatingMap
