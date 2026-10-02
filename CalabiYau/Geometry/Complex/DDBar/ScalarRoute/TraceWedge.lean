module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.DiagonalCounting
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.ExteriorPair
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.PullbackNaturality
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.HodgeRiemann.PrimitiveDiagonal

/-!
# Trace–wedge identity for real `(1,1)`-forms

For a positive form `ω` and an arbitrary real `(1,1)`-form `α`, the product
of the relative trace with `ω^n` is `n` times the mixed wedge. The proof uses
a common normal frame, exterior-pair identities, diagonal counting, and
pullback naturality.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics* (GSM 152),
Lemma 4.7, p. 60.
-/

@[expose] public section

namespace ContinuousAlternatingMap

/-- In complex dimension one, the mixed wedge uses the degree-zero unit. -/
private theorem mixedWedgeOfPos_one (α ω : Form 1 2) :
    mixedWedgeOfPos (by decide : 0 < 1) α ω = α := by
  change ((α ∧[ℝ] constOfIsEmpty ℝ (V 1) (Fin 0) (1 : ℝ)).domDomCongr
    (Fin.castOrderIso (by decide : 2 + 2 * (1 - 1) = 2 * 1))) = α
  rw [ContinuousAlternatingMap.wedge_right_unit]
  ext v
  rfl

/-- In complex dimension one, the second wedge power is the form itself. -/
private theorem wedgePow_one (ω : Form 1 2) : wedgePow ω 1 = ω := by
  change ((ω ∧[ℝ] constOfIsEmpty ℝ (V 1) (Fin 0) (1 : ℝ)).domDomCongr
    (Fin.castOrderIso (by decide : 2 + 2 * 0 = 2 * (0 + 1)))) = ω
  rw [ContinuousAlternatingMap.wedge_right_unit]
  ext v
  rfl

/-- Pullback by a linear equivalence is injective on top-degree forms. -/
private theorem trace_wedge_pullback_reverse {n : ℕ} (hn : 0 < n)
    (ω α : Form n 2) (hω : ω.IsOneOne) (hα : α.IsOneOne)
    (A : V n ≃L[ℂ] V n)
    (hframe : ((relTrace (ω.compContinuousLinearMap
        (A.toContinuousLinearMap.restrictScalars ℝ))
      (α.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ))) •
        wedgePow (ω.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)) n =
      (n : ℝ) • mixedWedgeOfPos hn
        (α.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ))
        (ω.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)))) :
    (relTrace ω α) • wedgePow ω n =
      (n : ℝ) • mixedWedgeOfPos hn α ω := by
  have hinj : Function.Injective
      (fun η : Form n (2 * n) => η.compContinuousLinearMap
        (A.toContinuousLinearMap.restrictScalars ℝ)) := by
    intro η θ h
    ext v
    have heq := congrArg (fun ξ : Form n (2 * n) => ξ (A.symm ∘ v)) h
    simpa [compContinuousLinearMap_apply, Function.comp_def] using heq
  apply hinj
  change ((relTrace ω α) • wedgePow ω n).compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ) =
    ((n : ℝ) • mixedWedgeOfPos hn α ω).compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)
  rw [compContinuousLinearMap_smul, compContinuousLinearMap_smul,
    wedgePow_pullback, mixedWedge_pullback,
    ← relTrace_compContinuousLinearMap hω hα A]
  exact hframe

/-- The one-dimensional trace–wedge identity in a normalized frame. -/
private theorem diagonal_trace_one (ω α : Form 1 2)
    (hω : ω.IsOneOne) (hα : α.IsOneOne)
    (hωI : ω.coeffMatrix = 1) (d : Fin 1 → ℝ)
    (hαD : α.coeffMatrix = Matrix.diagonal (fun i ↦ (d i : ℂ))) :
    (relTrace ω α) • ω = α := by
  have halpha : α = (d 0) • ω := by
    apply hα.ext (hω.smul (d 0))
    rw [hαD, ContinuousAlternatingMap.coeffMatrix_smul, hωI]
    ext i j
    fin_cases i
    fin_cases j
    simp
  have htrace : relTrace ω ω = (1 : ℝ) := by
    simp [relTrace, hωI, Matrix.trace_one]
  rw [halpha, ContinuousAlternatingMap.relTrace_smul, htrace]
  simp

/--
For a positive real `(1,1)`-form `ω` and an arbitrary real `(1,1)`-form `α`,
the relative trace of `α` with respect to `ω` gives the mixed wedge identity.
Powers are the bare repeated wedge powers (not divided by factorials), and
`α` occupies the left slot of `mixedWedgeOfPos`.
-/
theorem trace_wedge {n : ℕ} (hn : 0 < n) (ω α : Form n 2)
    (hω : ω.IsPositive) (hα : α.IsOneOne) :
    (relTrace ω α) • wedgePow ω n =
      (n : ℝ) • mixedWedgeOfPos hn α ω := by
  obtain ⟨A, d, hωI, hαD⟩ :=
    exists_normalFrame_diagonal_equiv ω α hω hα
  let ω' : Form n 2 := ω.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)
  let α' : Form n 2 := α.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)
  have hω' : ω'.IsOneOne := hω.1.compContinuousLinearMap
    (A : V n →L[ℂ] V n)
  have hα' : α'.IsOneOne := hα.compContinuousLinearMap
    (A : V n →L[ℂ] V n)
  apply trace_wedge_pullback_reverse hn ω α hω.1 hα A
  by_cases h1 : n = 1
  · subst n
    have hscalar := diagonal_trace_one ω' α' hω' hα' hωI d hαD
    simpa [ω', α', wedgePow_one, mixedWedgeOfPos_one] using hscalar
  · have hn2 : 1 < n := by omega
    have hsq := fun j : Fin n => eta_wedge_self_zero j
    have hcomm := fun i j : Fin n => eta_wedge_comm i j
    simpa only [Subsingleton.elim (Nat.zero_lt_of_lt hn2) hn] using
      diagonal_trace_wedge_counting hn2 hsq hcomm ω' α' hω' hα' hωI d hαD

end ContinuousAlternatingMap
