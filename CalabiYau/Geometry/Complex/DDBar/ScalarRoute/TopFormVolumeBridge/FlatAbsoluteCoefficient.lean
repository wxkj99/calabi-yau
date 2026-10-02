module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.Basic
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.CoordinateBasis

import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.ExteriorPair
import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.DiagonalCounting
import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.FlatLastPairCoefficient

/-!
# Absolute coefficient of the flat Kähler power

Wells, *Differential Analysis on Complex Manifolds*, third edition (2008),
V §1, equations (1.5) and (1.9)–(1.12), pp. 157–158, uses
`Ω = (i/2) ∑ dzⱼ ∧ dbarzⱼ = ∑ dxⱼ ∧ dyⱼ` and proves
`Ωⁿ = n! dx₁ ∧ dy₁ ∧ ⋯ ∧ dxₙ ∧ dyₙ`.

The project's `omegaFlat` is twice this coordinate expression:
`eta j = 2 dxⱼ ∧ dyⱼ` and `omegaFlat = ∑ j, eta j`.
Thus its raw top power has coefficient `n! * 2^n`, not `n!`.
The wedge is the ordinary exterior product, and `wedgePow` does not
include division by a factorial. `topFormCoeff` uses the interleaved
positive frame `(e₀, Ie₀, …, eₙ₋₁, Ieₙ₋₁)`.

In dimension zero the wedge power is the scalar unit, so its coefficient
is one even though the flat two-form is the empty sum. In dimensions
one and two the raw coefficients are respectively `+2` and `+8`.
No determinant, relative-trace, nonvanishing or geometric hypothesis
is imposed on this fixed standard-coordinate evaluation.
-/

public section

namespace ContinuousAlternatingMap

private noncomputable def directLeftStep {n : ℕ} (η : Form n 2) {k : ℕ}
    (θ : Form n (2 * k)) : Form n (2 * (k + 1)) :=
  (η ∧[ℝ] θ).domDomCongr (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1)))

private noncomputable def directTuple {n : ℕ} {ι : Type*}
    (η : ι → Form n 2) : (k : ℕ) → (Fin k → ι) → Form n (2 * k)
  | 0, _ => constOfIsEmpty ℝ (V n) (Fin 0) 1
  | k + 1, f => directLeftStep (η (f 0)) (directTuple η k (f ∘ Fin.succ))

private theorem directLeftStep_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (η : ι → Form n 2) {k : ℕ} (θ : Form n (2 * k)) :
    directLeftStep (∑ i, η i) θ = ∑ i, directLeftStep (η i) θ := by
  classical
  let s : Finset ι := Finset.univ
  suffices h : ∀ t : Finset ι, directLeftStep (∑ i ∈ t, η i) θ =
      ∑ i ∈ t, directLeftStep (η i) θ by simpa [s] using h s
  intro t
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change ContinuousAlternatingMap.domDomCongr _ ((0 : Form n 2) ∧[ℝ] θ) = 0
      rw [← zero_smul ℝ (0 : Form n 2), ContinuousAlternatingMap.smul_wedge,
        ContinuousAlternatingMap.domDomCongr_smul, zero_smul]
  | @insert i t hit ih =>
      simp only [Finset.sum_insert hit]
      change ContinuousAlternatingMap.domDomCongr _ ((η i + ∑ j ∈ t, η j) ∧[ℝ] θ) = _
      rw [ContinuousAlternatingMap.add_wedge, ContinuousAlternatingMap.domDomCongr_add]
      exact congrArg (directLeftStep (η i) θ + ·) ih

private theorem directLeftStep_sum_right {n : ℕ} {ι : Type*} [Fintype ι]
    (η : Form n 2) {k : ℕ} (θ : ι → Form n (2 * k)) :
    directLeftStep η (∑ i, θ i) = ∑ i, directLeftStep η (θ i) := by
  classical
  let s : Finset ι := Finset.univ
  suffices h : ∀ t : Finset ι, directLeftStep η (∑ i ∈ t, θ i) =
      ∑ i ∈ t, directLeftStep η (θ i) by simpa [s] using h s
  intro t
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change ContinuousAlternatingMap.domDomCongr _ (η ∧[ℝ] (0 : Form n (2 * k))) = 0
      rw [← zero_smul ℝ (0 : Form n (2 * k)), ContinuousAlternatingMap.wedge_smul,
        ContinuousAlternatingMap.domDomCongr_smul, zero_smul]
  | @insert i t hit ih =>
      simp only [Finset.sum_insert hit]
      change ContinuousAlternatingMap.domDomCongr _ (η ∧[ℝ] (θ i + ∑ j ∈ t, θ j)) = _
      rw [ContinuousAlternatingMap.wedge_add, ContinuousAlternatingMap.domDomCongr_add]
      exact congrArg (directLeftStep η (θ i) + ·) ih

private theorem directWedgeExpansion {n : ℕ} {ι : Type*} [Fintype ι]
    (η : ι → Form n 2) (k : ℕ) :
    wedgePow (∑ i, η i) k = ∑ f : Fin k → ι, directTuple η k f := by
  classical
  induction k with
  | zero => simp [wedgePow, directTuple]
  | succ k ih =>
      change directLeftStep (∑ i, η i) (wedgePow (∑ i, η i) k) = _
      rw [ih, directLeftStep_sum]
      simp only [directLeftStep_sum_right]
      calc
        (∑ i : ι, ∑ f : Fin k → ι, directLeftStep (η i) (directTuple η k f)) =
            ∑ p : ι × (Fin k → ι), directLeftStep (η p.1) (directTuple η k p.2) := by
          simp only [Fintype.sum_prod_type]
        _ = ∑ f : Fin (k + 1) → ι, directTuple η (k + 1) f := by
          let e := Fin.consEquiv (fun _ : Fin (k + 1) => ι)
          calc
            (∑ p : ι × (Fin k → ι), directLeftStep (η p.1) (directTuple η k p.2)) =
                ∑ p : ι × (Fin k → ι), directTuple η (k + 1) (e p) := by
              apply Finset.sum_congr rfl
              intro ⟨i, f⟩ _
              rfl
            _ = _ := Equiv.sum_comp e (directTuple η (k + 1))

private noncomputable def directInterleavedIndex (n : ℕ) :
    Fin n × Fin 2 ≃ Fin (2 * n) :=
  (finProdFinEquiv (m := n) (n := 2)).trans
    (Equiv.cast (congrArg Fin (by omega : n * 2 = 2 * n)))

private theorem interleaved_dual_dx (n : ℕ) (j : Fin n) :
    (complexInterleavedBasis n).cDualBasis (directInterleavedIndex n (j, 0)) = dx j := by
  ext x
  change (complexInterleavedBasis n).dualBasis (directInterleavedIndex n (j, 0)) x = dx j x
  rw [Module.Basis.dualBasis_apply]
  rw [complexInterleavedBasis, Module.Basis.repr_reindex_apply]
  unfold directInterleavedIndex
  rw [Equiv.symm_apply_apply]
  simp [Module.Basis.smulTower'_repr, dx, EuclideanSpace.basisFun_repr,
    Complex.coe_basisOneI_repr]

private theorem interleaved_dual_dy (n : ℕ) (j : Fin n) :
    (complexInterleavedBasis n).cDualBasis (directInterleavedIndex n (j, 1)) = dy j := by
  ext x
  change (complexInterleavedBasis n).dualBasis (directInterleavedIndex n (j, 1)) x = dy j x
  rw [Module.Basis.dualBasis_apply]
  rw [complexInterleavedBasis, Module.Basis.repr_reindex_apply]
  unfold directInterleavedIndex
  rw [Equiv.symm_apply_apply]
  simp [Module.Basis.smulTower'_repr, dy, EuclideanSpace.basisFun_repr,
    Complex.coe_basisOneI_repr]

private theorem directOneForm {n d : ℕ}
    (B : Module.Basis (Fin d) ℝ (V n →L[ℝ] ℝ)) (i : Fin d) :
    ContinuousAlternatingMap.ofSubsingleton ℝ (V n) ℝ (0 : Fin 1) (B i) =
      elementaryCovector B (fun _ : Fin 1 => i) := by
  ext v
  rw [elementaryCovector_apply]
  rw [Matrix.det_fin_one]
  simp

private noncomputable def directCovectorBasis (n : ℕ) :
    Module.Basis (Fin (2 * n)) ℝ (V n →L[ℝ] ℝ) :=
  (complexInterleavedBasis n).cDualBasis

private theorem directEta (n : ℕ) (j : Fin n) :
    eta j = (2 : ℝ) • elementaryCovector (directCovectorBasis n)
      (fun i : Fin 2 => directInterleavedIndex n (j, i)) := by
  classical
  rw [eta]
  have hdx : dx j = directCovectorBasis n (directInterleavedIndex n (j, 0)) := by
    simpa [directCovectorBasis] using (interleaved_dual_dx n j).symm
  have hdy : dy j = directCovectorBasis n (directInterleavedIndex n (j, 1)) := by
    simpa [directCovectorBasis] using (interleaved_dual_dy n j).symm
  rw [hdx, hdy]
  rw [directOneForm, directOneForm]
  rw [ContinuousAlternatingMap.elementaryCovector_wedge]
  apply congrArg (fun f : Form n 2 => (2 : ℝ) • f)
  apply congrArg (elementaryCovector (directCovectorBasis n))
  funext i
  fin_cases i <;> simp [Fin.addCases, directInterleavedIndex]

/-- The unnormalized flat top power has absolute coefficient `n! * 2^n`
in the positive interleaved real frame, including the degree-zero unit. -/
theorem omegaFlat_topFormCoeff (n : ℕ) :
    topFormCoeff (wedgePow (omegaFlat (n := n)) n) =
      (n.factorial : ℝ) * 2 ^ n := by
  have omegaFlat_topFormCoeff_succ_recurrence (k : ℕ) :
      topFormCoeff (wedgePow (omegaFlat (n := k + 1)) (k + 1)) =
        ((k + 1 : ℕ) : ℝ) * 2 *
          topFormCoeff (wedgePow (omegaFlat (n := k)) k) := by
    by_cases hk : k = 0
    · subst k
      have hpow : wedgePow (omegaFlat (n := 1)) 1 = flatLastPairTop 0 := by
        have hflat : omegaFlat (n := 1) = eta (Fin.last 0) := by
          simp [omegaFlat]
        conv_lhs => rw [hflat]
        rfl
      calc
        topFormCoeff (wedgePow (omegaFlat (n := 1)) 1) =
            topFormCoeff (flatLastPairTop 0) := congrArg topFormCoeff hpow
        _ = 2 * topFormCoeff (wedgePow (omegaFlat (n := 0)) 0) := by
          rw [topFormCoeff_flatLastPairTop]
        _ = ((0 + 1 : ℕ) : ℝ) * 2 *
            topFormCoeff (wedgePow (omegaFlat (n := 0)) 0) := by
          norm_num
    · have hkpos : 0 < k := by omega
      let d : Fin (k + 1) → ℝ := fun i => if i = Fin.last k then 1 else 0
      have halphaD : (eta (Fin.last k)).coeffMatrix =
          Matrix.diagonal (fun i : Fin (k + 1) => (d i : ℂ)) := by
        rw [eta_coeffMatrix]
        congr 1
        funext i
        by_cases hi : i = Fin.last k <;> simp [d, hi]
      have hcount := diagonal_trace_wedge_counting
        (n := k + 1) (by omega) (fun j => eta_wedge_self_zero j)
        (fun i j => eta_wedge_comm i j)
        (omegaFlat (n := k + 1)) (eta (Fin.last k))
        omegaFlat_isOneOne (eta_isOneOne (Fin.last k))
        omegaFlat_coeffMatrix d halphaD
      have htrace : (omegaFlat (n := k + 1)).relTrace (eta (Fin.last k)) = 1 := by
        rw [relTrace, omegaFlat_coeffMatrix, eta_coeffMatrix]
        simp [Matrix.trace_diagonal, Finset.sum_ite_eq', Finset.mem_univ]
      have hcount' :
          wedgePow (omegaFlat (n := k + 1)) (k + 1) =
            ((k + 1 : ℕ) : ℝ) • flatLastPairTop k := by
        calc
          wedgePow (omegaFlat (n := k + 1)) (k + 1) =
              1 • wedgePow (omegaFlat (n := k + 1)) (k + 1) := by simp
          _ = ((omegaFlat (n := k + 1)).relTrace (eta (Fin.last k))) •
                wedgePow (omegaFlat (n := k + 1)) (k + 1) :=
            (congrArg (fun c : ℝ => c • wedgePow (omegaFlat (n := k + 1)) (k + 1))
              htrace).symm
          _ = ((k + 1 : ℕ) : ℝ) •
                mixedWedgeOfPos (by omega) (eta (Fin.last k))
                  (omegaFlat (n := k + 1)) := hcount
          _ = ((k + 1 : ℕ) : ℝ) • flatLastPairTop k :=
            congrArg (fun β => ((k + 1 : ℕ) : ℝ) • β)
              (omegaFlat_mixedWedge_lastPair k)
      have hcoeff := congrArg topFormCoeff hcount'
      have hcoeff' :
          topFormCoeff (wedgePow (omegaFlat (n := k + 1)) (k + 1)) =
            ((k + 1 : ℕ) : ℝ) * topFormCoeff (flatLastPairTop k) := by
        change topFormCoeff (wedgePow (omegaFlat (n := k + 1)) (k + 1)) =
          ((k + 1 : ℕ) : ℝ) * topFormCoeff (flatLastPairTop k) at hcoeff
        exact hcoeff
      rw [topFormCoeff_flatLastPairTop] at hcoeff'
      calc
        topFormCoeff (wedgePow (omegaFlat (n := k + 1)) (k + 1)) =
            ((k + 1 : ℕ) : ℝ) * (2 *
              topFormCoeff (wedgePow (omegaFlat (n := k)) k)) := hcoeff'
        _ = _ := by ring
  induction n with
  | zero =>
      simp [topFormCoeff, wedgePow]
  | succ n ih =>
      rw [omegaFlat_topFormCoeff_succ_recurrence n, ih, Nat.factorial_succ]
      push_cast
      ring

end ContinuousAlternatingMap
