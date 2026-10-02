module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.CoordinateBasis
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.PullbackNaturality
import CalabiYau.Geometry.Manifold.DifferentialForm.Model

/-!
# The diagonal Hodge wedge quadratic

In a unitary frame, the square wedge `γ ∧ γ ∧ ω^(n-2)` is the normalized
quadratic `( (∑ λᵢ)^2 - ∑ λᵢ² ) / (n(n-1))` times `ω^n`. Powers are the
project's unnormalized left-recursive wedge powers.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §4.1,
polarized Lemma 4.7 (printed pp. 60–61).
-/

open scoped BigOperators

@[expose] section

namespace ContinuousAlternatingMap

/-- `γ ∧ γ ∧ ω^(n−2)`, with the canonical degree cast. -/
public noncomputable def hodgeWedgeSquare {n : ℕ} (hn : 2 ≤ n)
    (ω γ : Form n 2) : Form n (2 * n) :=
  ((γ ∧[ℝ] γ) ∧[ℝ] wedgePow ω (n - 2)).domDomCongr
    (Fin.castOrderIso (by omega : 2 + 2 + 2 * (n - 2) = 2 * n))

/-- The square wedge commutes with complex-linear pullback. -/
public theorem hodgeWedgeSquare_compContinuousLinearMap {n : ℕ} (hn : 2 ≤ n)
    (ω γ : Form n 2) (A : V n ≃L[ℂ] V n) :
    (hodgeWedgeSquare hn ω γ).compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ) =
      hodgeWedgeSquare hn
        (ω.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ))
        (γ.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)) := by
  simp only [hodgeWedgeSquare,
    CalabiYau.DifferentialForm.domDomCongr_compContinuousLinearMap,
    CalabiYau.DifferentialForm.wedge_product_compContinuousLinearMap,
    wedgePow_pullback]

end ContinuousAlternatingMap

end

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
private theorem eta_wedge_self_zero {n : ℕ} (j : Fin n) :
    (eta j ∧[ℝ] eta j) = (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ) := by
  rw [eta]
  exact twice_decomposable_wedge_square_zero
    (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) (dx j))
    (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) (dy j))

/-- Coordinate two-forms commute, with no negative sign in degree two. -/
private theorem eta_wedge_comm {n : ℕ} (i j : Fin n) :
    (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i) := by
  simpa [Fin.finAddCongr, show (-1 : ℝ) ^ (2 * 2) = 1 by norm_num] using
    (ContinuousAlternatingMap.wedge_antisymm (eta i) (eta j))

private theorem relTrace_diagonalForm {n : ℕ} (d : Fin n → ℝ) :
    (omegaFlat (n := n)).relTrace (diagonalForm d) = ∑ j, d j := by
  dsimp only [relTrace]
  rw [omegaFlat_coeffMatrix, diagonalForm_coeffMatrix]
  simp [Matrix.trace_diagonal]

private noncomputable def diagonalLeftStep {n : ℕ}
    (η : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) {k : ℕ}
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ) :
    EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * (k + 1))]→L[ℝ] ℝ :=
  (η ∧[ℝ] θ).domDomCongr (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1)))

private theorem diagonalLeftStep_reduce {n k : ℕ} (η : Form n 2)
    (θ : Form n (2 * k)) :
    diagonalLeftStep η θ =
      (η ∧[ℝ] θ).domDomCongr (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1))) := by
  rfl

private noncomputable def diagonalWedgeTuple {n : ℕ} {ι : Type*}
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (k : ℕ) → (Fin k → ι) →
      EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ
  | 0, _ => constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n)) (Fin 0) 1
  | k + 1, f => diagonalLeftStep (η (f 0))
      (diagonalWedgeTuple η k (f ∘ Fin.succ))

private theorem diagonalWedgeTuple_zero_reduce {n : ℕ} {ι : Type*}
    (η : ι → Form n 2) (f : Fin 0 → ι) :
    diagonalWedgeTuple η 0 f = constOfIsEmpty ℝ (V n) (Fin 0) 1 := by
  rfl

private theorem diagonalWedgeTuple_succ_reduce {n k : ℕ} {ι : Type*}
    (η : ι → Form n 2) (f : Fin (k + 1) → ι) :
    diagonalWedgeTuple η (k + 1) f =
      diagonalLeftStep (η (f 0)) (diagonalWedgeTuple η k (f ∘ Fin.succ)) := by
  rfl

private theorem diagonalLeftStep_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) {k : ℕ}
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ) :
    diagonalLeftStep (∑ i, η i) θ = ∑ i, diagonalLeftStep (η i) θ := by
  classical
  let s : Finset ι := Finset.univ
  suffices h : ∀ t : Finset ι, diagonalLeftStep (∑ i ∈ t, η i) θ =
      ∑ i ∈ t, diagonalLeftStep (η i) θ by simpa [s] using h s
  intro t
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change ContinuousAlternatingMap.domDomCongr _ ((0 :
        EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) ∧[ℝ] θ) = 0
      rw [← zero_smul ℝ (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ),
        ContinuousAlternatingMap.smul_wedge,
        ContinuousAlternatingMap.domDomCongr_smul, zero_smul]
  | @insert i t hit ih =>
      simp only [Finset.sum_insert hit]
      change ContinuousAlternatingMap.domDomCongr _
        ((η i + ∑ j ∈ t, η j) ∧[ℝ] θ) = _
      rw [ContinuousAlternatingMap.add_wedge, ContinuousAlternatingMap.domDomCongr_add]
      exact congrArg (diagonalLeftStep (η i) θ + ·) ih

private theorem diagonalLeftStep_sum_right {n : ℕ} {ι : Type*} [Fintype ι]
    (η : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) {k : ℕ}
    (θ : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ) :
    diagonalLeftStep η (∑ i, θ i) = ∑ i, diagonalLeftStep η (θ i) := by
  classical
  let s : Finset ι := Finset.univ
  suffices h : ∀ t : Finset ι, diagonalLeftStep η (∑ i ∈ t, θ i) =
      ∑ i ∈ t, diagonalLeftStep η (θ i) by simpa [s] using h s
  intro t
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change ContinuousAlternatingMap.domDomCongr _
        (η ∧[ℝ] (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ)) = 0
      rw [← zero_smul ℝ (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ),
        ContinuousAlternatingMap.wedge_smul,
        ContinuousAlternatingMap.domDomCongr_smul, zero_smul]
  | @insert i t hit ih =>
      simp only [Finset.sum_insert hit]
      change ContinuousAlternatingMap.domDomCongr _
        (η ∧[ℝ] (θ i + ∑ j ∈ t, θ j)) = _
      rw [ContinuousAlternatingMap.wedge_add, ContinuousAlternatingMap.domDomCongr_add]
      exact congrArg (diagonalLeftStep η (θ i) + ·) ih

private theorem wedgePow_eq_diagonalWedgeTuple_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ) :
    wedgePow (∑ i, η i) k = ∑ f : Fin k → ι, diagonalWedgeTuple η k f := by
  classical
  induction k with
  | zero => simp [wedgePow, diagonalWedgeTuple_zero_reduce]
  | succ k ih =>
      change diagonalLeftStep (∑ i, η i) (wedgePow (∑ i, η i) k) = _
      rw [ih, diagonalLeftStep_sum]
      simp only [diagonalLeftStep_sum_right]
      calc
        (∑ i : ι, ∑ f : Fin k → ι,
            diagonalLeftStep (η i) (diagonalWedgeTuple η k f)) =
            ∑ p : ι × (Fin k → ι),
              diagonalLeftStep (η p.1) (diagonalWedgeTuple η k p.2) := by
          simp only [Fintype.sum_prod_type]
        _ = ∑ f : Fin (k + 1) → ι, diagonalWedgeTuple η (k + 1) f := by
          let e := Fin.consEquiv (fun _ : Fin (k + 1) => ι)
          calc
            (∑ p : ι × (Fin k → ι),
                diagonalLeftStep (η p.1) (diagonalWedgeTuple η k p.2)) =
                ∑ p : ι × (Fin k → ι), diagonalWedgeTuple η (k + 1) (e p) := by
              apply Finset.sum_congr rfl
              intro ⟨i, f⟩ _
              rfl
            _ = _ := Equiv.sum_comp e (diagonalWedgeTuple η (k + 1))

private theorem diagonalLeftStep_smul {n k : ℕ} (c : ℝ)
    (η : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ) :
    diagonalLeftStep (c • η) θ = c • diagonalLeftStep η θ := by
  simp only [diagonalLeftStep_reduce, ContinuousAlternatingMap.smul_wedge,
    ContinuousAlternatingMap.domDomCongr_smul]

private theorem diagonal_smul_fintype_sum {ι : Type*} {M : Type*}
    [Fintype ι] [AddCommMonoid M] [DistribSMul ℝ M]
    (c : ℝ) (f : ι → M) : c • (∑ i, f i) = ∑ i, c • f i := by
  classical
  let s : Finset ι := Finset.univ
  suffices h : ∀ t : Finset ι, c • (∑ i ∈ t, f i) = ∑ i ∈ t, c • f i by
    simpa [s] using h s
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      simp only [Finset.sum_insert hi, smul_add, ih]

private theorem weighted_diagonalWedgeTuple_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (d : ι → ℝ) (k : ℕ) :
    diagonalLeftStep (∑ i, d i • η i) (wedgePow (∑ i, η i) k) =
      ∑ i, ∑ f : Fin k → ι,
        d i • diagonalWedgeTuple η (k + 1) (Fin.cons i f) := by
  classical
  rw [wedgePow_eq_diagonalWedgeTuple_sum, diagonalLeftStep_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalLeftStep_smul]
  rw [diagonalLeftStep_sum_right, diagonal_smul_fintype_sum]
  apply Finset.sum_congr rfl
  intro f _
  rfl

private noncomputable def diagonalBlockCast {m m' : ℕ} (e : Fin m ≃ Fin m') :
    Fin (2 + m) ≃ Fin (2 + m') :=
  ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
    ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
      (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))

private theorem diagonalBlockCast_reduce {m m' : ℕ} (e : Fin m ≃ Fin m') :
    diagonalBlockCast e =
      ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
        ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
          (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m'))) := by
  rfl

private theorem diagonalWedgeRightArithmeticCast {n m m' : ℕ}
    (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin m]→L[ℝ] ℝ) (hm : m = m') :
    (a ∧[ℝ] θ.domDomCongr (Fin.castOrderIso hm).toEquiv) =
      (a ∧[ℝ] θ).domDomCongr
        (diagonalBlockCast (Fin.castOrderIso hm).toEquiv) := by
  cases hm
  simp [diagonalBlockCast_reduce]

private theorem diagonalWedgeAssocCast {n k q : ℕ}
    (a b : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ)
    (e : Fin ((2 + 2) + 2 * k) ≃ Fin q) :
    (a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr (Fin.finAssoc.symm.trans e) =
      ((a ∧[ℝ] b) ∧[ℝ] θ).domDomCongr e := by
  simpa only [← ContinuousAlternatingMap.domDomCongr_trans] using
    congrArg (fun f => f.domDomCongr e) (ContinuousAlternatingMap.wedge_mul_assoc a b θ)

private theorem diagonalWedgePowStepAssocCast {n k : ℕ}
    (a b : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ) :
    diagonalLeftStep a (diagonalLeftStep b θ) =
      (a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr
        ((diagonalBlockCast (Fin.castOrderIso
          (by omega : 2 + 2 * k = 2 * (k + 1))).toEquiv).trans
          (Fin.castOrderIso (by omega : 2 + 2 * (k + 1) = 2 * (k + 2))).toEquiv) := by
  dsimp only [diagonalLeftStep]
  let e₁ : Fin (2 + 2 * k) ≃ Fin (2 * (k + 1)) :=
    (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1))).toEquiv
  let e₂ : Fin (2 + 2 * (k + 1)) ≃ Fin (2 * (k + 2)) :=
    (Fin.castOrderIso (by omega : 2 + 2 * (k + 1) = 2 * (k + 2))).toEquiv
  calc
    _ = ((a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr (diagonalBlockCast e₁)).domDomCongr e₂ := by
      exact congrArg (fun f => f.domDomCongr e₂)
        (diagonalWedgeRightArithmeticCast a (b ∧[ℝ] θ) (by omega))
    _ = _ := by rw [ContinuousAlternatingMap.domDomCongr_trans]

private theorem diagonalWedgePowStepFrontSwap {n k : ℕ}
    (a b : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ)
    (h : (a ∧[ℝ] b) = (b ∧[ℝ] a)) :
    diagonalLeftStep a (diagonalLeftStep b θ) = diagonalLeftStep b (diagonalLeftStep a θ) := by
  let eTot :=
    (diagonalBlockCast (Fin.castOrderIso
      (by omega : 2 + 2 * k = 2 * (k + 1))).toEquiv).trans
      (Fin.castOrderIso (by omega : 2 + 2 * (k + 1) = 2 * (k + 2))).toEquiv
  let ePair := Fin.finAssoc.trans eTot
  have he : Fin.finAssoc.symm.trans ePair = eTot := by
    calc
      _ = (Fin.finAssoc.symm.trans Fin.finAssoc).trans eTot := by
        rw [← Equiv.trans_assoc]
      _ = eTot := by simp
  have hAssocL :
      (a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr eTot =
        ((a ∧[ℝ] b) ∧[ℝ] θ).domDomCongr ePair := by
    rw [← he]
    exact diagonalWedgeAssocCast a b θ ePair
  have hAssocR :
      (b ∧[ℝ] (a ∧[ℝ] θ)).domDomCongr eTot =
        ((b ∧[ℝ] a) ∧[ℝ] θ).domDomCongr ePair := by
    rw [← he]
    exact diagonalWedgeAssocCast b a θ ePair
  have hPair : ((a ∧[ℝ] b) ∧[ℝ] θ).domDomCongr ePair =
      ((b ∧[ℝ] a) ∧[ℝ] θ).domDomCongr ePair :=
    congrArg (fun c : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ =>
      (c ∧[ℝ] θ).domDomCongr ePair) h
  calc
    diagonalLeftStep a (diagonalLeftStep b θ) =
        (a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr eTot := by
      simpa [eTot] using diagonalWedgePowStepAssocCast a b θ
    _ = ((a ∧[ℝ] b) ∧[ℝ] θ).domDomCongr ePair := hAssocL
    _ = ((b ∧[ℝ] a) ∧[ℝ] θ).domDomCongr ePair := hPair
    _ = (b ∧[ℝ] (a ∧[ℝ] θ)).domDomCongr eTot := hAssocR.symm
    _ = diagonalLeftStep b (diagonalLeftStep a θ) := by
      simpa [eTot] using (diagonalWedgePowStepAssocCast b a θ).symm

private theorem diagonalWedgePowStepRepeatZero {n k : ℕ}
    (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ)
    (h : (a ∧[ℝ] a) = 0) : diagonalLeftStep a (diagonalLeftStep a θ) = 0 := by
  let eTot :=
    (diagonalBlockCast (Fin.castOrderIso
      (by omega : 2 + 2 * k = 2 * (k + 1))).toEquiv).trans
      (Fin.castOrderIso (by omega : 2 + 2 * (k + 1) = 2 * (k + 2))).toEquiv
  let ePair := Fin.finAssoc.trans eTot
  have he : Fin.finAssoc.symm.trans ePair = eTot := by
    calc
      _ = (Fin.finAssoc.symm.trans Fin.finAssoc).trans eTot := by
        rw [← Equiv.trans_assoc]
      _ = eTot := by simp
  have hzero : ((0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ) ∧[ℝ] θ) = 0 := by
    rw [← zero_smul ℝ (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ),
      ContinuousAlternatingMap.smul_wedge]
    simp
  calc
    diagonalLeftStep a (diagonalLeftStep a θ) =
        (a ∧[ℝ] (a ∧[ℝ] θ)).domDomCongr eTot := by
      simpa [eTot] using diagonalWedgePowStepAssocCast a a θ
    _ = ((a ∧[ℝ] a) ∧[ℝ] θ).domDomCongr ePair := by
      rw [← he]
      exact diagonalWedgeAssocCast a a θ ePair
    _ = 0 := by rw [h, hzero]; ext v; rfl

private theorem diagonalWedgeTuple_front_swap {n k : ℕ} {ι : Type*}
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (i j : ι) (f : Fin k → ι)
    (h : (η i ∧[ℝ] η j) = (η j ∧[ℝ] η i)) :
    diagonalWedgeTuple η ((k + 1) + 1) (Fin.cons i (Fin.cons j f)) =
      diagonalWedgeTuple η ((k + 1) + 1) (Fin.cons j (Fin.cons i f)) := by
  change diagonalLeftStep (η i)
      (diagonalLeftStep (η j) (diagonalWedgeTuple η k f)) =
    diagonalLeftStep (η j) (diagonalLeftStep (η i) (diagonalWedgeTuple η k f))
  exact diagonalWedgePowStepFrontSwap (η i) (η j) (diagonalWedgeTuple η k f) h

private theorem diagonalWedgeTuple_first_repeat_zero {n k : ℕ} {ι : Type*}
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hsq : ∀ j, (η j ∧[ℝ] η j) = 0) (i : ι) (f : Fin k → ι) :
    diagonalWedgeTuple η ((k + 1) + 1) (Fin.cons i (Fin.cons i f)) = 0 := by
  change diagonalLeftStep (η i)
      (diagonalLeftStep (η i) (diagonalWedgeTuple η k f)) = 0
  exact diagonalWedgePowStepRepeatZero (η i) (diagonalWedgeTuple η k f) (hsq i)

private theorem diagonal_count_injective_endomaps (n : ℕ) :
    Fintype.card {f : Fin n → Fin n // Function.Injective f} = n.factorial := by
  let e : {f : Fin n → Fin n // Function.Injective f} ≃ (Fin n ↪ Fin n) := {
    toFun := fun f => ⟨f.1, f.2⟩
    invFun := fun f => ⟨f.1, f.2⟩
    left_inv := by intro f; cases f; rfl
    right_inv := by intro f; cases f; rfl }
  calc
    _ = Fintype.card (Fin n ↪ Fin n) := Fintype.card_congr e
    _ = n.factorial := by simp [Fintype.card_embedding_eq, Nat.descFactorial_self]

private theorem diagonal_count_fixed_fiber {n : ℕ} (i : Fin n) :
    Fintype.card {f : Fin (n - 1) → Fin n //
      Function.Injective f ∧ ∀ j, f j ≠ i} = (n - 1).factorial := by
  classical
  let m := n - 1
  let A := {x : Fin n // x ≠ i}
  let s : Finset (Fin n) := Finset.univ.erase i
  have hA : Fintype.card A = m := by
    let e : A ≃ {x : Fin n // x ∈ s} := {
      toFun := fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩
      invFun := fun x => ⟨x.1, (Finset.mem_erase.mp x.2).1⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
    calc
      Fintype.card A = Fintype.card {x : Fin n // x ∈ s} := Fintype.card_congr e
      _ = s.card := Fintype.card_coe s
      _ = n - 1 := by simp [s, Finset.card_erase_of_mem (Finset.mem_univ i)]
      _ = m := rfl
  let eAvoid :
      {f : Fin m → Fin n // Function.Injective f ∧ ∀ j, f j ≠ i} ≃
        (Fin m ↪ A) := {
    toFun := fun f => ⟨fun j => ⟨f.1 j, f.2.2 j⟩, fun {a b} hab =>
      f.2.1 (congrArg Subtype.val hab)⟩
    invFun := fun f => ⟨fun j => (f j).1,
      ⟨fun {a b} hab => f.injective (Subtype.ext hab), fun j => (f j).2⟩⟩
    left_inv := by intro f; apply Subtype.ext; funext j; rfl
    right_inv := by intro f; apply DFunLike.ext; intro j; rfl }
  calc
    Fintype.card {f : Fin (n - 1) → Fin n // Function.Injective f ∧ ∀ j, f j ≠ i} =
        Fintype.card (Fin m ↪ A) := Fintype.card_congr eAvoid
    _ = (Fintype.card A).descFactorial (Fintype.card (Fin m)) := by
      rw [Fintype.card_embedding_eq]
    _ = m.factorial := by simp [hA, m, Nat.descFactorial_self]

private noncomputable def diagonalWedgeListTuple {n : ℕ} {ι : Type*}
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (k : ℕ) → (l : List ι) → l.length = k →
      EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ
  | 0, [], _ => constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n)) (Fin 0) 1
  | 0, _ :: _, h => by simp at h
  | k + 1, [], h => by simp at h
  | k + 1, a :: l, h => diagonalLeftStep (η a)
      (diagonalWedgeListTuple η k l (by simp at h; omega))

private theorem diagonalWedgeListTuple_zero_reduce {n : ℕ} {ι : Type*}
    (η : ι → Form n 2) (h : ([] : List ι).length = 0) :
    diagonalWedgeListTuple η 0 [] h = constOfIsEmpty ℝ (V n) (Fin 0) 1 := by
  rfl

private theorem diagonalWedgeListTuple_cons_reduce {n k : ℕ} {ι : Type*}
    (η : ι → Form n 2) (a : ι) (l : List ι) (h : (a :: l).length = k + 1) :
    diagonalWedgeListTuple η (k + 1) (a :: l) h =
      diagonalLeftStep (η a) (diagonalWedgeListTuple η k l (by simp at h; omega)) := by
  rfl

private theorem diagonalWedgeTuple_eq_listTuple {n : ℕ} {ι : Type*}
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    ∀ (k : ℕ) (f : Fin k → ι),
      diagonalWedgeTuple η k f =
        diagonalWedgeListTuple η k (List.ofFn f) (by simp) := by
  intro k
  induction k with
  | zero => intro f; simp [diagonalWedgeTuple_zero_reduce, diagonalWedgeListTuple_zero_reduce]
  | succ k ih =>
      intro f
      simp only [List.ofFn_succ, diagonalWedgeTuple_succ_reduce, diagonalWedgeListTuple_cons_reduce]
      apply congrArg (diagonalLeftStep (η (f 0)))
      exact ih (f ∘ Fin.succ)

private theorem diagonalWedgeListTuple_front_swap {n : ℕ} {ι : Type*}
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hcomm : ∀ i j, (η i ∧[ℝ] η j) = (η j ∧[ℝ] η i))
    (i j : ι) (l : List ι) :
    diagonalWedgeListTuple η ((l.length + 1) + 1) (i :: j :: l) (by simp) =
      diagonalWedgeListTuple η ((l.length + 1) + 1) (j :: i :: l) (by simp) := by
  change diagonalLeftStep (η i)
      (diagonalLeftStep (η j) (diagonalWedgeListTuple η l.length l rfl)) =
    diagonalLeftStep (η j)
      (diagonalLeftStep (η i) (diagonalWedgeListTuple η l.length l rfl))
  exact diagonalWedgePowStepFrontSwap (η i) (η j)
    (diagonalWedgeListTuple η l.length l rfl) (hcomm i j)

private theorem diagonalWedgeListTuple_perm {n k : ℕ} {ι : Type*}
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hfront : ∀ (i j : ι) (l : List ι),
      diagonalWedgeListTuple η ((l.length + 1) + 1) (i :: j :: l) (by simp) =
        diagonalWedgeListTuple η ((l.length + 1) + 1) (j :: i :: l) (by simp))
    {l₁ l₂ : List ι} (h₁ : l₁.length = k) (h₂ : l₂.length = k)
    (hp : l₁.Perm l₂) :
    diagonalWedgeListTuple η k l₁ h₁ = diagonalWedgeListTuple η k l₂ h₂ := by
  revert k h₁ h₂
  induction hp with
  | nil =>
      intro k h₁ h₂
      cases k with
      | zero => rfl
      | succ k => simp at h₁
  | @cons a l₁ l₂ hp ih =>
      intro k h₁ h₂
      cases k with
      | zero => simp at h₁
      | succ k =>
          simp only [List.length_cons] at h₁ h₂
          have h₁' : l₁.length = k := by omega
          have h₂' : l₂.length = k := by omega
          simpa [diagonalWedgeListTuple_zero_reduce, diagonalWedgeListTuple_cons_reduce] using
            congrArg (diagonalLeftStep (η a)) (ih h₁' h₂')
  | @swap a b l =>
      intro k h₁ h₂
      have hk : k = ((l.length + 1) + 1) := by
        simp only [List.length_cons] at h₁
        omega
      subst k
      simpa [diagonalWedgeListTuple_zero_reduce, diagonalWedgeListTuple_cons_reduce] using hfront b a l
  | @trans l₁ l₂ l₃ hp₁ hp₂ ih₁ ih₂ =>
      intro k h₁ h₂
      have h₁₂ : l₂.length = k := by
        calc
          l₂.length = l₁.length := hp₁.length_eq.symm
          _ = k := h₁
      exact (ih₁ h₁ h₁₂).trans (ih₂ h₁₂ h₂)

private theorem diagonalWedgeListTuple_first_repeat_zero {n : ℕ} {ι : Type*}
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hsq : ∀ i, (η i ∧[ℝ] η i) = 0) (i : ι) (l : List ι) :
    diagonalWedgeListTuple η ((l.length + 1) + 1) (i :: i :: l) (by simp) = 0 := by
  change diagonalLeftStep (η i)
      (diagonalLeftStep (η i) (diagonalWedgeListTuple η l.length l rfl)) = 0
  exact diagonalWedgePowStepRepeatZero (η i)
    (diagonalWedgeListTuple η l.length l rfl) (hsq i)

private theorem diagonalWedgeTuple_noninjective_zero {n k : ℕ}
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (f : Fin k → Fin n) (hnot : ¬ Function.Injective f) :
    diagonalWedgeTuple eta k f = 0 := by
  let l := List.ofFn f
  have hn : ¬ l.Nodup := by
    intro hn
    exact hnot (List.nodup_ofFn.mp (by simpa [l] using hn))
  obtain ⟨a, ha⟩ := List.exists_duplicate_iff_not_nodup.mpr hn
  rw [List.duplicate_iff_sublist] at ha
  obtain ⟨r, hp⟩ := List.Sublist.exists_perm_append ha
  have hrlen : (a :: a :: r).length = k := by
    have hlen := hp.length_eq
    simpa [l] using hlen.symm
  have hfront (i j : Fin n) (t : List (Fin n)) :=
    diagonalWedgeListTuple_front_swap eta hcomm i j t
  have hperm := diagonalWedgeListTuple_perm eta hfront (by simp [l]) hrlen hp
  calc
    diagonalWedgeTuple eta k f = diagonalWedgeListTuple eta k l (by simp [l]) :=
      diagonalWedgeTuple_eq_listTuple eta k f
    _ = diagonalWedgeListTuple eta k (a :: a :: r) hrlen := hperm
    _ = 0 := by
      have hindex : k = (r.length + 1) + 1 := by simpa using hrlen.symm
      cases hindex
      exact diagonalWedgeListTuple_first_repeat_zero eta hsq a r

private theorem diagonalWedgeTuple_generic_noninjective_zero {n k : ℕ} (η : Fin n → Form n 2)
    (hsq : ∀ j : Fin n, (η j ∧[ℝ] η j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (η i ∧[ℝ] η j) = (η j ∧[ℝ] η i))
    (f : Fin k → Fin n) (hnot : ¬ Function.Injective f) :
    diagonalWedgeTuple η k f = 0 := by
  let l := List.ofFn f
  have hn : ¬ l.Nodup := by
    intro hn
    exact hnot (List.nodup_ofFn.mp (by simpa [l] using hn))
  obtain ⟨a, ha⟩ := List.exists_duplicate_iff_not_nodup.mpr hn
  rw [List.duplicate_iff_sublist] at ha
  obtain ⟨r, hp⟩ := List.Sublist.exists_perm_append ha
  have hrlen : (a :: a :: r).length = k := by
    have hlen := hp.length_eq
    simpa [l] using hlen.symm
  have hfront (i j : Fin n) (t : List (Fin n)) :=
    diagonalWedgeListTuple_front_swap η hcomm i j t
  have hperm := diagonalWedgeListTuple_perm η hfront (by simp [l]) hrlen hp
  calc
    diagonalWedgeTuple η k f = diagonalWedgeListTuple η k l (by simp [l]) :=
      diagonalWedgeTuple_eq_listTuple η k f
    _ = diagonalWedgeListTuple η k (a :: a :: r) hrlen := hperm
    _ = 0 := by
      have hindex : k = (r.length + 1) + 1 := by simpa using hrlen.symm
      cases hindex
      exact diagonalWedgeListTuple_first_repeat_zero η hsq a r

private theorem diagonal_tuple_classification {n : ℕ} (η : Fin n → Form n 2)
    (hsq : ∀ i, (η i ∧[ℝ] η i) = 0)
    (hcomm : ∀ i j, (η i ∧[ℝ] η j) = (η j ∧[ℝ] η i))
    (f : Fin n → Fin n) :
    diagonalWedgeTuple η n f = if Function.Injective f then diagonalWedgeTuple η n id else 0 := by
  classical
  split_ifs with hf
  · let e : Equiv.Perm (Fin n) :=
      Equiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩
    have hp : (List.ofFn f).Perm (List.ofFn (id : Fin n → Fin n)) :=
      e.ofFn_comp_perm id
    rw [diagonalWedgeTuple_eq_listTuple, diagonalWedgeTuple_eq_listTuple]
    exact diagonalWedgeListTuple_perm η
      (diagonalWedgeListTuple_front_swap η hcomm) (by simp) (by simp) hp
  · exact diagonalWedgeTuple_generic_noninjective_zero η hsq hcomm f hf

-- This is exactly the mixed-wedge final degree cast, shared with two-prefix counting.
private noncomputable def fullTuple {n k : ℕ} (η : Fin n → Form n 2)
    (hk : k = n) (f : Fin k → Fin n) : Form n (2 * n) :=
  (diagonalWedgeTuple η k f).domDomCongr (Fin.castOrderIso (congrArg (2 * ·) hk))

private theorem fullTuple_reduce {n k : ℕ} (η : Fin n → Form n 2)
    (hk : k = n) (f : Fin k → Fin n) :
    fullTuple η hk f =
      (diagonalWedgeTuple η k f).domDomCongr (Fin.castOrderIso (congrArg (2 * ·) hk)) := by
  rfl

private theorem fullTuple_classification {n k : ℕ} (η : Fin n → Form n 2)
    (hsq : ∀ i, (η i ∧[ℝ] η i) = 0)
    (hcomm : ∀ i j, (η i ∧[ℝ] η j) = (η j ∧[ℝ] η i))
    (hk : k = n) (f : Fin k → Fin n) :
    fullTuple η hk f = if Function.Injective f then diagonalWedgeTuple η n id else 0 := by
  subst k
  change diagonalWedgeTuple η n f = _
  exact diagonal_tuple_classification η hsq hcomm f

private theorem cons_injective_iff {n k : ℕ} (i : Fin n) (f : Fin k → Fin n) :
    Function.Injective (Fin.cons i f) ↔ Function.Injective f ∧ ∀ j, f j ≠ i := by
  simpa [Set.mem_range, and_comm] using (Fin.cons_injective_iff (x₀ := i) (x := f))

private theorem top_sum {n : ℕ} (η : Fin n → Form n 2)
    (hsq : ∀ i, (η i ∧[ℝ] η i) = 0)
    (hcomm : ∀ i j, (η i ∧[ℝ] η j) = (η j ∧[ℝ] η i)) :
    (∑ f : Fin n → Fin n, diagonalWedgeTuple η n f) = (n.factorial : ℝ) • diagonalWedgeTuple η n id := by
  classical
  have he : (∑ f : Fin n → Fin n, diagonalWedgeTuple η n f) =
      ∑ f : Fin n → Fin n, if Function.Injective f then diagonalWedgeTuple η n id else 0 := by
    apply Finset.sum_congr rfl
    intro f _
    exact diagonal_tuple_classification η hsq hcomm f
  rw [he]
  have hc : ((Finset.univ : Finset (Fin n → Fin n)).filter
      Function.Injective).card = n.factorial := by
    rw [← Fintype.card_subtype]
    exact diagonal_count_injective_endomaps n
  rw [← Finset.sum_filter, Finset.sum_const, hc]
  simp only [Nat.cast_smul_eq_nsmul]

private theorem cast_step {n k l : ℕ} (a : Form n 2) (θ : Form n (2 * k))
    (h : k + 1 = l) :
    (diagonalLeftStep a θ).domDomCongr (Fin.castOrderIso (congrArg (2 * ·) h)) =
      (a ∧[ℝ] θ).domDomCongr
        (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * l) : Fin (2 + 2 * k) ≃ Fin (2 * l)) := by
  rw [diagonalLeftStep_reduce, domDomCongr_trans]
  congr 1

private theorem cast_sum {n k l : ℕ} {ι : Type*} [Fintype ι] (h : k = l)
    (F : ι → Form n k) :
    (∑ i, F i).domDomCongr (Fin.castOrderIso h) =
      ∑ i, (F i).domDomCongr (Fin.castOrderIso h : Fin k ≃ Fin l) := by
  classical
  simpa using domDomCongr_sum (Fin.castOrderIso h : Fin k ≃ Fin l) Finset.univ F

private theorem wedge_cast_right {n m m' : ℕ} (a : Form n 2) (θ : Form n m)
    (h : m = m') :
    (a ∧[ℝ] θ.domDomCongr (Fin.castOrderIso h : Fin m ≃ Fin m')) =
      (a ∧[ℝ] θ).domDomCongr
        (Fin.castOrderIso (congrArg (2 + ·) h) : Fin (2 + m) ≃ Fin (2 + m')) := by
  subst m'
  rfl
-- Quadratic needs two distinct prescribed prefix labels; no new algebraic ring.
private theorem count_fixed_two_tail {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Fintype.card {f : Fin (n - 2) → Fin n //
      Function.Injective f ∧ ∀ k, f k ≠ i ∧ f k ≠ j} = (n - 2).factorial := by
  classical
  let m := n - 2
  let A := {x : Fin n // x ≠ i ∧ x ≠ j}
  let s : Finset (Fin n) := (Finset.univ.erase i).erase j
  have hA : Fintype.card A = m := by
    let e : A ≃ {x : Fin n // x ∈ s} := {
      toFun := fun x => ⟨x.1, by simp [s, x.2.1, x.2.2]⟩
      invFun := fun x => ⟨x.1,
        ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp x.2).2).1,
          (Finset.mem_erase.mp x.2).1⟩⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
    calc
      _ = Fintype.card {x : Fin n // x ∈ s} := Fintype.card_congr e
      _ = s.card := Fintype.card_coe s
      _ = n - 2 := by
        rw [Finset.card_erase_of_mem (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)]
        simp [Finset.card_erase_of_mem (Finset.mem_univ i), Nat.sub_sub]
      _ = m := rfl
  let eAvoid :
      {f : Fin m → Fin n // Function.Injective f ∧ ∀ k, f k ≠ i ∧ f k ≠ j} ≃
        (Fin m ↪ A) := {
    toFun := fun f => ⟨fun k => ⟨f.1 k, f.2.2 k⟩, fun {a b} hab =>
      f.2.1 (congrArg Subtype.val hab)⟩
    invFun := fun f => ⟨fun k => (f k).1,
      ⟨fun {a b} hab => f.injective (Subtype.ext hab), fun k => (f k).2⟩⟩
    left_inv := by intro f; apply Subtype.ext; funext k; rfl
    right_inv := by intro f; apply DFunLike.ext; intro k; rfl }
  calc
    _ = Fintype.card (Fin m ↪ A) := Fintype.card_congr eAvoid
    _ = (Fintype.card A).descFactorial (Fintype.card (Fin m)) := Fintype.card_embedding_eq
    _ = m.factorial := by simp [hA, m, Nat.descFactorial_self]

private theorem cons_cons_injective_iff {n k : ℕ} (i j : Fin n) (f : Fin k → Fin n) :
    Function.Injective (Fin.cons i (Fin.cons j f)) ↔
      i ≠ j ∧ Function.Injective f ∧ ∀ k, f k ≠ i ∧ f k ≠ j := by
  rw [cons_injective_iff, cons_injective_iff]
  constructor
  · rintro ⟨⟨hf, hj⟩, hi⟩
    exact ⟨Ne.symm (by simpa using hi 0), hf, fun k => ⟨by simpa using hi k.succ, hj k⟩⟩
  · rintro ⟨hij, hf, h⟩
    refine ⟨⟨hf, fun k => (h k).2⟩, ?_⟩
    intro k
    induction k using Fin.cases with
    | zero => simpa using Ne.symm hij
    | succ k => simpa using (h k).1

private theorem fixed_two_sum {n : ℕ} (hn : 2 ≤ n) (η : Fin n → Form n 2)
    (hsq : ∀ i, (η i ∧[ℝ] η i) = 0)
    (hcomm : ∀ i j, (η i ∧[ℝ] η j) = (η j ∧[ℝ] η i)) (i j : Fin n) :
    (∑ f : Fin (n - 2) → Fin n,
      fullTuple η (by omega : (n - 2) + 1 + 1 = n) (Fin.cons i (Fin.cons j f))) =
      if i = j then 0 else ((n - 2).factorial : ℝ) • diagonalWedgeTuple η n id := by
  classical
  simp_rw [fullTuple_classification η hsq hcomm, cons_cons_injective_iff]
  by_cases hij : i = j
  · simp [hij]
  · simp only [Ne, hij, not_false_eq_true, ↓reduceIte, true_and]
    have hc : ((Finset.univ : Finset (Fin (n - 2) → Fin n)).filter
        (fun f => Function.Injective f ∧ ∀ k, f k ≠ i ∧ f k ≠ j)).card = (n - 2).factorial := by
      rw [← Fintype.card_subtype]
      exact count_fixed_two_tail i j hij
    rw [← Finset.sum_filter, Finset.sum_const, hc]
    simp only [Nat.cast_smul_eq_nsmul]

private theorem cast_trans {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) :
    (Fin.castOrderIso h₁ : Fin a ≃ Fin b).trans (Fin.castOrderIso h₂) =
      (Fin.castOrderIso (h₁.trans h₂) : Fin a ≃ Fin c) := by
  subst b c
  rfl

private theorem pair_step_cast {n k l : ℕ} (a b : Form n 2) (θ : Form n (2 * k))
    (h : k + 1 + 1 = l) :
    (diagonalLeftStep a (diagonalLeftStep b θ)).domDomCongr (Fin.castOrderIso (congrArg (2 * ·) h)) =
      ((a ∧[ℝ] b) ∧[ℝ] θ).domDomCongr
        (Fin.castOrderIso (by omega : 2 + 2 + 2 * k = 2 * l) : Fin (2 + 2 + 2 * k) ≃ Fin (2 * l)) := by
  rw [cast_step _ _ h, diagonalLeftStep_reduce, wedge_cast_right a (b ∧[ℝ] θ)
    (by omega : 2 + 2 * k = 2 * (k + 1)), domDomCongr_trans]
  have hassoc := wedge_mul_assoc a b θ
  have hc : Fin.finAssoc.symm.trans
      (Fin.castOrderIso (by omega : (2 + 2) + 2 * k = 2 * l) : Fin ((2 + 2) + 2 * k) ≃ Fin (2 * l)) =
      (Fin.castOrderIso (by omega : 2 + (2 + 2 * k) = 2 * l) : Fin (2 + (2 + 2 * k)) ≃ Fin (2 * l)) := by
    ext i
    rfl
  have hh := congrArg (fun F : Form n ((2 + 2) + 2 * k) => F.domDomCongr
      (Fin.castOrderIso (by omega : (2 + 2) + 2 * k = 2 * l) : Fin ((2 + 2) + 2 * k) ≃ Fin (2 * l))) hassoc
  rw [domDomCongr_trans, hc] at hh
  rw [cast_trans]
  exact hh

private theorem diagonalLeftStep_smul_right {n k : ℕ} (c : ℝ) (a : Form n 2) (θ : Form n (2 * k)) :
    diagonalLeftStep a (c • θ) = c • diagonalLeftStep a θ := by
  simp only [diagonalLeftStep_reduce, wedge_smul, domDomCongr_smul]

private theorem weighted_two_tuple_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (η : ι → Form n 2) (d : ι → ℝ) (k : ℕ) :
    diagonalLeftStep (∑ i, d i • η i) (diagonalLeftStep (∑ i, d i • η i) (wedgePow (∑ i, η i) k)) =
      ∑ i, ∑ j, ∑ f : Fin k → ι,
        (d i * d j) • diagonalWedgeTuple η (k + 1 + 1) (Fin.cons i (Fin.cons j f)) := by
  classical
  rw [weighted_diagonalWedgeTuple_sum, diagonalLeftStep_sum]
  simp only [diagonalLeftStep_sum_right, diagonalLeftStep_smul, diagonalLeftStep_smul_right, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro f _
  rw [mul_comm (d j) (d i)]
  rfl

private theorem square_sum {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℝ) :
    (((diagonalForm d ∧[ℝ] diagonalForm d) ∧[ℝ] wedgePow omegaFlat (n - 2)).domDomCongr
      (Fin.castOrderIso (by omega : 2 + 2 + 2 * (n - 2) = 2 * n))) =
      ∑ i, ∑ j, ∑ f : Fin (n - 2) → Fin n,
        (d i * d j) • fullTuple eta (by omega : (n - 2) + 1 + 1 = n)
          (Fin.cons i (Fin.cons j f)) := by
  classical
  rw [diagonalForm, omegaFlat, ← pair_step_cast _ _ _ (by omega : (n - 2) + 1 + 1 = n),
    weighted_two_tuple_sum]
  simp only [cast_sum, domDomCongr_smul, fullTuple_reduce]

private theorem ordered_quadratic {n : ℕ} (d : Fin n → ℝ) :
    (∑ i, ∑ j : Fin n, if i = j then 0 else d i * d j) =
      (∑ i, d i) ^ 2 - ∑ i, d i ^ 2 := by
  classical
  have hinner (i : Fin n) :
      (∑ j : Fin n, if i = j then 0 else d i * d j) =
        d i * (∑ j, d j) - d i ^ 2 := by
    have he (j : Fin n) :
        (if i = j then 0 else d i * d j) = d i * d j - if i = j then d i ^ 2 else 0 := by
      by_cases hij : i = j
      · subst j; simp; ring
      · simp [hij]
    simp_rw [he]
    simp [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp_rw [hinner]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

private theorem quadratic_consumer {n : ℕ} (hn : 2 ≤ n)
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) = (0 : Form n 4))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (d : Fin n → ℝ) :
    (((diagonalForm d ∧[ℝ] diagonalForm d) ∧[ℝ] wedgePow omegaFlat (n - 2)).domDomCongr
      (Fin.castOrderIso (by omega : 2 + 2 + 2 * (n - 2) = 2 * n))) =
      (((∑ i, d i) ^ 2 - ∑ i, d i ^ 2) / ((n : ℝ) * (n - 1))) • wedgePow omegaFlat n := by
  classical
  rw [square_sum hn, omegaFlat, wedgePow_eq_diagonalWedgeTuple_sum, top_sum eta hsq hcomm]
  simp_rw [← diagonal_smul_fintype_sum, fixed_two_sum hn eta hsq hcomm]
  have hs : (∑ i, ∑ j : Fin n,
      (d i * d j) • (if i = j then 0 else ((n - 2).factorial : ℝ) • diagonalWedgeTuple eta n id)) =
      ((∑ i, ∑ j : Fin n, if i = j then 0 else d i * d j) * ((n - 2).factorial : ℝ)) •
        diagonalWedgeTuple eta n id := by
    simp only [Finset.sum_mul, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [hij, smul_smul]
  rw [hs, ordered_quadratic, smul_smul]
  have hc : (n.factorial : ℝ) = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * ((n - 2).factorial : ℝ) := by
    have h₁ := Nat.factorial_succ (n - 1)
    have h₂ := Nat.factorial_succ (n - 2)
    rw [show n - 1 + 1 = n by omega] at h₁
    rw [show n - 2 + 1 = n - 1 by omega] at h₂
    rw [h₂, ← Nat.mul_assoc] at h₁
    exact_mod_cast h₁
  rw [hc, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hnm : (n : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    linarith
  congr 1
  field_simp

end ContinuousAlternatingMap

@[expose] section

namespace ContinuousAlternatingMap

/-- The diagonal trace–wedge quadratic identity in a unitary frame. -/
public theorem hodgeWedgeQuadraticNormalized {n : ℕ} (hn : 2 ≤ n)
    (ω γ : Form n 2) (hω : ω.IsOneOne) (hγ : γ.IsOneOne)
    (lam : Fin n → ℝ) (hωDiag : ω.coeffMatrix = 1)
    (hγDiag : γ.coeffMatrix = Matrix.diagonal (fun i => (lam i : ℂ))) :
    hodgeWedgeSquare hn ω γ =
      (((∑ i, lam i) ^ 2 - ∑ i, lam i ^ 2) / ((n : ℝ) * (n - 1))) •
        wedgePow ω n := by
  have hωflat := omegaFlat_eq_of_coeffMatrix_one ω hω hωDiag
  have hγflat := diagonalForm_eq_of_coeffMatrix_diagonal γ hγ lam hγDiag
  rw [hωflat, hγflat]
  exact quadratic_consumer hn eta_wedge_self_zero eta_wedge_comm lam

end ContinuousAlternatingMap

end
