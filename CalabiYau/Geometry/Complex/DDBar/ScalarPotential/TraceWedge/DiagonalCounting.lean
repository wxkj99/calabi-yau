module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.CoordinateBasis
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.WedgePowers

/-!
# Diagonal trace–wedge counting

In a unitary frame, the trace–wedge identity counts the surviving diagonal
coordinate blocks. The coordinate basis forms square to zero and commute, and
the unnormalized exterior powers contribute `n!` and `(n - 1)!` orderings.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics* (GSM 152),
Lemma 4.7, p. 60.
-/

@[expose] public section

open Matrix
open scoped BigOperators

namespace ContinuousAlternatingMap

private theorem relTrace_diagonalForm {n : ℕ} (d : Fin n → ℝ) :
    (omegaFlat (n := n)).relTrace (diagonalForm d) = ∑ j, d j := by
  rw [relTrace, omegaFlat_coeffMatrix, diagonalForm_coeffMatrix]
  simp [Matrix.trace_diagonal]

private noncomputable def diagonalLeftStep {n : ℕ}
    (η : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) {k : ℕ}
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ) :
    EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * (k + 1))]→L[ℝ] ℝ :=
  (η ∧[ℝ] θ).domDomCongr (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1)))

private noncomputable def diagonalWedgeTuple {n : ℕ} {ι : Type*}
    (η : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (k : ℕ) → (Fin k → ι) →
      EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ
  | 0, _ => constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n)) (Fin 0) 1
  | k + 1, f => diagonalLeftStep (η (f 0))
      (diagonalWedgeTuple η k (f ∘ Fin.succ))

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
  | zero => simp [wedgePow, diagonalWedgeTuple]
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
  simp only [diagonalLeftStep, ContinuousAlternatingMap.smul_wedge,
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

private theorem diagonalWedgeRightArithmeticCast {n m m' : ℕ}
    (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin m]→L[ℝ] ℝ) (hm : m = m') :
    (a ∧[ℝ] θ.domDomCongr (Fin.castOrderIso hm).toEquiv) =
      (a ∧[ℝ] θ).domDomCongr
        (((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
          ((Equiv.sumCongr (Equiv.refl (Fin 2)) (Fin.castOrderIso hm).toEquiv).trans
            (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))) := by
  cases hm
  simp

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
    let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
      ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
        ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
          (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
    let e₁ := (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1))).toEquiv
    let e₂ := (Fin.castOrderIso
      (by omega : 2 + 2 * (k + 1) = 2 * (k + 2))).toEquiv
    diagonalLeftStep a (diagonalLeftStep b θ) =
      (a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr ((blockCast e₁).trans e₂) := by
  unfold diagonalLeftStep
  let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
    ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
      ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
        (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
  let e₁ : Fin (2 + 2 * k) ≃ Fin (2 * (k + 1)) :=
    (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1))).toEquiv
  let e₂ : Fin (2 + 2 * (k + 1)) ≃ Fin (2 * (k + 2)) :=
    (Fin.castOrderIso (by omega : 2 + 2 * (k + 1) = 2 * (k + 2))).toEquiv
  calc
    _ = ((a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr (blockCast e₁)).domDomCongr e₂ := by
      exact congrArg (fun f => f.domDomCongr e₂)
        (diagonalWedgeRightArithmeticCast a (b ∧[ℝ] θ) (by omega))
    _ = _ := by rw [ContinuousAlternatingMap.domDomCongr_trans]

private theorem diagonalWedgePowStepFrontSwap {n k : ℕ}
    (a b : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ)
    (h : (a ∧[ℝ] b) = (b ∧[ℝ] a)) :
    diagonalLeftStep a (diagonalLeftStep b θ) = diagonalLeftStep b (diagonalLeftStep a θ) := by
  let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
    ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
      ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
        (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
  let eTot :=
    (blockCast (Fin.castOrderIso
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
  let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
    ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
      ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
        (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
  let eTot :=
    (blockCast (Fin.castOrderIso
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

set_option maxHeartbeats 10000 in
private theorem diagonalWedgeTuple_noninjective_zero {n k : ℕ}
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (f : Fin k → Fin n) (hnot : ¬ Function.Injective f) :
    diagonalWedgeTuple eta k f = 0 := by
  let Graded := (q : ℕ) →
    EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ
  let shift (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
      (F : Graded) : Graded := fun q =>
        Nat.casesOn q (motive := fun q => EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ)
          0 (fun k => diagonalLeftStep a (F k))
  let unitFamily : Graded := fun q =>
    if h : q = 0 then
      (constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n)) (Fin 0) (1 : ℝ)).domDomCongr
        (Fin.castOrderIso (by omega : 0 = 2 * q))
    else 0
  let listFold (l : List (Fin n)) : Graded :=
    l.foldr (fun a F => shift (eta a) F) unitFamily
  have hshiftzero (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (F : Graded) :
      shift a F 0 = 0 := by rfl
  have hshiftsucc (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (F : Graded)
      (q : ℕ) : shift a F (Nat.succ q) = diagonalLeftStep a (F q) := by rfl
  have hstepzero {q : ℕ} (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
      diagonalLeftStep a (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ) = 0 := by
    unfold diagonalLeftStep
    rw [← zero_smul ℝ (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ),
      ContinuousAlternatingMap.wedge_smul,
      ContinuousAlternatingMap.domDomCongr_smul, zero_smul]
  have shift_comm (a b : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
      (hswap : ∀ q, ∀ θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ,
        diagonalLeftStep a (diagonalLeftStep b θ) = diagonalLeftStep b (diagonalLeftStep a θ))
      (F : Graded) : shift a (shift b F) = shift b (shift a F) := by
    funext q
    cases q with
    | zero => rw [hshiftzero, hshiftzero]
    | succ q =>
        cases q with
        | zero => rw [hshiftsucc, hshiftzero, hstepzero, hshiftsucc, hshiftzero, hstepzero]
        | succ q =>
            rw [hshiftsucc, hshiftsucc, hshiftsucc, hshiftsucc]
            exact hswap q (F q)
  have shift_repeat_zero (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
      (hrepeat : ∀ q, ∀ θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ,
        diagonalLeftStep a (diagonalLeftStep a θ) = 0)
      (F : Graded) : shift a (shift a F) = 0 := by
    funext q
    cases q with
    | zero => rfl
    | succ q =>
        cases q with
        | zero => rw [hshiftsucc, hshiftzero, hstepzero]; rfl
        | succ q =>
            rw [hshiftsucc, hshiftsucc]
            exact hrepeat q (F q)
  have listFold_perm {l₁ l₂ : List (Fin n)} (hp : l₁.Perm l₂) :
      listFold l₁ = listFold l₂ := by
    induction hp with
    | nil => rfl
    | @cons a l₁ l₂ hp ih =>
        simpa [listFold] using congrArg (shift (eta a)) ih
    | @swap a b l =>
        simp only [listFold, List.foldr_cons]
        exact (shift_comm (eta a) (eta b)
          (fun q θ => diagonalWedgePowStepFrontSwap (eta a) (eta b) θ (hcomm a b))
          (listFold l)).symm
    | @trans l₁ l₂ l₃ hp₁ hp₂ ih₁ ih₂ => exact ih₁.trans ih₂
  have tuple_eq_listFold : ∀ (q : ℕ) (g : Fin q → Fin n),
      diagonalWedgeTuple eta q g = listFold (List.ofFn g) q := by
    intro q
    induction q with
    | zero =>
        intro g
        simp only [diagonalWedgeTuple, List.ofFn_zero, listFold, List.foldr_nil, unitFamily]
        ext v
        simp [ContinuousAlternatingMap.domDomCongr_apply]
    | succ q ih =>
        intro g
        simp only [List.ofFn_succ, diagonalWedgeTuple, listFold, List.foldr_cons, shift]
        exact congrArg (diagonalLeftStep (eta (g 0))) (ih (g ∘ Fin.succ))
  let l := List.ofFn f
  have hn : ¬ l.Nodup := by
    intro hn
    exact hnot (List.nodup_ofFn.mp (by simpa [l] using hn))
  obtain ⟨a, ha⟩ := List.exists_duplicate_iff_not_nodup.mpr hn
  rw [List.duplicate_iff_sublist] at ha
  obtain ⟨r, hp⟩ := List.Sublist.exists_perm_append ha
  have hfoldzero : listFold (a :: a :: r) = 0 := by
    simp only [listFold, List.foldr_cons]
    exact shift_repeat_zero (eta a)
      (fun q θ => diagonalWedgePowStepRepeatZero (eta a) θ (hsq a)) (listFold r)
  calc
    diagonalWedgeTuple eta k f = listFold l k := tuple_eq_listFold k f
    _ = listFold (a :: a :: r) k := by
      simpa only [List.cons_append, List.nil_append] using
        congrArg (fun F : Graded => F k) (listFold_perm hp)
    _ = 0 := by rw [hfoldzero]; rfl

set_option maxHeartbeats 10000 in
private theorem diagonalWedgeTuple_injective_eq {n : ℕ}
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (f : Fin n → Fin n) (hf : Function.Injective f) :
    diagonalWedgeTuple eta n f = diagonalWedgeTuple eta n id := by
  let Graded := (q : ℕ) →
    EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ
  let shift (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
      (F : Graded) : Graded := fun q =>
        Nat.casesOn q (motive := fun q => EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ)
          0 (fun k => diagonalLeftStep a (F k))
  let unitFamily : Graded := fun q =>
    if h : q = 0 then
      (constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin n)) (Fin 0) (1 : ℝ)).domDomCongr
        (Fin.castOrderIso (by omega : 0 = 2 * q))
    else 0
  let listFold (l : List (Fin n)) : Graded :=
    l.foldr (fun a F => shift (eta a) F) unitFamily
  have hshiftzero (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (F : Graded) :
      shift a F 0 = 0 := by rfl
  have hshiftsucc (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (F : Graded)
      (q : ℕ) : shift a F (Nat.succ q) = diagonalLeftStep a (F q) := by rfl
  have hstepzero {q : ℕ} (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
      diagonalLeftStep a (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ) = 0 := by
    unfold diagonalLeftStep
    rw [← zero_smul ℝ (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ),
      ContinuousAlternatingMap.wedge_smul,
      ContinuousAlternatingMap.domDomCongr_smul, zero_smul]
  have shift_comm (a b : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
      (hswap : ∀ q, ∀ θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * q)]→L[ℝ] ℝ,
        diagonalLeftStep a (diagonalLeftStep b θ) = diagonalLeftStep b (diagonalLeftStep a θ))
      (F : Graded) : shift a (shift b F) = shift b (shift a F) := by
    funext q
    cases q with
    | zero => rw [hshiftzero, hshiftzero]
    | succ q =>
        cases q with
        | zero => rw [hshiftsucc, hshiftzero, hstepzero, hshiftsucc, hshiftzero, hstepzero]
        | succ q =>
            rw [hshiftsucc, hshiftsucc, hshiftsucc, hshiftsucc]
            exact hswap q (F q)
  have listFold_perm {l₁ l₂ : List (Fin n)} (hp : l₁.Perm l₂) :
      listFold l₁ = listFold l₂ := by
    induction hp with
    | nil => rfl
    | @cons a l₁ l₂ hp ih =>
        simpa [listFold] using congrArg (shift (eta a)) ih
    | @swap a b l =>
        simp only [listFold, List.foldr_cons]
        exact (shift_comm (eta a) (eta b)
          (fun q θ => diagonalWedgePowStepFrontSwap (eta a) (eta b) θ (hcomm a b))
          (listFold l)).symm
    | @trans l₁ l₂ l₃ hp₁ hp₂ ih₁ ih₂ => exact ih₁.trans ih₂
  have tuple_eq_listFold : ∀ (q : ℕ) (g : Fin q → Fin n),
      diagonalWedgeTuple eta q g = listFold (List.ofFn g) q := by
    intro q
    induction q with
    | zero =>
        intro g
        simp only [diagonalWedgeTuple, List.ofFn_zero, listFold, List.foldr_nil, unitFamily]
        ext v
        simp [ContinuousAlternatingMap.domDomCongr_apply]
    | succ q ih =>
        intro g
        simp only [List.ofFn_succ, diagonalWedgeTuple, listFold, List.foldr_cons, shift]
        exact congrArg (diagonalLeftStep (eta (g 0))) (ih (g ∘ Fin.succ))
  let p : Equiv.Perm (Fin n) :=
    Equiv.ofBijective f ⟨hf, (Finite.injective_iff_surjective).mp hf⟩
  have hpFun : (fun x : Fin n => p x) = f := by
    funext x
    rfl
  have hperm : (List.ofFn f).Perm (List.ofFn id) := by
    have hp0 := Equiv.Perm.ofFn_comp_perm p (fun x : Fin n => x)
    have hp : List.Perm (List.ofFn (fun x : Fin n => p x))
        (List.ofFn (fun x : Fin n => x)) := by
      simpa [Function.comp_def] using hp0
    have hlist : List.ofFn (fun x : Fin n => p x) = List.ofFn f :=
      congrArg List.ofFn hpFun
    rw [← hlist]
    change List.Perm (List.ofFn (fun x : Fin n => p x))
      (List.ofFn (fun x : Fin n => x))
    exact hp
  calc
    diagonalWedgeTuple eta n f = listFold (List.ofFn f) n := tuple_eq_listFold n f
    _ = listFold (List.ofFn id) n := by
      exact congrArg (fun F : Graded => F n) (listFold_perm hperm)
    _ = diagonalWedgeTuple eta n id := (tuple_eq_listFold n id).symm

private theorem diagonalWedgeTuple_classification {n : ℕ}
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (f : Fin n → Fin n) :
    diagonalWedgeTuple eta n f =
      if Function.Injective f then diagonalWedgeTuple eta n id else 0 := by
  by_cases hf : Function.Injective f
  · rw [ite_eq_left hf]
    exact diagonalWedgeTuple_injective_eq hcomm f hf
  · rw [ite_eq_right hf]
    exact diagonalWedgeTuple_noninjective_zero hsq hcomm f hf

private theorem diagonalWedgeTuple_full_classification {n k : ℕ}
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (hk : k = n) (f : Fin k → Fin n) :
    (diagonalWedgeTuple eta k f).domDomCongr
        (Fin.castOrderIso (congrArg (fun q : ℕ => 2 * q) hk)) =
      if Function.Injective f then diagonalWedgeTuple eta n id else 0 := by
  subst k
  change diagonalWedgeTuple eta n f = _
  exact diagonalWedgeTuple_classification hsq hcomm f

private theorem diagonal_cons_injective_iff {n k : ℕ} (i : Fin n) (f : Fin k → Fin n) :
    Function.Injective (Fin.cons i f) ↔ Function.Injective f ∧ ∀ j, f j ≠ i := by
  simpa [Set.mem_range, and_comm] using (Fin.cons_injective_iff (x₀ := i) (x := f))

private theorem diagonalWedgeTuple_fixed_head_sum {n : ℕ} (hn : 0 < n)
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (i : Fin n) :
    (∑ f : Fin (n - 1) → Fin n,
      (diagonalWedgeTuple eta ((n - 1) + 1) (Fin.cons i f)).domDomCongr
        (Fin.castOrderIso (congrArg (fun q : ℕ => 2 * q)
          (Nat.sub_add_cancel hn)))) =
      ((n - 1).factorial : ℝ) • diagonalWedgeTuple eta n id := by
  classical
  simp_rw [diagonalWedgeTuple_full_classification hsq hcomm (Nat.sub_add_cancel hn),
    diagonal_cons_injective_iff]
  have hc : ((Finset.univ : Finset (Fin (n - 1) → Fin n)).filter
      (fun f => Function.Injective f ∧ ∀ j, f j ≠ i)).card = (n - 1).factorial := by
    rw [← Fintype.card_subtype]
    exact diagonal_count_fixed_fiber i
  rw [← Finset.sum_filter, Finset.sum_const, hc]
  simp only [Nat.cast_smul_eq_nsmul]

private theorem diagonalWedgeTuple_sum_top {n : ℕ}
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i)) :
    (∑ f : Fin n → Fin n, diagonalWedgeTuple eta n f) =
      (n.factorial : ℝ) • diagonalWedgeTuple eta n id := by
  classical
  have hclass : (∑ f : Fin n → Fin n, diagonalWedgeTuple eta n f) =
      ∑ f : Fin n → Fin n,
        if Function.Injective f then diagonalWedgeTuple eta n id else 0 := by
    apply Finset.sum_congr rfl
    intro f hf
    exact diagonalWedgeTuple_classification hsq hcomm f
  rw [hclass]
  have hc : ((Finset.univ : Finset (Fin n → Fin n)).filter
      Function.Injective).card = n.factorial := by
    rw [← Fintype.card_subtype]
    exact diagonal_count_injective_endomaps n
  rw [← Finset.sum_filter, Finset.sum_const, hc]
  simp only [Nat.cast_smul_eq_nsmul]

private theorem diagonalWedge_cast_step {n k l : ℕ}
    (a : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * k)]→L[ℝ] ℝ)
    (h : k + 1 = l) :
    (diagonalLeftStep a θ).domDomCongr
        (Fin.castOrderIso (congrArg (fun q : ℕ => 2 * q) h)).toEquiv =
      (a ∧[ℝ] θ).domDomCongr
        (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * l)).toEquiv := by
  rw [diagonalLeftStep, ContinuousAlternatingMap.domDomCongr_trans]
  congr 1

private theorem diagonalWedge_domDomCongr_sum {n k l : ℕ} {ι : Type*} [Fintype ι]
    (h : k = l) (F : ι → EuclideanSpace ℂ (Fin n) [⋀^Fin k]→L[ℝ] ℝ) :
    (∑ i, F i).domDomCongr (Fin.castOrderIso h).toEquiv =
      ∑ i, (F i).domDomCongr ((Fin.castOrderIso h).toEquiv : Fin k ≃ Fin l) := by
  classical
  simpa using ContinuousAlternatingMap.domDomCongr_sum
    ((Fin.castOrderIso h).toEquiv : Fin k ≃ Fin l) Finset.univ F

private theorem diagonal_mixedWedge_sum {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ) :
    mixedWedgeOfPos hn (diagonalForm d) omegaFlat =
      ∑ i, ∑ f : Fin (n - 1) → Fin n,
        d i • (diagonalWedgeTuple eta ((n - 1) + 1) (Fin.cons i f)).domDomCongr
          (Fin.castOrderIso (congrArg (fun q : ℕ => 2 * q)
            (Nat.sub_add_cancel hn))) := by
  classical
  change (diagonalForm d ∧[ℝ] wedgePow omegaFlat (n - 1)).domDomCongr
      (Fin.castOrderIso (by omega : 2 + 2 * (n - 1) = 2 * n)).toEquiv = _
  rw [diagonalForm, omegaFlat]
  change ((∑ i, d i • eta i) ∧[ℝ]
      wedgePow (∑ i, eta i) (n - 1)).domDomCongr
      (Fin.castOrderIso (by omega : 2 + 2 * (n - 1) = 2 * n)).toEquiv = _
  rw [← diagonalWedge_cast_step _ _ (Nat.sub_add_cancel hn)]
  rw [weighted_diagonalWedgeTuple_sum]
  simp only [diagonalWedge_domDomCongr_sum, ContinuousAlternatingMap.domDomCongr_smul]
  rfl

private theorem diagonal_tuple_count {n : ℕ} (hn : 1 < n)
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (d : Fin n → ℝ) :
    (∑ j, d j) • (∑ f : Fin n → Fin n, diagonalWedgeTuple eta n f) =
      (n : ℝ) • mixedWedgeOfPos (Nat.zero_lt_of_lt hn) (diagonalForm d) omegaFlat := by
  classical
  rw [diagonalWedgeTuple_sum_top hsq hcomm,
    diagonal_mixedWedge_sum (Nat.zero_lt_of_lt hn) d]
  simp_rw [← diagonal_smul_fintype_sum,
    diagonalWedgeTuple_fixed_head_sum (Nat.zero_lt_of_lt hn) hsq hcomm]
  simp only [smul_smul]
  rw [← Finset.sum_smul]
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hfac : (n.factorial : ℝ) = (n : ℝ) * ((n - 1).factorial : ℝ) := by
    have h := Nat.factorial_succ (n - 1)
    rw [Nat.sub_add_cancel hnpos] at h
    exact_mod_cast h
  rw [hfac, ← Finset.sum_mul]
  module

private theorem diagonal_trace_wedge_counting_flat {n : ℕ} (hn : 1 < n)
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (d : Fin n → ℝ) :
    ((omegaFlat (n := n)).relTrace (diagonalForm d)) • wedgePow (omegaFlat (n := n)) n =
      (n : ℝ) • mixedWedgeOfPos (Nat.zero_lt_of_lt hn) (diagonalForm d) omegaFlat := by
  rw [relTrace_diagonalForm]
  conv_lhs =>
    rw [omegaFlat, wedgePow_eq_diagonalWedgeTuple_sum]
  exact diagonal_tuple_count hn hsq hcomm d

/-- Diagonal trace–wedge counting in an identity unitary frame. -/
theorem diagonal_trace_wedge_counting {n : ℕ} (hn : 1 < n)
    (hsq : ∀ j : Fin n, (eta j ∧[ℝ] eta j) =
      (0 : EuclideanSpace ℂ (Fin n) [⋀^Fin 4]→L[ℝ] ℝ))
    (hcomm : ∀ i j : Fin n, (eta i ∧[ℝ] eta j) = (eta j ∧[ℝ] eta i))
    (ω α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hω : ω.IsOneOne) (hα : α.IsOneOne)
    (hωI : ω.coeffMatrix = 1) (d : Fin n → ℝ)
    (hαD : α.coeffMatrix = Matrix.diagonal (fun i => (d i : ℂ))) :
    (ω.relTrace α) • wedgePow ω n =
      (n : ℝ) • mixedWedgeOfPos (Nat.zero_lt_of_lt hn) α ω := by
  have hωeq : ω = omegaFlat := omegaFlat_eq_of_coeffMatrix_one ω hω hωI
  have hαeq : α = diagonalForm d := diagonalForm_eq_of_coeffMatrix_diagonal α hα d hαD
  subst ω
  subst α
  exact diagonal_trace_wedge_counting_flat hn hsq hcomm d

end ContinuousAlternatingMap
