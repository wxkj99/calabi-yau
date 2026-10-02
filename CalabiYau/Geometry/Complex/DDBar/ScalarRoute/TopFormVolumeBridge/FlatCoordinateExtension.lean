module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.CoordinateBasis
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.WedgePowers

/-!
# The last coordinate pair in a flat Kähler wedge

Wells, *Differential Analysis on Complex Manifolds* (1980), V §1,
pp. 157–159, computes the flat volume in positive complex orientation.
Here `omegaFlat = 2 ∑ dxⱼ ∧ dyⱼ`, powers are unnormalized, and the final
coordinate pair stays on the left. The equality is the elementary
square-zero reduction in that fixed-family computation, not a general
alternating-form determinant theorem.

The projection preserves the order of the first `k` complex coordinates.
Moving the two final real coordinates past the first `2*k` has positive
sign. These definitions also apply for `k = 0`, with the degree-zero unit.
-/

@[expose] public section

namespace ContinuousAlternatingMap

/-- Ordered projection onto the first `k` complex coordinates. -/
noncomputable def flatFirstCoordinates (k : ℕ) : V (k + 1) →L[ℂ] V k :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin k => EuclideanSpace.proj i.castSucc))

/-- The last coordinate pair, followed by the pulled-back lower flat power.
The pair is on the left, just as in `mixedWedgeOfPos`. -/
noncomputable def flatLastPairTop (k : ℕ) : Form (k + 1) (2 * (k + 1)) :=
  (eta (Fin.last k) ∧[ℝ]
    (wedgePow (omegaFlat (n := k)) k).compContinuousLinearMap
      ((flatFirstCoordinates k).restrictScalars ℝ)).domDomCongr
    (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1)))

private theorem flatWedgeAssocCast {n r q : ℕ}
    (a b : Form n 2) (θ : Form n (2 * r))
    (e : Fin ((2 + 2) + 2 * r) ≃ Fin q) :
    (a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr (Fin.finAssoc.symm.trans e) =
      ((a ∧[ℝ] b) ∧[ℝ] θ).domDomCongr e := by
  simpa only [← ContinuousAlternatingMap.domDomCongr_trans] using
    congrArg (fun f => f.domDomCongr e)
      (ContinuousAlternatingMap.wedge_mul_assoc a b θ)

private theorem flatLastPairFirstCastAssoc (r : ℕ) :
    let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
      ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
        ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
          (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
    let e₁ : Fin (2 + 2 * r) ≃ Fin (2 * (r + 1)) :=
      Fin.castOrderIso (by omega : 2 + 2 * r = 2 * (r + 1))
    let e₂ : Fin (2 + 2 * (r + 1)) ≃ Fin (2 * (r + 2)) :=
      Fin.castOrderIso (by omega : 2 + 2 * (r + 1) = 2 * (r + 2))
    let eTot := (blockCast e₁).trans e₂
    let ePair := Fin.finAssoc.trans eTot
    Fin.finAssoc.symm.trans ePair = eTot := by
  dsimp
  let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
    ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
      ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
        (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
  let e₁ : Fin (2 + 2 * r) ≃ Fin (2 * (r + 1)) :=
    Fin.castOrderIso (by omega : 2 + 2 * r = 2 * (r + 1))
  let e₂ : Fin (2 + 2 * (r + 1)) ≃ Fin (2 * (r + 2)) :=
    Fin.castOrderIso (by omega : 2 + 2 * (r + 1) = 2 * (r + 2))
  let eTot := (blockCast e₁).trans e₂
  let ePair := Fin.finAssoc.trans eTot
  calc
    _ = (Fin.finAssoc.symm.trans Fin.finAssoc).trans eTot := by
      rw [← Equiv.trans_assoc]
    _ = eTot := by simp

set_option maxHeartbeats 1000000 in
/-- Terms using the final area piece again vanish in the mixed flat power.
Only the fixed coordinate family is involved; the lower power is not evaluated. -/
theorem omegaFlat_mixedWedge_lastPair (k : ℕ) :
    mixedWedgeOfPos (Nat.succ_pos k) (eta (Fin.last k))
      (omegaFlat (n := k + 1)) = flatLastPairTop k := by
  have omegaFlat_split (k : ℕ) :
      omegaFlat (n := k + 1) =
        (∑ i : Fin k, eta i.castSucc) + eta (Fin.last k) := by
    classical
    rw [omegaFlat, Fin.sum_univ_castSucc]

  have eta_castSucc_comp (k : ℕ) (i : Fin k) :
      (eta i).compContinuousLinearMap
        ((flatFirstCoordinates k).restrictScalars ℝ) = eta i.castSucc := by
    ext v
    have hv : v = ![v 0, v 1] := by
      funext j
      fin_cases j <;> simp
    rw [hv]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hvec : (↑((flatFirstCoordinates k).restrictScalars ℝ)) ∘ ![v 0, v 1] =
        ![flatFirstCoordinates k (v 0), flatFirstCoordinates k (v 1)] := by
      funext j
      fin_cases j <;> rfl
    rw [hvec, eta_apply, eta_apply]
    dsimp [flatFirstCoordinates]
    rw [PiLp.coe_symm_continuousLinearEquiv]

  have omegaFlat_comp_first (k : ℕ) :
      (omegaFlat (n := k)).compContinuousLinearMap
        ((flatFirstCoordinates k).restrictScalars ℝ) =
        ∑ i : Fin k, eta i.castSucc := by
    classical
    ext v
    simp only [omegaFlat, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun f => f v) (eta_castSucc_comp k i)

  have omegaFlat_decompose (k : ℕ) :
      omegaFlat (n := k + 1) = eta (Fin.last k) +
        (omegaFlat (n := k)).compContinuousLinearMap
          ((flatFirstCoordinates k).restrictScalars ℝ) := by
    rw [omegaFlat_split, omegaFlat_comp_first]
    exact (add_comm _ _)

  have wedge_product_compLocal {n m k l : ℕ}
      (g : Form n k) (h : Form n l) (A : V m →L[ℝ] V n) :
      (g ∧[ℝ] h).compContinuousLinearMap A =
        (g.compContinuousLinearMap A) ∧[ℝ] (h.compContinuousLinearMap A) := by
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.wedge_product_def]
    change ContinuousAlternatingMap.uncurryFinAdd
        (ContinuousLinearMap.compContinuousAlternatingMap₂
          (ContinuousLinearMap.mul ℝ ℝ) g h) (A ∘ v) =
      ContinuousAlternatingMap.uncurryFinAdd
        (ContinuousLinearMap.compContinuousAlternatingMap₂
          (ContinuousLinearMap.mul ℝ ℝ) (g.compContinuousLinearMap A)
          (h.compContinuousLinearMap A)) v
    rw [ContinuousAlternatingMap.uncurryFinAdd, ContinuousAlternatingMap.uncurryFinAdd,
      ContinuousAlternatingMap.domDomCongr_apply,
      ContinuousAlternatingMap.domDomCongr_apply,
      ContinuousAlternatingMap.uncurrySum_apply, ContinuousAlternatingMap.uncurrySum_apply,
      _root_.sum_apply, _root_.sum_apply]
    apply Finset.sum_congr rfl
    intro σ hσ
    refine Quotient.inductionOn' σ ?_
    intro σ'
    rw [ContinuousAlternatingMap.uncurrySum_summand_eval,
      ContinuousAlternatingMap.uncurrySum_summand_eval]
    simp only [ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
      ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_apply]
    rfl

  have domDomCongr_compLocal {d p m n : ℕ}
      (σ : Fin m ≃ Fin n) (L : Form d m) (A : V p →L[ℝ] V d) :
      (ContinuousAlternatingMap.domDomCongr σ L).compContinuousLinearMap A =
        ContinuousAlternatingMap.domDomCongr σ (L.compContinuousLinearMap A) := by
    ext v
    rfl

  have constOfIsEmpty_compLocal {n m : ℕ} (y : ℝ)
      (A : V m →L[ℝ] V n) :
      (ContinuousAlternatingMap.constOfIsEmpty ℝ (V n) (Fin 0) y).compContinuousLinearMap A =
        ContinuousAlternatingMap.constOfIsEmpty ℝ (V m) (Fin 0) y := by
    ext v
    rfl

  have wedgePow_comp {n m : ℕ}
      (ω : Form n 2) (A : V m →L[ℝ] V n) (q : ℕ) :
      (wedgePow ω q).compContinuousLinearMap A =
        wedgePow (ω.compContinuousLinearMap A) q := by
    induction q with
    | zero => exact constOfIsEmpty_compLocal (n := n) (m := m) 1 A
    | succ q ih =>
        change (ContinuousAlternatingMap.domDomCongr
            (Fin.castOrderIso (by omega : 2 + 2 * q = 2 * (q + 1))).toEquiv
            ((ω ∧[ℝ] wedgePow ω q) : Form n (2 + 2 * q))).compContinuousLinearMap A =
          ContinuousAlternatingMap.domDomCongr
            (Fin.castOrderIso (by omega : 2 + 2 * q = 2 * (q + 1))).toEquiv
            (((ω.compContinuousLinearMap A) ∧[ℝ]
              wedgePow (ω.compContinuousLinearMap A) q) : Form m (2 + 2 * q))
        rw [domDomCongr_compLocal, wedge_product_compLocal, ih]

  have flatLowerWedgePow_comp (k : ℕ) :
      (wedgePow (omegaFlat (n := k)) k).compContinuousLinearMap
          ((flatFirstCoordinates k).restrictScalars ℝ) =
        wedgePow (∑ i : Fin k, eta i.castSucc) k := by
    rw [wedgePow_comp, omegaFlat_comp_first]

  have flatLastPairTop_asFlatSum (k : ℕ) :
      flatLastPairTop k =
        (eta (Fin.last k) ∧[ℝ]
          wedgePow (∑ i : Fin k, eta i.castSucc) k).domDomCongr
          (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1))) := by
    change (eta (Fin.last k) ∧[ℝ]
        (wedgePow (omegaFlat (n := k)) k).compContinuousLinearMap
          ((flatFirstCoordinates k).restrictScalars ℝ)).domDomCongr
        (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1))).toEquiv = _
    rw [← flatLowerWedgePow_comp]
    rfl

  let flatLeftStep {n : ℕ}
      (a : Form n 2) {r : ℕ} (θ : Form n (2 * r)) : Form n (2 * (r + 1)) :=
    (a ∧[ℝ] θ).domDomCongr (Fin.castOrderIso (by omega : 2 + 2 * r = 2 * (r + 1)))

  have flatStepRightArithmeticCast {n m m' : ℕ}
      (a : Form n 2) (θ : Form n m) (hm : m = m') :
      (a ∧[ℝ] θ.domDomCongr (Fin.castOrderIso hm).toEquiv) =
        (a ∧[ℝ] θ).domDomCongr
          (((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
            ((Equiv.sumCongr (Equiv.refl (Fin 2))
              (Fin.castOrderIso hm).toEquiv).trans
              (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))) := by
    cases hm
    simp

  have flatStepAssocCast {n r q : ℕ}
      (a b : Form n 2) (θ : Form n (2 * r))
      (e : Fin ((2 + 2) + 2 * r) ≃ Fin q) :
      (a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr (Fin.finAssoc.symm.trans e) =
        ((a ∧[ℝ] b) ∧[ℝ] θ).domDomCongr e := by
    simpa only [← ContinuousAlternatingMap.domDomCongr_trans] using
      congrArg (fun f => f.domDomCongr e)
        (ContinuousAlternatingMap.wedge_mul_assoc a b θ)

  have flatStepStepAssocCast {n r : ℕ}
      (a b : Form n 2) (θ : Form n (2 * r)) :
      let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
        ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
          ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
            (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
      let e₁ := (Fin.castOrderIso (by omega : 2 + 2 * r = 2 * (r + 1))).toEquiv
      let e₂ := (Fin.castOrderIso
        (by omega : 2 + 2 * (r + 1) = 2 * (r + 2))).toEquiv
      flatLeftStep a (flatLeftStep b θ) =
        (a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr ((blockCast e₁).trans e₂) := by
    unfold flatLeftStep
    let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
      ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
        ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
          (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
    let e₁ : Fin (2 + 2 * r) ≃ Fin (2 * (r + 1)) :=
      (Fin.castOrderIso (by omega : 2 + 2 * r = 2 * (r + 1))).toEquiv
    let e₂ : Fin (2 + 2 * (r + 1)) ≃ Fin (2 * (r + 2)) :=
      (Fin.castOrderIso (by omega : 2 + 2 * (r + 1) = 2 * (r + 2))).toEquiv
    calc
      _ = ((a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr (blockCast e₁)).domDomCongr e₂ := by
        exact congrArg (fun f => f.domDomCongr e₂)
          (flatStepRightArithmeticCast a (b ∧[ℝ] θ) (by omega))
      _ = _ := by rw [ContinuousAlternatingMap.domDomCongr_trans]

  have flatLeftStep_commute {n r : ℕ} (a b : Form n 2)
      (θ : Form n (2 * r)) (hab : (a ∧[ℝ] b) = (b ∧[ℝ] a)) :
      flatLeftStep a (flatLeftStep b θ) = flatLeftStep b (flatLeftStep a θ) := by
    let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
      ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
        ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
          (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
    let e₁ : Fin (2 + 2 * r) ≃ Fin (2 * (r + 1)) :=
      (Fin.castOrderIso (by omega : 2 + 2 * r = 2 * (r + 1))).toEquiv
    let e₂ : Fin (2 + 2 * (r + 1)) ≃ Fin (2 * (r + 2)) :=
      (Fin.castOrderIso (by omega : 2 + 2 * (r + 1) = 2 * (r + 2))).toEquiv
    let eTot := (blockCast e₁).trans e₂
    let ePair := Fin.finAssoc.trans eTot
    have he : Fin.finAssoc.symm.trans ePair = eTot := by
      calc
        _ = (Fin.finAssoc.symm.trans Fin.finAssoc).trans eTot := by rw [← Equiv.trans_assoc]
        _ = eTot := by simp
    have hleft : flatLeftStep a (flatLeftStep b θ) =
        ((a ∧[ℝ] b) ∧[ℝ] θ).domDomCongr ePair := by
      calc
        _ = (a ∧[ℝ] (b ∧[ℝ] θ)).domDomCongr eTot := by
          simpa [flatLeftStep, eTot, blockCast] using flatStepStepAssocCast a b θ
        _ = _ := by rw [← he]; exact flatStepAssocCast a b θ ePair
    have hright : flatLeftStep b (flatLeftStep a θ) =
        ((b ∧[ℝ] a) ∧[ℝ] θ).domDomCongr ePair := by
      calc
        _ = (b ∧[ℝ] (a ∧[ℝ] θ)).domDomCongr eTot := by
          simpa [flatLeftStep, eTot, blockCast] using flatStepStepAssocCast b a θ
        _ = _ := by rw [← he]; exact flatStepAssocCast b a θ ePair
    calc
      _ = ((a ∧[ℝ] b) ∧[ℝ] θ).domDomCongr ePair := hleft
      _ = ((b ∧[ℝ] a) ∧[ℝ] θ).domDomCongr ePair := by rw [hab]
      _ = _ := hright.symm

  have flatLeftStep_repeatZero {n r : ℕ} (a : Form n 2)
      (θ : Form n (2 * r)) (haa : (a ∧[ℝ] a) = 0) :
      flatLeftStep a (flatLeftStep a θ) = 0 := by
    let blockCast {m m' : ℕ} (e : Fin m ≃ Fin m') : Fin (2 + m) ≃ Fin (2 + m') :=
      ((finSumFinEquiv : Fin 2 ⊕ Fin m ≃ Fin (2 + m)).symm).trans
        ((Equiv.sumCongr (Equiv.refl (Fin 2)) e).trans
          (finSumFinEquiv : Fin 2 ⊕ Fin m' ≃ Fin (2 + m')))
    let e₁ : Fin (2 + 2 * r) ≃ Fin (2 * (r + 1)) :=
      (Fin.castOrderIso (by omega : 2 + 2 * r = 2 * (r + 1))).toEquiv
    let e₂ : Fin (2 + 2 * (r + 1)) ≃ Fin (2 * (r + 2)) :=
      (Fin.castOrderIso (by omega : 2 + 2 * (r + 1) = 2 * (r + 2))).toEquiv
    let eTot := (blockCast e₁).trans e₂
    let ePair := Fin.finAssoc.trans eTot
    have he : Fin.finAssoc.symm.trans ePair = eTot := by
      calc
        _ = (Fin.finAssoc.symm.trans Fin.finAssoc).trans eTot := by rw [← Equiv.trans_assoc]
        _ = eTot := by simp
    have hzero : ((0 : Form n 4) ∧[ℝ] θ) = 0 := by
      rw [← zero_smul ℝ (0 : Form n 4), ContinuousAlternatingMap.smul_wedge]
      simp
    calc
      _ = (a ∧[ℝ] (a ∧[ℝ] θ)).domDomCongr eTot := by
        simpa [flatLeftStep, eTot, blockCast] using flatStepStepAssocCast a a θ
      _ = ((a ∧[ℝ] a) ∧[ℝ] θ).domDomCongr ePair := by
        rw [← he]; exact flatStepAssocCast a a θ ePair
      _ = 0 := by rw [haa, hzero]; ext v; rfl

  have flatLeftStep_add_left {n r : ℕ} (a b : Form n 2)
      (θ : Form n (2 * r)) :
      flatLeftStep (a + b) θ = flatLeftStep a θ + flatLeftStep b θ := by
    simp [flatLeftStep, ContinuousAlternatingMap.add_wedge,
      ContinuousAlternatingMap.domDomCongr_add]

  have flatLeftStep_add_right {n r : ℕ} (a : Form n 2)
      (θ ψ : Form n (2 * r)) :
      flatLeftStep a (θ + ψ) = flatLeftStep a θ + flatLeftStep a ψ := by
    simp [flatLeftStep, ContinuousAlternatingMap.wedge_add,
      ContinuousAlternatingMap.domDomCongr_add]

  have eta_castSucc_wedge_commute (k : ℕ) :
      (eta (Fin.last k) ∧[ℝ] (∑ i : Fin k, eta i.castSucc)) =
        ((∑ i : Fin k, eta i.castSucc) ∧[ℝ] eta (Fin.last k)) := by
    simpa [Fin.finAddCongr, show (-1 : ℝ) ^ (2 * 2) = 1 by norm_num] using
      (ContinuousAlternatingMap.wedge_antisymm
        (eta (Fin.last k)) (∑ i : Fin k, eta i.castSucc))

  have flatReindexZero {n m l : ℕ} (e : Fin m ≃ Fin l) :
      ContinuousAlternatingMap.domDomCongr e
        (0 : Form (n := n) m) = 0 := by
    ext x
    rfl

  have flatDecomposable_wedge_square_zero {n : ℕ}
      (u v : Form n 1) :
      ((u ∧[ℝ] v) ∧[ℝ] (u ∧[ℝ] v)) = 0 := by
    have hvv : (v ∧[ℝ] v) = 0 := by
      exact ContinuousAlternatingMap.wedge_self_odd_zero v (by decide) (by norm_num)
    have hright : ((u ∧[ℝ] v) ∧[ℝ] v) = 0 := by
      have hh := ContinuousAlternatingMap.wedge_mul_assoc u v v
      rw [hvv] at hh
      have hz : (u ∧[ℝ] (0 : Form n 2)) = 0 := by
        simpa using (ContinuousAlternatingMap.wedge_smul (0 : ℝ) u (v ∧[ℝ] v)
          (ContinuousLinearMap.mul ℝ ℝ))
      rw [hz] at hh
      simpa only [flatReindexZero] using hh.symm
    have hmiddle : (v ∧[ℝ] (u ∧[ℝ] v)) = 0 := by
      have hh := ContinuousAlternatingMap.wedge_antisymm v (u ∧[ℝ] v)
      rw [hright] at hh
      simpa only [ContinuousAlternatingMap.domDomCongr_smul, flatReindexZero,
        smul_zero] using hh
    have hh := ContinuousAlternatingMap.wedge_mul_assoc u v (u ∧[ℝ] v)
    rw [hmiddle] at hh
    have hz : (u ∧[ℝ] (0 : Form n 3)) = 0 := by
      simpa using (ContinuousAlternatingMap.wedge_smul (0 : ℝ) u
        (v ∧[ℝ] (u ∧[ℝ] v)) (ContinuousLinearMap.mul ℝ ℝ))
    rw [hz] at hh
    simpa only [flatReindexZero] using hh.symm

  have flatTwiceDecomposable_wedge_square_zero {n : ℕ}
      (u v : Form n 1) :
      (((2 : ℝ) • (u ∧[ℝ] v)) ∧[ℝ] ((2 : ℝ) • (u ∧[ℝ] v))) = 0 := by
    rw [ContinuousAlternatingMap.smul_wedge,
      ContinuousAlternatingMap.wedge_smul, flatDecomposable_wedge_square_zero]
    simp

  have eta_castSucc_wedge_square_zero (k : ℕ) :
      (eta (Fin.last k) ∧[ℝ] eta (Fin.last k)) = 0 := by
    let u : V (k + 1) [⋀^Fin 1]→L[ℝ] ℝ :=
      ContinuousAlternatingMap.ofSubsingleton ℝ (V (k + 1)) ℝ (0 : Fin 1) (dx (Fin.last k))
    let v : V (k + 1) [⋀^Fin 1]→L[ℝ] ℝ :=
      ContinuousAlternatingMap.ofSubsingleton ℝ (V (k + 1)) ℝ (0 : Fin 1) (dy (Fin.last k))
    change (((2 : ℝ) • (u ∧[ℝ] v)) ∧[ℝ] ((2 : ℝ) • (u ∧[ℝ] v))) = 0
    exact flatTwiceDecomposable_wedge_square_zero u v

  have flatLeftStep_absorb {n r : ℕ} (a b : Form n 2)
      (haa : (a ∧[ℝ] a) = 0) (hab : (a ∧[ℝ] b) = (b ∧[ℝ] a)) :
      flatLeftStep a (wedgePow (a + b) r) = flatLeftStep a (wedgePow b r) := by
    induction r with
    | zero => rfl
    | succ r ih =>
        change flatLeftStep a (flatLeftStep (a + b) (wedgePow (a + b) r)) =
          flatLeftStep a (flatLeftStep b (wedgePow b r))
        rw [flatLeftStep_add_left, flatLeftStep_add_right]
        rw [flatLeftStep_repeatZero a _ haa, zero_add]
        rw [flatLeftStep_commute a b _ hab, ih]
        exact (flatLeftStep_commute b a _ hab.symm)

  change flatLeftStep (eta (Fin.last k))
    (wedgePow (omegaFlat (n := k + 1)) k) = flatLastPairTop k
  have hcommute :
      (eta (Fin.last k) ∧[ℝ]
        (omegaFlat (n := k)).compContinuousLinearMap
          ((flatFirstCoordinates k).restrictScalars ℝ)) =
      ((omegaFlat (n := k)).compContinuousLinearMap
          ((flatFirstCoordinates k).restrictScalars ℝ) ∧[ℝ]
        eta (Fin.last k)) := by
    rw [omegaFlat_comp_first]
    exact eta_castSucc_wedge_commute k
  calc
    _ = flatLeftStep (eta (Fin.last k))
        (wedgePow (eta (Fin.last k) +
          (omegaFlat (n := k)).compContinuousLinearMap
            ((flatFirstCoordinates k).restrictScalars ℝ)) k) := by
      rw [omegaFlat_decompose]
    _ = flatLeftStep (eta (Fin.last k))
        (wedgePow ((omegaFlat (n := k)).compContinuousLinearMap
          ((flatFirstCoordinates k).restrictScalars ℝ)) k) :=
      flatLeftStep_absorb (eta (Fin.last k)) _
        (eta_castSucc_wedge_square_zero k) hcommute
    _ = flatLastPairTop k := by
      rw [flatLastPairTop_asFlatSum, ← omegaFlat_comp_first]
end ContinuousAlternatingMap
