module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.Basic
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.FlatCoordinateExtension

/-!
# Absolute coefficient of the final flat coordinate pair

This is the last-pair evaluation in the elementary fixed-family flat volume
computation of Wells, *Differential Analysis on Complex Manifolds* (1980),
V §1, pp. 157–159. It leaves the lower-dimensional wedge power unevaluated.
Thus it supplies the absolute factor two, rather than a relative trace
identity or a determinant formula assumed as a premise.

`topFormCoeff` uses the interleaved positive frame `(e₀,Ie₀,…,eₖ,Ieₖ)`.
The last area block evaluates to `+2`, including for `k = 0`. Its position
on the left contributes no sign, since it passes an even number of entries.
For `k = 1` the resulting coefficient is `+4`; the flat square then has
coefficient `8`, before division by `2!`.
-/

public section

namespace ContinuousAlternatingMap

/-- The last flat area pair contributes exactly a positive factor two.
No formula, nonvanishing assumption, or factorial normalization is imposed
on the coefficient of the lower flat power. -/

private def interleavedIndex (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  (finProdFinEquiv (m := n) (n := 2)).trans
    (Equiv.cast (congrArg Fin (by omega : n * 2 = 2 * n)))

private theorem castFinVal {n m : ℕ} (h : n = m) (i : Fin n) :
    (Equiv.cast (congrArg Fin h) i).val = i.val := by
  cases h
  rfl

private theorem interleavedIndex_val (n : ℕ) (p : Fin n × Fin 2) :
    (interleavedIndex n p).val = 2 * p.1.val + p.2.val := by
  unfold interleavedIndex
  rw [Equiv.trans_apply, castFinVal (by omega : n * 2 = 2 * n)]
  simp [finProdFinEquiv]
  omega

private theorem interleavedBasis_apply (n : ℕ) (j : Fin n) (a : Fin 2) :
    complexInterleavedBasis n (interleavedIndex n (j, a)) =
      if a = 0 then EuclideanSpace.single j (1 : ℂ)
      else Complex.I • EuclideanSpace.single j (1 : ℂ) := by
  unfold complexInterleavedBasis interleavedIndex
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  fin_cases a <;> simp [Module.Basis.smulTower'_apply, EuclideanSpace.basisFun_toBasis,
    PiLp.basisFun_apply]

private def pairEvaluationIndex (k : ℕ) :
    Fin (2 * k) ⊕ Fin 2 ≃ Fin (2 * (k + 1)) :=
  finSumFinEquiv.trans
    ((Fin.finAddCongr : Fin (2 * k + 2) ≃ Fin (2 + 2 * k)).trans
      (Fin.castOrderIso (by omega : 2 + 2 * k = 2 * (k + 1))).toEquiv)

private theorem pairEvaluationIndex_left_val (k : ℕ) (i : Fin (2 * k)) :
    (pairEvaluationIndex k (Sum.inl i)).val = i.val := by
  simp [pairEvaluationIndex, finSumFinEquiv, Fin.finAddCongr, finCongr]

private theorem pairEvaluationIndex_right_val (k : ℕ) (a : Fin 2) :
    (pairEvaluationIndex k (Sum.inr a)).val = 2 * k + a.val := by
  simp [pairEvaluationIndex, finSumFinEquiv, Fin.finAddCongr, finCongr]

private theorem pairEvaluationIndex_interleaved_right (k : ℕ) (a : Fin 2) :
    pairEvaluationIndex k (Sum.inr a) =
      interleavedIndex (k + 1) (Fin.last k, a) := by
  apply Fin.ext
  rw [pairEvaluationIndex_right_val, interleavedIndex_val]
  simp [Fin.val_last]

private theorem pairEvaluationIndex_interleaved_left_coord_lt (k : ℕ) (i : Fin (2 * k)) :
    ((interleavedIndex (k + 1)).symm (pairEvaluationIndex k (Sum.inl i))).1.val < k := by
  let p := (interleavedIndex (k + 1)).symm (pairEvaluationIndex k (Sum.inl i))
  have hidx : interleavedIndex (k + 1) p = pairEvaluationIndex k (Sum.inl i) := by
    exact Equiv.apply_symm_apply _ _
  have hv := congrArg Fin.val hidx
  rw [interleavedIndex_val, pairEvaluationIndex_left_val] at hv
  change p.1.val < k
  by_contra h
  have hk : k ≤ p.1.val := by omega
  have ha := p.2.isLt
  omega

private theorem eta_basis_zero_of_first_coord_ne (n : ℕ) (j : Fin n)
    (p q : Fin n × Fin 2) (hp : p.1 ≠ j) :
    eta j ![complexInterleavedBasis n (interleavedIndex n p),
      complexInterleavedBasis n (interleavedIndex n q)] = 0 := by
  rw [eta_apply, interleavedBasis_apply, interleavedBasis_apply]
  rcases p with ⟨p, a⟩
  rcases q with ⟨q, b⟩
  fin_cases a <;> fin_cases b <;> simp [hp]

private theorem flatFirstCoordinates_single (k : ℕ) (j : Fin (k + 1))
    (hj : j.val < k) (z : ℂ) :
    flatFirstCoordinates k (EuclideanSpace.single j z) =
      EuclideanSpace.single (j.castLT hj) z := by
  ext i
  simp [flatFirstCoordinates, EuclideanSpace.proj, EuclideanSpace.single]
  have hidx : i.castSucc = j ↔ i = j.castLT hj := by
    simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_castLT]
  simp only [hidx]

private theorem flatFirstCoordinates_interleaved_left (k : ℕ) (i : Fin (2 * k)) :
    flatFirstCoordinates k
      (complexInterleavedBasis (k + 1) (pairEvaluationIndex k (Sum.inl i))) =
    complexInterleavedBasis k i := by
  let p := (interleavedIndex (k + 1)).symm (pairEvaluationIndex k (Sum.inl i))
  have hp : p.1.val < k := pairEvaluationIndex_interleaved_left_coord_lt k i
  have hidx : pairEvaluationIndex k (Sum.inl i) = interleavedIndex (k + 1) p :=
    (Equiv.apply_symm_apply _ _).symm
  have hval : i.val = 2 * p.1.val + p.2.val := by
    have hv := congrArg Fin.val hidx
    rw [interleavedIndex_val, pairEvaluationIndex_left_val] at hv
    exact hv
  have hlow : i = interleavedIndex k (p.1.castLT hp, p.2) := by
    apply Fin.ext
    rw [interleavedIndex_val]
    simpa [Fin.val_castLT] using hval
  by_cases ha : p.2 = 0
  · calc
      flatFirstCoordinates k
          (complexInterleavedBasis (k + 1) (pairEvaluationIndex k (Sum.inl i))) =
          flatFirstCoordinates k (EuclideanSpace.single p.1 (1 : ℂ)) := by
            rw [hidx, interleavedBasis_apply, if_pos ha]
      _ = EuclideanSpace.single (p.1.castLT hp) (1 : ℂ) :=
        flatFirstCoordinates_single k p.1 hp 1
      _ = complexInterleavedBasis k i := by
        rw [hlow, interleavedBasis_apply, if_pos ha]
  · have ha1 : p.2 = 1 := by
      apply Fin.ext
      have hne : p.2.val ≠ 0 := by
        intro hz
        apply ha
        exact Fin.ext hz
      omega
    calc
      flatFirstCoordinates k
          (complexInterleavedBasis (k + 1) (pairEvaluationIndex k (Sum.inl i))) =
          flatFirstCoordinates k (Complex.I • EuclideanSpace.single p.1 (1 : ℂ)) := by
            rw [hidx, interleavedBasis_apply, if_neg ha]
      _ = Complex.I • flatFirstCoordinates k (EuclideanSpace.single p.1 (1 : ℂ)) := by
        rw [map_smul]
      _ = Complex.I • EuclideanSpace.single (p.1.castLT hp) (1 : ℂ) := by
        rw [flatFirstCoordinates_single]
      _ = complexInterleavedBasis k i := by
        rw [hlow, interleavedBasis_apply, ha1]
        simp

private theorem eta_basis_zero_of_second_coord_ne (n : ℕ) (j : Fin n)
    (p q : Fin n × Fin 2) (hq : q.1 ≠ j) :
    eta j ![complexInterleavedBasis n (interleavedIndex n p),
      complexInterleavedBasis n (interleavedIndex n q)] = 0 := by
  rw [eta_apply, interleavedBasis_apply, interleavedBasis_apply]
  rcases p with ⟨p, a⟩
  rcases q with ⟨q, b⟩
  fin_cases a <;> fin_cases b <;> simp [hq]

private def pairSlot (k : ℕ) (s : Fin (2 * k) ⊕ Fin 2) : Fin (k + 1) × Fin 2 :=
  (interleavedIndex (k + 1)).symm (pairEvaluationIndex k s)

private theorem pairEvaluationBasis_repr (k : ℕ) (s : Fin (2 * k) ⊕ Fin 2) :
    complexInterleavedBasis (k + 1) (pairEvaluationIndex k s) =
      complexInterleavedBasis (k + 1)
        (interleavedIndex (k + 1) (pairSlot k s)) := by
  simp [pairSlot]

private theorem eta_last_pair_eval (k : ℕ) :
    eta (Fin.last k) ![
      complexInterleavedBasis (k + 1)
        (pairEvaluationIndex k (Sum.inr (0 : Fin 2))),
      complexInterleavedBasis (k + 1)
        (pairEvaluationIndex k (Sum.inr (1 : Fin 2)))] = 2 := by
  rw [pairEvaluationIndex_interleaved_right, pairEvaluationIndex_interleaved_right,
    interleavedBasis_apply, interleavedBasis_apply]
  simp [eta_apply]

private theorem quotient_eq_one_of_right_invariant {m n : ℕ}
    (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (hR : ∀ i, ∃ j, σ (Sum.inr i) = Sum.inr j) :
    (Quotient.mk'' σ : Equiv.Perm.ModSumCongr (Fin m) (Fin n)) = Quotient.mk'' 1 := by
  classical
  have hRfun : ∀ i, σ (Sum.inr i) = Sum.inr (Classical.choose (hR i)) :=
    fun i => Classical.choose_spec (hR i)
  let g : Fin n → Fin n := fun i => Classical.choose (hR i)
  have hginj : Function.Injective g := by
    intro i j hij
    have hEq : σ (Sum.inr i) = σ (Sum.inr j) := by
      rw [hRfun i, hRfun j]
      exact congrArg Sum.inr (by simpa [g] using hij)
    exact Sum.inr.inj (σ.injective hEq)
  have hgsurj : Function.Surjective g :=
    (Finite.injective_iff_surjective).mp hginj
  have hL : ∀ i, ∃ j, σ (Sum.inl i) = Sum.inl j := by
    intro i
    cases hσ : σ (Sum.inl i) with
    | inl j => exact ⟨j, rfl⟩
    | inr j =>
      obtain ⟨j', hj'⟩ := hgsurj j
      have hEq : σ (Sum.inl i) = σ (Sum.inr j') := by
        rw [hσ, hRfun]
        exact congrArg Sum.inr hj'.symm
      exact False.elim (Sum.inl_ne_inr (σ.injective hEq))
  have hmaps : Set.MapsTo σ (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro x ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hL i
    exact ⟨j, hj.symm⟩
  have hmem : σ ∈ (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range :=
    Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
  apply Quotient.sound
  change QuotientGroup.leftRel (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range σ 1
  rw [QuotientGroup.leftRel_apply]
  simpa using (Equiv.Perm.sumCongrHom (Fin m) (Fin n)).range.inv_mem hmem

theorem topFormCoeff_flatLastPairTop (k : ℕ) :
    topFormCoeff (flatLastPairTop k) =
      2 * topFormCoeff (wedgePow (omegaFlat (n := k)) k) := by
  classical
  rw [topFormCoeff, flatLastPairTop, ContinuousAlternatingMap.domDomCongr_apply]
  have hcomm := ContinuousAlternatingMap.wedge_antisymm
    (eta (Fin.last k))
    ((wedgePow (omegaFlat (n := k)) k).compContinuousLinearMap
      ((flatFirstCoordinates k).restrictScalars ℝ))
  have hsign : (-1 : ℝ) ^ (2 * (2 * k)) = 1 := by
    rw [pow_mul]
    norm_num
  have hswap :
      (eta (Fin.last k) ∧[ℝ]
        ((wedgePow (omegaFlat (n := k)) k).compContinuousLinearMap
          ((flatFirstCoordinates k).restrictScalars ℝ))) =
      ContinuousAlternatingMap.domDomCongr Fin.finAddCongr
        (((wedgePow (omegaFlat (n := k)) k).compContinuousLinearMap
          ((flatFirstCoordinates k).restrictScalars ℝ)) ∧[ℝ] eta (Fin.last k)) := by
    simpa [hsign] using hcomm
  rw [hswap, ContinuousAlternatingMap.domDomCongr_apply,
    ContinuousAlternatingMap.wedge_product_mul, ContinuousAlternatingMap.uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.uncurrySum_apply]
  let w : Fin (2 * k) ⊕ Fin 2 → V (k + 1) :=
    complexInterleavedBasis (k + 1) ∘ pairEvaluationIndex k
  let f : V (k + 1) [⋀^Fin (2 * k)]→L[ℝ]
      V (k + 1) [⋀^Fin 2]→L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).compContinuousAlternatingMap₂
      ((wedgePow (omegaFlat (n := k)) k).compContinuousLinearMap
        ((flatFirstCoordinates k).restrictScalars ℝ)) (eta (Fin.last k))
  change ((∑ σ : Equiv.Perm.ModSumCongr (Fin (2 * k)) (Fin 2),
    uncurrySum.summand f σ) w) = _
  let q0 : Equiv.Perm.ModSumCongr (Fin (2 * k)) (Fin 2) :=
    Quotient.mk'' (1 : Equiv.Perm (Fin (2 * k) ⊕ Fin 2))
  have hleft : (fun i : Fin (2 * k) => flatFirstCoordinates k (w (Sum.inl i))) =
      complexInterleavedBasis k := by
    funext i
    exact flatFirstCoordinates_interleaved_left k i
  have hright : (fun a : Fin 2 => w (Sum.inr a)) =
      ![w (Sum.inr 0), w (Sum.inr 1)] := by
    funext a
    fin_cases a <;> rfl
  have hq0 : uncurrySum.summand f q0 w =
      2 * topFormCoeff (wedgePow (omegaFlat (n := k)) k) := by
    dsimp [q0]
    rw [uncurrySum_summand_eval]
    simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, id_eq]
    change (wedgePow (omegaFlat (n := k)) k)
        (fun i => flatFirstCoordinates k (w (Sum.inl i))) *
      eta (Fin.last k) (fun a => w (Sum.inr a)) = _
    rw [hleft, hright]
    simp only [w, Function.comp_apply]
    rw [eta_last_pair_eval]
    change topFormCoeff (wedgePow (omegaFlat (n := k)) k) * 2 =
      2 * topFormCoeff (wedgePow (omegaFlat (n := k)) k)
    exact mul_comm _ _
  rw [_root_.sum_apply]
  change (∑ σ : Equiv.Perm.ModSumCongr (Fin (2 * k)) (Fin 2),
    uncurrySum.summand f σ w) = _
  rw [Finset.sum_eq_single_of_mem q0 (Finset.mem_univ q0) (by
    intro q hq hneq
    obtain ⟨σ, rfl⟩ := Quotient.exists_rep q
    have hbad : ∃ a : Fin 2, ∃ i : Fin (2 * k), σ (Sum.inr a) = Sum.inl i := by
      by_contra h
      have hR : ∀ a : Fin 2, ∃ b : Fin 2, σ (Sum.inr a) = Sum.inr b := by
        intro a
        cases hs : σ (Sum.inr a) with
        | inl i => exact False.elim (h ⟨a, i, hs⟩)
        | inr b => exact ⟨b, rfl⟩
      exact hneq (by simpa [q0] using quotient_eq_one_of_right_invariant σ hR)
    obtain ⟨a, i, hai⟩ := hbad
    have heta : eta (Fin.last k) (fun b => w (σ (Sum.inr b))) = 0 := by
      have htuple : (fun b : Fin 2 => w (σ (Sum.inr b))) =
          ![w (σ (Sum.inr 0)), w (σ (Sum.inr 1))] := by
        funext b
        fin_cases b <;> rfl
      rw [htuple]
      have hcase : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      rcases hcase with ha | ha
      · subst a
        let p := pairSlot k (Sum.inl i)
        let q := pairSlot k (σ (Sum.inr 1))
        have hp : p.1.val < k := by
          simpa [p, pairSlot] using pairEvaluationIndex_interleaved_left_coord_lt k i
        have hpne : p.1 ≠ Fin.last k := by
          intro heq
          have hval := congrArg Fin.val heq
          rw [Fin.val_last] at hval
          have hlt := hp
          rw [hval] at hlt
          exact Nat.lt_irrefl k hlt
        have hv0 : w (σ (Sum.inr 0)) =
            complexInterleavedBasis (k + 1) (interleavedIndex (k + 1) p) := by
          change complexInterleavedBasis (k + 1) (pairEvaluationIndex k (σ (Sum.inr 0))) = _
          rw [hai]
          exact pairEvaluationBasis_repr k (Sum.inl i)
        have hv1 : w (σ (Sum.inr 1)) =
            complexInterleavedBasis (k + 1) (interleavedIndex (k + 1) q) := by
          change complexInterleavedBasis (k + 1) (pairEvaluationIndex k (σ (Sum.inr 1))) = _
          exact pairEvaluationBasis_repr k (σ (Sum.inr 1))
        rw [hv0, hv1]
        exact eta_basis_zero_of_first_coord_ne (k + 1) (Fin.last k) p q hpne
      · subst a
        let p := pairSlot k (Sum.inl i)
        let q := pairSlot k (σ (Sum.inr 0))
        have hp : p.1.val < k := by
          simpa [p, pairSlot] using pairEvaluationIndex_interleaved_left_coord_lt k i
        have hpne : p.1 ≠ Fin.last k := by
          intro heq
          have hval := congrArg Fin.val heq
          rw [Fin.val_last] at hval
          have hlt := hp
          rw [hval] at hlt
          exact Nat.lt_irrefl k hlt
        have hv0 : w (σ (Sum.inr 0)) =
            complexInterleavedBasis (k + 1) (interleavedIndex (k + 1) q) := by
          change complexInterleavedBasis (k + 1) (pairEvaluationIndex k (σ (Sum.inr 0))) = _
          exact pairEvaluationBasis_repr k (σ (Sum.inr 0))
        have hv1 : w (σ (Sum.inr 1)) =
            complexInterleavedBasis (k + 1) (interleavedIndex (k + 1) p) := by
          change complexInterleavedBasis (k + 1) (pairEvaluationIndex k (σ (Sum.inr 1))) = _
          rw [hai]
          exact pairEvaluationBasis_repr k (Sum.inl i)
        rw [hv0, hv1]
        exact eta_basis_zero_of_second_coord_ne (k + 1) (Fin.last k) q p hpne
    rw [uncurrySum_summand_eval,
      ContinuousLinearMap.compContinuousAlternatingMap₂_mul_apply]
    rw [heta]
    simp) ]
  exact hq0

end ContinuousAlternatingMap
