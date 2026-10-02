module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.Stokes.Basic

/-!
# Exterior derivative of an even-degree wedge

For even `k`, moving the exterior differential past the `k` inputs of the
first factor introduces no sign. This statement concerns the actual normalized
shuffle `FormField.wedge`, with exterior differentiation computed in charts by
`FormField.extDeriv`. The chart-level missing ingredient is the corresponding
`extDeriv` rule for `ContinuousAlternatingMap.wedgeProduct`; no such rule is
currently supplied by Mathlib or the extracted differential-form modules.

Source: Bott–Tu, *Differential Forms in Algebraic Topology*, Chapter I, §1,
Proposition 1.3, even-degree case of the antiderivation formula.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace FormField

open ContinuousAlternatingMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {k l : ℕ}

private theorem wedge_fderiv {f : E → E [⋀^Fin k]→L[ℝ] ℝ}
    {g : E → E [⋀^Fin l]→L[ℝ] ℝ} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun z => ContinuousAlternatingMap.wedgeProduct (f z) (g z)
      (ContinuousLinearMap.mul ℝ ℝ)) x v =
      ContinuousAlternatingMap.wedgeProduct (fderiv ℝ f x v) (g x)
        (ContinuousLinearMap.mul ℝ ℝ) +
      ContinuousAlternatingMap.wedgeProduct (f x) (fderiv ℝ g x v)
        (ContinuousLinearMap.mul ℝ ℝ) := by
  let B := ContinuousAlternatingMap.wedgeProductL
      (m := k) (n := l) (M := E) (ContinuousLinearMap.mul ℝ ℝ)
  have h := B.fderiv_of_bilinear hf hg
  have h' := congrArg (fun L => L v) h
  have hfun : (fun z => ContinuousAlternatingMap.wedgeProduct (f z) (g z)
      (ContinuousLinearMap.mul ℝ ℝ)) = fun y => (B (f y)) (g y) := by
    funext z
    rfl
  rw [← hfun] at h'
  rw [h']
  change ContinuousAlternatingMap.wedgeProduct (f x) (fderiv ℝ g x v)
      (ContinuousLinearMap.mul ℝ ℝ) +
    ContinuousAlternatingMap.wedgeProduct (fderiv ℝ f x v) (g x)
      (ContinuousLinearMap.mul ℝ ℝ) = _
  exact add_comm _ _

private theorem alternatizeUncurryFin_eq_uncurryFin
    (da : E →L[ℝ] E [⋀^Fin k]→L[ℝ] ℝ) :
    ContinuousAlternatingMap.alternatizeUncurryFin da =
      ContinuousAlternatingMap.uncurryFin da := by
  ext v
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.uncurryFin_apply]

private theorem fderiv_wedgeProduct {a : E → E [⋀^Fin k]→L[ℝ] ℝ}
    {b : E → E [⋀^Fin l]→L[ℝ] ℝ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    fderiv ℝ (fun z => ContinuousAlternatingMap.wedgeProduct (a z) (b z)
      (ContinuousLinearMap.mul ℝ ℝ)) x =
      (ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompL E
        (fderiv ℝ a x) (b x) +
      (ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR E
        (a x) (fderiv ℝ b x) := by
  let B := ContinuousAlternatingMap.wedgeProductL
      (m := k) (n := l) (M := E) (ContinuousLinearMap.mul ℝ ℝ)
  have h := B.fderiv_of_bilinear ha hb
  have hfun : (fun z => ContinuousAlternatingMap.wedgeProduct (a z) (b z)
      (ContinuousLinearMap.mul ℝ ℝ)) = fun y => (B (a y)) (b y) := by
    funext z
    rfl
  rw [← hfun] at h
  simpa only [add_comm] using h

private def rightInsertion_finSwapLast (k l : ℕ) : Fin (l + k + 1) ≃ Fin (k + l + 1) :=
  (Fin.finAddFlipAssoc (m := l) (n := k) (p := 1)).symm.trans
    ((Fin.finAddCongr (m := l + 1) (n := k)).trans
      (Fin.finAssoc (m := k) (n := l) (p := 1)).symm)

private theorem rightInsertion_finSwapLast_eq_finCongr (k l : ℕ) :
    rightInsertion_finSwapLast k l = finCongr (show l + k + 1 = k + l + 1 by omega) := by
  ext q
  simp only [rightInsertion_finSwapLast, Fin.finAddFlipAssoc, Fin.finAddCongr,
    Fin.finAssoc]
  exact Fin.val_cast (show l + k + 1 = k + l + 1 by omega) q

private theorem rightInsertion_finSwapLast_val (q : Fin (l + k + 1)) :
    (rightInsertion_finSwapLast k l q).val = q.val := by
  rw [rightInsertion_finSwapLast_eq_finCongr]
  exact Fin.val_cast (show l + k + 1 = k + l + 1 by omega) q

private noncomputable def rightInsertion_complementEquiv {n : ℕ} (p : Fin (n + 1)) :
    Fin n ≃ {x : Fin (n + 1) // x ≠ p} :=
  Equiv.ofBijective (fun q => ⟨p.succAbove q, p.succAbove_ne q⟩) (by
    constructor
    · intro x y h
      have hv := congrArg Subtype.val h
      exact Fin.succAbove_right_injective hv
    · intro ⟨x, hx⟩
      obtain ⟨q, hq⟩ := Fin.exists_succAbove_eq hx
      exact ⟨q, Subtype.ext hq⟩)

private noncomputable def rightInsertion_complementMap (i : Fin (k + l + 1)) :
    Fin (l + k) ≃ Fin (l + k) := by
  let σ := rightInsertion_finSwapLast k l
  let j := σ.symm i
  let hc : ∀ x : Fin (l + k + 1), x ≠ j ↔ σ x ≠ i := by
    intro x
    constructor
    · intro hx hxi
      apply hx
      apply σ.injective
      simpa [j] using hxi
    · intro hx hxi
      apply hx
      rw [hxi]
      simp [j]
  exact (rightInsertion_complementEquiv j).trans
    ((σ.subtypeEquiv hc).trans
      ((rightInsertion_complementEquiv i).symm.trans
        (Fin.finAddCongr (m := l) (n := k)).symm))

private theorem rightInsertion_complementEquiv_symm_value {n : ℕ}
    (p : Fin (n + 1)) (y : Fin (n + 1)) (hy : y ≠ p) :
    p.succAbove ((rightInsertion_complementEquiv p).symm ⟨y, hy⟩) = y := by
  have h := (rightInsertion_complementEquiv p).apply_symm_apply ⟨y, hy⟩
  exact congrArg Subtype.val h

private theorem rightInsertion_finSwapLast_castSucc (q : Fin (l + k)) :
    rightInsertion_finSwapLast k l q.castSucc =
      (Fin.finAddCongr (m := l) (n := k) q).castSucc := by
  apply Fin.ext
  simp [rightInsertion_finSwapLast_val, Fin.val_castSucc,
    Fin.finAddCongr, Fin.val_cast]

private theorem rightInsertion_finSwapLast_succ (q : Fin (l + k)) :
    rightInsertion_finSwapLast k l q.succ =
      (Fin.finAddCongr (m := l) (n := k) q).succ := by
  apply Fin.ext
  simp [rightInsertion_finSwapLast_val, Fin.val_succ,
    Fin.finAddCongr, Fin.val_cast]

private theorem rightInsertion_complementMap_eq_refl (i : Fin (k + l + 1)) :
    rightInsertion_complementMap (k := k) (l := l) i = Equiv.refl (Fin (l + k)) := by
  ext q
  let σ := rightInsertion_finSwapLast k l
  let j := σ.symm i
  let e := Fin.finAddCongr (m := l) (n := k)
  let y := σ (j.succAbove q)
  have hj : j.val = i.val := by
    have h := rightInsertion_finSwapLast_val (k := k) (l := l) j
    simpa [j, σ] using h.symm
  have he : (e q).val = q.val := Fin.val_cast (Nat.add_comm l k) q
  have hcond : q.castSucc < j ↔ (e q).castSucc < i := by
    simp [Fin.lt_def, Fin.val_castSucc, hj, he]
  have hblock : y = i.succAbove (e q) := by
    dsimp [y]
    by_cases hq : q.castSucc < j
    · have hi := hcond.mp hq
      rw [Fin.succAbove_of_castSucc_lt j q hq,
        Fin.succAbove_of_castSucc_lt i (e q) hi]
      exact rightInsertion_finSwapLast_castSucc q
    · have hj' : j ≤ q.castSucc := le_of_not_gt hq
      have hi' : i ≤ (e q).castSucc := le_of_not_gt (fun hi => hq (hcond.mpr hi))
      rw [Fin.succAbove_of_le_castSucc j q hj',
        Fin.succAbove_of_le_castSucc i (e q) hi']
      exact rightInsertion_finSwapLast_succ q
  have hy : y ≠ i := by
    intro h
    have hs : σ (j.succAbove q) = σ j := by simpa [y, j] using h
    have hjq : j.succAbove q = j := σ.injective hs
    exact (Fin.succAbove_ne j q) hjq
  let r := (rightInsertion_complementEquiv i).symm ⟨y, hy⟩
  have hr := rightInsertion_complementEquiv_symm_value i y hy
  have hr' : i.succAbove r = i.succAbove (e q) := hr.trans hblock
  have hr'' : r = e q := Fin.succAbove_right_injective hr'
  have hcomp : rightInsertion_complementMap (k := k) (l := l) i q = e.symm r := by
    rfl
  rw [hcomp, hr'']
  exact congrArg Fin.val (e.symm_apply_apply q)

private theorem rightInsertion_removedSlots {F : Type*} (v : Fin (k + l + 1) → F)
    (i : Fin (k + l + 1)) :
    ((rightInsertion_finSwapLast k l).symm i).removeNth
      (v ∘ rightInsertion_finSwapLast k l) =
      (i.removeNth v) ∘ Fin.finAddCongr (m := l) (n := k) ∘
        rightInsertion_complementMap (k := k) (l := l) i := by
  funext q
  apply congrArg v
  simp [rightInsertion_complementMap, rightInsertion_finSwapLast,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [rightInsertion_complementEquiv_symm_value]
  rfl

private theorem rightInsertion_leftDerivative_reindex (a : E [⋀^Fin k]→L[ℝ] ℝ)
    (db : E →L[ℝ] E [⋀^Fin l]→L[ℝ] ℝ) :
    uncurryFin ((wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR E a db) =
      (-1 : ℝ) ^ (k * l) •
        domDomCongr (rightInsertion_finSwapLast k l)
          (uncurryFin ((wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompL E db a)) := by
  ext v
  simp only [uncurryFin_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.domDomCongr_apply]
  simp [ContinuousLinearMap.precompR, ContinuousLinearMap.compL_apply,
    ContinuousAlternatingMap.wedge_productL_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (rightInsertion_finSwapLast k l).symm ?_ ?_
  · intro i
    simp
  · intro i hi
    rw [ContinuousAlternatingMap.wedge_antisymm,
      ContinuousAlternatingMap.domDomCongr_smul,
      ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.domDomCongr_apply]
    have hrem := rightInsertion_removedSlots (v := v) i
    rw [rightInsertion_complementMap_eq_refl] at hrem
    rw [hrem]
    have hfun : (i.removeNth v) ∘ Fin.finAddCongr (m := l) (n := k) =
        (i.removeNth v) ∘ Fin.finAddCongr (m := l) (n := k) ∘
          ⇑(Equiv.refl (Fin (l + k))) := by
      funext q
      rfl
    rw [← hfun]
    simp only [Equiv.apply_symm_apply]
    have hj : ((rightInsertion_finSwapLast k l).symm i).val = i.val := by
      have h := rightInsertion_finSwapLast_val
        (k := k) (l := l) ((rightInsertion_finSwapLast k l).symm i)
      simpa using h.symm
    rw [hj]
    ring

private theorem rightInsertion_finSwapLast_assoc (k l : ℕ) :
    (Fin.finAddFlipAssoc (m := l) (n := k) (p := 1)).trans
        (rightInsertion_finSwapLast k l) =
      (Fin.finAddCongr (m := l + 1) (n := k)).trans
        (Fin.finAssoc (m := k) (n := l) (p := 1)).symm := by
  change (Fin.finAddFlipAssoc (m := l) (n := k) (p := 1)).trans
      ((Fin.finAddFlipAssoc (m := l) (n := k) (p := 1)).symm.trans
        ((Fin.finAddCongr (m := l + 1) (n := k)).trans
          (Fin.finAssoc (m := k) (n := l) (p := 1)).symm)) = _
  rw [← Equiv.trans_assoc]
  simp

private theorem rightInsertion_wedgeSymmetry (a : E [⋀^Fin k]→L[ℝ] ℝ)
    (db : E →L[ℝ] E [⋀^Fin l]→L[ℝ] ℝ) :
    (-1 : ℝ) ^ k • domDomCongr Fin.finAssoc.symm
        (wedgeProduct a (uncurryFin db) (ContinuousLinearMap.mul ℝ ℝ)) =
      (-1 : ℝ) ^ (k * l) •
        domDomCongr (Fin.finAddCongr.trans Fin.finAssoc.symm)
          (wedgeProduct (uncurryFin db) a (ContinuousLinearMap.mul ℝ ℝ)) := by
  have hswap := ContinuousAlternatingMap.wedge_antisymm a (uncurryFin db)
  rw [hswap, ContinuousAlternatingMap.domDomCongr_smul,
    ContinuousAlternatingMap.domDomCongr_smul,
    ContinuousAlternatingMap.domDomCongr_trans]
  have hpow : (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k * (l + 1)) = (-1 : ℝ) ^ (k * l) := by
    calc
      (-1 : ℝ) ^ k * (-1 : ℝ) ^ (k * (l + 1)) =
          (-1 : ℝ) ^ (k + k * (l + 1)) := by rw [← pow_add]
      _ = (-1 : ℝ) ^ (k * l + 2 * k) := by
        congr 1
        simp [Nat.mul_add]
        omega
      _ = (-1 : ℝ) ^ (k * l) := by
        rw [pow_add, pow_mul]
        simp
  rw [smul_smul, hpow]

private theorem rightInsertion (a : E [⋀^Fin k]→L[ℝ] ℝ)
    (db : E →L[ℝ] E [⋀^Fin l]→L[ℝ] ℝ) :
    ContinuousAlternatingMap.uncurryFin
        ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR E a db) =
      (-1 : ℝ) ^ k • ContinuousAlternatingMap.domDomCongr Fin.finAssoc.symm
        (ContinuousAlternatingMap.wedgeProduct a (ContinuousAlternatingMap.uncurryFin db)
          (ContinuousLinearMap.mul ℝ ℝ)) := by
  have hleft := ContinuousAlternatingMap.uncurryFin_wedge_productL_precompL_eq_domDomCongr
    (ContinuousLinearMap.mul ℝ ℝ) db a
  calc
    ContinuousAlternatingMap.uncurryFin
        ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR E a db) =
        (-1 : ℝ) ^ (k * l) •
          ContinuousAlternatingMap.domDomCongr (rightInsertion_finSwapLast k l)
            (ContinuousAlternatingMap.uncurryFin
              ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompL E db a)) :=
      rightInsertion_leftDerivative_reindex a db
    _ = (-1 : ℝ) ^ (k * l) •
          ContinuousAlternatingMap.domDomCongr (Fin.finAddCongr.trans Fin.finAssoc.symm)
            (ContinuousAlternatingMap.wedgeProduct (ContinuousAlternatingMap.uncurryFin db) a
              (ContinuousLinearMap.mul ℝ ℝ)) := by
      rw [hleft, ContinuousAlternatingMap.domDomCongr_trans,
        rightInsertion_finSwapLast_assoc]
    _ = (-1 : ℝ) ^ k • ContinuousAlternatingMap.domDomCongr Fin.finAssoc.symm
          (ContinuousAlternatingMap.wedgeProduct a (ContinuousAlternatingMap.uncurryFin db)
            (ContinuousLinearMap.mul ℝ ℝ)) :=
      (rightInsertion_wedgeSymmetry a db).symm

private theorem local_extDeriv_wedge_even {a : E → E [⋀^Fin k]→L[ℝ] ℝ}
    {b : E → E [⋀^Fin l]→L[ℝ] ℝ} {x : E}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) (hk : Even k) :
    _root_.extDeriv (fun z => ContinuousAlternatingMap.wedgeProduct (a z) (b z)
      (ContinuousLinearMap.mul ℝ ℝ)) x =
      ContinuousAlternatingMap.domDomCongr Fin.finAddFlipAssoc
        (ContinuousAlternatingMap.wedgeProduct (_root_.extDeriv a x) (b x)
          (ContinuousLinearMap.mul ℝ ℝ)) +
      ContinuousAlternatingMap.domDomCongr Fin.finAssoc.symm
        (ContinuousAlternatingMap.wedgeProduct (a x) (_root_.extDeriv b x)
          (ContinuousLinearMap.mul ℝ ℝ)) := by
  rw [_root_.extDeriv, fderiv_wedgeProduct ha hb,
    alternatizeUncurryFin_eq_uncurryFin,
    ContinuousAlternatingMap.uncurryFin_add,
    ContinuousAlternatingMap.uncurryFin_wedge_productL_precompL_eq_domDomCongr,
    rightInsertion]
  rw [← alternatizeUncurryFin_eq_uncurryFin (fderiv ℝ a x),
    ← alternatizeUncurryFin_eq_uncurryFin (fderiv ℝ b x)]
  simp only [hk.neg_one_pow, one_smul]
  rfl

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem cast_formField {a b : ℕ} (h : a = b) (γ : FormField E M a)
    (x : M) :
    (cast (congrArg (FormField E M) h) γ : FormField E M b) x =
      ContinuousAlternatingMap.domDomCongr (finCongr h) (γ x) := by
  cases h
  rfl

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem cast_wedge_left (γ : FormField E M ((k + 1) + l)) (x : M) :
    (cast (congrArg (FormField E M) (Nat.add_right_comm k 1 l)) γ :
      FormField E M ((k + l) + 1)) x =
      ContinuousAlternatingMap.domDomCongr Fin.finAddFlipAssoc (γ x) := by
  exact cast_formField _ _ _

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem cast_wedge_right (γ : FormField E M (k + (l + 1))) (x : M) :
    (cast (congrArg (FormField E M) (Nat.add_assoc k l 1).symm) γ :
      FormField E M ((k + l) + 1)) x =
      ContinuousAlternatingMap.domDomCongr Fin.finAssoc.symm (γ x) := by
  exact cast_formField (Nat.add_assoc k l 1).symm γ x

/-- The even-degree case of `d(α ∧ β) = dα ∧ β + (-1)^k α ∧ dβ`. -/
theorem extDeriv_wedge_even {α : FormField E M k} {β : FormField E M l}
    (hα : α.IsSmooth) (hβ : β.IsSmooth) (hk : Even k) :
    (wedge α β).extDeriv = derivWedgeLeft α β + derivWedgeRight α β := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro v
  let c := extChartAt 𝓘(ℝ, E) x
  have hz : c x ∈ c.target := mem_extChartAt_target x
  have ha : DifferentiableAt ℝ (α.chartRep x) (c x) :=
    ((hα x).contDiffAt (extChartAt_target_mem_nhds x)).differentiableAt (by simp)
  have hb : DifferentiableAt ℝ (β.chartRep x) (c x) :=
    ((hβ x).contDiffAt (extChartAt_target_mem_nhds x)).differentiableAt (by simp)
  have hl := local_extDeriv_wedge_even ha hb hk
  change _root_.extDeriv ((wedge α β).chartRep x) (c x) v =
    ((derivWedgeLeft α β + derivWedgeRight α β) x) v
  rw [chartRep_wedge, derivWedgeLeft, derivWedgeRight]
  simp only [Pi.add_apply, cast_wedge_left, cast_wedge_right]
  have heq := congrArg (fun q => q v) hl
  simpa only [c, extDeriv, chartRep_self, wedge] using heq

end FormField
