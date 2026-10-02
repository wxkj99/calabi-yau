module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.Stokes.Basic

/-!
# Exterior derivative of an odd-degree wedge

For odd `k`, moving the exterior differential past the `k` inputs of the
first factor changes sign. This statement concerns the actual normalized
shuffle `FormField.wedge`, with exterior differentiation computed in charts by
`FormField.extDeriv`; in particular the sign is not a choice of convention.

Source: Bott–Tu, *Differential Forms in Algebraic Topology*, Chapter I, §1,
Proposition 1.3, odd-degree case of the antiderivation formula.
-/

@[expose] public section

open scoped Manifold ContDiff

private theorem fderiv_bilinear
    {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    (B : F →L[𝕜] G →L[𝕜] H) (f : E → F) (g : E → G) (x : E)
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => B (f y) (g y)) x =
      B.precompR E (f x) (fderiv 𝕜 g x) + B.precompL E (fderiv 𝕜 f x) (g x) := by
  exact (B.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).fderiv

private theorem extDeriv_eq_uncurryFin_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (f : E → E [⋀^Fin n]→L[ℝ] ℝ) (x : E)
    (hf : DifferentiableAt ℝ f x) :
    _root_.extDeriv f x = ContinuousAlternatingMap.uncurryFin (fderiv ℝ f x) := by
  ext v
  rw [_root_.extDeriv_apply hf, ContinuousAlternatingMap.uncurryFin_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simpa using (fderiv_continuousAlternatingMap_apply_apply
    (f := f) (g := fun j : Fin n => fun _ : E => (i.removeNth v) j) hf
    (fun j => differentiableAt_const (c := (i.removeNth v) j)) (v i))

private theorem extDeriv_wedgeProduct_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k l : ℕ} (α : E → E [⋀^Fin k]→L[ℝ] ℝ)
    (β : E → E [⋀^Fin l]→L[ℝ] ℝ) (x : E)
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    _root_.extDeriv (fun y => ContinuousAlternatingMap.wedgeProduct (α y) (β y)
      (ContinuousLinearMap.mul ℝ ℝ)) x =
      ContinuousAlternatingMap.uncurryFin
        ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR
          E (α x) (fderiv ℝ β x)) +
      ContinuousAlternatingMap.uncurryFin
        ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompL
          E (fderiv ℝ α x) (β x)) := by
  have hprod : DifferentiableAt ℝ (fun y => ContinuousAlternatingMap.wedgeProduct
      (α y) (β y) (ContinuousLinearMap.mul ℝ ℝ)) x := by
    exact (ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).hasFDerivAt_of_bilinear
      hα.hasFDerivAt hβ.hasFDerivAt |>.differentiableAt
  rw [extDeriv_eq_uncurryFin_local _ x hprod]
  change ContinuousAlternatingMap.uncurryFin
      (fderiv ℝ (fun y =>
        (ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)) (α y) (β y)) x) = _
  rw [fderiv_bilinear (ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ))
      α β x hα hβ,
    ContinuousAlternatingMap.uncurryFin_add]

private theorem uncurryFin_wedge_precompR
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k l : ℕ} (α : E [⋀^Fin k]→L[ℝ] ℝ)
    (g : E →L[ℝ] E [⋀^Fin l]→L[ℝ] ℝ) :
    ContinuousAlternatingMap.uncurryFin
      ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR E α g) =
      (-1 : ℝ)^k • ContinuousAlternatingMap.wedgeProduct α
        (ContinuousAlternatingMap.uncurryFin g) (ContinuousLinearMap.mul ℝ ℝ) := by
  have graded_sign_rearrangement_local (a b : ℕ) :
      (-1 : ℝ)^a * (-1 : ℝ)^(a * (b + 1)) = (-1 : ℝ)^(a * b) := by
    calc
      (-1 : ℝ)^a * (-1 : ℝ)^(a * (b + 1)) = (-1 : ℝ)^(a + a * (b + 1)) := by
        rw [← pow_add]
      _ = (-1 : ℝ)^(a * b + 2 * a) := by
        congr 1
        rw [Nat.mul_add]
        omega
      _ = (-1 : ℝ)^(a * b) * (-1 : ℝ)^(2 * a) := by rw [pow_add]
      _ = (-1 : ℝ)^(a * b) := by rw [pow_mul]; norm_num
  let rightInsertionFinPermLocal (a b : ℕ) : Fin (b + a + 1) ≃ Fin (a + b + 1) :=
    (Fin.finAddFlipAssoc (m := b) (n := a) (p := 1)).symm.trans
      ((Fin.finAddCongr (m := b + 1) (n := a)).trans
        (Fin.finAssoc (m := a) (n := b) (p := 1)).symm)
  have rightInsertionFinPermLocal_assoc (a b : ℕ) :
      (Fin.finAddFlipAssoc (m := b) (n := a) (p := 1)).trans
          (rightInsertionFinPermLocal a b) =
        (Fin.finAddCongr (m := b + 1) (n := a)).trans
          (Fin.finAssoc (m := a) (n := b) (p := 1)).symm := by
    change (Fin.finAddFlipAssoc (m := b) (n := a) (p := 1)).trans
        ((Fin.finAddFlipAssoc (m := b) (n := a) (p := 1)).symm.trans
          ((Fin.finAddCongr (m := b + 1) (n := a)).trans
            (Fin.finAssoc (m := a) (n := b) (p := 1)).symm)) = _
    rw [← Equiv.trans_assoc]
    simp
  have wedgeProduct_swap_local {a b : ℕ}
      (γ : E [⋀^Fin a]→L[ℝ] ℝ) (δ : E [⋀^Fin b]→L[ℝ] ℝ) :
      ContinuousAlternatingMap.wedgeProduct γ δ (ContinuousLinearMap.mul ℝ ℝ) =
        (-1 : ℝ)^(a * b) • ContinuousAlternatingMap.domDomCongr
          (Fin.finAddCongr (m := b) (n := a))
          (ContinuousAlternatingMap.wedgeProduct δ γ (ContinuousLinearMap.mul ℝ ℝ)) := by
    have h := ContinuousAlternatingMap.wedge_antisymm γ δ
    rw [ContinuousAlternatingMap.domDomCongr_smul] at h
    exact h
  have domDomCongr_cast_local {a b : ℕ} (h : a = b)
      (φ : E [⋀^Fin a]→L[ℝ] ℝ) :
      ContinuousAlternatingMap.domDomCongr (Equiv.cast (congrArg Fin h)) φ =
        cast (congrArg (fun q => E [⋀^Fin q]→L[ℝ] ℝ) h) φ := by
    cases h
    rfl
  have uncurryFin_cast_local {a b : ℕ} (h : a = b)
      (f : E →L[ℝ] E [⋀^Fin a]→L[ℝ] ℝ) :
      ContinuousAlternatingMap.uncurryFin
          (cast (congrArg (fun q => E →L[ℝ] E [⋀^Fin q]→L[ℝ] ℝ) h) f) =
        cast (congrArg (fun q => E [⋀^Fin q]→L[ℝ] ℝ) (congrArg Nat.succ h))
          (ContinuousAlternatingMap.uncurryFin f) := by
    cases h
    rfl
  have castCLM_apply_local {a b : ℕ} (h : a = b)
      (f : E →L[ℝ] E [⋀^Fin a]→L[ℝ] ℝ) (x : E) :
      (cast (congrArg (fun q => E →L[ℝ] E [⋀^Fin q]→L[ℝ] ℝ) h) f) x =
        cast (congrArg (fun q => E [⋀^Fin q]→L[ℝ] ℝ) h) (f x) := by
    cases h
    rfl
  have cast_smul_local {a b : ℕ} (h : a = b) (c : ℝ)
      (φ : E [⋀^Fin a]→L[ℝ] ℝ) :
      cast (congrArg (fun q => E [⋀^Fin q]→L[ℝ] ℝ) h) (c • φ) =
        c • cast (congrArg (fun q => E [⋀^Fin q]→L[ℝ] ℝ) h) φ := by
    cases h
    rfl
  have rightInsertionFinPermLocal_cast (a b : ℕ) :
      rightInsertionFinPermLocal a b =
        Equiv.cast (congrArg Fin (congrArg Nat.succ (Nat.add_comm b a))) := by
    let hcast : b + (a + 1) = a + b + 1 := by omega
    have hflip (j : Fin (b + (a + 1))) :
        ((Fin.finAddFlipAssoc (m := b) (n := a) (p := 1)).symm j).val = j.val := by
      change ((finCongr _).symm j).val = j.val
      exact finCongr_symm_apply_coe _ j
    have hadd (j : Fin (b + 1 + a)) :
        (Fin.finAddCongr (m := b + 1) (n := a) j).val = j.val := by
      change (finCongr _ j).val = j.val
      exact finCongr_apply_coe _ j
    have hassoc (j : Fin (a + (b + 1))) :
        ((Fin.finAssoc (m := a) (n := b) (p := 1)).symm j).val = j.val := by
      change ((finCongr _).symm j).val = j.val
      exact finCongr_symm_apply_coe _ j
    have heval (j : Fin (b + a + 1)) : (rightInsertionFinPermLocal a b j).val = j.val := by
      dsimp [rightInsertionFinPermLocal]
      calc
        ((Fin.finAssoc (m := a) (n := b) (p := 1)).symm
          (Fin.finAddCongr (m := b + 1) (n := a)
            ((Fin.finAddFlipAssoc (m := b) (n := a) (p := 1)).symm j))).val =
            (Fin.finAddCongr (m := b + 1) (n := a)
              ((Fin.finAddFlipAssoc (m := b) (n := a) (p := 1)).symm j)).val :=
          hassoc _
        _ = ((Fin.finAddFlipAssoc (m := b) (n := a) (p := 1)).symm j).val := hadd _
        _ = j.val := hflip j
    have heq : rightInsertionFinPermLocal a b = Equiv.cast (congrArg Fin hcast) := by
      ext j
      rw [heval]
      rw [← finCongr_eq_equivCast hcast]
      simp
    have hcast' : hcast = congrArg Nat.succ (Nat.add_comm b a) := by
      apply Subsingleton.elim
    simpa [hcast'] using heq
  have wedge_precompR_cast_local {a : E [⋀^Fin k]→L[ℝ] ℝ}
      (db : E →L[ℝ] E [⋀^Fin l]→L[ℝ] ℝ) :
      (ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR
          E a db =
        cast (congrArg (fun q => E →L[ℝ] E [⋀^Fin q]→L[ℝ] ℝ) (Nat.add_comm l k))
          ((-1 : ℝ)^(k * l) •
            (ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompL
              E db a) := by
    ext y v
    change (ContinuousAlternatingMap.wedgeProduct a (db y) (ContinuousLinearMap.mul ℝ ℝ)) v =
      (cast (congrArg (fun q => E →L[ℝ] E [⋀^Fin q]→L[ℝ] ℝ) (Nat.add_comm l k))
        ((-1 : ℝ)^(k * l) •
          (ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompL
            E db a)) y v
    rw [castCLM_apply_local]
    change (ContinuousAlternatingMap.wedgeProduct a (db y)
        (ContinuousLinearMap.mul ℝ ℝ)) v =
      (cast (congrArg (fun q => E [⋀^Fin q]→L[ℝ] ℝ) (Nat.add_comm l k))
        ((-1 : ℝ)^(k * l) •
          ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompL
            E db a) y)) v
    rw [cast_smul_local, ContinuousLinearMap.precompL_apply,
      ContinuousAlternatingMap.wedge_productL_apply]
    have hswap := wedgeProduct_swap_local a (db y)
    have hFinCast : Fin.finAddCongr (m := l) (n := k) =
        Equiv.cast (congrArg Fin (Nat.add_comm l k)) := by
      simpa [Fin.finAddCongr] using finCongr_eq_equivCast (Nat.add_comm l k)
    rw [hFinCast, domDomCongr_cast_local] at hswap
    all_goals try omega
    exact congrArg (fun φ => φ v) hswap
  have rightInsertion_wedgeSymmetry_local {a : E [⋀^Fin k]→L[ℝ] ℝ}
      (db : E →L[ℝ] E [⋀^Fin l]→L[ℝ] ℝ) :
      (-1 : ℝ)^k • ContinuousAlternatingMap.domDomCongr Fin.finAssoc.symm
          (ContinuousAlternatingMap.wedgeProduct a
            (ContinuousAlternatingMap.uncurryFin db) (ContinuousLinearMap.mul ℝ ℝ)) =
        (-1 : ℝ)^(k * l) •
          ContinuousAlternatingMap.domDomCongr
            (Fin.finAddCongr.trans Fin.finAssoc.symm)
            (ContinuousAlternatingMap.wedgeProduct
              (ContinuousAlternatingMap.uncurryFin db) a (ContinuousLinearMap.mul ℝ ℝ)) := by
    have hswap := ContinuousAlternatingMap.wedge_antisymm a
      (ContinuousAlternatingMap.uncurryFin db)
    rw [hswap, ContinuousAlternatingMap.domDomCongr_smul,
      ContinuousAlternatingMap.domDomCongr_smul,
      ContinuousAlternatingMap.domDomCongr_trans,
      smul_smul, graded_sign_rearrangement_local]
  have hmap := wedge_precompR_cast_local (a := α) g
  have hunc : ContinuousAlternatingMap.uncurryFin
        ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR
          E α g) =
      (-1 : ℝ)^(k * l) •
        cast (congrArg (fun q => E [⋀^Fin q]→L[ℝ] ℝ)
          (congrArg Nat.succ (Nat.add_comm l k)))
          (ContinuousAlternatingMap.uncurryFin
            ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompL
              E g α)) := by
    rw [hmap, uncurryFin_cast_local, ContinuousAlternatingMap.uncurryFin_smul,
      cast_smul_local]
    all_goals omega
  have hleft := ContinuousAlternatingMap.uncurryFin_wedge_productL_precompL_eq_domDomCongr
      (ContinuousLinearMap.mul ℝ ℝ) g α
  rw [hleft, ← domDomCongr_cast_local (congrArg Nat.succ (Nat.add_comm l k)),
    ContinuousAlternatingMap.domDomCongr_trans,
    ← rightInsertionFinPermLocal_cast k l,
    rightInsertionFinPermLocal_assoc k l] at hunc
  calc
    ContinuousAlternatingMap.uncurryFin
        ((ContinuousAlternatingMap.wedgeProductL (ContinuousLinearMap.mul ℝ ℝ)).precompR
          E α g) =
        (-1 : ℝ)^(k * l) •
          ContinuousAlternatingMap.domDomCongr
            (Fin.finAddCongr.trans Fin.finAssoc.symm)
            (ContinuousAlternatingMap.wedgeProduct
              (ContinuousAlternatingMap.uncurryFin g) α (ContinuousLinearMap.mul ℝ ℝ)) := hunc
    _ = (-1 : ℝ)^k • ContinuousAlternatingMap.domDomCongr Fin.finAssoc.symm
          (ContinuousAlternatingMap.wedgeProduct α
            (ContinuousAlternatingMap.uncurryFin g) (ContinuousLinearMap.mul ℝ ℝ)) :=
      (rightInsertion_wedgeSymmetry_local (a := α) g).symm
    _ = (-1 : ℝ)^k • ContinuousAlternatingMap.wedgeProduct α
          (ContinuousAlternatingMap.uncurryFin g) (ContinuousLinearMap.mul ℝ ℝ) := by
      congr 1

namespace FormField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {k l : ℕ}

private theorem odd_pow_neg_one {k : ℕ} (hk : Odd k) : (-1 : ℝ) ^ k = -1 := by
  rcases hk with ⟨m, hm⟩
  rw [hm]
  simp [pow_add]

/-- The odd-degree case of `d(α ∧ β) = dα ∧ β - α ∧ dβ`. -/
theorem extDeriv_wedge_odd {α : FormField E M k} {β : FormField E M l}
    (hα : α.IsSmooth) (hβ : β.IsSmooth) (hk : Odd k) :
    (wedge α β).extDeriv = derivWedgeLeft α β - derivWedgeRight α β := by
  funext x
  have formFieldCastApply {m n : ℕ} (h : m = n)
      (f : FormField E M m) (y : M) :
      (cast (congrArg (FormField E M) h) f) y =
        cast (congrArg (fun d => E [⋀^Fin d]→L[ℝ] ℝ) h) (f y) := by
    cases h
    rfl
  have altCastDomDom {m n : ℕ} (h : m = n)
      (f : E [⋀^Fin m]→L[ℝ] ℝ) :
      cast (congrArg (fun d => E [⋀^Fin d]→L[ℝ] ℝ) h) f =
        ContinuousAlternatingMap.domDomCongr (finCongr h) f := by
    cases h
    rfl
  have castWedgeLeftTransport {a b : ℕ}
      (γ : FormField E M (a + 1)) (δ : FormField E M b) (y : M) :
      (cast (congrArg (FormField E M) (Nat.add_right_comm a 1 b))
        (wedge γ δ)) y =
        ContinuousAlternatingMap.domDomCongr (finCongr (Nat.add_right_comm a 1 b))
          (ContinuousAlternatingMap.wedgeProduct (γ y) (δ y)
            (ContinuousLinearMap.mul ℝ ℝ)) := by
    calc
      (cast (congrArg (FormField E M) (Nat.add_right_comm a 1 b))
          (wedge γ δ)) y =
        cast (congrArg (fun d => E [⋀^Fin d]→L[ℝ] ℝ) (Nat.add_right_comm a 1 b))
          (ContinuousAlternatingMap.wedgeProduct (γ y) (δ y)
            (ContinuousLinearMap.mul ℝ ℝ)) := by
              exact formFieldCastApply (Nat.add_right_comm a 1 b) (wedge γ δ) y
      _ = _ := altCastDomDom (Nat.add_right_comm a 1 b) _
  have castWedgeLeft {a b : ℕ}
      (γ : FormField E M (a + 1)) (δ : FormField E M b) (y : M) :
      (cast (congrArg (FormField E M) (Nat.add_right_comm a 1 b))
        (wedge γ δ)) y =
        ContinuousAlternatingMap.domDomCongr Fin.finAddFlipAssoc
          (ContinuousAlternatingMap.wedgeProduct (γ y) (δ y)
            (ContinuousLinearMap.mul ℝ ℝ)) := by
    have heq : finCongr (Nat.add_right_comm a 1 b) =
        Fin.finAddFlipAssoc (m := a) (n := b) (p := 1) := by
      apply Equiv.ext
      intro i
      apply Fin.ext
      rfl
    rw [castWedgeLeftTransport, heq]
  have castWedgeRight {a b : ℕ}
      (γ : FormField E M a) (δ : FormField E M (b + 1)) (y : M) :
      (cast (congrArg (FormField E M) (Nat.add_assoc a b 1).symm)
        (wedge γ δ)) y =
        ContinuousAlternatingMap.wedgeProduct (γ y) (δ y)
          (ContinuousLinearMap.mul ℝ ℝ) := by
    rfl
  let z := extChartAt 𝓘(ℝ, E) x x
  have hz : z ∈ (extChartAt 𝓘(ℝ, E) x).target := mem_extChartAt_target x
  have hαz : DifferentiableAt ℝ (α.chartRep x) z :=
    ((hα x).contDiffAt (extChartAt_target_mem_nhds x)).differentiableAt (by simp)
  have hβz : DifferentiableAt ℝ (β.chartRep x) z :=
    ((hβ x).contDiffAt (extChartAt_target_mem_nhds x)).differentiableAt (by simp)
  have hlocal :
      _root_.extDeriv (fun y => ContinuousAlternatingMap.wedgeProduct
        (α.chartRep x y) (β.chartRep x y) (ContinuousLinearMap.mul ℝ ℝ)) z =
      ContinuousAlternatingMap.domDomCongr Fin.finAddFlipAssoc
        (ContinuousAlternatingMap.wedgeProduct (_root_.extDeriv (α.chartRep x) z)
          (β.chartRep x z) (ContinuousLinearMap.mul ℝ ℝ)) +
      (-1 : ℝ)^k • ContinuousAlternatingMap.wedgeProduct (α.chartRep x z)
        (_root_.extDeriv (β.chartRep x) z) (ContinuousLinearMap.mul ℝ ℝ) := by
    rw [extDeriv_wedgeProduct_split (α.chartRep x) (β.chartRep x) z hαz hβz,
      ContinuousAlternatingMap.uncurryFin_wedge_productL_precompL_eq_domDomCongr,
      uncurryFin_wedge_precompR]
    rw [← extDeriv_eq_uncurryFin_local (α.chartRep x) z hαz,
      ← extDeriv_eq_uncurryFin_local (β.chartRep x) z hβz]
    abel
  have hαd : α.extDeriv.chartRep x z = _root_.extDeriv (α.chartRep x) z :=
    chartRep_extDeriv hα x hz
  have hβd : β.extDeriv.chartRep x z = _root_.extDeriv (β.chartRep x) z :=
    chartRep_extDeriv hβ x hz
  rw [← hαd, ← hβd] at hlocal
  rw [show z = extChartAt 𝓘(ℝ, E) x x from rfl] at hlocal
  simp only [chartRep_self] at hlocal
  have hleft := castWedgeLeft α.extDeriv β x
  have hright := castWedgeRight α β.extDeriv x
  rw [← hleft, ← hright] at hlocal
  have hsign : (-1 : ℝ)^k = -1 := hk.neg_one_pow
  rw [hsign, neg_one_smul] at hlocal
  change _root_.extDeriv ((wedge α β).chartRep x) z =
    (cast (congrArg (FormField E M) (Nat.add_right_comm k 1 l))
      (wedge α.extDeriv β)) x -
    (cast (congrArg (FormField E M) (Nat.add_assoc k l 1).symm)
      (wedge α β.extDeriv)) x
  rw [chartRep_wedge]
  exact hlocal

end FormField
