module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {n : ℕ}

/-- The integral of the coordinate divergence of a compactly supported `C¹` vector
field on real `(n+1)`-space vanishes. The proof integrates over a box enclosing
its support: on every front and back face the field vanishes. -/
theorem integral_coordinateDivergence_eq_zero
    {V : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ}
    (hV : ContDiff ℝ 1 V) (hcompact : HasCompactSupport V) :
    ∫ x, (∑ i : Fin (n + 1),
      fderiv ℝ (fun y => V y i) x (Pi.single i (1 : ℝ)))
      ∂(volume : Measure (Fin (n + 1) → ℝ)) = 0 := by
  classical
  let d := n + 1
  let K : Set (Fin d → ℝ) := tsupport V
  have hK : IsCompact K := hcompact
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Fin d → ℝ)
  have hcoord (x : Fin d → ℝ) (hx : x ∈ tsupport V) (i : Fin d) :
      -R < x i ∧ x i < R := by
    have hxball : x ∈ Metric.ball 0 R := hR hx
    have hnorm : ‖x‖ < R := by simpa [Metric.mem_ball] using hxball
    have hi : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    have habs : |x i| < R := by
      simpa [Real.norm_eq_abs] using hi.trans_lt hnorm
    exact abs_lt.mp habs
  let a : Fin d → ℝ := fun _ => -R
  let b : Fin d → ℝ := fun _ => R
  have hle : a ≤ b := by
    intro i
    exact neg_le_self hRpos.le
  let f : Fin d → (Fin d → ℝ) → ℝ := fun i x => V x i
  let f' : Fin d → (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ := fun i x =>
    (ContinuousLinearMap.proj i).comp (fderiv ℝ V x)
  have hVderiv (x : Fin d → ℝ) : HasFDerivAt V (fderiv ℝ V x) x :=
    ((hV.contDiffAt (x := x)).differentiableAt (by norm_num)).hasFDerivAt
  have hC : ∀ i, ContinuousOn (f i) (Set.Icc a b) := by
    intro i
    exact ((continuous_apply i).comp hV.continuous).continuousOn
  have hD (i : Fin d) (x : Fin d → ℝ) : HasFDerivAt (f i) (f' i x) x := by
    change HasFDerivAt (fun y => V y i) _ x
    have hcomp := (ContinuousLinearMap.proj i).hasFDerivAt.comp x (hVderiv x)
    change HasFDerivAt (fun y : Fin d → ℝ => V y i)
      ((ContinuousLinearMap.proj i).comp (fderiv ℝ V x)) x
    exact hcomp
  have hD' : ∀ x ∈ (Set.univ.pi fun i => Set.Ioo (a i) (b i)) \ (∅ : Set (Fin d → ℝ)),
      ∀ i, HasFDerivAt (f i) (f' i x) x := by
    intro x hx i
    exact hD i x
  have hDF (x : Fin d → ℝ) :
      (∑ i : Fin d, f' i x (Pi.single i (1 : ℝ))) =
      ∑ i : Fin d, fderiv ℝ (fun y => V y i) x (Pi.single i (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hcomp := (ContinuousLinearMap.proj i).hasFDerivAt.comp x (hVderiv x)
    have heq := hcomp.fderiv
    change f' i x (Pi.single i (1 : ℝ)) = _
    rw [show f' i x = (fderiv ℝ (fun y => V y i) x) by
      apply ContinuousLinearMap.ext
      intro v
      have heval := congrArg (fun L => L v) heq
      simpa [Function.comp_def, f'] using heval.symm]
  have hderivCont : Continuous (fderiv ℝ V) :=
    hV.continuous_fderiv (by norm_num)
  have hdivCont : Continuous (fun x : Fin d → ℝ =>
      ∑ i : Fin d, f' i x (Pi.single i (1 : ℝ))) := by
    apply continuous_finsetSum
    intro i hi
    change Continuous (fun x => ((ContinuousLinearMap.proj i).comp
      (fderiv ℝ V x)) (Pi.single i (1 : ℝ)))
    exact (continuous_apply i).comp
      (hderivCont.clm_apply continuous_const)
  have hdivZero (x : Fin d → ℝ) (hx : x ∉ tsupport V) :
      (∑ i : Fin d, f' i x (Pi.single i (1 : ℝ))) = 0 := by
    have hloc : V =ᶠ[nhds x] fun _ => (0 : Fin d → ℝ) := by
      filter_upwards [(isClosed_tsupport V).isOpen_compl.mem_nhds hx] with y hy
      by_contra hne
      exact hy (subset_tsupport _ hne)
    have hderiv : fderiv ℝ V x = 0 :=
      (hasFDerivAt_zero_of_eventually_const (0 : Fin d → ℝ) hloc).fderiv
    simp [f', hderiv]
  have hdivCompact : HasCompactSupport
      (fun x : Fin d → ℝ => ∑ i : Fin d, f' i x (Pi.single i (1 : ℝ))) :=
    HasCompactSupport.intro hcompact (fun x hx => hdivZero x hx)
  have hdivIntegrable : Integrable
      (fun x : Fin d → ℝ => ∑ i : Fin d, f' i x (Pi.single i (1 : ℝ)))
      (volume : Measure (Fin d → ℝ)) :=
    hdivCont.integrable_of_hasCompactSupport hdivCompact
  have hI : IntegrableOn
      (fun x : Fin d → ℝ => ∑ i : Fin d, f' i x (Pi.single i (1 : ℝ)))
      (Set.Icc a b) (volume : Measure (Fin d → ℝ)) := hdivIntegrable.integrableOn
  have hsum := MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
    a b hle f f' ∅ Set.countable_empty hC hD' hI
  have hVzero (x : Fin d → ℝ) (i : Fin d)
      (hc : x i = R ∨ x i = -R) : V x = 0 := by
    by_contra hne
    have hx : x ∈ tsupport V := subset_tsupport _ hne
    rcases hc with hc | hc
    · linarith [(hcoord x hx i).2]
    · linarith [(hcoord x hx i).1]
  have hfrontzero (i : Fin d) (y : Fin n → ℝ) : f i (i.insertNth R y) = 0 := by
    dsimp [f]
    have hz : V (i.insertNth R y) = 0 := by
      apply hVzero
      exact Or.inl (Fin.insertNth_apply_same (α := fun _ : Fin d => ℝ) i R y)
    simp [hz]
  have hbackzero (i : Fin d) (y : Fin n → ℝ) : f i (i.insertNth (-R) y) = 0 := by
    dsimp [f]
    have hz : V (i.insertNth (-R) y) = 0 := by
      apply hVzero
      exact Or.inr (Fin.insertNth_apply_same (α := fun _ : Fin d => ℝ) i (-R) y)
    simp [hz]
  have hfrontInt (i : Fin d) :
      (∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        f i (i.insertNth (b i) y)) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact hfrontzero i y
  have hbackInt (i : Fin d) :
      (∫ y in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        f i (i.insertNth (a i) y)) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    exact hbackzero i y
  have hbox :
      (∫ x in Set.Icc a b,
        ∑ i : Fin d, f' i x (Pi.single i (1 : ℝ))) = 0 := by
    rw [hsum]
    simp [hfrontInt, hbackInt]
  have hsupportBox : tsupport V ⊆ Set.Icc a b := by
    intro x hx
    constructor <;> intro i
    · simpa [a] using (hcoord x hx i).1.le
    · simpa [b] using (hcoord x hx i).2.le
  have hglobal :
      (∫ x, (∑ i : Fin d, fderiv ℝ (fun y => V y i) x
        (Pi.single i (1 : ℝ))) ∂(volume : Measure (Fin d → ℝ))) =
      ∫ x in Set.Icc a b,
        ∑ i : Fin d, f' i x (Pi.single i (1 : ℝ)) := by
    rw [show (fun x : Fin d → ℝ => ∑ i, fderiv ℝ (fun y => V y i) x
        (Pi.single i (1 : ℝ))) = fun x => ∑ i, f' i x (Pi.single i (1 : ℝ)) by
      funext x
      symm
      exact hDF x]
    symm
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply hdivZero x
    intro hx'
    exact hx (hsupportBox hx')
  rw [hglobal]
  exact hbox

end MeasureTheory
