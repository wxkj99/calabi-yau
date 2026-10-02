module

public import CalabiYau.Geometry.Complex.Schauder.OperatorCommutator
public import CalabiYau.Geometry.Complex.Schauder.DerivativeHolder

/-!
# Hölder bounds for directional coefficient derivatives

This estimate transfers entrywise coefficient jets to the directional derivative field.
-/

@[expose] public section

open Set Matrix
open scoped NNReal

namespace CalabiYau.Schauder

private theorem coefficient_iteratedFDeriv_directional_eval
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {k : ℕ} {f : E → F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U) {x : E} (hx : x ∈ U) (v : E) :
    iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ f y v) x =
      (ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap
        ((continuousMultilinearCurryRightEquiv' ℝ k E F)
          (iteratedFDeriv ℝ (k + 1) f x)) := by
  have hD : ContDiffOn ℝ k (fderiv ℝ f) U := by
    apply hf.fderiv_of_isOpen hU
    exact_mod_cast (Nat.le_refl (k + 1))
  have hg : ContDiffOn ℝ k (fun y ↦ fderiv ℝ f y v) U :=
    hD.clm_apply contDiffOn_const
  have hDtotal (m : ℕ) (hm : m ≤ k) :
      iteratedFDerivWithin ℝ m (fderiv ℝ f) U x = iteratedFDeriv ℝ m (fderiv ℝ f) x := by
    apply iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    · exact (hD.contDiffAt (hU.mem_nhds hx)).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hm))
    · exact hx
  have hgtotal (m : ℕ) (hm : m ≤ k) :
      iteratedFDerivWithin ℝ m (fun y ↦ fderiv ℝ f y v) U x =
        iteratedFDeriv ℝ m (fun y ↦ fderiv ℝ f y v) x := by
    apply iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    · exact (hg.contDiffAt (hU.mem_nhds hx)).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hm))
    · exact hx
  ext m
  rw [← hgtotal k le_rfl]
  rw [iteratedFDerivWithin_clm_apply_const_apply hU.uniqueDiffOn hD le_rfl hx]
  rw [hDtotal k le_rfl]
  simp [continuousMultilinearCurryRightEquiv_apply', iteratedFDeriv_succ_apply_right]

private theorem holderBoundOn_coefficient_directionalDerivative_unit
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {k : ℕ} {α C : ℝ≥0} {f : E → F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U)
    (hbound : HolderBoundOn (k + 1) α C U f) (v : E) (hv : ‖v‖ ≤ 1) :
    HolderBoundOn k α C U (fun z ↦ fderiv ℝ f z v) := by
  have hD : ContDiffOn ℝ k (fderiv ℝ f) U := by
    apply hf.fderiv_of_isOpen hU
    exact_mod_cast (Nat.le_refl (k + 1))
  have hEval : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
    intro L
    simpa [mul_comm] using L.le_opNorm v
  have hPostApplied (j : ℕ) (T : E [×j]→L[ℝ] (E →L[ℝ] F)) :
      ‖(ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap T‖ ≤
        ‖v‖ * ‖T‖ := by
    exact ((ContinuousLinearMap.apply ℝ F v).norm_compContinuousMultilinearMap_le T).trans
      (mul_le_mul_of_nonneg_right hEval (norm_nonneg T))
  have hCurryHolder : HolderOnWith C α
      (fun z ↦ (continuousMultilinearCurryRightEquiv' ℝ k E F)
        (iteratedFDeriv ℝ (k + 1) f z)) U := by
    intro x hx y hy
    simpa [edist_dist, (continuousMultilinearCurryRightEquiv' ℝ k E F).dist_map] using
      hbound.2 x hx y hy
  have hPostDist (S T : E [×k]→L[ℝ] (E →L[ℝ] F)) :
      dist ((ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap S)
        ((ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap T) ≤ dist S T := by
    have hdiff :
        (ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap S -
          (ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap T =
            (ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap (S - T) := by
      ext m
      simp
    rw [dist_eq_norm, hdiff]
    calc
      ‖(ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap (S - T)‖ ≤
          ‖ContinuousLinearMap.apply ℝ F v‖ * ‖S - T‖ :=
        (ContinuousLinearMap.apply ℝ F v).norm_compContinuousMultilinearMap_le _
      _ ≤ 1 * ‖S - T‖ := mul_le_mul_of_nonneg_right
        (hEval.trans (by exact_mod_cast hv)) (norm_nonneg _)
      _ = dist S T := by simp [dist_eq_norm]
  have hCurryHolder : HolderOnWith C α
      (fun z ↦ (continuousMultilinearCurryRightEquiv' ℝ k E F)
        (iteratedFDeriv ℝ (k + 1) f z)) U := by
    intro x hx y hy
    simpa [edist_dist, (continuousMultilinearCurryRightEquiv' ℝ k E F).dist_map] using
      hbound.2 x hx y hy
  have hJetEq (z : E) (hz : z ∈ U) :
      (ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap
        ((continuousMultilinearCurryRightEquiv' ℝ k E F)
          (iteratedFDeriv ℝ (k + 1) f z)) = iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ f y v) z :=
    (coefficient_iteratedFDeriv_directional_eval hU hf hz v).symm
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hjbound : j + 1 ≤ k + 1 := Nat.succ_le_succ hj
    have hjboundTop : (j : WithTop ℕ) + 1 ≤ (k : WithTop ℕ) + 1 := by
      exact_mod_cast hjbound
    have hf' : ContDiffOn ℝ (j + 1) f U :=
      hf.of_le (WithTop.coe_le_coe.mpr hjboundTop)
    have hJetEqj :
        iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ f y v) z =
          (ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap
            ((continuousMultilinearCurryRightEquiv' ℝ j E F)
              (iteratedFDeriv ℝ (j + 1) f z)) :=
      coefficient_iteratedFDeriv_directional_eval hU hf' hz v
    have hsrc := hbound.1 (j + 1) hjbound z hz
    calc
      ‖iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ f y v) z‖ =
          ‖(ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap
            ((continuousMultilinearCurryRightEquiv' ℝ j E F)
              (iteratedFDeriv ℝ (j + 1) f z))‖ := congrArg norm hJetEqj
      _ ≤ ‖v‖ *
          ‖(continuousMultilinearCurryRightEquiv' ℝ j E F)
            (iteratedFDeriv ℝ (j + 1) f z)‖ := hPostApplied j _
      _ = ‖v‖ * ‖iteratedFDeriv ℝ (j + 1) f z‖ := by
        rw [(continuousMultilinearCurryRightEquiv' ℝ j E F).norm_map]
      _ ≤ ‖v‖ * C := mul_le_mul_of_nonneg_left hsrc (norm_nonneg _)
      _ ≤ C := by
        calc
          ‖v‖ * C ≤ 1 * C := mul_le_mul_of_nonneg_right hv (show 0 ≤ C by exact bot_le)
          _ = C := by simp
  · intro z hz w hw
    rw [← hJetEq z hz, ← hJetEq w hw]
    calc
      edist ((ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap
          ((continuousMultilinearCurryRightEquiv' ℝ k E F)
            (iteratedFDeriv ℝ (k + 1) f z)))
        ((ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap
          ((continuousMultilinearCurryRightEquiv' ℝ k E F)
            (iteratedFDeriv ℝ (k + 1) f w))) ≤
          ENNReal.ofReal (dist
            ((continuousMultilinearCurryRightEquiv' ℝ k E F)
              (iteratedFDeriv ℝ (k + 1) f z))
            ((continuousMultilinearCurryRightEquiv' ℝ k E F)
              (iteratedFDeriv ℝ (k + 1) f w))) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (hPostDist _ _)
      _ = edist
          ((continuousMultilinearCurryRightEquiv' ℝ k E F)
            (iteratedFDeriv ℝ (k + 1) f z))
          ((continuousMultilinearCurryRightEquiv' ℝ k E F)
            (iteratedFDeriv ℝ (k + 1) f w)) := (edist_dist _ _).symm
      _ ≤ (C : ENNReal) * edist z w ^ (α : ℝ) := hCurryHolder z hz w hw

/-- A unit directional derivative of a matrix coefficient has the expected lower-order
`HolderBoundOn` control, entrywise. -/
theorem holderBoundOn_coefficient_directional_derivative
    {n k : ℕ} {α K : ℝ≥0}
    {U V : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hVU : V ⊆ U)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (e : EuclideanSpace ℂ (Fin n))
    (hACont : ∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U)
    (hA : ∀ i j, HolderBoundOn (k + 1) α K U (fun z ↦ A z i j))
    (he : ‖e‖ ≤ 1) :
    ∀ i j,
      ContDiffOn ℝ k (fun z ↦ (fderiv ℝ A z e) i j) V ∧
      HolderBoundOn k α K V (fun z ↦ (fderiv ℝ A z e) i j) := by
  intro i j
  let f : EuclideanSpace ℂ (Fin n) → ℂ := fun z ↦ A z i j
  have hfCont : ContDiffOn ℝ (k + 1) f U := hACont i j
  have hfBound : HolderBoundOn (k + 1) α K U f := hA i j
  have hdir := holderBoundOn_coefficient_directionalDerivative_unit
    hU hfCont hfBound e he
  have hD : ContDiffOn ℝ k (fderiv ℝ f) U := by
    apply hfCont.fderiv_of_isOpen hU
    exact_mod_cast (Nat.le_refl (k + 1))
  have hscalarCont : ContDiffOn ℝ k (fun z ↦ fderiv ℝ f z e) U :=
    hD.clm_apply contDiffOn_const
  have hentryDiff (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
      (p q : Fin n) : DifferentiableAt ℝ (fun y ↦ A y p q) z := by
    exact ((hACont p q).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hrowDiff (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (i : Fin n) :
      DifferentiableAt ℝ (fun y ↦ A y i) z := by
    apply differentiableAt_pi.2
    intro j
    exact hentryDiff z hz i j
  have hmatDiff (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
      DifferentiableAt ℝ A z := by
    apply differentiableAt_pi.2
    exact hrowDiff z hz
  have hentryEq (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
      (fderiv ℝ A z e) i j = fderiv ℝ f z e := by
    change (fderiv ℝ (fun y a b ↦ A y a b) z e) i j = fderiv ℝ f z e
    rw [fderiv_pi (hrowDiff z hz), ContinuousLinearMap.pi_apply,
      fderiv_pi (hentryDiff z hz i)]
    rfl
  have htargetCont : ContDiffOn ℝ k
      (fun z ↦ (fderiv ℝ A z e) i j) U := by
    apply hscalarCont.congr
    intro z hz
    exact hentryEq z hz
  have hjetEq (m : ℕ) (hm : m ≤ k) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
      iteratedFDeriv ℝ m (fun y ↦ (fderiv ℝ A y e) i j) z =
        iteratedFDeriv ℝ m (fun y ↦ fderiv ℝ f y e) z := by
    have hleftAt : ContDiffAt ℝ m (fun y ↦ (fderiv ℝ A y e) i j) z :=
      (htargetCont.contDiffAt (hU.mem_nhds hz)).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hm))
    have hrightAt : ContDiffAt ℝ m (fun y ↦ fderiv ℝ f y e) z :=
      (hscalarCont.contDiffAt (hU.mem_nhds hz)).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hm))
    calc
      iteratedFDeriv ℝ m (fun y ↦ (fderiv ℝ A y e) i j) z =
          iteratedFDerivWithin ℝ m (fun y ↦ (fderiv ℝ A y e) i j) U z :=
        (iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hleftAt hz).symm
      _ = iteratedFDerivWithin ℝ m (fun y ↦ fderiv ℝ f y e) U z :=
        iteratedFDerivWithin_congr (fun y hy ↦ hentryEq y hy) hz m
      _ = iteratedFDeriv ℝ m (fun y ↦ fderiv ℝ f y e) z :=
        iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hrightAt hz
  have hdirV := hdir.mono_set hVU
  refine ⟨(htargetCont.mono hVU), ?_⟩
  refine ⟨?_, ?_⟩
  · intro m hm z hz
    rw [hjetEq m hm z (hVU hz)]
    exact hdirV.1 m hm z hz
  · intro z hz w hw
    rw [hjetEq k le_rfl z (hVU hz), hjetEq k le_rfl w (hVU hw)]
    exact hdirV.2 z hz w hw

end CalabiYau.Schauder
