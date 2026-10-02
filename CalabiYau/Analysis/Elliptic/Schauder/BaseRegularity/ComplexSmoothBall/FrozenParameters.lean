module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.ComplexSmoothBall.Basic

/-!
# Uniform frozen-symbol parameters

Source: Gilbarg–Trudinger, §6.1, Theorem 6.2, freezing/interpolation proof;
Constantin, Schauder Estimates, pp. 6–9. The estimates follow Constantin, *Schauder Estimates*, pp. 6–9.
-/

@[expose] public section

open Set Matrix
open scoped NNReal ContDiff Topology

namespace CalabiYau.Schauder

private theorem quadratic_form_entry_bound_aux
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (v : n → ℝ) (K : ℝ≥0)
    (hA : ∀ i j, ‖A i j‖ ≤ (K : ℝ)) :
    dotProduct (star v) (Matrix.mulVec A v) ≤
      (K : ℝ) * (∑ i, |v i|) ^ 2 := by
  classical
  have hentry : ∀ i j, (v i * A i j) * v j ≤ |v i| * (K : ℝ) * |v j| := by
    intro i j
    have hAabs : |A i j| ≤ (K : ℝ) := by simpa [Real.norm_eq_abs] using hA i j
    calc
      (v i * A i j) * v j ≤ |(v i * A i j) * v j| := le_abs_self _
      _ = |v i| * |A i j| * |v j| := by rw [abs_mul, abs_mul]
      _ ≤ |v i| * (K : ℝ) * |v j| := by gcongr
  calc
    dotProduct (star v) (Matrix.mulVec A v) = ∑ i, ∑ j, (v i * A i j) * v j := by
      simp [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, star_trivial,
        mul_assoc]
    _ ≤ ∑ i, ∑ j, |v i| * (K : ℝ) * |v j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hentry i j
    _ = (K : ℝ) * (∑ i, |v i|) ^ 2 := by
      calc
        _ = ∑ i, ∑ j, (K : ℝ) * (|v i| * |v j|) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (K : ℝ) * (∑ i, ∑ j, |v i| * |v j|) := by
          simp_rw [show ∀ i, ∑ j, (K : ℝ) * (|v i| * |v j|) =
            (K : ℝ) * ∑ j, |v i| * |v j| from fun i => by rw [Finset.mul_sum]]
          rw [Finset.mul_sum]
        _ = (K : ℝ) * ((∑ i, |v i|) * (∑ j, |v j|)) := by
          congr 1
          rw [← Finset.sum_mul_sum]
        _ = _ := by rw [pow_two]

private theorem spd_sqrt_norm_bound_of_entry_bounds
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.PosDef) {K : ℝ≥0}
    (hAupper : ∀ i j, ‖A i j‖ ≤ K) :
    ‖(HeatEquation.spdSqrtEquiv A hA :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖ ≤
        Real.sqrt ((Fintype.card n : ℝ) * (Fintype.card n : ℝ) * (K : ℝ)) := by
  apply HeatEquation.spdSqrt_norm_le A hA (by positivity)
  intro x
  have h := quadratic_form_entry_bound_aux A (fun i => x i) K (by
    intro i j
    exact_mod_cast hAupper i j)
  have hsum : (∑ i, ‖x i‖ ^ 2) = ‖x‖ ^ 2 := by
    simpa [Real.norm_eq_abs, abs_sq] using
      (EuclideanSpace.real_norm_sq_eq x).symm
  have hcoord : ∀ i, |x i| ≤ ‖x‖ := by
    intro i
    have hterm : ‖x i‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j => ‖x j‖ ^ 2)
        (fun j hj => sq_nonneg (‖x j‖)) (Finset.mem_univ i)
    have hterm' : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
      calc
        |x i| ^ 2 = ‖x i‖ ^ 2 := by simp [Real.norm_eq_abs]
        _ ≤ ∑ j, ‖x j‖ ^ 2 := hterm
        _ = ‖x‖ ^ 2 := hsum
    nlinarith [sq_nonneg (|x i| - ‖x‖), abs_nonneg (x i), norm_nonneg x]
  have habsSum : ∑ i, |x i| ≤ (Fintype.card n : ℝ) * ‖x‖ := by
    calc
      _ ≤ ∑ _i : n, ‖x‖ := Finset.sum_le_sum (fun i hi => hcoord i)
      _ = (Fintype.card n : ℝ) * ‖x‖ := by simp
  have hsumNonneg : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun i hi => abs_nonneg _
  have hsumSq : (∑ i, |x i|) ^ 2 ≤ ((Fintype.card n : ℝ) * ‖x‖) ^ 2 :=
    (sq_le_sq₀ hsumNonneg (by positivity)).2 habsSum
  have hbound : dotProduct (star (fun i => x i))
      (Matrix.mulVec A (fun i => x i)) ≤
      ((Fintype.card n : ℝ) ^ 2 * (K : ℝ)) * ‖x‖ ^ 2 := by
    calc
      _ ≤ (K : ℝ) * (∑ i, |x i|) ^ 2 := h
      _ ≤ (K : ℝ) * ((Fintype.card n : ℝ) * ‖x‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsumSq (by positivity)
      _ = _ := by ring
  simpa [Matrix.inner_toEuclideanCLM, star_trivial, pow_two] using hbound

private theorem spd_sqrt_inv_bound_of_ellipticity
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.PosDef)
    {lam : ℝ≥0} (hlam : 0 < lam)
    (hEll : ∀ v : n → ℝ,
      (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤
        dotProduct (star v) (Matrix.mulVec A v)) :
    ‖((HeatEquation.spdSqrtEquiv A hA).symm :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖ ≤
        (Real.sqrt (lam : ℝ))⁻¹ := by
  apply HeatEquation.spdSqrt_inv_le A hA (by exact_mod_cast hlam)
  intro x
  have h := hEll (fun i => x i)
  have hsum : (∑ i, ‖x i‖ ^ 2) = ‖x‖ ^ 2 := by
    simpa [Real.norm_eq_abs, abs_sq] using
      (EuclideanSpace.real_norm_sq_eq x).symm
  rw [hsum] at h
  simpa [Matrix.inner_toEuclideanCLM, star_trivial] using h

private theorem heatDuhamelConstSchauderConst_mono_inputs
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    (alpha : ℝ≥0) (halpha1 : alpha < 1)
    (K₁ K₂ B₁ B₂ : ℝ≥0) (hK : K₁ ≤ K₂) (hB : B₁ ≤ B₂) :
    HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha K₁ B₁ 1 ≤
      HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha K₂ B₂ 1 := by
  calc
    _ ≤ HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha K₁ B₁ 1 +
        HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha (K₂ - K₁) (B₂ - B₁) 1 :=
      le_add_of_nonneg_right (by positivity)
    _ = HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha
        (K₁ + (K₂ - K₁)) (B₁ + (B₂ - B₁)) 1 := by
      symm
      exact HeatEquation.heatDuhamelConstSchauderConst_add halpha1 K₁ (K₂ - K₁)
        B₁ (B₂ - B₁) (by norm_num)
    _ = HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha K₂ B₂ 1 := by
      have hk : K₁ + (K₂ - K₁) = K₂ := by
        simpa [add_comm] using tsub_add_cancel_of_le hK
      have hb : B₁ + (B₂ - B₁) = B₂ := by
        simpa [add_comm] using tsub_add_cancel_of_le hB
      rw [hk, hb]

private theorem contDiffHolderLinearEquivConst_le_of_inv_norm_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V ≃L[ℝ] V) (alpha S C : ℝ≥0)
    (hS : ‖(L.symm : V →L[ℝ] V)‖₊ ≤ S) :
    contDiffHolderLinearEquivConst L alpha C ≤
      (1 + max 1 S + (max 1 S) ^ 2 + (max 1 S) ^ 2 *
        (max 1 S) ^ (alpha : ℝ)) * C := by
  unfold contDiffHolderLinearEquivConst
  let R : ℝ≥0 := max 1 ‖(L.symm : V →L[ℝ] V)‖₊
  let Rb : ℝ≥0 := max 1 S
  have hR : R ≤ Rb := max_le_max le_rfl hS
  have hRpow : R ^ (alpha : ℝ) ≤ Rb ^ (alpha : ℝ) :=
    NNReal.rpow_le_rpow hR alpha.property
  have hR2 : R ^ 2 ≤ Rb ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul hR hR (by positivity) (by positivity)
  calc
    _ = C + R * C + R ^ 2 * C + R ^ 2 * (C * R ^ (alpha : ℝ)) := by simp only [R]
    _ ≤ C + Rb * C + Rb ^ 2 * C + Rb ^ 2 * (C * Rb ^ (alpha : ℝ)) := by
      apply add_le_add (add_le_add (add_le_add le_rfl ?_) ?_) ?_
      · exact mul_le_mul_of_nonneg_right hR C.property
      · exact mul_le_mul_of_nonneg_right hR2 C.property
      · calc
          R ^ 2 * (C * R ^ (alpha : ℝ)) ≤ Rb ^ 2 * (C * R ^ (alpha : ℝ)) :=
            mul_le_mul_of_nonneg_right hR2 (by positivity)
          _ ≤ Rb ^ 2 * (C * Rb ^ (alpha : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRpow C.property)
              (by positivity)
    _ = (1 + Rb + Rb ^ 2 + Rb ^ 2 * Rb ^ (alpha : ℝ)) * C := by ring

private theorem contDiffHolderLinearEquivConst_mono
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V ≃L[ℝ] V) (alpha C₁ C₂ : ℝ≥0) (hC : C₁ ≤ C₂) :
    contDiffHolderLinearEquivConst L alpha C₁ ≤ contDiffHolderLinearEquivConst L alpha C₂ := by
  simp only [contDiffHolderLinearEquivConst]
  gcongr

private theorem spdLaplacianSchauderDefectConst_mono_inputs
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.PosDef) (alpha K₁ K₂ B₁ B₂ : ℝ≥0)
    (halpha1 : alpha < 1) (hK : K₁ ≤ K₂) (hB : B₁ ≤ B₂) :
    spdLaplacianSchauderDefectConst A hA alpha K₁ B₁ ≤
      spdLaplacianSchauderDefectConst A hA alpha K₂ B₂ := by
  let L := HeatEquation.spdSqrtEquiv A hA
  let q := ‖(L : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖₊ ^ (alpha : ℝ)
  change contDiffHolderLinearEquivConst L alpha
      (HeatEquation.heatDuhamelConstSchauderConst (V := EuclideanSpace ℝ n)
        alpha (K₁ * q) B₁ 1) ≤
    contDiffHolderLinearEquivConst L alpha
      (HeatEquation.heatDuhamelConstSchauderConst (V := EuclideanSpace ℝ n)
        alpha (K₂ * q) B₂ 1)
  apply contDiffHolderLinearEquivConst_mono
  apply heatDuhamelConstSchauderConst_mono_inputs (V := EuclideanSpace ℝ n)
    alpha halpha1
  · exact mul_le_mul_of_nonneg_right hK q.property
  · exact hB

private theorem exists_uniform_spd_laplacian_defect_envelope
    {n : ℕ} (hn : 0 < n)
    {alpha lam KA : ℝ≥0}
    (_halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hlam : 0 < lam) :
    ∃ C : ℝ≥0,
      ∀ (A₀ : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
        (hA₀ : A₀.PosDef),
        (∀ i j, ‖A₀ i j‖ ≤ (KA : ℝ)) →
        (∀ v : Fin n × Fin 2 → ℝ,
          (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤
            dotProduct (star v) (Matrix.mulVec A₀ v)) →
        spdLaplacianSchauderDefectConst A₀ hA₀ alpha
          (3 * (Fintype.card (Fin n × Fin 2) : ℝ≥0) ^ 2 * KA)
          (2 * (Fintype.card (Fin n × Fin 2) : ℝ≥0) ^ 2 * KA) ≤ C := by
  let I := Fin n × Fin 2
  let H₀ : ℝ≥0 := 3 * (Fintype.card I : ℝ≥0) ^ 2 * KA
  let B₀ : ℝ≥0 := 2 * (Fintype.card I : ℝ≥0) ^ 2 * KA
  let T : ℝ≥0 := Real.toNNReal
    (Real.sqrt ((Fintype.card I : ℝ) * (Fintype.card I : ℝ) * (KA : ℝ)))
  let Q : ℝ≥0 := T ^ (alpha : ℝ)
  let S : ℝ≥0 := Real.toNNReal ((Real.sqrt (lam : ℝ))⁻¹)
  let R : ℝ≥0 := max 1 S
  let Cunit : ℝ≥0 := HeatEquation.heatDuhamelConstSchauderConst
    (V := EuclideanSpace ℝ I) alpha (H₀ * Q) B₀ 1
  let C : ℝ≥0 := (1 + R + R ^ 2 + R ^ 2 * R ^ (alpha : ℝ)) * Cunit
  refine ⟨C, ?_⟩
  intro A₀ hA₀ hA₀upper hEll
  let : Nonempty I := by
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    exact ⟨(Classical.choice ‹Nonempty (Fin n)›, 0)⟩
  let L := HeatEquation.spdSqrtEquiv A₀ hA₀
  have hLnorm : ‖(L : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖₊ ≤ T := by
    apply NNReal.coe_le_coe.mp
    have hL := spd_sqrt_norm_bound_of_entry_bounds A₀ hA₀ hA₀upper
    simpa only [L, T, coe_nnnorm,
      Real.coe_toNNReal _ (Real.sqrt_nonneg _)] using hL
  have hq : ‖(L : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖₊ ^ (alpha : ℝ) ≤ Q := by
    simpa [Q] using NNReal.rpow_le_rpow hLnorm alpha.property
  have hEll' : ∀ v : I → ℝ,
      (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ dotProduct (star v) (Matrix.mulVec A₀ v) := by
    intro v
    simpa [Real.norm_eq_abs, abs_sq, star_trivial] using hEll v
  have hLinInv : ‖(L.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖₊ ≤ S := by
    apply NNReal.coe_le_coe.mp
    have hLin := spd_sqrt_inv_bound_of_ellipticity A₀ hA₀ hlam hEll'
    simpa only [L, S, coe_nnnorm,
      Real.coe_toNNReal _ (inv_nonneg.mpr (Real.sqrt_nonneg _))] using hLin
  have hDuhamel : HeatEquation.heatDuhamelConstSchauderConst
      (V := EuclideanSpace ℝ I) alpha
        (H₀ * ‖(L : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖₊ ^ (alpha : ℝ)) B₀ 1 ≤ Cunit := by
    apply heatDuhamelConstSchauderConst_mono_inputs
      (V := EuclideanSpace ℝ I) alpha halpha1
    · exact mul_le_mul_of_nonneg_left hq H₀.property
    · exact le_rfl
  change contDiffHolderLinearEquivConst L alpha
      (HeatEquation.heatDuhamelConstSchauderConst
        (V := EuclideanSpace ℝ I) alpha
        (H₀ * ‖(L : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖₊ ^ (alpha : ℝ)) B₀ 1) ≤ C
  calc
    _ ≤ contDiffHolderLinearEquivConst L alpha Cunit :=
      contDiffHolderLinearEquivConst_mono L alpha _ _ hDuhamel
    _ ≤ C := by
      simpa [C, R] using
        contDiffHolderLinearEquivConst_le_of_inv_norm_bound L alpha S Cunit hLinInv

private theorem exists_nnreal_rpow_smallness
    {alpha C gap : ℝ≥0} (halpha : 0 < alpha) (hgap : 0 < gap) :
    ∃ r : ℝ≥0, 0 < r ∧ r ≤ gap ∧ r ^ (alpha : ℝ) * C ≤ 1 / 8 := by
  let f : ℝ≥0 → ℝ≥0 := fun t ↦ t ^ (alpha : ℝ) * C
  have hf : Continuous f :=
    (NNReal.continuous_rpow_const alpha.property).mul continuous_const
  have halphaReal : (alpha : ℝ) ≠ 0 := by exact_mod_cast halpha.ne'
  have hzero : f 0 ∈ Set.Iio (1 / 8 : ℝ≥0) := by
    change f 0 < 1 / 8
    simp [f, halphaReal]
  have hpre : f ⁻¹' Set.Iio (1 / 8 : ℝ≥0) ∈ 𝓝 (0 : ℝ≥0) :=
    hf.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hzero)
  obtain ⟨eta, heta, hetaBall⟩ := Metric.mem_nhds_iff.mp hpre
  let etaNN : ℝ≥0 := Real.toNNReal eta
  have hetaNN : 0 < etaNN := Real.toNNReal_pos.mpr heta
  let r : ℝ≥0 := min (gap / 2) (etaNN / 2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by positivity) (by positivity)
  have hrGap : r ≤ gap := by
    dsimp [r]
    exact (min_le_left _ _).trans (div_le_self (by positivity) (by norm_num))
  have hrEtaNN : r < etaNN := by
    calc
      r ≤ etaNN / 2 := min_le_right _ _
      _ < etaNN := div_lt_self hetaNN (by norm_num)
  have hetaNNcoe : (etaNN : ℝ) = eta := Real.coe_toNNReal eta heta.le
  have hrEta : (r : ℝ) < eta := by
    rw [← hetaNNcoe]
    exact_mod_cast hrEtaNN
  have hrmem : r ∈ Metric.ball (0 : ℝ≥0) eta := by
    rw [Metric.mem_ball]
    simpa [NNReal.dist_eq, abs_of_nonneg r.coe_nonneg] using hrEta
  have hsmall : f r < 1 / 8 := hetaBall hrmem
  exact ⟨r, hr, hrGap, le_of_lt (by simpa [f] using hsmall)⟩

private theorem hessianInterpolationFunctionConst_mul
    (epsilon c M : ℝ≥0) :
    hessianInterpolationFunctionConst epsilon (c * M) =
      c * hessianInterpolationFunctionConst epsilon M := by
  simp [hessianInterpolationFunctionConst, div_eq_mul_inv, mul_assoc, mul_comm]

private theorem source_interpolation_holder_linear_bound
    {n : Type*} [Fintype n] [DecidableEq n]
    (epsilon M KR K₀ K₁ : ℝ≥0) (hM : M ≤ K₀) :
    matrixFreezeInterpolationSourceHolderConst epsilon M K₁
        (fun _ _ : n ↦ KR) ≤
      (1 + (Fintype.card n : ℝ≥0) ^ 2 *
        hessianInterpolationFunctionConst epsilon 1 * KR) * (K₀ + K₁) := by
  let D : ℝ≥0 := (Fintype.card n : ℝ≥0) ^ 2 *
    hessianInterpolationFunctionConst epsilon 1 * KR
  have hH : hessianInterpolationFunctionConst epsilon M =
      M * hessianInterpolationFunctionConst epsilon 1 := by
    rw [show M = M * 1 by simp, hessianInterpolationFunctionConst_mul]
    ring
  have hsource : matrixFreezeInterpolationSourceHolderConst epsilon M K₁
      (fun _ _ : n ↦ KR) = K₁ + M * D := by
    simp [matrixFreezeInterpolationSourceHolderConst, D, hH,
      Finset.sum_const, Finset.card_univ]
    ring
  rw [hsource]
  calc
    K₁ + M * ((Fintype.card n : ℝ≥0) ^ 2 *
        hessianInterpolationFunctionConst epsilon 1 * KR) ≤
      K₁ + K₀ * ((Fintype.card n : ℝ≥0) ^ 2 *
        hessianInterpolationFunctionConst epsilon 1 * KR) := by
      gcongr
    _ ≤ (1 + (Fintype.card n : ℝ≥0) ^ 2 *
        hessianInterpolationFunctionConst epsilon 1 * KR) * (K₀ + K₁) := by
      calc
        K₁ + K₀ * ((Fintype.card n : ℝ≥0) ^ 2 *
            hessianInterpolationFunctionConst epsilon 1 * KR) ≤
          K₁ + K₀ * ((Fintype.card n : ℝ≥0) ^ 2 *
            hessianInterpolationFunctionConst epsilon 1 * KR) +
              (K₀ + ((Fintype.card n : ℝ≥0) ^ 2 *
                hessianInterpolationFunctionConst epsilon 1 * KR) * K₁) :=
          le_add_of_nonneg_right (by positivity)
        _ = (1 + (Fintype.card n : ℝ≥0) ^ 2 *
            hessianInterpolationFunctionConst epsilon 1 * KR) * (K₀ + K₁) := by ring

private theorem heatSupSchauderConst_mono_norm
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (u w : BoundedContinuousFunction V F) (h : ‖u‖ ≤ ‖w‖) :
    HeatEquation.heatSupSchauderConst (V := V) 1 u ≤
      HeatEquation.heatSupSchauderConst (V := V) 1 w := by
  unfold HeatEquation.heatSupSchauderConst HeatEquation.heatSupSpatialJetConst
    HeatEquation.heatSupHessianHolderConst HeatEquation.heatD2SupHolderConst
  gcongr
  all_goals try exact mul_nonneg (by positivity) (HeatEquation.heatC2_nonneg (V := V))
  all_goals try exact HeatEquation.heatC3_nonneg (V := V)
  all_goals try exact inv_nonneg.mpr (HeatEquation.heatScale_pos (by norm_num)).le
  case h =>
    have hj3 : j < 3 := by
      have hj : j ∈ Finset.range 3 := by assumption
      simpa using hj
    interval_cases j
    · simpa
    · apply Real.toNNReal_mono
      gcongr
      exact mul_nonneg
        (inv_nonneg.mpr (HeatEquation.heatScale_pos (by norm_num)).le)
        (HeatEquation.heatC1_nonneg (V := V))
    · apply Real.toNNReal_mono
      gcongr
      exact mul_nonneg (by norm_num) (HeatEquation.heatC2_nonneg (V := V))

private theorem spatialJetConst_nnreal_smul
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (c : ℝ≥0) (u : BoundedContinuousFunction V F) (j : Nat) :
    HeatEquation.heatSupSpatialJetConst (V := V) 1 ((c : ℝ) • u) j =
      c * HeatEquation.heatSupSpatialJetConst (V := V) 1 u j := by
  cases j with
  | zero =>
      change ‖(c : ℝ) • u‖₊ = c * ‖u‖₊
      rw [nnnorm_smul]
      have hc : ‖(c : ℝ)‖₊ = c := by simp
      rw [hc]
  | succ j =>
      cases j with
      | zero =>
          change Real.toNNReal ((HeatEquation.heatScale 1)⁻¹ *
            HeatEquation.heatC1 V * ‖(c : ℝ) • u‖) =
              c * Real.toNNReal ((HeatEquation.heatScale 1)⁻¹ *
                HeatEquation.heatC1 V * ‖u‖)
          rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ (c : ℝ) by exact_mod_cast c.property)]
          rw [show (HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC1 V *
              ((c : ℝ) * ‖u‖) = (c : ℝ) *
                ((HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC1 V * ‖u‖) by ring]
          calc
            Real.toNNReal ((c : ℝ) *
                ((HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC1 V * ‖u‖)) =
              Real.toNNReal (c : ℝ) * Real.toNNReal
                ((HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC1 V * ‖u‖) :=
                Real.toNNReal_mul c.coe_nonneg
            _ = c * Real.toNNReal
                ((HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC1 V * ‖u‖) := by simp
      | succ j =>
          change Real.toNNReal ((1 : ℝ)⁻¹ * HeatEquation.heatC2 V *
            ‖(c : ℝ) • u‖) =
              c * Real.toNNReal ((1 : ℝ)⁻¹ * HeatEquation.heatC2 V * ‖u‖)
          rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ (c : ℝ) by exact_mod_cast c.property)]
          rw [show (1 : ℝ)⁻¹ * HeatEquation.heatC2 V *
              ((c : ℝ) * ‖u‖) = (c : ℝ) *
                ((1 : ℝ)⁻¹ * HeatEquation.heatC2 V * ‖u‖) by ring]
          calc
            Real.toNNReal ((c : ℝ) *
                ((1 : ℝ)⁻¹ * HeatEquation.heatC2 V * ‖u‖)) =
              Real.toNNReal (c : ℝ) * Real.toNNReal
                ((1 : ℝ)⁻¹ * HeatEquation.heatC2 V * ‖u‖) :=
                Real.toNNReal_mul c.coe_nonneg
            _ = c * Real.toNNReal
                ((1 : ℝ)⁻¹ * HeatEquation.heatC2 V * ‖u‖) := by simp

private theorem heatSupSchauderConst_nnreal_smul
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (c : ℝ≥0) (u : BoundedContinuousFunction V F) :
    HeatEquation.heatSupSchauderConst (V := V) 1 ((c : ℝ) • u) =
      c * HeatEquation.heatSupSchauderConst (V := V) 1 u := by
  have hnorm : ‖(c : ℝ) • u‖ = (c : ℝ) * ‖u‖ := by
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ (c : ℝ) by exact_mod_cast c.property)]
  have hjet := spatialJetConst_nnreal_smul c u
  have hd2 : HeatEquation.heatD2SupHolderConst (V := V) 1 ((c : ℝ) • u) =
      c * HeatEquation.heatD2SupHolderConst (V := V) 1 u := by
    unfold HeatEquation.heatD2SupHolderConst
    have h₁ : 2 * Real.toNNReal (1⁻¹ * HeatEquation.heatC2 V *
          ‖(c : ℝ) • u‖) = c *
        (2 * Real.toNNReal (1⁻¹ * HeatEquation.heatC2 V * ‖u‖)) := by
      rw [hnorm]
      rw [show 1⁻¹ * HeatEquation.heatC2 V * ((c : ℝ) * ‖u‖) =
          (c : ℝ) * (1⁻¹ * HeatEquation.heatC2 V * ‖u‖) by ring]
      calc
        2 * Real.toNNReal ((c : ℝ) * (1⁻¹ * HeatEquation.heatC2 V * ‖u‖)) =
            2 * (Real.toNNReal (c : ℝ) *
              Real.toNNReal (1⁻¹ * HeatEquation.heatC2 V * ‖u‖)) := by
          rw [Real.toNNReal_mul c.coe_nonneg]
        _ = c * (2 * Real.toNNReal (1⁻¹ * HeatEquation.heatC2 V * ‖u‖)) := by simp; ring
    have h₂ : Real.toNNReal (‖(c : ℝ) • u‖ * 1⁻¹ *
          (HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC3 V) = c *
        Real.toNNReal (‖u‖ * 1⁻¹ *
          (HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC3 V) := by
      rw [hnorm]
      rw [show ((c : ℝ) * ‖u‖) * 1⁻¹ * (HeatEquation.heatScale 1)⁻¹ *
          HeatEquation.heatC3 V = (c : ℝ) *
            (‖u‖ * 1⁻¹ * (HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC3 V) by ring]
      calc
        Real.toNNReal ((c : ℝ) *
            (‖u‖ * 1⁻¹ * (HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC3 V)) =
            Real.toNNReal (c : ℝ) *
              Real.toNNReal (‖u‖ * 1⁻¹ * (HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC3 V) :=
          Real.toNNReal_mul c.coe_nonneg
        _ = c * Real.toNNReal (‖u‖ * 1⁻¹ *
            (HeatEquation.heatScale 1)⁻¹ * HeatEquation.heatC3 V) := by simp
    rw [h₁, h₂, max_mul_mul_left]
  unfold HeatEquation.heatSupSchauderConst HeatEquation.heatSupHessianHolderConst
  simp_rw [hjet, hd2]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]

private theorem heatSupSchauderConst_le_norm_mul
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    (u : BoundedContinuousFunction V ℝ) :
    HeatEquation.heatSupSchauderConst (V := V) 1 u ≤
      ‖u‖₊ * HeatEquation.heatSupSchauderConst (V := V) 1
        (BoundedContinuousFunction.const V (1 : ℝ)) := by
  let w : BoundedContinuousFunction V ℝ :=
    BoundedContinuousFunction.const V (‖u‖ : ℝ)
  have hwNorm : ‖w‖ = ‖u‖ := by simp [w, BoundedContinuousFunction.norm_const_eq]
  have hw : ‖u‖ ≤ ‖w‖ := by rw [hwNorm]
  have hconst : w = (‖u‖₊ : ℝ) • BoundedContinuousFunction.const V (1 : ℝ) := by
    ext x
    simp [w, BoundedContinuousFunction.const_apply]
  calc
    HeatEquation.heatSupSchauderConst (V := V) 1 u ≤
        HeatEquation.heatSupSchauderConst (V := V) 1 w :=
      heatSupSchauderConst_mono_norm u w hw
    _ = ‖u‖₊ * HeatEquation.heatSupSchauderConst (V := V) 1
        (BoundedContinuousFunction.const V (1 : ℝ)) := by
      rw [hconst, heatSupSchauderConst_nnreal_smul]

private theorem heatDuhamelConstSchauderConst_linear_envelope
    {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (alpha : ℝ≥0) (halpha1 : alpha < 1)
    (c U Q source q : ℝ≥0) (hsource : source ≤ U * c) (hq : q ≤ Q) :
    HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha (q * source) source 1 ≤
      c * HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha (Q * U) U 1 := by
  have hK : q * source ≤ (Q * U) * c := by
    calc
      q * source ≤ Q * source := mul_le_mul_of_nonneg_right hq (by positivity)
      _ ≤ Q * (U * c) := mul_le_mul_of_nonneg_left hsource (by positivity)
      _ = (Q * U) * c := by ring
  calc
    HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha (q * source) source 1 ≤
      HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha ((Q * U) * c) (U * c) 1 :=
        heatDuhamelConstSchauderConst_mono_inputs (V := V) alpha halpha1
          (q * source) ((Q * U) * c) source (U * c) hK hsource
    _ = c * HeatEquation.heatDuhamelConstSchauderConst (V := V) alpha (Q * U) U 1 := by
      rw [show (Q * U) * c = c * (Q * U) by ring,
        show U * c = c * U by ring]
      exact HeatEquation.heatDuhamelConstSchauderConst_nnreal_mul
        (V := V) alpha c (Q * U) U 1

private theorem contDiffHolderLinearEquivConst_mul
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V ≃L[ℝ] V) (alpha c C : ℝ≥0) :
    contDiffHolderLinearEquivConst L alpha (c * C) =
      c * contDiffHolderLinearEquivConst L alpha C := by
  unfold contDiffHolderLinearEquivConst
  ring

private theorem spdLaplacianSchauderConst_mono_inputs
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (hA : A.PosDef) (alpha : ℝ≥0)
    (K₁ K₂ B₁ B₂ : ℝ≥0) (halpha1 : alpha < 1)
    (u : BoundedContinuousFunction (EuclideanSpace ℝ n) ℝ)
    (hK : K₁ ≤ K₂) (hB : B₁ ≤ B₂) :
    spdLaplacianSchauderConst A hA alpha K₁ B₁ u ≤
      spdLaplacianSchauderConst A hA alpha K₂ B₂ u := by
  let L := HeatEquation.spdSqrtEquiv A hA
  let q := ‖(L : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)‖₊ ^ (alpha : ℝ)
  change contDiffHolderLinearEquivConst L alpha
      (laplacianSchauderConst alpha (K₁ * q) B₁
        (HeatEquation.linPullBoundedContinuousFunction L u)) ≤
    contDiffHolderLinearEquivConst L alpha
      (laplacianSchauderConst alpha (K₂ * q) B₂
        (HeatEquation.linPullBoundedContinuousFunction L u))
  apply contDiffHolderLinearEquivConst_mono
  unfold laplacianSchauderConst
  apply add_le_add le_rfl
  apply heatDuhamelConstSchauderConst_mono_inputs
    (V := EuclideanSpace ℝ n) alpha halpha1
  · exact mul_le_mul_of_nonneg_right hK (by positivity)
  · exact hB

private theorem frozen_defect_absorbs
    {n : ℕ} (hn : 0 < n) {alpha lam K r : ℝ≥0}
    (_halpha0 : 0 < alpha) (halpha1 : alpha < 1) (_hlam : 0 < lam)
    (hr : 0 < r) (hrle : r ≤ 1)
    {C : ℝ≥0} (hsmall : r ^ (alpha : ℝ) * C ≤ 1 / 8)
    (hC : ∀ (B : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ)
      (hB : B.PosDef),
      (∀ i j, ‖B i j‖ ≤ (K : ℝ)) →
      (∀ v : Fin n × Fin 2 → ℝ,
        (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ dotProduct (star v) (Matrix.mulVec B v)) →
      spdLaplacianSchauderDefectConst B hB alpha
        (3 * (Fintype.card (Fin n × Fin 2) : ℝ≥0) ^ 2 * K)
        (2 * (Fintype.card (Fin n × Fin 2) : ℝ≥0) ^ 2 * K) ≤ C) :
    ∀ (B : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hB : B.PosDef),
      (∀ v, (lam : ℝ) * ∑ i, v i ^ 2 ≤ dotProduct v (B.mulVec v)) →
      (∀ i j, ‖B i j‖ ≤ (K : ℝ)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ (r : ℝ) →
        spdLaplacianSchauderDefectConst B hB alpha
          (matrixFreezeInterpolationHolderConst (n := Fin n × Fin 2) r alpha
            (fun _ _ => K) (fun _ _ => K * Real.toNNReal δ ^ (alpha : ℝ)))
          (matrixFreezeInterpolationSupConst (n := Fin n × Fin 2) r alpha
            (fun _ _ => K * Real.toNNReal δ ^ (alpha : ℝ))) ≤ 1 / 8 := by
  intro B hB hEll hUpper δ hδpos hδle
  let : Nonempty (Fin n × Fin 2) := by
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    exact ⟨(Classical.choice ‹Nonempty (Fin n)›, 0)⟩
  let q : ℝ≥0 := Fintype.card (Fin n × Fin 2)
  let H₀ : ℝ≥0 := 3 * q ^ 2 * K
  let B₀ : ℝ≥0 := 2 * q ^ 2 * K
  let s : ℝ≥0 := r ^ (alpha : ℝ)
  have hδnn : Real.toNNReal δ ≤ r := by
    have hcast : Real.toNNReal δ ≤ Real.toNNReal (r : ℝ) :=
      (Real.toNNReal_le_toNNReal_iff (by positivity : 0 ≤ (r : ℝ))).2 hδle
    simpa using hcast
  have hδpow : Real.toNNReal δ ^ (alpha : ℝ) ≤ s :=
    NNReal.rpow_le_rpow hδnn alpha.property
  have hsle : s ≤ 1 := by
    dsimp [s]
    exact NNReal.rpow_le_one hrle alpha.property
  have hEll' : ∀ v : Fin n × Fin 2 → ℝ,
      (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ dotProduct (star v) (Matrix.mulVec B v) := by
    intro v
    simpa [Real.norm_eq_abs, abs_sq, star_trivial] using hEll v
  have hBase := hC B hB hUpper hEll'
  have hHolderEq :
      matrixFreezeInterpolationHolderConst (n := Fin n × Fin 2) r alpha
        (fun _ _ => K) (fun _ _ => K * Real.toNNReal δ ^ (alpha : ℝ)) =
      q ^ 2 * (K * Real.toNNReal δ ^ (alpha : ℝ) + 2 * s * K) := by
    simp [matrixFreezeInterpolationHolderConst, q, s, Finset.sum_const,
      Fintype.card_prod, nsmul_eq_mul]
    ring
  have hSupEq :
      matrixFreezeInterpolationSupConst (n := Fin n × Fin 2) r alpha
        (fun _ _ => K * Real.toNNReal δ ^ (alpha : ℝ)) =
      q ^ 2 * (2 * (K * Real.toNNReal δ ^ (alpha : ℝ)) * s) := by
    simp [matrixFreezeInterpolationSupConst, q, s, Finset.sum_const,
      Fintype.card_prod, nsmul_eq_mul]
    ring
  have hHolder :
      matrixFreezeInterpolationHolderConst (n := Fin n × Fin 2) r alpha
        (fun _ _ => K) (fun _ _ => K * Real.toNNReal δ ^ (alpha : ℝ)) ≤ s * H₀ := by
    rw [hHolderEq]
    dsimp [H₀]
    have hδK : K * Real.toNNReal δ ^ (alpha : ℝ) ≤ K * s :=
      mul_le_mul_of_nonneg_left hδpow K.property
    calc
      q ^ 2 * (K * Real.toNNReal δ ^ (alpha : ℝ) + 2 * s * K) ≤
          q ^ 2 * (K * s + 2 * s * K) :=
        mul_le_mul_of_nonneg_left (add_le_add hδK le_rfl) (by positivity)
      _ = s * (3 * q ^ 2 * K) := by ring
  have hSup :
      matrixFreezeInterpolationSupConst (n := Fin n × Fin 2) r alpha
        (fun _ _ => K * Real.toNNReal δ ^ (alpha : ℝ)) ≤ s * B₀ := by
    rw [hSupEq]
    dsimp [B₀]
    have hδK : K * Real.toNNReal δ ^ (alpha : ℝ) ≤ K * s :=
      mul_le_mul_of_nonneg_left hδpow K.property
    have hδKeps : K * Real.toNNReal δ ^ (alpha : ℝ) * s ≤ K * s := by
      calc
        K * Real.toNNReal δ ^ (alpha : ℝ) * s ≤ (K * s) * s :=
          mul_le_mul_of_nonneg_right hδK s.property
        _ ≤ (K * s) * 1 := mul_le_mul_of_nonneg_left hsle (by positivity)
        _ = K * s := by simp
    have hterm : 2 * (K * Real.toNNReal δ ^ (alpha : ℝ)) * s ≤ 2 * K * s := by
      calc
        _ = 2 * (K * Real.toNNReal δ ^ (alpha : ℝ) * s) := by ring
        _ ≤ 2 * (K * s) := mul_le_mul_of_nonneg_left hδKeps (by norm_num)
        _ = 2 * K * s := by ring
    calc
      q ^ 2 * (2 * (K * Real.toNNReal δ ^ (alpha : ℝ)) * s) ≤
          q ^ 2 * (2 * K * s) := mul_le_mul_of_nonneg_left hterm (by positivity)
      _ = s * (2 * q ^ 2 * K) := by ring
  calc
    _ ≤ spdLaplacianSchauderDefectConst B hB alpha (s * H₀) (s * B₀) :=
      spdLaplacianSchauderDefectConst_mono_inputs B hB alpha _ _ _ _ halpha1
        hHolder hSup
    _ = s * spdLaplacianSchauderDefectConst B hB alpha H₀ B₀ := by
      rw [spdLaplacianSchauderDefectConst_nnreal_mul]
    _ ≤ s * C := mul_le_mul_of_nonneg_left hBase s.property
    _ ≤ 1 / 8 := by simpa [s] using hsmall

set_option maxHeartbeats 1000000 in
/-- Choose one patch radius, interpolation scale and amplification factor before the frozen
matrix and the potential. The lower ellipticity and entry bound control the SPD square-root
change of variables. Shrinking only the patch radius does not remove the unweighted coefficient
Hölder constant, so the extracted Hessian interpolation scale is essential here.
The defect is strictly below one, making the absorption denominator positive.
The actual constants being controlled are defined in `RealBallFrozenParameters`. -/
theorem exists_realBallFrozenParameters :
    ∀ {n : ℕ}, 0 < n → ∀ (α lam K : ℝ≥0), 0 < α → α < 1 → 0 < lam →
  ∃ (d : ℝ) (ε M : ℝ≥0), 0 < d ∧ 0 < ε ∧ 1 ≤ M ∧
    RealBallFrozenParameters (n := n) α lam K d ε M := by
  intro n hn alpha lam K halpha0 halpha1 hlam
  let I := Fin n × Fin 2
  let : Nonempty I := by
    let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    exact ⟨(Classical.choice ‹Nonempty (Fin n)›, 0)⟩
  obtain ⟨C, hC⟩ := exists_uniform_spd_laplacian_defect_envelope
    (KA := K) hn halpha0 halpha1 hlam
  obtain ⟨r, hr, hrle, hsmall⟩ :=
    exists_nnreal_rpow_smallness (alpha := alpha) (C := C) (gap := 1)
      halpha0 (by norm_num)
  let qcard : ℝ≥0 := Fintype.card I
  let U : ℝ≥0 := 1 + qcard ^ 2 * hessianInterpolationFunctionConst r 1 * K
  let T : ℝ≥0 := Real.toNNReal
    (Real.sqrt ((Fintype.card I : ℝ) * (Fintype.card I : ℝ) * (K : ℝ)))
  let Q : ℝ≥0 := T ^ (alpha : ℝ)
  let S : ℝ≥0 := Real.toNNReal ((Real.sqrt (lam : ℝ))⁻¹)
  let R : ℝ≥0 := max 1 S
  let supOne : ℝ≥0 := HeatEquation.heatSupSchauderConst
    (V := EuclideanSpace ℝ I) 1 (BoundedContinuousFunction.const _ (1 : ℝ))
  let duhamelUnit : ℝ≥0 := HeatEquation.heatDuhamelConstSchauderConst
    (V := EuclideanSpace ℝ I) alpha (Q * U) U 1
  let Cunit : ℝ≥0 := supOne + duhamelUnit
  let Csrc : ℝ≥0 := (1 + R + R ^ 2 + R ^ 2 * R ^ (alpha : ℝ)) * Cunit
  let M : ℝ≥0 := max 1 (2 * Csrc)
  refine ⟨(r : ℝ), r, M, ?_, hr, le_max_left _ _, ?_⟩
  · exact_mod_cast hr
  · intro B hB hEll hUpper delta hdeltaPos hdeltaLe
    have hdef := frozen_defect_absorbs hn halpha0 halpha1 hlam hr hrle hsmall hC
      B hB hEll hUpper delta hdeltaPos hdeltaLe
    constructor
    · exact lt_of_le_of_lt hdef (by norm_num)
    · intro w Kf Bf
      let c : ℝ≥0 := Kf + Bf + ‖w‖₊
      let sourceHolder := matrixFreezeInterpolationSourceHolderConst r ‖w‖₊ Kf
        (fun _ _ : I ↦ K)
      let omega : I → I → ℝ≥0 := fun _ _ ↦ K * Real.toNNReal delta ^ (alpha : ℝ)
      let sourceSup := matrixFreezeInterpolationSourceSupConst r ‖w‖₊ Bf omega
      let defect : ℝ≥0 := spdLaplacianSchauderDefectConst B hB alpha
        (matrixFreezeInterpolationHolderConst (n := I) r alpha (fun _ _ => K) omega)
        (matrixFreezeInterpolationSupConst (n := I) r alpha omega)
      let numerator : ℝ≥0 := spdLaplacianSchauderConst B hB alpha sourceHolder sourceSup w
      change numerator / (1 - defect) ≤ M * c
      have hdeltaNN : Real.toNNReal delta ≤ r := by
        have hcast : Real.toNNReal delta ≤ Real.toNNReal (r : ℝ) :=
          (Real.toNNReal_le_toNNReal_iff (by positivity : 0 ≤ (r : ℝ))).2 hdeltaLe
        simpa using hcast
      have hdeltaPowOne : Real.toNNReal delta ^ (alpha : ℝ) ≤ 1 :=
        NNReal.rpow_le_one (hdeltaNN.trans hrle) alpha.property
      have homega : K * Real.toNNReal delta ^ (alpha : ℝ) ≤ K := by
        calc
          K * Real.toNNReal delta ^ (alpha : ℝ) ≤ K * 1 :=
            mul_le_mul_of_nonneg_left hdeltaPowOne K.property
          _ = K := by simp
      have hsourceHolder : sourceHolder ≤ U * c := by
        have h := source_interpolation_holder_linear_bound (n := I)
          r ‖w‖₊ K ‖w‖₊ Kf le_rfl
        have hsum : ‖w‖₊ + Kf ≤ c := by
          dsimp [c]
          calc
            ‖w‖₊ + Kf ≤ ‖w‖₊ + Kf + Bf := le_add_of_nonneg_right Bf.property
            _ = Kf + Bf + ‖w‖₊ := by ring
        calc
          sourceHolder ≤ U * (‖w‖₊ + Kf) := by simpa [sourceHolder, U, qcard] using h
          _ ≤ U * c := mul_le_mul_of_nonneg_left hsum U.property
      have hsourceSupMono : sourceSup ≤
          matrixFreezeInterpolationSourceSupConst r ‖w‖₊ Bf (fun _ _ : I ↦ K) := by
        unfold sourceSup matrixFreezeInterpolationSourceSupConst
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right homega (by positivity)
      have hsourceEq :
          matrixFreezeInterpolationSourceSupConst r ‖w‖₊ Bf (fun _ _ : I ↦ K) =
          matrixFreezeInterpolationSourceHolderConst r ‖w‖₊ Bf (fun _ _ : I ↦ K) := by
        simp [matrixFreezeInterpolationSourceSupConst,
          matrixFreezeInterpolationSourceHolderConst, mul_comm]
      have hsourceSup : sourceSup ≤ U * c := by
        calc
          sourceSup ≤ matrixFreezeInterpolationSourceSupConst r ‖w‖₊ Bf
              (fun _ _ : I ↦ K) := hsourceSupMono
          _ = matrixFreezeInterpolationSourceHolderConst r ‖w‖₊ Bf
              (fun _ _ : I ↦ K) := hsourceEq
          _ ≤ U * (‖w‖₊ + Bf) := by
            have h := source_interpolation_holder_linear_bound (n := I)
              r ‖w‖₊ K ‖w‖₊ Bf le_rfl
            simpa [U, qcard] using h
          _ ≤ U * c := by
            have hsum : ‖w‖₊ + Bf ≤ c := by
              dsimp [c]
              calc
                ‖w‖₊ + Bf ≤ ‖w‖₊ + Bf + Kf := le_add_of_nonneg_right Kf.property
                _ = Kf + Bf + ‖w‖₊ := by ring
            exact mul_le_mul_of_nonneg_left hsum U.property
      have hnumMono : numerator ≤
          spdLaplacianSchauderConst B hB alpha (U * c) (U * c) w := by
        exact spdLaplacianSchauderConst_mono_inputs B hB alpha
          sourceHolder (U * c) sourceSup (U * c) halpha1 w
          hsourceHolder hsourceSup
      let L := HeatEquation.spdSqrtEquiv B hB
      let qL : ℝ≥0 := ‖(L : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖₊ ^ (alpha : ℝ)
      have hLnorm : ‖(L : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖₊ ≤ T := by
        apply NNReal.coe_le_coe.mp
        have hL := spd_sqrt_norm_bound_of_entry_bounds B hB hUpper
        simpa only [L, T, coe_nnnorm,
          Real.coe_toNNReal _ (Real.sqrt_nonneg _)] using hL
      have hqL : qL ≤ Q := by
        simpa [qL, Q] using NNReal.rpow_le_rpow hLnorm alpha.property
      have hEll' : ∀ v : I → ℝ,
          (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ dotProduct (star v) (Matrix.mulVec B v) := by
        intro v
        simpa [Real.norm_eq_abs, abs_sq, star_trivial] using hEll v
      have hLinInv : ‖(L.symm : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ I)‖₊ ≤ S := by
        apply NNReal.coe_le_coe.mp
        have hLin := spd_sqrt_inv_bound_of_ellipticity B hB hlam hEll'
        simpa only [L, S, coe_nnnorm,
          Real.coe_toNNReal _ (inv_nonneg.mpr (Real.sqrt_nonneg _))] using hLin
      let pullw : BoundedContinuousFunction (EuclideanSpace ℝ I) ℝ :=
        HeatEquation.linPullBoundedContinuousFunction L w
      have hpullNorm : ‖pullw‖₊ = ‖w‖₊ := by
        apply NNReal.coe_inj.mp
        simpa only [coe_nnnorm] using HeatEquation.norm_linPullBoundedContinuousFunction L w
      have hnormw : ‖w‖₊ ≤ c := by
        dsimp [c]
        exact le_add_of_nonneg_left (by positivity)
      have hheat : HeatEquation.heatSupSchauderConst (V := EuclideanSpace ℝ I) 1 pullw ≤
          c * supOne := by
        calc
          HeatEquation.heatSupSchauderConst (V := EuclideanSpace ℝ I) 1 pullw ≤
              ‖pullw‖₊ * supOne := heatSupSchauderConst_le_norm_mul pullw
          _ ≤ c * supOne := by
            rw [hpullNorm]
            exact mul_le_mul_of_nonneg_right hnormw (by positivity)
      have hduh := heatDuhamelConstSchauderConst_linear_envelope
        (V := EuclideanSpace ℝ I) (F := ℝ) alpha halpha1 c U Q (U * c) qL
        (by rfl) hqL
      have hduh' : HeatEquation.heatDuhamelConstSchauderConst
          (V := EuclideanSpace ℝ I) alpha ((U * c) * qL) (U * c) 1 ≤
          c * duhamelUnit := by
        simpa [duhamelUnit, mul_comm] using hduh
      have hbase : laplacianSchauderConst alpha ((U * c) * qL) (U * c) pullw ≤ c * Cunit := by
        unfold laplacianSchauderConst
        calc
          HeatEquation.heatSupSchauderConst (V := EuclideanSpace ℝ I) 1 pullw +
              HeatEquation.heatDuhamelConstSchauderConst (V := EuclideanSpace ℝ I)
                alpha ((U * c) * qL) (U * c) 1 ≤ c * supOne + c * duhamelUnit :=
            add_le_add hheat hduh'
          _ = c * Cunit := by simp [Cunit]; rw [← mul_add]
      have hCL : contDiffHolderLinearEquivConst L alpha Cunit ≤ Csrc := by
        simpa [Csrc, R] using
          contDiffHolderLinearEquivConst_le_of_inv_norm_bound L alpha S Cunit hLinInv
      have hcommon : spdLaplacianSchauderConst B hB alpha (U * c) (U * c) w ≤
          Csrc * c := by
        change contDiffHolderLinearEquivConst L alpha
            (laplacianSchauderConst alpha ((U * c) * qL) (U * c) pullw) ≤ Csrc * c
        calc
          _ ≤ contDiffHolderLinearEquivConst L alpha (c * Cunit) :=
            contDiffHolderLinearEquivConst_mono L alpha _ _ hbase
          _ = c * contDiffHolderLinearEquivConst L alpha Cunit :=
            contDiffHolderLinearEquivConst_mul L alpha c Cunit
          _ ≤ c * Csrc := mul_le_mul_of_nonneg_left hCL c.property
          _ = Csrc * c := by ring
      have hnum : numerator ≤ Csrc * c := hnumMono.trans hcommon
      have hdef' : defect ≤ 1 / 8 := by simpa [defect, omega] using hdef
      have hfracTop : (1 / 8 : ℝ≥0) ≤ 1 := by
        exact_mod_cast (by norm_num : (1 / 8 : ℝ) ≤ 1)
      have hhalf : (1 / 8 : ℝ≥0) ≤ 1 / 2 := by
        exact_mod_cast (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)
      have hhalfAdd : (1 / 2 : ℝ≥0) + 1 / 2 = 1 := by
        apply NNReal.coe_inj.mp
        norm_num
      have hden : (1 / 2 : ℝ≥0) ≤ 1 - defect := by
        apply (le_tsub_iff_right (le_trans hdef' hfracTop)).2
        have hsum : (1 / 2 : ℝ≥0) + 1 / 8 ≤ 1 := by
          calc
            1 / 2 + 1 / 8 ≤ 1 / 2 + 1 / 2 := add_le_add le_rfl hhalf
            _ = 1 := hhalfAdd
        calc
          1 / 2 + defect ≤ 1 / 2 + 1 / 8 := add_le_add le_rfl hdef'
          _ ≤ 1 := hsum
      have hdenPos : 0 < 1 - defect := lt_of_lt_of_le (by norm_num) hden
      have hfactor : numerator / (1 - defect) ≤ 2 * numerator := by
        apply (div_le_iff₀ hdenPos).2
        have hmul : (1 : ℝ≥0) ≤ 2 * (1 - defect) := by
          calc
            1 = 2 * (1 / 2 : ℝ≥0) := by norm_num
            _ ≤ 2 * (1 - defect) := mul_le_mul_of_nonneg_left hden (by norm_num)
        calc
          numerator = 1 * numerator := by simp
          _ ≤ (2 * (1 - defect)) * numerator :=
            mul_le_mul_of_nonneg_right hmul (by positivity)
          _ = (2 * numerator) * (1 - defect) := by ring
      calc
        numerator / (1 - defect) ≤ 2 * numerator := hfactor
        _ ≤ 2 * (Csrc * c) := mul_le_mul_of_nonneg_left hnum (by norm_num)
        _ = (2 * Csrc) * c := by ring
        _ ≤ M * c := mul_le_mul_of_nonneg_right (le_max_right _ _) c.property

end CalabiYau.Schauder
