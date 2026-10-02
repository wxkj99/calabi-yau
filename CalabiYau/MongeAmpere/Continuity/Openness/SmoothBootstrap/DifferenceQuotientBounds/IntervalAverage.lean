module

public import CalabiYau.Analysis.Elliptic.Schauder
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

public section
open scoped NNReal Topology
open Set Matrix MeasureTheory
namespace KahlerForm

private theorem quadratic_eq_rankOne_trace {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    star v ⬝ᵥ (A *ᵥ v) = (A * vecMulVec v (star v)).trace := by
  classical
  simp only [dotProduct, mulVec, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    vecMulVec_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem trace_intervalIntegral_matrix_mul {n : ℕ}
    (F : ℝ → Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, IntervalIntegrable (fun s ↦ F s i j) MeasureTheory.volume 0 1) :
    (let I : Matrix (Fin n) (Fin n) ℂ := fun i j ↦ ∫ s in (0 : ℝ)..1, F s i j
     (I * D).trace) = ∫ s in (0 : ℝ)..1, (F s * D).trace := by
  classical
  change (∑ i, ∑ j, (∫ s in (0 : ℝ)..1, F s i j) * D j i) =
    ∫ s in (0 : ℝ)..1, ∑ i, ∑ j, F s i j * D j i
  calc
    (∑ i, ∑ j, (∫ s in (0 : ℝ)..1, F s i j) * D j i) =
        ∑ i, ∫ s in (0 : ℝ)..1, ∑ j, F s i j * D j i := by
      congr 1
      funext i
      simpa only [intervalIntegral.integral_mul_const] using
        (intervalIntegral.integral_finsetSum
          (s := Finset.univ) (f := fun j s ↦ F s i j * D j i)
          (fun j hj ↦ (hF i j).mul_const (D j i))).symm
    _ = ∫ s in (0 : ℝ)..1, ∑ i, ∑ j, F s i j * D j i := by
      exact (intervalIntegral.integral_finsetSum
        (s := Finset.univ) (f := fun i s ↦ ∑ j, F s i j * D j i)
        (fun i hi ↦ by
          have hsum := IntervalIntegrable.sum Finset.univ
            (fun j hj ↦ (hF i j).mul_const (D j i))
          have heq : (∑ j, fun s : ℝ ↦ F s i j * D j i) =
              (fun s ↦ ∑ j, F s i j * D j i) := by funext s; simp
          rw [← heq]
          exact hsum)).symm

private theorem quadratic_intervalIntegral {n : ℕ}
    (F : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ i j, ContinuousOn (fun s ↦ F s i j) (Icc (0 : ℝ) 1))
    (v : Fin n → ℂ) :
    Complex.re (star v ⬝ᵥ ((fun i j ↦ ∫ s in (0 : ℝ)..1, F s i j) *ᵥ v)) =
      ∫ s in (0 : ℝ)..1, Complex.re (star v ⬝ᵥ (F s *ᵥ v)) := by
  have hint (i j : Fin n) : IntervalIntegrable (fun s ↦ F s i j) MeasureTheory.volume 0 1 :=
    (hF i j).intervalIntegrable_of_Icc (by norm_num)
  have htcont : ContinuousOn
      (fun s ↦ (F s * vecMulVec v (star v)).trace) (Icc (0 : ℝ) 1) := by
    change ContinuousOn (fun s ↦ ∑ i, ∑ j,
      F s i j * (vecMulVec v (star v)) j i) (Icc (0 : ℝ) 1)
    fun_prop
  have htint : IntervalIntegrable
      (fun s ↦ (F s * vecMulVec v (star v)).trace) MeasureTheory.volume 0 1 :=
    htcont.intervalIntegrable_of_Icc (by norm_num)
  let I : Matrix (Fin n) (Fin n) ℂ := fun i j ↦ ∫ s in (0 : ℝ)..1, F s i j
  calc
    _ = Complex.re (I * vecMulVec v (star v)).trace :=
      congrArg Complex.re (quadratic_eq_rankOne_trace _ v)
    _ = Complex.re (∫ s in (0 : ℝ)..1, (F s * vecMulVec v (star v)).trace) :=
      congrArg Complex.re (trace_intervalIntegral_matrix_mul F _ hint)
    _ = ∫ s in (0 : ℝ)..1, Complex.re (F s * vecMulVec v (star v)).trace :=
      (intervalIntegral.intervalIntegral_re htint).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact congrArg Complex.re (quadratic_eq_rankOne_trace (F s) v).symm

/-- Entrywise averaging over the unit interval preserves a common ellipticity constant. -/
theorem isUniformlyEllipticOn_intervalAverage {n : ℕ}
    (F : ℝ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (K : Set (EuclideanSpace ℂ (Fin n))) (lam : ℝ≥0)
    (hF : ∀ z ∈ K, ∀ i j,
      ContinuousOn (fun s ↦ F s z i j) (Icc (0 : ℝ) 1))
    (hEll : ∀ s ∈ Icc (0 : ℝ) 1, IsUniformlyEllipticOn (F s) lam K) :
    IsUniformlyEllipticOn
      (fun z i j ↦ ∫ s in (0 : ℝ)..1, F s z i j) lam K := by
  intro z hz
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    change star (∫ s in (0 : ℝ)..1, F s z j i) = ∫ s in (0 : ℝ)..1, F s z i j
    have heq : (∫ s in (0 : ℝ)..1, star (F s z j i)) =
        ∫ s in (0 : ℝ)..1, F s z i j := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
      exact (hEll s hs' z hz).1.apply i j
    have hc := intervalIntegral.intervalIntegral_conj
      (f := fun s ↦ F s z j i) (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    exact hc.symm.trans heq
  · intro v
    have hqcont : ContinuousOn
        (fun s ↦ Complex.re (star v ⬝ᵥ (F s z *ᵥ v))) (Icc (0 : ℝ) 1) := by
      unfold dotProduct mulVec
      fun_prop
    have hqint : IntervalIntegrable
        (fun s ↦ Complex.re (star v ⬝ᵥ (F s z *ᵥ v))) MeasureTheory.volume 0 1 :=
      hqcont.intervalIntegrable_of_Icc (by norm_num)
    have hconst : IntervalIntegrable
        (fun _ : ℝ ↦ (lam : ℝ) * ∑ i, ‖v i‖ ^ 2) MeasureTheory.volume 0 1 :=
      intervalIntegrable_const
    have hm := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hconst hqint (fun s hs ↦ (hEll s hs z hz).2 v)
    calc
      (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 =
          ∫ _ in (0 : ℝ)..1, (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 := by simp
      _ ≤ ∫ s in (0 : ℝ)..1, Complex.re (star v ⬝ᵥ (F s z *ᵥ v)) := hm
      _ = _ := (quadratic_intervalIntegral (fun s ↦ F s z) (hF z hz) v).symm

theorem holderBoundOn_interval_average
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (α K : ℝ≥0) (hα₀ : 0 < α) (_hα₁ : α < 1)
    (U : Set E) (F : ℝ → E → G)
    (hHolder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HolderBoundOn 0 α K U (F s))
    (hIntegrable : ∀ z ∈ U,
      IntervalIntegrable (fun s ↦ F s z) MeasureTheory.volume 0 1)
    (_hContinuous : ∀ z ∈ U,
      ContinuousOn (fun s ↦ F s z) (Set.Icc (0 : ℝ) 1)) :
    HolderBoundOn 0 α K U (fun z ↦ ∫ s in (0 : ℝ)..1, F s z) := by
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (z : E) (hz : z ∈ U) :
      ‖F s z‖ ≤ (K : ℝ) := by
    have h := (hHolder s hs).1 0 le_rfl z hz
    simpa only [norm_iteratedFDeriv_zero] using h
  have hinterval (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) 1) (z : E) (hz : z ∈ U) :
      ‖F s z‖ ≤ (K : ℝ) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact hpoint s ⟨hs.1.le, hs.2⟩ z hz
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    have hbound : ‖∫ s in (0 : ℝ)..1, F s z‖ ≤ (K : ℝ) := by
      calc
        ‖∫ s in (0 : ℝ)..1, F s z‖ ≤ (K : ℝ) * |(1 : ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
            (C := (K : ℝ)) (fun s hs ↦ hinterval s hs z hz)
        _ = (K : ℝ) := by norm_num
    simpa only [norm_iteratedFDeriv_zero] using hbound
  · intro z hz w hw
    have hdiffint :
        (∫ s in (0 : ℝ)..1, F s z) - (∫ s in (0 : ℝ)..1, F s w) =
          ∫ s in (0 : ℝ)..1, (F s z - F s w) := by
      rw [intervalIntegral.integral_sub (hIntegrable z hz) (hIntegrable w hw)]
    have hnorm (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
        ‖F s z - F s w‖ ≤ (K : ℝ) * dist z w ^ (α : ℝ) := by
      let e := continuousMultilinearCurryFin0 ℝ E G
      have heq : ‖e.symm (F s z) - e.symm (F s w)‖ = ‖F s z - F s w‖ := by
        rw [← e.symm.map_sub, LinearIsometryEquiv.norm_map]
      have h := (hHolder s hs).2.dist_le hz hw
      rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply] at h
      rw [dist_eq_norm, heq] at h
      simpa only [dist_eq_norm] using h
    have hnormint :
        ‖∫ s in (0 : ℝ)..1, (F s z - F s w)‖ ≤
          (K : ℝ) * dist z w ^ (α : ℝ) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := (K : ℝ) * dist z w ^ (α : ℝ)) (fun s hs ↦ by
          have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
            exact ⟨hs.1.le, hs.2⟩
          exact hnorm s hs')
      simpa using h
    have hdist :
        dist (∫ s in (0 : ℝ)..1, F s z) (∫ s in (0 : ℝ)..1, F s w) ≤
          (K : ℝ) * dist z w ^ (α : ℝ) := by
      rw [dist_eq_norm, hdiffint]
      exact hnormint
    have havg : edist (∫ s in (0 : ℝ)..1, F s z) (∫ s in (0 : ℝ)..1, F s w) ≤
        (K : ENNReal) * edist z w ^ (α : ℝ) := by
      calc
        edist (∫ s in (0 : ℝ)..1, F s z) (∫ s in (0 : ℝ)..1, F s w) =
            ENNReal.ofReal (dist (∫ s in (0 : ℝ)..1, F s z)
              (∫ s in (0 : ℝ)..1, F s w)) := edist_dist _ _
        _ ≤ ENNReal.ofReal ((K : ℝ) * dist z w ^ (α : ℝ)) :=
          ENNReal.ofReal_le_ofReal hdist
        _ = (K : ENNReal) * edist z w ^ (α : ℝ) := by
          rw [edist_dist, ENNReal.coe_nnreal_eq,
            ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity : 0 ≤ (α : ℝ)),
            ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ))]
    let e := continuousMultilinearCurryFin0 ℝ E G
    change edist (e.symm (∫ s in (0 : ℝ)..1, F s z))
      (e.symm (∫ s in (0 : ℝ)..1, F s w)) ≤ (K : ENNReal) * edist z w ^ (α : ℝ)
    simpa only [e.symm.edist_map] using havg

end KahlerForm
