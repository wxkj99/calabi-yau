module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.InnerProductSpace.PiL2

import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderInductionStep.LowerDerivativeHolder
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderInductionStep.ResolventJetHolder

/-!
# Local Hölder jets of a nonsingular matrix inverse

The inverse is taken only near an invertible matrix. Constants are chosen after
the matrix function and the centre; the neighbourhood may shrink. `HolderBoundOn`
does not encode differentiability, so genuine finite regularity is kept explicit.
No extra derivative of the matrix function is assumed.
-/

@[expose] public section

open scoped ContDiff NNReal Topology

private theorem inverse_entry_det_adjugate
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    B⁻¹ i j = B.det⁻¹ * B.adjugate i j := by
  rw [Matrix.inv_def]
  simp

private theorem matrix_det_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n r : ℕ} {W : Set E}
    (B : E → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiffOn ℝ r (fun w ↦ B w i j) W) :
    ContDiffOn ℝ r (fun w ↦ (B w).det) W := by
  simp only [Matrix.det_apply]
  fun_prop

private theorem matrix_adjugate_entry_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n r : ℕ} {W : Set E}
    (B : E → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiffOn ℝ r (fun w ↦ B w i j) W) (i j : Fin n) :
    ContDiffOn ℝ r (fun w ↦ (B w).adjugate i j) W := by
  have hUpdate (a b : Fin n) : ContDiffOn ℝ r
      (fun w ↦ (B w).updateRow j (Pi.single i 1) a b) W := by
    by_cases ha : a = j
    · subst a
      by_cases hb : b = i
      · subst b
        simp [Matrix.updateRow_apply]
        exact contDiffOn_const
      · simp [Matrix.updateRow_apply, hb]
        exact contDiffOn_const
    · simp [Matrix.updateRow_apply, ha]
      exact hB a b
  have hdetUpdate : ContDiffOn ℝ r
      (fun w ↦ ((B w).updateRow j (Pi.single i 1)).det) W := by
    apply matrix_det_contDiffOn
    intro a b
    exact hUpdate a b
  apply hdetUpdate.congr
  intro w hw
  exact Matrix.adjugate_apply (B w) i j

private theorem exists_open_neighborhood_norm_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set E} {f : E → ℂ} {z : E}
    (hW : IsOpen W) (hz : z ∈ W) (hf : ContinuousAt f z) (hfz : f z ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      ∃ c : ℝ, 0 < c ∧ ∀ w ∈ V, c ≤ ‖f w‖ := by
  have hn : 0 < ‖f z‖ := norm_pos_iff.mpr hfz
  have hε : 0 < ‖f z‖ / 2 := by positivity
  have hnear : f ⁻¹' Metric.ball (f z) (‖f z‖ / 2) ∈ 𝓝 z :=
    hf.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
  obtain ⟨V, hVsub, hVopen, hzV⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hW.mem_nhds hz) hnear)
  refine ⟨V, hVopen, hzV, ?_, ‖f z‖ / 2, hε, ?_⟩
  · exact fun w hw ↦ (hVsub hw).1
  · intro w hw
    have hball : ‖f w - f z‖ < ‖f z‖ / 2 := by
      simpa [dist_eq_norm] using Metric.mem_ball.mp (hVsub hw).2
    have htriangle : ‖f z‖ ≤ ‖f w‖ + ‖f w - f z‖ := by
      calc
        ‖f z‖ = ‖f w - (f w - f z)‖ := by congr 1; ring
        _ ≤ ‖f w‖ + ‖f w - f z‖ := norm_sub_le _ _
    nlinarith

private theorem exists_local_matrix_det_separation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n r : ℕ} {W : Set E}
    (hW : IsOpen W)
    (B : E → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiffOn ℝ r (fun w ↦ B w i j) W)
    (hunit : ∀ w ∈ W, IsUnit (B w))
    (z : E) (hz : z ∈ W) :
    ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      ∃ c : ℝ, 0 < c ∧ ∀ w ∈ V, c ≤ ‖(B w).det‖ := by
  have hdet := matrix_det_contDiffOn B hB
  have hdetAt : ContinuousAt (fun w ↦ (B w).det) z :=
    hdet.continuousOn.continuousAt (hW.mem_nhds hz)
  have hdetNe : (B z).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (B z)).mp (hunit z hz)).ne_zero
  exact exists_open_neighborhood_norm_lower hW hz hdetAt hdetNe

private theorem matrix_det_inv_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n r : ℕ} {W : Set E}
    (B : E → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiffOn ℝ r (fun w ↦ B w i j) W)
    (hdet : ∀ w ∈ W, (B w).det ≠ 0) :
    ContDiffOn ℝ r (fun w ↦ ((B w).det)⁻¹) W := by
  exact (matrix_det_contDiffOn B hB).inv hdet

private theorem matrix_inverse_entry_contDiffOn_of_det_inv_adjugate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n r : ℕ} {W : Set E}
    (B : E → Matrix (Fin n) (Fin n) ℂ)
    (hdetInv : ContDiffOn ℝ r (fun w ↦ ((B w).det)⁻¹) W)
    (hadj : ∀ i j, ContDiffOn ℝ r (fun w ↦ (B w).adjugate i j) W)
    (i j : Fin n) :
    ContDiffOn ℝ r (fun w ↦ (B w)⁻¹ i j) W := by
  have hprod := hdetInv.mul (hadj i j)
  apply hprod.congr
  intro w hw
  rw [Matrix.inv_def]
  simp

private theorem compact_derivative_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Set E} (hW : IsOpen W) {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ m f W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ C : ℝ≥0, ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have htop (j : ℕ) (hj : j ≤ m) : (j : ℕ∞ω) ≤ (m : ℕ∞ω) := by
    exact_mod_cast hj
  have hcont (j : ℕ) (hj : j ≤ m) :
      ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ j f x‖) K := by
    have hwithin := hf.continuousOn_iteratedFDerivWithin (htop j hj) hW.uniqueDiffOn
    have heq : ∀ x ∈ W,
        iteratedFDerivWithin ℝ j f W x = iteratedFDeriv ℝ j f x := by
      intro x hx
      exact iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn
        ((hf.contDiffAt (hW.mem_nhds hx)).of_le (htop j hj)) hx
    exact (hwithin.congr (fun x hx => (heq x hx).symm)).mono hKW |>.norm
  let q : E → ℝ := fun x ↦ ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j f x‖
  have hq : ContinuousOn q K := by
    dsimp [q]
    exact continuousOn_finsetSum (Finset.range (m + 1)) fun j hj =>
      hcont j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  obtain ⟨B, hB0, hB⟩ := (hK.bddAbove_image hq).exists_ge 0
  let C : ℝ≥0 := ⟨B, hB0⟩
  refine ⟨C, ?_⟩
  intro j hj x hx
  have hqbound : q x ≤ B := hB (q x) (Set.mem_image_of_mem q hx)
  have hterm : ‖iteratedFDeriv ℝ j f x‖ ≤ q x := by
    dsimp [q]
    apply Finset.single_le_sum (f := fun i ↦ ‖iteratedFDeriv ℝ i f x‖)
    · intro i hi
      exact norm_nonneg _
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  change ‖iteratedFDeriv ℝ j f x‖ ≤ B
  exact hterm.trans hqbound

private theorem compact_matrix_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n r : ℕ} {W Q : Set E} {B : E → Matrix (Fin n) (Fin n) ℂ}
    (hW : IsOpen W) (hQ : IsCompact Q) (hQW : Q ⊆ W)
    (hInv : ∀ i j, ContDiffOn ℝ r (fun x ↦ (B x)⁻¹ i j) W) :
    ∃ N : ℝ≥0, ∀ i j, ∀ k ≤ r, ∀ x ∈ Q,
      ‖iteratedFDeriv ℝ k (fun x ↦ (B x)⁻¹ i j) x‖ ≤ N := by
  classical
  choose C hC using fun ij : Fin n × Fin n =>
    compact_derivative_bound hW (hInv ij.1 ij.2) hQ hQW
  refine ⟨∑ ij : Fin n × Fin n, C ij, ?_⟩
  intro i j k hk x hx
  have hentry := hC (i, j) k hk x hx
  have hle : C (i, j) ≤ ∑ ij : Fin n × Fin n, C ij := by
    exact Finset.single_le_sum (fun ij hij => bot_le) (Finset.mem_univ (i, j))
  exact hentry.trans hle

private theorem matrix_resolvent_holderOnWith
    {E : Type*} [PseudoMetricSpace E] {n : ℕ} {α C B : ℝ≥0} {U : Set E}
    (A : E → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, HolderOnWith C α (fun z ↦ A z i j) U)
    (hUnit : ∀ z ∈ U, IsUnit (A z))
    (hInv : ∀ z ∈ U, ∀ i j, ‖(A z)⁻¹ i j‖ ≤ B) (i j : Fin n) :
    HolderOnWith ((n : ℝ≥0) ^ 2 * B ^ 2 * C) α
      (fun z ↦ (A z)⁻¹ i j) U := by
  intro x hx y hy
  have hiden : (A x)⁻¹ - (A y)⁻¹ = (A x)⁻¹ * (A y - A x) * (A y)⁻¹ := by
    have hxdet : IsUnit (Matrix.det (A x)) :=
      (Matrix.isUnit_iff_isUnit_det (A x)).mp (hUnit x hx)
    have hydet : IsUnit (Matrix.det (A y)) :=
      (Matrix.isUnit_iff_isUnit_det (A y)).mp (hUnit y hy)
    calc
      (A x)⁻¹ - (A y)⁻¹ = (A x)⁻¹ * 1 - 1 * (A y)⁻¹ := by simp
      _ = (A x)⁻¹ * (A y * (A y)⁻¹) -
          ((A x)⁻¹ * (A x)) * (A y)⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hydet, Matrix.nonsing_inv_mul _ hxdet]
      _ = (A x)⁻¹ * (A y - A x) * (A y)⁻¹ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        simp only [Matrix.mul_assoc]
  have hentry (k l : Fin n) :
      ‖A y k l - A x k l‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    have h := (hA k l).edist_le hx hy
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at h
    have h' : dist (A x k l) (A y k l) ≤
        (C : ℝ) * dist x y ^ (α : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff
        (p := dist (A x k l) (A y k l))
        (q := (C : ℝ) * dist x y ^ (α : ℝ)) (by positivity)).mp h
    rw [dist_eq_norm] at h'
    simpa [norm_sub_rev] using h'
  have hnorm : ‖((A x)⁻¹) i j - ((A y)⁻¹) i j‖ ≤
      ((n : ℝ) ^ 2) * (B : ℝ) ^ 2 * (C : ℝ) * dist x y ^ (α : ℝ) := by
    rw [show ((A x)⁻¹) i j - ((A y)⁻¹) i j =
        ∑ k : Fin n, ∑ l : Fin n,
          (A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j by
      rw [← Matrix.sub_apply, hiden]
      simp only [Matrix.mul_apply, Matrix.sub_apply, Finset.sum_mul]
      rw [Finset.sum_comm]]
    calc
      ‖∑ k : Fin n, ∑ l : Fin n,
          (A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j‖ ≤
          ∑ k : Fin n, ∑ l : Fin n,
            ‖(A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j‖ := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦ norm_sum_le _ _)
      _ ≤ ∑ k : Fin n, ∑ l : Fin n,
          (B : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)) * (B : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        apply Finset.sum_le_sum
        intro l hl
        calc
          ‖(A x)⁻¹ i k * (A y k l - A x k l) * (A y)⁻¹ l j‖ ≤
              ‖(A x)⁻¹ i k‖ * ‖A y k l - A x k l‖ * ‖(A y)⁻¹ l j‖ := by
            exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
          _ ≤ (B : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)) * (B : ℝ) := by
            gcongr
            · exact hInv x hx i k
            · exact hentry k l
            · exact hInv y hy l j
      _ = ((n : ℝ) ^ 2) * (B : ℝ) ^ 2 * (C : ℝ) *
          dist x y ^ (α : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  change edist (((A x)⁻¹) i j) (((A y)⁻¹) i j) ≤
      (((n : ℝ≥0) ^ 2 * B ^ 2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ)
  rw [edist_dist]
  calc
    ENNReal.ofReal (dist (((A x)⁻¹) i j) (((A y)⁻¹) i j)) =
        ENNReal.ofReal ‖((A x)⁻¹) i j - ((A y)⁻¹) i j‖ := by rw [dist_eq_norm]
    _ ≤ ENNReal.ofReal (((n : ℝ) ^ 2) * (B : ℝ) ^ 2 * (C : ℝ) *
        dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal hnorm
    _ = (((n : ℝ≥0) ^ 2 * B ^ 2 * C : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
      rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
      norm_cast

/-- Local inversion preserves a genuine finite `C^{r,α}` matrix jet. -/
theorem locally_holder_matrix_inverse
    {n r : ℕ} {α K : ℝ≥0} {W : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (hα₁ : α < 1)
    (B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiffOn ℝ r (fun w ↦ B w i j) W)
    (hunit : ∀ w ∈ W, IsUnit (B w))
    (hBH : ∀ i j, HolderBoundOn r α K W (fun w ↦ B w i j))
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ W) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), ∃ C : ℝ≥0,
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      ∀ i j, HolderBoundOn r α C V (fun w ↦ (B w)⁻¹ i j) := by
  have hdetSmooth := matrix_det_contDiffOn B hB
  have hadjSmooth (i j : Fin n) := matrix_adjugate_entry_contDiffOn B hB i j
  obtain ⟨V, hVo, hzV, hVW, c, hc, hdetLower⟩ :=
    exists_local_matrix_det_separation hW B hB hunit z hz
  have hdetNonzero : ∀ w ∈ V, (B w).det ≠ 0 := by
    intro w hw hzero
    have := hdetLower w hw
    rw [hzero, norm_zero] at this
    linarith
  have hdetInv := matrix_det_inv_contDiffOn B (fun i j ↦ (hB i j).mono hVW) hdetNonzero
  have hinvContDiff (i j : Fin n) :
      ContDiffOn ℝ r (fun w ↦ (B w)⁻¹ i j) V :=
    matrix_inverse_entry_contDiffOn_of_det_inv_adjugate B hdetInv
      (fun i j ↦ (hadjSmooth i j).mono hVW) i j
  have hinvRepr (i j : Fin n) (w : EuclideanSpace ℂ (Fin n)) :
      (B w)⁻¹ i j = ((B w).det)⁻¹ * (B w).adjugate i j :=
    inverse_entry_det_adjugate (B w) i j
  obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.mp (hVo.mem_nhds hzV)
  obtain ⟨ρLower, hρLowerPos, _, _, hLowerJets⟩ :=
    locally_holder_lower_matrix_jets hW hα₁ B hB hBH z hz
  let ρ : ℝ := min (R / 2) (min (1 / 8) ρLower)
  let U : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball z ρ
  let Q : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall z ρ
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hρlt : ρ < R := by
    dsimp [ρ]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρleLower : ρ ≤ ρLower := by
    dsimp [ρ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := by
    change z ∈ Metric.ball z ρ
    exact Metric.mem_ball_self hρpos
  have hUsubQ : U ⊆ Q := Metric.ball_subset_closedBall
  have hQcompact : IsCompact Q := isCompact_closedBall z ρ
  have hQsubV : Q ⊆ V := by
    intro w hw
    apply hRball
    rw [Metric.mem_ball]
    have hw' : dist w z ≤ ρ := by
      simpa [Q, Metric.mem_closedBall] using hw
    exact lt_of_le_of_lt hw' hρlt
  have hQsubW : Q ⊆ W := hQsubV.trans hVW
  have hUsubW : U ⊆ W := fun w hw ↦ hQsubW (hUsubQ hw)
  have hUsubV : U ⊆ V := hUsubQ.trans hQsubV
  have hUsubLower : U ⊆ Metric.ball z ρLower := by
    intro w hw
    change dist w z < ρ at hw
    change dist w z < ρLower
    exact lt_of_lt_of_le hw hρleLower
  have hBJetHolder : ∀ i j m, m ≤ r → HolderOnWith K α
      (fun w ↦ iteratedFDeriv ℝ m (fun v ↦ B v i j) w) U := by
    intro i j m hm
    by_cases hmr : m = r
    · subst m
      exact ((hBH i j).mono_set hUsubW).2
    · exact (hLowerJets i j m (lt_of_le_of_ne hm hmr)).mono hUsubLower
  obtain ⟨N, hN⟩ := compact_matrix_derivative_bound hVo hQcompact hQsubV hinvContDiff
  let C : ℝ≥0 := max N
    ((n : ℝ≥0) ^ 2 * ((2 : ℝ≥0) ^ r) ^ 2 * N ^ 2 * K)
  refine ⟨U, C, hUopen, hzU, hUsubW, ?_⟩
  intro i j
  refine ⟨?_, ?_⟩
  · intro k hk w hw
    exact (hN i j k hk w (hUsubQ hw)).trans (by exact_mod_cast (le_max_left _ _))
  · intro x hx y hy
    by_cases hr : r = 0
    · subst r
      let L := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℂ
      have hAHolder (p q : Fin n) : HolderOnWith K α (fun w ↦ B w p q) U := by
        have hLocal : HolderBoundOn 0 α K U (fun w ↦ B w p q) :=
          (hBH p q).mono_set hUsubW
        intro x hx y hy
        have h := hLocal.2 x hx y hy
        rw [iteratedFDeriv_zero_eq_comp] at h
        change edist (L.symm (B x p q)) (L.symm (B y p q)) ≤ _ at h
        rw [L.symm.edist_map] at h
        exact h
      have hUnitLocal : ∀ w ∈ U, IsUnit (B w) := fun w hw ↦ hunit w (hUsubW hw)
      have hInvBound : ∀ w ∈ U, ∀ p q, ‖(B w)⁻¹ p q‖ ≤ N := by
        intro w hw p q
        have h := hN p q 0 (by simp) w (hUsubQ hw)
        rw [norm_iteratedFDeriv_zero] at h
        exact h
      have hHolder := matrix_resolvent_holderOnWith B hAHolder hUnitLocal hInvBound i j
      have hHolder' : HolderOnWith C α (fun w ↦ (B w)⁻¹ i j) U := by
        exact hHolder.mono_const (by
          dsimp [C]
          simp only [pow_zero, one_pow, mul_one]
          exact le_max_right _ _)
      rw [iteratedFDeriv_zero_eq_comp]
      change edist (L.symm ((B x)⁻¹ i j)) (L.symm ((B y)⁻¹ i j)) ≤ _
      rw [L.symm.edist_map]
      exact hHolder' x hx y hy
    ·
      have hrpos : 0 < r := by omega
      have hHolderTop := matrix_inverse_top_jet_holder_from_jets hUopen B
        (fun i j ↦ (hB i j).mono hUsubW)
        (fun w hw ↦ hunit w (hUsubW hw))
        (fun i j ↦ (hinvContDiff i j).mono hUsubV)
        (by
          intro i j m hm w hw
          exact hN i j m hm w (hUsubQ hw))
        hBJetHolder
      have hHolder' : HolderOnWith C α
          (fun w ↦ iteratedFDeriv ℝ r (fun w ↦ (B w)⁻¹ i j) w) U := by
        exact (hHolderTop i j).mono_const (by
          dsimp [C]
          exact le_max_right _ _)
      exact hHolder' x hx y hy
