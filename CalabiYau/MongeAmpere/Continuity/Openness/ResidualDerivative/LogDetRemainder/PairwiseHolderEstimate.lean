module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.ChartTaylorData
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.MixedBaseVariation
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.PointwiseDifference

/-!
# Pairwise matrix Taylor Holder estimate

Székelyhidi Lemma 3.3: all three shifted cones and BOTH base-variation terms
are needed. The second is controlled by the perturbation increment, not background
alone. Shrink the radius using the same epsilon and inverse-bound witnesses.
-/

@[expose] public section

set_option maxHeartbeats 800000

open scoped Manifold ContDiff NNReal Topology ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory Set

namespace KahlerForm

private theorem holderBoundOn_zero_from_holderOnWith
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E}
    {α C : ℝ≥0} {f : E → F}
    (hf : HolderOnWith C α f K) (hBound : ∀ x ∈ K, ‖f x‖ ≤ C) :
    HolderBoundOn 0 α C K f := by
  let L := continuousMultilinearCurryFin0 ℝ E F
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa [norm_iteratedFDeriv_zero] using hBound x hx
  · intro x hx y hy
    rw [iteratedFDeriv_zero_eq_comp]
    change edist (L.symm (f x)) (L.symm (f y)) ≤ _
    rw [L.symm.edist_map]
    exact hf x hx y hy

private theorem holderBoundOn_zero_value
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E}
    {α C : ℝ≥0} {f : E → F}
    (hf : HolderBoundOn 0 α C K f) {x : E} (hx : x ∈ K) :
    ‖f x‖ ≤ C := by
  have h := hf.1 0 (Nat.zero_le 0) x hx
  simpa [norm_iteratedFDeriv_zero] using h

private theorem holderBoundOn_zero_normDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E}
    {α C : ℝ≥0} {f : E → F}
    (hf : HolderBoundOn 0 α C K f) {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
  let L := continuousMultilinearCurryFin0 ℝ E F
  have hHolder : HolderOnWith C α f K := by
    intro x hx y hy
    have h := hf.2 x hx y hy
    rw [iteratedFDeriv_zero_eq_comp] at h
    change edist (L.symm (f x)) (L.symm (f y)) ≤ _ at h
    rw [L.symm.edist_map] at h
    exact h
  have hdist := hHolder.dist_le hx hy
  simpa only [dist_eq_norm] using hdist

private theorem fixed_pairwise_pointwise
    {n : ℕ} {U E κ : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ≥0) (S : κ → Set E)
    (A : κ → E → Matrix (Fin n) (Fin n) ℂ)
    (H : U → κ → E → Matrix (Fin n) (Fin n) ℂ)
    (ctrl : ChartTaylorControl α S A H)
    (hfixed : LogDetTaylorRemainderLipschitz n)
    {r : ℝ} (hr : 0 < r) (hrsmall : 3 * (ctrl.jetConstant : ℝ) * r < ctrl.epsilon)
    {u v : U} (hu : ‖u‖ < r) (hv : ‖v‖ < r)
    {i : κ} {x : E} (hx : x ∈ S i) (hn : 0 < n) :
    |Matrix.logDetTaylorRemainder (A i x) (H u i x) -
      Matrix.logDetTaylorRemainder (A i x) (H v i x)| ≤
      (ctrl.inverseBound : ℝ) ^ 2 * (ctrl.jetConstant : ℝ) ^ 2 *
        ((‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊) := by
  let μ : ℝ := Real.sqrt (Fintype.card (Fin n) : ℝ) / (ctrl.inverseBound : ℝ)
  have hμ : 0 < μ := by
    apply div_pos
    · rw [Fintype.card_fin]
      exact Real.sqrt_pos.2 (by exact_mod_cast hn)
    · exact_mod_cast ctrl.inverseBound_pos
  have hsmallJ (J : Matrix (Fin n) (Fin n) ℂ) (hJ : J.IsHermitian)
      (hJn : ‖J‖ < ctrl.epsilon) :
      (A i x + J).PosDef ∧ ‖(A i x + J)⁻¹‖ ≤ ctrl.inverseBound := by
    have h := ctrl.smallHermitian i x x hx hx 0 (by norm_num) J hJ hJn
    constructor
    · simpa [add_assoc] using h.1
    · simpa [add_assoc] using h.2
  have hAx0 := hsmallJ 0 (by simp) (by simpa using ctrl.epsilon_pos)
  have hHuBound : ‖H u i x‖ ≤ (ctrl.jetConstant : ℝ) * ‖u‖ := by
    exact holderBoundOn_zero_value (ctrl.jetHolder u i) hx
  have hHvBound : ‖H v i x‖ ≤ (ctrl.jetConstant : ℝ) * ‖v‖ := by
    exact holderBoundOn_zero_value (ctrl.jetHolder v i) hx
  have hHuSmall : ‖H u i x‖ < ctrl.epsilon := by
    calc
      ‖H u i x‖ ≤ (ctrl.jetConstant : ℝ) * ‖u‖ := hHuBound
      _ ≤ (ctrl.jetConstant : ℝ) * r := mul_le_mul_of_nonneg_left hu.le (NNReal.coe_nonneg _)
      _ < ctrl.epsilon := by nlinarith [hrsmall, NNReal.coe_nonneg ctrl.jetConstant]
  have hHvSmall : ‖H v i x‖ < ctrl.epsilon := by
    calc
      ‖H v i x‖ ≤ (ctrl.jetConstant : ℝ) * ‖v‖ := hHvBound
      _ ≤ (ctrl.jetConstant : ℝ) * r := mul_le_mul_of_nonneg_left hv.le (NNReal.coe_nonneg _)
      _ < ctrl.epsilon := by nlinarith [hrsmall, NNReal.coe_nonneg ctrl.jetConstant]
  have hsegment : ∀ s ∈ Icc (0 : ℝ) 1,
      (A i x + (1 - s) • H v i x + s • H u i x).PosDef := by
    intro s hs
    let J : Matrix (Fin n) (Fin n) ℂ := (1 - s) • H v i x + s • H u i x
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1s : 0 ≤ 1 - s := by linarith
    have hJherm : J.IsHermitian := by
      have hvh : (H v i x).conjTranspose = H v i x := ctrl.jet_hermitian v i x hx
      have huh : (H u i x).conjTranspose = H u i x := ctrl.jet_hermitian u i x hx
      simp [J, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        hvh, huh]
    have hJnorm : ‖J‖ < ctrl.epsilon := by
      dsimp [J]
      calc
        ‖(1 - s) • H v i x + s • H u i x‖ ≤
            ‖(1 - s) • H v i x‖ + ‖s • H u i x‖ := norm_add_le _ _
        _ = (1 - s) * ‖H v i x‖ + s * ‖H u i x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1s, abs_of_nonneg hs0]
        _ ≤ (1 - s) * ((ctrl.jetConstant : ℝ) * ‖v‖) +
              s * ((ctrl.jetConstant : ℝ) * ‖u‖) := by gcongr
        _ ≤ (ctrl.jetConstant : ℝ) * r := by
          calc
            _ ≤ (1 - s) * ((ctrl.jetConstant : ℝ) * r) +
                  s * ((ctrl.jetConstant : ℝ) * r) := by gcongr
            _ = (ctrl.jetConstant : ℝ) * r := by ring
        _ < ctrl.epsilon := by nlinarith [hrsmall, NNReal.coe_nonneg ctrl.jetConstant]
    have h := hsmallJ J hJherm hJnorm
    simpa [J, add_assoc] using h.1
  have hsegmentInv : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖(A i x + (1 - s) • H v i x + s • H u i x)⁻¹‖ ≤ ctrl.inverseBound := by
    intro s hs
    let J : Matrix (Fin n) (Fin n) ℂ := (1 - s) • H v i x + s • H u i x
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1s : 0 ≤ 1 - s := by linarith
    have hJherm : J.IsHermitian := by
      have hvh : (H v i x).conjTranspose = H v i x := ctrl.jet_hermitian v i x hx
      have huh : (H u i x).conjTranspose = H u i x := ctrl.jet_hermitian u i x hx
      simp [J, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        hvh, huh]
    have hJnorm : ‖J‖ < ctrl.epsilon := by
      dsimp [J]
      calc
        ‖(1 - s) • H v i x + s • H u i x‖ ≤
            ‖(1 - s) • H v i x‖ + ‖s • H u i x‖ := norm_add_le _ _
        _ = (1 - s) * ‖H v i x‖ + s * ‖H u i x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1s, abs_of_nonneg hs0]
        _ ≤ (1 - s) * ((ctrl.jetConstant : ℝ) * ‖v‖) +
              s * ((ctrl.jetConstant : ℝ) * ‖u‖) := by gcongr
        _ ≤ (ctrl.jetConstant : ℝ) * r := by
          calc
            _ ≤ (1 - s) * ((ctrl.jetConstant : ℝ) * r) +
                  s * ((ctrl.jetConstant : ℝ) * r) := by gcongr
            _ = (ctrl.jetConstant : ℝ) * r := by ring
        _ < ctrl.epsilon := by nlinarith [hrsmall, NNReal.coe_nonneg ctrl.jetConstant]
    have h := hsmallJ J hJherm hJnorm
    simpa [J, add_assoc] using h.2
  have hsqrtpos : 0 < Real.sqrt (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin]
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hMpos : 0 < (ctrl.inverseBound : ℝ) := by exact_mod_cast ctrl.inverseBound_pos
  have hratio : Real.sqrt (Fintype.card (Fin n) : ℝ) / μ =
      (ctrl.inverseBound : ℝ) := by
    dsimp [μ]
    field_simp [ne_of_gt hsqrtpos, ne_of_gt hMpos]
  have hAxInv : ‖(A i x)⁻¹‖ ≤ Real.sqrt (Fintype.card (Fin n) : ℝ) / μ := by
    rw [hratio]
    simpa [add_zero] using (show ‖(A i x + 0)⁻¹‖ ≤ (ctrl.inverseBound : ℝ) from by
      exact_mod_cast hAx0.2)
  have hfac : (Fintype.card (Fin n) : ℝ) / μ ^ 2 =
      (ctrl.inverseBound : ℝ) ^ 2 := by
    dsimp [μ]
    rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card (Fin n) : ℝ))]
    field_simp [ne_of_gt hsqrtpos, ne_of_gt hMpos]
    have hncard : (Fintype.card (Fin n) : ℝ) ≠ 0 := by
      rw [Fintype.card_fin]
      exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hncard]
  have hInvBound : (ctrl.inverseBound : ℝ) ≤ Real.sqrt (Fintype.card (Fin n) : ℝ) / μ :=
    le_of_eq hratio.symm
  have hsegmentInv' : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖(A i x + (1 - s) • H v i x + s • H u i x)⁻¹‖ ≤
        Real.sqrt (Fintype.card (Fin n) : ℝ) / μ := by
    intro s hs
    exact (hsegmentInv s hs).trans hInvBound
  have hfixed' := hfixed (A i x) (H u i x) (H v i x) μ hμ
    (by simpa [add_zero] using hAx0.1) hAxInv hsegment hsegmentInv'
  have hD : ‖H u i x - H v i x‖ ≤ (ctrl.jetConstant : ℝ) * ‖u - v‖ := by
    rw [← ctrl.jet_sub u v i x hx]
    exact holderBoundOn_zero_value (ctrl.jetHolder (u - v) i) hx
  have hmax : max ‖H u i x‖ ‖H v i x‖ ≤
      (ctrl.jetConstant : ℝ) * (‖u‖ + ‖v‖) := by
    apply max_le
    · exact hHuBound.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (norm_nonneg v)) (NNReal.coe_nonneg _))
    · exact hHvBound.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (norm_nonneg u)) (NNReal.coe_nonneg _))
  rw [hfac] at hfixed'
  calc
    |Matrix.logDetTaylorRemainder (A i x) (H u i x) -
      Matrix.logDetTaylorRemainder (A i x) (H v i x)| ≤
        (ctrl.inverseBound : ℝ) ^ 2 * max ‖H u i x‖ ‖H v i x‖ *
          ‖H u i x - H v i x‖ := hfixed'
    _ ≤ (ctrl.inverseBound : ℝ) ^ 2 *
          ((ctrl.jetConstant : ℝ) * (‖u‖ + ‖v‖)) *
          ((ctrl.jetConstant : ℝ) * ‖u - v‖) := by gcongr
    _ = (ctrl.inverseBound : ℝ) ^ 2 * (ctrl.jetConstant : ℝ) ^ 2 *
          ((‖u‖ + ‖v‖) * ‖u - v‖) := by ring
    _ = (ctrl.inverseBound : ℝ) ^ 2 * (ctrl.jetConstant : ℝ) ^ 2 *
          ((‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊) := by simp

private theorem small_four_jet_combination
    {n : ℕ} {U E κ : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ≥0) (S : κ → Set E)
    (A : κ → E → Matrix (Fin n) (Fin n) ℂ)
    (H : U → κ → E → Matrix (Fin n) (Fin n) ℂ)
    (ctrl : ChartTaylorControl α S A H)
    {u v : U} {i : κ} {x y : E}
    (hx : x ∈ S i) (hy : y ∈ S i)
    {r : ℝ} (hr0 : 0 ≤ r) (hu : ‖u‖ < r) (hv : ‖v‖ < r)
    (hsmall : 3 * (ctrl.jetConstant : ℝ) * r < ctrl.epsilon)
    (a b c d : ℝ)
    (hcoeff : |a| + |b| + |c| + |d| ≤ 3)
    (J : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J = a • H u i x + b • H v i x + c • H u i y + d • H v i y) :
    J.IsHermitian ∧ ‖J‖ < ctrl.epsilon := by
  have hHuX := holderBoundOn_zero_value (ctrl.jetHolder u i) hx
  have hHvX := holderBoundOn_zero_value (ctrl.jetHolder v i) hx
  have hHuY := holderBoundOn_zero_value (ctrl.jetHolder u i) hy
  have hHvY := holderBoundOn_zero_value (ctrl.jetHolder v i) hy
  have hHuX' : ‖H u i x‖ ≤ (ctrl.jetConstant : ℝ) * r := by
    exact hHuX.trans (mul_le_mul_of_nonneg_left hu.le (NNReal.coe_nonneg _))
  have hHvX' : ‖H v i x‖ ≤ (ctrl.jetConstant : ℝ) * r := by
    exact hHvX.trans (mul_le_mul_of_nonneg_left hv.le (NNReal.coe_nonneg _))
  have hHuY' : ‖H u i y‖ ≤ (ctrl.jetConstant : ℝ) * r := by
    exact hHuY.trans (mul_le_mul_of_nonneg_left hu.le (NNReal.coe_nonneg _))
  have hHvY' : ‖H v i y‖ ≤ (ctrl.jetConstant : ℝ) * r := by
    exact hHvY.trans (mul_le_mul_of_nonneg_left hv.le (NNReal.coe_nonneg _))
  have hherm : J.IsHermitian := by
    have hux : (H u i x).conjTranspose = H u i x := ctrl.jet_hermitian u i x hx
    have hvx : (H v i x).conjTranspose = H v i x := ctrl.jet_hermitian v i x hx
    have huy : (H u i y).conjTranspose = H u i y := ctrl.jet_hermitian u i y hy
    have hvy : (H v i y).conjTranspose = H v i y := ctrl.jet_hermitian v i y hy
    change J.conjTranspose = J
    rw [hJ]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hux, hvx, huy, hvy,
      star_trivial]
  have hnorm : ‖J‖ ≤ (|a| + |b| + |c| + |d|) *
      ((ctrl.jetConstant : ℝ) * r) := by
    rw [hJ]
    calc
      ‖a • H u i x + b • H v i x + c • H u i y + d • H v i y‖ ≤
          ‖a • H u i x‖ + ‖b • H v i x‖ + ‖c • H u i y‖ + ‖d • H v i y‖ := by
        calc
          _ ≤ ‖a • H u i x + b • H v i x + c • H u i y‖ + ‖d • H v i y‖ := norm_add_le _ _
          _ ≤ _ := by
            have h := norm_add_le (a • H u i x + b • H v i x) (c • H u i y)
            have h' := norm_add_le (a • H u i x) (b • H v i x)
            nlinarith
      _ ≤ |a| * ((ctrl.jetConstant : ℝ) * r) + |b| * ((ctrl.jetConstant : ℝ) * r) +
          |c| * ((ctrl.jetConstant : ℝ) * r) + |d| * ((ctrl.jetConstant : ℝ) * r) := by
        simp only [norm_smul, Real.norm_eq_abs]
        gcongr
      _ = (|a| + |b| + |c| + |d|) * ((ctrl.jetConstant : ℝ) * r) := by ring
  refine ⟨hherm, ?_⟩
  calc
    ‖J‖ ≤ 3 * ((ctrl.jetConstant : ℝ) * r) := by
      calc
        ‖J‖ ≤ (|a| + |b| + |c| + |d|) * ((ctrl.jetConstant : ℝ) * r) := hnorm
        _ ≤ 3 * ((ctrl.jetConstant : ℝ) * r) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ < ctrl.epsilon := by nlinarith [hsmall]

private theorem exists_matrixPairwiseTaylor_nearDifferenceBound
    {n : ℕ} {U E κ : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ≥0) (S : κ → Set E)
    (A : κ → E → Matrix (Fin n) (Fin n) ℂ)
    (H : U → κ → E → Matrix (Fin n) (Fin n) ℂ)
    (ctrl : ChartTaylorControl α S A H)
    (hfixed : LogDetTaylorRemainderLipschitz n) (hbase : LogDetTaylorRemainderBaseLipschitz n)
    (hn : 0 < n) :
    ∃ Anear Bnear : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      3 * (ctrl.jetConstant : ℝ) * r < ctrl.epsilon ∧
      ∀ u v : U, ‖u‖ < r → ‖v‖ < r → ∀ i x y, x ∈ S i → y ∈ S i →
        |(Matrix.logDetTaylorRemainder (A i x) (H u i x) -
            Matrix.logDetTaylorRemainder (A i x) (H v i x)) -
          (Matrix.logDetTaylorRemainder (A i y) (H u i y) -
            Matrix.logDetTaylorRemainder (A i y) (H v i y))| ≤
          (‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊ *
            ((Anear : ℝ) * dist x y ^ (α : ℝ) +
              (Bnear : ℝ) * (dist x y ^ (α : ℝ)) ^ 2) := by
  classical
  let J : ℝ := ctrl.jetConstant
  let r : ℝ := min 1 (ctrl.epsilon / (12 * (J + 1)))
  have hJnonneg : 0 ≤ J := NNReal.coe_nonneg ctrl.jetConstant
  have heps : 0 < ctrl.epsilon := ctrl.epsilon_pos
  have hr : 0 < r := by
    dsimp [r]
    apply lt_min
    · norm_num
    · positivity
  have hsmall : 3 * J * r < ctrl.epsilon := by
    have hmin : min 1 (ctrl.epsilon / (12 * (J + 1))) ≤
        ctrl.epsilon / (12 * (J + 1)) := min_le_right _ _
    have hratio : 3 * J * (ctrl.epsilon / (12 * (J + 1))) < ctrl.epsilon := by
      have hfrac : 3 * J / (12 * (J + 1)) < 1 := by
        apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 12 * (J + 1))).2
        nlinarith
      calc
        3 * J * (ctrl.epsilon / (12 * (J + 1))) =
            (3 * J / (12 * (J + 1))) * ctrl.epsilon := by ring
        _ < ctrl.epsilon := by nlinarith [mul_lt_mul_of_pos_right hfrac heps]
    dsimp [r]
    exact (mul_le_mul_of_nonneg_left hmin (by positivity)).trans_lt hratio
  have hcontrolled {u v : U} {i : κ} {x y : E}
      (hu : ‖u‖ < r) (hv : ‖v‖ < r) (hx : x ∈ S i) (hy : y ∈ S i)
      (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (a b c d : ℝ) (hcoeff : |a| + |b| + |c| + |d| ≤ 3)
      (Q : Matrix (Fin n) (Fin n) ℂ)
      (hQ : Q = a • H u i x + b • H v i x + c • H u i y + d • H v i y) :
      (((1 - s) • A i x + s • A i y + Q).PosDef ∧
        ‖((1 - s) • A i x + s • A i y + Q)⁻¹‖ ≤ ctrl.inverseBound) := by
    obtain ⟨hQherm, hQnorm⟩ := small_four_jet_combination
      α S A H ctrl hx hy (le_of_lt hr) hu hv hsmall a b c d hcoeff Q hQ
    exact ctrl.smallHermitian i x y hx hy s hs Q hQherm hQnorm
  obtain ⟨Cb, hCb⟩ := hbase ctrl.inverseBound ctrl.inverseBound_pos
  let R : ℝ≥0 := r.toNNReal
  have hRcoe : (R : ℝ) = r := Real.coe_toNNReal r (le_of_lt hr)
  let G : ℝ≥0 := ctrl.baseConstant
  let c : ℝ≥0 := ctrl.jetConstant
  let M : ℝ≥0 := ctrl.inverseBound
  let N : ℝ≥0 := max 1 M
  let Anear : ℝ≥0 :=
    2 * Cb * (G + c * R) * c ^ 2 + M ^ 2 * c ^ 2 +
      N ^ 3 * c ^ 2 * (2 * G + 3 * c * R + 1) + N ^ 2 * c ^ 2
  refine ⟨Anear, 1, r, hr, hsmall, ?_⟩
  intro u v hu hv i x y hx hy
  let τ : ℝ := dist x y ^ (α : ℝ)
  let snorm : ℝ := (‖u‖₊ + ‖v‖₊ : ℝ)
  let dnorm : ℝ := (‖u - v‖₊ : ℝ)
  let Kx : Matrix (Fin n) (Fin n) ℂ := H v i x
  let Ky : Matrix (Fin n) (Fin n) ℂ := H v i y
  let Hx : Matrix (Fin n) (Fin n) ℂ := H u i x
  let Hy : Matrix (Fin n) (Fin n) ℂ := H u i y
  let Dx : Matrix (Fin n) (Fin n) ℂ := Hx - Kx
  let Dy : Matrix (Fin n) (Fin n) ℂ := Hy - Ky
  have hdu : ‖u - v‖₊ ≤ ‖u‖₊ + ‖v‖₊ := by
    exact_mod_cast norm_sub_le u v
  have hvR : ‖v‖₊ ≤ R := by
    change (‖v‖₊ : ℝ) ≤ (R : ℝ)
    rw [hRcoe]
    exact le_of_lt hv
  have hbase1 (s₀ t₀ : ℝ) (hs₀ : s₀ ∈ Icc (0 : ℝ) 1)
      (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
      (A i x + Kx + (1 - s₀) • ((A i y + Kx) - (A i x + Kx)) +
        t₀ • Dx).PosDef ∧
        ‖(A i x + Kx + (1 - s₀) • ((A i y + Kx) - (A i x + Kx)) +
          t₀ • Dx)⁻¹‖ ≤ M := by
    let Q : Matrix (Fin n) (Fin n) ℂ := (1 - t₀) • Kx + t₀ • Hx
    have hcoeff : |t₀| + |1 - t₀| + |(0 : ℝ)| + |(0 : ℝ)| ≤ 3 := by
      rw [abs_of_nonneg ht₀.1, abs_of_nonneg (by linarith [ht₀.2] : 0 ≤ 1 - t₀)]
      norm_num
    have hQ : Q = t₀ • H u i x + (1 - t₀) • H v i x +
        (0 : ℝ) • H u i y + (0 : ℝ) • H v i y := by
      dsimp [Q, Kx, Hx]
      module
    have hs' : 1 - s₀ ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hs₀.2], by linarith [hs₀.1]⟩
    have hctl := hcontrolled hu hv hx hy (1 - s₀) hs'
      t₀ (1 - t₀) 0 0 hcoeff Q hQ
    have heq : A i x + Kx + (1 - s₀) • ((A i y + Kx) - (A i x + Kx)) +
        t₀ • Dx = (1 - (1 - s₀)) • A i x + (1 - s₀) • A i y + Q := by
      dsimp [Q, Dx, Hx, Kx]
      module
    rw [heq]
    exact hctl
  have hbase2 (s₀ t₀ : ℝ) (hs₀ : s₀ ∈ Icc (0 : ℝ) 1)
      (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
      (A i y + Kx + (1 - s₀) • ((A i y + Ky) - (A i y + Kx)) +
        t₀ • Dy).PosDef ∧
        ‖(A i y + Kx + (1 - s₀) • ((A i y + Ky) - (A i y + Kx)) +
          t₀ • Dy)⁻¹‖ ≤ M := by
    let Q : Matrix (Fin n) (Fin n) ℂ :=
      s₀ • Kx + (1 - s₀ - t₀) • Ky + t₀ • Hy
    have habs : |1 - s₀ - t₀| ≤ 1 := by
      rw [abs_le]
      constructor <;> nlinarith [hs₀.1, hs₀.2, ht₀.1, ht₀.2]
    have hcoeff : |(0 : ℝ)| + |s₀| + |t₀| + |1 - s₀ - t₀| ≤ 3 := by
      rw [abs_of_nonneg hs₀.1, abs_of_nonneg ht₀.1, abs_of_nonneg (by norm_num : 0 ≤ (0 : ℝ))]
      nlinarith [hs₀.2, ht₀.2]
    have hQ : Q = (0 : ℝ) • H u i x + s₀ • H v i x + t₀ • H u i y +
        (1 - s₀ - t₀) • H v i y := by
      dsimp [Q, Kx, Ky, Hy]
      module
    obtain ⟨hQherm, hQnorm⟩ := small_four_jet_combination
      α S A H ctrl hx hy (le_of_lt hr) hu hv hsmall 0 s₀ t₀ (1 - s₀ - t₀)
      hcoeff Q hQ
    have hctrl := ctrl.smallHermitian i y y hy hy 0 (by norm_num) Q hQherm hQnorm
    have heq : A i y + Kx + (1 - s₀) • ((A i y + Ky) - (A i y + Kx)) +
        t₀ • Dy = A i y + Q := by
      dsimp [Q, Kx, Ky, Hy, Dy]
      module
    rw [heq]
    simpa using hctrl
  have hfixedSegment (s₀ : ℝ) (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
      (A i y + Kx + (1 - s₀) • Dy + s₀ • Dx).PosDef ∧
        ‖(A i y + Kx + (1 - s₀) • Dy + s₀ • Dx)⁻¹‖ ≤ M := by
    let Q : Matrix (Fin n) (Fin n) ℂ :=
      s₀ • Hx + (1 - s₀) • Hy + (1 - s₀) • Kx - (1 - s₀) • Ky
    have h1s : 0 ≤ 1 - s₀ := by linarith [hs₀.2]
    have hsabs : |s₀| = s₀ := abs_of_nonneg hs₀.1
    have h1abs : |1 - s₀| = 1 - s₀ := abs_of_nonneg h1s
    have hnegabs : |-(1 - s₀)| = 1 - s₀ := by rw [abs_neg, h1abs]
    have hcoeff : |s₀| + |1 - s₀| + |1 - s₀| + |-(1 - s₀)| ≤ 3 := by
      calc
        |s₀| + |1 - s₀| + |1 - s₀| + |-(1 - s₀)| =
            s₀ + (1 - s₀) + (1 - s₀) + (1 - s₀) := by rw [hsabs, h1abs, hnegabs]
        _ ≤ 3 := by nlinarith [hs₀.1]
    have hQ : Q = s₀ • H u i x + (1 - s₀) • H v i x +
        (1 - s₀) • H u i y + (-(1 - s₀)) • H v i y := by
      dsimp [Q, Hx, Hy, Kx, Ky]
      module
    obtain ⟨hQherm, hQnorm⟩ := small_four_jet_combination
      α S A H ctrl hx hy (le_of_lt hr) hu hv hsmall s₀ (1 - s₀) (1 - s₀)
      (-(1 - s₀)) hcoeff Q hQ
    have hctrl := ctrl.smallHermitian i y y hy hy 0 (by norm_num) Q hQherm hQnorm
    have heq : A i y + Kx + (1 - s₀) • Dy + s₀ • Dx = A i y + Q := by
      dsimp [Q, Hx, Hy, Kx, Ky, Dx, Dy]
      module
    rw [heq]
    simpa using hctrl
  have hbaseFirst := hCb (A i x + Kx) (A i y + Kx) Dx
    (by intro s₀ hs₀ t₀ ht₀; exact (hbase1 s₀ hs₀ t₀ ht₀).1)
    (by intro s₀ hs₀ t₀ ht₀; exact (hbase1 s₀ hs₀ t₀ ht₀).2)
  have hbaseSecond := hCb (A i y + Kx) (A i y + Ky) Dy
    (by intro s₀ hs₀ t₀ ht₀; exact (hbase2 s₀ hs₀ t₀ ht₀).1)
    (by intro s₀ hs₀ t₀ ht₀; exact (hbase2 s₀ hs₀ t₀ ht₀).2)
  let Qbase : Matrix (Fin n) (Fin n) ℂ := Kx
  have hQbase : Qbase = (0 : ℝ) • H u i x + (1 : ℝ) • H v i x +
      (0 : ℝ) • H u i y + (0 : ℝ) • H v i y := by
    dsimp [Qbase, Kx]
    simp
  obtain ⟨hQbaseHerm, hQbaseSmall⟩ := small_four_jet_combination
    α S A H ctrl hx hy (le_of_lt hr) hu hv hsmall 0 1 0 0
    (by norm_num) Qbase hQbase
  have hbaseCtrl := ctrl.smallHermitian i y y hy hy 0 (by norm_num)
    Qbase hQbaseHerm hQbaseSmall
  have hbasePD : (A i y + Kx).PosDef := by simpa [Qbase] using hbaseCtrl.1
  have hbaseInv : ‖(A i y + Kx)⁻¹‖ ≤ M := by
    simpa [Qbase, M] using hbaseCtrl.2
  let μ : ℝ := Real.sqrt (Fintype.card (Fin n) : ℝ) / (M : ℝ)
  have hncard : 0 < (Fintype.card (Fin n) : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (Fintype.card (Fin n) : ℝ) := Real.sqrt_pos.2 hncard
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast ctrl.inverseBound_pos
  have hμ : 0 < μ := by dsimp [μ]; exact div_pos hsqrt hMpos
  have hratio : Real.sqrt (Fintype.card (Fin n) : ℝ) / μ = (M : ℝ) := by
    dsimp [μ]
    field_simp [ne_of_gt hsqrt, ne_of_gt hMpos]
  have hscaleSq : (Fintype.card (Fin n) : ℝ) / μ ^ 2 = (M : ℝ) ^ 2 := by
    dsimp [μ]
    rw [div_pow, Real.sq_sqrt (le_of_lt hncard)]
    field_simp [ne_of_gt hMpos]
  have hbaseInv' : ‖(A i y + Kx)⁻¹‖ ≤
      Real.sqrt (Fintype.card (Fin n) : ℝ) / μ := by rw [hratio]; exact hbaseInv
  have hfixed' : ∀ s₀ ∈ Icc (0 : ℝ) 1,
      ‖(A i y + Kx + (1 - s₀) • Dy + s₀ • Dx)⁻¹‖ ≤
        Real.sqrt (Fintype.card (Fin n) : ℝ) / μ := by
    intro s₀ hs₀
    rw [hratio]
    exact (hfixedSegment s₀ hs₀).2
  have hfixedRaw := hfixed (A i y + Kx) Dx Dy μ hμ hbasePD hbaseInv'
    (by intro s₀ hs₀; exact (hfixedSegment s₀ hs₀).1) hfixed'
  have hzero : (0 : Matrix (Fin n) (Fin n) ℂ) =
      (0 : ℝ) • H u i x + (0 : ℝ) • H v i x +
        (0 : ℝ) • H u i y + (0 : ℝ) • H v i y := by simp
  have hAxCtrl := hcontrolled hu hv hx hy 0 (by norm_num) 0 0 0 0
    (by norm_num) (0 : Matrix (Fin n) (Fin n) ℂ) hzero
  have hAyCtrl := hcontrolled hu hv hx hy 1 (by norm_num) 0 0 0 0
    (by norm_num) (0 : Matrix (Fin n) (Fin n) ℂ) hzero
  have hKxEq : Kx = (0 : ℝ) • H u i x + (1 : ℝ) • H v i x +
      (0 : ℝ) • H u i y + (0 : ℝ) • H v i y := hQbase
  have hKyEq : Ky = (0 : ℝ) • H u i x + (0 : ℝ) • H v i x +
      (0 : ℝ) • H u i y + (1 : ℝ) • H v i y := by
    dsimp [Ky]
    simp
  have hUxCtrl := hcontrolled hu hv hx hy 0 (by norm_num) 0 1 0 0
    (by norm_num) Kx hKxEq
  have hUyCtrl := hcontrolled hu hv hx hy 1 (by norm_num) 0 0 0 1
    (by norm_num) Ky hKyEq
  have hAx : (A i x).PosDef := by simpa using hAxCtrl.1
  have hAy : (A i y).PosDef := by simpa using hAyCtrl.1
  have hUx : (A i x + Kx).PosDef := by simpa using hUxCtrl.1
  have hUy : (A i y + Ky).PosDef := by simpa using hUyCtrl.1
  have hAxInv : ‖(A i x)⁻¹‖ ≤ (M : ℝ) := by simpa [M] using hAxCtrl.2
  have hAyInv : ‖(A i y)⁻¹‖ ≤ (M : ℝ) := by simpa [M] using hAyCtrl.2
  have hUxInv : ‖(A i x + Kx)⁻¹‖ ≤ (M : ℝ) := by simpa [M] using hUxCtrl.2
  have hUyInv : ‖(A i y + Ky)⁻¹‖ ≤ (M : ℝ) := by simpa [M] using hUyCtrl.2
  have hKxNorm : ‖Kx‖ ≤ (c : ℝ) * ‖v‖ := by
    dsimp [Kx, c]
    have h := holderBoundOn_zero_value (ctrl.jetHolder v i) hx
    simpa [NNReal.coe_mul] using h
  have hKyNorm : ‖Ky‖ ≤ (c : ℝ) * ‖v‖ := by
    dsimp [Ky, c]
    have h := holderBoundOn_zero_value (ctrl.jetHolder v i) hy
    simpa [NNReal.coe_mul] using h
  have hDxEq : Dx = H (u - v) i x := by
    dsimp [Dx, Hx, Kx]
    exact (ctrl.jet_sub u v i x hx).symm
  have hDyEq : Dy = H (u - v) i y := by
    dsimp [Dy, Hy, Ky]
    exact (ctrl.jet_sub u v i y hy).symm
  have hDxNorm : ‖Dx‖ ≤ (c : ℝ) * dnorm := by
    rw [hDxEq]
    dsimp [dnorm, c]
    exact holderBoundOn_zero_value (ctrl.jetHolder (u - v) i) hx
  have hDyNorm : ‖Dy‖ ≤ (c : ℝ) * dnorm := by
    rw [hDyEq]
    dsimp [dnorm, c]
    exact holderBoundOn_zero_value (ctrl.jetHolder (u - v) i) hy
  have hAxAy : ‖A i x - A i y‖ ≤ (G : ℝ) * τ := by
    dsimp [τ, G]
    exact holderBoundOn_zero_normDiff (ctrl.baseHolder i) hx hy
  have hKxKy : ‖Kx - Ky‖ ≤ ((c : ℝ) * ‖v‖) * τ := by
    rw [show Kx = H v i x by rfl, show Ky = H v i y by rfl]
    have h := holderBoundOn_zero_normDiff (ctrl.jetHolder v i) hx hy
    simpa [τ, c, NNReal.coe_mul, mul_assoc] using h
  have hDxDy : ‖Dx - Dy‖ ≤ ((c : ℝ) * dnorm) * τ := by
    rw [hDxEq, hDyEq]
    have h := holderBoundOn_zero_normDiff (ctrl.jetHolder (u - v) i) hx hy
    simpa [τ, dnorm, c, NNReal.coe_mul, mul_assoc] using h
  let Q : ℝ := (c : ℝ) * ‖v‖
  let Δ : ℝ := (c : ℝ) * dnorm
  let a : ℝ := ((G : ℝ) + Q) * τ
  let k : ℝ := Q * τ
  let d : ℝ := Δ * τ
  have hQnonneg : 0 ≤ Q := by positivity
  have hΔnonneg : 0 ≤ Δ := by positivity
  have hanonneg : 0 ≤ a := by positivity
  have hknonneg : 0 ≤ k := by positivity
  have hdnonneg : 0 ≤ d := by positivity
  have hAxAy' : ‖A i x - A i y‖ ≤ a := by
    dsimp [a, Q]
    calc
      ‖A i x - A i y‖ ≤ (G : ℝ) * τ := hAxAy
      _ ≤ ((G : ℝ) + (c : ℝ) * ‖v‖) * τ := by
        apply mul_le_mul_of_nonneg_right
        · exact le_add_of_nonneg_right (by positivity)
        · exact Real.rpow_nonneg (dist_nonneg) _
  have hKxKy' : ‖Kx - Ky‖ ≤ k := by
    simpa [k, Q] using hKxKy
  have hDxBound : ‖Dx‖ ≤ Δ := by simpa [Δ] using hDxNorm
  have hDyBound : ‖Dy‖ ≤ Δ := by simpa [Δ] using hDyNorm
  have hDxDy' : ‖Dx - Dy‖ ≤ d := by simpa [d, Δ] using hDxDy
  have hbase1Diff : ‖(A i x + Kx) - (A i y + Kx)‖ ≤ a := by
    have heq : (A i x + Kx) - (A i y + Kx) = A i x - A i y := by abel
    rw [heq]
    exact hAxAy'
  have hbase2Diff : ‖(A i y + Kx) - (A i y + Ky)‖ ≤ a := by
    have heq : (A i y + Kx) - (A i y + Ky) = Kx - Ky := by abel
    rw [heq]
    calc
      ‖Kx - Ky‖ ≤ k := hKxKy'
      _ ≤ a := by
        dsimp [k, a, Q]
        have hG : 0 ≤ (G : ℝ) := NNReal.coe_nonneg G
        have htau : 0 ≤ τ := Real.rpow_nonneg (dist_nonneg) _
        nlinarith
  have hbasePair1 :
      |Matrix.logDetTaylorRemainder (A i x + Kx) Dx -
        Matrix.logDetTaylorRemainder (A i y + Kx) Dx| ≤
        (Cb : ℝ) * a * Δ ^ 2 := by
    calc
      _ ≤ (Cb : ℝ) * ‖(A i x + Kx) - (A i y + Kx)‖ * ‖Dx‖ ^ 2 := hbaseFirst
      _ ≤ (Cb : ℝ) * a * Δ ^ 2 := by
        have hCbnonneg : 0 ≤ (Cb : ℝ) := NNReal.coe_nonneg Cb
        have hsq : ‖Dx‖ ^ 2 ≤ Δ ^ 2 := by
          nlinarith [hDxBound, norm_nonneg Dx, hΔnonneg]
        calc
          (Cb : ℝ) * ‖(A i x + Kx) - (A i y + Kx)‖ * ‖Dx‖ ^ 2 =
              ((Cb : ℝ) * ‖(A i x + Kx) - (A i y + Kx)‖) * ‖Dx‖ ^ 2 := by ring
          _ ≤ ((Cb : ℝ) * a) * Δ ^ 2 := mul_le_mul
            (mul_le_mul_of_nonneg_left hbase1Diff hCbnonneg) hsq
            (sq_nonneg _) (mul_nonneg hCbnonneg hanonneg)
          _ = (Cb : ℝ) * a * Δ ^ 2 := by ring
  have hbasePair2 :
      |Matrix.logDetTaylorRemainder (A i y + Kx) Dy -
        Matrix.logDetTaylorRemainder (A i y + Ky) Dy| ≤
        (Cb : ℝ) * a * Δ ^ 2 := by
    calc
      _ ≤ (Cb : ℝ) * ‖(A i y + Kx) - (A i y + Ky)‖ * ‖Dy‖ ^ 2 := hbaseSecond
      _ ≤ (Cb : ℝ) * a * Δ ^ 2 := by
        have hCbnonneg : 0 ≤ (Cb : ℝ) := NNReal.coe_nonneg Cb
        have hsq : ‖Dy‖ ^ 2 ≤ Δ ^ 2 := by
          nlinarith [hDyBound, norm_nonneg Dy, hΔnonneg]
        calc
          (Cb : ℝ) * ‖(A i y + Kx) - (A i y + Ky)‖ * ‖Dy‖ ^ 2 =
              ((Cb : ℝ) * ‖(A i y + Kx) - (A i y + Ky)‖) * ‖Dy‖ ^ 2 := by ring
          _ ≤ ((Cb : ℝ) * a) * Δ ^ 2 := mul_le_mul
            (mul_le_mul_of_nonneg_left hbase2Diff hCbnonneg) hsq
            (sq_nonneg _) (mul_nonneg hCbnonneg hanonneg)
          _ = (Cb : ℝ) * a * Δ ^ 2 := by ring
  have hfixedPair :
      |Matrix.logDetTaylorRemainder (A i y + Kx) Dx -
        Matrix.logDetTaylorRemainder (A i y + Kx) Dy| ≤ (M : ℝ) ^ 2 * Δ * d := by
    rw [hscaleSq] at hfixedRaw
    have hmax : max ‖Dx‖ ‖Dy‖ ≤ Δ := max_le_iff.mpr ⟨hDxBound, hDyBound⟩
    calc
      _ ≤ (M : ℝ) ^ 2 * max ‖Dx‖ ‖Dy‖ * ‖Dx - Dy‖ := hfixedRaw
      _ ≤ (M : ℝ) ^ 2 * Δ * d := by
        have hM2 : 0 ≤ (M : ℝ) ^ 2 := sq_nonneg _
        calc
          (M : ℝ) ^ 2 * max ‖Dx‖ ‖Dy‖ * ‖Dx - Dy‖ =
              ((M : ℝ) ^ 2 * max ‖Dx‖ ‖Dy‖) * ‖Dx - Dy‖ := by ring
          _ ≤ ((M : ℝ) ^ 2 * Δ) * d := mul_le_mul
            (mul_le_mul_of_nonneg_left hmax hM2) hDxDy'
            (norm_nonneg _) (mul_nonneg hM2 hΔnonneg)
          _ = (M : ℝ) ^ 2 * Δ * d := by ring
  have hPair := matrixDifferenceRemainder_pointwise
    (M : ℝ) Q Δ a k d (Cb : ℝ) ((M : ℝ) ^ 2)
    (A i x) (A i y) Hx Kx Hy Ky
    hQnonneg hanonneg hknonneg
    hAx hAy hUx hUy hAxInv hAyInv hUxInv hUyInv
    hKxNorm hKyNorm hDxBound hAxAy' hKxKy' hDxDy'
    hbasePair1 hbasePair2 hfixedPair (fun U V => abs_re_trace_mul_le_frobenius_test U V)
  have hSnonneg : 0 ≤ snorm := by positivity
  have hDnonneg : 0 ≤ dnorm := by positivity
  have hτnonneg : 0 ≤ τ := Real.rpow_nonneg (dist_nonneg) _
  have hDleS : dnorm ≤ snorm := by exact_mod_cast hdu
  have hDsq : dnorm ^ 2 ≤ snorm * dnorm := by
    calc
      dnorm ^ 2 = dnorm * dnorm := by ring
      _ ≤ snorm * dnorm := mul_le_mul_of_nonneg_right hDleS hDnonneg
  have hvRreal : ‖v‖ ≤ (R : ℝ) := by
    change (‖v‖₊ : ℝ) ≤ (R : ℝ)
    rw [hRcoe]
    exact le_of_lt hv
  have hQleR : Q ≤ (c : ℝ) * (R : ℝ) := by
    dsimp [Q]
    exact mul_le_mul_of_nonneg_left hvRreal (NNReal.coe_nonneg c)
  have hQleS : Q ≤ (c : ℝ) * snorm := by
    dsimp [Q, snorm]
    apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg c)
    have hvle : ‖v‖ ≤ ‖u‖ + ‖v‖ := le_add_of_nonneg_left (norm_nonneg u)
    exact hvle
  have haBound : a ≤ ((G : ℝ) + (c : ℝ) * (R : ℝ)) * τ := by
    dsimp [a]
    have hsum : (G : ℝ) + Q ≤ (G : ℝ) + (c : ℝ) * (R : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_right hsum hτnonneg
  have hkBoundS : k ≤ ((c : ℝ) * snorm) * τ := by
    dsimp [k]
    exact mul_le_mul_of_nonneg_right hQleS hτnonneg
  have hkBoundR : k ≤ ((c : ℝ) * (R : ℝ)) * τ := by
    dsimp [k]
    exact mul_le_mul_of_nonneg_right hQleR hτnonneg
  have hbracketSpatial : Q * (2 * a + k) + k ≤
      ((c : ℝ) * snorm) * ((2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ) + 1) * τ) := by
    have hlin : 2 * a + k ≤ (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) * τ := by
      calc
        2 * a + k ≤ 2 * (((G : ℝ) + (c : ℝ) * (R : ℝ)) * τ) +
            ((c : ℝ) * (R : ℝ)) * τ :=
              add_le_add (mul_le_mul_of_nonneg_left haBound (by norm_num)) hkBoundR
        _ = (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) * τ := by ring
    calc
      Q * (2 * a + k) + k ≤ Q * ((2 * (G : ℝ) +
          3 * (c : ℝ) * (R : ℝ)) * τ) + k := by
        exact add_le_add (mul_le_mul_of_nonneg_left hlin hQnonneg) le_rfl
      _ ≤ Q * ((2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) * τ) +
          ((c : ℝ) * snorm) * τ := add_le_add le_rfl hkBoundS
      _ ≤ ((c : ℝ) * snorm) * ((2 * (G : ℝ) +
          3 * (c : ℝ) * (R : ℝ) + 1) * τ) := by
        have hcoef : 0 ≤ 2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ) := by positivity
        have hprod : Q * (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) ≤
            ((c : ℝ) * snorm) * (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) :=
          mul_le_mul_of_nonneg_right hQleS hcoef
        have hprodτ : Q * ((2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) * τ) ≤
            ((c : ℝ) * snorm) * (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) * τ := by
          calc
            Q * ((2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) * τ) =
                (Q * (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ))) * τ := by ring
            _ ≤ (((c : ℝ) * snorm) * (2 * (G : ℝ) +
                3 * (c : ℝ) * (R : ℝ))) * τ :=
                  mul_le_mul_of_nonneg_right hprod hτnonneg
        calc
          Q * ((2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) * τ) +
              ((c : ℝ) * snorm) * τ ≤
              ((c : ℝ) * snorm) * (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ)) * τ +
                ((c : ℝ) * snorm) * τ := add_le_add hprodτ le_rfl
          _ = ((c : ℝ) * snorm) *
              ((2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ) + 1) * τ) := by ring
  have hbaseMajor : 2 * (Cb : ℝ) * a * Δ ^ 2 ≤
      (2 * (Cb : ℝ) * ((G : ℝ) + (c : ℝ) * (R : ℝ)) * (c : ℝ) ^ 2) *
        snorm * dnorm * τ := by
    have hΔsq : Δ ^ 2 = ((c : ℝ) * dnorm) ^ 2 := by rfl
    have hcoef : 0 ≤ 2 * (Cb : ℝ) * ((G : ℝ) + (c : ℝ) * (R : ℝ)) * (c : ℝ) ^ 2 := by
      positivity
    calc
      2 * (Cb : ℝ) * a * Δ ^ 2 ≤
          2 * (Cb : ℝ) * (((G : ℝ) + (c : ℝ) * (R : ℝ)) * τ) *
            ((c : ℝ) * dnorm) ^ 2 := by
        rw [hΔsq]
        calc
          2 * (Cb : ℝ) * a * ((c : ℝ) * dnorm) ^ 2 =
              (2 * (Cb : ℝ) * a) * ((c : ℝ) * dnorm) ^ 2 := by ring
          _ ≤ (2 * (Cb : ℝ) * (((G : ℝ) + (c : ℝ) * (R : ℝ)) * τ)) *
                ((c : ℝ) * dnorm) ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left haBound (by positivity))
                (sq_nonneg ((c : ℝ) * dnorm))
          _ = 2 * (Cb : ℝ) * (((G : ℝ) + (c : ℝ) * (R : ℝ)) * τ) *
                ((c : ℝ) * dnorm) ^ 2 := by ring
      _ = (2 * (Cb : ℝ) * ((G : ℝ) + (c : ℝ) * (R : ℝ)) * (c : ℝ) ^ 2) *
          (dnorm ^ 2) * τ := by ring
      _ ≤ (2 * (Cb : ℝ) * ((G : ℝ) + (c : ℝ) * (R : ℝ)) * (c : ℝ) ^ 2) *
          snorm * dnorm * τ := by
        calc
          (2 * (Cb : ℝ) * ((G : ℝ) + (c : ℝ) * (R : ℝ)) * (c : ℝ) ^ 2) *
              dnorm ^ 2 * τ ≤
            (2 * (Cb : ℝ) * ((G : ℝ) + (c : ℝ) * (R : ℝ)) * (c : ℝ) ^ 2) *
              (snorm * dnorm) * τ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hDsq hcoef) hτnonneg
          _ = (2 * (Cb : ℝ) * ((G : ℝ) + (c : ℝ) * (R : ℝ)) * (c : ℝ) ^ 2) *
              snorm * dnorm * τ := by ring
  have hfixedMajor : (M : ℝ) ^ 2 * Δ * d ≤
      ((M : ℝ) ^ 2 * (c : ℝ) ^ 2) * snorm * dnorm * τ := by
    have hcoef : 0 ≤ (M : ℝ) ^ 2 * (c : ℝ) ^ 2 := by positivity
    dsimp [d, Δ]
    calc
      (M : ℝ) ^ 2 * ((c : ℝ) * dnorm) * ((c : ℝ) * dnorm * τ) =
          ((M : ℝ) ^ 2 * (c : ℝ) ^ 2) * dnorm ^ 2 * τ := by ring
      _ ≤ ((M : ℝ) ^ 2 * (c : ℝ) ^ 2) * snorm * dnorm * τ := by
        calc
          ((M : ℝ) ^ 2 * (c : ℝ) ^ 2) * dnorm ^ 2 * τ ≤
              ((M : ℝ) ^ 2 * (c : ℝ) ^ 2) * (snorm * dnorm) * τ := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hDsq hcoef) hτnonneg
          _ = ((M : ℝ) ^ 2 * (c : ℝ) ^ 2) * snorm * dnorm * τ := by ring
  have hbaseMetricMajor : (N : ℝ) ^ 3 *
      (Q * (2 * a + k) + k) * Δ ≤
      ((N : ℝ) ^ 3 * (c : ℝ) ^ 2 *
        (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ) + 1)) * snorm * dnorm * τ := by
    dsimp [Δ]
    have hcoef : 0 ≤ (N : ℝ) ^ 3 * (c : ℝ) ^ 2 := by positivity
    calc
      (N : ℝ) ^ 3 * (Q * (2 * a + k) + k) * ((c : ℝ) * dnorm) ≤
          (N : ℝ) ^ 3 * (((c : ℝ) * snorm) *
            ((2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ) + 1) * τ)) *
            ((c : ℝ) * dnorm) := by gcongr
      _ = ((N : ℝ) ^ 3 * (c : ℝ) ^ 2 *
          (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ) + 1)) *
            snorm * dnorm * τ := by ring
  have hbaseMetricMajor2 : (N : ℝ) ^ 2 * Q * d ≤
      ((N : ℝ) ^ 2 * (c : ℝ) ^ 2) * snorm * dnorm * τ := by
    dsimp [d, Δ]
    have hcoef : 0 ≤ (N : ℝ) ^ 2 * (c : ℝ) ^ 2 := by positivity
    calc
      (N : ℝ) ^ 2 * Q * ((c : ℝ) * dnorm * τ) ≤
          (N : ℝ) ^ 2 * ((c : ℝ) * snorm) * ((c : ℝ) * dnorm * τ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hQleS (by positivity)) (by positivity)
      _ = ((N : ℝ) ^ 2 * (c : ℝ) ^ 2) * snorm * dnorm * τ := by ring
  have hAnearCast : (Anear : ℝ) =
      2 * (Cb : ℝ) * ((G : ℝ) + (c : ℝ) * (R : ℝ)) * (c : ℝ) ^ 2 +
        (M : ℝ) ^ 2 * (c : ℝ) ^ 2 +
        (N : ℝ) ^ 3 * (c : ℝ) ^ 2 *
          (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ) + 1) +
        (N : ℝ) ^ 2 * (c : ℝ) ^ 2 := by
    simp [Anear, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow]
  have hmatrixNear :
      |(Matrix.logDetTaylorRemainder (A i x) (H u i x) -
          Matrix.logDetTaylorRemainder (A i x) (H v i x)) -
        (Matrix.logDetTaylorRemainder (A i y) (H u i y) -
          Matrix.logDetTaylorRemainder (A i y) (H v i y))| ≤
        (Anear : ℝ) * snorm * dnorm * τ := by
    have hsum := add_le_add (add_le_add hbaseMajor hfixedMajor)
      (add_le_add hbaseMetricMajor hbaseMetricMajor2)
    calc
      _ ≤ (Cb : ℝ) * a * Δ ^ 2 + (M : ℝ) ^ 2 * Δ * d +
          (Cb : ℝ) * a * Δ ^ 2 +
          (N : ℝ) ^ 3 * (Q * (2 * a + k) + k) * Δ +
          (N : ℝ) ^ 2 * Q * d := by
        simpa [Hx, Kx, Hy, Ky, N, NNReal.coe_max, add_assoc] using hPair
      _ = 2 * (Cb : ℝ) * a * Δ ^ 2 + (M : ℝ) ^ 2 * Δ * d +
          (N : ℝ) ^ 3 * (Q * (2 * a + k) + k) * Δ +
          (N : ℝ) ^ 2 * Q * d := by ring
      _ = 2 * (Cb : ℝ) * a * Δ ^ 2 + (M : ℝ) ^ 2 * Δ * d +
          ((N : ℝ) ^ 3 * (Q * (2 * a + k) + k) * Δ + (N : ℝ) ^ 2 * Q * d) := by ring
      _ ≤
          (2 * (Cb : ℝ) * ((G : ℝ) + (c : ℝ) * (R : ℝ)) * (c : ℝ) ^ 2) *
            snorm * dnorm * τ + ((M : ℝ) ^ 2 * (c : ℝ) ^ 2) * snorm * dnorm * τ +
          (((N : ℝ) ^ 3 * (c : ℝ) ^ 2 *
            (2 * (G : ℝ) + 3 * (c : ℝ) * (R : ℝ) + 1)) * snorm * dnorm * τ +
            ((N : ℝ) ^ 2 * (c : ℝ) ^ 2) * snorm * dnorm * τ) := by
        simpa [add_assoc] using hsum
      _ = (Anear : ℝ) * snorm * dnorm * τ := by rw [hAnearCast]; ring
  change |(Matrix.logDetTaylorRemainder (A i x) (H u i x) -
      Matrix.logDetTaylorRemainder (A i x) (H v i x)) -
    (Matrix.logDetTaylorRemainder (A i y) (H u i y) -
      Matrix.logDetTaylorRemainder (A i y) (H v i y))| ≤
    snorm * dnorm * ((Anear : ℝ) * τ + (1 : ℝ) * τ ^ 2)
  calc
    _ ≤ (Anear : ℝ) * snorm * dnorm * τ := hmatrixNear
    _ = snorm * dnorm * ((Anear : ℝ) * τ) := by ring
    _ ≤ snorm * dnorm * ((Anear : ℝ) * τ + (1 : ℝ) * τ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (sq_nonneg τ))
      · positivity

private theorem mixedPower_near_far_holder_absorption
    {X : Type*} [MetricSpace X]
    (α S du A B C : ℝ≥0) (f : X → ℝ) (x y : X)
    (hnear : |f x - f y| ≤ (S : ℝ) * (du : ℝ) *
      ((A : ℝ) * dist x y ^ (α : ℝ) +
        (B : ℝ) * (dist x y ^ (α : ℝ)) ^ 2))
    (hpoint_x : |f x| ≤ (C : ℝ) * (S : ℝ) * (du : ℝ))
    (hpoint_y : |f y| ≤ (C : ℝ) * (S : ℝ) * (du : ℝ)) :
    |f x - f y| ≤ ((max (A + B) (2 * C) : ℝ≥0) : ℝ) *
      (S : ℝ) * (du : ℝ) * dist x y ^ (α : ℝ) := by
  let d : ℝ := dist x y
  let τ : ℝ := d ^ (α : ℝ)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hα : 0 ≤ (α : ℝ) := NNReal.coe_nonneg α
  have hτ : 0 ≤ τ := Real.rpow_nonneg hd _
  have hSD : 0 ≤ (S : ℝ) * (du : ℝ) := by positivity
  by_cases hcase : d ≤ 1
  · have hτle : τ ≤ 1 := by
      dsimp [τ, d]
      exact Real.rpow_le_one (dist_nonneg) hcase hα
    have hτsq : τ ^ 2 ≤ τ := by
      calc
        τ ^ 2 = τ * τ := by ring
        _ ≤ 1 * τ := mul_le_mul_of_nonneg_right hτle hτ
        _ = τ := by ring
    have hnear' : |f x - f y| ≤ (S : ℝ) * (du : ℝ) *
        (((A : ℝ) + (B : ℝ)) * τ) := by
      calc
        |f x - f y| ≤ (S : ℝ) * (du : ℝ) *
            ((A : ℝ) * τ + (B : ℝ) * τ ^ 2) := by
              simpa [d, τ] using hnear
        _ ≤ (S : ℝ) * (du : ℝ) * (((A : ℝ) + (B : ℝ)) * τ) :=
          mul_le_mul_of_nonneg_left
            (calc
              (A : ℝ) * τ + (B : ℝ) * τ ^ 2 ≤ (A : ℝ) * τ + (B : ℝ) * τ :=
                add_le_add (le_refl ((A : ℝ) * τ))
                  (mul_le_mul_of_nonneg_left hτsq (NNReal.coe_nonneg B))
              _ = ((A : ℝ) + (B : ℝ)) * τ := by ring) hSD
    have hcoeff : ((A + B : ℝ≥0) : ℝ) ≤ ((max (A + B) (2 * C) : ℝ≥0) : ℝ) := by
      exact_mod_cast (le_max_left (A + B) (2 * C))
    calc
      |f x - f y| ≤ (S : ℝ) * (du : ℝ) * (((A : ℝ) + (B : ℝ)) * τ) := hnear'
      _ = ((A + B : ℝ≥0) : ℝ) * ((S : ℝ) * (du : ℝ) * τ) := by
        simp only [NNReal.coe_add]
        ring
      _ ≤ ((max (A + B) (2 * C) : ℝ≥0) : ℝ) * ((S : ℝ) * (du : ℝ) * τ) := by
        have hfactor : 0 ≤ (S : ℝ) * (du : ℝ) * τ := mul_nonneg hSD hτ
        calc
          ((A + B : ℝ≥0) : ℝ) * ((S : ℝ) * (du : ℝ) * τ) ≤
              ((max (A + B) (2 * C) : ℝ≥0) : ℝ) * ((S : ℝ) * (du : ℝ) * τ) :=
            mul_le_mul_of_nonneg_right hcoeff hfactor
          _ = ((max (A + B) (2 * C) : ℝ≥0) : ℝ) *
              ((S : ℝ) * (du : ℝ) * τ) := by ring
      _ = ((max (A + B) (2 * C) : ℝ≥0) : ℝ) *
          (S : ℝ) * (du : ℝ) * dist x y ^ (α : ℝ) := by ring
  · have hlarge : 1 ≤ d := le_of_not_ge hcase
    have hτge : 1 ≤ τ := by
      dsimp [τ, d]
      exact Real.one_le_rpow hlarge hα
    have hbase : |f x - f y| ≤ 2 * ((C : ℝ) * (S : ℝ) * (du : ℝ)) := by
      calc
        |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ (C : ℝ) * (S : ℝ) * (du : ℝ) +
            (C : ℝ) * (S : ℝ) * (du : ℝ) := add_le_add hpoint_x hpoint_y
        _ = 2 * ((C : ℝ) * (S : ℝ) * (du : ℝ)) := by ring
    have hcoeff : (2 * C : ℝ≥0) ≤ max (A + B) (2 * C) := le_max_right _ _
    have hcoeff' : (2 * (C : ℝ)) ≤ ((max (A + B) (2 * C) : ℝ≥0) : ℝ) := by
      exact_mod_cast hcoeff
    have hfactor : 0 ≤ (S : ℝ) * (du : ℝ) * τ :=
      mul_nonneg hSD (le_trans (by norm_num) hτge)
    calc
      |f x - f y| ≤ 2 * ((C : ℝ) * (S : ℝ) * (du : ℝ)) := hbase
      _ ≤ (2 * (C : ℝ) * (S : ℝ) * (du : ℝ)) * τ := by
        have h := mul_le_mul_of_nonneg_left hτge
          (show 0 ≤ 2 * (C : ℝ) * (S : ℝ) * (du : ℝ) by positivity)
        nlinarith
      _ = (2 * (C : ℝ)) * ((S : ℝ) * (du : ℝ) * τ) := by ring
      _ ≤ ((max (A + B) (2 * C) : ℝ≥0) : ℝ) *
          ((S : ℝ) * (du : ℝ) * τ) := mul_le_mul_of_nonneg_right hcoeff' hfactor
      _ = ((max (A + B) (2 * C) : ℝ≥0) : ℝ) *
          (S : ℝ) * (du : ℝ) * τ := by ring
      _ = ((max (A + B) (2 * C) : ℝ≥0) : ℝ) *
          (S : ℝ) * (du : ℝ) * dist x y ^ (α : ℝ) := by rfl

theorem exists_matrixPairwiseTaylor_holderBound
    {n : ℕ} {U E κ : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ≥0) (S : κ → Set E)
    (A : κ → E → Matrix (Fin n) (Fin n) ℂ)
    (H : U → κ → E → Matrix (Fin n) (Fin n) ℂ)
    (ctrl : ChartTaylorControl α S A H)
    (hfixed : LogDetTaylorRemainderLipschitz n) (hbase : LogDetTaylorRemainderBaseLipschitz n) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      ∀ u v : U, ‖u‖ < r → ‖v‖ < r → ∀ i,
        HolderBoundOn 0 α (C * (‖u‖₊ + ‖v‖₊) * ‖u - v‖₊) (S i)
          (fun z ↦ Matrix.logDetTaylorRemainder (A i z) (H u i z) -
            Matrix.logDetTaylorRemainder (A i z) (H v i z)) := by
  classical
  by_cases hn : 0 < n
  · obtain ⟨Anear, Bnear, r, hr, hrsmall, hnear⟩ :=
      exists_matrixPairwiseTaylor_nearDifferenceBound α S A H ctrl hfixed hbase hn
    let Cpoint : ℝ≥0 := ctrl.inverseBound ^ 2 * ctrl.jetConstant ^ 2
    let C : ℝ≥0 := max (Anear + Bnear) (2 * Cpoint)
    refine ⟨C, r, hr, ?_⟩
    intro u v hu hv i
    let c := C * (‖u‖₊ + ‖v‖₊) * ‖u - v‖₊
    let f : E → ℝ := fun z ↦ Matrix.logDetTaylorRemainder (A i z) (H u i z) -
      Matrix.logDetTaylorRemainder (A i z) (H v i z)
    have hcoeff : Anear + Bnear ≤ C := le_max_left _ _
    have hcoeffFar : 2 * Cpoint ≤ C := le_max_right _ _
    have hcoeffPoint : Cpoint ≤ C := by
      have hmul : Cpoint ≤ 2 * Cpoint := by
        simpa using mul_le_mul_of_nonneg_right
          (show (1 : ℝ≥0) ≤ 2 by norm_num) (NNReal.coe_nonneg Cpoint)
      exact le_trans hmul hcoeffFar
    have hHolder : HolderOnWith c α f (S i) := by
      intro x hx y hy
      have hxy := hnear u v hu hv i x y hx hy
      have hdist : |f x - f y| ≤ (‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊ *
          ((Anear : ℝ) * dist x y ^ (α : ℝ) +
            (Bnear : ℝ) * (dist x y ^ (α : ℝ)) ^ 2) := by
        simpa [f] using hxy
      have hpx0 := fixed_pairwise_pointwise α S A H ctrl hfixed
        hr hrsmall hu hv hx hn
      have hpy0 := fixed_pairwise_pointwise α S A H ctrl hfixed
        hr hrsmall hu hv hy hn
      have hpx : |f x| ≤ (Cpoint : ℝ) *
          (‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊ := by
        simpa [f, Cpoint, mul_assoc, mul_left_comm, mul_comm] using hpx0
      have hpy : |f y| ≤ (Cpoint : ℝ) *
          (‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊ := by
        simpa [f, Cpoint, mul_assoc, mul_left_comm, mul_comm] using hpy0
      have hscalar := mixedPower_near_far_holder_absorption α
        (‖u‖₊ + ‖v‖₊) ‖u - v‖₊ Anear Bnear Cpoint f x y hdist hpx hpy
      have hscalar' : |f x - f y| ≤
          (C : ℝ) * (‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊ * dist x y ^ (α : ℝ) := by
        simpa [C, mul_assoc, mul_left_comm, mul_comm] using hscalar
      rw [edist_dist]
      calc
        ENNReal.ofReal (dist (f x) (f y)) ≤
            ENNReal.ofReal ((c : ℝ) * dist x y ^ (α : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.dist_eq]
          simpa [c, mul_assoc] using hscalar'
        _ = (c : ENNReal) * edist x y ^ (α : ℝ) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          rw [ENNReal.ofReal_coe_nnreal]
          rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg]
          rw [← edist_dist]
    have hbound (x : E) (hx : x ∈ S i) : ‖f x‖ ≤ (c : ℝ) := by
      rw [Real.norm_eq_abs]
      have hpx0 := fixed_pairwise_pointwise α S A H ctrl hfixed
        hr hrsmall hu hv hx hn
      have hpoint : |f x| ≤ (Cpoint : ℝ) *
          (‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊ := by
        simpa [f, Cpoint, mul_assoc, mul_left_comm, mul_comm] using hpx0
      dsimp [c]
      calc
        |f x| ≤ (Cpoint : ℝ) * (‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊ := hpoint
        _ ≤ (C : ℝ) * (‖u‖₊ + ‖v‖₊ : ℝ) * ‖u - v‖₊ := by
          gcongr
    change HolderBoundOn 0 α c (S i) f
    exact holderBoundOn_zero_from_holderOnWith hHolder hbound
  · have hn0 : n = 0 := by omega
    subst n
    refine ⟨0, 1, by norm_num, ?_⟩
    intro u v hu hv i
    apply holderBoundOn_zero_from_holderOnWith
    · intro x hx y hy
      simp [Matrix.logDetTaylorRemainder]
    · intro x hx
      simp [Matrix.logDetTaylorRemainder]

end KahlerForm
