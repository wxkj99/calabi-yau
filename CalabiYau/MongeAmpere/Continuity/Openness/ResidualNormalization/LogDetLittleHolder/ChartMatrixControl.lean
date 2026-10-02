module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.Basic
import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.BoundaryJetIdentity
import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets.CompletedJetHolderWith

/-!
# Full-piece chart matrix control from completed second jets

The norm here is Frobenius. The second real jet gives the complex Hessian through the existing
1/4 formula; summing n² entry estimates gives the safe constant n+1, including n=0. The completed
jet identity must be used on the entire compact piece, not only its interior. C² regularity of
the evaluated limit is an explicit hypothesis, supplied by the parent from limit positivity.
-/

public section

open scoped Manifold ContDiff NNReal Topology ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

private theorem frobenius_norm_le_of_entry_bound {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A‖ ≤ Real.sqrt (Fintype.card (ι × ι) : ℝ) * B := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, pow_two]
  calc
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ * ‖A i j‖) ≤
        Real.sqrt ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * (B * B)) := by
      apply Real.sqrt_le_sqrt
      calc
        (∑ i, ∑ j, ‖A i j‖ * ‖A i j‖) ≤ ∑ i, ∑ j, B * B := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul (hA i j) (hA i j) (norm_nonneg _) hB
        _ = (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * (B * B) := by
          simp [mul_assoc]
    _ = Real.sqrt (Fintype.card (ι × ι) : ℝ) * B := by
      rw [Fintype.card_prod, Nat.cast_mul, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul_self hB]

private theorem complexHessian_entry_bound_of_secondJet
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (B : ℝ)
    (hD : ‖iteratedFDeriv ℝ 2 f z‖ ≤ B) (j k : Fin n) :
    ‖complexHessian f z j k‖ ≤ B := by
  rw [complexHessian_apply hf j k]
  have hunit : ∀ l : Fin n, ‖EuclideanSpace.single l (1 : ℂ)‖ = 1 := by
    intro l
    rw [PiLp.norm_single]
    norm_num
  have hIunit : ∀ l : Fin n, ‖(Complex.I : ℂ) • EuclideanSpace.single l (1 : ℂ)‖ = 1 := by
    intro l
    rw [norm_smul, Complex.norm_I, hunit]
    norm_num
  have hEval (a b : EuclideanSpace ℂ (Fin n)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
      ‖fderiv ℝ (fderiv ℝ f) z a b‖ ≤ B := by
    have hjet : (iteratedFDeriv ℝ 2 f z) ![a, b] =
        fderiv ℝ (fderiv ℝ f) z a b := by
      calc
        (iteratedFDeriv ℝ 2 f z) ![a, b] =
            fderiv ℝ (fderiv ℝ f) z (![a, b] 0) (![a, b] 1) :=
          iteratedFDeriv_two_apply (𝕜 := ℝ) f z ![a, b]
        _ = fderiv ℝ (fderiv ℝ f) z a b := by simp
    rw [← hjet]
    calc
      ‖(iteratedFDeriv ℝ 2 f z) ![a, b]‖ ≤
          ‖iteratedFDeriv ℝ 2 f z‖ * ∏ q : Fin 2, ‖![a, b] q‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 2 f z‖ := by simp [ha, hb]
      _ ≤ B := hD
  have h₁ := hEval (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
    (hunit j) (hunit k)
  have h₂ := hEval (Complex.I • EuclideanSpace.single j 1) (Complex.I • EuclideanSpace.single k 1)
    (hIunit j) (hIunit k)
  have h₃ := hEval (EuclideanSpace.single j 1) (Complex.I • EuclideanSpace.single k 1)
    (hunit j) (hIunit k)
  have h₄ := hEval (Complex.I • EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
    (hIunit j) (hunit k)
  have hcomplex : ‖((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
      (EuclideanSpace.single k 1) : ℂ) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) +
        Complex.I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) -
          fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
            (EuclideanSpace.single k 1)))‖ ≤ 4 * B := by
    let x : ℂ := fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
      (EuclideanSpace.single k 1)
    let y : ℂ := fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
      (Complex.I • EuclideanSpace.single k 1)
    let u : ℂ := fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
      (Complex.I • EuclideanSpace.single k 1)
    let w : ℂ := fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
      (EuclideanSpace.single k 1)
    have hx : ‖x‖ ≤ B := by simpa [x] using
      (show ‖(↑(fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1)) : ℂ)‖ ≤ B by exact_mod_cast h₁)
    have hy : ‖y‖ ≤ B := by simpa [y] using
      (show ‖(↑(fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1)) : ℂ)‖ ≤ B by exact_mod_cast h₂)
    have hu : ‖u‖ ≤ B := by simpa [u] using
      (show ‖(↑(fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1)) : ℂ)‖ ≤ B by exact_mod_cast h₃)
    have hw : ‖w‖ ≤ B := by simpa [w] using
      (show ‖(↑(fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1)) : ℂ)‖ ≤ B by exact_mod_cast h₄)
    change ‖x + y + Complex.I * (u - w)‖ ≤ 4 * B
    calc
      ‖x + y + Complex.I * (u - w)‖ ≤ ‖x + y‖ + ‖Complex.I * (u - w)‖ := norm_add_le _ _
      _ ≤ ‖x‖ + ‖y‖ + (‖u‖ + ‖w‖) := by
        rw [norm_mul, Complex.norm_I]
        simpa using add_le_add (norm_add_le x y) (norm_sub_le u w)
      _ ≤ B + B + (B + B) := by nlinarith [hx, hy, hu, hw]
      _ = 4 * B := by ring
  rw [norm_div]
  norm_num
  calc
    ‖((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) : ℂ) +
      fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1) +
      Complex.I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1) -
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1)))‖ / 4 ≤ (4 * B) / 4 := by
      gcongr
    _ = B := by ring

private theorem complexHessian_frobenius_bound_of_secondJet
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (B : ℝ) (hB : 0 ≤ B)
    (hD : ‖iteratedFDeriv ℝ 2 f z‖ ≤ B) :
    ‖complexHessian f z‖ ≤ ((n + 1 : ℕ) : ℝ) * B := by
  have hentry : ∀ j k, ‖complexHessian f z j k‖ ≤ B :=
    fun j k => complexHessian_entry_bound_of_secondJet hf B hD j k
  have hcard : Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) = n := by
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    rw [Real.sqrt_mul_self (by positivity)]
  calc
    ‖complexHessian f z‖ ≤ Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * B :=
      frobenius_norm_le_of_entry_bound _ B hB hentry
    _ = (n : ℝ) * B := by rw [hcard]
    _ ≤ ((n + 1 : ℕ) : ℝ) * B := by
      gcongr
      exact_mod_cast Nat.le_succ n

private theorem matrix_holder_bound {ι : Type*} [Fintype ι]
    {X : Type*} [PseudoMetricSpace X] {K : Set X} {α C : ℝ≥0}
    (A : X → Matrix ι ι ℂ)
    (hentry : ∀ i j, HolderOnWith C α (fun x => A x i j) K) :
    HolderOnWith (((Fintype.card ι : ℝ≥0) + 1) * C) α A K := by
  intro x hx y hy
  let B : ℝ := (C : ℝ) * dist x y ^ (α : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : ∀ i j, ‖(A x - A y) i j‖ ≤ B := by
    intro i j
    have h := (hentry i j).dist_le hx hy
    dsimp [B]
    simpa only [dist_eq_norm, Matrix.sub_apply] using h
  have hnorm := frobenius_norm_le_of_entry_bound (A x - A y) B hB hA
  have hcard : Real.sqrt (Fintype.card (ι × ι) : ℝ) = (Fintype.card ι : ℝ) := by
    rw [Fintype.card_prod, Nat.cast_mul]
    rw [Real.sqrt_mul_self (by positivity)]
  have hnorm' : ‖A x - A y‖ ≤ ((Fintype.card ι : ℝ) + 1) * B := by
    calc
      ‖A x - A y‖ ≤ Real.sqrt (Fintype.card (ι × ι) : ℝ) * B := hnorm
      _ = (Fintype.card ι : ℝ) * B := by rw [hcard]
      _ ≤ ((Fintype.card ι : ℝ) + 1) * B := by
        nlinarith [mul_nonneg (show 0 ≤ (Fintype.card ι : ℝ) by positivity) hB]
  calc
    edist (A x) (A y) = ENNReal.ofReal (‖A x - A y‖) := by
      rw [edist_dist, dist_eq_norm]
    _ ≤ ENNReal.ofReal (((Fintype.card ι : ℝ) + 1) * (C : ℝ) *
        dist x y ^ (α : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      simpa [B, mul_assoc] using hnorm'
    _ = ENNReal.ofNNReal (((Fintype.card ι : ℝ≥0) + 1) * C) *
        edist x y ^ (α : ℝ) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_coe_nnreal]
      rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
      rw [ENNReal.ofReal_add (by norm_num)]
      simp only [ENNReal.ofReal_one, ENNReal.ofReal_natCast]
      push_cast
      ring
      norm_num

private theorem hessian_entry_holder_of_jet_holder
    {n : ℕ} {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderOnWith C α (fun z => iteratedFDeriv ℝ 2 f z) K)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n) :
    HolderOnWith C α (fun z => complexHessian f z i j) K := by
  let u : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iu := Complex.I • u
  let iv := Complex.I • v
  let D := iteratedFDeriv ℝ 2 f
  have hu : ‖u‖ = 1 := by simp [u]
  have hv : ‖v‖ = 1 := by simp [v]
  have hiu : ‖iu‖ = 1 := by simp [iu, hu, norm_smul, Complex.norm_I]
  have hiv : ‖iv‖ = 1 := by simp [iv, hv, norm_smul, Complex.norm_I]
  have hform (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
      complexHessian f z i j =
        ((D z ![u, v] : ℂ) + D z ![iu, iv] +
          Complex.I * (D z ![u, iv] - D z ![iu, v])) / 4 := by
    rw [complexHessian_apply (hSmooth z hz) i j]
    rw [show fderiv ℝ (fderiv ℝ f) z u v = D z ![u, v] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![u, v]).symm,
      show fderiv ℝ (fderiv ℝ f) z iu iv = D z ![iu, iv] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![iu, iv]).symm,
      show fderiv ℝ (fderiv ℝ f) z u iv = D z ![u, iv] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![u, iv]).symm,
      show fderiv ℝ (fderiv ℝ f) z iu v = D z ![iu, v] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![iu, v]).symm]
  have hD (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ K)
      (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ K) :
      ‖D x - D y‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hf.dist_le hx hy
  have hEval (T : (EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ))
      (w : Fin 2 → EuclideanSpace ℂ (Fin n)) (hw : ∀ k, ‖w k‖ = 1) :
      ‖T w‖ ≤ ‖T‖ := by
    calc
      ‖T w‖ ≤ ‖T‖ * ∏ k, ‖w k‖ := ContinuousMultilinearMap.le_opNorm T w
      _ = ‖T‖ := by simp [hw]
  have huvv (w : Fin 2 → EuclideanSpace ℂ (Fin n))
      (w0 : ‖w 0‖ = 1) (w1 : ‖w 1‖ = 1) : ∀ k, ‖w k‖ = 1 := by
    intro k
    fin_cases k
    · exact w0
    · exact w1
  have hdiff (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ K)
      (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ K) :
      complexHessian f x i j - complexHessian f y i j =
        (((D x - D y) ![u, v] : ℂ) + (D x - D y) ![iu, iv] +
          Complex.I * ((D x - D y) ![u, iv] - (D x - D y) ![iu, v])) / 4 := by
    rw [hform x hx, hform y hy]
    simp only [sub_apply]
    field_simp
    push_cast
    ring
  intro x hx y hy
  rw [edist_dist]
  have hnum :
      ‖(((D x - D y) ![u, v] : ℝ) : ℂ) + (D x - D y) ![iu, iv] +
        Complex.I * ((D x - D y) ![u, iv] - (D x - D y) ![iu, v])‖ ≤
      4 * ‖D x - D y‖ := by
    have h1 := hEval (D x - D y) ![u, v] (huvv _ hu hv)
    have h2 := hEval (D x - D y) ![iu, iv] (huvv _ hiu hiv)
    have h3 := hEval (D x - D y) ![u, iv] (huvv _ hu hiv)
    have h4 := hEval (D x - D y) ![iu, v] (huvv _ hiu hv)
    let a : ℝ := (D x) ![u, v]
    let b : ℝ := (D x) ![iu, iv]
    let c : ℝ := (D x) ![u, iv]
    let d : ℝ := (D x) ![iu, v]
    let a' : ℝ := (D y) ![u, v]
    let b' : ℝ := (D y) ![iu, iv]
    let c' : ℝ := (D y) ![u, iv]
    let d' : ℝ := (D y) ![iu, v]
    have h1C : ‖Complex.ofReal a - Complex.ofReal a'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [a, a', sub_apply] using h1
    have h2C : ‖Complex.ofReal b - Complex.ofReal b'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [b, b', sub_apply] using h2
    have h3C : ‖Complex.ofReal c - Complex.ofReal c'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [c, c', sub_apply] using h3
    have h4C : ‖Complex.ofReal d - Complex.ofReal d'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [d, d', sub_apply] using h4
    have hrest : ‖Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
        (Complex.ofReal d - Complex.ofReal d'))‖ ≤
        ‖D x - D y‖ + ‖D x - D y‖ := by
      rw [norm_mul, Complex.norm_I]
      simpa only [one_mul] using (norm_sub_le _ _).trans (add_le_add h3C h4C)
    have htri : ‖Complex.ofReal (a - a') + Complex.ofReal (b - b') +
        Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
          (Complex.ofReal d - Complex.ofReal d'))‖ ≤
        ‖Complex.ofReal (a - a')‖ + ‖Complex.ofReal (b - b')‖ +
          ‖D x - D y‖ + ‖D x - D y‖ := by
      calc
        _ ≤ ‖Complex.ofReal (a - a') + Complex.ofReal (b - b')‖ +
            ‖Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
              (Complex.ofReal d - Complex.ofReal d'))‖ := norm_add_le _ _
        _ ≤ _ := by exact add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have h := add_le_add_left hrest
            (‖Complex.ofReal (a - a')‖ + ‖Complex.ofReal (b - b')‖)
          nlinarith
    calc
      _ = ‖Complex.ofReal (a - a') + Complex.ofReal (b - b') +
          Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
            (Complex.ofReal d - Complex.ofReal d'))‖ := by
        simp [a, b, c, d, a', b', c', d', Complex.ofReal_sub]
      _ ≤ ‖D x - D y‖ + ‖D x - D y‖ +
          (‖D x - D y‖ + ‖D x - D y‖) := by
        have h1R : ‖Complex.ofReal (a - a')‖ ≤ ‖D x - D y‖ := by
          simpa [Complex.norm_real] using h1C
        have h2R : ‖Complex.ofReal (b - b')‖ ≤ ‖D x - D y‖ := by
          simpa [Complex.norm_real] using h2C
        have hrest' := hrest
        nlinarith [htri, h1R, h2R, hrest']
      _ = 4 * ‖D x - D y‖ := by ring
  calc
    ENNReal.ofReal (dist (complexHessian f x i j) (complexHessian f y i j)) =
        ENNReal.ofReal ‖complexHessian f x i j - complexHessian f y i j‖ := by
          rw [dist_eq_norm]
    _ ≤ ENNReal.ofReal (‖D x - D y‖) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hdiff x hx y hy, norm_div, Complex.norm_ofNat]
      calc
        ‖(((D x - D y) ![u, v] : ℝ) : ℂ) + (D x - D y) ![iu, iv] +
            Complex.I * ((D x - D y) ![u, iv] - (D x - D y) ![iu, v])‖ / 4 ≤
            (4 * ‖D x - D y‖) / 4 := div_le_div_of_nonneg_right hnum (by positivity)
        _ = ‖D x - D y‖ := by norm_num
    _ ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (α : ℝ)) :=
      ENNReal.ofReal_le_ofReal (hD x hx y hy)
    _ = (C : ENNReal) * edist x y ^ (α : ℝ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
      rw [ENNReal.ofReal_coe_nnreal]

private theorem chart_smoothCore_contDiffAt
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0)
    (v : SmoothChartHolderCore cover 2 α) (i : cover.ι)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ cover.piece i) :
    ContDiffAt ℝ 2 (v.smoothMap ∘
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  have hz' : z ∈ e.target := cover.piece_in_target i hz
  have hx : e.symm z ∈ e.source := e.map_target hz'
  have he : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z :=
    (contMDiffOn_extChartAt_symm (cover.base i)).contMDiffAt
      ((isOpen_extChartAt_target (cover.base i)).mem_nhds hz')
  have hv : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      v.smoothMap (e.symm z) := v.smoothMap.contMDiff (e.symm z)
  have hcomp : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (v.smoothMap ∘ e.symm) z := hv.comp_of_eq he rfl
  have hcomp' : ContDiffAt ℝ ∞ (v.smoothMap ∘ e.symm) z :=
    (contMDiffAt_iff_contDiffAt).mp hcomp
  exact hcomp'.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

private theorem complexHessian_sub_local
    {f g : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    complexHessian (f - g) z = complexHessian f z - complexHessian g z := by
  simp only [complexHessian, ddbar_sub hf hg, ContinuousAlternatingMap.coeffMatrix_sub]

private theorem smoothCorePerturbedChartMatrix_sub_local
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0)
    (v w : SmoothChartHolderCore cover 2 α) (i : cover.ι)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ cover.piece i) :
    smoothCorePerturbedChartMatrix ω₁ cover α v i z -
      smoothCorePerturbedChartMatrix ω₁ cover α w i z =
        complexHessian ((v.smoothMap - w.smoothMap) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  have hv := chart_smoothCore_contDiffAt cover α v i hz
  have hw := chart_smoothCore_contDiffAt cover α w i hz
  have hsub : complexHessian ((v.smoothMap - w.smoothMap) ∘ e.symm) z =
      complexHessian (v.smoothMap ∘ e.symm) z -
        complexHessian (w.smoothMap ∘ e.symm) z := by
    convert complexHessian_sub_local hv hw using 1 ; ext y ; rfl
  ext j k
  have hsubEntry : complexHessian ((v.smoothMap - w.smoothMap) ∘ e.symm) z j k =
      complexHessian (v.smoothMap ∘ e.symm) z j k -
        complexHessian (w.smoothMap ∘ e.symm) z j k :=
    congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A j k) hsub
  have hsubEntry' : complexHessian ((v.smoothMap - w.smoothMap) ∘
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z j k =
      complexHessian (v.smoothMap ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z j k -
        complexHessian (w.smoothMap ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z j k := by
    simpa [e] using hsubEntry
  simp only [smoothCorePerturbedChartMatrix, Matrix.sub_apply, Matrix.add_apply]
  calc
    ω₁.metricInChart (cover.base i) z j k +
        complexHessian (v.smoothMap ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z j k -
      (ω₁.metricInChart (cover.base i) z j k +
        complexHessian (w.smoothMap ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z j k) =
        complexHessian (v.smoothMap ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z j k -
        complexHessian (w.smoothMap ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z j k := by abel
    _ = complexHessian ((v.smoothMap - w.smoothMap) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z j k := hsubEntry'.symm

private theorem smoothCore_chartMatrix_diff_bound
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [CompactSpace M]
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0)
    (N : SmoothChartHolderNormedData cover 2 α)
    (v w : SmoothChartHolderCore cover 2 α) (i : cover.ι)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ cover.piece i) :
    ‖smoothCorePerturbedChartMatrix ω₁ cover α v i z -
      smoothCorePerturbedChartMatrix ω₁ cover α w i z‖ ≤
        ((n + 1 : ℝ≥0) : ℝ) *
          ‖(v : LittleHolder cover 2 α N) - (w : LittleHolder cover 2 α N)‖ := by
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  let d : SmoothChartHolderCore cover 2 α := v - w
  let dC : LittleHolder cover 2 α N := d
  let e := extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  have hdmap : d.smoothMap = v.smoothMap - w.smoothMap := by rfl
  have hcoe : dC = (v : LittleHolder cover 2 α N) - (w : LittleHolder cover 2 α N) := by
    change (↑(v - w) : LittleHolder cover 2 α N) = _
    rw [UniformSpace.Completion.coe_sub]
  have hjet := (smoothChartHolderCompletedJetHolderWith cover α N dC i).1
    2 le_rfl ⟨z, hz⟩
  have hjet' : ‖iteratedFDeriv ℝ 2 (d.smoothMap ∘ e.symm) z‖ ≤ ‖dC‖ := by
    simpa [e, dC, d, smoothChartHolderJetCanonicalExtension_coe,
      smoothChartHolderJetData] using hjet
  have hjet'' : ‖iteratedFDeriv ℝ 2 ((v.smoothMap - w.smoothMap) ∘ e.symm) z‖ ≤ ‖dC‖ := by
    simpa [hdmap] using hjet'
  have hmat := smoothCorePerturbedChartMatrix_sub_local ω₁ cover α v w i hz
  have hmat' : smoothCorePerturbedChartMatrix ω₁ cover α v i z -
      smoothCorePerturbedChartMatrix ω₁ cover α w i z =
        complexHessian ((v.smoothMap - w.smoothMap) ∘ e.symm) z := by
    simpa only [extChartAt_real_eq] using hmat
  have hreg : ContDiffAt ℝ 2 ((v - w).smoothMap ∘ e.symm) z := by
    simpa only [extChartAt_real_eq] using
      (chart_smoothCore_contDiffAt cover α (v - w) i hz)
  have hcalc : ‖smoothCorePerturbedChartMatrix ω₁ cover α v i z -
      smoothCorePerturbedChartMatrix ω₁ cover α w i z‖ ≤
        ((n + 1 : ℕ) : ℝ) * ‖dC‖ := by
    calc
      ‖smoothCorePerturbedChartMatrix ω₁ cover α v i z -
          smoothCorePerturbedChartMatrix ω₁ cover α w i z‖ =
        ‖complexHessian ((v.smoothMap - w.smoothMap) ∘ e.symm) z‖ := by rw [hmat']
      _ ≤ ((n + 1 : ℕ) : ℝ) * ‖dC‖ :=
        complexHessian_frobenius_bound_of_secondJet hreg ‖dC‖ (norm_nonneg _) hjet''
  have hcast : ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℝ≥0) : ℝ) := by norm_num
  calc
    ‖smoothCorePerturbedChartMatrix ω₁ cover α v i z -
        smoothCorePerturbedChartMatrix ω₁ cover α w i z‖ = _ := rfl
    _ ≤ ((n + 1 : ℝ≥0) : ℝ) *
        ‖(v : LittleHolder cover 2 α N) - (w : LittleHolder cover 2 α N)‖ := by
      rw [← hcast, ← hcoe]
      exact hcalc

private theorem smoothCore_actualLimit_secondJet_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (huC2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u))
    (j : ℕ) (i : P.finiteChartCover.ι) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ P.finiteChartCover.piece i) :
    ‖iteratedFDeriv ℝ 2
      (((v j).smoothMap ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm) -
        (P.evalC2 u ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm)) z‖ ≤
      ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
        (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖ := by
  let cover := P.finiteChartCover
  let N := P.normedDataC2
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  let J := smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl
  let d : LittleHolder cover 2 α N :=
    (v j : LittleHolder cover 2 α N) - (u : LittleHolder cover 2 α N)
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N
  have hEvalEq : P.evalC2 u = smoothChartHolderContinuousMapExtension cover 2 α N
      (u : LittleHolder cover 2 α N) := by
    funext x
    rfl
  have hjetv := smoothChartHolderCompletedBoundaryJetIdentity cover α N
    (v j : LittleHolder cover 2 α N) 2 le_rfl i z hz
  have hjetu := smoothChartHolderCompletedBoundaryJetIdentity cover α N
    (u : LittleHolder cover 2 α N) 2 le_rfl i z hz
  let f := (v j).smoothMap ∘ e.symm
  let g := P.evalC2 u ∘ e.symm
  have hf : ContDiffAt ℝ 2 f z := by
    have h' := (contMDiff_iff.mp (v j).smoothMap.contMDiff).2 (cover.base i) 0
    have h'' : ContDiffOn ℝ 2 ((v j).smoothMap ∘ e.symm) e.target := by
      simpa [e, extChartAt, chartAt_self_eq] using h'.of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    exact h''.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
      (cover.piece_in_target i hz))
  have hg : ContDiffAt ℝ 2 g z := by
    have h' := (contMDiff_iff.mp huC2).2 (cover.base i) 0
    have h'' : ContDiffOn ℝ 2 (P.evalC2 u ∘ e.symm) e.target := by
      simpa [e, extChartAt, chartAt_self_eq] using h'
    exact h''.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
      (cover.piece_in_target i hz))
  have hjetv' : iteratedFDeriv ℝ 2 f z = J (v j : LittleHolder cover 2 α N) i ⟨z, hz⟩ := by
    simpa [f, e, J, smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap] using hjetv
  have hjetu' : iteratedFDeriv ℝ 2 g z = J (u : LittleHolder cover 2 α N) i ⟨z, hz⟩ := by
    simpa [g, e, J, hEvalEq] using hjetu
  have hjetd : iteratedFDeriv ℝ 2 (f - g) z = J d i ⟨z, hz⟩ := by
    rw [iteratedFDeriv_sub_apply hf hg, hjetv', hjetu']
    change J (v j : LittleHolder cover 2 α N) i ⟨z, hz⟩ -
      J (u : LittleHolder cover 2 α N) i ⟨z, hz⟩ =
        J ((v j : LittleHolder cover 2 α N) - (u : LittleHolder cover 2 α N)) i ⟨z, hz⟩
    exact (congrArg (fun q => q i ⟨z, hz⟩) (J.map_sub
      (v j : LittleHolder cover 2 α N) (u : LittleHolder cover 2 α N))).symm
  have hbound := (smoothChartHolderCompletedJetHolderWith cover α N d i).1
    2 le_rfl ⟨z, hz⟩
  rw [hjetd]
  exact hbound

/-- Full-piece sup and Hölder bounds for smooth Hessian differences, and uniform closeness to
exactly the matrix of the evaluated C² limit. -/
theorem smoothCore_chartMatrix_control
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (huC2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u)) :
    (∀ j k i z, z ∈ P.finiteChartCover.piece i →
      ‖smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z -
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z‖ ≤
          ((n + 1 : ℝ≥0) : ℝ) *
            ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
              (v k : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖) ∧
    (∀ j k i, HolderOnWith
      (2 * (n + 1 : ℝ≥0) *
        ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
          (v k : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖₊) α
      (fun z =>
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z -
        smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v k) i z)
      (P.finiteChartCover.piece i)) ∧
    (∀ j i z, z ∈ P.finiteChartCover.piece i →
      ‖smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) P.finiteChartCover α (v j) i z -
        evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z‖ ≤
          ((n + 1 : ℝ≥0) : ℝ) *
            ‖(v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) -
              (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)‖) := by
  constructor
  · intro j k i z hz
    exact smoothCore_chartMatrix_diff_bound (ω₀.perturb φ hφ) P.finiteChartCover α
      P.normedDataC2 (v j) (v k) i hz
  · constructor
    · intro j k i
      let cover := P.finiteChartCover
      let N := P.normedDataC2
      let d : SmoothChartHolderCore cover 2 α := v j - v k
      let dC : LittleHolder cover 2 α N :=
        (v j : LittleHolder cover 2 α N) - (v k : LittleHolder cover 2 α N)
      let chart := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm
      let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
        smoothChartHolderCoreNormedAddCommGroup cover 2 α N
      let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
        smoothChartHolderCoreNormedSpace cover 2 α N
      have hcoe : dC = (d : LittleHolder cover 2 α N) := by
        change (↑(v j) : LittleHolder cover 2 α N) - ↑(v k) = ↑(v j - v k)
        rw [UniformSpace.Completion.coe_sub]
      have hdmap : d.smoothMap = (v j).smoothMap - (v k).smoothMap := by rfl
      have hcanonical := (smoothChartHolderCompletedJetHolderWith cover α N dC i).2
      have hjetIdent (x : cover.piece i) :
          iteratedFDeriv ℝ 2 (d.smoothMap ∘ chart) x.1 =
            smoothChartHolderJetCanonicalExtension cover 2 α N 2 le_rfl dC i x := by
        have h := smoothChartHolderCompletedBoundaryJetIdentity cover α N dC
          2 le_rfl i x.1 x.2
        simpa [dC, hcoe, d, chart, smoothChartHolderContinuousMapExtension_coe,
          smoothChartHolderContinuousMapLinearMap] using h
      have hholderSub : HolderWith ‖dC‖₊ α
          (fun x : cover.piece i => iteratedFDeriv ℝ 2 (d.smoothMap ∘ chart) x.1) := by
        intro x y
        change edist (iteratedFDeriv ℝ 2 (d.smoothMap ∘ chart) x.1)
          (iteratedFDeriv ℝ 2 (d.smoothMap ∘ chart) y.1) ≤ _
        rw [hjetIdent x, hjetIdent y]
        exact hcanonical x y
      have hjetHolder : HolderOnWith ‖dC‖₊ α
          (fun z => iteratedFDeriv ℝ 2 (d.smoothMap ∘ chart) z) (cover.piece i) := by
        apply HolderWith.restrict_iff.mp
        change HolderWith ‖dC‖₊ α
          (fun x : cover.piece i => iteratedFDeriv ℝ 2 (d.smoothMap ∘ chart) x.1)
        exact hholderSub
      have hentry (a b : Fin n) : HolderOnWith ‖dC‖₊ α
          (fun z => (smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v j) i z -
            smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v k) i z) a b)
          (cover.piece i) := by
        have hbase := hessian_entry_holder_of_jet_holder hjetHolder
          (fun z hz => chart_smoothCore_contDiffAt cover α d i hz) a b
        intro x hx y hy
        have hmatx := smoothCorePerturbedChartMatrix_sub_local
          (ω₀.perturb φ hφ) cover α (v j) (v k) i hx
        have hmaty := smoothCorePerturbedChartMatrix_sub_local
          (ω₀.perturb φ hφ) cover α (v j) (v k) i hy
        have hmatx' : smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v j) i x -
            smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v k) i x =
              complexHessian (d.smoothMap ∘ chart) x := by
          simpa [d, chart, hdmap] using hmatx
        have hmaty' : smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v j) i y -
            smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v k) i y =
              complexHessian (d.smoothMap ∘ chart) y := by
          simpa [d, chart, hdmap] using hmaty
        change edist
          ((smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v j) i x -
            smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v k) i x) a b)
          ((smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v j) i y -
            smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v k) i y) a b) ≤ _
        have hxentry := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A a b) hmatx'
        have hyentry := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A a b) hmaty'
        rw [hxentry, hyentry]
        exact hbase x hx y hy
      have hmatrixHolder := matrix_holder_bound
        (fun z => smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v j) i z -
          smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v k) i z) hentry
      have hconst : ((Fintype.card (Fin n) : ℝ≥0) + 1) * ‖dC‖₊ ≤
          2 * ((n + 1 : ℝ≥0)) *
            ‖(v j : LittleHolder cover 2 α N) - (v k : LittleHolder cover 2 α N)‖₊ := by
        rw [Fintype.card_fin]
        change ((n : ℝ≥0) + 1) *
            ‖(v j : LittleHolder cover 2 α N) - (v k : LittleHolder cover 2 α N)‖₊ ≤
          2 * ((n + 1 : ℝ≥0)) *
            ‖(v j : LittleHolder cover 2 α N) - (v k : LittleHolder cover 2 α N)‖₊
        have hn : 0 ≤ (n : ℝ≥0) + 1 := by positivity
        have hc : 0 ≤ ‖(v j : LittleHolder cover 2 α N) -
            (v k : LittleHolder cover 2 α N)‖₊ := by positivity
        have hfactor : (n : ℝ≥0) + 1 ≤ 2 * ((n : ℝ≥0) + 1) := by
          calc
            (n : ℝ≥0) + 1 ≤ (n : ℝ≥0) + 1 + ((n : ℝ≥0) + 1) :=
              le_add_of_nonneg_right hn
            _ = 2 * ((n : ℝ≥0) + 1) := by ring
        have hnat : ((n + 1 : ℕ) : ℝ≥0) = (n : ℝ≥0) + 1 := by norm_num
        calc
          ((n : ℝ≥0) + 1) *
              ‖(v j : LittleHolder cover 2 α N) - (v k : LittleHolder cover 2 α N)‖₊ ≤
            (2 * ((n : ℝ≥0) + 1)) *
              ‖(v j : LittleHolder cover 2 α N) - (v k : LittleHolder cover 2 α N)‖₊ :=
                mul_le_mul_of_nonneg_right hfactor hc
          _ = 2 * ((n + 1 : ℝ≥0)) *
              ‖(v j : LittleHolder cover 2 α N) - (v k : LittleHolder cover 2 α N)‖₊ := by
                ring
      exact hmatrixHolder.mono_const hconst
    · intro j i z hz
      let cover := P.finiteChartCover
      let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
      let f := (v j).smoothMap ∘ e.symm
      let g := P.evalC2 u ∘ e.symm
      have hf : ContDiffAt ℝ 2 f z := by
        have h' := (contMDiff_iff.mp (v j).smoothMap.contMDiff).2 (cover.base i) 0
        have h'' : ContDiffOn ℝ 2 ((v j).smoothMap ∘ e.symm) e.target := by
          simpa [e, extChartAt, chartAt_self_eq] using h'.of_le
            (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
        exact h''.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
          (cover.piece_in_target i hz))
      have hg : ContDiffAt ℝ 2 g z := by
        have h' := (contMDiff_iff.mp huC2).2 (cover.base i) 0
        have h'' : ContDiffOn ℝ 2 (P.evalC2 u ∘ e.symm) e.target := by
          simpa [e, extChartAt, chartAt_self_eq] using h'
        exact h''.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
          (cover.piece_in_target i hz))
      have hjet := smoothCore_actualLimit_secondJet_bound ω₀ φ hφ α u v huC2 j i z hz
      have hmatrix :
          smoothCorePerturbedChartMatrix (ω₀.perturb φ hφ) cover α (v j) i z -
            evaluatedPerturbedChartMatrix (ω₀.perturb φ hφ) α u i z =
            complexHessian (f - g) z := by
        ext a b
        change ((ω₀.perturb φ hφ).metricInChart (cover.base i) z a b +
            complexHessian f z a b) -
          ((ω₀.perturb φ hφ).metricInChart (cover.base i) z a b +
            complexHessian g z a b) = complexHessian (f - g) z a b
        rw [complexHessian_sub_local hf hg]
        simp only [Matrix.sub_apply]
        abel
      have hbound := complexHessian_frobenius_bound_of_secondJet (hf.sub hg)
        ‖(v j : LittleHolder cover 2 α P.normedDataC2) -
          (u : LittleHolder cover 2 α P.normedDataC2)‖
        (norm_nonneg _) hjet
      rw [hmatrix]
      have hcast : ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℝ≥0) : ℝ) := by norm_num
      calc
        ‖complexHessian (f - g) z‖ ≤
            ((n + 1 : ℕ) : ℝ) *
              ‖(v j : LittleHolder cover 2 α P.normedDataC2) -
                (u : LittleHolder cover 2 α P.normedDataC2)‖ := hbound
        _ = ((n + 1 : ℝ≥0) : ℝ) *
              ‖(v j : LittleHolder cover 2 α P.normedDataC2) -
                (u : LittleHolder cover 2 α P.normedDataC2)‖ := by rw [hcast]

end KahlerForm
