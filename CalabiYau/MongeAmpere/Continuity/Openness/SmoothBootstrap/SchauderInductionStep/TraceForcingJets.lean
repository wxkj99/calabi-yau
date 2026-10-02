module

public import CalabiYau.Analysis.Elliptic.Schauder
public import CalabiYau.Analysis.Elliptic.Schauder.OperatorCommutator.HolderBound.TraceProduct

open scoped ContDiff NNReal Topology
open Set Matrix
open CalabiYau.Schauder

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

private theorem ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux {Du Eu Fu Gu : Type u}
    [NormedAddCommGroup Du] [NormedSpace 𝕜 Du] [NormedAddCommGroup Eu] [NormedSpace 𝕜 Eu]
    [NormedAddCommGroup Fu] [NormedSpace 𝕜 Fu] [NormedAddCommGroup Gu] [NormedSpace 𝕜 Gu]
    (B : Eu →L[𝕜] Fu →L[𝕜] Gu) {f : Du → Eu} {g : Du → Fu} {n : ℕ} {s : Set Du} {x : Du}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ‖iteratedFDerivWithin 𝕜 n (fun y => B (f y) (g y)) s x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
        ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
  /- We argue by induction on `n`. The bound is trivial for `n = 0`. For `n + 1`, we write
    the `(n+1)`-th derivative as the `n`-th derivative of the derivative `B f g' + B f' g`,
    and apply the inductive assumption to each of those two terms. For this induction to make sense,
    the spaces of linear maps that appear in the induction should be in the same universe as the
    original spaces, which explains why we assume in the lemma that all spaces live in the same
    universe. -/
  induction n generalizing Eu Fu Gu with
  | zero =>
    simp only [norm_iteratedFDerivWithin_zero, zero_add, Finset.range_one,
      Finset.sum_singleton, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero, ← mul_assoc]
    apply B.le_opNorm₂
  | succ n IH =>
    have In : ((n : WithTop ℕ∞) + 1) ≤ (n.succ : WithTop ℕ∞) := by simp only [Nat.cast_succ, le_refl]
    have I1 :
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s x‖ ≤
          ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
            ‖iteratedFDerivWithin 𝕜 (n + 1 - i) g s x‖ := by
      calc
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s x‖ ≤
            ‖B.precompR Du‖ * ∑ i ∈ Finset.range (n + 1),
              n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
                ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 g s) s x‖ :=
          IH _ (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
        _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 i f s x‖ *
              ‖iteratedFDerivWithin 𝕜 (n - i) (fderivWithin 𝕜 g s) s x‖ := by
            gcongr; exact B.norm_precompR_le Du
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl fun i hi => ?_
          rw [Nat.succ_sub (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)),
            ← norm_iteratedFDerivWithin_fderivWithin hs hx]
    have I2 :
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x‖ ≤
        ‖B‖ * ∑ i ∈ Finset.range (n + 1), n.choose i * ‖iteratedFDerivWithin 𝕜 (i + 1) f s x‖ *
          ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
      calc
        ‖iteratedFDerivWithin 𝕜 n (fun y : Du => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x‖ ≤
            ‖B.precompL Du‖ * ∑ i ∈ Finset.range (n + 1),
              n.choose i * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 f s) s x‖ *
                ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ :=
          IH _ (hf.fderivWithin hs In) (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
        _ ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
            n.choose i * ‖iteratedFDerivWithin 𝕜 i (fderivWithin 𝕜 f s) s x‖ *
              ‖iteratedFDerivWithin 𝕜 (n - i) g s x‖ := by
          gcongr; exact B.norm_precompL_le Du
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl fun i _ => ?_
          rw [← norm_iteratedFDerivWithin_fderivWithin hs hx]
    have J : iteratedFDerivWithin 𝕜 n
        (fun y : Du => fderivWithin 𝕜 (fun y : Du => B (f y) (g y)) s y) s x =
          iteratedFDerivWithin 𝕜 n (fun y => B.precompR Du (f y)
            (fderivWithin 𝕜 g s y) + B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s x := by
      apply iteratedFDerivWithin_congr (fun y hy => ?_) hx
      exact B.fderivWithin_of_bilinear (hf.differentiableOn (by positivity) y hy)
        (hg.differentiableOn (by positivity) y hy) (hs y hy)
    rw [← norm_iteratedFDerivWithin_fderivWithin hs hx, J]
    have A : ContDiffOn 𝕜 n (fun y => B.precompR Du (f y) (fderivWithin 𝕜 g s y)) s :=
      (B.precompR Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn
        (hf.of_le (Nat.cast_le.2 (Nat.le_succ n))) (hg.fderivWithin hs In)
    have A' : ContDiffOn 𝕜 n (fun y => B.precompL Du (fderivWithin 𝕜 f s y) (g y)) s :=
      (B.precompL Du).isBoundedBilinearMap.contDiff.comp₂_contDiffOn (hf.fderivWithin hs In)
        (hg.of_le (Nat.cast_le.2 (Nat.le_succ n)))
    rw [fun_iteratedFDerivWithin_add_apply (A.contDiffWithinAt hx) (A'.contDiffWithinAt hx) hs hx]
    apply (norm_add_le _ _).trans ((add_le_add I1 I2).trans (le_of_eq ?_))
    simp_rw [← mul_add, mul_assoc]
    congr 1
    exact (Finset.sum_choose_succ_mul
      (fun i j => ‖iteratedFDerivWithin 𝕜 i f s x‖ * ‖iteratedFDerivWithin 𝕜 j g s x‖) n).symm

private theorem holderBoundOn_complex_mul_convex
    {E : Type 0} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {α CF CG : ℝ≥0} {V : Set E}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hV : IsOpen V) (hVconvex : Convex ℝ V)
    (f g : E → ℂ)
    (hf : ContDiffOn ℝ k f V ∧ HolderBoundOn k α CF V f)
    (hg : ContDiffOn ℝ k g V ∧ HolderBoundOn k α CG V g) :
    HolderBoundOn k α (4 * (2 : ℝ≥0) ^ k * CF * CG) V (fun x ↦ f x * g x) := by
  have hprod : ContDiffOn ℝ k (fun x ↦ f x * g x) V := hf.1.mul hg.1
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hjk : j ≤ k := hj
    have hn : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hjk
    let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
    have hwithin₀ := ContinuousLinearMap.norm_iteratedFDerivWithin_le_of_bilinear_aux
      (n := j) B (hf.1.of_le hn) (hg.1.of_le hn) hV.uniqueDiffOn hz
    have hwithin := hwithin₀.trans (mul_le_of_le_one_left (by positivity)
      (ContinuousLinearMap.opNorm_mul_le _ _))
    have hwithin' : ‖iteratedFDerivWithin ℝ j (fun y ↦ f y * g y) V z‖ ≤
        ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f V z‖ *
          ‖iteratedFDerivWithin ℝ (j - i) g V z‖ := by
      simpa [B] using hwithin
    have hterm : ∀ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f V z‖ *
          ‖iteratedFDerivWithin ℝ (j - i) g V z‖ ≤
        (j.choose i : ℝ) * (CF : ℝ) * (CG : ℝ) := by
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hfiAt : ContDiffAt ℝ i f z :=
        (hf.1.contDiffAt (hV.mem_nhds hz)).of_le (by exact_mod_cast Nat.le_trans hij hjk)
      have hsub : ((j - i : ℕ) : WithTop ℕ∞) ≤ (j : WithTop ℕ∞) := by
        exact_mod_cast (Nat.sub_le j i)
      have hgiAt : ContDiffAt ℝ (j - i) g z :=
        (hg.1.contDiffAt (hV.mem_nhds hz)).of_le (hsub.trans hn)
      have hfi := hf.2.1 i (Nat.le_trans hij hjk) z hz
      have hgi := hg.2.1 (j - i) (Nat.le_trans (Nat.sub_le j i) hjk) z hz
      have hfi' := iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hfiAt hz
      have hgi' := iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hgiAt hz
      rw [hfi', hgi']
      gcongr
    have hsum := Finset.sum_le_sum hterm
    have hchoose : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    have hfactor : (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (CF : ℝ) * (CG : ℝ)) =
        (2 : ℝ) ^ j * (CF : ℝ) * (CG : ℝ) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
    have hpow : (2 : ℝ) ^ j ≤ 4 * (2 : ℝ) ^ k := by
      calc
        (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hjk
        _ ≤ 4 * (2 : ℝ) ^ k := by
          have hp := pow_pos (by norm_num : (0 : ℝ) < 2) k
          nlinarith
    calc
      ‖iteratedFDeriv ℝ j (fun x ↦ f x * g x) z‖ =
          ‖iteratedFDerivWithin ℝ j (fun y ↦ f y * g y) V z‖ := by
            have hprodAt : ContDiffAt ℝ j (fun x ↦ f x * g x) z :=
              (hprod.contDiffAt (hV.mem_nhds hz)).of_le (by exact_mod_cast hjk)
            exact congrArg norm
              (iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn hprodAt hz).symm
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i f V z‖ *
            ‖iteratedFDerivWithin ℝ (j - i) g V z‖ := hwithin'
      _ ≤ ∑ i ∈ Finset.range (j + 1),
            (j.choose i : ℝ) * (CF : ℝ) * (CG : ℝ) := hsum
      _ = (2 : ℝ) ^ j * (CF : ℝ) * (CG : ℝ) := hfactor
      _ ≤ (4 : ℝ) * (2 : ℝ) ^ k * (CF : ℝ) * (CG : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)
      _ = (4 * (2 : ℝ≥0) ^ k * CF * CG : ℝ) := by
            push_cast
            ring
  · exact holderOnWith_complex_mul_topJet_convex hα₀ hα₁ hV hVconvex f g hf hg

private theorem holderOnWith_finset_sum
    {X ι F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {s : Set X} {α : ℝ≥0} (t : Finset ι) (K : ι → ℝ≥0) (f : ι → X → F)
    (hf : ∀ i ∈ t, HolderOnWith (K i) α (f i) s) :
    HolderOnWith (t.sum K) α (fun x ↦ t.sum (fun i ↦ f i x)) s := by
  classical
  have hsum : ∀ u : Finset ι,
      (∀ i ∈ u, HolderOnWith (K i) α (f i) s) →
        HolderOnWith (u.sum K) α (fun x ↦ u.sum (fun i ↦ f i x)) s := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        intro hu x hx y hy
        simp
    | @insert i u hi ih =>
        intro hu x hx y hy
        have hhead := hu i (Finset.mem_insert_self i u) x hx y hy
        have htail : ∀ j ∈ u, HolderOnWith (K j) α (f j) s := by
          intro j hj
          exact hu j (Finset.mem_insert_of_mem hj)
        have hrest := ih htail x hx y hy
        change edist ((insert i u).sum (fun j ↦ f j x))
          ((insert i u).sum (fun j ↦ f j y)) ≤
            (↑((insert i u).sum K) : ENNReal) * edist x y ^ (α : ℝ)
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        grw [edist_add_add_le, hhead, hrest]
        rw [Finset.sum_insert hi, ENNReal.coe_add, ← add_mul]
  exact hsum t hf

private theorem compact_derivative_bound_probe {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ m f U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have htop (j : ℕ) (hj : j ≤ m) : (j : ℕ∞ω) ≤ (m : ℕ∞ω) := by
    exact_mod_cast hj
  have hcont (j : ℕ) (hj : j ≤ m) :
      ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ j f x‖) K := by
    have hwithin := hf.continuousOn_iteratedFDerivWithin (htop j hj) hU.uniqueDiffOn
    have heq : EqOn (iteratedFDerivWithin ℝ j f U) (iteratedFDeriv ℝ j f) U := by
      intro x hx
      exact iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        ((hf.contDiffAt (hU.mem_nhds hx)).of_le (htop j hj)) hx
    exact (hwithin.congr heq.symm).mono hKU |>.norm
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
    apply Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f x‖)
    · intro i hi
      exact norm_nonneg _
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  change ‖iteratedFDeriv ℝ j f x‖ ≤ B
  exact hterm.trans hqbound

private theorem holderBoundOn_succ_derivative_bound_probe
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {k : ℕ} {alpha C : ℝ≥0} {f : E → F}
    (hsOpen : IsOpen s) (hsConvex : Convex ℝ s)
    (hsDiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 1)
    (hAlpha : alpha ≤ 1) (hf : ContDiffOn ℝ (k + 1) f s)
    (hbound : ∀ j ≤ k + 1, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    HolderBoundOn k alpha C s f := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    exact hbound j (le_trans hj (Nat.le_succ k)) x hx
  · let g : E → _ := iteratedFDeriv ℝ k f
    have hklt : (↑k : ℕ∞ω) < (↑(k + 1) : ℕ∞ω) := by
      exact_mod_cast Nat.lt_succ_self k
    have hgDiff (x : E) (hx : x ∈ s) : DifferentiableAt ℝ g x := by
      have hfx : ContDiffAt ℝ (k + 1) f x := hf.contDiffAt (hsOpen.mem_nhds hx)
      exact hfx.differentiableAt_iteratedFDeriv hklt
    have hgDeriv (x : E) (hx : x ∈ s) : ‖fderiv ℝ g x‖ ≤ (C : ℝ) := by
      rw [norm_fderiv_iteratedFDeriv]
      exact hbound (k + 1) le_rfl x hx
    have hLip : LipschitzOnWith C g s := by
      apply hsConvex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      · exact hgDiff
      · exact hgDeriv
    have hdiam (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) :
        edist x y ≤ (1 : ENNReal) := by
      rw [edist_dist]
      exact_mod_cast hsDiam x hx y hy
    simpa [g] using (hLip.holderOnWith.of_le hdiam hAlpha)

private theorem smooth_holder_on_ball_probe {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {k : ℕ} {alpha : ℝ≥0}
    (_ha0 : 0 < alpha) (ha1 : alpha < 1) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {z : E} {R : ℝ}
    (hR : 0 < R) (hRsmall : R ≤ 1 / 4)
    (hball : Metric.closedBall z R ⊆ U) :
    ∃ C : ℝ≥0, HolderBoundOn k alpha C (Metric.ball z R) f := by
  let K := Metric.closedBall z R
  have hK : IsCompact K := isCompact_closedBall z R
  obtain ⟨C, hC⟩ := compact_derivative_bound_probe hU
    (m := k + 1) (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hK hball
  have hfinite : ContDiffOn ℝ (k + 1) f (Metric.ball z R) := by
    exact hf.mono (Metric.ball_subset_closedBall.trans hball) |>.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hbound (j : ℕ) (hj : j ≤ k + 1) (x : E) (hx : x ∈ Metric.ball z R) :
      ‖iteratedFDeriv ℝ j f x‖ ≤ C := hC j (by omega) x (Metric.ball_subset_closedBall hx)
  refine ⟨C, ?_⟩
  apply holderBoundOn_succ_derivative_bound_probe Metric.isOpen_ball (convex_ball z R) ?_ ha1.le hfinite hbound
  intro x hx y hy
  have hx' : dist x z < R := by simpa [Metric.mem_ball] using hx
  have hy' : dist y z < R := by simpa [Metric.mem_ball] using hy
  have hdist := dist_triangle x z y
  have hdist' : dist x y < 2 * R := by
    have hyx : dist z y = dist y z := dist_comm z y
    linarith
  linarith

private theorem holderBoundOn_sub_probe
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} {k : ℕ} {α C D : ℝ≥0} {f g : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ k f U) (hg : ContDiffOn ℝ k g U)
    (hfb : HolderBoundOn k α C K f) (hgb : HolderBoundOn k α D K g) :
    HolderBoundOn k α (C + D) K (fun x ↦ f x - g x) := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hfj : ContDiffAt ℝ j f x :=
      (hf.contDiffAt (hU.mem_nhds (hKU hx))).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
    have hgj : ContDiffAt ℝ j g x :=
      (hg.contDiffAt (hU.mem_nhds (hKU hx))).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
    change ‖iteratedFDeriv ℝ j (f - g) x‖ ≤ (C + D : ℝ≥0)
    rw [iteratedFDeriv_sub_apply hfj hgj]
    exact (norm_sub_le _ _).trans (by
      simpa using add_le_add (hfb.1 j hj x hx) (hgb.1 j hj x hx))
  · intro x hx y hy
    have hfx := hf.contDiffAt (hU.mem_nhds (hKU hx))
    have hgx := hg.contDiffAt (hU.mem_nhds (hKU hx))
    have hfy := hf.contDiffAt (hU.mem_nhds (hKU hy))
    have hgy := hg.contDiffAt (hU.mem_nhds (hKU hy))
    change edist (iteratedFDeriv ℝ k (f - g) x) (iteratedFDeriv ℝ k (f - g) y) ≤ _
    rw [iteratedFDeriv_sub_apply hfx hgx, iteratedFDeriv_sub_apply hfy hgy]
    have hgb' : edist (-iteratedFDeriv ℝ k g x) (-iteratedFDeriv ℝ k g y) ≤
        (D : ENNReal) * edist x y ^ (α : ℝ) := by
      simpa only [edist_neg_neg] using hgb.2 x hx y hy
    calc
      edist (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k g x)
          (iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k g y) ≤
        edist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) +
          edist (-iteratedFDeriv ℝ k g x) (-iteratedFDeriv ℝ k g y) := by
            simpa only [sub_eq_add_neg, edist_neg_neg] using
              (edist_add_add_le (iteratedFDeriv ℝ k f x) (-iteratedFDeriv ℝ k g x)
                (iteratedFDeriv ℝ k f y) (-iteratedFDeriv ℝ k g y))
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
          (D : ENNReal) * edist x y ^ (α : ℝ) := add_le_add (hfb.2 x hx y hy) hgb'
      _ = ((C + D : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_add]
        ring

/-!
# Hölder jets of the differentiated log-determinant forcing

Smooth background data and a genuine finite Hölder coefficient jet give a finite
Hölder jet for the forcing. Matrix multiplication uses the swapped trace indices:
`re tr(A Dg) = re ∑ i, ∑ j, A i j * Dg j i`.
The assertion includes every lower-jet sup bound, not just the top seminorm.
-/

@[expose] public section

open scoped ContDiff NNReal Topology

/-- Local finite Hölder control of the smooth derivative minus the coefficient trace. -/
theorem locally_holder_directional_trace_forcing
    {n r : ℕ} {α K : ℝ≥0} {W : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (hα₀ : 0 < α) (hα₁ : α < 1)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (H : EuclideanSpace ℂ (Fin n) → ℝ)
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, ContDiffOn ℝ r (fun w ↦ A w i j) W)
    (hAH : ∀ i j, HolderBoundOn r α K W (fun w ↦ A w i j))
    (hH : ContDiffOn ℝ ∞ H W)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ g w i j) W)
    (v z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ W) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), ∃ C : ℝ≥0,
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      HolderBoundOn r α C V (fun w ↦ fderiv ℝ H w v -
        RCLike.re (A w * fderiv ℝ g w v).trace) := by

  classical
  obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hz)
  let ρ : ℝ := min (R / 2) (1 / 8)
  let V : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball z ρ
  let closedBall : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall z ρ
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hρlt : ρ < R := by dsimp [ρ]; simp only [min_lt_iff]; left; linarith
  have hρsmall : ρ ≤ 1 / 4 := by dsimp [ρ]; exact (min_le_right _ _).trans (by norm_num)
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hzV : z ∈ V := by
    change z ∈ Metric.ball z ρ
    exact Metric.mem_ball_self hρpos
  have hVsubK : V ⊆ closedBall := Metric.ball_subset_closedBall
  have hKcompact : IsCompact closedBall := isCompact_closedBall z ρ
  have hKsubW : closedBall ⊆ W := by
    intro w hw
    apply hRball
    rw [Metric.mem_ball]
    have hw' : dist w z ≤ ρ := by
      simpa [closedBall, Metric.mem_closedBall] using hw
    exact lt_of_le_of_lt hw' hρlt
  have hVsubW : V ⊆ W := fun w hw ↦ hKsubW (hVsubK hw)
  let : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  let : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  let B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ fderiv ℝ g w v
  have hgMatrix : ContDiffOn ℝ ∞ g W :=
    contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr fun j ↦ hg i j
  have hB : ContDiffOn ℝ ∞ B W := by
    dsimp [B]
    exact (hgMatrix.fderiv_of_isOpen hW (WithTop.coe_le_coe.mpr le_top)).clm_apply
      contDiffOn_const
  have hBentry : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ B w i j) W := by
    intro i j
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp hB i)) j
  have hDgHolder (i j : Fin n) :
      ∃ C : ℝ≥0, HolderBoundOn r α C V (fun w ↦ B w i j) := by
    have hLocal := smooth_holder_on_ball_probe (k := r) hW hα₀ hα₁
      (hBentry i j) hρpos hρsmall hKsubW
    simpa [V] using hLocal
  let q : Fin n × Fin n → ℝ≥0 := fun p ↦ Classical.choose (hDgHolder p.1 p.2)
  let CB : ℝ≥0 := ∑ p : Fin n × Fin n, q p
  have hBbound (i j : Fin n) : HolderBoundOn r α CB V (fun w ↦ B w i j) := by
    have hq := Classical.choose_spec (hDgHolder i j)
    apply hq.mono_const
    change q (i, j) ≤ ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), q p
    exact Finset.single_le_sum (fun p hp ↦ by positivity) (Finset.mem_univ (i, j))
  have hHdir : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ H w v) W := by
    exact (hH.fderiv_of_isOpen hW (WithTop.coe_le_coe.mpr le_top)).clm_apply
      contDiffOn_const
  have hHholder : ∃ CH : ℝ≥0,
      HolderBoundOn r α CH V (fun w ↦ fderiv ℝ H w v) := by
    have hLocal := smooth_holder_on_ball_probe (k := r) hW hα₀ hα₁
      hHdir hρpos hρsmall hKsubW
    simpa [V] using hLocal
  obtain ⟨CH, hHholder⟩ := hHholder
  have hHfinite : ContDiffOn ℝ r (fun w ↦ fderiv ℝ H w v) V :=
    hHdir.mono hVsubW |>.of_le (WithTop.coe_le_coe.mpr le_top)
  have hTrace : HolderBoundOn r α
      (8 * (2 : ℝ≥0) ^ r * (Fintype.card (Fin n × Fin n) : ℝ≥0) * K * CB) V
      (fun w ↦ RCLike.re ((A w * B w).trace)) := by
    apply holderBoundOn_real_trace_product_convex
      hα₀ hα₁ hVopen (convex_ball z ρ) A B
    · intro i j
      exact ⟨(hA i j).mono hVsubW, (hAH i j).mono_set hVsubW⟩
    · intro i j
      exact ⟨(hBentry i j).mono hVsubW |>.of_le
          (WithTop.coe_le_coe.mpr le_top), hBbound i j⟩
  have hTraceFinite : ContDiffOn ℝ r
      (fun w ↦ RCLike.re ((A w * B w).trace)) V := by
    have hsum : ContDiffOn ℝ r (fun w ↦
        ∑ i, ∑ j, Complex.reCLM (A w i j * B w j i)) V := by
      apply ContDiffOn.sum
      intro i hi
      apply ContDiffOn.sum
      intro j hj
      exact Complex.reCLM.contDiff.comp_contDiffOn
        ((hA i j).mono hVsubW |>.mul ((hBentry j i).mono hVsubW
          |>.of_le (WithTop.coe_le_coe.mpr le_top)))
    apply hsum.congr
    intro w hw
    simp [Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]
  have hResult := holderBoundOn_sub_probe hVopen Set.Subset.rfl
    hHfinite hTraceFinite hHholder hTrace
  exact ⟨V, CH + (8 * (2 : ℝ≥0) ^ r *
    (Fintype.card (Fin n × Fin n) : ℝ≥0) * K * CB),
    hVopen, hzV, hVsubW, hResult⟩

end
