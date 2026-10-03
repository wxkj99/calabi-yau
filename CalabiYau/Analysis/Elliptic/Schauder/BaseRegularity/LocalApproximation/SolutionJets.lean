module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.Basic

/-!
# Solution smoothing and convergence of the first two jets

Only the compactly buffered ball is asserted smooth. Fixed-scale derivative commutation and
positive unit-mass averaging give local jet convergence and the exact input value bound.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped ContDiff NNReal Topology Convolution

namespace CalabiYau.Schauder

set_option maxHeartbeats 500000 in
private theorem localConvolution_fderiv_apply {n : ℕ}
    (k g : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ)
    (hk : LocallyIntegrable k)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (x v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x v =
      ∫ y, k y * fderiv ℝ g (x - y) v := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hfirst : fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
      (k ⋆[L.precompR (EuclideanSpace ℝ (Fin n × Fin 2))] fderiv ℝ g) x :=
    (hgc.hasFDerivAt_convolution_right L hk (hg.of_le (by norm_num)) x).fderiv
  rw [hfirst]
  change ((k ⋆[L.precompR (EuclideanSpace ℝ (Fin n × Fin 2))] fderiv ℝ g) x) v = _
  have hint : Integrable (fun y ↦ k y • fderiv ℝ g (x - y)) := by
    exact ((hgc.fderiv ℝ).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
      hk (hg.fderiv_right (m := 1) (by norm_num) |>.continuous) x)
  rw [convolution_def]
  change (∫ y, k y • fderiv ℝ g (x - y)) v = _
  rw [ContinuousLinearMap.integral_apply hint]
  simp only [_root_.smul_apply, smul_eq_mul]

set_option maxHeartbeats 500000 in
private theorem localConvolution_fderiv_fderiv_apply {n : ℕ}
    (k g : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ)
    (hk : LocallyIntegrable k)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (x v w : EuclideanSpace ℝ (Fin n × Fin 2)) :
    fderiv ℝ (fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)) x v w =
      ∫ y, k y * fderiv ℝ (fderiv ℝ g) (x - y) v w := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hdg : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hfirst (a : EuclideanSpace ℝ (Fin n × Fin 2)) :
      fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) a =
        (k ⋆[L.precompR (EuclideanSpace ℝ (Fin n × Fin 2))] fderiv ℝ g) a :=
    (hgc.hasFDerivAt_convolution_right L hk (hg.of_le (by norm_num)) a).fderiv
  have hsecond : fderiv ℝ (fderiv ℝ
      (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)) x =
        (k ⋆[(L.precompR (EuclideanSpace ℝ (Fin n × Fin 2))).precompR
          (EuclideanSpace ℝ (Fin n × Fin 2))]
          (fderiv ℝ (fderiv ℝ g))) x := by
    rw [show fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) =
        k ⋆[L.precompR (EuclideanSpace ℝ (Fin n × Fin 2))] fderiv ℝ g by
          funext a
          exact hfirst a]
    exact ((hgc.fderiv ℝ).hasFDerivAt_convolution_right
      (L.precompR (EuclideanSpace ℝ (Fin n × Fin 2))) hk hdg x).fderiv
  rw [hsecond]
  have hint : Integrable (fun y ↦ k y • fderiv ℝ (fderiv ℝ g) (x - y)) := by
    exact (((hgc.fderiv ℝ).fderiv ℝ).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hk
      (hg.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0)
        (by norm_num) |>.continuous) x)
  change (∫ y, k y • fderiv ℝ (fderiv ℝ g) (x - y)) v w = _
  rw [ContinuousLinearMap.integral_apply hint]
  have hintv : Integrable (fun y ↦ (k y • fderiv ℝ (fderiv ℝ g) (x - y)) v) :=
    (ContinuousLinearMap.apply ℝ
      (EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ) v).integrable_comp hint
  rw [ContinuousLinearMap.integral_apply hintv]
  simp only [_root_.smul_apply, smul_eq_mul]

private theorem iteratedFDeriv_linearIsometry_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (f : F → ℝ) (hf : ContDiff ℝ 2 f) (x : E)
    {j : ℕ} (hj : j ≤ 2) :
    iteratedFDeriv ℝ j (fun y : E => f (e y)) x =
      (iteratedFDeriv ℝ j f (e x)).compContinuousLinearMap
        (fun _ => e.toContinuousLinearMap) := by
  exact e.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by exact_mod_cast hj)

private theorem jet_one_as_fderiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (m : Fin 1 → E) :
    iteratedFDeriv ℝ 1 f x m = fderiv ℝ f x (m 0) := by
  rw [iteratedFDeriv_succ_apply_right]
  simp

private theorem jet_two_as_fderiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (m : Fin 2 → E) :
    iteratedFDeriv ℝ 2 f x m = fderiv ℝ (fderiv ℝ f) x (m 0) (m 1) := by
  rw [iteratedFDeriv_succ_apply_right]
  have h := jet_one_as_fderiv (fun y => fderiv ℝ f y) x (Fin.init m)
  change (iteratedFDeriv ℝ 1 (fun y => fderiv ℝ f y) x (Fin.init m)) (m 1) = _
  exact congrArg (fun L : E →L[ℝ] F => L (m 1)) h

private theorem localConvolution_jet1_average {n : ℕ}
    (k g : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ)
    (hk : LocallyIntegrable k) (hkc : Continuous k) (hkcompact : HasCompactSupport k)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    iteratedFDeriv ℝ 1 (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
      ∫ y, k y • iteratedFDeriv ℝ 1 g (x - y) := by
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  have hJcont : Continuous (fun y : E =>
      k y • iteratedFDeriv ℝ 1 g (x - y)) := by
    have hcont : Continuous (iteratedFDeriv ℝ 1 g) :=
      hg.continuous_iteratedFDeriv (by norm_num)
    exact hkc.smul (hcont.comp (continuous_const.sub continuous_id))
  have hJcomp : HasCompactSupport (fun y : E =>
      k y • iteratedFDeriv ℝ 1 g (x - y)) := hkcompact.smul_right
  have hJint : Integrable (fun y : E =>
      k y • iteratedFDeriv ℝ 1 g (x - y)) :=
    hJcont.integrable_of_hasCompactSupport hJcomp
  ext v
  rw [jet_one_as_fderiv]
  rw [localConvolution_fderiv_apply k g hk hg hgc x (v 0)]
  rw [ContinuousMultilinearMap.integral_apply hJint]
  apply integral_congr_ae
  filter_upwards with y
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [jet_one_as_fderiv]

private theorem localConvolution_jet2_average {n : ℕ}
    (k g : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ)
    (hk : LocallyIntegrable k) (hkc : Continuous k) (hkcompact : HasCompactSupport k)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    iteratedFDeriv ℝ 2 (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
      ∫ y, k y • iteratedFDeriv ℝ 2 g (x - y) := by
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  have hJcont : Continuous (fun y : E =>
      k y • iteratedFDeriv ℝ 2 g (x - y)) := by
    have hcont : Continuous (iteratedFDeriv ℝ 2 g) :=
      hg.continuous_iteratedFDeriv (by norm_num)
    exact hkc.smul (hcont.comp (continuous_const.sub continuous_id))
  have hJcomp : HasCompactSupport (fun y : E =>
      k y • iteratedFDeriv ℝ 2 g (x - y)) := hkcompact.smul_right
  have hJint : Integrable (fun y : E =>
      k y • iteratedFDeriv ℝ 2 g (x - y)) :=
    hJcont.integrable_of_hasCompactSupport hJcomp
  ext v
  rw [jet_two_as_fderiv]
  rw [localConvolution_fderiv_fderiv_apply k g hk hg hgc x (v 0) (v 1)]
  rw [ContinuousMultilinearMap.integral_apply hJint]
  apply integral_congr_ae
  filter_upwards with y
  simp only [_root_.smul_apply, smul_eq_mul]
  rw [jet_two_as_fderiv]

private theorem localFixedMollify_jet_commutation {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {R S η : ℝ} {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (_hR : 0 < R) (hRS : R < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) :
    ∀ j ≤ 2, ∀ m z, z ∈ Metric.ball c R →
      iteratedFDeriv ℝ j (localFixedMollify U hη m u) z =
        ∫ t : EuclideanSpace ℝ (Fin n × Fin 2), localFixedKernel hη m t •
          iteratedFDeriv ℝ j u
            (complexToRealCoordinateEquiv.symm (complexToRealCoordinateEquiv z - t)) := by
  classical
  intro j hj m z hz
  let E := EuclideanSpace ℝ (Fin n × Fin 2)
  let e := complexToRealCoordinateEquiv (n := n)
  let k : E → ℝ := localFixedKernel hη m
  let K : Set E := Metric.closedBall 0 (localKernelRadius η m)
  have hr : localKernelRadius η m ≤ η / 4 := by
    dsimp [localKernelRadius]
    apply div_le_div_of_nonneg_left (le_of_lt hη) (by norm_num)
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hkcont : Continuous k := (localKernelBump (n := n) hη m).continuous_normed
  have hkzero (w : E) (hw : w ∉ K) : k w = 0 := by
    have hnot : w ∉ tsupport k := by
      simpa only [k, localFixedKernel, ContDiffBump.tsupport_normed_eq,
        localKernelBump, K] using hw
    exact image_eq_zero_of_notMem_tsupport hnot
  have hzS : z ∈ Metric.closedBall c S := by
    rw [Metric.mem_closedBall]
    have hzR := Metric.mem_ball.mp hz
    linarith
  have hnearU (y : E) (hy : dist y (e z) < η) : e.symm y ∈ U := by
    apply hCollar
    apply Metric.mem_thickening_iff.mpr
    refine ⟨z, hzS, ?_⟩
    have hedist : dist (e.symm y) z = dist y (e z) := by
      rw [← e.isometry.dist_eq, e.apply_symm_apply]
    rwa [hedist]
  have hsample (w : E) (hw : w ∈ K) : e.symm (e z - w) ∈ U := by
    apply hnearU
    have hnorm : ‖w‖ ≤ localKernelRadius η m := by
      simpa only [K, Metric.mem_closedBall, dist_zero_right] using hw
    have hdist : dist (e z - w) (e z) = ‖w‖ := by simp
    rw [hdist]
    linarith
  let b : ContDiffBump (e z) :=
    ⟨η / 2, 3 * η / 4, by positivity, by linarith⟩
  let g : E → ℝ := fun y => b y * if e.symm y ∈ U then u (e.symm y) else 0
  have hgcompact : HasCompactSupport g := b.hasCompactSupport.mul_right
  have hgd : ContDiff ℝ 2 g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport (b : E → ℝ)
    · have hyU : e.symm y ∈ U := by
        apply hnearU
        have hy' : dist y (e z) ≤ 3 * η / 4 := by
          simpa only [b.tsupport_eq, Metric.mem_closedBall, b] using hy
        linarith
      have hcond : ∀ᶠ t in 𝓝 y, e.symm t ∈ U :=
        e.symm.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
      have heq : g =ᶠ[𝓝 y] fun t => b t * u (e.symm t) := by
        filter_upwards [hcond] with t ht
        change e.symm t ∈ U at ht
        simp only [g, ite_eq_left ht]
      apply ContDiffAt.congr_of_eventuallyEq _ heq
      exact b.contDiff.contDiffAt.mul
        (((hu _ hyU).contDiffAt (hU.mem_nhds hyU)).comp y (by fun_prop))
    · have heq : g =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport (b : E → ℝ)).isOpen_compl.mem_nhds hy] with t ht
        simp only [g, image_eq_zero_of_notMem_tsupport ht, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hgnear (y : E) (hy : y ∈ Metric.ball (e z) (η / 2)) :
      g =ᶠ[𝓝 y] fun t => u (e.symm t) := by
    have hcond : ∀ᶠ t in 𝓝 y, t ∈ Metric.ball (e z) (η / 2) :=
      Metric.isOpen_ball.mem_nhds hy
    filter_upwards [hcond] with t ht
    have htU : e.symm t ∈ U := hnearU t (by
      have := Metric.mem_ball.mp ht
      linarith)
    simp only [g, ite_eq_left htU, b.one_of_mem_closedBall (Metric.ball_subset_closedBall ht), one_mul]
  have htrans (x w : E) (hx : x ∈ Metric.ball (e z) (η / 8)) (hw : w ∈ K) :
      x - w ∈ Metric.ball (e z) (η / 2) := by
    have hw' : ‖w‖ ≤ localKernelRadius η m := by
      simpa only [K, Metric.mem_closedBall, dist_zero_right] using hw
    have hdist : dist (x - w) (e z) ≤ dist x (e z) + ‖w‖ := by
      calc
        dist (x - w) (e z) ≤ dist (x - w) x + dist x (e z) := dist_triangle _ _ _
        _ = dist x (e z) + ‖w‖ := by simp [dist_eq_norm, add_comm]
    apply Metric.mem_ball.mpr
    have hx' := Metric.mem_ball.mp hx
    linarith [hr]
  have hcf : HasCompactSupport k := by
    change HasCompactSupport ((localKernelBump hη m).normed (volume : Measure E))
    exact (localKernelBump hη m).hasCompactSupport_normed
  have hkdiff : ContDiff ℝ ∞ k := by
    change ContDiff ℝ ∞ ((localKernelBump hη m).normed (volume : Measure E))
    exact (localKernelBump hη m).contDiff_normed
  have hgloc : LocallyIntegrable g := hgd.continuous.locallyIntegrable
  have hkg : LocallyIntegrable k := hkdiff.continuous.locallyIntegrable
  let F : E → ℝ := k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
  have hFd : ContDiff ℝ ∞ F := by
    exact hcf.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hkdiff hgloc
  have hFeq : localFixedMollify U hη m u =ᶠ[𝓝 z] fun x => F (e x) := by
    have hnh : ∀ᶠ x in 𝓝 z, e x ∈ Metric.ball (e z) (η / 8) :=
      e.continuous.continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [hnh] with x hx
    apply integral_congr_ae
    filter_upwards with w
    simp only [g, ContinuousLinearMap.lsmul_apply]
    by_cases hw : w ∈ K
    · have ht := htrans (e x) w hx hw
      have htU := hnearU (e x - w) (by
        have := Metric.mem_ball.mp ht
        linarith)
      change k w • (if e.symm (e x - w) ∈ U then u (e.symm (e x - w)) else 0) =
        k w • (b (e x - w) * if e.symm (e x - w) ∈ U then
          u (e.symm (e x - w)) else 0)
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall ht)]
      simp
    · change k w • _ = k w • _
      simp [hkzero w hw]
  have hjet_coord (i : ℕ) (hi : i ≤ 2) (y : E)
      (hy : y ∈ Metric.ball (e z) (η / 2))
      (v : Fin i → EuclideanSpace ℂ (Fin n)) :
      iteratedFDeriv ℝ i g y (fun a => e (v a)) =
        iteratedFDeriv ℝ i u (e.symm y) v := by
    let G : EuclideanSpace ℂ (Fin n) → ℝ := fun x => g (e x)
    have hG : ContDiff ℝ 2 G := by
      exact hgd.comp e.contDiff
    have hne : ∀ᶠ t in 𝓝 y, g t = u (e.symm t) := hgnear y hy
    have hGeq : G =ᶠ[𝓝 (e.symm y)] u := by
      have hne' : {t : E | g t = u (e.symm t)} ∈ 𝓝 y := hne
      have hne'' : {t : E | g t = u (e.symm t)} ∈ 𝓝 (e (e.symm y)) := by
        rw [e.apply_symm_apply]
        exact hne'
      have hpre : ∀ᶠ x in 𝓝 (e.symm y), g (e x) = u (e.symm (e x)) := by
        change e ⁻¹' {t : E | g t = u (e.symm t)} ∈ 𝓝 (e.symm y)
        exact e.continuous.continuousAt.preimage_mem_nhds hne''
      filter_upwards [hpre] with x hx
      simpa [G] using hx
    have hGjet := (hGeq.iteratedFDeriv ℝ i).eq_of_nhds
    have hpull := iteratedFDeriv_linearIsometry_pullback e g hgd (e.symm y) hi
    calc
      iteratedFDeriv ℝ i g y (fun a => e (v a)) =
          (iteratedFDeriv ℝ i g y).compContinuousLinearMap
            (fun _ => e.toContinuousLinearMap) v := by simp
      _ = iteratedFDeriv ℝ i G (e.symm y) v := by
        rw [hpull, e.apply_symm_apply]
      _ = iteratedFDeriv ℝ i u (e.symm y) v := congrArg (fun L => L v) hGjet
  cases j with
  | zero =>
      have hjet := (hFeq.iteratedFDeriv ℝ 0).eq_of_nhds
      have hpull := iteratedFDeriv_linearIsometry_pullback e F
        (hFd.of_le (by exact ENat.LEInfty.out)) z (j := 0) (by norm_num)
      rw [hjet, hpull]
      ext v
      simp only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
      have hintL : Integrable (fun t : E => k t • g (e z - t)) := by
        exact hgcompact.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hkg
          hgd.continuous (e z)
      have hintR : Integrable (fun t : E =>
          k t • iteratedFDeriv ℝ 0 u (e.symm (e z - t))) := by
        let P : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin 0 => EuclideanSpace ℂ (Fin n)) ℝ :=
          ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => e.toContinuousLinearMap)
        have hJcont : Continuous (fun y : E => P (iteratedFDeriv ℝ 0 g y)) := by
          exact P.continuous.comp (hgd.continuous_iteratedFDeriv (by norm_num))
        have hScont : Continuous (fun t : E => k t • P (iteratedFDeriv ℝ 0 g (e z - t))) :=
          hkcont.smul (hJcont.comp (continuous_const.sub continuous_id))
        have hScomp : HasCompactSupport (fun t : E =>
            k t • P (iteratedFDeriv ℝ 0 g (e z - t))) := hcf.smul_right
        have hS : Integrable (fun t : E =>
            k t • P (iteratedFDeriv ℝ 0 g (e z - t))) (volume : Measure E) :=
          hScont.integrable_of_hasCompactSupport hScomp
        have hAE : (fun t : E => k t • P (iteratedFDeriv ℝ 0 g (e z - t))) =ᵐ[volume]
            (fun t => k t • iteratedFDeriv ℝ 0 u (e.symm (e z - t))) := by
          filter_upwards with t
          by_cases ht : t ∈ K
          · have hy : e z - t ∈ Metric.ball (e z) (η / 2) :=
              htrans (e z) t (Metric.mem_ball_self (by positivity)) ht
            ext w
            have hc := hjet_coord 0 (by norm_num) (e z - t) hy w
            simp only [P, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
            exact congrArg (fun a : ℝ => k t * a) hc
          · simp [hkzero t ht]
        exact hS.congr hAE
      change (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (e z) = _
      rw [convolution_def, ContinuousMultilinearMap.integral_apply hintR]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ K
      · have hy : e z - t ∈ Metric.ball (e z) (η / 2) :=
          htrans (e z) t (Metric.mem_ball_self (by positivity)) ht
        have hc := hjet_coord 0 (by norm_num) (e z - t) hy (fun i => Fin.elim0 i)
        have hc' : g (e z - t) =
            iteratedFDeriv ℝ 0 u (e.symm (e z - t)) v := by simpa using hc
        rw [hc']
        rfl
      · simp [hkzero t ht]
  | succ j =>
      cases j with
      | zero =>
        have hjet := (hFeq.iteratedFDeriv ℝ 1).eq_of_nhds
        have hpull := iteratedFDeriv_linearIsometry_pullback e F
          (hFd.of_le (by exact ENat.LEInfty.out)) z (j := 1) (by norm_num)
        rw [hjet, hpull]
        let P : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin 1 => EuclideanSpace ℂ (Fin n)) ℝ :=
          (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
            (fun _ : Fin 1 => EuclideanSpace ℂ (Fin n)) (fun _ : Fin 1 => E) ℝ)
            (fun _ => e.toContinuousLinearMap)
        rw [localConvolution_jet1_average k g hkg hkcont hcf hgd hgcompact (e z)]
        change P (∫ t : E, k t • iteratedFDeriv ℝ 1 g (e z - t)) = _
        have hJcont : Continuous (fun t : E =>
            k t • iteratedFDeriv ℝ 1 g (e z - t)) := by
          exact hkcont.smul ((hgd.continuous_iteratedFDeriv (by norm_num)).comp
            (continuous_const.sub continuous_id))
        have hJcompact : HasCompactSupport (fun t : E =>
            k t • iteratedFDeriv ℝ 1 g (e z - t)) := hcf.smul_right
        have hJint : Integrable (fun t : E =>
            k t • iteratedFDeriv ℝ 1 g (e z - t)) (volume : Measure E) :=
          hJcont.integrable_of_hasCompactSupport hJcompact
        rw [(P.integral_comp_comm hJint).symm]
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ K
        · have hy : e z - t ∈ Metric.ball (e z) (η / 2) :=
            htrans (e z) t (Metric.mem_ball_self (by positivity)) ht
          have hc := hjet_coord 1 (by norm_num) (e z - t) hy
          ext v
          change k t • iteratedFDeriv ℝ 1 g (e z - t) (fun i => e (v i)) = _
          exact congrArg (fun a => k t • a) (hc v)
        · have hkt : localFixedKernel hη m t = 0 := by
            simpa only [k] using hkzero t ht
          simp [k, hkt]
      | succ j =>
        cases j with
        | zero =>
          have hjet := (hFeq.iteratedFDeriv ℝ 2).eq_of_nhds
          have hpull := iteratedFDeriv_linearIsometry_pullback e F
            (hFd.of_le (by exact ENat.LEInfty.out)) z (j := 2) (by norm_num)
          rw [hjet, hpull]
          let P : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) ℝ :=
            (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
              (fun _ : Fin 2 => EuclideanSpace ℂ (Fin n)) (fun _ : Fin 2 => E) ℝ)
              (fun _ => e.toContinuousLinearMap)
          rw [localConvolution_jet2_average k g hkg hkcont hcf hgd hgcompact (e z)]
          change P (∫ t : E, k t • iteratedFDeriv ℝ 2 g (e z - t)) = _
          have hJcont : Continuous (fun t : E =>
              k t • iteratedFDeriv ℝ 2 g (e z - t)) := by
            exact hkcont.smul ((hgd.continuous_iteratedFDeriv (by norm_num)).comp
              (continuous_const.sub continuous_id))
          have hJcompact : HasCompactSupport (fun t : E =>
              k t • iteratedFDeriv ℝ 2 g (e z - t)) := hcf.smul_right
          have hJint : Integrable (fun t : E =>
              k t • iteratedFDeriv ℝ 2 g (e z - t)) (volume : Measure E) :=
            hJcont.integrable_of_hasCompactSupport hJcompact
          rw [(P.integral_comp_comm hJint).symm]
          apply integral_congr_ae
          filter_upwards with t
          by_cases ht : t ∈ K
          · have hy : e z - t ∈ Metric.ball (e z) (η / 2) :=
              htrans (e z) t (Metric.mem_ball_self (by positivity)) ht
            have hc := hjet_coord 2 (by norm_num) (e z - t) hy
            ext v
            change k t • iteratedFDeriv ℝ 2 g (e z - t) (fun i => e (v i)) = _
            exact congrArg (fun a => k t • a) (hc v)
          · have hkt : localFixedKernel hη m t = 0 := by
              simpa only [k] using hkzero t ht
            simp [k, hkt]
        | succ j => omega

/-- Probability averages of a continuous Banach-valued function converge uniformly on an inner
compact set when the averaging measures concentrate in shrinking balls and those balls remain
inside a compact collar. The integrability hypothesis is stated explicitly so the result applies
to kernel families without imposing global bounds on the function. -/
private theorem compact_collar_probability_average_tendsto_uniformly
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (H : E → F) {K C : Set E} (_hK : IsCompact K) (hC : IsCompact C)
    (hH : ContinuousOn H C) (hKC : K ⊆ C)
    (η : ℝ) (hη : 0 < η)
    (hcollar : ∀ x ∈ K, Metric.closedBall x η ⊆ C)
    (δ : ℕ → ℝ) (hδpos : ∀ m, 0 < δ m)
    (hδ : Tendsto δ atTop (𝓝 0))
    (μ : ℕ → Measure E)
    (hfinite : ∀ m, IsFiniteMeasure (μ m))
    (hprob : ∀ m, μ m Set.univ = 1)
    (hsupport : ∀ m, ∀ᵐ z ∂(μ m), ‖z‖ ≤ δ m)
    (hint : ∀ m, ∀ x ∈ K, Integrable (fun z => H (x - z)) (μ m)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ x ∈ K,
      ‖(∫ z, H (x - z) ∂(μ m)) - H x‖ ≤ ε := by
  have hUC : UniformContinuousOn H C := hC.uniformContinuousOn_of_continuous hH
  intro ε hε
  obtain ⟨r, hr, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hUC) ε hε
  have hmin : 0 < min r η := lt_min hr hη
  have hsmall : ∀ᶠ m : ℕ in atTop, dist (δ m) 0 < min r η :=
    (Metric.tendsto_nhds.1 hδ) (min r η) hmin
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨N, ?_⟩
  intro m hm x hx
  have hδsmall : δ m < min r η := by
    have h := hN m hm
    simpa [Real.dist_eq, abs_of_pos (hδpos m)] using h
  have hδr : δ m < r := lt_of_lt_of_le hδsmall (min_le_left _ _)
  have hδη : δ m ≤ η := le_of_lt (lt_of_lt_of_le hδsmall (min_le_right _ _))
  have hxC : x ∈ C := hKC hx
  have : IsFiniteMeasure (μ m) := hfinite m
  have hintDiff : Integrable (fun z => H (x - z) - H x) (μ m) :=
    (hint m x hx).sub (integrable_const (H x))
  have haverage : (∫ z, H (x - z) ∂(μ m)) - H x =
      ∫ z, (H (x - z) - H x) ∂(μ m) := by
    rw [integral_sub (hint m x hx) (integrable_const (H x)), integral_const]
    rw [show (μ m).real Set.univ = 1 by simp [Measure.real, hprob m]]
    simp
  have hsupportMod : ∀ᵐ z ∂(μ m),
      ‖H (x - z) - H x‖ ≤ ε := (hsupport m).mono fun z hz => by
    have hxz : dist x (x - z) ≤ δ m := by
      rw [dist_eq_norm]
      change ‖x - (x - z)‖ ≤ δ m
      rw [show x - (x - z) = z by abel]
      exact hz
    have hxz' : dist (x - z) x ≤ δ m := by simpa [dist_comm] using hxz
    have hxzη : x - z ∈ Metric.closedBall x η :=
      Metric.mem_closedBall.mpr (le_trans hxz' hδη)
    have hxzC : x - z ∈ C := hcollar x hx hxzη
    have hxzr : dist x (x - z) < r := lt_of_le_of_lt hxz hδr
    have hcont := hmod x hxC (x - z) hxzC hxzr
    simpa [dist_eq_norm, norm_sub_rev] using hcont.le
  calc
    ‖(∫ z, H (x - z) ∂(μ m)) - H x‖ =
        ‖∫ z, (H (x - z) - H x) ∂(μ m)‖ := by rw [haverage]
    _ ≤ ∫ z, ‖H (x - z) - H x‖ ∂(μ m) := norm_integral_le_integral_norm _
    _ ≤ ∫ _z, ε ∂(μ m) := integral_mono_ae hintDiff.norm (integrable_const ε) hsupportMod
    _ = ε := by
      rw [integral_const, show (μ m).real Set.univ = 1 by simp [Measure.real, hprob m]]
      simp

private noncomputable def localKernelProbabilityDensityCanonical {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) : EuclideanSpace ℝ (Fin n × Fin 2) → ENNReal :=
  fun z => ENNReal.ofReal (localFixedKernel (n := n) hη m z)

private noncomputable def localKernelProbabilityMeasureCanonical {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) : Measure (EuclideanSpace ℝ (Fin n × Fin 2)) :=
  volume.withDensity (localKernelProbabilityDensityCanonical (n := n) hη m)

/-- The canonical kernel's probability measure has the expected volume-weighted integrability
bridge for any Banach-valued sample. -/
private theorem localKernelProbability_integrable_iff_canonical {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → F) :
    Integrable f (localKernelProbabilityMeasureCanonical (n := n) hη m) ↔
      Integrable (fun z => localFixedKernel (n := n) hη m z • f z) volume := by
  have hkcont : Continuous (localFixedKernel (n := n) hη m) := by
    have hksmooth : ContDiff ℝ ∞ (localFixedKernel (n := n) hη m) := by
      change ContDiff ℝ ∞ ((localKernelBump (n := n) hη m).normed
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
      exact (localKernelBump (n := n) hη m).contDiff_normed
    exact hksmooth.continuous
  have hdensity : Measurable (localKernelProbabilityDensityCanonical (n := n) hη m) := by
    exact ENNReal.measurable_ofReal.comp hkcont.measurable
  have hfiniteDensity : ∀ᵐ z ∂volume,
      localKernelProbabilityDensityCanonical (n := n) hη m z < ⊤ := by
    filter_upwards with z
    exact ENNReal.ofReal_lt_top
  rw [localKernelProbabilityMeasureCanonical,
    integrable_withDensity_iff_integrable_smul' hdensity hfiniteDensity]
  have heq : (fun z =>
      (localKernelProbabilityDensityCanonical (n := n) hη m z).toReal • f z) =
      (fun z => localFixedKernel (n := n) hη m z • f z) := by
    funext z
    simp [localKernelProbabilityDensityCanonical, ENNReal.toReal_ofReal,
      localFixedKernel_nonneg]
  rw [heq]

private theorem localKernelRadius_tendsto_canonical {η : ℝ} :
    Tendsto (fun m : ℕ => localKernelRadius η m) atTop (𝓝 0) := by
  have hrecip : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have heq : (fun m : ℕ => localKernelRadius η m) =
      fun m : ℕ => (η / 4) * ((1 : ℝ) / ((m : ℝ) + 1)) := by
    funext m
    simp [localKernelRadius]
    field_simp
  rw [heq]
  convert tendsto_const_nhds.mul hrecip using 1 ; simp

private noncomputable def localOriginalJetCanonical {n j : ℕ}
    (u : EuclideanSpace ℂ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n × Fin 2) →
      ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclideanSpace ℂ (Fin n)) ℝ :=
  fun y => iteratedFDeriv ℝ j u ((complexToRealCoordinateEquiv (n := n)).symm y)

/-- The compact-collar average estimate specialized to the canonical kernel probability and the
original-coordinate jet codomain. Only the domain of each jet is pulled back by the real-coordinate
equivalence. -/
private theorem canonical_original_jet_average_bound_canonical {n j : ℕ}
    {η R S : ℝ} {c : EuclideanSpace ℂ (Fin n)}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hη : 0 < η) (hRS : R < S)
    (hjetCont : ContinuousOn (localOriginalJetCanonical (n := n) (j := j) u)
      (Metric.closedBall
        (complexToRealCoordinateEquiv (n := n) c) (S + η / 2)))
    (hweighted : ∀ m x,
      x ∈ Metric.closedBall (complexToRealCoordinateEquiv (n := n) c) R →
      Integrable (fun z => localFixedKernel (n := n) hη m z •
        localOriginalJetCanonical (n := n) (j := j) u (x - z)) volume)
    (hfinite : ∀ m, IsFiniteMeasure (localKernelProbabilityMeasureCanonical (n := n) hη m))
    (hprob : ∀ m, localKernelProbabilityMeasureCanonical (n := n) hη m Set.univ = 1)
    (hsupport : ∀ m, ∀ᵐ z ∂(localKernelProbabilityMeasureCanonical (n := n) hη m),
      ‖z‖ ≤ localKernelRadius η m) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m →
      ∀ x ∈ Metric.closedBall (complexToRealCoordinateEquiv (n := n) c) R,
        ‖(∫ z, localOriginalJetCanonical (n := n) (j := j) u (x - z) ∂
          (localKernelProbabilityMeasureCanonical (n := n) hη m)) -
          localOriginalJetCanonical (n := n) (j := j) u x‖ ≤ ε := by
  classical
  let e := complexToRealCoordinateEquiv (n := n)
  let H := localOriginalJetCanonical (n := n) (j := j) u
  let K : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := Metric.closedBall (e c) R
  let C : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := Metric.closedBall (e c) (S + η / 2)
  have hK : IsCompact K := by
    simpa [K] using (isCompact_closedBall (e c) R)
  have hC : IsCompact C := by
    simpa [C] using (isCompact_closedBall (e c) (S + η / 2))
  have hHC : ContinuousOn H C := hjetCont
  have hKC : K ⊆ C := by
    intro x hx
    apply Metric.mem_closedBall.mpr
    have hx' : dist x (e c) ≤ R := Metric.mem_closedBall.mp hx
    linarith
  have hcollar : ∀ x ∈ K, Metric.closedBall x (η / 2) ⊆ C := by
    intro x hx y hy
    apply Metric.mem_closedBall.mpr
    calc
      dist y (e c) ≤ dist y x + dist x (e c) := dist_triangle _ _ _
      _ ≤ η / 2 + R := add_le_add (Metric.mem_closedBall.mp hy)
        (Metric.mem_closedBall.mp hx)
      _ ≤ S + η / 2 := by linarith
  let δ : ℕ → ℝ := fun m => localKernelRadius η m
  have hδpos : ∀ m, 0 < δ m := fun m => localKernelRadius_pos hη m
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using localKernelRadius_tendsto_canonical (η := η)
  let μ : ℕ → Measure (EuclideanSpace ℝ (Fin n × Fin 2)) :=
    fun m => localKernelProbabilityMeasureCanonical (n := n) hη m
  have hint : ∀ m x, x ∈ K → Integrable (fun z => H (x - z)) (μ m) := by
    intro m x hx
    exact (localKernelProbability_integrable_iff_canonical (n := n) hη m
      (fun z => H (x - z))).2 (hweighted m x hx)
  exact compact_collar_probability_average_tendsto_uniformly H hK hC hHC hKC
    (η / 2) (by positivity) hcollar δ hδpos hδ μ hfinite hprob hsupport hint

private theorem localKernelProbability_univ_canonical {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    localKernelProbabilityMeasureCanonical (n := n) hη m Set.univ = 1 := by
  have hkint : Integrable (localFixedKernel (n := n) hη m) volume := by
    change Integrable ((localKernelBump (n := n) hη m).normed
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) volume
    exact (localKernelBump (n := n) hη m).integrable_normed
  have hknonneg : 0 ≤ᵐ[volume] localFixedKernel (n := n) hη m :=
    Filter.Eventually.of_forall (localFixedKernel_nonneg hη m)
  have hlin : ENNReal.ofReal (∫ z, localFixedKernel (n := n) hη m z ∂volume) =
      ∫⁻ z, ENNReal.ofReal (localFixedKernel (n := n) hη m z) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hkint hknonneg
  have hmass : (∫⁻ z, localKernelProbabilityDensityCanonical (n := n) hη m z ∂volume) = 1 := by
    calc
      _ = ∫⁻ z, ENNReal.ofReal (localFixedKernel (n := n) hη m z) ∂volume := rfl
      _ = ENNReal.ofReal (∫ z, localFixedKernel (n := n) hη m z ∂volume) := hlin.symm
      _ = 1 := by rw [localFixedKernel_integral]; norm_num
  change volume.withDensity (localKernelProbabilityDensityCanonical (n := n) hη m) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ]
  simpa using hmass

private theorem localKernelProbability_finite_canonical {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    IsFiniteMeasure (localKernelProbabilityMeasureCanonical (n := n) hη m) := by
  refine ⟨?_⟩
  rw [localKernelProbability_univ_canonical hη m]
  exact ENNReal.one_lt_top

private theorem localKernelProbabilityDensity_measurable_canonical {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    Measurable (localKernelProbabilityDensityCanonical (n := n) hη m) := by
  have hkcont : Continuous (localFixedKernel (n := n) hη m) := by
    have hksmooth : ContDiff ℝ ∞ (localFixedKernel (n := n) hη m) := by
      change ContDiff ℝ ∞ ((localKernelBump (n := n) hη m).normed
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
      exact (localKernelBump (n := n) hη m).contDiff_normed
    exact hksmooth.continuous
  exact ENNReal.measurable_ofReal.comp hkcont.measurable

private theorem localKernelProbability_support_canonical {n : ℕ} {η : ℝ}
    (hη : 0 < η) (m : ℕ) :
    ∀ᵐ z ∂(localKernelProbabilityMeasureCanonical (n := n) hη m),
      ‖z‖ ≤ localKernelRadius η m := by
  have hksupp : Function.support (localFixedKernel (n := n) hη m) =
      Metric.ball (0 : EuclideanSpace ℝ (Fin n × Fin 2)) (localKernelRadius η m) := by
    change Function.support ((localKernelBump (n := n) hη m).normed
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) = _
    rw [(localKernelBump (n := n) hη m).support_normed_eq]
    simp [localKernelBump]
  rw [localKernelProbabilityMeasureCanonical,
    ae_withDensity_iff (localKernelProbabilityDensity_measurable_canonical hη m)]
  filter_upwards with z hden
  have hknezero : localFixedKernel (n := n) hη m z ≠ 0 := by
    intro hkzero
    apply hden
    simp [localKernelProbabilityDensityCanonical, hkzero]
  have hzsupport : z ∈ Function.support (localFixedKernel (n := n) hη m) := by
    change localFixedKernel (n := n) hη m z ≠ 0
    exact hknezero
  rw [hksupp] at hzsupport
  have hdist : dist z 0 < localKernelRadius η m := Metric.mem_ball.mp hzsupport
  simpa [dist_eq_norm] using hdist.le

private theorem localKernelProbability_sample_weighted_integrable_canonical
    {n : ℕ} {η : ℝ} (hη : 0 < η) (m : ℕ) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F]
    (H : EuclideanSpace ℝ (Fin n × Fin 2) → F) {K C : Set (EuclideanSpace ℝ (Fin n × Fin 2))}
    (hC : IsCompact C) (hH : ContinuousOn H C)
    (hcollar : ∀ x ∈ K, Metric.closedBall x (η / 2) ⊆ C)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) (hx : x ∈ K)
    (hradius : localKernelRadius η m ≤ η / 2) :
    Integrable (fun z => localFixedKernel (n := n) hη m z • H (x - z)) volume := by
  classical
  let q : EuclideanSpace ℝ (Fin n × Fin 2) → EuclideanSpace ℝ (Fin n × Fin 2) :=
    fun z => x - z
  let s := q ⁻¹' C
  let g : EuclideanSpace ℝ (Fin n × Fin 2) → F :=
    s.piecewise (fun z => H (q z)) (fun _ => 0)
  obtain ⟨B, hB⟩ := (hC.image_of_continuousOn hH).isBounded.subset_closedBall (0 : F)
  have hBound : ∀ y ∈ C, ‖H y‖ ≤ B := by
    intro y hy
    have hmem : H y ∈ H '' C := ⟨y, hy, rfl⟩
    have hball := Metric.mem_closedBall.mp (hB hmem)
    simpa [dist_eq_norm] using hball
  have hxC : x ∈ C := hcollar x hx (Metric.mem_closedBall.mpr (by simp; linarith))
  have hBnonneg : 0 ≤ B := (norm_nonneg (H x)).trans (hBound x hxC)
  have hsClosed : IsClosed s := hC.isClosed.preimage (by fun_prop)
  have hsMeas : MeasurableSet s := hsClosed.measurableSet
  have hgCont : ContinuousOn (fun z => H (q z)) s := by
    apply hH.comp (by fun_prop : Continuous q).continuousOn
    intro z hz
    exact hz
  have hgmeas : Measurable g := by
    exact hgCont.measurable_piecewise continuousOn_const hsMeas
  have hssep : TopologicalSpace.IsSeparable s :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  have himage : TopologicalSpace.IsSeparable
      (Set.range (s.domRestrict (fun z => H (q z)))) :=
    TopologicalSpace.isSeparable_range
      (continuousOn_iff_continuous_domRestrict.mp hgCont)
  have hrange : TopologicalSpace.IsSeparable (Set.range g) := by
    apply (himage.union (finite_singleton (0 : F)).isSeparable).mono
    rintro y ⟨z, rfl⟩
    by_cases hz : z ∈ s
    · left
      exact ⟨⟨z, hz⟩, by simp [g, hz]⟩
    · right
      simp [g, hz]
  have hgSM : StronglyMeasurable g :=
    (stronglyMeasurable_iff_measurable_separable).2 ⟨hgmeas, hrange⟩
  have hgBound : ∀ᵐ z ∂volume, ‖g z‖ ≤ B := by
    filter_upwards with z
    by_cases hz : z ∈ s
    · simpa [g, hz] using hBound (q z) hz
    · simpa [g, hz] using hBnonneg
  have hkint : Integrable (localFixedKernel (n := n) hη m) volume := by
    change Integrable ((localKernelBump (n := n) hη m).normed
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) volume
    exact (localKernelBump (n := n) hη m).integrable_normed
  have hksupp : Function.support (localFixedKernel (n := n) hη m) =
      Metric.ball (0 : EuclideanSpace ℝ (Fin n × Fin 2)) (localKernelRadius η m) := by
    change Function.support ((localKernelBump (n := n) hη m).normed
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) = _
    rw [(localKernelBump (n := n) hη m).support_normed_eq]
    simp [localKernelBump]
  have heq : (fun z => localFixedKernel (n := n) hη m z • H (x - z)) =
      (fun z => localFixedKernel (n := n) hη m z • g z) := by
    funext z
    by_cases hk : localFixedKernel (n := n) hη m z = 0
    · simp [hk]
    · have hmem : z ∈ Function.support (localFixedKernel (n := n) hη m) := by
        change localFixedKernel (n := n) hη m z ≠ 0
        exact hk
      rw [hksupp] at hmem
      have hdist : dist z 0 < localKernelRadius η m := Metric.mem_ball.mp hmem
      have hnorm : ‖z‖ ≤ localKernelRadius η m := by simpa [dist_eq_norm] using hdist.le
      have hqdist : dist (x - z) x ≤ η / 2 := by
        rw [dist_eq_norm, show (x - z) - x = -z by abel, norm_neg]
        exact le_trans hnorm hradius
      have hqC : x - z ∈ C := hcollar x hx (Metric.mem_closedBall.mpr hqdist)
      have hzS : z ∈ s := by
        change x - z ∈ C
        exact hqC
      simp [g, hzS, q]
  rw [heq]
  exact hkint.smul_bdd B hgSM.aestronglyMeasurable hgBound

private theorem canonical_original_jet_weighted_integrable_canonical {n j : ℕ}
    {η R S : ℝ} {c : EuclideanSpace ℂ (Fin n)}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hη : 0 < η) (hRS : R < S)
    (hjetCont : ContinuousOn (localOriginalJetCanonical (n := n) (j := j) u)
      (Metric.closedBall
        (complexToRealCoordinateEquiv (n := n) c) (S + η / 2))) :
    ∀ m x, x ∈ Metric.closedBall (complexToRealCoordinateEquiv (n := n) c) R →
      Integrable (fun z => localFixedKernel (n := n) hη m z •
        localOriginalJetCanonical (n := n) (j := j) u (x - z)) volume := by
  classical
  let e := complexToRealCoordinateEquiv (n := n)
  let H := localOriginalJetCanonical (n := n) (j := j) u
  let K : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := Metric.closedBall (e c) R
  let C : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := Metric.closedBall (e c) (S + η / 2)
  let : MeasurableSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclideanSpace ℂ (Fin n)) ℝ) :=
    borel _
  let : BorelSpace
      (ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclideanSpace ℂ (Fin n)) ℝ) := ⟨rfl⟩
  have hC : IsCompact C := by
    simpa [C] using (isCompact_closedBall (e c) (S + η / 2))
  have hHC : ContinuousOn H C := hjetCont
  have hcollar : ∀ x ∈ K, Metric.closedBall x (η / 2) ⊆ C := by
    intro x hx y hy
    apply Metric.mem_closedBall.mpr
    calc
      dist y (e c) ≤ dist y x + dist x (e c) := dist_triangle _ _ _
      _ ≤ η / 2 + R := add_le_add (Metric.mem_closedBall.mp hy)
        (Metric.mem_closedBall.mp hx)
      _ ≤ S + η / 2 := by linarith
  intro m x hx
  apply localKernelProbability_sample_weighted_integrable_canonical hη m H hC hHC
    hcollar x hx
  rw [localKernelRadius]
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [mul_nonneg hη.le (Nat.cast_nonneg m)]

/-- Probability, support, and density normalization are all instantiated for the actual canonical
kernel; only the compact-collar weighted sample-integrability input remains. -/
private theorem canonical_original_jet_average_bound_full_canonical {n j : ℕ}
    {η R S : ℝ} {c : EuclideanSpace ℂ (Fin n)}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hη : 0 < η) (hRS : R < S)
    (hjetCont : ContinuousOn (localOriginalJetCanonical (n := n) (j := j) u)
      (Metric.closedBall
        (complexToRealCoordinateEquiv (n := n) c) (S + η / 2)))
    (hweighted : ∀ m x,
      x ∈ Metric.closedBall (complexToRealCoordinateEquiv (n := n) c) R →
      Integrable (fun z => localFixedKernel (n := n) hη m z •
        localOriginalJetCanonical (n := n) (j := j) u (x - z)) volume) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m →
      ∀ x ∈ Metric.closedBall (complexToRealCoordinateEquiv (n := n) c) R,
        ‖(∫ z, localOriginalJetCanonical (n := n) (j := j) u (x - z) ∂
          (localKernelProbabilityMeasureCanonical (n := n) hη m)) -
          localOriginalJetCanonical (n := n) (j := j) u x‖ ≤ ε := by
  exact canonical_original_jet_average_bound_canonical hη hRS hjetCont hweighted
    (fun m => localKernelProbability_finite_canonical hη m)
    (fun m => localKernelProbability_univ_canonical hη m)
    (fun m => localKernelProbability_support_canonical hη m)

private theorem canonical_original_jet_average_bound_complete_canonical {n j : ℕ}
    {η R S : ℝ} {c : EuclideanSpace ℂ (Fin n)}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hη : 0 < η) (hRS : R < S)
    (hjetCont : ContinuousOn (localOriginalJetCanonical (n := n) (j := j) u)
      (Metric.closedBall
        (complexToRealCoordinateEquiv (n := n) c) (S + η / 2))) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m →
      ∀ x ∈ Metric.closedBall (complexToRealCoordinateEquiv (n := n) c) R,
        ‖(∫ z, localOriginalJetCanonical (n := n) (j := j) u (x - z) ∂
          (localKernelProbabilityMeasureCanonical (n := n) hη m)) -
          localOriginalJetCanonical (n := n) (j := j) u x‖ ≤ ε := by
  exact canonical_original_jet_average_bound_full_canonical hη hRS hjetCont
    (canonical_original_jet_weighted_integrable_canonical hη hRS hjetCont)

private theorem closedBall_subset_thickening_larger_ball_canonical {n : ℕ}
    {c : EuclideanSpace ℂ (Fin n)} {R S η : ℝ}
    (hR : 0 < R) (hRS : R < S) (hη : 0 < η) :
    Metric.closedBall c (S + η / 2) ⊆
      Metric.thickening η (Metric.closedBall c S) := by
  intro x hx
  have hS : 0 < S := lt_trans hR hRS
  have hdist := Metric.mem_closedBall.mp hx
  rw [Metric.mem_thickening_iff]
  by_cases hxS : dist x c ≤ S
  · refine ⟨x, Metric.mem_closedBall.mpr hxS, ?_⟩
    simpa using hη
  · have hSd : S < dist x c := lt_of_not_ge hxS
    have hdpos : 0 < dist x c := lt_trans hS hSd
    have hnorm : ‖x - c‖ = dist x c := by rw [dist_eq_norm]
    let y := c + (S / dist x c) • (x - c)
    have hyc : y - c = (S / dist x c) • (x - c) := by
      dsimp [y]
      module
    have hscale : 0 ≤ S / dist x c := div_nonneg hS.le hdpos.le
    have hcy : dist y c = S := by
      rw [dist_eq_norm, hyc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale,
        hnorm]
      field_simp [ne_of_gt hdpos]
    have hxy : x - y = (1 - S / dist x c) • (x - c) := by
      dsimp [y]
      module
    have hscale' : 0 ≤ 1 - S / dist x c := by
      have hle : S / dist x c ≤ 1 := (div_le_one hdpos).2 hSd.le
      linarith
    have hxyDist : dist x y = dist x c - S := by
      rw [dist_eq_norm, hxy, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale',
        hnorm]
      field_simp [ne_of_gt hdpos]
    refine ⟨y, Metric.mem_closedBall.mpr (le_of_eq hcy), ?_⟩
    rw [hxyDist]
    linarith

private theorem localOriginalJet_continuousOn_expandedBall_canonical {n j : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)}
    {R S η : ℝ} {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hR : 0 < R) (hRS : R < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hj : j ≤ 2) :
    ContinuousOn (localOriginalJetCanonical (n := n) (j := j) u)
      (Metric.closedBall
        (complexToRealCoordinateEquiv (n := n) c) (S + η / 2)) := by
  classical
  let e := complexToRealCoordinateEquiv (n := n)
  have hExpanded : Metric.closedBall c (S + η / 2) ⊆ U :=
    (closedBall_subset_thickening_larger_ball_canonical hR hRS hη).trans hCollar
  have hDcont : ContinuousOn (iteratedFDeriv ℝ j u) U := by
    intro z hz
    exact ((hu z hz).contDiffAt (hU.mem_nhds hz)).continuousAt_iteratedFDeriv
      (by exact_mod_cast hj) |>.continuousWithinAt
  have hpull : ContinuousOn (fun y => iteratedFDeriv ℝ j u (e.symm y))
      (Metric.closedBall (e c) (S + η / 2)) := by
    apply hDcont.comp (by fun_prop : Continuous e.symm).continuousOn
    intro y hy
    apply hExpanded
    apply Metric.mem_closedBall.mpr
    have hdist : dist (e.symm y) c = dist y (e c) := by
      rw [← e.isometry.dist_eq, e.apply_symm_apply]
    rw [hdist]
    exact Metric.mem_closedBall.mp hy
  change ContinuousOn (fun y => iteratedFDeriv ℝ j u (e.symm y)) _
  exact hpull

/-- The canonical averages of the original-coordinate solution jet converge uniformly on the
inner real-coordinate ball under the geometric and regularity hypotheses used for the solution
jets. This packages the actual continuity premise with the complete kernel-average estimate. -/
private theorem canonical_original_jet_average_bound_from_solution_hypotheses_canonical
    {n j : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {R S η : ℝ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hR : 0 < R) (hRS : R < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hj : j ≤ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m →
      ∀ x ∈ Metric.closedBall (complexToRealCoordinateEquiv (n := n) c) R,
        ‖(∫ z, localOriginalJetCanonical (n := n) (j := j) u (x - z) ∂
          (localKernelProbabilityMeasureCanonical (n := n) hη m)) -
          localOriginalJetCanonical (n := n) (j := j) u x‖ ≤ ε := by
  exact canonical_original_jet_average_bound_complete_canonical hη hRS
    (localOriginalJet_continuousOn_expandedBall_canonical hU hR hRS hη hCollar hu hj)

/-- The same canonical-average convergence estimate expressed on the original complex ball,
with the averaging variable pulled back by the real-coordinate isometry. -/
private theorem canonical_original_jet_average_bound_complex_ball_from_solution_hypotheses_canonical
    {n j : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {R S η : ℝ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hR : 0 < R) (hRS : R < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hj : j ≤ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m →
      ∀ x ∈ Metric.closedBall c R,
        ‖(∫ z, localOriginalJetCanonical (n := n) (j := j) u
          (complexToRealCoordinateEquiv (n := n) x - z) ∂
            (localKernelProbabilityMeasureCanonical (n := n) hη m)) -
          iteratedFDeriv ℝ j u x‖ ≤ ε := by
  have havg := canonical_original_jet_average_bound_from_solution_hypotheses_canonical
    hU hR hRS hη hCollar hu hj
  intro ε hε
  obtain ⟨N, hN⟩ := havg ε hε
  refine ⟨N, ?_⟩
  intro m hm x hx
  have hex : complexToRealCoordinateEquiv (n := n) x ∈
      Metric.closedBall (complexToRealCoordinateEquiv (n := n) c) R := by
    apply Metric.mem_closedBall.mpr
    rw [(complexToRealCoordinateEquiv (n := n)).isometry.dist_eq]
    exact Metric.mem_closedBall.mp hx
  have hbound := hN m hm _ hex
  simpa [localOriginalJetCanonical] using hbound

/-- The actual canonical solution rows are smooth, bounded, and converge through order two. -/
theorem localFixedMollify_solutionJets {n : ℕ}
    {K₀ : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {R S η : ℝ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hR : 0 < R) (hRS : R < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hBound : ∀ z ∈ U, |u z| ≤ K₀) :
    (∀ m, ContDiffOn ℝ ∞ (localFixedMollify U hη m u) (Metric.ball c S)) ∧
    (∀ m z, z ∈ Metric.ball c S → |localFixedMollify U hη m u z| ≤ K₀) ∧
    (∀ j ≤ 2, TendstoLocallyUniformlyOn
      (fun m z ↦ iteratedFDeriv ℝ j (localFixedMollify U hη m u) z)
      (iteratedFDeriv ℝ j u) atTop (Metric.ball c R)) := by
  classical
  have hJets : ∀ j ≤ 2, TendstoLocallyUniformlyOn
      (fun m z ↦ iteratedFDeriv ℝ j (localFixedMollify U hη m u) z)
      (iteratedFDeriv ℝ j u) atTop (Metric.ball c R) := by
    intro j hj
    let e := complexToRealCoordinateEquiv (n := n)
    let H := localOriginalJetCanonical (n := n) (j := j) u
    have hJcont := localOriginalJet_continuousOn_expandedBall_canonical
      hU hR hRS hη hCollar hu hj
    have havg := canonical_original_jet_average_bound_complex_ball_from_solution_hypotheses_canonical
      hU hR hRS hη hCollar hu hj
    have hUniform : TendstoUniformlyOn
        (fun m z ↦ iteratedFDeriv ℝ j (localFixedMollify U hη m u) z)
        (iteratedFDeriv ℝ j u) atTop (Metric.ball c R) := by
      intro W hW
      obtain ⟨ε, hε, hWε⟩ := Metric.uniformity_basis_dist.mem_iff.mp hW
      obtain ⟨N, hN⟩ := havg (ε / 2) (half_pos hε)
      filter_upwards [eventually_atTop.2 ⟨N, fun m hm => hm⟩] with m hm
      intro z hz
      have hzC : z ∈ Metric.closedBall c R := Metric.ball_subset_closedBall hz
      have heC : e z ∈ Metric.closedBall (e c) R := by
        apply Metric.mem_closedBall.mpr
        rw [e.isometry.dist_eq]
        exact Metric.mem_closedBall.mp hzC
      have hmeasureEq :
          (∫ t, H (e z - t) ∂localKernelProbabilityMeasureCanonical (n := n) hη m) =
            ∫ t, localFixedKernel hη m t • H (e z - t) := by
        change (∫ t, H (e z - t) ∂(volume.withDensity
          (localKernelProbabilityDensityCanonical (n := n) hη m))) = _
        rw [integral_withDensity_eq_integral_toReal_smul
          (localKernelProbabilityDensity_measurable_canonical hη m)
          (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards with t
        simp [localKernelProbabilityDensityCanonical, ENNReal.toReal_ofReal,
          localFixedKernel_nonneg hη m t]
      have hcomm := localFixedMollify_jet_commutation hU hR hRS hη hCollar hu j hj m z hz
      have hcomm' : iteratedFDeriv ℝ j (localFixedMollify U hη m u) z =
          ∫ t, localFixedKernel hη m t • H (e z - t) := by
        simpa [H, localOriginalJetCanonical, e] using hcomm
      have haverage : iteratedFDeriv ℝ j (localFixedMollify U hη m u) z =
          ∫ t, H (e z - t) ∂localKernelProbabilityMeasureCanonical (n := n) hη m :=
        hcomm'.trans hmeasureEq.symm
      have hbound := hN m hm z hzC
      have hbound' : ‖(∫ t, H (e z - t) ∂
          localKernelProbabilityMeasureCanonical (n := n) hη m) -
          iteratedFDeriv ℝ j u z‖ ≤ ε / 2 := by
        simpa [H, localOriginalJetCanonical, e] using hbound
      apply hWε
      change dist (iteratedFDeriv ℝ j u z)
        (iteratedFDeriv ℝ j (localFixedMollify U hη m u) z) < ε
      rw [dist_eq_norm]
      calc
        _ = ‖iteratedFDeriv ℝ j (localFixedMollify U hη m u) z -
            iteratedFDeriv ℝ j u z‖ := by rw [norm_sub_rev]
        _ ≤ ε / 2 := by rw [haverage]; exact hbound'
        _ < ε := by linarith
    exact hUniform.tendstoLocallyUniformlyOn
  refine ⟨?_, ?_, hJets⟩
  · intro m
    let e := complexToRealCoordinateEquiv (n := n)
    let s : Set (EuclideanSpace ℝ (Fin n × Fin 2)) := (fun x => e.symm x) ⁻¹' U
    let g : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ :=
      fun x => if e.symm x ∈ U then u (e.symm x) else 0
    have hes : Continuous e.symm := by fun_prop
    have hs : IsOpen s := hU.preimage hes
    have hgmeas : Measurable g := by
      have hc : ContinuousOn (fun x => u (e.symm x)) s := by
        apply hu.continuousOn.comp hes.continuousOn
        intro x hx
        exact hx
      have heq : g = s.piecewise (fun x => u (e.symm x)) (fun _ => 0) := by
        funext x
        by_cases hx : e.symm x ∈ U <;> simp [g, s, hx]
      rw [heq]
      exact hc.measurable_piecewise continuousOn_const hs.measurableSet
    have hgbound : ∀ᵐ x : EuclideanSpace ℝ (Fin n × Fin 2) ∂volume,
        ‖g x‖ ≤ (K₀ : ℝ) := by
      filter_upwards with x
      by_cases hx : e.symm x ∈ U
      · simpa [g, hx, Real.norm_eq_abs] using hBound (e.symm x) hx
      · simp [g, hx]
    have hgmem : MemLp g (⊤ : ENNReal) volume :=
      memLp_top_of_bound hgmeas.aestronglyMeasurable (K₀ : ℝ) hgbound
    have hgloc : LocallyIntegrable g volume := hgmem.locallyIntegrable le_top
    have hcf : HasCompactSupport (localFixedKernel (n := n) hη m) := by
      change HasCompactSupport ((localKernelBump hη m).normed
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) )
      exact (localKernelBump hη m).hasCompactSupport_normed
    have hf : ContDiff ℝ ∞ (localFixedKernel (n := n) hη m) := by
      change ContDiff ℝ ∞ ((localKernelBump hη m).normed
        (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
      exact (localKernelBump hη m).contDiff_normed
    let f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ :=
      localFixedKernel (n := n) hη m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g
    have hfc : ContDiff ℝ ∞ f := by
      exact hcf.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hf hgloc
    have heq : localFixedMollify U hη m u = fun z => f (e z) := by
      funext z
      change (∫ w, localFixedKernel (n := n) hη m w •
        (if e.symm (e z - w) ∈ U then u (e.symm (e z - w)) else 0) ∂volume) =
          (localFixedKernel (n := n) hη m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) (e z)
      rw [MeasureTheory.convolution_def]
      rfl
    rw [heq]
    exact (hfc.comp (by fun_prop)).contDiffOn
  ·
    intro m z hz
    let e := complexToRealCoordinateEquiv (n := n)
    let q : EuclideanSpace ℝ (Fin n × Fin 2) → EuclideanSpace ℂ (Fin n) :=
      fun w => e.symm (e z - w)
    let s := q ⁻¹' U
    have hq : Continuous q := by fun_prop
    have hs : IsOpen s := hU.preimage hq
    have hgmeas : Measurable (fun w => if q w ∈ U then u (q w) else 0) := by
      have hc : ContinuousOn (fun w => u (q w)) s := by
        apply hu.continuousOn.comp hq.continuousOn
        intro w hw
        exact hw
      have heq : (fun w => if q w ∈ U then u (q w) else 0) =
          s.piecewise (fun w => u (q w)) (fun _ => 0) := by
        funext w
        by_cases hw : q w ∈ U <;> simp [s, hw]
      rw [heq]
      exact hc.measurable_piecewise continuousOn_const hs.measurableSet
    have hkint : MeasureTheory.Integrable (localFixedKernel hη m)
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
      change MeasureTheory.Integrable ((localKernelBump hη m).normed
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) _
      exact (localKernelBump hη m).integrable_normed
    have hgBound : ∀ᵐ w : EuclideanSpace ℝ (Fin n × Fin 2) ∂MeasureTheory.volume,
        ‖(if q w ∈ U then u (q w) else 0)‖ ≤ (K₀ : ℝ) := by
      filter_upwards with w
      by_cases hw : q w ∈ U
      · simpa [hw, Real.norm_eq_abs] using hBound (q w) hw
      · simp [hw]
    have hint : MeasureTheory.Integrable (fun w => localFixedKernel hη m w *
        (if q w ∈ U then u (q w) else 0))
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
      hkint.mul_bdd hgmeas.aestronglyMeasurable hgBound
    have hnorm : ‖∫ w, localFixedKernel hη m w *
        (if q w ∈ U then u (q w) else 0)‖ ≤
        ∫ w, ‖localFixedKernel hη m w * (if q w ∈ U then u (q w) else 0)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    have hpoint : ∀ w, ‖localFixedKernel hη m w *
        (if q w ∈ U then u (q w) else 0)‖ ≤
        (K₀ : ℝ) * localFixedKernel hη m w := by
      intro w
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (localFixedKernel_nonneg hη m w)]
      by_cases hw : q w ∈ U
      · rw [ite_eq_left hw]
        calc
          _ ≤ localFixedKernel hη m w * (K₀ : ℝ) :=
            mul_le_mul_of_nonneg_left (hBound (q w) hw)
              (localFixedKernel_nonneg hη m w)
          _ = (K₀ : ℝ) * localFixedKernel hη m w := mul_comm _ _
      · rw [ite_eq_right hw]
        simpa using mul_nonneg K₀.2 (localFixedKernel_nonneg hη m w)
    have hintBound : MeasureTheory.Integrable (fun w : EuclideanSpace ℝ (Fin n × Fin 2) =>
        (K₀ : ℝ) * localFixedKernel hη m w) MeasureTheory.volume := hkint.const_mul _
    have hIntBound : (∫ w, ‖localFixedKernel hη m w *
        (if q w ∈ U then u (q w) else 0)‖) ≤ (K₀ : ℝ) := by
      calc
        _ ≤ ∫ w, (K₀ : ℝ) * localFixedKernel hη m w :=
          MeasureTheory.integral_mono_ae (hint.norm) hintBound (Filter.Eventually.of_forall hpoint)
        _ = (K₀ : ℝ) := by
          rw [MeasureTheory.integral_const_mul]
          simp [localFixedKernel_integral]
    change |∫ w, localFixedKernel hη m w •
        (if e.symm (e z - w) ∈ U then u (e.symm (e z - w)) else 0)| ≤ (K₀ : ℝ)
    simpa [smul_eq_mul, q] using hnorm.trans hIntBound

end CalabiYau.Schauder
