module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.Basic

/-!
# Trace contraction and fixed-kernel Hessian commutation

The error uses `A i j` with `H j i` in the trace. Realification is an isometry and the complex
Hessian contains its existing factor of one quarter; no new scaling is introduced here.
-/

@[expose] public section

open Set Filter Matrix
open scoped ContDiff NNReal Topology

namespace CalabiYau.Schauder

/-- A C2 function has continuous complex Hessian entries on an open domain. -/
theorem continuousOn_complexHessian_entry {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (j l : Fin n) :
    ContinuousOn (fun z ↦ complexHessian u z j l) U := by
  have hDu : ContDiffOn ℝ 1 (fderiv ℝ u) U :=
    hu.fderiv_of_isOpen hU (by norm_num)
  have hD₂u : ContinuousOn (fderiv ℝ (fderiv ℝ u)) U :=
    hDu.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hEval (v w : EuclideanSpace ℂ (Fin n)) :
      ContinuousOn (fun z ↦ fderiv ℝ (fderiv ℝ u) z v w) U := by
    fun_prop
  have hFormula : ContinuousOn (fun z ↦
      ((fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1)
          (EuclideanSpace.single l 1) : ℂ) +
        fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single l 1) +
        Complex.I * (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single l 1) -
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
            (EuclideanSpace.single l 1))) / 4) U := by
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  apply hFormula.congr
  intro z hz
  exact complexHessian_apply ((hu z hz).contDiffAt (hU.mem_nhds hz)) j l

/-- Fixed mollification of the actual operator differs by the finite scalar covariances.
This includes local integrability, derivative commutation, and trace/integral linearity. -/
theorem localFixedMollify_trace_covariance {n : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))} {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hA₀ : ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U)
    (hu : ContDiffOn ℝ 2 u U) (m : ℕ) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ Metric.ball c S) :
    complexEllipticOp (localFixedCoefficientSeq U hη A m) (localFixedMollify U hη m u) z =
      localFixedMollify U hη m (complexEllipticOp A u) z +
        ∑ i, ∑ j, (localMollificationCovariance U hη m
          (fun y ↦ A y i j) (fun y ↦ complexHessian u y j i) z).re := by
  exact (open MeasureTheory in by
    classical
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
    have hsample (w : E) (hw : w ∈ K) : e.symm (e z - w) ∈ U := by
      apply hCollar
      apply Metric.mem_thickening_iff.mpr
      refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
      have hnorm : ‖w‖ ≤ localKernelRadius η m := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right] using hw
      have hdist : dist (e.symm (e z - w)) z = ‖w‖ := by
        rw [← e.symm_apply_apply z, e.symm.isometry.dist_eq, dist_eq_norm]
        simp
      rw [hdist]
      linarith
    have hint {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
        (f : EuclideanSpace ℂ (Fin n) → F) (hf : ContinuousOn f U) :
        Integrable (fun w : E ↦ k w •
          (if e.symm (e z - w) ∈ U then f (e.symm (e z - w)) else 0)) := by
      have hc : ContinuousOn (fun w : E ↦ k w • f (e.symm (e z - w))) K :=
        hkcont.continuousOn.smul (hf.comp (by fun_prop) hsample)
      have hc' : ContinuousOn (fun w : E ↦ k w •
          (if e.symm (e z - w) ∈ U then f (e.symm (e z - w)) else 0)) K := by
        apply hc.congr
        intro w hw
        simp only [ite_eq_left (hsample w hw)]
      exact (hc'.integrableOn_compact (isCompact_closedBall _ _)).integrable_of_forall_notMem_eq_zero
        (fun w hw ↦ by simp [hkzero w hw])
    have hprod (i j : Fin n) : Integrable (fun w : E ↦ k w •
        (if e.symm (e z - w) ∈ U then
          A (e.symm (e z - w)) i j * complexHessian u (e.symm (e z - w)) j i else 0)) :=
      hint _ ((hA₀ i j).continuousOn.mul (continuousOn_complexHessian_entry hU hu j i))
    have hH (j i : Fin n) : complexHessian (localFixedMollify U hη m u) z j i =
        localFixedMollify U hη m (fun y ↦ complexHessian u y j i) z := by
      have hnearU (y : E) (hy : dist y (e z) < η) : e.symm y ∈ U := by
        apply hCollar
        apply Metric.mem_thickening_iff.mpr
        refine ⟨z, Metric.ball_subset_closedBall hz, ?_⟩
        have hedist : dist (e.symm y) z = dist y (e z) := by
          rw [← e.isometry.dist_eq, e.apply_symm_apply]
        rwa [hedist]
      let b : ContDiffBump (e z) :=
        ⟨η / 2, 3 * η / 4, by positivity, by linarith⟩
      let g : E → ℝ := fun y ↦ b y * if e.symm y ∈ U then u (e.symm y) else 0
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
          have heq : g =ᶠ[𝓝 y] fun t ↦ b t * u (e.symm t) := by
            filter_upwards [hcond] with t ht
            change e.symm t ∈ U at ht
            simp only [g, ite_eq_left ht]
          apply ContDiffAt.congr_of_eventuallyEq _ heq
          exact b.contDiff.contDiffAt.mul
            (((hu _ hyU).contDiffAt (hU.mem_nhds hyU)).comp y (by fun_prop))
        · have heq : g =ᶠ[𝓝 y] fun _ ↦ 0 := by
            filter_upwards [(isClosed_tsupport (b : E → ℝ)).isOpen_compl.mem_nhds hy] with t ht
            simp only [g, image_eq_zero_of_notMem_tsupport ht, zero_mul]
          exact contDiffAt_const.congr_of_eventuallyEq heq
      have hgnear (y : E) (hy : y ∈ Metric.ball (e z) (η / 2)) :
          g =ᶠ[𝓝 y] fun t ↦ u (e.symm t) := by
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
        linarith
      let F : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦ (convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume) (e x)
      have hFd : ContDiff ℝ 2 F :=
        (hgcompact.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
          hkcont.locallyIntegrable hgd).comp e.toContinuousLinearEquiv.contDiff
      have hFeq : localFixedMollify U hη m u =ᶠ[𝓝 z] F := by
        have hnh : ∀ᶠ x in 𝓝 z, e x ∈ Metric.ball (e z) (η / 8) :=
          e.continuous.continuousAt.preimage_mem_nhds
            (Metric.ball_mem_nhds _ (by positivity))
        filter_upwards [hnh] with x hx
        apply integral_congr_ae
        filter_upwards with w
        simp only [ContinuousLinearMap.lsmul_apply]
        by_cases hw : w ∈ K
        · have ht := htrans (e x) w hx hw
          have htU := hnearU (e x - w) (by
            have := Metric.mem_ball.mp ht
            linarith)
          change k w • (if e.symm (e x - w) ∈ U then u (e.symm (e x - w)) else 0) =
            k w • g (e x - w)
          rw [ite_eq_left htU, (hgnear _ ht).eq_of_nhds]
        · change k w • _ = k w • _
          simp [hkzero w hw]
      have conv_hessian (g : E → ℝ) (hg : ContDiff ℝ 2 g)
          (hgc : HasCompactSupport g) (x v w : E) :
          fderiv ℝ (fderiv ℝ (convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume)) x v w =
            ∫ y, k y * fderiv ℝ (fderiv ℝ g) (x - y) v w := by
        let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
        have hkg : LocallyIntegrable k := hkcont.locallyIntegrable
        have hdg : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
        have hfirst (a : E) : fderiv ℝ (convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume) a =
            (convolution k (fderiv ℝ g) (L.precompR E) volume) a :=
          (hgc.hasFDerivAt_convolution_right L hkg (hg.of_le (by norm_num)) a).fderiv
        have hsecond : fderiv ℝ (fderiv ℝ (convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume)) x =
            (convolution k (fderiv ℝ (fderiv ℝ g)) ((L.precompR E).precompR E) volume) x := by
          rw [show fderiv ℝ (convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume) = convolution k (fderiv ℝ g) (L.precompR E) volume by funext a; exact hfirst a]
          exact ((hgc.fderiv ℝ).hasFDerivAt_convolution_right (L.precompR E) hkg hdg x).fderiv
        rw [hsecond]
        have hint : Integrable (fun y ↦ k y • fderiv ℝ (fderiv ℝ g) (x - y)) := by
          exact (((hgc.fderiv ℝ).fderiv ℝ).convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
            hkg (hg.fderiv_right (m := 1) (by norm_num) |>.fderiv_right (m := 0) (by norm_num) |>.continuous) x)
        change (∫ y, k y • fderiv ℝ (fderiv ℝ g) (x - y)) v w = _
        rw [ContinuousLinearMap.integral_apply hint]
        have hintv : Integrable (fun y ↦ (k y • fderiv ℝ (fderiv ℝ g) (x - y)) v) :=
          (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).integrable_comp hint
        rw [ContinuousLinearMap.integral_apply hintv]
        simp only [_root_.smul_apply, smul_eq_mul]
      have hsecond (v w : EuclideanSpace ℂ (Fin n)) :
          fderiv ℝ (fderiv ℝ (localFixedMollify U hη m u)) z v w =
            ∫ t : E, k t * fderiv ℝ (fderiv ℝ u) (e.symm (e z - t)) v w := by
        rw [hFeq.fderiv.fderiv_eq]
        have hpull : (fun y : E ↦ F (e.symm y)) = convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
          funext y
          simp only [F, e.apply_symm_apply]
        have hp := complexToRealCoordinateEquiv_hessian_apply F z hFd.contDiffAt (e v) (e w)
        change fderiv ℝ (fderiv ℝ (fun y : E ↦ F (e.symm y))) (e z) (e v) (e w) =
          fderiv ℝ (fderiv ℝ F) z (e.symm (e v)) (e.symm (e w)) at hp
        simp only [e.symm_apply_apply, hpull] at hp
        rw [← hp, conv_hessian g hgd hgcompact]
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ K
        · have htz := htrans (e z) t (Metric.mem_ball_self (by positivity)) ht
          have htU := hnearU (e z - t) (by
            have := Metric.mem_ball.mp htz
            linarith)
          rw [(hgnear _ htz).fderiv.fderiv_eq]
          have hp' := complexToRealCoordinateEquiv_hessian_apply u (e.symm (e z - t))
            ((hu _ htU).contDiffAt (hU.mem_nhds htU)) (e v) (e w)
          change fderiv ℝ (fderiv ℝ (fun y : E ↦ u (e.symm y)))
            (e (e.symm (e z - t))) (e v) (e w) =
            fderiv ℝ (fderiv ℝ u) (e.symm (e z - t)) (e.symm (e v)) (e.symm (e w)) at hp'
          simp only [e.apply_symm_apply, e.symm_apply_apply] at hp'
          rw [hp']
        · simp only [hkzero t ht, zero_mul]
      have hD₂ : ContinuousOn (fderiv ℝ (fderiv ℝ u)) U :=
        (hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU (by norm_num)
      have hfields (v w : EuclideanSpace ℂ (Fin n)) :
          Integrable (fun t : E ↦ k t * fderiv ℝ (fderiv ℝ u) (e.symm (e z - t)) v w) := by
        have hc : ContinuousOn (fun t : E ↦
            k t * fderiv ℝ (fderiv ℝ u) (e.symm (e z - t)) v w) K := by
          have hd : ContinuousOn (fun y ↦ fderiv ℝ (fderiv ℝ u) y v w) U := by fun_prop
          exact hkcont.continuousOn.mul (hd.comp (by fun_prop) hsample)
        exact (hc.integrableOn_compact (isCompact_closedBall _ _)).integrable_of_forall_notMem_eq_zero
          (fun t ht ↦ by simp only [hkzero t ht, zero_mul])
      let q (v w : EuclideanSpace ℂ (Fin n)) (t : E) : ℂ :=
        (k t * fderiv ℝ (fderiv ℝ u) (e.symm (e z - t)) v w : ℝ)
      have hq (v w : EuclideanSpace ℂ (Fin n)) : Integrable (q v w) :=
        Complex.ofRealCLM.integrable_comp (hfields v w)
      let v := EuclideanSpace.single j (1 : ℂ)
      let w := EuclideanSpace.single i (1 : ℂ)
      rw [complexHessian_apply (hFd.contDiffAt.congr_of_eventuallyEq hFeq) j i]
      simp only [hsecond]
      symm
      calc
        localFixedMollify U hη m (fun y ↦ complexHessian u y j i) z =
            ∫ t : E, (q v w t + q (Complex.I • v) (Complex.I • w) t +
              Complex.I * (q v (Complex.I • w) t - q (Complex.I • v) w t)) / 4 := by
          apply integral_congr_ae
          filter_upwards with t
          by_cases ht : t ∈ K
          · have htU := hsample t ht
            change k t • (if e.symm (e z - t) ∈ U then complexHessian u (e.symm (e z - t)) j i
              else 0) = _
            rw [ite_eq_left htU, complexHessian_apply ((hu _ htU).contDiffAt (hU.mem_nhds htU)) j i]
            dsimp [q, v, w]
            simp only [Complex.ofReal_mul]
            ring
          · change k t • _ = _
            simp only [q, hkzero t ht, zero_smul, zero_mul, Complex.ofReal_zero, add_zero,
              sub_zero, mul_zero, zero_div]
        _ = ((∫ t : E, q v w t) + (∫ t : E, q (Complex.I • v) (Complex.I • w) t) +
            Complex.I * ((∫ t : E, q v (Complex.I • w) t) -
              (∫ t : E, q (Complex.I • v) w t))) / 4 := by
          rw [integral_div]
          rw [integral_add (f := fun t ↦ q v w t + q (Complex.I • v) (Complex.I • w) t)
            (g := fun t ↦ Complex.I * (q v (Complex.I • w) t - q (Complex.I • v) w t))
            ((hq v w).add (hq _ _))
            (((hq v (Complex.I • w)).sub (hq (Complex.I • v) w)).const_mul Complex.I)]
          rw [integral_add (hq v w) (hq (Complex.I • v) (Complex.I • w)),
            integral_const_mul]
          rw [integral_sub (f := fun t ↦ q v (Complex.I • w) t)
            (g := fun t ↦ q (Complex.I • v) w t)
            (hq v (Complex.I • w)) (hq (Complex.I • v) w)]
        _ = _ := by simp only [q, integral_complex_ofReal, v, w]
    have hsource : localFixedMollify U hη m (complexEllipticOp A u) z =
        ∑ i, ∑ j, (localFixedMollify U hη m
          (fun y ↦ A y i j * complexHessian u y j i) z).re := by
      have hsum : Integrable (fun w : E ↦ ∑ i, ∑ j, k w •
          (if e.symm (e z - w) ∈ U then
            A (e.symm (e z - w)) i j * complexHessian u (e.symm (e z - w)) j i
          else 0)) :=
        integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hprod i j))
      calc
        localFixedMollify U hη m (complexEllipticOp A u) z =
            ∫ w : E, (∑ i, ∑ j, k w •
              (if e.symm (e z - w) ∈ U then
                A (e.symm (e z - w)) i j * complexHessian u (e.symm (e z - w)) j i
              else 0)).re := by
          apply integral_congr_ae
          filter_upwards with w
          dsimp [localFixedMollify, complexEllipticOp, Matrix.trace, Matrix.mul_apply, e, k]
          split_ifs <;> simp [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
        _ = (∫ w : E, ∑ i, ∑ j, k w •
            (if e.symm (e z - w) ∈ U then
              A (e.symm (e z - w)) i j * complexHessian u (e.symm (e z - w)) j i
            else 0)).re := integral_re hsum
        _ = ∑ i, ∑ j, (localFixedMollify U hη m
            (fun y ↦ A y i j * complexHessian u y j i) z).re := by
          rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hprod i j))]
          simp only [Complex.re_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [integral_finsetSum _ (fun j _ ↦ hprod i j)]
          simp only [Complex.re_sum, localFixedMollify, e, k]
          rfl
    rw [hsource]
    change (∑ i, ∑ j, localFixedMollify U hη m (fun y ↦ A y i j) z *
      complexHessian (localFixedMollify U hη m u) z j i).re = _
    simp only [Complex.re_sum, hH, localMollificationCovariance, Complex.sub_re,
      Finset.sum_sub_distrib]
    ring)

end CalabiYau.Schauder
