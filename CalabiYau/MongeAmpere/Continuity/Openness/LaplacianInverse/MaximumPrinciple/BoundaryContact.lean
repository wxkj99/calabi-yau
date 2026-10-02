module

public import CalabiYau.Geometry.Complex.Schauder

/-!
# Boundary contact from a supplied strict barrier

Gilbarg–Trudinger, §3.2, Lemma 3.4: compare `u + ε v` on the outer half-annulus,
then use the inward difference quotient at the touching point. The construction and elliptic
estimate for `v` are proved in `Barrier`; this proves the comparison argument.
-/

@[expose] public section

open scoped ContDiff NNReal
open Set

/-- Annular comparison with a given C² strict barrier forces a positive outward radial
derivative at a boundary maximum that is strictly greater than every interior value. -/
@[deprecated "unused hypothesis `hlam`; will be removed" (since := "2026-10-02")]
theorem complexEllipticOp_boundary_contact_deriv_pos {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {u v : EuclideanSpace ℂ (Fin n) → ℝ}
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiff ℝ 2 v)
    {c z : EuclideanSpace ℂ (Fin n)} {R : ℝ} (hR : 0 < R)
    (hball : Metric.closedBall c R ⊆ U) (hz : z ∈ Metric.sphere c R)
    {lam : ℝ≥0} (hlam : 0 < lam)
    (hEll : IsUniformlyEllipticOn A lam (Metric.ball c R))
    (hLu : ∀ y ∈ Metric.ball c R, 0 ≤ complexEllipticOp A u y)
    (hmax : ∀ y ∈ Metric.closedBall c R, u y ≤ u z)
    (hstrict : ∀ y ∈ Metric.ball c R, u y < u z)
    (hvzero : ∀ y ∈ Metric.sphere c R, v y = 0)
    (hLv : ∀ y ∈ Metric.ball c R \ Metric.closedBall c (R / 2),
      0 < complexEllipticOp A v y)
    (hvderiv : fderiv ℝ v z (z - c) < 0) :
    0 < fderiv ℝ u z (z - c) := by
  let : PartialOrder ℂ := Complex.partialOrder
  have matrix_trace_mul_nonneg_of_posSemidef {n : Type} [Fintype n] [DecidableEq n]
      {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
      0 ≤ Complex.re (A * B).trace := by
    classical
    let u := hA.1.eigenvectorUnitary
    let U : Matrix n n ℂ := u
    let D : Matrix n n ℂ := Matrix.diagonal (fun i => (hA.1.eigenvalues i : ℂ))
    let C := Matrix.conjTranspose U * B * U
    have hSpec : A = U * D * Matrix.conjTranspose U := by
      rw [hA.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
      rfl
    have hC : C.PosSemidef := hB.conjTranspose_mul_mul_same U
    have htrace : (A * B).trace = (D * C).trace := by
      rw [hSpec]
      rw [show (U * D * Matrix.conjTranspose U) * B =
        U * (D * (Matrix.conjTranspose U * B)) by simp [mul_assoc]]
      rw [Matrix.trace_mul_comm]
      congr 1
      simp [C, mul_assoc]
    have hsum : Complex.re (D * C).trace =
        ∑ i, hA.1.eigenvalues i * Complex.re (C i i) := by
      simp [Matrix.trace, Matrix.mul_apply, D, Matrix.diagonal, Complex.re_sum]
    rw [htrace, hsum]
    apply Finset.sum_nonneg
    intro i hi
    have heig : 0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg i
    have hCii : 0 ≤ C i i := hC.diag_nonneg
    have hre : 0 ≤ Complex.re (C i i) := (Complex.nonneg_iff.mp hCii).1
    exact mul_nonneg heig hre

  have complexEllipticOp_nonpos_of_isLocalMax {n : ℕ}
      (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (z : EuclideanSpace ℂ (Fin n)) {u : EuclideanSpace ℂ (Fin n) → ℝ}
      (hu : ContDiffAt ℝ 2 u z) (hmax : IsLocalMax u z)
      {lam : ℝ≥0} (hEll : IsUniformlyEllipticOn A lam {z}) :
      complexEllipticOp A u z ≤ 0 := by
    have hAdata := hEll z (by simp)
    have hA : (A z).PosSemidef :=
      Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hAdata.1 fun x => by
        rw [Complex.nonneg_iff]
        constructor
        · apply le_trans ?_ (hAdata.2 x)
          exact mul_nonneg (NNReal.coe_nonneg lam)
            (Finset.sum_nonneg fun i hi => sq_nonneg ‖x i‖)
        · simpa [eq_comm] using hAdata.1.im_star_dotProduct_mulVec_self x
    have hdd := isNonneg_neg_ddbar_of_isLocalMax hu hmax
    have hB : (-complexHessian u z).PosSemidef := by
      have hb := (ContinuousAlternatingMap.isNonneg_iff.mp hdd).2
      simpa [complexHessian, ContinuousAlternatingMap.coeffMatrix_neg] using hb
    have htrace := matrix_trace_mul_nonneg_of_posSemidef hA hB
    unfold complexEllipticOp
    have hneg : 0 ≤ -Complex.re ((A z * complexHessian u z).trace) := by
      simpa [Matrix.mul_neg, Matrix.trace_neg] using htrace
    exact neg_nonneg.mp hneg

  have complexHessian_add_of_C2 {n : ℕ}
      (f g : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
      (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
      complexHessian (f + g) z = complexHessian f z + complexHessian g z := by
    simp only [complexHessian, ddbar_add hf hg, ContinuousAlternatingMap.coeffMatrix_add]

  have complexHessian_smul_of_C2 {n : ℕ}
      (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
      (hf : ContDiffAt ℝ 2 f z) (a : ℝ) :
      complexHessian (a • f) z = a • complexHessian f z := by
    simp only [complexHessian, ddbar_smul hf a, ContinuousAlternatingMap.coeffMatrix_smul]

  have complexEllipticOp_add_smul {n : ℕ}
      (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (f g : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
      (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (a : ℝ) :
      complexEllipticOp A (f + a • g) z =
        complexEllipticOp A f z + a * complexEllipticOp A g z := by
    rw [complexEllipticOp, complexEllipticOp, complexEllipticOp,
      complexHessian_add_of_C2 f (a • g) z hf (hg.const_smul a),
      complexHessian_smul_of_C2 g z hg a]
    simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul]

  have exists_eps_inner_ball_perturbation {n : ℕ}
      (u v : EuclideanSpace ℂ (Fin n) → ℝ) (c z : EuclideanSpace ℂ (Fin n))
      {R : ℝ} (hR : 0 < R)
      (hK : ContinuousOn u (Metric.closedBall c (R / 2)))
      (hVK : ContinuousOn (fun y => ‖v y‖) (Metric.closedBall c (R / 2)))
      (hstrict : ∀ y ∈ Metric.ball c R, u y < u z) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ Metric.closedBall c (R / 2),
        u y + ε * v y < u z := by
    let K := Metric.closedBall c (R / 2)
    have hKcompact : IsCompact K := isCompact_closedBall c (R / 2)
    have hKne : K.Nonempty := ⟨c, by simp [K, Metric.mem_closedBall]; positivity⟩
    obtain ⟨x, hxK, hux⟩ := hKcompact.exists_isMaxOn hKne hK
    obtain ⟨y, hyK, hvy⟩ := hKcompact.exists_isMaxOn hKne hVK
    have hxball : x ∈ Metric.ball c R := by
      have hxmem : dist x c ≤ R / 2 := Metric.mem_closedBall.mp hxK
      rw [Metric.mem_ball]
      nlinarith
    have hgap : 0 < u z - u x := sub_pos.mpr (hstrict x hxball)
    let B := ‖v y‖
    have hB : 0 ≤ B := norm_nonneg _
    let ε := (u z - u x) / (2 * (B + 1))
    have hε : 0 < ε := by dsimp [ε]; positivity
    refine ⟨ε, hε, ?_⟩
    intro a haK
    have haball : a ∈ Metric.ball c R := by
      have ha : dist a c ≤ R / 2 := Metric.mem_closedBall.mp haK
      rw [Metric.mem_ball]
      nlinarith
    have hux' : ∀ b ∈ K, u b ≤ u x := isMaxOn_iff.mp hux
    have hau : u a ≤ u x := hux' a haK
    have hvy' : ∀ b ∈ K, ‖v b‖ ≤ ‖v y‖ := isMaxOn_iff.mp hvy
    have hav : v a ≤ B := by
      dsimp [B]
      exact le_trans (le_abs_self _) (hvy' a haK)
    have hden : 0 < 2 * (B + 1) := by positivity
    have hprod : ε * B < u z - u x := by
      dsimp [ε]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hden).2
      nlinarith [hgap, hB]
    calc
      u a + ε * v a ≤ u x + ε * B :=
        add_le_add hau (mul_le_mul_of_nonneg_left hav hε.le)
      _ < u z := by linarith

  have fderiv_inward_nonpos_of_closedBall_bound {n : ℕ}
      (w : EuclideanSpace ℂ (Fin n) → ℝ) (c z : EuclideanSpace ℂ (Fin n))
      {R : ℝ} (hR : 0 < R) (hz : z ∈ Metric.sphere c R)
      (hw : ContDiffAt ℝ 2 w z)
      (hbound : ∀ y ∈ Metric.closedBall c R, w y ≤ w z) :
      fderiv ℝ w z (c - z) ≤ 0 := by
    let γ : ℝ → EuclideanSpace ℂ (Fin n) := fun t => z + t • (c - z)
    let g : ℝ → ℝ := fun t => w (γ t)
    have hdist : ‖z - c‖ = R := by
      have hs := Metric.mem_sphere.mp hz
      simpa [dist_eq_norm] using hs
    let posZero : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
    have hγmem : Filter.Eventually (fun t => γ t ∈ Metric.closedBall c R) posZero := by
      have htone : Filter.Eventually (fun t : ℝ => t < 1) posZero :=
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) ∈ Iio 1))
      filter_upwards [eventually_mem_nhdsWithin, htone] with t ht ht1
      have htpos : 0 < t := by simpa using ht
      apply Metric.mem_closedBall.mpr
      rw [dist_eq_norm]
      have hident : γ t - c = (1 - t) • (z - c) := by
        dsimp [γ]
        module
      rw [hident, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
      nlinarith [htpos, ht1, hdist, hR.le]
    have hboundSlope : Filter.Eventually (fun t : ℝ =>
        t⁻¹ * (g t - g 0) ≤ 0) posZero := by
      filter_upwards [hγmem, eventually_mem_nhdsWithin] with t htK ht
      have htpos : 0 < t := by simpa using ht
      have hgt : g t ≤ g 0 := by
        dsimp [g, γ]
        simpa using hbound (z + t • (c - z)) htK
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr htpos.le) (sub_nonpos.mpr hgt)
    have hγderiv : HasDerivAt γ (c - z) 0 := by
      dsimp [γ]
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (c - z) |>.const_add z
    have hwF : HasFDerivAt w (fderiv ℝ w z) z := by
      have hle : (1 : ℕ∞ω) ≤ 2 := by norm_num
      have hwAt1 : ContDiffAt ℝ 1 w z := hw.of_le hle
      exact (hwAt1.differentiableAt (by norm_num)).hasFDerivAt
    have hgderiv : HasDerivAt g (fderiv ℝ w z (c - z)) 0 := by
      dsimp [g]
      have hwFγ : HasFDerivAt w (fderiv ℝ w z) (γ 0) := by simpa [γ] using hwF
      exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hwFγ hγderiv
    have hboundSlope' : Filter.Eventually (fun t : ℝ =>
        t⁻¹ • (g (0 + t) - g 0) ≤ 0) posZero := by
      filter_upwards [hboundSlope] with t ht
      simpa only [smul_eq_mul, zero_add] using ht
    exact le_of_tendsto hgderiv.tendsto_slope_zero_right hboundSlope'

  let K := Metric.closedBall c R
  let Kinner := Metric.closedBall c (R / 2)
  have hzK : z ∈ K := Metric.sphere_subset_closedBall hz
  have hinnerSub : Kinner ⊆ K := by
    intro y hy
    apply Metric.mem_closedBall.mpr
    have hy' : dist y c ≤ R / 2 := Metric.mem_closedBall.mp hy
    apply le_trans hy'
    nlinarith [hR]
  have hinnerU : Kinner ⊆ U := fun y hy => hball (hinnerSub hy)
  have hinnerCont : ContinuousOn u Kinner := hu.continuousOn.mono hinnerU
  have hvNormCont : ContinuousOn (fun y => ‖v y‖) Kinner :=
    (continuous_norm.comp hv.continuous).continuousOn
  obtain ⟨ε, hε, hinner⟩ :=
    exists_eps_inner_ball_perturbation u v c z hR hinnerCont hvNormCont hstrict
  let w : EuclideanSpace ℂ (Fin n) → ℝ := u + ε • v
  have hwz : w z = u z := by simp [w, hvzero z hz]
  have hKne : K.Nonempty := ⟨c, by
    apply Metric.mem_closedBall.mpr
    simpa using hR.le⟩
  have huCont : ContinuousOn u K := hu.continuousOn.mono hball
  have hvCont : ContinuousOn v K := hv.continuous.continuousOn
  have hwCont : ContinuousOn w K := by
    dsimp [w]
    exact huCont.add (hvCont.const_smul ε)
  have hwBound : ∀ y ∈ K, w y ≤ u z := by
    intro a ha
    by_contra habad
    have habad' : u z < w a := lt_of_not_ge habad
    obtain ⟨y, hyK, hymax⟩ := isCompact_closedBall c R |>.exists_isMaxOn hKne hwCont
    have hymax' : ∀ b ∈ K, w b ≤ w y := isMaxOn_iff.mp hymax
    have hygt : u z < w y := lt_of_lt_of_le habad' (hymax' a ha)
    have hyNotInner : y ∉ Kinner := by
      intro hy
      have hlt := hinner y hy
      change u y + ε • v y < u z at hlt
      have hlt' : w y < u z := by simpa [w] using hlt
      exact (not_lt_of_ge (le_of_lt hlt')) hygt
    have hyNotSphere : y ∉ Metric.sphere c R := by
      intro hs
      have hyW : w y ≤ u z := by
        have hwy : w y = u y := by simp [w, hvzero y hs]
        rw [hwy]
        exact hmax y (Metric.sphere_subset_closedBall hs)
      exact (not_lt_of_ge hyW) hygt
    have hyBall : y ∈ Metric.ball c R := by
      rw [Metric.mem_ball]
      by_contra hy
      have hyR : dist y c ≤ R := Metric.mem_closedBall.mp hyK
      have hRle : R ≤ dist y c := le_of_not_gt hy
      exact hyNotSphere (Metric.mem_sphere.mpr (le_antisymm hyR hRle))
    have hyAnn : y ∈ Metric.ball c R \ Kinner := ⟨hyBall, hyNotInner⟩
    have hyU : y ∈ U := hball hyK
    have huAt : ContDiffAt ℝ 2 u y := (hu y hyU).contDiffAt (hU.mem_nhds hyU)
    have hvAt : ContDiffAt ℝ 2 v y := hv.contDiffAt
    have hwAt : ContDiffAt ℝ 2 w y := by
      dsimp [w]
      exact huAt.add (hvAt.const_smul ε)
    have hlocal : IsLocalMax w y := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hyBall] with b hb
      exact hymax' b (Metric.ball_subset_closedBall hb)
    have hEllY : IsUniformlyEllipticOn A lam {y} := by
      intro b hb
      have : b = y := Set.mem_singleton_iff.mp hb
      subst b
      exact hEll y hyBall
    have hLw : 0 < complexEllipticOp A w y := by
      change 0 < complexEllipticOp A (u + ε • v) y
      rw [complexEllipticOp_add_smul A u v y huAt hvAt ε]
      exact add_pos_of_nonneg_of_pos (hLu y hyBall)
        (mul_pos hε (hLv y hyAnn))
    have hLw' := complexEllipticOp_nonpos_of_isLocalMax A y hwAt hlocal hEllY
    linarith
  have hwBoundZ : IsMaxOn w K z := isMaxOn_iff.mpr (by
    intro y hy
    calc
      w y ≤ u z := hwBound y hy
      _ = w z := hwz.symm)
  have huAtZ : ContDiffAt ℝ 2 u z :=
    (hu z (hball hzK)).contDiffAt (hU.mem_nhds (hball hzK))
  have hwAtZ : ContDiffAt ℝ 2 w z := by
    dsimp [w]
    exact huAtZ.add ((hv.contDiffAt).const_smul ε)
  have hwBoundAtZ : ∀ y ∈ K, w y ≤ w z := isMaxOn_iff.mp hwBoundZ
  have hDwithin : fderiv ℝ w z (c - z) ≤ 0 :=
    fderiv_inward_nonpos_of_closedBall_bound w c z hR hz hwAtZ hwBoundAtZ
  have hD : fderiv ℝ w z (c - z) =
      fderiv ℝ u z (c - z) + ε * fderiv ℝ v z (c - z) := by
    change fderiv ℝ (u + (fun y => ε • v y)) z (c - z) = _
    rw [fderiv_add
      ((huAtZ.of_le (WithTop.coe_le_coe.mpr (by norm_num : (1 : ℕ∞) ≤ 2))).differentiableAt (by norm_num))
      (((hv.contDiffAt.const_smul ε).of_le
        (WithTop.coe_le_coe.mpr (by norm_num : (1 : ℕ∞) ≤ 2))).differentiableAt (by norm_num))]
    change fderiv ℝ u z (c - z) + fderiv ℝ (ε • v) z (c - z) = _
    rw [congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := v) ε) z]
    simp [smul_eq_mul]
  have hDu : fderiv ℝ u z (c - z) = -fderiv ℝ u z (z - c) := by
    rw [show c - z = -(z - c) by abel, map_neg]
  have hDv : fderiv ℝ v z (c - z) = -fderiv ℝ v z (z - c) := by
    rw [show c - z = -(z - c) by abel, map_neg]
  rw [hD, hDu, hDv] at hDwithin
  have hsum : 0 ≤ fderiv ℝ u z (z - c) + ε * fderiv ℝ v z (z - c) := by
    linarith
  have hprod : ε * fderiv ℝ v z (z - c) < 0 := mul_neg_of_pos_of_neg hε hvderiv
  linarith
