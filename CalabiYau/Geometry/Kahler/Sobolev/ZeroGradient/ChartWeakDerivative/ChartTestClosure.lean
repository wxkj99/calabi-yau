module

public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.WeakDerivative
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Test-function closure for chartwise weak derivatives

The hypotheses express local `L²` convergence on a compact set containing the test support. They
include measurability and `MemLp` data so the local pairings are meaningful, and an explicit
integrability condition for the conclusion. No differentiability assumption is made on the limit.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace KahlerForm

private lemma tendsto_integral_mul_of_eLpNorm_tendsto_zero_p
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {g : ℕ → α → ℝ} {p q : ℝ}
    (hpq : p⁻¹ + q⁻¹ = 1) (hp : 1 < p) (hq : 1 < q)
    (hf : MemLp f (ENNReal.ofReal q) μ)
    (hg : ∀ n, MemLp (g n) (ENNReal.ofReal p) μ)
    (hlim : Tendsto (fun n => eLpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f x * g n x ∂μ) atTop (nhds 0) := by
  have hpqR : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp, hpq⟩
  let C : ℝ := MeasureTheory.lpNorm f (ENNReal.ofReal q) μ
  have hlim' : Tendsto (fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) atTop
      (nhds 0) := by
    have hlim_toReal : Tendsto (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal)
        atTop (nhds 0) :=
      (ENNReal.tendsto_toReal_zero_iff (fun n => (hg n).eLpNorm_ne_top)).2 hlim
    have hEq : (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal) =
        fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
      funext n
      simpa using MeasureTheory.toReal_eLpNorm (μ := μ) (p := ENNReal.ofReal p)
        (f := g n)
    simpa [hEq] using hlim_toReal
  have hbound : ∀ n, |∫ x, f x * g n x ∂μ| ≤
      C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
    intro n
    have h_int : |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by
      calc
        |∫ x, f x * g n x ∂μ| = ‖∫ x, f x * g n x ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ x, ‖f x * g n x‖ ∂μ := by
          simpa using norm_integral_le_integral_norm (μ := μ) (f := fun x => f x * g n x)
        _ = ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by simp_rw [norm_mul]
    have h_holder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
      (μ := μ) (f := f) (g := g n) (p := q) (q := p) hpqR.symm hf (hg n)
    have hp0 : ENNReal.ofReal p ≠ 0 := by
      intro hp0'
      have : p ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hp0'
      linarith
    have hq0 : ENNReal.ofReal q ≠ 0 := by
      intro hq0'
      have : q ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hq0'
      linarith
    have h_f_lp : MeasureTheory.lpNorm f (ENNReal.ofReal q) μ =
        (∫ x, ‖f x‖ ^ q ∂μ) ^ q⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] using
        MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal q) (f := f) hq0 (by simp) hf.aestronglyMeasurable
    have h_g_lp : MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ =
        (∫ x, ‖g n x‖ ^ p ∂μ) ^ p⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
        MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal p) (f := g n) hp0 (by simp)
            (hg n).aestronglyMeasurable
    calc
      |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := h_int
      _ ≤ C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
        simpa [C, h_f_lp, h_g_lp, mul_comm, mul_left_comm, mul_assoc] using h_holder
  have h_upper : Tendsto (fun n => C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ)
      atTop (nhds 0) := by
    simpa using Tendsto.const_mul C hlim'
  have h_abs : Tendsto (fun n => |∫ x, f x * g n x ∂μ|) atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound h_upper
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs

private lemma integral_restrict_eq_integral_of_zero_outside
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℝ}
    (hzero : ∀ x, x ∉ s → f x = 0) :
    ∫ x, f x ∂(μ.restrict s) = ∫ x, f x ∂μ := by
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) hzero

private lemma euclidean_test_integration_by_parts
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (v : V) (f φ : V → ℝ)
    (hφ : Differentiable ℝ φ)
    (hf : ∀ x ∈ tsupport φ, DifferentiableAt ℝ f x)
    (hderiv : Integrable (fun y => fderiv ℝ f y v * φ y))
    (hvalue : Integrable (fun y => f y * fderiv ℝ φ y v))
    (hproduct : Integrable (fun y => f y * φ y)) :
    ∫ y, f y * fderiv ℝ φ y v =
      -∫ y, fderiv ℝ f y v * φ y := by
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hderiv hvalue hproduct hf (fun x _ => hφ.differentiableAt)

/-- A local `L²` limit of smooth functions whose directional derivatives tend to zero has zero
weak directional derivative, tested against compactly supported smooth functions. -/
theorem euclidean_test_integral_eq_zero_of_l2_tendsto
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {Ω : Set V} (hΩ : IsOpen Ω)
    {K : Set V} (hK : K ⊆ Ω)
    (v : V) (F : ℕ → V → ℝ) (U φ : V → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_support : HasCompactSupport φ)
    (hφK : tsupport φ ⊆ K)
    (hF : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (F k) Ω)
    (hUmeas : AEStronglyMeasurable U (volume.restrict K))
    (hUmem : MemLp U (ENNReal.ofReal 2) (volume.restrict K))
    (hFmem : ∀ k, MemLp (fun y => F k y - U y)
      (ENNReal.ofReal 2) (volume.restrict K))
    (hFlim : Tendsto
      (fun k => eLpNorm (fun y => F k y - U y)
        (ENNReal.ofReal 2) (volume.restrict K)) atTop (𝓝 0))
    (hDmem : ∀ k, MemLp (fun y => fderiv ℝ (F k) y v)
      (ENNReal.ofReal 2) (volume.restrict K))
    (hDlim : Tendsto
      (fun k => eLpNorm (fun y => fderiv ℝ (F k) y v)
        (ENNReal.ofReal 2) (volume.restrict K)) atTop (𝓝 0)) :
    ∫ y in Ω, U y * fderiv ℝ φ y v = 0 := by
  let μ : Measure V := volume.restrict K
  let dφ : V → ℝ := fun y => fderiv ℝ φ y v
  have hφmem : MemLp φ (ENNReal.ofReal 2) μ := by
    exact (hφ.continuous.memLp_of_hasCompactSupport hφ_support).restrict K
  have hdφcont : Continuous dφ := by
    dsimp [dφ]
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφsupport : HasCompactSupport dφ := by
    dsimp [dφ]
    exact hφ_support.fderiv_apply (𝕜 := ℝ) v
  have hdφmem : MemLp dφ (ENNReal.ofReal 2) μ := by
    exact (hdφcont.memLp_of_hasCompactSupport hdφsupport).restrict K
  have hpairF : Tendsto
      (fun k => ∫ y, dφ y * (F k y - U y) ∂μ) atTop (𝓝 0) := by
    exact tendsto_integral_mul_of_eLpNorm_tendsto_zero_p
      (p := 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
      hdφmem hFmem hFlim
  have hpairD : Tendsto
      (fun k => ∫ y, φ y * fderiv ℝ (F k) y v ∂μ) atTop (𝓝 0) := by
    exact tendsto_integral_mul_of_eLpNorm_tendsto_zero_p
      (p := 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
      hφmem hDmem hDlim
  let : (ENNReal.ofReal 2).HolderTriple (ENNReal.ofReal 2) 1 :=
    ENNReal.HolderConjugate.of_toReal <| by
      simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] using
        (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
          (2 : ℝ).HolderConjugate 2)
  have hUφmem : Integrable (fun y => U y * dφ y) μ := by
    have hi := hUmem.integrable_mul hdφmem
    exact hi.congr (Filter.Eventually.of_forall fun y => by simp)
  have hpairF_integrable : ∀ k, Integrable
      (fun y => dφ y * (F k y - U y)) μ := by
    intro k
    exact hdφmem.integrable_mul (hFmem k)
  have hFpair : Tendsto (fun k => ∫ y, F k y * dφ y ∂μ) atTop
      (𝓝 (∫ y, U y * dφ y ∂μ)) := by
    have hEq : ∀ k, (∫ y, F k y * dφ y ∂μ) =
        (∫ y, U y * dφ y ∂μ) + ∫ y, dφ y * (F k y - U y) ∂μ := by
      intro k
      calc
        ∫ y, F k y * dφ y ∂μ =
            ∫ y, U y * dφ y + dφ y * (F k y - U y) ∂μ := by
              congr 1
              funext y
              ring
        _ = (∫ y, U y * dφ y ∂μ) + ∫ y, dφ y * (F k y - U y) ∂μ :=
              integral_add hUφmem (hpairF_integrable k)
    have hfunc : (fun k => ∫ y, F k y * dφ y ∂μ) =
        fun k => (∫ y, U y * dφ y ∂μ) + ∫ y, dφ y * (F k y - U y) ∂μ := by
      funext k
      exact hEq k
    rw [hfunc]
    simpa [add_zero] using Tendsto.const_add (∫ y, U y * dφ y ∂μ) hpairF
  have hφzero : ∀ y, y ∉ K → φ y = 0 := by
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (fun hs => hy (hφK hs))
  have hdφK : tsupport dφ ⊆ K := by
    dsimp [dφ]
    exact (tsupport_fderiv_apply_subset ℝ v).trans hφK
  have hdφzero : ∀ y, y ∉ K → dφ y = 0 := by
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (fun hs => hy (hdφK hs))
  have hFkMem : ∀ k, MemLp (F k) (ENNReal.ofReal 2) μ := by
    intro k
    have hsum : MemLp (fun y => (F k y - U y) + U y) (ENNReal.ofReal 2) μ :=
      (hFmem k).add hUmem
    have haes : AEStronglyMeasurable (F k) μ := by
      have h := (hFmem k).aestronglyMeasurable.add hUmeas
      convert h using 1
      ext y
      simp
    apply hsum.congr_norm haes
    filter_upwards [] with y
    congr 1
    ring
  have hFkDglobal : ∀ k, Integrable (fun y => F k y * dφ y) volume := by
    intro k
    have hk : IntegrableOn (fun y => F k y * dφ y) K volume :=
      (hFkMem k).integrable_mul hdφmem
    exact hk.integrable_of_forall_notMem_eq_zero (fun y hy => by simp [hdφzero y hy])
  have hDφglobal : ∀ k, Integrable
      (fun y => fderiv ℝ (F k) y v * φ y) volume := by
    intro k
    have hk : IntegrableOn (fun y => fderiv ℝ (F k) y v * φ y) K volume :=
      (hDmem k).integrable_mul hφmem
    exact hk.integrable_of_forall_notMem_eq_zero (fun y hy => by simp [hφzero y hy])
  have hFkφglobal : ∀ k, Integrable (fun y => F k y * φ y) volume := by
    intro k
    have hk : IntegrableOn (fun y => F k y * φ y) K volume :=
      (hFkMem k).integrable_mul hφmem
    exact hk.integrable_of_forall_notMem_eq_zero (fun y hy => by simp [hφzero y hy])
  have hFdiffAt : ∀ k, ∀ y ∈ tsupport φ, DifferentiableAt ℝ (F k) y := by
    intro k y hy
    have hyΩ : y ∈ Ω := hK (hφK hy)
    have hdiffOn : DifferentiableOn ℝ (F k) Ω :=
      (hF k).differentiableOn (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
    exact (hdiffOn y hyΩ).differentiableAt (hΩ.mem_nhds hyΩ)
  have hUΩeq : (∫ y in Ω, U y * dφ y) = ∫ y, U y * dφ y ∂μ := by
    have hzeroΩ : ∀ y, y ∉ Ω → U y * dφ y = 0 := by
      intro y hy
      have hyK : y ∉ K := fun hk => hy (hK hk)
      simp [hdφzero y hyK]
    calc
      ∫ y in Ω, U y * dφ y = ∫ y, U y * dφ y ∂volume :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzeroΩ
      _ = ∫ y, U y * dφ y ∂μ := by
        symm
        exact integral_restrict_eq_integral_of_zero_outside (μ := volume) (s := K)
          (f := fun y => U y * dφ y) (fun y hy => by simp [hdφzero y hy])
  have hFΩeq : ∀ k, (∫ y in Ω, F k y * dφ y) = ∫ y, F k y * dφ y ∂μ := by
    intro k
    have hzeroΩ : ∀ y, y ∉ Ω → F k y * dφ y = 0 := by
      intro y hy
      have hyK : y ∉ K := fun hk => hy (hK hk)
      simp [hdφzero y hyK]
    calc
      ∫ y in Ω, F k y * dφ y = ∫ y, F k y * dφ y ∂volume :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzeroΩ
      _ = ∫ y, F k y * dφ y ∂μ := by
        symm
        exact integral_restrict_eq_integral_of_zero_outside (μ := volume) (s := K)
          (f := fun y => F k y * dφ y) (fun y hy => by simp [hdφzero y hy])
  have hDΩeq : ∀ k, (∫ y in Ω, φ y * fderiv ℝ (F k) y v) =
      ∫ y, φ y * fderiv ℝ (F k) y v ∂μ := by
    intro k
    have hzeroΩ : ∀ y, y ∉ Ω → φ y * fderiv ℝ (F k) y v = 0 := by
      intro y hy
      have hyK : y ∉ K := fun hk => hy (hK hk)
      simp [hφzero y hyK]
    calc
      ∫ y in Ω, φ y * fderiv ℝ (F k) y v =
          ∫ y, φ y * fderiv ℝ (F k) y v ∂volume :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hzeroΩ
      _ = ∫ y, φ y * fderiv ℝ (F k) y v ∂μ := by
        symm
        exact integral_restrict_eq_integral_of_zero_outside (μ := volume) (s := K)
          (f := fun y => φ y * fderiv ℝ (F k) y v) (fun y hy => by simp [hφzero y hy])
  have hIBPseq : ∀ k, (∫ y in Ω, F k y * dφ y) =
      -∫ y in Ω, φ y * fderiv ℝ (F k) y v := by
    intro k
    have hIBP := euclidean_test_integration_by_parts v (F k) φ
      (hφ.differentiable (by simp)) (hFdiffAt k)
      (hDφglobal k) (hFkDglobal k) (hFkφglobal k)
    have hKleft := integral_restrict_eq_integral_of_zero_outside (μ := volume) (s := K)
      (f := fun y => F k y * dφ y) (fun y hy => by simp [hdφzero y hy])
    have hKright := integral_restrict_eq_integral_of_zero_outside (μ := volume) (s := K)
      (f := fun y => φ y * fderiv ℝ (F k) y v) (fun y hy => by simp [hφzero y hy])
    have hcomm : (∫ y, fderiv ℝ (F k) y v * φ y ∂volume) =
        ∫ y, φ y * fderiv ℝ (F k) y v ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by ring
    calc
      ∫ y in Ω, F k y * dφ y = ∫ y, F k y * dφ y ∂μ := hFΩeq k
      _ = ∫ y, F k y * dφ y ∂volume := hKleft
      _ = -∫ y, fderiv ℝ (F k) y v * φ y ∂volume := hIBP
      _ = -∫ y, φ y * fderiv ℝ (F k) y v ∂volume := by rw [hcomm]
      _ = -∫ y, φ y * fderiv ℝ (F k) y v ∂μ := by rw [hKright]
      _ = -∫ y in Ω, φ y * fderiv ℝ (F k) y v := by rw [← hDΩeq k]
  have hDset_tendsto : Tendsto
      (fun k => ∫ y in Ω, φ y * fderiv ℝ (F k) y v) atTop (𝓝 0) := by
    have hfunc : (fun k => ∫ y in Ω, φ y * fderiv ℝ (F k) y v) =
        fun k => ∫ y, φ y * fderiv ℝ (F k) y v ∂μ := by
      funext k
      exact hDΩeq k
    rw [hfunc]
    exact hpairD
  have hFset_tendsto : Tendsto (fun k => ∫ y in Ω, F k y * dφ y) atTop
      (𝓝 (∫ y in Ω, U y * dφ y)) := by
    have hfunc : (fun k => ∫ y in Ω, F k y * dφ y) =
        fun k => ∫ y, F k y * dφ y ∂μ := by
      funext k
      exact hFΩeq k
    rw [hfunc, hUΩeq]
    exact hFpair
  have hFset_zero : Tendsto (fun k => ∫ y in Ω, F k y * dφ y) atTop (𝓝 0) := by
    have hfunc : (fun k => ∫ y in Ω, F k y * dφ y) =
        fun k => -∫ y in Ω, φ y * fderiv ℝ (F k) y v := by
      funext k
      exact hIBPseq k
    rw [hfunc]
    simpa using hDset_tendsto.neg
  exact tendsto_nhds_unique hFset_tendsto hFset_zero

end KahlerForm

end
