module

public import CalabiYau.Analysis.Sobolev.Euclidean.Poincare.SobolevPoincare

/-!
# Distributionally constant real functions on a Euclidean ball

Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, §7.1:
apply the Poincaré inequality on balls to a zero weak gradient. The extracted De Giorgi
unit-ball inequality supplies the quantitative input; positive affine rescaling transfers it
from the unit ball to any translated ball. The dimension-zero case belongs to the chart bridge.
-/

@[expose] public section

open scoped ContDiff
open MeasureTheory

namespace KahlerForm

/-- Package zero distributional derivatives as a zero-gradient De Giorgi witness. -/
private theorem exists_zero_gradient_witness_on_unit_ball
    {d : ℕ} [NeZero d]
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : MemLp u (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))
    (hzero : ∀ i : Fin d, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 →
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0) :
    ∃ hw : Sobolev.Euclidean.MemW1pWitness (ENNReal.ofReal 2) u
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1), hw.weakGrad = 0 := by
  let B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 1
  let : IsFiniteMeasure (MeasureTheory.volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top.lt_top⟩
  refine ⟨{
    memLp := by simpa [B] using hu
    weakGrad := fun _ => 0
    weakGrad_component_memLp := by
      intro i
      exact memLp_const (0 : ℝ)
    isWeakGrad := by
      intro i φ hφ hcompact hsub
      rw [hzero i φ hφ hcompact (by simpa [B] using hsub)]
      simp
  }, ?_⟩
  rfl

/-- A zero weak gradient on the unit ball makes the function equal to its ball average a.e. -/
private theorem ae_eq_average_on_unit_ball_of_zero_distributional_derivative
    {d : ℕ} [NeZero d]
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : MemLp u (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))
    (hzero : ∀ i : Fin d, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 →
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)),
      u x = ⨍ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, u y ∂MeasureTheory.volume := by
  obtain ⟨hw, hgrad⟩ := exists_zero_gradient_witness_on_unit_ball u hu hzero
  have hpoincare := Sobolev.Euclidean.poincare_unitBall_W1p_public
    (d := d) (p := 2) (by norm_num) hw
  have hgrad_norm : eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) = 0 := by
    rw [hgrad]
    simp
  have hdist_norm : eLpNorm
      (fun x => u x - ⨍ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        u y ∂MeasureTheory.volume)
      (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) = 0 := by
    apply le_antisymm
    · calc
        _ ≤ ENNReal.ofReal (Sobolev.Euclidean.poincareConstant d) *
            eLpNorm (fun x => ‖hw.weakGrad x‖) (ENNReal.ofReal 2)
              (MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := hpoincare
        _ = 0 := by rw [hgrad_norm]; simp
    · exact bot_le
  have hdist_mem : MemLp
      (fun x => u x - ⨍ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        u y ∂MeasureTheory.volume)
      (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
    let : IsFiniteMeasure (MeasureTheory.volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top.lt_top⟩
    exact hu.sub (memLp_const _)
  have hp_ne_zero : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
  have haezero := (eLpNorm_eq_zero_iff hdist_mem.aestronglyMeasurable hp_ne_zero).mp hdist_norm
  exact haezero.mono fun x hx => by simpa [sub_eq_zero] using hx

/-- Positive affine scaling carries the unit ball onto the ball centered at `q`. -/
private theorem affine_smul_image_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E) {r : ℝ} (hr : 0 < r) :
    (fun x : E => q + r • x) '' Metric.ball 0 1 = Metric.ball q r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simpa using mul_lt_mul_of_pos_left hx hr
  · intro hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    refine ⟨r⁻¹ • (y - q), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      calc
        r⁻¹ * ‖y - q‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hy (inv_pos.mpr hr)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · simp [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne']

/-- Affine change of variables for integration on a real Euclidean ball. -/
private theorem setIntegral_comp_affine_unit_ball
    {d : ℕ} [NeZero d] (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (q : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, f (q + r • x)
      ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) =
      (r ^ d)⁻¹ * ∫ y in Metric.ball q r, f y
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  calc
    _ = (r ^ d)⁻¹ * ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r, f (q + z)
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by
      rw [Measure.setIntegral_comp_smul_of_pos
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))
        (fun z => f (q + z)) (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) hr]
      rw [smul_unitBall_of_pos hr]
      simp [smul_eq_mul]
    _ = (r ^ d)⁻¹ * ∫ y in Metric.ball q r, f y
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by
      congr 1
      let T : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) :=
        Homeomorph.addLeft q
      have hmp : MeasurePreserving T
          (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))
          (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by
        simpa [T] using measurePreserving_add_left
          (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) q
      have hemb : MeasurableEmbedding T := T.measurableEmbedding
      simpa [T, vadd_ball_zero] using
        (hmp.setIntegral_image_emb hemb f
          (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r)).symm

/-- The inverse Jacobian `r⁻ᵈ` under positive affine dilation. -/
private theorem measure_map_affine_smul
    {d : ℕ} [NeZero d] (q : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun x : EuclideanSpace ℝ (Fin d) => q + r • x)
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) =
    ENNReal.ofReal ((r ^ d)⁻¹) •
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  let A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => q + x
  let S : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => r • x
  have hscale : Measure.map S (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) =
      ENNReal.ofReal ((r ^ d)⁻¹) •
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    simpa [S, abs_of_pos (inv_pos.mpr (pow_pos hr d))] using
      (MeasureTheory.Measure.map_addHaar_smul
        (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))) hr.ne')
  have htrans : MeasurePreserving A
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    simpa [A] using measurePreserving_add_left
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) q
  have hcomp : (fun x : EuclideanSpace ℝ (Fin d) => q + r • x) = A ∘ S := by
    funext x
    rfl
  calc
    _ = Measure.map (A ∘ S)
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by rw [hcomp]
    _ = Measure.map A (Measure.map S
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))) := by
      exact (Measure.map_map
        (μ := (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))))
        (by fun_prop) (by fun_prop)).symm
    _ = Measure.map A (ENNReal.ofReal ((r ^ d)⁻¹) •
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))) := by rw [hscale]
    _ = ENNReal.ofReal ((r ^ d)⁻¹) •
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) := by
      rw [Measure.map_smul, htrans.map_eq]

/-- Pull a compactly supported smooth unit-ball test function back to the translated ball. -/
private theorem affine_pullback_test_is_admissible
    {d : ℕ} [NeZero d]
    (q : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 < r)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφcompact : HasCompactSupport φ)
    (hφsupport : tsupport φ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :
    let ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun y => φ (r⁻¹ • (y - q))
    ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ Metric.ball q r := by
  dsimp
  let G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun y => r⁻¹ • (y - q)
  let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => q + r • x
  let T : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) :=
    (Homeomorph.addLeft (-q)).trans
      (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne'))
  have hTG : (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) = G := by
    funext y
    simp [T, G, sub_eq_add_neg, add_comm]
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin d) => r⁻¹ • (y - q))
    fun_prop
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ G) := hφ.comp hG
  have hψcompact : HasCompactSupport (φ ∘ G) := by
    have h := hφcompact.comp_homeomorph T
    simpa [hTG] using h
  have hts : tsupport (φ ∘ G) = G ⁻¹' tsupport φ := by
    rw [← hTG]
    exact tsupport_comp_eq_preimage φ T
  have hpre : F ⁻¹' Metric.ball q r = Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, F,
      add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, sub_zero]
    simpa using (mul_lt_mul_iff_right₀ hr : r * ‖x‖ < r * 1 ↔ ‖x‖ < 1)
  refine ⟨hψ, hψcompact, ?_⟩
  intro y hy
  change y ∈ tsupport (φ ∘ G) at hy
  rw [hts] at hy
  have hGy : G y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 := hφsupport hy
  have hFG : F (G y) = y := by
    simp [F, G, smul_sub, smul_smul, mul_inv_cancel₀ hr.ne']
  have hball : G y ∈ F ⁻¹' Metric.ball q r := by
    rw [hpre]
    exact hGy
  change F (G y) ∈ Metric.ball q r at hball
  rw [hFG] at hball
  exact hball

/-- Pull `L²` and zero test-function derivatives back along positive affine dilation.
Both directions of the affine map are needed: a test on the unit ball pushes to a test
on the ball with the same coordinate index and a nonzero factor `r⁻¹`. -/
private theorem affine_ball_zero_gradient_to_unit_ball
    {d : ℕ} [NeZero d]
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (q : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 < r)
    (hu : MemLp u (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball q r)))
    (hzero : ∀ i : Fin d, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball q r →
      ∫ x in Metric.ball q r, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0) :
    MemLp (fun x => u (q + r • x)) (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)) ∧
    (∀ i : Fin d, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 →
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        u (q + r • x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0) := by
  constructor
  · let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => q + r • x
    let U : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 1
    let B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball q r
    have hpre : F ⁻¹' B = U := by
      ext x
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, F, B, U,
        add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, sub_zero]
      simpa using (mul_lt_mul_iff_right₀ hr : r * ‖x‖ < r * 1 ↔ ‖x‖ < 1)
    have hfull : Measure.map F (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) =
        ENNReal.ofReal ((r ^ d)⁻¹) •
          (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) :=
      measure_map_affine_smul q hr
    have hF : Measurable F := by
      change Measurable (fun x : EuclideanSpace ℝ (Fin d) => q + r • x)
      fun_prop
    have hmap : Measure.map F
        ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict U) =
        ENNReal.ofReal ((r ^ d)⁻¹) •
          (MeasureTheory.volume.restrict B) := by
      calc
        _ = Measure.map F
            ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (F ⁻¹' B)) := by
          rw [hpre]
        _ = (Measure.map F (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))).restrict B := by
          exact (Measure.restrict_map hF Metric.isOpen_ball.measurableSet).symm
        _ = (ENNReal.ofReal ((r ^ d)⁻¹) •
            (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))).restrict B := by
          rw [hfull]
        _ = ENNReal.ofReal ((r ^ d)⁻¹) • (MeasureTheory.volume.restrict B) := by
          rw [Measure.restrict_smul]
    have hc : ENNReal.ofReal ((r ^ d)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hu' : MemLp u (ENNReal.ofReal 2)
        (ENNReal.ofReal ((r ^ d)⁻¹) • (MeasureTheory.volume.restrict B)) :=
      hu.smul_measure hc
    have hu'' : MemLp u (ENNReal.ofReal 2)
        (Measure.map F ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict U)) := by
      rw [hmap]
      exact hu'
    have hcomp := hu''.comp_of_map hF.aemeasurable
    change MemLp (fun x => u (q + r • x)) (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    exact hcomp
  · intro i φ hφ hφcompact hφsupport
    let ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun y => φ (r⁻¹ • (y - q))
    have hψdata := affine_pullback_test_is_admissible q r hr φ hφ hφcompact hφsupport
    have hψsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by simpa [ψ] using hψdata.1
    have hψcompact : HasCompactSupport ψ := by simpa [ψ] using hψdata.2.1
    have hψsupport : tsupport ψ ⊆ Metric.ball q r := by simpa [ψ] using hψdata.2.2
    let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => q + r • x
    let G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun y => r⁻¹ • (y - q)
    have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
      change ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclideanSpace ℝ (Fin d) => r⁻¹ • (y - q))
      fun_prop
    have hIdSub : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin d) => z - q) =
        fun _ => (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := by
      funext z
      simp [fderiv_sub_const]
      ext v
      rfl
    have hGderiv : fderiv ℝ G =
        fun _ => r⁻¹ • (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := by
      change fderiv ℝ (r⁻¹ • (fun z : EuclideanSpace ℝ (Fin d) => z - q)) = _
      rw [fderiv_const_smul_field, hIdSub]
      rfl
    have hFG (x : EuclideanSpace ℝ (Fin d)) : G (F x) = x := by
      simp [F, G, smul_sub, smul_smul, inv_mul_cancel₀ hr.ne']
    have hderiv (x : EuclideanSpace ℝ (Fin d)) :
        (fderiv ℝ ψ (F x)) (EuclideanSpace.single i 1) =
          r⁻¹ * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
      change (fderiv ℝ (φ ∘ G) (F x)) (EuclideanSpace.single i 1) = _
      rw [fderiv_comp (x := F x) (g := φ) (f := G)
        (hφ.contDiffAt.differentiableAt (by simp))
        (hG.contDiffAt.differentiableAt (by simp)), hGderiv]
      simp [G, hFG x, ContinuousLinearMap.comp_apply]
    let w : EuclideanSpace ℝ (Fin d) → ℝ := fun y =>
      u y * (fderiv ℝ ψ y) (EuclideanSpace.single i 1)
    let g : EuclideanSpace ℝ (Fin d) → ℝ := fun x =>
      u (F x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1)
    have hphysical : ∫ y in Metric.ball q r, w y = 0 := by
      simpa [w] using hzero i ψ hψsmooth hψcompact hψsupport
    have hscale := setIntegral_comp_affine_unit_ball w q hr
    have hunit : ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, w (F x) = 0 := by
      rw [hscale]
      simp [hphysical]
    have hintegrand : (fun x => w (F x)) = fun x => r⁻¹ * g x := by
      funext x
      simp [w, g, hderiv x, mul_left_comm]
    have hscaled : ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1,
        r⁻¹ * g x = 0 := by simpa [hintegrand] using hunit
    have hcoeff : r⁻¹ * (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, g x) = 0 := by
      simpa only [integral_const_mul] using hscaled
    exact (mul_eq_zero.mp hcoeff).resolve_left (inv_ne_zero hr.ne')

/-- Push a.e. constancy forward by the affine ball homeomorphism. -/
private theorem affine_ae_eq_const_on_ball
    {d : ℕ} [NeZero d]
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (q : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 < r)
    (c : ℝ)
    (hae : ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)), u (q + r • x) = c) :
    ∀ᵐ y ∂(MeasureTheory.volume.restrict (Metric.ball q r)), u y = c := by
  let F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => q + r • x
  let U : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball 0 1
  let B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball q r
  have hpre : F ⁻¹' B = U := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, F, B, U,
      add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr, sub_zero]
    simpa using (mul_lt_mul_iff_right₀ hr : r * ‖x‖ < r * 1 ↔ ‖x‖ < 1)
  have hF : Measurable F := by
    change Measurable (fun x : EuclideanSpace ℝ (Fin d) => q + r • x)
    fun_prop
  have hmap : Measure.map F
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict U) =
      ENNReal.ofReal ((r ^ d)⁻¹) •
        (MeasureTheory.volume.restrict B) := by
    calc
      _ = Measure.map F
          ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (F ⁻¹' B)) := by
        rw [hpre]
      _ = (Measure.map F (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))).restrict B := by
        exact (Measure.restrict_map hF Metric.isOpen_ball.measurableSet).symm
      _ = (ENNReal.ofReal ((r ^ d)⁻¹) •
          (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d)))).restrict B := by
        rw [measure_map_affine_smul q hr]
      _ = ENNReal.ofReal ((r ^ d)⁻¹) • (MeasureTheory.volume.restrict B) := by
        rw [Measure.restrict_smul]
  let T : EuclideanSpace ℝ (Fin d) ≃ₜ EuclideanSpace ℝ (Fin d) :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft q)
  have hTF : (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) = F := by
    funext x
    rfl
  have hmapae : Filter.map F
      (ae (MeasureTheory.volume.restrict U)) =
      ae (Measure.map F (MeasureTheory.volume.restrict U)) := by
    rw [← hTF]
    exact T.toMeasurableEquiv.map_ae _
  have hpush : ∀ᵐ y ∂(Measure.map F
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))).restrict U)), u y = c := by
    rw [← hmapae]
    change {y | u y = c} ∈ Filter.map F
      (ae (MeasureTheory.volume.restrict U))
    rw [Filter.mem_map]
    change {x | u (q + r • x) = c} ∈ ae (MeasureTheory.volume.restrict U)
    exact hae
  rw [hmap] at hpush
  exact (MeasureTheory.Measure.ae_ennreal_smul_measure_iff
    (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr d))))).mp hpush

/-- Zero distributional derivatives imply a.e. constancy on *each ball*, not on a
possibly disconnected open chart target containing that ball. -/
theorem euclideanBall_ae_eq_const_of_zero_weak_derivative
    {d : ℕ} [NeZero d]
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (q : EuclideanSpace ℝ (Fin d)) (r : ℝ) (hr : 0 < r)
    (hu : MemLp u (ENNReal.ofReal 2)
      (MeasureTheory.volume.restrict (Metric.ball q r)))
    (hzero : ∀ i : Fin d, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball q r →
      ∫ x in Metric.ball q r, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂(MeasureTheory.volume.restrict (Metric.ball q r)), u x = c := by
  let v : EuclideanSpace ℝ (Fin d) → ℝ := fun x => u (q + r • x)
  obtain ⟨hv, hderiv⟩ := affine_ball_zero_gradient_to_unit_ball u q r hr hu hzero
  let c : ℝ := ⨍ y in Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1, v y
    ∂MeasureTheory.volume
  have hunit : ∀ᵐ y ∂(MeasureTheory.volume.restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)), v y = c := by
    simpa [v, c] using ae_eq_average_on_unit_ball_of_zero_distributional_derivative
      v hv hderiv
  exact ⟨c, affine_ae_eq_const_on_ball u q r hr c (by simpa [v] using hunit)⟩

end KahlerForm
