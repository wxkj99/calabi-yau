module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

public section

namespace Complex

open scoped ContDiff Topology Interval
open Filter MeasureTheory

private theorem hasFTaylorSeriesUpToOn_restrictScalars
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] {n : ℕ∞ω} {f : E → F}
    {p : E → FormalMultilinearSeries ℂ E F} {s : Set E}
    (h : HasFTaylorSeriesUpToOn n f p s) :
    HasFTaylorSeriesUpToOn n f (fun x => (p x).restrictScalars ℝ) s where
  zero_eq x hx := h.zero_eq x hx
  fderivWithin m hm x hx :=
    ((ContinuousMultilinearMap.restrictScalarsLinear ℝ).hasFDerivAt.comp_hasFDerivWithinAt x <|
      (h.fderivWithin m hm x hx).restrictScalars ℝ :)
  cont m hm :=
    ContinuousMultilinearMap.continuous_restrictScalars.comp_continuousOn (h.cont m hm)

private theorem contDiffAt_restrictScalars
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
    [IsScalarTower ℝ ℂ F] {n : ℕ} {f : E → F} {x : E}
    (h : ContDiffAt ℂ n f x) : ContDiffAt ℝ n f x := by
  rw [← contDiffWithinAt_univ] at h ⊢
  intro m hm
  rcases h m hm with ⟨u, hu, p, hp⟩
  exact ⟨u, hu, (fun y => (p y).restrictScalars ℝ),
    hasFTaylorSeriesUpToOn_restrictScalars hp⟩

private theorem exists_neighborhood_affineSlice_subset
    {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U) (v : EuclideanSpace ℂ (Fin n)) :
    ∃ δ > 0, ∃ r > 0, ∀ x ∈ Metric.ball z δ, ∀ t : ℂ, t ∈ Metric.closedBall 0 r →
      x + t • v ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hz
  refine ⟨ε / 2, by positivity, ε / (2 * (‖v‖ + 1)), by positivity, ?_⟩
  intro x hx t ht
  have hx' : dist x z < ε / 2 := by simpa using hx
  have ht' : ‖t‖ ≤ ε / (2 * (‖v‖ + 1)) := by
    have := Metric.mem_closedBall.mp ht
    simpa [dist_eq_norm] using this
  have hva : 0 ≤ ‖v‖ := norm_nonneg v
  have hratio : ‖v‖ / (‖v‖ + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hsmul : ‖t • v‖ < ε / 2 := by
    calc
      ‖t • v‖ = ‖t‖ * ‖v‖ := norm_smul _ _
      _ ≤ (ε / (2 * (‖v‖ + 1))) * ‖v‖ :=
        mul_le_mul_of_nonneg_right ht' hva
      _ = (ε / 2) * (‖v‖ / (‖v‖ + 1)) := by field_simp
      _ < (ε / 2) * 1 := mul_lt_mul_of_pos_left hratio (by positivity)
      _ = ε / 2 := by ring
  have hdist : dist (x + t • v) x = ‖t • v‖ := by
    rw [dist_eq_norm]
    congr 1
    abel
  have hsum : dist (x + t • v) z < ε := by
    calc
      dist (x + t • v) z ≤ dist (x + t • v) x + dist x z := dist_triangle _ _ _
      _ = ‖t • v‖ + dist x z := by rw [hdist]
      _ < ε := by linarith
  exact hball hsum

private theorem fderiv_apply_eq_circleIntegral
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))} {x : EuclideanSpace ℂ (Fin n)}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) (hx : x ∈ U)
    (v : EuclideanSpace ℂ (Fin n)) {r : ℝ} (hr : 0 < r)
    (htube : ∀ t ∈ Metric.closedBall (0 : ℂ) r, x + t • v ∈ U) :
    ∮ z in C(0, r), (1 / z ^ 2) • ψ (x + z • v) =
      (2 * Real.pi * I : ℂ) • fderiv ℂ ψ x v := by
  let g : ℂ → EuclideanSpace ℂ (Fin n) := fun t => x + t • v
  let f : ℂ → EuclideanSpace ℂ (Fin n) := ψ ∘ g
  have hψx : DifferentiableAt ℂ ψ x := hψ.differentiableAt (hU.mem_nhds hx)
  have hgd : DifferentiableAt ℂ g 0 := by fun_prop
  have hline : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r) := by
    intro t ht
    have hψt : DifferentiableAt ℂ ψ (g t) :=
      hψ.differentiableAt (hU.mem_nhds (htube t ht))
    exact (hψt.comp t (by fun_prop)).differentiableWithinAt
  have hCauchy := hline.deriv_eq_smul_circleIntegral hr
  have hlineDeriv : deriv f 0 = fderiv ℂ ψ x v := by
    change fderiv ℂ (ψ ∘ g) 0 (1 : ℂ) = _
    have hψg0 : DifferentiableAt ℂ ψ (g 0) := by simpa [g] using hψx
    have hgderiv : fderiv ℂ g 0 1 = v := by
      dsimp [g]
      simp [fderiv_const_add, fderiv_smul_const]
    have hcomp : fderiv ℂ (ψ ∘ g) 0 =
        (fderiv ℂ ψ (g 0)).comp (fderiv ℂ g 0) :=
      fderiv_comp (f := g) (g := ψ) 0 hψg0 hgd
    rw [hcomp]
    change fderiv ℂ ψ (g 0) (fderiv ℂ g 0 1) = _
    rw [hgderiv]
    simp [g]
  rw [hlineDeriv] at hCauchy
  simpa [f, g, sub_zero, pow_two, Real.pi] using hCauchy

private theorem continuousAt_fderiv_apply_complex
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hψ : DifferentiableOn ℂ ψ U) {x₀ : EuclideanSpace ℂ (Fin n)} (hx₀ : x₀ ∈ U)
    (v : EuclideanSpace ℂ (Fin n)) :
    ContinuousAt (fun x => fderiv ℂ ψ x v) x₀ := by
  obtain ⟨δ, hδ, r, hr, htube⟩ := exists_neighborhood_affineSlice_subset hU hx₀ v
  let S := Metric.sphere (0 : ℂ) r
  let Y := {z : ℂ // z ∈ S}
  let F : EuclideanSpace ℂ (Fin n) → Y → EuclideanSpace ℂ (Fin n) := fun x z =>
    (1 / z.val ^ 2) • ψ (x + z.val • v)
  have hnonzero : ∀ z : Y, z.1 ≠ 0 := by
    intro z hz
    have hdist : dist z.1 (0 : ℂ) = r := Metric.mem_sphere.mp z.2
    have hr0 : (0 : ℝ) = r := by simpa [hz] using hdist
    exact (ne_of_gt hr) hr0.symm
  have hkernel : Continuous (fun p : EuclideanSpace ℂ (Fin n) × Y =>
      (1 / p.2.val ^ 2 : ℂ)) := by
    have hval : Continuous (fun p : EuclideanSpace ℂ (Fin n) × Y => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact continuous_const.div (hval.pow 2) fun p => pow_ne_zero _ (hnonzero p.2)
  have hline : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × Y => p.1 + p.2.val • v)
      (Metric.ball x₀ δ ×ˢ Set.univ) := by
    have hval : Continuous (fun p : EuclideanSpace ℂ (Fin n) × Y => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hlineCont : Continuous
        (fun p : EuclideanSpace ℂ (Fin n) × Y => p.1 + p.2.val • v) :=
      continuous_fst.add (hval.smul continuous_const)
    exact hlineCont.continuousOn
  have hmap : Set.MapsTo
      (fun p : EuclideanSpace ℂ (Fin n) × Y => p.1 + p.2.val • v)
      (Metric.ball x₀ δ ×ˢ Set.univ) U := by
    intro p hp
    exact htube p.1 hp.1 p.2.val (Metric.sphere_subset_closedBall p.2.property)
  have hψline : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × Y => ψ (p.1 + p.2.val • v))
      (Metric.ball x₀ δ ×ˢ Set.univ) := hψ.continuousOn.comp hline hmap
  have hF : ContinuousOn (Function.uncurry F) (Metric.ball x₀ δ ×ˢ Set.univ) := by
    change ContinuousOn (fun p : EuclideanSpace ℂ (Fin n) × Y =>
      (1 / p.2.val ^ 2 : ℂ) • ψ (p.1 + p.2.val • v)) _
    exact hkernel.continuousOn.smul hψline
  have hUniform : TendstoUniformly F (F x₀) (𝓝 x₀) :=
    hF.tendstoUniformly (Metric.ball_mem_nhds x₀ hδ)
  have hUniformOn : TendstoUniformlyOn
      (fun (x : EuclideanSpace ℂ (Fin n)) (z : ℂ) => (1 / z ^ 2 : ℂ) • ψ (x + z • v))
      (fun (z : ℂ) => (1 / z ^ 2 : ℂ) • ψ (x₀ + z • v)) (𝓝 x₀) S := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    change TendstoUniformly (fun (x : EuclideanSpace ℂ (Fin n)) (z : Y) => F x z)
      (fun (z : Y) => F x₀ z) (𝓝 x₀)
    exact hUniform
  have hcircleCont : ∀ᶠ x in 𝓝 x₀, ContinuousOn
      (fun z : ℂ => (1 / z ^ 2 : ℂ) • ψ (x + z • v)) S := by
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
    have hline' : ContinuousOn (fun z : ℂ => x + z • v) S := by fun_prop
    have hmap' : Set.MapsTo (fun z : ℂ => x + z • v) S U := by
      intro z hz
      exact htube x hx z (Metric.sphere_subset_closedBall hz)
    have hψ' : ContinuousOn (fun z : ℂ => ψ (x + z • v)) S :=
      hψ.continuousOn.comp hline' hmap'
    have hk' : ContinuousOn (fun z : ℂ => (1 / z ^ 2 : ℂ)) S := by
      apply continuousOn_const.div (continuousOn_id.pow 2)
      intro z hz
      exact pow_ne_zero _ (hnonzero ⟨z, hz⟩)
    exact hk'.smul hψ'
  have hcircle := hUniformOn.tendsto_circleIntegral_of_continuousOn (le_of_lt hr) hcircleCont
  let c : ℂ := 2 * Real.pi * I
  have hc : c ≠ 0 := by simp [c, Real.pi_ne_zero, I_ne_zero]
  have hscaled : Tendsto (fun x => c⁻¹ • ∮ z in C(0, r),
      (1 / z ^ 2 : ℂ) • ψ (x + z • v)) (𝓝 x₀)
      (𝓝 (c⁻¹ • ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (x₀ + z • v))) := by
    have hccont : ContinuousAt (fun y : EuclideanSpace ℂ (Fin n) => c⁻¹ • y)
        (∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (x₀ + z • v)) := by fun_prop
    exact hccont.tendsto.comp hcircle
  have heq : ∀ᶠ x in 𝓝 x₀, fderiv ℂ ψ x v =
      c⁻¹ • ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (x + z • v) := by
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
    have hxU : x ∈ U := by
      simpa using htube x hx 0 (by simp [Metric.mem_closedBall, hr.le])
    have hformula := fderiv_apply_eq_circleIntegral hU hψ hxU v hr (htube x hx)
    calc
      fderiv ℂ ψ x v = c⁻¹ • (c • fderiv ℂ ψ x v) := by simp [smul_smul, hc]
      _ = c⁻¹ • ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (x + z • v) := by rw [hformula]
  have h0formula :=
    fderiv_apply_eq_circleIntegral hU hψ hx₀ v hr (htube x₀ (Metric.mem_ball_self hδ))
  have h0eq : c⁻¹ • ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (x₀ + z • v) =
      fderiv ℂ ψ x₀ v := by
    rw [h0formula]
    exact inv_smul_smul₀ hc _
  change Tendsto (fun x => fderiv ℂ ψ x v) (𝓝 x₀) (𝓝 (fderiv ℂ ψ x₀ v))
  rw [← h0eq]
  have heq' : ∀ᶠ x in 𝓝 x₀,
      c⁻¹ • ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (x + z • v) = fderiv ℂ ψ x v := by
    filter_upwards [heq] with x hx
    exact hx.symm
  exact Tendsto.congr' heq' hscaled

private theorem continuousOn_fderiv_apply_complex
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hψ : DifferentiableOn ℂ ψ U) (v : EuclideanSpace ℂ (Fin n)) :
    ContinuousOn (fun x => fderiv ℂ ψ x v) U := by
  intro x hx
  exact (continuousAt_fderiv_apply_complex hU hψ hx v).continuousWithinAt

private theorem continuousOn_fderiv_complex
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) :
    ContinuousOn (fderiv ℂ ψ) U := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] Fin n → ℂ := EuclideanSpace.equiv (Fin n) ℂ
  let d : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) ≃L[ℂ]
      Fin n → EuclideanSpace ℂ (Fin n) :=
    (e.arrowCongr (1 : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))).trans
      (ContinuousLinearEquiv.piRing (Fin n))
  have hcoords : ContinuousOn (fun x => d (fderiv ℂ ψ x)) U := by
    rw [continuousOn_pi]
    intro i
    have hcomponent := continuousOn_fderiv_apply_complex hU hψ
      (e.symm (Pi.single i (1 : ℂ)))
    have hcoord : (fun x => d (fderiv ℂ ψ x) i) =
        fun x => fderiv ℂ ψ x (e.symm (Pi.single i (1 : ℂ))) := by
      funext x
      change (LinearEquiv.piRing ℂ (EuclideanSpace ℂ (Fin n)) (Fin n) ℂ
          (((e.arrowCongr (1 : EuclideanSpace ℂ (Fin n) ≃L[ℂ]
            EuclideanSpace ℂ (Fin n))) (fderiv ℂ ψ x)).toLinearMap)) i = _
      rw [LinearEquiv.piRing_apply]
      simp [ContinuousLinearEquiv.arrowCongr_apply]
      rfl
    rw [hcoord]
    exact hcomponent
  have hback : ContinuousOn (d.symm ∘ fun x => d (fderiv ℂ ψ x)) U :=
    d.symm.continuous.comp_continuousOn hcoords
  convert hback using 1
  funext x
  simp

private theorem hasFDerivAt_circleIntegral_affineSlice
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))} {x : EuclideanSpace ℂ (Fin n)}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U)
    (hψderiv : ContinuousOn (fderiv ℂ ψ) U)
    (v : EuclideanSpace ℂ (Fin n)) {r : ℝ} (hr : 0 < r)
    (htube : ∀ t ∈ Metric.closedBall (0 : ℂ) r, x + t • v ∈ U) :
    HasFDerivAt
      (fun y : EuclideanSpace ℂ (Fin n) =>
        ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (y + z • v))
      (∮ z in C(0, r), (1 / z ^ 2 : ℂ) • fderiv ℂ ψ (x + z • v)) x := by
  let E := EuclideanSpace ℂ (Fin n)
  let J : Set ℝ := Set.Icc 0 (2 * Real.pi)
  let γ : ℝ → ℂ := circleMap 0 r
  let T : E × ℝ → E := fun p => p.1 + γ p.2 • v
  have hJ : IsCompact J := isCompact_Icc
  have hT : Continuous T := by fun_prop
  have hTopen : IsOpen (T ⁻¹' U) := hU.preimage hT
  have hTmem : ∀ θ ∈ J, T (x, θ) ∈ U := by
    intro θ hθ
    apply htube (γ θ)
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [γ, norm_circleMap_zero, abs_of_pos hr]
  let P : E → ℝ → Prop := fun y θ => T (y, θ) ∈ U
  have hTneigh : ∀ θ ∈ J, ∀ᶠ p : E × ℝ in 𝓝 (x, θ), P p.1 p.2 := by
    intro θ hθ
    filter_upwards [hTopen.mem_nhds (hTmem θ hθ)] with p hp
    simpa [P, T] using hp
  have hnear : ∀ᶠ y : E in 𝓝 x, ∀ θ ∈ J, T (y, θ) ∈ U := by
    simpa [J, P] using
      (hJ.eventually_forall_of_forall_eventually (x₀ := x) (P := P) hTneigh)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnear
  let s : Set E := Metric.ball x (δ / 2)
  have hs : s ∈ 𝓝 x := by
    exact Metric.ball_mem_nhds x (by positivity)
  have hsmall : ∀ y ∈ Metric.closedBall x (δ / 2), ∀ θ ∈ J, T (y, θ) ∈ U := by
    intro y hy θ hθ
    have hyball : y ∈ Metric.ball x δ := by
      apply Metric.mem_ball.mpr
      have hdist : dist y x ≤ δ / 2 := Metric.mem_closedBall.mp hy
      linarith [hδ]
    exact (hball hyball) θ hθ
  let D : Set (E × ℝ) := Metric.closedBall x (δ / 2) ×ˢ J
  have hD : IsCompact D := (isCompact_closedBall x (δ / 2)).prod hJ
  have hDmap : ∀ p ∈ D, T p ∈ U := by
    rintro ⟨y, θ⟩ ⟨hy, hθ⟩
    exact hsmall y hy θ hθ
  have hTcontD : ContinuousOn T D := hT.continuousOn
  have hderivCont : ContinuousOn (fun p : E × ℝ => fderiv ℂ ψ (T p)) D :=
    hψderiv.comp hTcontD hDmap
  have hderivCompact : IsCompact ((fun p : E × ℝ => fderiv ℂ ψ (T p)) '' D) :=
    hD.image_of_continuousOn hderivCont
  obtain ⟨B, hB⟩ :=
    (Metric.isBounded_iff_subset_closedBall
      (0 : E →L[ℂ] E)).1 hderivCompact.isBounded
  let k : ℝ → ℂ := fun θ => deriv γ θ * (1 / γ θ ^ 2)
  let F : E → ℝ → E := fun y θ => k θ • ψ (y + γ θ • v)
  let F' : E → ℝ → E →L[ℂ] E := fun y θ => k θ • fderiv ℂ ψ (y + γ θ • v)
  let bound : ℝ → ℝ := fun θ => ‖k θ‖ * B
  have hγne : ∀ θ ∈ J, γ θ ≠ 0 := by
    intro θ hθ
    change circleMap 0 r θ ≠ 0
    exact circleMap_ne_center (c := 0) hr.ne'
  have hγcont : Continuous γ := by
    change Continuous (circleMap 0 r)
    fun_prop
  have hderivCircle : Continuous (deriv γ) := by
    have hd : deriv γ = fun θ => γ θ * I := by
      funext θ
      change deriv (circleMap 0 r) θ = circleMap 0 r θ * I
      exact deriv_circleMap (0 : ℂ) r θ
    rw [hd]
    fun_prop
  have hk : ContinuousOn k J := by
    dsimp [k]
    apply hderivCircle.continuousOn.mul
    apply continuousOn_const.div (hγcont.continuousOn.pow 2)
    intro θ hθ
    exact pow_ne_zero _ (hγne θ hθ)
  have hFcont : ∀ y ∈ Metric.closedBall x (δ / 2),
      ContinuousOn (F y) J := by
    intro y hy
    have hline : Continuous (fun θ : ℝ => y + γ θ • v) := by fun_prop
    have hlineU : ∀ θ ∈ J, y + γ θ • v ∈ U := by
      intro θ hθ
      exact hsmall y hy θ hθ
    have hψline : ContinuousOn (fun θ : ℝ => ψ (y + γ θ • v)) J :=
      hψ.continuousOn.comp hline.continuousOn hlineU
    change ContinuousOn (fun θ => k θ • ψ (y + γ θ • v)) J
    exact hk.smul hψline
  have hFprimeCont : ContinuousOn (F' x) J := by
    have hline : Continuous (fun θ : ℝ => x + γ θ • v) := by fun_prop
    have hlineU : ∀ θ ∈ J, x + γ θ • v ∈ U := by
      intro θ hθ
      exact hsmall x (Metric.mem_closedBall_self (by positivity)) θ hθ
    have hderivLine : ContinuousOn (fun θ : ℝ => fderiv ℂ ψ (x + γ θ • v)) J :=
      hψderiv.comp hline.continuousOn hlineU
    change ContinuousOn (fun θ => k θ • fderiv ℂ ψ (x + γ θ • v)) J
    exact hk.smul hderivLine
  have hboundcont : ContinuousOn bound J := by
    change ContinuousOn (fun θ => ‖k θ‖ * B) J
    exact (hk.norm).mul continuousOn_const
  have hFint : IntervalIntegrable (F x) volume 0 (2 * Real.pi) :=
    (hFcont x (Metric.mem_closedBall_self (by positivity))).intervalIntegrable_of_Icc
      (le_of_lt (by positivity))
  have hFprimeInt : IntervalIntegrable (F' x) volume 0 (2 * Real.pi) :=
    hFprimeCont.intervalIntegrable_of_Icc (le_of_lt (by positivity))
  have hFmeas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable (F y) (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < δ / 2)] with y hy
    have hy' : y ∈ Metric.closedBall x (δ / 2) := by
      apply Metric.mem_closedBall.mpr
      exact le_of_lt (Metric.mem_ball.mp hy)
    exact (hFcont y hy').aestronglyMeasurable_of_subset_isCompact hJ measurableSet_uIoc (by
      intro θ hθ
      simpa only [J, Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
        (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 2 * Real.pi) hθ))
  have hFprimeMeas : AEStronglyMeasurable (F' x)
      (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    exact hFprimeCont.aestronglyMeasurable_of_subset_isCompact hJ measurableSet_uIoc (by
      intro θ hθ
      simpa only [J, Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
        (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 2 * Real.pi) hθ))
  have hboundInt : IntervalIntegrable bound volume 0 (2 * Real.pi) :=
    hboundcont.intervalIntegrable_of_Icc (le_of_lt (by positivity))
  have hbound : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ y ∈ s, ‖F' y θ‖ ≤ bound θ := by
    apply Filter.Eventually.of_forall
    intro θ hθ y hy
    have hθJ : θ ∈ J := by
      simpa only [J, Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
        (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 2 * Real.pi) hθ)
    have hyD : y ∈ Metric.closedBall x (δ / 2) := by
      apply Metric.mem_closedBall.mpr
      exact le_of_lt (Metric.mem_ball.mp hy)
    have hfd : ‖fderiv ℂ ψ (y + γ θ • v)‖ ≤ B := by
      have hmem : fderiv ℂ ψ (y + γ θ • v) ∈
          (fun p : E × ℝ => fderiv ℂ ψ (T p)) '' D := by
        refine ⟨(y, θ), ⟨hyD, hθJ⟩, ?_⟩
        rfl
      have hclosed := Metric.mem_closedBall.mp (hB hmem)
      rw [dist_eq_norm] at hclosed
      simpa using hclosed
    calc
      ‖F' y θ‖ = ‖k θ‖ * ‖fderiv ℂ ψ (y + γ θ • v)‖ := by
        simp [F', norm_smul]
      _ ≤ ‖k θ‖ * B := mul_le_mul_of_nonneg_left hfd (norm_nonneg _)
  have hdiff : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ y ∈ s, HasFDerivAt (F · θ) (F' y θ) y := by
    apply Filter.Eventually.of_forall
    intro θ hθ y hy
    have hyU : y + γ θ • v ∈ U := hsmall y
      (Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hy)))
      θ (by
        have : θ ∈ J := by
          simpa only [J, Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using
            (Set.uIoc_subset_uIcc (a := (0 : ℝ)) (b := 2 * Real.pi) hθ)
        exact this)
    have hψat : DifferentiableAt ℂ ψ (y + γ θ • v) :=
      hψ.differentiableAt (hU.mem_nhds hyU)
    have harg : HasFDerivAt (fun q : E => q + γ θ • v)
        (ContinuousLinearMap.id ℂ E) y := by
      exact (hasFDerivAt_id y).add_const (γ θ • v)
    have hcomp := hψat.hasFDerivAt.comp y harg
    change HasFDerivAt (fun q : E => k θ • ψ (q + γ θ • v))
      (k θ • fderiv ℂ ψ (y + γ θ • v)) y
    exact hcomp.const_smul (k θ)
  have hkey := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := F) (F' := F') (bound := bound) (s := s) hs hFmeas hFint hFprimeMeas
    hbound hboundInt hdiff
  have hkey' : HasFDerivAt (fun y : E => ∫ θ in 0..2 * Real.pi, F y θ)
      (∫ θ in 0..2 * Real.pi, F' x θ) x := hkey
  change HasFDerivAt
    (fun y : E => ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (y + z • v))
    (∮ z in C(0, r), (1 / z ^ 2 : ℂ) • fderiv ℂ ψ (x + z • v)) x
  have hfun : (fun y : E => ∫ θ in 0..2 * Real.pi, F y θ) =
      fun y => ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (y + z • v) := by
    funext y
    rw [circleIntegral_def_Icc]
    simp only [F, k, γ, smul_smul]
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hderiv : (∫ θ in 0..2 * Real.pi, F' x θ) =
      ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • fderiv ℂ ψ (x + z • v) := by
    rw [circleIntegral_def_Icc]
    simp only [F', k, γ, smul_smul]
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      Measure.restrict_congr_set Ioc_ae_eq_Icc]
  rw [← hfun, ← hderiv]
  exact hkey'

private theorem differentiableOn_fderiv_apply_complex
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U)
    (v : EuclideanSpace ℂ (Fin n)) :
    DifferentiableOn ℂ (fun x => fderiv ℂ ψ x v) U := by
  intro x hx
  obtain ⟨δ, hδ, r, hr, htube⟩ := exists_neighborhood_affineSlice_subset hU hx v
  have hψderiv : ContinuousOn (fderiv ℂ ψ) U := continuousOn_fderiv_complex hU hψ
  have hparam := hasFDerivAt_circleIntegral_affineSlice hU hψ hψderiv v hr (htube x (Metric.mem_ball_self hδ))
  let c : ℂ := 2 * Real.pi * I
  have hc : c ≠ 0 := by simp [c, Real.pi_ne_zero, I_ne_zero]
  have hscaled : DifferentiableAt ℂ
      (fun y : EuclideanSpace ℂ (Fin n) =>
        c⁻¹ • ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (y + z • v)) x :=
    (hparam.const_smul c⁻¹).differentiableAt
  have heq : (fun y => fderiv ℂ ψ y v) =ᶠ[𝓝 x]
      (fun y => c⁻¹ • ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (y + z • v)) := by
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
    have hyU : y ∈ U := by
      simpa using htube y hy 0 (by simp [Metric.mem_closedBall, hr.le])
    have hformula := fderiv_apply_eq_circleIntegral hU hψ hyU v hr (htube y hy)
    calc
      fderiv ℂ ψ y v = c⁻¹ • (c • fderiv ℂ ψ y v) := by simp [smul_smul, hc]
      _ = c⁻¹ • ∮ z in C(0, r), (1 / z ^ 2 : ℂ) • ψ (y + z • v) := by rw [hformula]
  exact (hscaled.congr_of_eventuallyEq heq).differentiableWithinAt

private theorem differentiableOn_fderiv_complex
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) :
    DifferentiableOn ℂ (fderiv ℂ ψ) U := by
  let e : EuclideanSpace ℂ (Fin n) ≃L[ℂ] Fin n → ℂ := EuclideanSpace.equiv (Fin n) ℂ
  let d : (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) ≃L[ℂ]
      Fin n → EuclideanSpace ℂ (Fin n) :=
    (e.arrowCongr (1 : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))).trans
      (ContinuousLinearEquiv.piRing (Fin n))
  have hcoords : DifferentiableOn ℂ (fun x => d (fderiv ℂ ψ x)) U := by
    rw [differentiableOn_pi]
    intro i
    have hcomponent := differentiableOn_fderiv_apply_complex hU hψ
      (e.symm (Pi.single i (1 : ℂ)))
    have hcoord : (fun x => d (fderiv ℂ ψ x) i) =
        fun x => fderiv ℂ ψ x (e.symm (Pi.single i (1 : ℂ))) := by
      funext x
      change (LinearEquiv.piRing ℂ (EuclideanSpace ℂ (Fin n)) (Fin n) ℂ
          (((e.arrowCongr (1 : EuclideanSpace ℂ (Fin n) ≃L[ℂ]
            EuclideanSpace ℂ (Fin n))) (fderiv ℂ ψ x)).toLinearMap)) i = _
      rw [LinearEquiv.piRing_apply]
      simp [ContinuousLinearEquiv.arrowCongr_apply]
      rfl
    rw [hcoord]
    exact hcomponent
  have hback : DifferentiableOn ℂ (d.symm ∘ fun x => d (fderiv ℂ ψ x)) U :=
    d.symm.differentiable.comp_differentiableOn hcoords
  convert hback using 1
  funext x
  simp

private theorem continuousOn_secondFDeriv_complex
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) :
    ContinuousOn (fderiv ℂ (fderiv ℂ ψ)) U := by
  let E := EuclideanSpace ℂ (Fin n)
  let e : E ≃L[ℂ] Fin n → ℂ := EuclideanSpace.equiv (Fin n) ℂ
  let d : (E →L[ℂ] E) ≃L[ℂ] Fin n → E :=
    (e.arrowCongr (1 : E ≃L[ℂ] E)).trans (ContinuousLinearEquiv.piRing (Fin n))
  let d₂ : (E →L[ℂ] (E →L[ℂ] E)) ≃L[ℂ] Fin n → Fin n → E :=
    (e.arrowCongr d).trans (ContinuousLinearEquiv.piRing (Fin n))
  have hcoords : ContinuousOn
      (fun x => d₂ (fderiv ℂ (fderiv ℂ ψ) x)) U := by
    rw [continuousOn_pi]
    intro k
    rw [continuousOn_pi]
    intro i
    let vk : E := e.symm (Pi.single k (1 : ℂ))
    let vi : E := e.symm (Pi.single i (1 : ℂ))
    let ψi : E → E := fun x => fderiv ℂ ψ x vi
    have hψi : DifferentiableOn ℂ ψi U :=
      differentiableOn_fderiv_apply_complex hU hψ vi
    have hc := continuousOn_fderiv_apply_complex hU hψi vk
    refine ContinuousOn.congr hc ?_
    intro x hx
    have hDx : DifferentiableAt ℂ (fderiv ℂ ψ) x :=
      (differentiableOn_fderiv_complex hU hψ).differentiableAt (hU.mem_nhds hx)
    have hev : DifferentiableAt ℂ (fun A : E →L[ℂ] E => A vi) (fderiv ℂ ψ x) := by
      fun_prop
    have hcomp := fderiv_comp (f := fun y : E => fderiv ℂ ψ y)
      (g := fun A : E →L[ℂ] E => A vi) x hev hDx
    have hcompApp := congrArg (fun L : E →L[ℂ] E => L vk) hcomp
    have hcoord : d₂ (fderiv ℂ (fderiv ℂ ψ) x) k i =
        (fderiv ℂ (fderiv ℂ ψ) x) vk vi := by
      change (LinearEquiv.piRing ℂ (Fin n → E) (Fin n) ℂ
          (((e.arrowCongr d) (fderiv ℂ (fderiv ℂ ψ) x)).toLinearMap)) k i = _
      rw [LinearEquiv.piRing_apply]
      simp [ContinuousLinearEquiv.arrowCongr_apply, d, e, vk, vi]
      rfl
    have hEval : fderiv ℂ (fun A : E →L[ℂ] E => A vi)
        (fderiv ℂ ψ x) = ContinuousLinearMap.apply ℂ E vi :=
      (ContinuousLinearMap.apply ℂ E vi).isBoundedLinearMap.fderiv
    calc
      d₂ (fderiv ℂ (fderiv ℂ ψ) x) k i =
          (fderiv ℂ (fderiv ℂ ψ) x) vk vi := hcoord
      _ = fderiv ℂ ψi x vk := by
        rw [hEval] at hcompApp
        simpa [ψi, Function.comp_def] using hcompApp.symm
  have hback : ContinuousOn
      (d₂.symm ∘ fun x => d₂ (fderiv ℂ (fderiv ℂ ψ) x)) U :=
    d₂.symm.continuous.comp_continuousOn hcoords
  convert hback using 1
  funext x
  simp

private theorem differentiableOn_fderiv_contDiffOn_complex_one
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) :
    ContDiffOn ℂ 1 (fderiv ℂ ψ) U := by
  have hderiv : DifferentiableOn ℂ (fderiv ℂ ψ) U :=
    differentiableOn_fderiv_complex hU hψ
  have hsecond : ContDiffOn ℂ 0 (fderiv ℂ (fderiv ℂ ψ)) U :=
    contDiffOn_zero.mpr (continuousOn_secondFDeriv_complex hU hψ)
  have hcont : ContDiffOn ℂ (0 + 1) (fderiv ℂ ψ) U := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) hU]
    refine ⟨hderiv, ?_, hsecond⟩
    intro h
    norm_num at h
  norm_num at hcont ⊢
  exact hcont

private theorem differentiableOn_contDiffOn_complex_two
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hψ : DifferentiableOn ℂ ψ U) :
    ContDiffOn ℂ 2 ψ U := by
  have hcont : ContDiffOn ℂ (1 + 1) ψ U := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hU]
    refine ⟨hψ, ?_, differentiableOn_fderiv_contDiffOn_complex_one hU hψ⟩
    intro h
    norm_num at h
  norm_num at hcont ⊢
  exact hcont

/-- A holomorphic map on an open subset of finite-dimensional complex Euclidean space is
real twice continuously differentiable at each point of that subset. -/
theorem differentiableOn_contDiffAt_real_two
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))} {z : EuclideanSpace ℂ (Fin n)}
    (hU : IsOpen U) (hz : z ∈ U) (hψ : DifferentiableOn ℂ ψ U) :
    ContDiffAt ℝ 2 ψ z := by
  have hψ_complex : ContDiffAt ℂ 2 ψ z :=
    (differentiableOn_contDiffOn_complex_two hU hψ).contDiffAt (hU.mem_nhds hz)
  exact contDiffAt_restrictScalars hψ_complex

end Complex
