module

public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientIdentity
public import CalabiYau.Geometry.Manifold.Holder.ChartNorm
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.AllChartHolderBound.ChartTransitionTransfer
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.HolderAlgebra

/-!
# Uniform Hölder bounds for translated metric-Hessian segments

Fix the direction before choosing the positive step radius. Compact chart containment gives a
buffer on which the raw C²,α gauge transfers to this chart; affine interpolation preserves the
entrywise bounds. The statement does not reuse an externally supplied translation radius.
-/

public section

open scoped Manifold ContDiff NNReal Topology
open Set

namespace KahlerForm

private noncomputable def segmentHessianEval {n : ℕ}
    (v w : EuclideanSpace ℂ (Fin n)) :
    (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) v)

private noncomputable def segmentHessianEntryQ {n : ℕ} (i j : Fin n) :
    (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℂ := by
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let w : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iv := Complex.I • v
  let iw := Complex.I • w
  let e₁ := segmentHessianEval v w
  let e₂ := segmentHessianEval iv iw
  let e₃ := segmentHessianEval v iw
  let e₄ := segmentHessianEval iv w
  let realPart
      (e : (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ) :
      (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp e
  exact (1 / 4 : ℝ) •
    (realPart e₁ + realPart e₂ +
      (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp (realPart (e₃ - e₄)))

private theorem segmentHessianEntryQ_norm_le {n : ℕ} (i j : Fin n) :
    ‖segmentHessianEntryQ i j‖ ≤ 1 := by
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let w : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iv := Complex.I • v
  let iw := Complex.I • w
  have hv : ‖v‖ = 1 := by simp [v]
  have hw : ‖w‖ = 1 := by simp [w]
  have hiv : ‖iv‖ = 1 := by simp [iv, hv, norm_smul, Complex.norm_I]
  have hiw : ‖iw‖ = 1 := by simp [iw, hw, norm_smul, Complex.norm_I]
  have hEval (a b : EuclideanSpace ℂ (Fin n)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
      (T : EuclideanSpace ℂ (Fin n) →L[ℝ]
        EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) : ‖T a b‖ ≤ ‖T‖ := by
    calc
      ‖T a b‖ ≤ ‖T a‖ * ‖b‖ := (T a).le_opNorm b
      _ ≤ ‖T‖ * ‖a‖ * ‖b‖ := by gcongr; exact T.le_opNorm a
      _ = ‖T‖ := by rw [ha, hb]; ring
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  dsimp [segmentHessianEntryQ]
  have h1 : ‖Complex.ofReal (T v w)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval v w hv hw T
  have h2 : ‖Complex.ofReal (T iv iw)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval iv iw hiv hiw T
  have h3 : ‖Complex.ofReal (T v iw)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval v iw hv hiw T
  have h4 : ‖Complex.ofReal (T iv w)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval iv w hiv hw T
  have hrest : ‖Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ ≤
      ‖T‖ + ‖T‖ := by
    rw [norm_mul, Complex.norm_I]
    simpa only [one_mul] using (norm_sub_le _ _).trans (add_le_add h3 h4)
  have hnum : ‖Complex.ofReal (T v w) + Complex.ofReal (T iv iw) +
      Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ ≤ 4 * ‖T‖ := by
    calc
      _ ≤ ‖Complex.ofReal (T v w)‖ + ‖Complex.ofReal (T iv iw)‖ +
          ‖Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ := by
        calc
          _ ≤ ‖Complex.ofReal (T v w) + Complex.ofReal (T iv iw)‖ +
              ‖Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ := norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ 4 * ‖T‖ := by nlinarith
  rw [one_mul]
  rw [_root_.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hscaled : (1 / 4) *
      ‖Complex.ofReal (T v w) + Complex.ofReal (T iv iw) +
        Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ ≤ ‖T‖ := by
    calc
      (1 / 4) * _ ≤ (1 / 4) * (4 * ‖T‖) := mul_le_mul_of_nonneg_left hnum (by norm_num)
      _ = ‖T‖ := by ring
  simpa [segmentHessianEval, v, w, iv, iw, mul_sub] using hscaled

private theorem segmentHessian_eq_entryQ {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (i j : Fin n) :
    complexHessian f z i j =
      segmentHessianEntryQ i j (fderiv ℝ (fderiv ℝ f) z) := by
  rw [complexHessian_apply hf]
  simp [segmentHessianEntryQ, segmentHessianEval, Complex.ofRealCLM_apply]
  ring

private theorem segmentHolderBoundOn_of_contDiffOn_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U K : Set E} {f : E → F} {α : ℝ≥0}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderBoundOn 0 α C K f := by
  classical
  have hNormCont : ContinuousOn (fun x => ‖f x‖) K :=
    (hf.continuousOn.mono hKU).norm
  obtain ⟨B, hB₀, hB⟩ := (hK.bddAbove_image hNormCont).exists_ge 0
  let C : ℝ≥0 := ⟨B, hB₀⟩
  have hBound (x : E) (hx : x ∈ K) : ‖f x‖ ≤ (C : ℝ) := by
    exact_mod_cast hB (‖f x‖) ⟨x, hx, rfl⟩
  have hLoc : LocallyLipschitzOn K f := by
    intro x hx
    have hxU : x ∈ U := hKU hx
    have hfx : ContDiffAt ℝ 1 f x :=
      (hf.contDiffAt (hU.mem_nhds hxU)).of_le (by simp)
    obtain ⟨L, t, ht, hLip⟩ := hfx.exists_lipschitzOnWith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨L, Metric.ball x δ ∩ K,
      Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩, ?_⟩
    · exact fun y hy => ⟨hy.1, hy.2⟩
    · apply hLip.mono
      intro y hy
      exact hball hy.1
  obtain ⟨L, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hLoc
  have hdiamTop : Metric.ediam K ≠ ⊤ := hK.isBounded.ediam_ne_top
  let D : ℝ≥0 := (Metric.ediam K).toNNReal
  have hdist (x : E) (hx : x ∈ K) (y : E) (hy : y ∈ K) :
      edist x y ≤ (D : ENNReal) := by
    have heq : (D : ENNReal) = Metric.ediam K := ENNReal.coe_toNNReal hdiamTop
    rw [heq]
    exact Metric.edist_le_ediam_of_mem hx hy
  have hHolderF := hLip.holderOnWith.of_le hdist hα
  let Cα : ℝ≥0 := L * D ^ ((1 : ℝ) - (α : ℝ))
  let Ctot : ℝ≥0 := max (2 * C) Cα
  let JI : F ≃ₗᵢ[ℝ] (E [×0]→L[ℝ] F) :=
    (continuousMultilinearCurryFin0 ℝ E F).symm
  let J : F →L[ℝ] (E [×0]→L[ℝ] F) := JI.toContinuousLinearMap
  have hJlip : LipschitzWith 1 J := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (J x) (J y) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact JI.norm_map _
      _ ≤ 1 * dist x y := by simp
  have hJ : HolderWith 1 1 J := hJlip.holderWith
  have hHolderJet : HolderOnWith Cα α (iteratedFDeriv ℝ 0 f) K := by
    have hcomp : HolderOnWith (1 * Cα ^ (1 : ℝ)) (1 * α) (J ∘ f) K :=
      (hJ.holderOnWith Set.univ).comp hHolderF (by intro x hx; exact Set.mem_univ _)
    have hcomp' : HolderOnWith Cα α (J ∘ f) K := by
      simpa [NNReal.rpow_one, one_mul] using hcomp
    have heq : iteratedFDeriv ℝ 0 f = J ∘ f := by
      simpa [J] using (iteratedFDeriv_zero_eq_comp (𝕜 := ℝ) (f := f))
    rw [heq]
    exact hcomp'
  refine ⟨Ctot, ?_⟩
  constructor
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero]
    exact (hBound x hx).trans (by
      calc
        (C : ℝ) = 1 * C := by ring
        _ ≤ (2 * C : ℝ) := by gcongr; norm_num
        _ ≤ (Ctot : ℝ) := by exact_mod_cast (le_max_left (2 * C) Cα))
  · exact hHolderJet.mono_const (le_max_right _ _)

private theorem segmentHolderOnWith_zero_of_holderBoundOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E}
    {α C : ℝ≥0} {f : E → F} (hf : HolderBoundOn 0 α C K f) :
    HolderOnWith C α f K := by
  let L := continuousMultilinearCurryFin0 ℝ E F
  intro x hx y hy
  have h := hf.2 x hx y hy
  rw [iteratedFDeriv_zero_eq_comp] at h
  change edist (L.symm (f x)) (L.symm (f y)) ≤ _ at h
  rw [L.symm.edist_map] at h
  exact h

private theorem segmentHolderBoundOn_zero_add
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E}
    {α C D : ℝ≥0} {f g : E → F}
    (hf : HolderBoundOn 0 α C K f) (hg : HolderBoundOn 0 α D K g) :
    HolderBoundOn 0 α (C + D) K (fun z ↦ f z + g z) := by
  have hHolder : HolderOnWith (C + D) α (fun z ↦ f z + g z) K := by
    intro x hx y hy
    calc
      edist (f x + g x) (f y + g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
        edist_add_add_le _ _ _ _
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
          (D : ENNReal) * edist x y ^ (α : ℝ) := add_le_add (segmentHolderOnWith_zero_of_holderBoundOn hf x hx y hy)
            (segmentHolderOnWith_zero_of_holderBoundOn hg x hx y hy)
      _ = ((C + D : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_add, add_mul]
  have hBound (z : E) (hz : z ∈ K) : ‖f z + g z‖ ≤ (C + D : ℝ) := by
    calc
      ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
      _ ≤ (C : ℝ) + D := by
        have hfc := hf.1 0 le_rfl z hz
        have hgc := hg.1 0 le_rfl z hz
        simpa only [norm_iteratedFDeriv_zero] using add_le_add hfc hgc
  exact holderBoundOn_zero_of_localHolderOnWith hHolder hBound

private theorem segmentHolderBoundOn_hessianEntry
    {n : ℕ} {α H : ℝ≥0} {U K : Set (EuclideanSpace ℂ (Fin n))}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {j l : Fin n}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (huCont : ContDiffOn ℝ 2 u U) (hu : HolderBoundOn 2 α H K u)
    (Q : (EuclideanSpace ℂ (Fin n) →L[ℝ]
      EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℂ)
    (hQ : ‖Q‖ ≤ 1)
    (hEq : ∀ z, ContDiffAt ℝ 2 u z →
      complexHessian u z j l = Q (fderiv ℝ (fderiv ℝ u) z)) :
    HolderBoundOn 0 α (4 * H) K (fun z ↦ complexHessian u z j l) := by
  let E := EuclideanSpace ℂ (Fin n)
  let g : E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦ fderiv ℝ (fderiv ℝ u) z
  let C₁ := continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ
  let C₂ := continuousMultilinearCurryRightEquiv' ℝ 0 E (E →L[ℝ] ℝ)
  have hD₁ : ContDiffOn ℝ 1 (fderiv ℝ u) U := huCont.fderiv_of_isOpen hU (by rfl)
  have hg : ContDiffOn ℝ 0 g U := hD₁.fderiv_of_isOpen hU (by rfl)
  have hJetAt (z : E) (hz : z ∈ K) :
      iteratedFDeriv ℝ 0 (fun y ↦ complexHessian u y j l) z =
        Q.compContinuousMultilinearMap (iteratedFDeriv ℝ 0 g z) := by
    have hEqNear : (fun y ↦ complexHessian u y j l) =ᶠ[𝓝 z] (Q ∘ g) := by
      filter_upwards [hU.mem_nhds (hKU hz)] with y hy
      exact hEq y ((huCont y hy).contDiffAt (hU.mem_nhds hy))
    calc
      iteratedFDeriv ℝ 0 (fun y ↦ complexHessian u y j l) z =
          iteratedFDeriv ℝ 0 (Q ∘ g) z := (hEqNear.iteratedFDeriv ℝ 0).eq_of_nhds
      _ = Q.compContinuousMultilinearMap (iteratedFDeriv ℝ 0 g z) :=
        Q.iteratedFDeriv_comp_left ((hg z (hKU hz)).contDiffAt (hU.mem_nhds (hKU hz)))
          (by exact_mod_cast Nat.zero_le 0)
  have hC₂ (z : E) : iteratedFDeriv ℝ 0 g z =
      C₂ (iteratedFDeriv ℝ 1 (fderiv ℝ u) z) := by
    rw [iteratedFDeriv_succ_eq_comp_right (f := fderiv ℝ u) (x := z) (n := 0)]
    simp [C₂, g, E, LinearIsometryEquiv.apply_symm_apply]
  have hC₁ (z : E) : iteratedFDeriv ℝ 1 (fderiv ℝ u) z =
      C₁ (iteratedFDeriv ℝ 2 u z) := by
    rw [iteratedFDeriv_succ_eq_comp_right (f := u) (x := z) (n := 1)]
    simp [C₁, E, LinearIsometryEquiv.apply_symm_apply]
  have hCurryDist (x y : E) :
      dist (iteratedFDeriv ℝ 0 g x) (iteratedFDeriv ℝ 0 g y) =
        dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) := by
    rw [hC₂ x, hC₂ y, hC₁ x, hC₁ y]
    simp [C₁, C₂, (continuousMultilinearCurryRightEquiv' ℝ 1 E ℝ).dist_map,
      (continuousMultilinearCurryRightEquiv' ℝ 0 E (E →L[ℝ] ℝ)).dist_map]
  have hPostDist (S T : E [×0]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :
      dist (Q.compContinuousMultilinearMap S) (Q.compContinuousMultilinearMap T) ≤ dist S T := by
    have hdiff : Q.compContinuousMultilinearMap S - Q.compContinuousMultilinearMap T =
        Q.compContinuousMultilinearMap (S - T) := by
      ext m
      simp
    rw [dist_eq_norm, hdiff]
    calc
      ‖Q.compContinuousMultilinearMap (S - T)‖ ≤ ‖Q‖ * ‖S - T‖ :=
        Q.norm_compContinuousMultilinearMap_le _
      _ ≤ 1 * ‖S - T‖ := mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
      _ = dist S T := by simp [dist_eq_norm]
  have hsource : HolderOnWith (4 * H) α (iteratedFDeriv ℝ 2 u) K :=
    hu.2.mono_const (by
      calc
        H = 1 * H := by simp
        _ ≤ 4 * H := mul_le_mul_of_nonneg_right (by norm_num) (bot_le))
  have hHolder : HolderOnWith (4 * H) α
      (iteratedFDeriv ℝ 0 (fun z ↦ complexHessian u z j l)) K := by
    intro x hx y hy
    rw [hJetAt x hx, hJetAt y hy, edist_dist]
    calc
      ENNReal.ofReal (dist (Q.compContinuousMultilinearMap (iteratedFDeriv ℝ 0 g x))
          (Q.compContinuousMultilinearMap (iteratedFDeriv ℝ 0 g y))) ≤
        ENNReal.ofReal (dist (iteratedFDeriv ℝ 0 g x) (iteratedFDeriv ℝ 0 g y)) :=
          ENNReal.ofReal_le_ofReal (hPostDist _ _)
      _ = ENNReal.ofReal (dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y)) := by
        rw [hCurryDist]
      _ ≤ ((4 * H : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [← edist_dist]
        exact hsource x hx y hy
  refine ⟨?_, hHolder⟩
  intro r hr z hz
  have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
  subst r
  have hjetNorm : ‖iteratedFDeriv ℝ 0 g z‖ = ‖iteratedFDeriv ℝ 2 u z‖ := by
    dsimp [g]
    rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  rw [hJetAt z hz]
  calc
    ‖Q.compContinuousMultilinearMap (iteratedFDeriv ℝ 0 g z)‖ ≤
        ‖Q‖ * ‖iteratedFDeriv ℝ 0 g z‖ := Q.norm_compContinuousMultilinearMap_le _
    _ ≤ 1 * ‖iteratedFDeriv ℝ 2 u z‖ := by
      rw [hjetNorm]
      exact mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
    _ ≤ 4 * H := by
      have h := hu.1 2 (by norm_num) z hz
      have hH : (H : ℝ) ≤ (4 : ℝ) * (H : ℝ) := by nlinarith [NNReal.coe_nonneg H]
      simpa only [one_mul, NNReal.coe_mul] using h.trans
        (by simpa only [NNReal.coe_mul] using hH)

/-- The raw affine segment has a uniform entrywise value and Hölder bound for sufficiently small
steps in a fixed direction. The genuine C² assumption is separate from the raw chart gauge. -/
theorem exists_uniform_chart_segment_holderBoundOn
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₁ : α < 1)
    (φ : M → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (hGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (x : M) (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUcompact : IsCompact (closure U))
    (hUchart : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) :
    ∃ δ Kmat : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ, |h| < (δ : ℝ) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j l,
          HolderBoundOn 0 α Kmat U
            (fun z ↦
              (chartBootstrapMatrix ω₀ φ x z + s •
                (chartBootstrapMatrix ω₀ φ x (z + h • v) -
                  chartBootstrapMatrix ω₀ φ x z)) j l) := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let target := (extChartAt 𝓘(ℝ, E) x).target
  let N : Set (E × E) := {p | p.1 + p.2 ∈ target}
  have hNopen : IsOpen N := by
    have hadd : Continuous fun p : E × E ↦ p.1 + p.2 := by fun_prop
    have htarget : IsOpen target := isOpen_extChartAt_target x
    exact htarget.preimage hadd
  have hN : closure U ×ˢ ({0} : Set E) ⊆ N := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    have hw0 : w = 0 := Set.mem_singleton_iff.mp hw
    subst w
    have hzTarget : z ∈ target := by simpa [target, E] using hUchart hz
    change z + 0 ∈ target
    simpa using hzTarget
  obtain ⟨V, W, _hVopen, hWopen, hVW, h0W, hVWSum⟩ :=
    generalized_tube_lemma hUcompact isCompact_singleton hNopen hN
  have h0 : (0 : E) ∈ W := h0W (Set.mem_singleton 0)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWopen 0 h0
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let K' : Set E := (fun p : E × E ↦ p.1 + p.2) ''
    (closure U ×ˢ Metric.closedBall (0 : E) r)
  have hK'compact : IsCompact K' := by
    dsimp [K']
    exact hUcompact.prod (isCompact_closedBall _ _) |>.image (by fun_prop)
  have hK'target : K' ⊆ target := by
    rintro q ⟨⟨z, w⟩, ⟨hz, hw⟩, rfl⟩
    have hwW : w ∈ W := by
      apply hball
      rw [Metric.mem_ball]
      have hw' : dist w 0 ≤ r := by simpa [Metric.mem_closedBall] using hw
      have : ‖w‖ < ε := by
        rw [dist_zero_right] at hw'
        dsimp [r] at *
        linarith
      simpa [dist_zero_right] using this
    exact hVWSum ⟨hVW hz, hwW⟩
  have hK'incl : closure U ⊆ K' := by
    intro z hz
    change z ∈ (fun p : E × E ↦ p.1 + p.2) ''
      (closure U ×ˢ Metric.closedBall (0 : E) r)
    refine ⟨(z, 0), ⟨hz, Metric.mem_closedBall_self (le_of_lt hr)⟩, ?_⟩
    simp
  let δr : ℝ := ε / (2 * (1 + ‖v‖))
  have hδr : 0 < δr := by dsimp [δr]; positivity
  have hTranslate : ∀ h : ℝ, |h| < δr → ∀ z ∈ U, z + h • v ∈ K' := by
    intro h hh z hz
    change z + h • v ∈ (fun p : E × E ↦ p.1 + p.2) ''
      (closure U ×ˢ Metric.closedBall (0 : E) r)
    refine ⟨(z, h • v), ⟨subset_closure hz, ?_⟩, by simp⟩
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    calc
      |h| * ‖v‖ ≤ δr * ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt hh) (norm_nonneg _)
      _ ≤ (ε / (2 * (1 + ‖v‖))) * (1 + ‖v‖) := by
        gcongr
        linarith [norm_nonneg v]
      _ = ε / 2 := by
        field_simp
      _ = r := by rfl
  have hEndpoint : ∃ C : ℝ≥0, ∀ j l,
      HolderBoundOn 0 α C K' (fun z ↦ chartBootstrapMatrix ω₀ φ x z j l) := by
    let e := extChartAt 𝓘(ℝ, E) x
    let f : E → ℝ := φ ∘ e.symm
    have hopen : IsOpen e.target := isOpen_extChartAt_target x
    have hφOn : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) 2 φ Set.univ :=
      contMDiffOn_univ.mpr hφ
    have hf : ContDiffOn ℝ 2 f e.target := by
      have hchart := hφOn.comp (contMDiffOn_extChartAt_symm x) (by
        intro z hz
        simp)
      exact hchart.contDiffOn
    have hfixed : HolderBoundedOnFiniteChartCover cover 2 α {φ} := by
      obtain ⟨C, hC⟩ := (finiteChartHolderGauge_lt_top_iff cover 2 α φ).mp hGauge
      refine ⟨C, ?_⟩
      intro ψ hψ i
      have hψeq : ψ = φ := Set.mem_singleton_iff.mp hψ
      subst ψ
      exact hC i
    have hchartHolder : HolderBoundedInCharts E 2 α {φ} :=
      holderBoundedInCharts_of_fixedCoverBound cover φ hφ (le_of_lt hα₁) hfixed
    obtain ⟨H, hH⟩ := hchartHolder x K' hK'compact hK'target
    have hu : HolderBoundOn 2 α H K' f := by
      simpa [f, e] using hH φ (Set.mem_singleton φ)
    have hMetric (j l : Fin n) :
        ∃ D : ℝ≥0, HolderBoundOn 0 α D K'
          (fun z : E ↦ ω₀.metricInChart x z j l) := by
      apply segmentHolderBoundOn_of_contDiffOn_compact hopen hK'compact hK'target
      · exact ω₀.contDiffOn_metricInChart x j l
      · exact le_of_lt hα₁
    have hHess (j l : Fin n) :
        HolderBoundOn 0 α (4 * H) K' (fun z : E ↦ complexHessian f z j l) := by
      apply segmentHolderBoundOn_hessianEntry hopen hK'target hf hu
        (segmentHessianEntryQ j l) (segmentHessianEntryQ_norm_le j l)
      intro z hz
      exact segmentHessian_eq_entryQ hz j l
    let D (j l : Fin n) : ℝ≥0 := Classical.choose (hMetric j l)
    have hD (j l : Fin n) : HolderBoundOn 0 α (D j l) K'
        (fun z : E ↦ ω₀.metricInChart x z j l) :=
      Classical.choose_spec (hMetric j l)
    let Dsum : ℝ≥0 := ∑ j : Fin n, ∑ l : Fin n, D j l
    have hDle (j l : Fin n) : D j l ≤ Dsum := by
      dsimp [Dsum]
      calc
        D j l ≤ ∑ l' : Fin n, D j l' :=
          Finset.single_le_sum (fun _ _ ↦ by positivity) (Finset.mem_univ l)
        _ ≤ ∑ j' : Fin n, ∑ l' : Fin n, D j' l' :=
          Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity)
            (Finset.mem_univ j)
    refine ⟨Dsum + 4 * H, ?_⟩
    intro j l
    have hMetric' := (hD j l).mono_const (hDle j l)
    have hEntry := segmentHolderBoundOn_zero_add hMetric' (hHess j l)
    simpa [chartBootstrapMatrix, f, e] using hEntry
  obtain ⟨C, hC⟩ := hEndpoint
  let δ : ℝ≥0 := ⟨δr, hδr.le⟩
  have hδ : 0 < δ := NNReal.coe_pos.mpr hδr
  refine ⟨δ, 3 * C, hδ, ?_⟩
  intro h hh s hs j l
  have hh' : |h| < δr := by
    change |h| < (δ : ℝ)
    simpa [δ] using hh
  have hBase : U ⊆ K' := fun z hz => hK'incl (subset_closure hz)
  have hAffine := holderBoundOn_affineTranslatedMatrix (K := U) (K' := K')
    (fun z ↦ chartBootstrapMatrix ω₀ φ x z) hC hBase v δr hδr hTranslate h hh' s hs j l
  simpa only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] using hAffine

end KahlerForm
