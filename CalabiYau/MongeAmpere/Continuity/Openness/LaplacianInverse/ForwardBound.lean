module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.Geometry.Kahler.Poisson

/-!
# Bounded forward Laplacian on smooth cores

The forward estimate is separate from the inverse Schauder estimate. In each chart the Laplacian
is a second-order operator with smooth coefficients, so its order-zero Hölder gauge is bounded by
a constant times the order-two gauge of the input. The integral identity for the Kähler Laplacian
puts its image in the smooth mean-zero core.

For the flat complex one-dimensional torus with constant coefficient metric, the convention is
`Δω = (1/4)(∂²ₓ + ∂²ᵧ)`. On the Fourier mode `cos (2πx)` this gives `-π² cos (2πx)`; its mean is
zero and the upper estimate has the expected second-order scaling. This check fixes the factor
and sign used in the chartwise coefficient calculation.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal Topology
open Set MeasureTheory

namespace KahlerForm

/-- A smooth function on a neighborhood of a compact chart piece has a finite order-zero
Hölder bound there. This supplies the local coefficient bounds used by the forward Laplacian. -/
private theorem holderBoundOn_of_contDiffOn_compact
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
      edist x y ≤ (D : ℝ≥0∞) := by
    have heq : (D : ℝ≥0∞) = Metric.ediam K := ENNReal.coe_toNNReal hdiamTop
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
      (hJ.holderOnWith univ).comp hHolderF (by intro x hx; trivial)
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

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem finiteChartHolderGauge_lt_top_of_smooth_orderZero
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0)
    (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (hα : α ≤ 1) : finiteChartHolderGauge cover 0 α f < ⊤ := by
  classical
  change HasFiniteChartHolderGauge cover 0 α f
  rw [finiteChartHolderGauge_lt_top_iff]
  let B (i : cover.ι) : ℝ≥0 := Classical.choose
    (holderBoundOn_of_contDiffOn_compact
      (isOpen_extChartAt_target (cover.base i))
      (cover.isCompact_piece i) (cover.piece_in_target i)
      (((contMDiffOn_univ.mpr hf).comp
        (contMDiffOn_extChartAt_symm (cover.base i))
        (by intro z hz; simp)).contDiffOn.of_le (by simp)) hα)
  refine ⟨∑ i, B i, ?_⟩
  intro i
  have hBi := Classical.choose_spec
    (holderBoundOn_of_contDiffOn_compact
      (isOpen_extChartAt_target (cover.base i))
      (cover.isCompact_piece i) (cover.piece_in_target i)
      (((contMDiffOn_univ.mpr hf).comp
        (contMDiffOn_extChartAt_symm (cover.base i))
        (by intro z hz; simp)).contDiffOn.of_le (by simp)) hα)
  exact hBi.mono_const (Finset.single_le_sum (s := Finset.univ) (f := B)
    (fun j hj => by positivity) (Finset.mem_univ i))

variable [MeasurableSpace M] [T2Space M] [CompactSpace M] in
/-- The finite-chart gauge bound and mean-zero mapping property for the smooth forward operator.
The codomain value is required to be an actual order-zero smooth core element, not merely a function
with a finite gauge. -/
def HasBoundedForwardLaplacian (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0) : Prop :=
  ∃ C : ℝ≥0, ∀ f : SmoothChartHolderCore cover 2 α,
    finiteChartHolderGauge cover 2 α f.smoothMap < ⊤ ∧
    ∃ g : SmoothChartHolderCore cover 0 α,
      g.smoothMap = ω₁.laplacian f.smoothMap ∧
      (∫ x, g.smoothMap x ∂ω₁.volume = 0) ∧
      finiteChartHolderGauge cover 0 α g.smoothMap < ⊤ ∧
      (finiteChartHolderGauge cover 0 α g.smoothMap).toReal ≤
        (C : ℝ) * (finiteChartHolderGauge cover 2 α f.smoothMap).toReal

private theorem exists_metricInChartInverseEntryHolderBound
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₁ : α < 1) (i : cover.ι) (j k : Fin n) :
    ∃ C : ℝ≥0, HolderBoundOn 0 α C (cover.piece i)
      (fun z => (ω₁.metricInChart (cover.base i) z)⁻¹ j k) := by
  let x := cover.base i
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let U := e.target
  let K := cover.piece i
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z => ω₁.metricInChart x z
  have hG_entry (a b : Fin n) : ContDiffOn ℝ ∞ (fun z => G z a b) U := by
    exact ω₁.contDiffOn_metricInChart x a b
  have hdet : ContDiffOn ℝ ∞ (fun z => (G z).det) U := by
    simp_rw [Matrix.det_apply]
    fun_prop
  have hdet_ne {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U) : (G z).det ≠ 0 := by
    have hpos := (RCLike.pos_iff.mp (ω₁.posDef_metricInChart x hz).det_pos).1
    exact fun h => hpos.ne' (congrArg RCLike.re h)
  have hdetInv : ContDiffOn ℝ ∞ (fun z => ((G z).det)⁻¹) U :=
    hdet.inv (fun z hz => hdet_ne hz)
  have hUpdate (r c s t : Fin n) :
      ContDiffOn ℝ ∞ (fun z => (G z).updateRow r (Pi.single c (1 : ℂ)) s t) U := by
    simp_rw [Matrix.updateRow_apply]
    by_cases hrs : s = r
    · subst s
      simp only [Pi.single_apply]
      exact contDiffOn_const
    · simp only [if_neg hrs]
      exact hG_entry s t
  have hAdj_entry (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun z => (G z).adjugate a b) U := by
    simp_rw [Matrix.adjugate_apply, Matrix.det_apply']
    apply ContDiffOn.sum
    intro σ hσ
    have hp : ContDiffOn ℝ ∞ (fun z =>
        ∏ t, (G z).updateRow b (Pi.single a (1 : ℂ)) (σ t) t) U := by
      exact contDiffOn_prod (t := Finset.univ) (fun t ht => hUpdate b a (σ t) t)
    change ContDiffOn ℝ ∞ (fun z =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ t, (G z).updateRow b (Pi.single a (1 : ℂ)) (σ t) t) U
    exact contDiffOn_const.mul hp
  have hInv_entry (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun z => (G z)⁻¹ a b) U := by
    have hmul : ContDiffOn ℝ ∞
        (fun z => ((G z).det)⁻¹ * (G z).adjugate a b) U :=
      hdetInv.mul (hAdj_entry a b)
    refine hmul.congr ?_
    intro z hz
    rw [Matrix.inv_def]
    simp [Matrix.smul_apply, smul_eq_mul]
  exact holderBoundOn_of_contDiffOn_compact (isOpen_extChartAt_target x)
    (cover.isCompact_piece i) (cover.piece_in_target i) (hInv_entry j k)
    (le_of_lt hα₁)

private theorem holderOnWith_complex_mul_bounded
    {E : Type*} [PseudoMetricSpace E] {K : Set E}
    {α Cf Cg Bf Bg : ℝ≥0} {f g : E → ℂ}
    (hf : HolderOnWith Cf α f K) (hg : HolderOnWith Cg α g K)
    (hfBound : ∀ x ∈ K, ‖f x‖₊ ≤ Bf) (hgBound : ∀ x ∈ K, ‖g x‖₊ ≤ Bg) :
    HolderOnWith (Bf * Cg + Bg * Cf) α (fun x ↦ f x * g x) K := by
  intro x hx y hy
  have hdecomp : f x * g x - f y * g y =
      f x * (g x - g y) + (f x - f y) * g y := by ring
  have hfirst : edist (f x * (g x - g y)) 0 ≤
      (‖f x‖₊ : ENNReal) * edist (g x) (g y) := by
    have h := edist_smul_le (f x) (g x - g y) 0
    have heq : f x * (g x - g y) = f x • (g x - g y) := by simp [smul_eq_mul]
    rw [heq]
    simp [enorm_eq_nnnorm, edist_dist, dist_eq_norm]
  have hsecond : edist ((f x - f y) * g y) 0 ≤
      (‖g y‖₊ : ENNReal) * edist (f x) (f y) := by
    have h := edist_smul_le (g y) (f x - f y) 0
    have heq : (f x - f y) * g y = g y • (f x - f y) := by
      simp [smul_eq_mul, mul_comm]
    rw [heq]
    simp [enorm_eq_nnnorm, edist_dist, dist_eq_norm]
  calc
    edist (f x * g x) (f y * g y) =
        edist (f x * (g x - g y) + (f x - f y) * g y) 0 := by
          rw [← hdecomp]
          simp [edist_dist, dist_eq_norm]
    _ ≤ edist (f x * (g x - g y)) 0 + edist ((f x - f y) * g y) 0 := by
      simpa using edist_add_add_le (f x * (g x - g y)) ((f x - f y) * g y)
        (0 : ℂ) (0 : ℂ)
    _ ≤ (‖f x‖₊ : ENNReal) * edist (g x) (g y) +
        (‖g y‖₊ : ENNReal) * edist (f x) (f y) := add_le_add hfirst hsecond
    _ ≤ (Bf : ENNReal) * ((Cg : ENNReal) * edist x y ^ (α : ℝ)) +
        (Bg : ENNReal) * ((Cf : ENNReal) * edist x y ^ (α : ℝ)) := by
      apply add_le_add
      · have hnorm : (‖f x‖₊ : ENNReal) ≤ (Bf : ENNReal) := by exact_mod_cast hfBound x hx
        exact mul_le_mul hnorm (hg.edist_le hx hy) (by positivity) (by positivity)
      · have hnorm : (‖g y‖₊ : ENNReal) ≤ (Bg : ENNReal) := by exact_mod_cast hgBound y hy
        exact mul_le_mul hnorm (hf.edist_le hx hy) (by positivity) (by positivity)
    _ = ((Bf * Cg + Bg * Cf : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
      simp only [ENNReal.coe_add, ENNReal.coe_mul]
      ring

private theorem holderBoundOn_zero_complex_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    {α C D : ℝ≥0} {f g : E → ℂ}
    (hf : HolderBoundOn 0 α C K f) (hg : HolderBoundOn 0 α D K g) :
    HolderBoundOn 0 α (2 * C * D) K (fun x ↦ f x * g x) := by
  let L := continuousMultilinearCurryFin0 ℝ E ℂ
  have hfBound (x : E) (hx : x ∈ K) : ‖f x‖₊ ≤ C := by
    have h := hf.1 0 le_rfl x hx
    rw [norm_iteratedFDeriv_zero] at h
    have hreal : (‖f x‖₊ : ℝ) ≤ C := by simpa only [coe_nnnorm] using h
    exact NNReal.coe_le_coe.mpr hreal
  have hgBound (x : E) (hx : x ∈ K) : ‖g x‖₊ ≤ D := by
    have h := hg.1 0 le_rfl x hx
    rw [norm_iteratedFDeriv_zero] at h
    have hreal : (‖g x‖₊ : ℝ) ≤ D := by simpa only [coe_nnnorm] using h
    exact NNReal.coe_le_coe.mpr hreal
  have hfHolder : HolderOnWith C α f K := by
    intro x hx y hy
    have h := hf.2 x hx y hy
    rw [iteratedFDeriv_zero_eq_comp] at h
    change edist (L.symm (f x)) (L.symm (f y)) ≤ _ at h
    rw [L.symm.edist_map] at h
    exact h
  have hgHolder : HolderOnWith D α g K := by
    intro x hx y hy
    have h := hg.2 x hx y hy
    rw [iteratedFDeriv_zero_eq_comp] at h
    change edist (L.symm (g x)) (L.symm (g y)) ≤ _ at h
    rw [L.symm.edist_map] at h
    exact h
  have hProduct := holderOnWith_complex_mul_bounded hfHolder hgHolder hfBound hgBound
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    calc
      ‖iteratedFDeriv ℝ 0 (fun x ↦ f x * g x) x‖ = ‖f x * g x‖ := by simp
      _ = ‖f x‖ * ‖g x‖ := norm_mul _ _
      _ ≤ (C : ℝ) * D := by
        exact mul_le_mul (by exact_mod_cast hfBound x hx) (by exact_mod_cast hgBound x hx)
          (norm_nonneg _) (by positivity)
      _ ≤ (2 * C * D : ℝ) := by
        have hC : 0 ≤ (C : ℝ) := NNReal.coe_nonneg C
        have hD : 0 ≤ (D : ℝ) := NNReal.coe_nonneg D
        nlinarith
  · intro x hx y hy
    have h := hProduct x hx y hy
    rw [show C * D + D * C = 2 * C * D by ring] at h
    rw [iteratedFDeriv_zero_eq_comp]
    change edist (L.symm (f x * g x)) (L.symm (f y * g y)) ≤ _
    rw [L.symm.edist_map]
    exact h

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

private theorem holderOnWith_of_holderBoundOn_zero
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

private theorem holderBoundOn_zero_add
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E}
    {α C D : ℝ≥0} {f g : E → F}
    (hf : HolderBoundOn 0 α C K f) (hg : HolderBoundOn 0 α D K g) :
    HolderBoundOn 0 α (C + D) K (fun x ↦ f x + g x) := by
  have hfHolder := holderOnWith_of_holderBoundOn_zero hf
  have hgHolder := holderOnWith_of_holderBoundOn_zero hg
  have hHolder : HolderOnWith (C + D) α (fun x ↦ f x + g x) K := by
    intro x hx y hy
    calc
      edist (f x + g x) (f y + g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
        edist_add_add_le (f x) (g x) (f y) (g y)
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
          (D : ENNReal) * edist x y ^ (α : ℝ) := add_le_add
            (hfHolder x hx y hy) (hgHolder x hx y hy)
      _ = ((C + D : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_add]
        ring
  apply holderBoundOn_zero_from_holderOnWith hHolder
  intro x hx
  have hfx := hf.1 0 le_rfl x hx
  have hgx := hg.1 0 le_rfl x hx
  rw [norm_iteratedFDeriv_zero] at hfx hgx
  calc
    ‖f x + g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ (C : ℝ) + D := add_le_add hfx hgx

private theorem holderBoundOn_zero_sum
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι] [DecidableEq ι]
    {K : Set E} {α : ℝ≥0} (C : ι → ℝ≥0) (f : ι → E → F)
    (hf : ∀ i, HolderBoundOn 0 α (C i) K (f i)) :
    HolderBoundOn 0 α (∑ i, C i) K (fun x ↦ ∑ i, f i x) := by
  classical
  have hsum (s : Finset ι) :
      HolderBoundOn 0 α (∑ i ∈ s, C i) K (fun x ↦ ∑ i ∈ s, f i x) := by
    induction s using Finset.induction_on with
    | empty =>
      constructor
      · intro j hj x hx
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        simp
      · intro x hx y hy
        simp
    | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using holderBoundOn_zero_add (hf i) ih
  simpa using hsum Finset.univ

private theorem holderOnWith_complexHessian_entry_of_orderTwoBound
    {n : ℕ} {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n) :
    HolderOnWith C α (fun z ↦ complexHessian f z i j) K := by
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
    have h := hf.2.dist_le hx hy
    simpa only [dist_eq_norm] using h
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
        _ ≤ ‖Complex.ofReal (a - a')‖ + ‖Complex.ofReal (b - b')‖ +
            ‖Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
              (Complex.ofReal d - Complex.ofReal d'))‖ := by
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
      have hden : (0 : ℝ) < 4 := by norm_num
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

private theorem holderBoundOn_zero_realPart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    {α C : ℝ≥0} {f : E → ℂ}
    (hf : HolderBoundOn 0 α C K f) :
    HolderBoundOn 0 α (‖Complex.reCLM‖₊ * C) K (fun x ↦ Complex.reCLM (f x)) := by
  let L : ℂ →L[ℝ] ℝ := Complex.reCLM
  have hLip : LipschitzWith ‖L‖₊ L := L.lipschitz
  have hComp : HolderOnWith (‖L‖₊ * C ^ (1 : ℝ)) (1 * α)
      (L ∘ f) K := (hLip.holderWith.holderOnWith Set.univ).comp
        (holderOnWith_of_holderBoundOn_zero hf) (by intro x hx; exact Set.mem_univ _)
  have hComp' : HolderOnWith (‖L‖₊ * C) α (L ∘ f) K := by
    simpa [NNReal.rpow_one, one_mul] using hComp
  apply holderBoundOn_zero_from_holderOnWith hComp'
  intro x hx
  have hfx := hf.1 0 le_rfl x hx
  rw [norm_iteratedFDeriv_zero] at hfx
  change ‖L (f x)‖ ≤ (‖L‖₊ * C : ℝ)
  calc
    ‖L (f x)‖ ≤ ‖L‖ * ‖f x‖ := L.le_opNorm (f x)
    _ ≤ (‖L‖₊ : ℝ) * C := by
      exact mul_le_mul_of_nonneg_left hfx (norm_nonneg L)

private theorem complexHessian_norm_le_of_orderTwoBound
    {n : ℕ} {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) :
    ‖complexHessian f z i j‖ ≤ (C : ℝ) := by
  let u : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iu := Complex.I • u
  let iv := Complex.I • v
  let D := iteratedFDeriv ℝ 2 f
  have hu : ‖u‖ = 1 := by simp [u]
  have hv : ‖v‖ = 1 := by simp [v]
  have hiu : ‖iu‖ = 1 := by simp [iu, hu, norm_smul, Complex.norm_I]
  have hiv : ‖iv‖ = 1 := by simp [iv, hv, norm_smul, Complex.norm_I]
  have hform : complexHessian f z i j =
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
  have hEval (w : Fin 2 → EuclideanSpace ℂ (Fin n))
      (hw0 : ‖w 0‖ = 1) (hw1 : ‖w 1‖ = 1) : ‖D z w‖ ≤ ‖D z‖ := by
    calc
      ‖D z w‖ ≤ ‖D z‖ * ∏ k, ‖w k‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖D z‖ := by simp [hw0, hw1]
  have hD : ‖D z‖ ≤ (C : ℝ) := hf.1 2 le_rfl z hz
  have h1 : ‖((D z ![u, v] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![u, v] hu hv).trans hD
  have h2 : ‖((D z ![iu, iv] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![iu, iv] hiu hiv).trans hD
  have h3 : ‖((D z ![u, iv] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![u, iv] hu hiv).trans hD
  have h4 : ‖((D z ![iu, v] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![iu, v] hiu hv).trans hD
  have hCross : ‖Complex.I * ((D z ![u, iv] : ℂ) - D z ![iu, v])‖ ≤
      (C : ℝ) + C := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (norm_sub_le _ _).trans (add_le_add h3 h4)
  have hNumerator : ‖(D z ![u, v] : ℂ) + D z ![iu, iv] +
      Complex.I * (D z ![u, iv] - D z ![iu, v])‖ ≤
      (C : ℝ) + C + ((C : ℝ) + C) := by
    calc
      _ ≤ ‖(D z ![u, v] : ℂ)‖ + ‖(D z ![iu, iv] : ℂ)‖ +
          ‖Complex.I * ((D z ![u, iv] : ℂ) - D z ![iu, v])‖ := by
        calc
          _ ≤ ‖(D z ![u, v] : ℂ) + D z ![iu, iv]‖ +
              ‖Complex.I * ((D z ![u, iv] : ℂ) - D z ![iu, v])‖ := norm_add_le _ _
          _ ≤ _ := by exact add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (C : ℝ) + C + ((C : ℝ) + C) := add_le_add (add_le_add h1 h2) hCross
  rw [hform, norm_div, Complex.norm_ofNat]
  calc
    ‖(D z ![u, v] : ℂ) + D z ![iu, iv] +
        Complex.I * (D z ![u, iv] - D z ![iu, v])‖ / 4 ≤
        ((C : ℝ) + C + ((C : ℝ) + C)) / 4 := div_le_div_of_nonneg_right hNumerator (by norm_num)
    _ = C := by ring

private theorem holderBoundOn_zero_complexHessian_entry_of_orderTwoBound
    {n : ℕ} {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n) :
    HolderBoundOn 0 α C K (fun z ↦ complexHessian f z i j) := by
  apply holderBoundOn_zero_from_holderOnWith
    (holderOnWith_complexHessian_entry_of_orderTwoBound hf hSmooth i j)
  intro z hz
  exact complexHessian_norm_le_of_orderTwoBound hf hSmooth i j hz

private theorem laplacianInChart_holderBoundOn_zero
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₁ : α < 1) (i : cover.ι) :
    ∃ K₀ : ℝ≥0, ∀ (f : M → ℝ),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
      ∀ {C : ℝ≥0}, HolderBoundOn 2 α C (cover.piece i)
        (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) →
      HolderBoundOn 0 α (K₀ * C) (cover.piece i)
        (fun z ↦ ω₁.laplacian f
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) := by
  classical
  let A (r s : Fin n) : ℝ≥0 := Classical.choose
    (exists_metricInChartInverseEntryHolderBound ω₁ cover α hα₁ i r s)
  have hA (r s : Fin n) :
      HolderBoundOn 0 α (A r s) (cover.piece i)
        (fun z => (ω₁.metricInChart (cover.base i) z)⁻¹ r s) := by
    exact Classical.choose_spec
      (exists_metricInChartInverseEntryHolderBound ω₁ cover α hα₁ i r s)
  let K₀ : ℝ≥0 := ∑ r, ∑ s, ‖Complex.reCLM‖₊ * (2 * A r s)
  refine ⟨K₀, ?_⟩
  intro f hf C hC
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  let K := cover.piece i
  let u := f ∘ e.symm
  have huOn : ContDiffOn ℝ ∞ u e.target :=
    ((contMDiffOn_univ.mpr hf).comp (contMDiffOn_extChartAt_symm (cover.base i))
      (by intro z hz; simp)).contDiffOn
  have huAt {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) : ContDiffAt ℝ 2 u z :=
    (huOn.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
      (cover.piece_in_target i hz))).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  let term (r s : Fin n) : EuclideanSpace ℂ (Fin n) → ℝ := fun z =>
    Complex.reCLM ((ω₁.metricInChart (cover.base i) z)⁻¹ r s * complexHessian u z s r)
  let B (r s : Fin n) : ℝ≥0 := ‖Complex.reCLM‖₊ * (2 * A r s * C)
  have hB (r s : Fin n) : HolderBoundOn 0 α (B r s) K (term r s) := by
    have hProd := holderBoundOn_zero_complex_mul (hA r s)
      (holderBoundOn_zero_complexHessian_entry_of_orderTwoBound hC
        (by intro z hz; exact huAt (by simpa [K] using hz)) s r)
    simpa [B, term, u, e, K] using holderBoundOn_zero_realPart hProd
  let Fsum : EuclideanSpace ℂ (Fin n) → ℝ := fun z => ∑ r, ∑ s, term r s z
  have hSumS (r : Fin n) :
      HolderBoundOn 0 α (∑ s, B r s) K (fun z => ∑ s, term r s z) :=
    holderBoundOn_zero_sum (B r) (term r) (hB r)
  have hSum : HolderBoundOn 0 α (∑ r, ∑ s, B r s) K Fsum := by
    simpa [Fsum] using holderBoundOn_zero_sum (fun r => ∑ s, B r s)
      (fun r z => ∑ s, term r s z) hSumS
  have hsumConst : (∑ r, ∑ s, B r s) = K₀ * C := by
    dsimp [B, K₀]
    calc
      (∑ r, ∑ s, ‖Complex.reCLM‖₊ * (2 * A r s * C)) =
          (∑ r, ∑ s, ‖Complex.reCLM‖₊ * (2 * A r s)) * C := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro s hs
            ring
      _ = _ := rfl
  have hEq {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) :
      ω₁.laplacian f (e.symm z) = Fsum z := by
    have hzTarget : z ∈ e.target := cover.piece_in_target i (by simpa [K] using hz)
    have hy : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).source := by
      simpa [e, ← extChartAt_source] using e.map_target hzTarget
    have hLap := ω₁.laplacian_eq_inChart hf (cover.base i) (y := e.symm z) hy
    rw [e.right_inv hzTarget] at hLap
    change ω₁.laplacian f (e.symm z) =
      Complex.reCLM (((ω₁.metricInChart (cover.base i) z)⁻¹ * complexHessian u z).trace) at hLap
    calc
      ω₁.laplacian f (e.symm z) =
          Complex.reCLM (((ω₁.metricInChart (cover.base i) z)⁻¹ * complexHessian u z).trace) := by
            simpa [Complex.reCLM_apply, u] using hLap
      _ = Fsum z := by
        simp [Fsum, term, Matrix.trace, Matrix.mul_apply, Complex.reCLM_apply]
  have hSumScaled : HolderBoundOn 0 α (K₀ * C) K Fsum := by
    rw [← hsumConst]
    exact hSum
  refine ⟨?_, ?_⟩
  · intro q hq z hz
    have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
    subst q
    rw [norm_iteratedFDeriv_zero, hEq (by simpa [K] using hz)]
    have h := hSumScaled.1 0 le_rfl z (by simpa [K] using hz)
    rw [norm_iteratedFDeriv_zero] at h
    exact h
  · intro z hz w hw
    have hjet (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ K) :
        iteratedFDeriv ℝ 0 (fun z => ω₁.laplacian f (e.symm z)) x =
          iteratedFDeriv ℝ 0 Fsum x := by
      rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
      change (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).symm
          (ω₁.laplacian f (e.symm x)) =
        (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ).symm (Fsum x)
      rw [hEq hx]
    rw [hjet z (by simpa [K] using hz), hjet w (by simpa [K] using hw)]
    exact hSumScaled.2 z (by simpa [K] using hz) w (by simpa [K] using hw)

private theorem forward_laplacian_gauge_toReal_bound
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ f : SmoothChartHolderCore cover 2 α,
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian f.smoothMap)).toReal ≤
        (C : ℝ) * (finiteChartHolderGauge cover 2 α f.smoothMap).toReal := by
  classical
  let Ki (i : cover.ι) : ℝ≥0 :=
    Classical.choose (laplacianInChart_holderBoundOn_zero ω₁ cover α hα₁ i)
  have hKi (i : cover.ι) : ∀ (f : M → ℝ),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
      ∀ {C : ℝ≥0}, HolderBoundOn 2 α C (cover.piece i)
        (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) →
      HolderBoundOn 0 α (Ki i * C) (cover.piece i)
        (fun z ↦ ω₁.laplacian f
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) := by
    exact Classical.choose_spec (laplacianInChart_holderBoundOn_zero ω₁ cover α hα₁ i)
  let Ctotal : ℝ≥0 := ∑ i, 2 * Ki i
  refine ⟨Ctotal, ?_⟩
  intro f
  have hfGauge : finiteChartHolderGauge cover 2 α f.smoothMap < ⊤ :=
    smoothChartHolderGauge_finite cover 2 α hα₁ f
  let Cinput : ℝ≥0 := (finiteChartHolderGauge cover 2 α f.smoothMap).toNNReal
  have hGaugeEq : (Cinput : ℝ≥0∞) = finiteChartHolderGauge cover 2 α f.smoothMap :=
    ENNReal.coe_toNNReal (ne_of_lt hfGauge)
  have hChartInput (i : cover.ι) : HolderBoundOn 2 α Cinput (cover.piece i)
      (f.smoothMap ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
    have hi : CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α (cover.piece i)
        (f.smoothMap ∘ e.symm) ≤ (Cinput : ℝ≥0∞) := by
      calc
        _ ≤ finiteChartHolderGauge cover 2 α f.smoothMap := by
          unfold finiteChartHolderGauge
          exact le_iSup
            (fun j : cover.ι => CalabiYau.Schauder.eContDiffHolderGaugeOn 2 α
              (cover.piece j) (f.smoothMap ∘
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).symm)) i
        _ = (Cinput : ℝ≥0∞) := hGaugeEq.symm
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      exact CalabiYau.Schauder.spatialJet_norm_le hi hj (x := z) hz
    · exact HolderWith.restrict_iff.mp
        (CalabiYau.Schauder.topSpatialJet_holderWith_restrict hi)
  have hLocal (i : cover.ι) : HolderBoundOn 0 α (Ki i * Cinput)
      (cover.piece i)
      (fun z ↦ ω₁.laplacian f.smoothMap
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) :=
    hKi i f.smoothMap f.smoothMap.contMDiff (hChartInput i)
  have hLocalGauge (i : cover.ι) :
      CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α (cover.piece i)
        (fun z ↦ ω₁.laplacian f.smoothMap
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) ≤
        (2 * Ki i * Cinput : ℝ≥0∞) := by
    have hspatial : ∀ j ≤ 0, ∀ z ∈ cover.piece i,
        ‖iteratedFDeriv ℝ j (fun z ↦ ω₁.laplacian f.smoothMap
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) z‖ ≤
          (Ki i * Cinput : ℝ) := by
      intro j hj z hz
      exact (hLocal i).1 j hj z hz
    have hHolder : HolderWith (Ki i * Cinput) α
        ((cover.piece i).domRestrict
          (iteratedFDeriv ℝ 0 (fun z ↦ ω₁.laplacian f.smoothMap
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)))) :=
      HolderWith.restrict_iff.mpr (hLocal i).2
    have hGauge := CalabiYau.Schauder.eContDiffHolderGaugeOn_le
      (fun _ => Ki i * Cinput) (Ki i * Cinput) hspatial hHolder
    have hGauge' : CalabiYau.Schauder.eContDiffHolderGaugeOn 0 α (cover.piece i)
        (fun z ↦ ω₁.laplacian f.smoothMap
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)) ≤
        (Ki i * Cinput : ℝ≥0∞) + (Ki i * Cinput : ℝ≥0∞) := by
      simpa [Finset.sum_range_succ] using hGauge
    calc
      _ ≤ (Ki i * Cinput : ℝ≥0∞) + (Ki i * Cinput : ℝ≥0∞) := hGauge'
      _ = (2 * Ki i * Cinput : ℝ≥0∞) := by ring
  have hOutGauge : finiteChartHolderGauge cover 0 α (ω₁.laplacian f.smoothMap) ≤
      (Ctotal * Cinput : ℝ≥0∞) := by
    unfold finiteChartHolderGauge
    apply iSup_le
    intro i
    calc
      _ ≤ (2 * Ki i * Cinput : ℝ≥0∞) := hLocalGauge i
      _ ≤ (Ctotal * Cinput : ℝ≥0∞) := by
        have hCoeff : 2 * Ki i ≤ Ctotal := by
          dsimp [Ctotal]
          exact Finset.single_le_sum (f := fun j : cover.ι => 2 * Ki j)
            (fun j hj => by positivity) (Finset.mem_univ i)
        exact_mod_cast (mul_le_mul_of_nonneg_right hCoeff (by positivity : 0 ≤ Cinput))
  have hOutFinite : finiteChartHolderGauge cover 0 α (ω₁.laplacian f.smoothMap) < ⊤ :=
    lt_of_le_of_lt hOutGauge ENNReal.coe_lt_top
  have hToReal := ENNReal.toReal_mono ENNReal.coe_ne_top hOutGauge
  have hInputReal :
      (finiteChartHolderGauge cover 2 α f.smoothMap).toReal = (Cinput : ℝ) := by
    rw [← hGaugeEq]
    simp
  rw [hInputReal]
  simpa using hToReal

private theorem forward_laplacian_gauge_estimate
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₁ : α < 1) :
    ∃ C : ℝ≥0, ∀ f : SmoothChartHolderCore cover 2 α,
      finiteChartHolderGauge cover 2 α f.smoothMap < ⊤ ∧
      finiteChartHolderGauge cover 0 α (ω₁.laplacian f.smoothMap) < ⊤ ∧
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian f.smoothMap)).toReal ≤
        (C : ℝ) * (finiteChartHolderGauge cover 2 α f.smoothMap).toReal := by
  obtain ⟨C, hC⟩ := forward_laplacian_gauge_toReal_bound ω₁ cover α hα₁
  refine ⟨C, ?_⟩
  intro f
  refine ⟨?_, ?_, hC f⟩
  · exact smoothChartHolderGauge_finite cover 2 α hα₁ f
  · exact finiteChartHolderGauge_lt_top_of_smooth_orderZero cover α
      (ω₁.laplacian f.smoothMap) (ω₁.contMDiff_laplacian f.smoothMap.contMDiff)
      (le_of_lt hα₁)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
private theorem forward_laplacian_smoothCoreOutput
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₁ : α < 1) (f : SmoothChartHolderCore cover 2 α) :
    ∃ g : SmoothChartHolderCore cover 0 α,
      g.smoothMap = ω₁.laplacian f.smoothMap ∧
      (∫ x, g.smoothMap x ∂ω₁.volume = 0) ∧
      finiteChartHolderGauge cover 0 α g.smoothMap < ⊤ := by
  let g : SmoothChartHolderCore cover 0 α :=
    ⟨⟨ω₁.laplacian f.smoothMap, ω₁.contMDiff_laplacian f.smoothMap.contMDiff⟩⟩
  refine ⟨g, rfl, ω₁.integral_laplacian f.smoothMap.contMDiff, ?_⟩
  exact finiteChartHolderGauge_lt_top_of_smooth_orderZero cover α g.smoothMap
    g.smoothMap.contMDiff (le_of_lt hα₁)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
/-- The smooth Laplacian has a bounded order-two-to-order-zero finite-chart gauge, and its
integral vanishes. In particular it maps a smooth mean-zero core into the smooth mean-zero target
core. -/
theorem exists_forward_laplacian_holder_bound
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₁ : α < 1) :
    HasBoundedForwardLaplacian ω₁ cover α := by
  obtain ⟨C, hC⟩ := forward_laplacian_gauge_estimate ω₁ cover α hα₁
  refine ⟨C, ?_⟩
  intro f
  obtain ⟨hInput, hOutput, hBound⟩ := hC f
  obtain ⟨g, hg, hIntegral, hOutputSmooth⟩ :=
    forward_laplacian_smoothCoreOutput ω₁ cover α hα₁ f
  refine ⟨hInput, g, hg, hIntegral, ?_, ?_⟩
  · exact hOutputSmooth
  · simpa [hg] using hBound

end KahlerForm
