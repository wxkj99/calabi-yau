-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Density.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.WeakDerivative.Closedness
public import CalabiYau.Analysis.Sobolev.Tools.FrechetKolmogorov
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Rellich.Basic
public import CalabiYau.Analysis.Sobolev.Tools.Mollification.Kernel
public import CalabiYau.Analysis.Sobolev.Tools.Mollification.WeakDerivative

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below.

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal Convolution Pointwise

namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem tsupport_convolution_subset_thickening
    {f η : E → ℝ} {δ : ℝ}
    (hη_support : Function.support η ⊆ Metric.closedBall (0 : E) δ) :
    tsupport (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) ⊆
      Metric.cthickening δ (tsupport f) := by
  classical
  have hsupp_convergence :
      Function.support (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) ⊆
        Function.support f + Function.support η :=
    support_convolution_subset (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
  have hsupp_f : Function.support f ⊆ tsupport f := subset_tsupport f
  have hsum_subset :
      Function.support f + Function.support η ⊆
        tsupport f + Metric.closedBall (0 : E) δ :=
    Set.add_subset_add hsupp_f hη_support
  have hadd_subset :
      tsupport f + Metric.closedBall (0 : E) δ ⊆
        Metric.cthickening δ (tsupport f) := by
    intro x hx
    rcases Set.mem_add.mp hx with ⟨a, ha, b, hb, rfl⟩
    refine Metric.mem_cthickening_of_dist_le (x := a + b) (y := a) (δ := δ)
      (tsupport f) ha ?_
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    rw [dist_eq_norm]
    have heq : a + b - a = b := by abel
    rw [heq]
    exact hb
  have hclosed : IsClosed (Metric.cthickening δ (tsupport f)) :=
    Metric.isClosed_cthickening
  exact closure_minimal (hsupp_convergence.trans (hsum_subset.trans hadd_subset)) hclosed

theorem tsupport_convolution_mollifierEps_subset_thickening
    {f : E → ℝ}
    {ε : ℝ} (hε : 0 < ε) :
    tsupport (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps (d := d) hε) ⊆
      Metric.cthickening ε (tsupport f) :=
  tsupport_convolution_subset_thickening
    (mollifierEps_support_subset_closedBall_eps hε)

theorem contDiff_convolution_mollifierEps
    {u : E → ℝ} (hu_local : LocallyIntegrable u volume)
    {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞)
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps (d := d) hε) := by
  have h1 : HasCompactSupport (mollifierEps (d := d) hε) :=
    mollifierEps_compactSupport hε
  exact h1.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hu_local
    (mollifierEps_smooth hε)

theorem hasCompactSupport_convolution_mollifierEps
    {u : E → ℝ} (hu_compact : HasCompactSupport u)
    {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps (d := d) hε) := by
  classical
  have h_support_subset :
      tsupport (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps (d := d) hε) ⊆
        Metric.cthickening ε (tsupport u) :=
    tsupport_convolution_subset_thickening
      (mollifierEps_support_subset_closedBall_eps hε)
  refine HasCompactSupport.intro' (K := Metric.cthickening ε (tsupport u))
    (hu_compact.isCompact.cthickening (r := ε))
    Metric.isClosed_cthickening
    ?_
  intro x hx
  by_contra h_nonzero
  exact hx (h_support_subset (subset_tsupport _ (Function.mem_support.mpr h_nonzero)))

theorem exists_smooth_cutoff_with_neighborhood
    {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ (δ : ℝ) (η : E → ℝ),
      0 < δ ∧
      Metric.cthickening δ K ⊆ Ω ∧
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      HasCompactSupport η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ Metric.cthickening δ K, η x = 1) ∧
      tsupport η ⊆ Ω := by
  obtain ⟨δ, hδ_pos, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hδ_half_pos : 0 < δ / 2 := by linarith
  have hδ_half_lt : δ / 2 < δ := by linarith
  have hcthick_half_subset : Metric.cthickening (δ / 2) K ⊆ Ω := by
    refine subset_trans ?_ hδΩ
    exact Metric.cthickening_mono (by linarith) K
  have h_subset : Metric.cthickening (δ / 2) K ⊆ Metric.thickening δ K :=
    Metric.cthickening_subset_thickening' hδ_pos hδ_half_lt K
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ E) (s := Metric.thickening δ K)
      (t := Metric.cthickening (δ / 2) K)
      isOpen_thickening Metric.isClosed_cthickening
      h_subset with
    ⟨η, hη_smooth, hη_range, hη_support, hη_one_iff⟩
  refine ⟨δ / 2, η, hδ_half_pos, hcthick_half_subset,
    contMDiff_iff_contDiff.mp hη_smooth, ?_, hη_range, ?_, ?_⟩
  · refine HasCompactSupport.intro' (K := Metric.cthickening δ K)
      (hK.cthickening (r := δ)) Metric.isClosed_cthickening ?_
    intro x hx
    have hxt : x ∉ tsupport η := by
      intro hxt
      have hx_closure : x ∈ closure (Metric.thickening δ K) := by
        rw [tsupport, hη_support] at hxt
        exact hxt
      exact hx ((Metric.closure_thickening_subset_cthickening δ K) hx_closure)
    exact image_eq_zero_of_notMem_tsupport hxt
  · intro x hx
    exact (hη_one_iff x).1 hx
  · rw [tsupport, hη_support]
    exact (Metric.closure_thickening_subset_cthickening δ K).trans hδΩ

theorem fderiv_cutoff_apply_zero_on_cthickening
    {K : Set E} {δ : ℝ} (hδ : 0 < δ)
    {η : E → ℝ}
    (hη_one : ∀ x ∈ Metric.cthickening δ K, η x = 1)
    {x : E} (hx : x ∈ K) (i : Fin d) :
    (fderiv ℝ η x) (EuclideanSpace.single i 1) = 0 := by
  have hη_eq : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x (by linarith : 0 < δ / 2)) ?_
    intro y hy
    rw [Metric.mem_ball] at hy
    have hy_closed : y ∈ Metric.closedBall x (δ / 2) := by
      rw [Metric.mem_closedBall]
      exact le_of_lt hy
    have hy_cthick_half : y ∈ Metric.cthickening (δ / 2) K :=
      Metric.closedBall_subset_cthickening hx (δ / 2) hy_closed
    have hy_cthick : y ∈ Metric.cthickening δ K :=
      Metric.cthickening_mono (by linarith : δ / 2 ≤ δ) K hy_cthick_half
    exact hη_one y hy_cthick
  rw [Filter.EventuallyEq.fderiv_eq hη_eq]
  simp

theorem chosenWeakPartialOrZero_ae_zero_on_sdiff_tsupport
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ_open : IsOpen Ω)
    {u : E → ℝ} (hu : Sobolev.Euclidean.MemW1p p u Ω)
    (i : Fin d) :
    chosenWeakPartialOrZero p i u Ω =ᵐ[volume.restrict (Ω \ tsupport u)]
      (fun _ : E => (0 : ℝ)) := by
  classical
  set V : Set E := Ω \ tsupport u with hV_def
  have hV_open : IsOpen V := hΩ_open.sdiff (isClosed_tsupport _)
  have hu_ae_zero_V : u =ᵐ[volume.restrict V] (fun _ : E => (0 : ℝ)) := by
    refine (ae_restrict_iff' hV_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hx_notin : x ∉ tsupport u := hx.2
    exact image_eq_zero_of_notMem_tsupport hx_notin
  have hu_V : Sobolev.Euclidean.MemW1p p u V := by
    refine ⟨?_, ?_⟩
    · refine hu.1.mono_measure ?_
      exact Measure.restrict_mono_set volume (Set.sdiff_subset : V ⊆ Ω)
    · intro j
      obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 j
      refine ⟨g, ?_, ?_⟩
      · exact hg_memLp.mono_measure (Measure.restrict_mono_set volume (Set.sdiff_subset : V ⊆ Ω))
      · exact Sobolev.Euclidean.HasWeakPartialDeriv.restrict (Set.sdiff_subset : V ⊆ Ω) hg_weak
  have h_partial_V : Sobolev.Euclidean.HasWeakPartialDeriv i (chosenWeakPartialOrZero p i u V) u V :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hu_V i
  have h_partial_Ω : Sobolev.Euclidean.HasWeakPartialDeriv i (chosenWeakPartialOrZero p i u Ω) u Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hu i
  have h_partial_Ω_V : Sobolev.Euclidean.HasWeakPartialDeriv i (chosenWeakPartialOrZero p i u Ω) u V :=
    Sobolev.Euclidean.HasWeakPartialDeriv.restrict (Set.sdiff_subset : V ⊆ Ω) h_partial_Ω
  have h_chosen_V_zero : chosenWeakPartialOrZero p i u V
      =ᵐ[volume.restrict V] (fun _ : E => (0 : ℝ)) :=
    chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := d) hp hV_open hu_ae_zero_V i
  have hg_lp_Ω : MemLp (chosenWeakPartialOrZero p i u Ω) p (volume.restrict Ω) :=
    chosenWeakPartialOrZero_memLp_of_mem hu i
  have hg_lp_Ω_V : MemLp (chosenWeakPartialOrZero p i u Ω) p (volume.restrict V) :=
    hg_lp_Ω.mono_measure (Measure.restrict_mono_set volume (Set.sdiff_subset : V ⊆ Ω))
  have hg_local_Ω_V : LocallyIntegrable (chosenWeakPartialOrZero p i u Ω) (volume.restrict V) :=
    hg_lp_Ω_V.locallyIntegrable hp
  have hgV_lp : MemLp (chosenWeakPartialOrZero p i u V) p (volume.restrict V) :=
    chosenWeakPartialOrZero_memLp_of_mem hu_V i
  have hgV_local : LocallyIntegrable (chosenWeakPartialOrZero p i u V) (volume.restrict V) :=
    hgV_lp.locallyIntegrable hp
  have h_unique : chosenWeakPartialOrZero p i u Ω
      =ᵐ[volume.restrict V] chosenWeakPartialOrZero p i u V :=
    Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hV_open h_partial_Ω_V h_partial_V
      hg_local_Ω_V hgV_local
  exact h_unique.trans h_chosen_V_zero

theorem hasWeakPartialDeriv_indicator_chosenWeakPartial_univ
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ_open : IsOpen Ω)
    {u : E → ℝ} (hu_W : Sobolev.Euclidean.MemW1p p u Ω)
    (hu_compact : HasCompactSupport u) (hu_support : tsupport u ⊆ Ω)
    (i : Fin d) :
    Sobolev.Euclidean.HasWeakPartialDeriv i (Ω.indicator (chosenWeakPartialOrZero p i u Ω)) u
      Set.univ := by
  classical
  intro ψ hψ_smooth hψ_compact _hψ_sub
  set g : E → ℝ := chosenWeakPartialOrZero p i u Ω with hg_def
  obtain ⟨δ, χ, hδ_pos, _hδΩ, hχ_smooth, hχ_compact, _hχ_range, hχ_one,
    hχ_sub⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := d)
      hu_compact.isCompact hΩ_open hu_support
  let ei : E := EuclideanSpace.single i (1 : ℝ)
  have hχψ_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * ψ x) := hχ_smooth.mul hψ_smooth
  have hχψ_compact : HasCompactSupport (fun x => χ x * ψ x) := hψ_compact.mul_left
  have hχψ_sub : tsupport (fun x => χ x * ψ x) ⊆ Ω :=
    (tsupport_smul_subset_left χ ψ).trans hχ_sub
  have h_partial_Ω : Sobolev.Euclidean.HasWeakPartialDeriv i g u Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hu_W i
  have hIBP_Ω :
      ∫ x in Ω, u x * (fderiv ℝ (fun y => χ y * ψ y) x) ei =
        -∫ x in Ω, g x * (χ x * ψ x) :=
    h_partial_Ω _ hχψ_smooth hχψ_compact hχψ_sub
  have hχ_diff : Differentiable ℝ χ := hχ_smooth.differentiable (by simp)
  have hψ_diff : Differentiable ℝ ψ := hψ_smooth.differentiable (by simp)
  have h_fderiv_χψ : ∀ x : E,
      (fderiv ℝ (fun y => χ y * ψ y) x) ei =
        χ x * (fderiv ℝ ψ x) ei + ψ x * (fderiv ℝ χ x) ei := by
    intro x
    rw [fderiv_fun_mul hχ_diff.differentiableAt hψ_diff.differentiableAt]
    simp [ei, add_apply, smul_apply, smul_eq_mul]
  have h_u_ψ_dχ_zero : ∀ x : E, u x * ψ x * (fderiv ℝ χ x) ei = 0 := by
    intro x
    by_cases hx : x ∈ tsupport u
    · have hdχ_zero : (fderiv ℝ χ x) ei = 0 :=
        fderiv_cutoff_apply_zero_on_cthickening (d := d) hδ_pos hχ_one hx i
      simp [hdχ_zero]
    · have hux : u x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hux]
  have h_u_χ_eq_u : ∀ x : E, u x * χ x = u x := by
    intro x
    by_cases hx : x ∈ tsupport u
    · have hχx : χ x = 1 := hχ_one x (Metric.self_subset_cthickening (tsupport u) hx)
      rw [hχx, mul_one]
    · have hux : u x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hux, zero_mul]
  have h_lhs_pt : ∀ x : E,
      u x * (fderiv ℝ (fun y => χ y * ψ y) x) ei = u x * (fderiv ℝ ψ x) ei := by
    intro x
    rw [h_fderiv_χψ]
    rw [mul_add]
    have : u x * (ψ x * (fderiv ℝ χ x) ei) = u x * ψ x * (fderiv ℝ χ x) ei := by ring
    rw [this, h_u_ψ_dχ_zero, add_zero]
    have huχx : u x * χ x = u x := h_u_χ_eq_u x
    have : u x * (χ x * (fderiv ℝ ψ x) ei) = u x * χ x * (fderiv ℝ ψ x) ei := by ring
    rw [this, huχx]
  have hLHS_eq :
      ∫ x in Ω, u x * (fderiv ℝ (fun y => χ y * ψ y) x) ei =
        ∫ x in Ω, u x * (fderiv ℝ ψ x) ei :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => h_lhs_pt x)
  have h_u_zero_outside_Ω : ∀ x : E, x ∉ Ω → u x * (fderiv ℝ ψ x) ei = 0 := by
    intro x hx
    have hux : u x = 0 :=
      Sobolev.Euclidean.zero_outside_of_tsupport_subset (Ω := Ω) hu_support hx
    rw [hux, zero_mul]
  have hLHS_E :
      ∫ x in Ω, u x * (fderiv ℝ ψ x) ei = ∫ x : E, u x * (fderiv ℝ ψ x) ei :=
    setIntegral_eq_integral_of_forall_compl_eq_zero h_u_zero_outside_Ω
  have h_g_ae_zero : g =ᵐ[volume.restrict (Ω \ tsupport u)] (fun _ : E => (0 : ℝ)) :=
    chosenWeakPartialOrZero_ae_zero_on_sdiff_tsupport (d := d) hp hΩ_open hu_W i
  have h_χ_on_tsupport : ∀ x ∈ tsupport u, χ x = 1 := fun x hx =>
    hχ_one x (Metric.self_subset_cthickening (tsupport u) hx)
  have h_g_χψ_eq_g_ψ_ae : (fun x : E => g x * (χ x * ψ x)) =ᵐ[volume.restrict Ω]
      (fun x : E => g x * ψ x) := by
    have hsub : tsupport u ⊆ Ω := hu_support
    have hΩ_eq_union : Ω = tsupport u ∪ (Ω \ tsupport u) := by
      ext x
      constructor
      · intro hx
        by_cases hxs : x ∈ tsupport u
        · left; exact hxs
        · right; exact ⟨hx, hxs⟩
      · rintro (hx | hx)
        · exact hsub hx
        · exact hx.1
    have h_ae_tsupport : (fun x : E => g x * (χ x * ψ x))
        =ᵐ[volume.restrict (tsupport u)] (fun x : E => g x * ψ x) := by
      refine (ae_restrict_iff' (isClosed_tsupport _).measurableSet).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      have hχx : χ x = 1 := h_χ_on_tsupport x hx
      simp [hχx]
    have h_ae_diff : (fun x : E => g x * (χ x * ψ x))
        =ᵐ[volume.restrict (Ω \ tsupport u)] (fun x : E => g x * ψ x) := by
      filter_upwards [h_g_ae_zero] with x hx
      rw [hx]; ring
    rw [show volume.restrict Ω = volume.restrict (tsupport u ∪ (Ω \ tsupport u)) by
      rw [← hΩ_eq_union]]
    have hP : ∀ x : E, g x * (χ x * ψ x) = g x * ψ x ∨
        ¬ (g x * (χ x * ψ x) = g x * ψ x) := fun x => Classical.em _
    have := ae_restrict_union_iff (s := tsupport u) (t := Ω \ tsupport u)
      (μ := (volume : Measure E))
      (p := fun x => g x * (χ x * ψ x) = g x * ψ x)
    exact this.mpr ⟨h_ae_tsupport, h_ae_diff⟩
  have hRHS_eq :
      ∫ x in Ω, g x * (χ x * ψ x) = ∫ x in Ω, g x * ψ x :=
    integral_congr_ae h_g_χψ_eq_g_ψ_ae
  have h_indicator_zero_outside_Ω : ∀ x : E, x ∉ Ω →
      Ω.indicator g x * ψ x = 0 := by
    intro x hx
    rw [Set.indicator_of_notMem hx]
    ring
  have h_indicator_eq_g_on_Ω : ∀ x ∈ Ω,
      Ω.indicator g x * ψ x = g x * ψ x := by
    intro x hx
    rw [Set.indicator_of_mem hx]
  have hRHS_E :
      ∫ x in Ω, g x * ψ x = ∫ x : E, Ω.indicator g x * ψ x := by
    have h_ext : ∫ x : E, Ω.indicator g x * ψ x = ∫ x in Ω, Ω.indicator g x * ψ x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        h_indicator_zero_outside_Ω).symm
    rw [h_ext]
    refine integral_congr_ae ?_
    refine (ae_restrict_iff' hΩ_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact (h_indicator_eq_g_on_Ω x hx).symm
  change ∫ x in (Set.univ : Set E), u x * (fderiv ℝ ψ x) (EuclideanSpace.single i 1) =
    -∫ x in (Set.univ : Set E), Ω.indicator g x * ψ x
  rw [setIntegral_univ, setIntegral_univ]
  calc
    ∫ x : E, u x * (fderiv ℝ ψ x) (EuclideanSpace.single i 1)
        = ∫ x in Ω, u x * (fderiv ℝ ψ x) ei := hLHS_E.symm
    _ = ∫ x in Ω, u x * (fderiv ℝ (fun y => χ y * ψ y) x) ei := hLHS_eq.symm
    _ = -∫ x in Ω, g x * (χ x * ψ x) := hIBP_Ω
    _ = -∫ x in Ω, g x * ψ x := by rw [hRHS_eq]
    _ = -∫ x : E, Ω.indicator g x * ψ x := by rw [hRHS_E]

theorem MemWkp.extend_zero {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω V : Set E} (hΩ : IsOpen Ω) (hV : IsOpen V) (hΩV : Ω ⊆ V)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω)
    (hu_support : tsupport u ⊆ Ω) (hu_compactSupport : HasCompactSupport u) :
    MemWkp (d := d) k p u V := by
  induction k generalizing u with
  | zero =>
      rw [MemWkp_zero] at hu ⊢
      have h_indicator_mem : MemLp (Ω.indicator u) p (volume.restrict V) := by
        rw [memLp_indicator_iff_restrict hΩ.measurableSet]
        rw [Measure.restrict_restrict_of_subset hΩV]
        exact hu
      have hu_eq_indicator_ae : u =ᵐ[volume.restrict V] Ω.indicator u := by
        refine (ae_restrict_iff' hV.measurableSet).mpr ?_
        refine Filter.Eventually.of_forall fun x (hx : x ∈ V) => ?_
        by_cases hxΩ : x ∈ Ω
        · rw [Set.indicator_of_mem hxΩ]
        · have hx_not_support : x ∉ tsupport u := fun h => hxΩ (hu_support h)
          rw [image_eq_zero_of_notMem_tsupport hx_not_support, Set.indicator_of_notMem hxΩ]
      exact (memLp_congr_ae hu_eq_indicator_ae).mpr h_indicator_mem
  | succ k ih =>
      rw [MemWkp_succ] at hu ⊢
      rcases hu with ⟨hu_W_Ω, hwp_Ω⟩
      have hu_memLp_V : MemLp u p (volume.restrict V) := by
        have h_indicator_mem : MemLp (Ω.indicator u) p (volume.restrict V) := by
          rw [memLp_indicator_iff_restrict hΩ.measurableSet]
          rw [Measure.restrict_restrict_of_subset hΩV]
          exact hu_W_Ω.1
        have hu_eq_indicator_ae : u =ᵐ[volume.restrict V] Ω.indicator u := by
          refine (ae_restrict_iff' hV.measurableSet).mpr ?_
          refine Filter.Eventually.of_forall fun x (hx : x ∈ V) => ?_
          by_cases hxΩ : x ∈ Ω
          · rw [Set.indicator_of_mem hxΩ]
          · have hx_not_support : x ∉ tsupport u := fun h => hxΩ (hu_support h)
            rw [image_eq_zero_of_notMem_tsupport hx_not_support, Set.indicator_of_notMem hxΩ]
        exact (memLp_congr_ae hu_eq_indicator_ae).mpr h_indicator_mem
      have hΩ_meas : MeasurableSet Ω := hΩ.measurableSet
      have h_weak_partials_V : ∀ i : Fin d, ∃ g : E → ℝ,
          MemLp g p (volume.restrict V) ∧ Sobolev.Euclidean.HasWeakPartialDeriv i g u V := by
        intro i
        have h_univ : Sobolev.Euclidean.HasWeakPartialDeriv i
            (Ω.indicator (chosenWeakPartialOrZero p i u Ω)) u Set.univ :=
          hasWeakPartialDeriv_indicator_chosenWeakPartial_univ hp hΩ hu_W_Ω
            hu_compactSupport hu_support i
        have h_V : Sobolev.Euclidean.HasWeakPartialDeriv i
            (Ω.indicator (chosenWeakPartialOrZero p i u Ω)) u V :=
          Sobolev.Euclidean.HasWeakPartialDeriv.restrict (Set.subset_univ V) h_univ
        have h_memLp : MemLp (Ω.indicator (chosenWeakPartialOrZero p i u Ω)) p
            (volume.restrict V) := by
          rw [memLp_indicator_iff_restrict hΩ_meas]
          rw [Measure.restrict_restrict_of_subset hΩV]
          exact chosenWeakPartialOrZero_memLp_of_mem hu_W_Ω i
        exact ⟨Ω.indicator (chosenWeakPartialOrZero p i u Ω), h_memLp, h_V⟩
      have hu_W_V : Sobolev.Euclidean.MemW1p p u V :=
        ⟨hu_memLp_V, h_weak_partials_V⟩
      have hwp_V : ∀ i : Fin d, MemWkp (d := d) k p (chosenWeakPartialOrZero p i u V) V := by
        intro i
        set g_Ω := chosenWeakPartialOrZero p i u Ω with hg_Ω_def
        set g_V := chosenWeakPartialOrZero p i u V with hg_V_def
        let g_mod : E → ℝ := (tsupport u).indicator g_Ω
        have h_tsupp_u_closed : IsClosed (tsupport u) := isClosed_tsupport _
        have h_tsupp_u_compact : IsCompact (tsupport u) := hu_compactSupport
        have h_support_g_mod_subset : Function.support g_mod ⊆ tsupport u := by
          intro x hx
          have hx_nonzero : g_mod x ≠ 0 := hx
          dsimp [g_mod] at hx_nonzero
          by_contra hx_not
          have : g_mod x = 0 := Set.indicator_of_notMem hx_not _
          exact hx_nonzero this
        have h_tsupp_g_mod_subset : tsupport g_mod ⊆ tsupport u :=
          (closure_mono h_support_g_mod_subset).trans
            (by rw [h_tsupp_u_closed.closure_eq])
        have hg_mod_compactSupport : HasCompactSupport g_mod :=
          h_tsupp_u_compact.of_isClosed_subset (isClosed_tsupport _) h_tsupp_g_mod_subset
        have hg_mod_tsupport_subset_Ω : tsupport g_mod ⊆ Ω :=
          h_tsupp_g_mod_subset.trans hu_support
        have hg_mod_ae_eq_g_Ω : g_mod =ᵐ[volume.restrict Ω] g_Ω := by
          have h_meas_tsupp_u : MeasurableSet (tsupport u) := h_tsupp_u_closed.measurableSet
          have h_ae_tsupport : g_mod =ᵐ[volume.restrict (tsupport u)] g_Ω := by
            refine (ae_restrict_iff' h_meas_tsupp_u).mpr ?_
            refine Filter.Eventually.of_forall ?_
            intro x hx
            dsimp [g_mod]
            rw [Set.indicator_of_mem hx]
          have h_ae_diff : g_mod =ᵐ[volume.restrict (Ω \ tsupport u)] g_Ω := by
            have h_g_Ω_zero : g_Ω =ᵐ[volume.restrict (Ω \ tsupport u)]
                (fun _ : E => (0 : ℝ)) :=
              chosenWeakPartialOrZero_ae_zero_on_sdiff_tsupport hp hΩ hu_W_Ω i
            have h_g_mod_zero : g_mod =ᵐ[volume.restrict (Ω \ tsupport u)]
                (fun _ : E => (0 : ℝ)) := by
              have h_meas : MeasurableSet (Ω \ tsupport u) :=
                hΩ.measurableSet.diff (isClosed_tsupport _).measurableSet
              refine (ae_restrict_iff' h_meas).mpr ?_
              refine Filter.Eventually.of_forall fun x hx => ?_
              dsimp [g_mod]
              have hx_not : x ∉ tsupport u := hx.2
              rw [Set.indicator_of_notMem hx_not]
            exact h_g_mod_zero.trans h_g_Ω_zero.symm
          have h_union : Ω = tsupport u ∪ (Ω \ tsupport u) := by
            ext x; constructor
            · intro hx
              by_cases hx' : x ∈ tsupport u
              · exact Or.inl hx'
              · exact Or.inr ⟨hx, hx'⟩
            · rintro (hx | ⟨hx, -⟩)
              · exact hu_support hx
              · exact hx
          rw [h_union]
          exact ((ae_restrict_union_iff (tsupport u) (Ω \ tsupport u)
            (fun x => g_mod x = g_Ω x)).mpr ⟨h_ae_tsupport, h_ae_diff⟩)
        have hg_Ω_mem : MemWkp (d := d) k p g_Ω Ω := hwp_Ω i
        have hg_mod_mem_Ω : MemWkp (d := d) k p g_mod Ω :=
          (MemWkp_congr_ae hp hΩ hg_mod_ae_eq_g_Ω).mpr hg_Ω_mem
        have hg_mod_mem_V : MemWkp (d := d) k p g_mod V :=
          ih hg_mod_mem_Ω hg_mod_tsupport_subset_Ω hg_mod_compactSupport
        have hg_mod_ae_eq_g_V : g_mod =ᵐ[volume.restrict V] g_V := by
          have hg_Ω_ae_g_V_Ω : g_Ω =ᵐ[volume.restrict Ω] g_V := by
            have h_g_Ω_weak : Sobolev.Euclidean.HasWeakPartialDeriv i g_Ω u Ω :=
              chosenWeakPartialOrZero_isWeakPartial_of_mem hu_W_Ω i
            have h_g_V_weak : Sobolev.Euclidean.HasWeakPartialDeriv i g_V u V :=
              chosenWeakPartialOrZero_isWeakPartial_of_mem hu_W_V i
            have h_g_V_weak_Ω : Sobolev.Euclidean.HasWeakPartialDeriv i g_V u Ω :=
              Sobolev.Euclidean.HasWeakPartialDeriv.restrict hΩV h_g_V_weak
            have h_g_Ω_local : LocallyIntegrable g_Ω (volume.restrict Ω) :=
              (chosenWeakPartialOrZero_memLp_of_mem hu_W_Ω i).locallyIntegrable hp
            have h_g_V_local : LocallyIntegrable g_V (volume.restrict Ω) := by
              have h_mem : MemLp g_V p (volume.restrict V) :=
                chosenWeakPartialOrZero_memLp_of_mem hu_W_V i
              have h_mem_Ω : MemLp g_V p (volume.restrict Ω) :=
                h_mem.mono_measure (Measure.restrict_mono_set volume hΩV)
              exact h_mem_Ω.locallyIntegrable hp
            exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ h_g_Ω_weak h_g_V_weak_Ω
              h_g_Ω_local h_g_V_local
          have h_ae_Ω : g_mod =ᵐ[volume.restrict Ω] g_V :=
            hg_mod_ae_eq_g_Ω.trans hg_Ω_ae_g_V_Ω
          have h_ae_V_diff : g_mod =ᵐ[volume.restrict (V \ Ω)] g_V := by
            have h_g_V_zero : g_V =ᵐ[volume.restrict (V \ tsupport u)]
                (fun _ : E => (0 : ℝ)) :=
              chosenWeakPartialOrZero_ae_zero_on_sdiff_tsupport hp hV hu_W_V i
            have h_subset : V \ Ω ⊆ V \ tsupport u :=
              Set.sdiff_subset_sdiff_right hu_support
            have h_g_V_zero' : g_V =ᵐ[volume.restrict (V \ Ω)]
                (fun _ : E => (0 : ℝ)) :=
              ae_restrict_of_ae_restrict_of_subset h_subset h_g_V_zero
            have h_meas_V_diff : MeasurableSet (V \ Ω) :=
              (hV.measurableSet.diff hΩ_meas)
            have h_g_mod_zero : g_mod =ᵐ[volume.restrict (V \ Ω)]
                (fun _ : E => (0 : ℝ)) := by
              refine (ae_restrict_iff' h_meas_V_diff).mpr ?_
              refine Filter.Eventually.of_forall ?_
              intro x hx
              have hx_not_Ω : x ∉ Ω := hx.2
              have hx_not_tsupp : x ∉ tsupport g_mod :=
                fun h => hx_not_Ω (hg_mod_tsupport_subset_Ω h)
              exact image_eq_zero_of_notMem_tsupport hx_not_tsupp
            exact h_g_mod_zero.trans h_g_V_zero'.symm
          have h_union_V : V = Ω ∪ (V \ Ω) := by
            ext x; constructor
            · intro hx
              by_cases hx' : x ∈ Ω
              · exact Or.inl hx'
              · exact Or.inr ⟨hx, hx'⟩
            · rintro (hx | ⟨hx, -⟩)
              · exact hΩV hx
              · exact hx
          rw [h_union_V]
          exact ((ae_restrict_union_iff Ω (V \ Ω) (fun x => g_mod x = g_V x)).mpr
            ⟨h_ae_Ω, h_ae_V_diff⟩)
        exact (MemWkp_congr_ae hp hV hg_mod_ae_eq_g_V).mp hg_mod_mem_V
      exact ⟨hu_W_V, hwp_V⟩

theorem convolution_fderiv_eq_convolution_indicator_chosenWeakPartial
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ_open : IsOpen Ω)
    {u : E → ℝ} (hu_W : Sobolev.Euclidean.MemW1p p u Ω)
    (hu_compact : HasCompactSupport u) (hu_support : tsupport u ⊆ Ω)
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (i : Fin d) (x : E) :
    ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Ω.indicator (chosenWeakPartialOrZero p i u Ω)) x :=
  convolution_fderiv_eq_convolution_weakPartial_univ
    (hasWeakPartialDeriv_indicator_chosenWeakPartial_univ
      (d := d) hp hΩ_open hu_W hu_compact hu_support i)
    hφ_smooth hφ_compact x

noncomputable def iteratedZeroExtension (p : ℝ≥0∞) (Ω K : Set E) :
    ∀ (j : ℕ), (Fin j → Fin d) → (E → ℝ) → (E → ℝ)
  | 0,     _, u => u
  | j + 1, β, u =>
      iteratedZeroExtension p Ω K j (fun i : Fin j => β i.succ)
        (K.indicator (chosenWeakPartialOrZero p (β 0) u Ω))

@[simp] lemma iteratedZeroExtension_zero
    (p : ℝ≥0∞) (Ω K : Set E) (β : Fin 0 → Fin d) (u : E → ℝ) :
    iteratedZeroExtension (d := d) p Ω K 0 β u = u := rfl

lemma iteratedZeroExtension_succ
    (p : ℝ≥0∞) (Ω K : Set E) (j : ℕ) (β : Fin (j + 1) → Fin d) (u : E → ℝ) :
    iteratedZeroExtension (d := d) p Ω K (j + 1) β u =
      iteratedZeroExtension p Ω K j (fun i : Fin j => β i.succ)
        (K.indicator (chosenWeakPartialOrZero p (β 0) u Ω)) := rfl

private lemma tsupport_indicator_chosenWeakPartial_subset
    {p : ℝ≥0∞} {Ω K : Set E} (hK_closed : IsClosed K)
    (v : E → ℝ) (i : Fin d) :
    tsupport (K.indicator (chosenWeakPartialOrZero p i v Ω)) ⊆ K := by
  classical
  have hsupp_subset :
      Function.support (K.indicator (chosenWeakPartialOrZero p i v Ω)) ⊆ K := by
    intro x hx
    by_contra hxK
    have h0 : K.indicator (chosenWeakPartialOrZero p i v Ω) x = 0 :=
      Set.indicator_of_notMem hxK _
    exact hx h0
  exact (closure_minimal hsupp_subset hK_closed)

theorem tsupport_iteratedZeroExtension_subset
    {p : ℝ≥0∞} {Ω K : Set E} (hK_closed : IsClosed K)
    {u : E → ℝ} (hu_support : tsupport u ⊆ K)
    (j : ℕ) (β : Fin j → Fin d) :
    tsupport (iteratedZeroExtension (d := d) p Ω K j β u) ⊆ K := by
  induction j generalizing u with
  | zero =>
      simpa [iteratedZeroExtension_zero] using hu_support
  | succ j ih =>
      rw [iteratedZeroExtension_succ]
      refine ih ?_ (fun i : Fin j => β i.succ)
      exact tsupport_indicator_chosenWeakPartial_subset (d := d) hK_closed _ _

private theorem indicator_chosenWeakPartial_ae_eq
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω K : Set E}
    (hΩ_open : IsOpen Ω) (hK_closed : IsClosed K)
    {v : E → ℝ} (hv_W : Sobolev.Euclidean.MemW1p p v Ω) (hv_support : tsupport v ⊆ K)
    (i : Fin d) :
    K.indicator (chosenWeakPartialOrZero p i v Ω)
      =ᵐ[volume.restrict Ω] chosenWeakPartialOrZero p i v Ω := by
  classical
  have h_zero_off : chosenWeakPartialOrZero p i v Ω
      =ᵐ[volume.restrict (Ω \ tsupport v)] (fun _ : E => (0 : ℝ)) :=
    chosenWeakPartialOrZero_ae_zero_on_sdiff_tsupport (d := d) hp hΩ_open hv_W i
  have hΩ_eq_union : Ω = (Ω ∩ K) ∪ (Ω \ K) := by
    ext x
    constructor
    · intro hx
      by_cases hxK : x ∈ K
      · left; exact ⟨hx, hxK⟩
      · right; exact ⟨hx, hxK⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have h_on_K : K.indicator (chosenWeakPartialOrZero p i v Ω)
      =ᵐ[volume.restrict (Ω ∩ K)] chosenWeakPartialOrZero p i v Ω := by
    refine (ae_restrict_iff' (hΩ_open.measurableSet.inter hK_closed.measurableSet)).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Set.indicator_of_mem hx.2]
  have hKc_meas : MeasurableSet (Ω \ K) :=
    hΩ_open.measurableSet.diff hK_closed.measurableSet
  have hsubset : (Ω \ K) ⊆ (Ω \ tsupport v) := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxv
    exact hx.2 (hv_support hxv)
  have h_zero_off' : chosenWeakPartialOrZero p i v Ω
      =ᵐ[volume.restrict (Ω \ K)] (fun _ : E => (0 : ℝ)) := by
    have h := h_zero_off
    rw [Filter.EventuallyEq] at h ⊢
    have h_mono := ae_mono (Measure.restrict_mono_set volume hsubset) h
    exact h_mono
  have h_off_K : K.indicator (chosenWeakPartialOrZero p i v Ω)
      =ᵐ[volume.restrict (Ω \ K)] chosenWeakPartialOrZero p i v Ω := by
    have h_lhs_zero : K.indicator (chosenWeakPartialOrZero p i v Ω)
        =ᵐ[volume.restrict (Ω \ K)] (fun _ : E => (0 : ℝ)) := by
      refine (ae_restrict_iff' hKc_meas).mpr ?_
      refine Filter.Eventually.of_forall ?_
      intro x hx
      rw [Set.indicator_of_notMem hx.2]
    exact h_lhs_zero.trans h_zero_off'.symm
  rw [show volume.restrict Ω = volume.restrict ((Ω ∩ K) ∪ (Ω \ K)) by
    rw [← hΩ_eq_union]]
  exact (ae_restrict_union_iff (s := Ω ∩ K) (t := Ω \ K)
    (μ := (volume : Measure E))
    (p := fun x => K.indicator (chosenWeakPartialOrZero p i v Ω) x =
      chosenWeakPartialOrZero p i v Ω x)).mpr ⟨h_on_K, h_off_K⟩

theorem iteratedZeroExtension_memWkp_and_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω K : Set E}
    (hΩ_open : IsOpen Ω) (hK_closed : IsClosed K) :
    ∀ (j k : ℕ), j ≤ k → ∀ (β : Fin j → Fin d) {u : E → ℝ},
      MemWkp (d := d) k p u Ω → tsupport u ⊆ K →
      MemWkp (d := d) (k - j) p (iteratedZeroExtension (d := d) p Ω K j β u) Ω ∧
      iteratedZeroExtension (d := d) p Ω K j β u
        =ᵐ[volume.restrict Ω] iterWeakPartial (d := d) p j β u Ω := by
  intro j
  induction j with
  | zero =>
      intro k _ β u hu_W _
      refine ⟨?_, ?_⟩
      · simpa [iteratedZeroExtension_zero, Nat.sub_zero] using hu_W
      · simp [iteratedZeroExtension_zero, iterWeakPartial_zero]
  | succ j ih =>
      intro k hjk β u hu_W hu_support
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
        cases k with
        | zero => exact absurd hjk (by simp)
        | succ k' => exact ⟨k', rfl⟩
      have hjk' : j ≤ k' := Nat.succ_le_succ_iff.mp hjk
      have h_chosen_mem : MemWkp (d := d) k' p (chosenWeakPartialOrZero p (β 0) u Ω) Ω :=
        hu_W.chosenWeakPartial_mem (β 0)
      have hu_W1p : Sobolev.Euclidean.MemW1p p u Ω := hu_W.memW1p
      have h_ind_ae : K.indicator (chosenWeakPartialOrZero p (β 0) u Ω)
          =ᵐ[volume.restrict Ω] chosenWeakPartialOrZero p (β 0) u Ω :=
        indicator_chosenWeakPartial_ae_eq (d := d) hp hΩ_open hK_closed hu_W1p hu_support (β 0)
      have h_ind_mem :
          MemWkp (d := d) k' p (K.indicator (chosenWeakPartialOrZero p (β 0) u Ω)) Ω :=
        (MemWkp_congr_ae (d := d) hp hΩ_open h_ind_ae).mpr h_chosen_mem
      have h_ind_support :
          tsupport (K.indicator (chosenWeakPartialOrZero p (β 0) u Ω)) ⊆ K :=
        tsupport_indicator_chosenWeakPartial_subset (d := d) hK_closed _ _
      obtain ⟨h_iter_mem, h_iter_ae⟩ :=
        ih k' hjk' (fun i : Fin j => β i.succ) h_ind_mem h_ind_support
      rw [iteratedZeroExtension_succ]
      refine ⟨?_, ?_⟩
      · have hsub : (k' + 1) - (j + 1) = k' - j := Nat.succ_sub_succ_eq_sub k' j
        rw [hsub]
        exact h_iter_mem
      · have h_iter_succ : iterWeakPartial (d := d) p (j + 1) β u Ω =
            iterWeakPartial (d := d) p j (fun i : Fin j => β i.succ)
              (chosenWeakPartialOrZero p (β 0) u Ω) Ω :=
          iterWeakPartial_succ p j β u Ω
        rw [h_iter_succ]
        have h_iter_congr : iterWeakPartial (d := d) p j (fun i : Fin j => β i.succ)
              (K.indicator (chosenWeakPartialOrZero p (β 0) u Ω)) Ω
            =ᵐ[volume.restrict Ω]
            iterWeakPartial (d := d) p j (fun i : Fin j => β i.succ)
              (chosenWeakPartialOrZero p (β 0) u Ω) Ω :=
          iterWeakPartial_ae_congr (d := d) hp hΩ_open j _ h_ind_ae
        exact h_iter_ae.trans h_iter_congr

theorem iteratedZeroExtension_memWkp
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω K : Set E}
    (hΩ_open : IsOpen Ω) (hK_closed : IsClosed K)
    (j k : ℕ) (hjk : j ≤ k) (β : Fin j → Fin d)
    {u : E → ℝ} (hu_W : MemWkp (d := d) k p u Ω) (hu_support : tsupport u ⊆ K) :
    MemWkp (d := d) (k - j) p (iteratedZeroExtension (d := d) p Ω K j β u) Ω :=
  (iteratedZeroExtension_memWkp_and_ae (d := d) hp hΩ_open hK_closed
    j k hjk β hu_W hu_support).1

theorem iteratedZeroExtension_ae_eq_iterWeakPartial
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω K : Set E}
    (hΩ_open : IsOpen Ω) (hK_closed : IsClosed K)
    (j k : ℕ) (hjk : j ≤ k) (β : Fin j → Fin d)
    {u : E → ℝ} (hu_W : MemWkp (d := d) k p u Ω) (hu_support : tsupport u ⊆ K) :
    iteratedZeroExtension (d := d) p Ω K j β u
      =ᵐ[volume.restrict Ω] iterWeakPartial (d := d) p j β u Ω :=
  (iteratedZeroExtension_memWkp_and_ae (d := d) hp hΩ_open hK_closed
    j k hjk β hu_W hu_support).2

lemma iteratedZeroExtension_one
    (p : ℝ≥0∞) (Ω K : Set E) (i : Fin d) (u : E → ℝ) :
    iteratedZeroExtension (d := d) p Ω K 1 (fun _ : Fin 1 => i) u =
      K.indicator (chosenWeakPartialOrZero p i u Ω) := by
  rw [iteratedZeroExtension_succ]
  simp [iteratedZeroExtension_zero]

noncomputable def iterClassicalPartial :
    ∀ (j : ℕ), (Fin j → Fin d) → (E → ℝ) → (E → ℝ)
  | 0,     _, f => f
  | j + 1, β, f =>
      iterClassicalPartial j (fun i : Fin j => β i.succ)
        (fun x => (fderiv ℝ f x) (EuclideanSpace.single (β 0) 1))

@[simp] lemma iterClassicalPartial_zero (β : Fin 0 → Fin d) (f : E → ℝ) :
    iterClassicalPartial (d := d) 0 β f = f := rfl

lemma iterClassicalPartial_succ
    (j : ℕ) (β : Fin (j + 1) → Fin d) (f : E → ℝ) :
    iterClassicalPartial (d := d) (j + 1) β f =
      iterClassicalPartial j (fun i : Fin j => β i.succ)
        (fun x => (fderiv ℝ f x) (EuclideanSpace.single (β 0) 1)) := rfl

theorem contDiff_iterClassicalPartial :
    ∀ (j : ℕ) (β : Fin j → Fin d) {f : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) (iterClassicalPartial (d := d) j β f) := by
  intro j
  induction j with
  | zero =>
      intro β f hf
      simpa [iterClassicalPartial_zero] using hf
  | succ j ih =>
      intro β f hf
      rw [iterClassicalPartial_succ]
      refine ih (fun i : Fin j => β i.succ) ?_
      have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := by
        exact hf.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
      exact hfd.clm_apply contDiff_const

private theorem fderiv_convolution_eq_convolution_weakPartial_indicator
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ_open : IsOpen Ω)
    {u : E → ℝ} (hu_W : Sobolev.Euclidean.MemW1p p u Ω)
    (hu_compact : HasCompactSupport u) (hu_support : tsupport u ⊆ Ω)
    {η : E → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (i : Fin d) (x : E) :
    (fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x)
        (EuclideanSpace.single i 1) =
      (Ω.indicator (chosenWeakPartialOrZero p i u Ω)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x := by
  classical
  have hu_local : LocallyIntegrable u volume := by
    have h_aemeas : AEStronglyMeasurable u volume := by
      have h1 : AEStronglyMeasurable u (volume.restrict Ω) :=
        hu_W.1.aestronglyMeasurable
      have h_zero_off : ∀ x : E, x ∉ Ω → u x = 0 := fun x hx =>
        Sobolev.Euclidean.zero_outside_of_tsupport_subset (Ω := Ω) hu_support hx
      have h_ae : u =ᵐ[volume] Ω.indicator u := by
        refine Filter.Eventually.of_forall ?_
        intro x
        by_cases hx : x ∈ Ω
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, h_zero_off x hx]
      have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
      have h_ind : AEStronglyMeasurable (Ω.indicator u) volume :=
        (aestronglyMeasurable_indicator_iff (μ := volume) hΩ_meas).mpr h1
      exact h_ind.congr h_ae.symm
    have h_uLp : MemLp u p volume := by
      rw [show u = Ω.indicator u from ?_]
      · rw [memLp_indicator_iff_restrict hΩ_open.measurableSet]
        exact hu_W.1
      · funext x
        by_cases hx : x ∈ Ω
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx,
            Sobolev.Euclidean.zero_outside_of_tsupport_subset (Ω := Ω) hu_support hx]
    exact h_uLp.locallyIntegrable hp
  have hη_C1 : ContDiff ℝ 1 η := hη_smooth.of_le (by norm_cast)
  have hderiv : HasFDerivAt
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η)
      ((u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR E, volume] fderiv ℝ η) x) x :=
    hη_compact.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hu_local hη_C1 x
  have hpartial :
      (fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x)
          (EuclideanSpace.single i 1) =
        (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (fun y => (fderiv ℝ η y) (EuclideanSpace.single i 1))) x := by
    rw [hderiv.fderiv]
    exact convolution_precompR_apply (𝕜 := ℝ) (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hu_local (hη_compact.fderiv ℝ) (hη_smooth.continuous_fderiv (by simp)) x
        (EuclideanSpace.single i 1)
  rw [hpartial]
  set dη : E → ℝ := fun y => (fderiv ℝ η y) (EuclideanSpace.single i 1) with hdη_def
  have hdη_smooth : ContDiff ℝ (⊤ : ℕ∞) dη :=
    (hη_smooth.fderiv_right (m := (⊤ : ℕ∞))
        (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
      contDiff_const
  have hdη_compact : HasCompactSupport dη :=
    hη_compact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hcomm1 :
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] dη) x =
        (dη ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x := by
    rw [convolution_lsmul, convolution_lsmul_swap]
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  rw [hcomm1]
  have hexisting :
      ((fun y => (fderiv ℝ η y) (EuclideanSpace.single i 1))
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
        (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Ω.indicator (chosenWeakPartialOrZero p i u Ω)) x :=
    convolution_fderiv_eq_convolution_indicator_chosenWeakPartial
      (d := d) hp hΩ_open hu_W hu_compact hu_support hη_smooth hη_compact i x
  rw [hexisting]
  rw [convolution_lsmul, convolution_lsmul_swap]
  refine integral_congr_ae ?_
  filter_upwards with t
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

private lemma convolution_lsmul_ae_eq
    {f g η : E → ℝ} (hfg : f =ᵐ[(volume : Measure E)] g) (x : E) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x =
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x := by
  classical
  rw [convolution_lsmul, convolution_lsmul]
  refine integral_congr_ae ?_
  filter_upwards [hfg] with t ht
  rw [ht]

private lemma K_indicator_ae_eq_Ω_indicator
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω K : Set E}
    (hΩ_open : IsOpen Ω) (hK_closed : IsClosed K) (hKΩ : K ⊆ Ω)
    {u : E → ℝ} (hu_W : Sobolev.Euclidean.MemW1p p u Ω) (hu_support : tsupport u ⊆ K)
    (i : Fin d) :
    K.indicator (chosenWeakPartialOrZero p i u Ω)
      =ᵐ[(volume : Measure E)] Ω.indicator (chosenWeakPartialOrZero p i u Ω) := by
  classical
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  have hKc_meas : MeasurableSet (Ω \ K) := hΩ_meas.diff hK_meas
  have h_zero_off : chosenWeakPartialOrZero p i u Ω
      =ᵐ[volume.restrict (Ω \ tsupport u)] (fun _ : E => (0 : ℝ)) :=
    chosenWeakPartialOrZero_ae_zero_on_sdiff_tsupport (d := d) hp hΩ_open hu_W i
  have hsubset : (Ω \ K) ⊆ (Ω \ tsupport u) := fun x hx =>
    ⟨hx.1, fun hxv => hx.2 (hu_support hxv)⟩
  have h_zero_on_diff : chosenWeakPartialOrZero p i u Ω
      =ᵐ[volume.restrict (Ω \ K)] (fun _ : E => (0 : ℝ)) :=
    ae_mono (Measure.restrict_mono_set volume hsubset) h_zero_off
  have h_on_K : K.indicator (chosenWeakPartialOrZero p i u Ω)
      =ᵐ[volume.restrict K] Ω.indicator (chosenWeakPartialOrZero p i u Ω) := by
    refine (ae_restrict_iff' hK_meas).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hKΩ hx)]
  have h_on_Ωc : K.indicator (chosenWeakPartialOrZero p i u Ω)
      =ᵐ[volume.restrict (Ωᶜ)] Ω.indicator (chosenWeakPartialOrZero p i u Ω) := by
    refine (ae_restrict_iff' hΩ_meas.compl).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro x hx
    have hxK : x ∉ K := fun hxK => hx (hKΩ hxK)
    rw [Set.indicator_of_notMem hxK, Set.indicator_of_notMem hx]
  have h_on_diff : K.indicator (chosenWeakPartialOrZero p i u Ω)
      =ᵐ[volume.restrict (Ω \ K)] Ω.indicator (chosenWeakPartialOrZero p i u Ω) := by
    filter_upwards [h_zero_on_diff, (ae_restrict_iff' hKc_meas).mpr
      (Filter.Eventually.of_forall (fun x hx => hx))] with x hx hx_in
    have hxK : x ∉ K := hx_in.2
    have hxΩ : x ∈ Ω := hx_in.1
    rw [Set.indicator_of_notMem hxK, Set.indicator_of_mem hxΩ, hx]
  have hE_eq_union : (Set.univ : Set E) = K ∪ (Ω \ K) ∪ Ωᶜ := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff, true_iff]
    by_cases hxK : x ∈ K
    · left; left; exact hxK
    · by_cases hxΩ : x ∈ Ω
      · left; right; exact ⟨hxΩ, hxK⟩
      · right; exact hxΩ
  have h_restrict_univ : (volume : Measure E).restrict Set.univ = volume :=
    Measure.restrict_univ
  rw [show (volume : Measure E) = volume.restrict Set.univ from h_restrict_univ.symm]
  rw [hE_eq_union]
  refine (ae_restrict_union_iff (s := K ∪ (Ω \ K)) (t := Ωᶜ)
    (μ := (volume : Measure E))
    (p := fun x => K.indicator (chosenWeakPartialOrZero p i u Ω) x =
      Ω.indicator (chosenWeakPartialOrZero p i u Ω) x)).mpr ⟨?_, h_on_Ωc⟩
  refine (ae_restrict_union_iff (s := K) (t := Ω \ K)
    (μ := (volume : Measure E))
    (p := fun x => K.indicator (chosenWeakPartialOrZero p i u Ω) x =
      Ω.indicator (chosenWeakPartialOrZero p i u Ω) x)).mpr ⟨h_on_K, h_on_diff⟩

private theorem fderiv_convolution_eq_convolution_K_indicator
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω K : Set E}
    (hΩ_open : IsOpen Ω) (hK_closed : IsClosed K) (hKΩ : K ⊆ Ω)
    {u : E → ℝ} (hu_W : Sobolev.Euclidean.MemW1p p u Ω)
    (hu_compact : HasCompactSupport u) (hu_support : tsupport u ⊆ K)
    {η : E → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) (i : Fin d) (x : E) :
    (fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x)
        (EuclideanSpace.single i 1) =
      (K.indicator (chosenWeakPartialOrZero p i u Ω)
          ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x := by
  classical
  have hu_support_Ω : tsupport u ⊆ Ω := hu_support.trans hKΩ
  rw [fderiv_convolution_eq_convolution_weakPartial_indicator (d := d)
    hp hΩ_open hu_W hu_compact hu_support_Ω hη_smooth hη_compact i x]
  exact (convolution_lsmul_ae_eq
    (K_indicator_ae_eq_Ω_indicator (d := d) hp hΩ_open hK_closed hKΩ
      hu_W hu_support i) x).symm

theorem iterClassicalPartial_convolution_eq_convolution_iteratedZeroExtension
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω K : Set E}
    (hΩ_open : IsOpen Ω) (hK_compact : IsCompact K) (hK_closed : IsClosed K)
    (hKΩ : K ⊆ Ω)
    {η : E → ℝ} (hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hη_compact : HasCompactSupport η) :
    ∀ (j k : ℕ), j ≤ k → ∀ (β : Fin j → Fin d) {u : E → ℝ},
      MemWkp (d := d) k p u Ω → HasCompactSupport u → tsupport u ⊆ K →
      ∀ (x : E),
        iterClassicalPartial (d := d) j β
            (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x =
          (iteratedZeroExtension (d := d) p Ω K j β u
              ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x := by
  intro j
  induction j with
  | zero =>
      intro k _ β u _ _ _ x
      simp [iterClassicalPartial_zero, iteratedZeroExtension_zero]
  | succ j ih =>
      intro k hjk β u hu_W hu_compact hu_support x
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
        cases k with
        | zero => exact absurd hjk (by simp)
        | succ k' => exact ⟨k', rfl⟩
      have hjk' : j ≤ k' := Nat.succ_le_succ_iff.mp hjk
      set u_K : E → ℝ := K.indicator (chosenWeakPartialOrZero p (β 0) u Ω) with hu_K_def
      have hu_W1p : Sobolev.Euclidean.MemW1p p u Ω := hu_W.memW1p
      have hu_K_support : tsupport u_K ⊆ K :=
        tsupport_indicator_chosenWeakPartial_subset (d := d) hK_closed _ _
      have hu_K_compact : HasCompactSupport u_K :=
        hK_compact.of_isClosed_subset (isClosed_tsupport _) hu_K_support
      have h_chosen_mem : MemWkp (d := d) k' p (chosenWeakPartialOrZero p (β 0) u Ω) Ω :=
        hu_W.chosenWeakPartial_mem (β 0)
      have h_ind_ae : K.indicator (chosenWeakPartialOrZero p (β 0) u Ω)
          =ᵐ[volume.restrict Ω] chosenWeakPartialOrZero p (β 0) u Ω :=
        indicator_chosenWeakPartial_ae_eq (d := d) hp hΩ_open hK_closed hu_W1p hu_support (β 0)
      have hu_K_W : MemWkp (d := d) k' p u_K Ω :=
        (MemWkp_congr_ae (d := d) hp hΩ_open h_ind_ae).mpr h_chosen_mem
      have h_step :
          ∀ y : E, (fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) y)
              (EuclideanSpace.single (β 0) 1) =
            (u_K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) y := by
        intro y
        exact fderiv_convolution_eq_convolution_K_indicator (d := d) hp hΩ_open
          hK_closed hKΩ hu_W1p hu_compact hu_support hη_smooth hη_compact (β 0) y
      have h_func_eq : (fun y => (fderiv ℝ
            (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) y)
              (EuclideanSpace.single (β 0) 1)) =
          (u_K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) := by
        funext y; exact h_step y
      have h_lhs : iterClassicalPartial (d := d) (j + 1) β
            (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x =
          iterClassicalPartial (d := d) j (fun i : Fin j => β i.succ)
              (u_K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x := by
        rw [iterClassicalPartial_succ, h_func_eq]
      rw [h_lhs]
      have h_ih_tail := ih k' hjk' (fun i : Fin j => β i.succ)
        (u := u_K) hu_K_W hu_K_compact hu_K_support x
      rw [h_ih_tail]
      rw [iteratedZeroExtension_succ]

theorem tendsto_eLpNorm_translate_sub_of_memLp
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : E → ℝ} (hf : MemLp f p (volume : Measure E)) :
    Filter.Tendsto (fun h : E => eLpNorm (fun x => f (x - h) - f x) p volume)
      (𝓝 0) (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε_pos
  have hε_quart_pos : 0 < (ε : ℝ≥0∞) / 4 := by
    refine ENNReal.div_pos ?_ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
    exact hε_pos.ne'
  by_cases hε_top : ε = ∞
  · refine Filter.Eventually.of_forall ?_
    intro h
    rw [hε_top]; exact le_top
  have hε_real_pos : 0 < ε.toReal := ENNReal.toReal_pos hε_pos.ne' hε_top
  set εR : ℝ := ε.toReal with hεR_def
  have h_εR_eq : ε = ENNReal.ofReal εR := (ENNReal.ofReal_toReal hε_top).symm
  have h_quart_pos : 0 < εR / 4 := by linarith
  have h_quart_eq : ENNReal.ofReal (εR / 4) ≤ ε := by
    rw [h_εR_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  obtain ⟨g, hg_compact, hg_smooth, hg_diff⟩ :=
    hf.exist_eLpNorm_sub_le hp_top hp_one h_quart_pos
  set Cgrad : ℝ≥0∞ := eLpNorm (fun x => ‖fderiv ℝ g x‖) p volume with hCgrad_def
  have hCgrad_lt_top : Cgrad < ∞ := by
    have h_grad_compact : HasCompactSupport (fderiv ℝ g) := hg_compact.fderiv ℝ
    have h_grad_cont : Continuous (fderiv ℝ g) :=
      hg_smooth.continuous_fderiv (by simp)
    have h_norm_cont : Continuous (fun x => ‖fderiv ℝ g x‖) := h_grad_cont.norm
    have h_norm_compact : HasCompactSupport (fun x => ‖fderiv ℝ g x‖) := by
      apply HasCompactSupport.intro h_grad_compact.isCompact
      intro x hx
      have : fderiv ℝ g x = 0 := by
        by_contra h
        exact hx (subset_tsupport _ h)
      rw [this]
      simp
    exact (h_norm_cont.memLp_of_hasCompactSupport
      (μ := (volume : Measure E)) h_norm_compact).eLpNorm_lt_top
  have hCgrad_ne_top : Cgrad ≠ ∞ := hCgrad_lt_top.ne
  have h_target : Filter.Tendsto (fun h : E =>
      ENNReal.ofReal ‖h‖ * Cgrad +
        ENNReal.ofReal (εR / 4) + ENNReal.ofReal (εR / 4))
      (𝓝 0) (𝓝 (0 * Cgrad + ENNReal.ofReal (εR / 4) + ENNReal.ofReal (εR / 4))) := by
    have h_norm_tendsto : Filter.Tendsto (fun h : E => ENNReal.ofReal ‖h‖)
        (𝓝 0) (𝓝 (ENNReal.ofReal 0)) := by
      have : Continuous (fun h : E => ENNReal.ofReal ‖h‖) :=
        ENNReal.continuous_ofReal.comp continuous_norm
      simpa [norm_zero] using this.tendsto 0
    have h1 : Filter.Tendsto (fun h : E => ENNReal.ofReal ‖h‖ * Cgrad) (𝓝 0)
        (𝓝 (ENNReal.ofReal 0 * Cgrad)) :=
      ENNReal.Tendsto.mul_const h_norm_tendsto (Or.inr hCgrad_ne_top)
    simpa [ENNReal.ofReal_zero] using
      ((h1.add tendsto_const_nhds).add tendsto_const_nhds)
  have h_lim_lt : 0 * Cgrad + ENNReal.ofReal (εR / 4) + ENNReal.ofReal (εR / 4)
      < ε := by
    rw [zero_mul, zero_add]
    rw [h_εR_eq]
    rw [← ENNReal.ofReal_add (le_of_lt h_quart_pos) (le_of_lt h_quart_pos)]
    rw [ENNReal.ofReal_lt_ofReal_iff hε_real_pos]
    linarith
  have h_eventually :
      ∀ᶠ h : E in 𝓝 0,
        ENNReal.ofReal ‖h‖ * Cgrad +
          ENNReal.ofReal (εR / 4) + ENNReal.ofReal (εR / 4) ≤ ε := by
    have h_lt := h_target.eventually_lt_const h_lim_lt
    exact h_lt.mono fun h hh => le_of_lt hh
  filter_upwards [h_eventually] with h hh
  set G : E → ℝ := fun x => f (x - h) - f x with hG_def
  set A : E → ℝ := fun x => f (x - h) - g (x - h) with hA_def
  set B : E → ℝ := fun x => g (x - h) - g x with hB_def
  set C : E → ℝ := fun x => g x - f x with hC_def
  have hG_eq : G = fun x => A x + B x + C x := by
    funext x; simp only [G, A, B, C]; ring
  have hf_aem : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hf_aem_h : AEStronglyMeasurable (fun x => f (x - h)) volume := by
    have hMP : MeasurePreserving (fun x : E => x - h) volume volume := by
      have h_neg : MeasurePreserving (fun x : E => x + (-h)) volume volume :=
        measurePreserving_add_right volume (-h)
      have heq : (fun x : E => x - h) = (fun x : E => x + (-h)) := by
        funext t; rw [sub_eq_add_neg]
      rw [heq]
      exact h_neg
    exact hf_aem.comp_measurePreserving hMP
  have hg_aem : AEStronglyMeasurable g volume :=
    hg_smooth.continuous.aestronglyMeasurable
  have hg_aem_h : AEStronglyMeasurable (fun x => g (x - h)) volume := by
    have hMP : MeasurePreserving (fun x : E => x - h) volume volume := by
      have h_neg : MeasurePreserving (fun x : E => x + (-h)) volume volume :=
        measurePreserving_add_right volume (-h)
      have heq : (fun x : E => x - h) = (fun x : E => x + (-h)) := by
        funext t; rw [sub_eq_add_neg]
      rw [heq]
      exact h_neg
    exact hg_aem.comp_measurePreserving hMP
  have hA_aem : AEStronglyMeasurable A volume := hf_aem_h.sub hg_aem_h
  have hB_aem : AEStronglyMeasurable B volume := hg_aem_h.sub hg_aem
  have hC_aem : AEStronglyMeasurable C volume := hg_aem.sub hf_aem
  have hAB_aem : AEStronglyMeasurable (fun x => A x + B x) volume := hA_aem.add hB_aem
  have h_triangle1 : eLpNorm (fun x => A x + B x + C x) p volume
      ≤ eLpNorm (fun x => A x + B x) p volume + eLpNorm C p volume := by
    have := eLpNorm_add_le (μ := (volume : Measure E)) (p := p) hAB_aem hC_aem hp_one
    have heq : ((fun x => A x + B x) + (fun x : E => C x)) =
        fun x => A x + B x + C x := by funext x; rfl
    rw [heq] at this
    exact this
  have h_triangle2 : eLpNorm (fun x => A x + B x) p volume
      ≤ eLpNorm A p volume + eLpNorm B p volume := by
    have := eLpNorm_add_le (μ := (volume : Measure E)) (p := p) hA_aem hB_aem hp_one
    have heq : ((fun x : E => A x) + (fun x => B x)) =
        fun x => A x + B x := by funext x; rfl
    rw [heq] at this
    exact this
  have hA_norm : eLpNorm A p volume = eLpNorm (fun x => f x - g x) p volume := by
    have hMP : MeasurePreserving (fun x : E => x - h) volume volume := by
      have h_neg : MeasurePreserving (fun x : E => x + (-h)) volume volume :=
        measurePreserving_add_right volume (-h)
      have heq : (fun x : E => x - h) = (fun x : E => x + (-h)) := by
        funext t; rw [sub_eq_add_neg]
      rw [heq]
      exact h_neg
    have h_aem : AEStronglyMeasurable (fun x => f x - g x) volume :=
      hf_aem.sub hg_aem
    have := eLpNorm_comp_measurePreserving (p := p) (g := fun x => f x - g x) h_aem hMP
    have heq : (fun x => f x - g x) ∘ (fun x : E => x - h) = A := by
      funext x; simp [A, Function.comp]
    rw [heq] at this
    exact this
  have hA_le : eLpNorm A p volume ≤ ENNReal.ofReal (εR / 4) := by
    rw [hA_norm]
    have h_eq : (fun x => f x - g x) = (f - g : E → ℝ) := rfl
    rw [h_eq]
    exact hg_diff
  have hC_le : eLpNorm C p volume ≤ ENNReal.ofReal (εR / 4) := by
    have heq : C = -((f - g : E → ℝ)) := by
      funext x; simp only [C, Pi.neg_apply, Pi.sub_apply]; ring
    rw [heq, eLpNorm_neg]
    exact hg_diff
  have hB_le : eLpNorm B p volume ≤ ENNReal.ofReal ‖h‖ * Cgrad := by
    have hBA : B = -(fun x => g x - g (x - h)) := by
      funext x; simp only [B, Pi.neg_apply]; ring
    rw [hBA, eLpNorm_neg]
    exact eLpNorm_translate_sub_le_smul_eLpNorm_fderiv (d := d) hp_one hp_top hg_smooth h
  rw [hG_eq]
  refine (h_triangle1.trans ?_).trans hh
  refine (add_le_add h_triangle2 hC_le).trans ?_
  refine (add_le_add (add_le_add hA_le hB_le) (le_refl _)).trans ?_
  rw [show ENNReal.ofReal (εR / 4) + ENNReal.ofReal ‖h‖ * Cgrad +
        ENNReal.ofReal (εR / 4) =
      ENNReal.ofReal ‖h‖ * Cgrad +
        ENNReal.ofReal (εR / 4) + ENNReal.ofReal (εR / 4) by ring]

private lemma convolution_lsmul_comm
    (f g : E → ℝ) (x : E) :
    (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
      (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
  rw [convolution_lsmul, convolution_lsmul_swap]
  refine integral_congr_ae ?_
  filter_upwards with t
  rw [smul_eq_mul, smul_eq_mul, mul_comm]

theorem chosenWeakPartial_smooth_ae_eq
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ_open : IsOpen Ω)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_W : Sobolev.Euclidean.MemW1p p ψ Ω) (i : Fin d) :
    chosenWeakPartialOrZero p i ψ Ω
      =ᵐ[volume.restrict Ω]
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) := by
  have h_chosen : Sobolev.Euclidean.HasWeakPartialDeriv i (chosenWeakPartialOrZero p i ψ Ω) ψ Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hψ_W i
  have h_classical : Sobolev.Euclidean.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) ψ Ω :=
    Sobolev.Euclidean.HasWeakPartialDeriv.of_contDiff
      (hψ_smooth.of_le (by norm_cast))
  have h_chosen_local : LocallyIntegrable (chosenWeakPartialOrZero p i ψ Ω)
      (volume.restrict Ω) :=
    (chosenWeakPartialOrZero_memLp_of_mem hψ_W i).locallyIntegrable hp
  have h_classical_local : LocallyIntegrable
      (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
    have h_cont : Continuous (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
      (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact h_cont.locallyIntegrable.mono_measure Measure.restrict_le_self
  exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ_open h_chosen h_classical
    h_chosen_local h_classical_local

theorem MemWkp_of_smooth_compactSupport
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {ψ : E → ℝ} (hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) (hψ_support : tsupport ψ ⊆ Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ) :
    MemWkp (d := d) k p ψ Ω := by
  classical
  induction k generalizing ψ with
  | zero =>
      rw [MemWkp_zero]
      exact (hψ_smooth.continuous.memLp_of_hasCompactSupport
        (μ := (volume : Measure E)) hψ_compact).restrict _
  | succ k ih =>
      rw [MemWkp_succ]
      have hψ_W1p : Sobolev.Euclidean.MemW1p p ψ Ω := by
        refine ⟨(hψ_smooth.continuous.memLp_of_hasCompactSupport
          (μ := (volume : Measure E)) hψ_compact).restrict _, ?_⟩
        intro i
        refine ⟨fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1), ?_, ?_⟩
        · have h_cont : Continuous
              (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
            (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
          have h_compact : HasCompactSupport
              (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
            hψ_compact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
          exact (h_cont.memLp_of_hasCompactSupport (μ := (volume : Measure E)) h_compact).restrict _
        · exact Sobolev.Euclidean.HasWeakPartialDeriv.of_contDiff
            (hψ_smooth.of_le (by norm_cast))
      refine ⟨hψ_W1p, ?_⟩
      intro i
      have h_ae := chosenWeakPartial_smooth_ae_eq (d := d) hp hΩ_open hψ_smooth hψ_W1p i
      have h_classical_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
        (hψ_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      have h_classical_compact : HasCompactSupport
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) :=
        hψ_compact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      have h_classical_support :
          tsupport (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single i 1)) ⊆ Ω := by
        refine subset_trans ?_ hψ_support
        exact tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single i 1)
      have h_ih_classical := ih h_classical_smooth h_classical_compact h_classical_support
      exact (MemWkp_congr_ae (d := d) hp hΩ_open h_ae).mpr h_ih_classical

theorem iteratedZeroExtension_memLp_volume
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω K : Set E}
    (hΩ_open : IsOpen Ω) (hK_closed : IsClosed K) (hKΩ : K ⊆ Ω)
    (j k : ℕ) (hjk : j ≤ k) (β : Fin j → Fin d)
    {u : E → ℝ} (hu_W : MemWkp (d := d) k p u Ω) (hu_support : tsupport u ⊆ K) :
    MemLp (iteratedZeroExtension (d := d) p Ω K j β u) p (volume : Measure E) := by
  classical
  have h_support : tsupport (iteratedZeroExtension (d := d) p Ω K j β u) ⊆ K :=
    tsupport_iteratedZeroExtension_subset (d := d) hK_closed hu_support j β
  have h_zero_off : ∀ x : E, x ∉ K →
      iteratedZeroExtension (d := d) p Ω K j β u x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hx_in => hx (h_support hx_in))
  have h_eq : iteratedZeroExtension (d := d) p Ω K j β u =
      K.indicator (iteratedZeroExtension (d := d) p Ω K j β u) := by
    funext x
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK]
    · rw [Set.indicator_of_notMem hxK, h_zero_off x hxK]
  rw [h_eq]
  rw [memLp_indicator_iff_restrict hK_closed.measurableSet]
  have h_memLp_Ω : MemLp (iteratedZeroExtension (d := d) p Ω K j β u) p
      (volume.restrict Ω) :=
    (iteratedZeroExtension_memWkp (d := d) hp hΩ_open hK_closed
      j k hjk β hu_W hu_support).memLp
  refine h_memLp_Ω.mono_measure ?_
  exact Measure.restrict_mono_set volume hKΩ

theorem exists_eLpNorm_convolution_mollifierEps_sub_le
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {G : E → ℝ} (hG : MemLp G p (volume : Measure E))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
      eLpNorm (fun x =>
        (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps (d := d) hδ) x - G x)
        p volume ≤ ε := by
  classical
  have hG_aem : AEStronglyMeasurable G volume := hG.aestronglyMeasurable
  set g : E → ℝ := hG_aem.mk G with hg_def
  have hg_sm : StronglyMeasurable g := hG_aem.stronglyMeasurable_mk
  have hg_meas : Measurable g := hg_sm.measurable
  have hG_eq_g : G =ᵐ[volume] g := hG_aem.ae_eq_mk
  have hg_memLp : MemLp g p (volume : Measure E) :=
    (memLp_congr_ae hG_eq_g).mp hG
  have hg_local : LocallyIntegrable g (volume : Measure E) := hg_memLp.locallyIntegrable hp_one
  have h_trans : Filter.Tendsto (fun h : E => eLpNorm
      (fun x => g (x - h) - g x) p volume) (𝓝 0) (𝓝 0) :=
    tendsto_eLpNorm_translate_sub_of_memLp (d := d) hp_one hp_top hg_memLp
  rw [ENNReal.tendsto_nhds_zero] at h_trans
  have h_event := h_trans ε hε
  rw [Metric.eventually_nhds_iff_ball] at h_event
  obtain ⟨δ₀, hδ₀_pos, hδ₀_event⟩ := h_event
  refine ⟨δ₀ / 2, by linarith, ?_⟩
  intro δ hδ_pos hδ_le
  have hδ_lt : δ < δ₀ := by linarith
  set η : E → ℝ := mollifierEps (d := d) hδ_pos with hη_def
  have h_FK := eLpNorm_convolution_sub_le_of_ae_translation_bound
    (η := η) (u := g) (T := ε) (p := p) hp_one hp_top
    (mollifierEps_continuous (d := d) hδ_pos)
    (mollifierEps_compactSupport (d := d) hδ_pos)
    (mollifierEps_nonneg (d := d) hδ_pos)
    (mollifierEps_integral_eq_one (d := d) hδ_pos)
    hg_meas hg_local
    (hT_le := by
      refine Filter.Eventually.of_forall ?_
      intro s hs_ne_zero
      have hs_support : s ∈ Function.support η := Function.mem_support.mpr hs_ne_zero
      have hs_ball : s ∈ Metric.closedBall (0 : E) δ :=
        mollifierEps_support_subset_closedBall_eps hδ_pos hs_support
      have hs_norm : ‖s‖ ≤ δ := by
        rw [Metric.mem_closedBall, dist_zero_right] at hs_ball
        exact hs_ball
      have hs_lt : ‖s‖ < δ₀ := lt_of_le_of_lt hs_norm hδ_lt
      have hs_in_ball : s ∈ Metric.ball (0 : E) δ₀ := by
        rw [Metric.mem_ball, dist_zero_right]
        exact hs_lt
      exact hδ₀_event s hs_in_ball)
  have h_trans_convergence : (fun x => (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x - G x)
      =ᵐ[(volume : Measure E)]
      (fun x => (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x - g x) := by
    have h_pointwise_left : ∀ x, (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x =
        (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) x :=
      fun x => convolution_lsmul_comm (d := d) G η x
    have h_pointwise_left_g : ∀ x, (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x =
        (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x :=
      fun x => convolution_lsmul_comm (d := d) g η x
    have h_ae_convergence : ∀ x : E, (G ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x =
        (g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x :=
      fun x => convolution_lsmul_ae_eq hG_eq_g x
    filter_upwards [hG_eq_g] with x hx
    rw [h_ae_convergence x, h_pointwise_left_g x, hx]
  rw [eLpNorm_congr_ae h_trans_convergence]
  exact h_FK

private theorem iterWeakPartial_sub_ae
    {j : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (β : Fin j → Fin d) {u v : E → ℝ}
    (hu : MemWkp (d := d) j p u Ω) (hv : MemWkp (d := d) j p v Ω) :
    iterWeakPartial (d := d) p j β (fun x => u x - v x) Ω
      =ᵐ[volume.restrict Ω]
      (fun x => iterWeakPartial (d := d) p j β u Ω x -
        iterWeakPartial (d := d) p j β v Ω x) := by
  classical
  have h_neg_v_W : MemWkp (d := d) j p (fun x => -v x) Ω :=
    MemWkp.neg (d := d) hp hΩ hv
  have h_add :=
    iterWeakPartial_add_ae (d := d) hp hΩ β hu h_neg_v_W
  have h_neg : iterWeakPartial (d := d) p j β (fun x => -v x) Ω
      =ᵐ[volume.restrict Ω]
      (fun x => -iterWeakPartial (d := d) p j β v Ω x) := by
    have h_smul := iterWeakPartial_const_smul_ae (d := d) hp hΩ β hv (-1 : ℝ)
    have h_eq : (fun x => (-1 : ℝ) * v x) = (fun x => -v x) := by
      funext x; ring
    rw [h_eq] at h_smul
    have h_eq2 : (fun x => (-1 : ℝ) * iterWeakPartial (d := d) p j β v Ω x) =
        (fun x => -iterWeakPartial (d := d) p j β v Ω x) := by
      funext x; ring
    rw [h_eq2] at h_smul
    exact h_smul
  have h_eq_sub : (fun x => u x + (-v x)) = (fun x => u x - v x) := by
    funext x; ring
  rw [h_eq_sub] at h_add
  refine h_add.trans ?_
  filter_upwards [h_neg] with x hx
  rw [hx]; ring

theorem iterWeakPartial_smooth_ae_eq_iterClassicalPartial
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ_open : IsOpen Ω) :
    ∀ (j : ℕ) (β : Fin j → Fin d) {ψ : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      iterWeakPartial (d := d) p j β ψ Ω
        =ᵐ[volume.restrict Ω] iterClassicalPartial (d := d) j β ψ := by
  intro j
  induction j with
  | zero =>
      intro β ψ _ _ _
      simp [iterWeakPartial_zero, iterClassicalPartial_zero]
  | succ j ih =>
      intro β ψ hψ_smooth hψ_compact hψ_support
      rw [iterWeakPartial_succ, iterClassicalPartial_succ]
      have hψ_W1p : Sobolev.Euclidean.MemW1p p ψ Ω := by
        have hψ_Wk : MemWkp (d := d) 1 p ψ Ω :=
          MemWkp_of_smooth_compactSupport (d := d) hΩ_open hψ_smooth hψ_compact hψ_support hp 1
        rwa [MemWkp.one_iff_memW1p] at hψ_Wk
      have h_ae := chosenWeakPartial_smooth_ae_eq (d := d) hp hΩ_open hψ_smooth hψ_W1p (β 0)
      have h_classical_smooth : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single (β 0) 1)) :=
        (hψ_smooth.fderiv_right (m := (⊤ : ℕ∞))
          (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).clm_apply
            contDiff_const
      have h_classical_compact : HasCompactSupport
          (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single (β 0) 1)) :=
        hψ_compact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single (β 0) 1)
      have h_classical_support :
          tsupport (fun x => (fderiv ℝ ψ x) (EuclideanSpace.single (β 0) 1)) ⊆ Ω :=
        (tsupport_fderiv_apply_subset (𝕜 := ℝ) (EuclideanSpace.single (β 0) 1)).trans hψ_support
      have h_ih := ih (fun i : Fin j => β i.succ)
        h_classical_smooth h_classical_compact h_classical_support
      have h_iter_congr := iterWeakPartial_ae_congr (d := d) hp hΩ_open j
        (fun i : Fin j => β i.succ) h_ae
      exact h_iter_congr.trans h_ih

theorem MemWkp.exists_smooth_compactSupport_approx
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ_open : IsOpen Ω)
    (k : ℕ) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : MemWkp k p u Ω)
    (hu_compactSupport : HasCompactSupport u) (hu_support : tsupport u ⊆ Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧
      iteratedWeakSobolevNorm k p (fun x => u x - φ x) Ω ≤ ENNReal.ofReal ε := by
  classical
  set K : Set E := tsupport u with hK_def
  have hK_compact : IsCompact K := hu_compactSupport
  have hK_closed : IsClosed K := isClosed_tsupport u
  have hKΩ : K ⊆ Ω := hu_support
  have hu_support_K : tsupport u ⊆ K := subset_refl _
  obtain ⟨δ_max, hδ_max_pos, hδ_max_subset⟩ :=
    hK_compact.exists_cthickening_subset_open hΩ_open hKΩ
  set N : ℕ := ∑ j ∈ Finset.range (k + 1), (Fintype.card (Fin j → Fin d)) with hN_def
  have hN_pos : 0 < N + 1 := by simp [hN_def]
  set εPer : ℝ := ε / (N + 1) with hεPer_def
  have hεPer_pos : 0 < εPer := by
    refine div_pos hε ?_
    exact_mod_cast hN_pos
  have h_pick : ∀ (j : ℕ) (hjk : j ≤ k) (β : Fin j → Fin d),
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
        eLpNorm (fun x =>
          (iteratedZeroExtension (d := d) p Ω K j β u
              ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps (d := d) hδ) x
            - iteratedZeroExtension (d := d) p Ω K j β u x) p volume
          ≤ ENNReal.ofReal εPer := by
    intro j hjk β
    have h_memLp : MemLp (iteratedZeroExtension (d := d) p Ω K j β u) p
        (volume : Measure E) :=
      iteratedZeroExtension_memLp_volume (d := d) hp_one hΩ_open hK_closed hKΩ
        j k hjk β hu hu_support_K
    exact exists_eLpNorm_convolution_mollifierEps_sub_le (d := d) hp_one hp_top
      h_memLp (ENNReal.ofReal_pos.mpr hεPer_pos)
  let Idx : Type := Σ j : Fin (k + 1), Fin (j.val) → Fin d
  have : Fintype Idx := inferInstance
  let i₀ : Idx := ⟨⟨0, Nat.zero_lt_succ k⟩, fun i => i.elim0⟩
  have huniv : (Finset.univ : Finset Idx).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  let δ_fun : Idx → ℝ := fun i =>
    Classical.choose (h_pick i.1.val (Nat.le_of_lt_succ i.1.isLt) i.2)
  have hδ_fun_pos : ∀ i, 0 < δ_fun i := fun i =>
    (Classical.choose_spec (h_pick i.1.val (Nat.le_of_lt_succ i.1.isLt) i.2)).1
  have hδ_fun_spec : ∀ (i : Idx) (δ : ℝ) (hδ : 0 < δ), δ ≤ δ_fun i →
      eLpNorm (fun x =>
        (iteratedZeroExtension (d := d) p Ω K i.1.val i.2 u
            ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps (d := d) hδ) x
          - iteratedZeroExtension (d := d) p Ω K i.1.val i.2 u x) p volume
        ≤ ENNReal.ofReal εPer := fun i δ hδ h_le =>
    (Classical.choose_spec (h_pick i.1.val (Nat.le_of_lt_succ i.1.isLt) i.2)).2 δ hδ h_le
  let δ : ℝ := (Finset.univ : Finset Idx).inf' huniv
    (fun i => min (δ_fun i) (δ_max / 2))
  have hδ_pos : 0 < δ := by
    rw [show δ = (Finset.univ : Finset Idx).inf'
      huniv
      (fun i => min (δ_fun i) (δ_max / 2)) from rfl]
    apply (Finset.lt_inf'_iff huniv).2
    intro i _
    exact lt_min (hδ_fun_pos i) (by linarith)
  have hδ_le_fun : ∀ i : Idx, δ ≤ δ_fun i := by
    intro i
    refine le_trans (Finset.inf'_le _ ?_) (min_le_left _ _)
    exact Finset.mem_univ _
  have hδ_le_half : δ ≤ δ_max / 2 := by
    have h_some : (⟨⟨0, Nat.zero_lt_succ k⟩, fun i => i.elim0⟩ : Idx) ∈
        (Finset.univ : Finset Idx) := Finset.mem_univ _
    refine le_trans (Finset.inf'_le _ h_some) (min_le_right _ _)
  have hδ_lt_max : δ < δ_max := by
    refine lt_of_le_of_lt hδ_le_half ?_
    linarith
  set η : E → ℝ := mollifierEps (d := d) hδ_pos with hη_def
  set φ : E → ℝ := u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η with hφ_def
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    have h_local : LocallyIntegrable u (volume : Measure E) := by
      have h_uLp : MemLp u p volume := by
        have heq : u = Ω.indicator u := by
          funext x
          by_cases hx : x ∈ Ω
          · rw [Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hx,
              Sobolev.Euclidean.zero_outside_of_tsupport_subset (Ω := Ω) hu_support hx]
        rw [heq, memLp_indicator_iff_restrict hΩ_open.measurableSet]
        exact hu.memLp
      exact h_uLp.locallyIntegrable hp_one
    exact contDiff_convolution_mollifierEps (d := d) h_local hδ_pos
  have hφ_compact : HasCompactSupport φ :=
    hasCompactSupport_convolution_mollifierEps (d := d) hu_compactSupport hδ_pos
  have hφ_support : tsupport φ ⊆ Ω := by
    refine subset_trans ?_ hδ_max_subset
    have : tsupport φ ⊆ Metric.cthickening δ K :=
      tsupport_convolution_mollifierEps_subset_thickening (d := d) hδ_pos
    refine subset_trans this ?_
    exact Metric.cthickening_mono (le_of_lt hδ_lt_max) K
  have hφ_W : MemWkp (d := d) k p φ Ω :=
    MemWkp_of_smooth_compactSupport (d := d) hΩ_open hφ_smooth hφ_compact hφ_support hp_one k
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_support, ?_⟩
  have huφ_W : MemWkp (d := d) k p (fun x => u x - φ x) Ω :=
    MemWkp.sub (d := d) hp_one hΩ_open hu hφ_W
  unfold iteratedWeakSobolevNorm
  refine (Finset.sum_le_sum (g := fun j =>
    ∑ _β : Fin j → Fin d, (ENNReal.ofReal εPer : ℝ≥0∞))
    (fun j hj => ?_)).trans ?_
  · have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    refine Finset.sum_le_sum (fun β _ => ?_)
    have hjβ_le : eLpNorm (iterWeakPartial (d := d) p j β
        (fun x => u x - φ x) Ω) p (volume.restrict Ω) ≤ ENNReal.ofReal εPer := by
      have h_uWj : MemWkp (d := d) j p u Ω := MemWkp.le_of_le hjk hu
      have h_φWj : MemWkp (d := d) j p φ Ω := MemWkp.le_of_le hjk hφ_W
      have h_sub_ae := iterWeakPartial_sub_ae (d := d) hp_one hΩ_open β h_uWj h_φWj
      have hG_ae := iteratedZeroExtension_ae_eq_iterWeakPartial (d := d) hp_one hΩ_open
        hK_closed j k hjk β hu hu_support_K
      have h_classical_ae := iterWeakPartial_smooth_ae_eq_iterClassicalPartial (d := d)
        hp_one hΩ_open j β hφ_smooth hφ_compact hφ_support
      have h_step_b :
          ∀ x : E,
            iterClassicalPartial (d := d) j β φ x =
              (iteratedZeroExtension (d := d) p Ω K j β u
                ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x := fun x =>
        iterClassicalPartial_convolution_eq_convolution_iteratedZeroExtension
          (d := d) hp_one hΩ_open hK_compact hK_closed hKΩ
          (mollifierEps_smooth (d := d) hδ_pos)
          (mollifierEps_compactSupport (d := d) hδ_pos)
          j k hjk β hu hu_compactSupport hu_support_K x
      have h_combined : iterWeakPartial (d := d) p j β
            (fun x => u x - φ x) Ω
          =ᵐ[volume.restrict Ω]
          (fun x => iteratedZeroExtension (d := d) p Ω K j β u x -
              (iteratedZeroExtension (d := d) p Ω K j β u
                ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x) := by
        refine h_sub_ae.trans ?_
        filter_upwards [hG_ae, h_classical_ae] with x hG hC
        rw [hG, hC, h_step_b]
      rw [eLpNorm_congr_ae h_combined]
      refine le_trans (eLpNorm_mono_measure (μ := volume) _ Measure.restrict_le_self) ?_
      have h_neg :
          (fun x => iteratedZeroExtension (d := d) p Ω K j β u x -
              (iteratedZeroExtension (d := d) p Ω K j β u
                ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x) =
            -(fun x => (iteratedZeroExtension (d := d) p Ω K j β u
                ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x -
              iteratedZeroExtension (d := d) p Ω K j β u x) := by
        funext x
        simp only [Pi.neg_apply]
        ring
      rw [h_neg, eLpNorm_neg]
      have h_idx := hδ_fun_spec ⟨⟨j, Nat.lt_succ_of_le hjk⟩, β⟩ δ hδ_pos
        (hδ_le_fun ⟨⟨j, Nat.lt_succ_of_le hjk⟩, β⟩)
      exact h_idx
    exact hjβ_le
  · have h_card_sum : ∑ j ∈ Finset.range (k + 1), ∑ _β : Fin j → Fin d,
        (ENNReal.ofReal εPer : ℝ≥0∞) = (N : ℝ≥0∞) * ENNReal.ofReal εPer := by
      have h_inner : ∀ j ∈ Finset.range (k + 1),
          (∑ _β : Fin j → Fin d, (ENNReal.ofReal εPer : ℝ≥0∞)) =
            (Fintype.card (Fin j → Fin d) : ℝ≥0∞) * ENNReal.ofReal εPer := by
        intro j _
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [Finset.sum_congr rfl h_inner]
      rw [← Finset.sum_mul]
      congr 1
      rw [hN_def]
      push_cast
      rfl
    rw [h_card_sum]
    have h_real_eq : (N : ℝ≥0∞) * ENNReal.ofReal εPer =
        ENNReal.ofReal (N * εPer) := by
      rw [show (N : ℝ≥0∞) = ENNReal.ofReal N from
        (ENNReal.ofReal_natCast N).symm]
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
    rw [h_real_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hεPer_def]
    have h_eq_div : (N : ℝ) * (ε / ((N : ℝ) + 1)) = (N : ℝ) * ε / ((N : ℝ) + 1) := by
      ring
    rw [h_eq_div]
    have hN1_pos : (0 : ℝ) < (N : ℝ) + 1 := by exact_mod_cast hN_pos
    rw [div_le_iff₀ hN1_pos]
    nlinarith [hε.le, Nat.cast_nonneg N (α := ℝ)]

end Euclidean
end Sobolev
