module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.SourceExtension
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform chart-transition estimates for local mollifications

Hirsch, *Differential Topology*, Chapter 2, §2, Theorem 2.6, p. 49:
transfer the approximation of each compactly supported localized function to
all chart pieces. Mathlib's `norm_iteratedFDerivWithin_comp_le` controls the
full second jet of a composition, including the term containing the first
error jet multiplied by the second transition jet. The partial chart maps are
smooth on open overlaps, not necessarily outside their chart targets.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

-- The target-chart piece and each source-supported overlap have compact images.
-- Neither lemma
-- assumes smoothness of a partial chart map outside its open domain.
omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M] in
private theorem compact_chart_piece_image
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (k : cover.ι) :
    IsCompact ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)).symm ''
      cover.piece k) := by
  apply (cover.isCompact_piece k).image_of_continuousOn
  exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
    (cover.base k)).mono (cover.piece_in_target k)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [CompactSpace M] in
private theorem compact_support_overlap_in_chart
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    {f : M → ℝ} (hcompact : IsCompact (tsupport f)) (i k : cover.ι)
    (hsupport : tsupport f ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).source) :
    IsCompact ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)) ''
      (tsupport f ∩ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)).symm ''
        cover.piece k))) := by
  have hcover : IsCompact ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      (cover.base k)).symm '' cover.piece k) := compact_chart_piece_image cover k
  have hoverlap : IsCompact (tsupport f ∩
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base k)).symm ''
        cover.piece k)) := hcompact.inter hcover
  apply hoverlap.image_of_continuousOn
  apply (continuousOn_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
    (cover.base i)).mono
  intro x hx
  exact hsupport hx.1

private def chart_overlap {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (i k : L.cover.ι) : Set (EuclideanSpace ℂ (Fin n)) :=
  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).target ∩
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm ⁻¹'
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).source

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M] in
private theorem chart_overlap_open {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (i k : L.cover.ι) : IsOpen (chart_overlap L i k) := by
  dsimp [chart_overlap]
  exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
    (L.cover.base k)).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (L.cover.base k))
      (isOpen_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (L.cover.base i))

omit [T2Space M] [CompactSpace M] in
private theorem chart_transition_contDiffOn {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (i k : L.cover.ι) :
    ContDiffOn ℝ 2
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm)
      (chart_overlap L i k) := by
  let ci := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)
  let ck := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)
  have hSymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (∞ : ℕ∞ω) ck.symm ck.target :=
    contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (n := (∞ : ℕ∞ω)) (L.cover.base k)
  have hChart : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (∞ : ℕ∞ω) ci
      (chartAt (EuclideanSpace ℂ (Fin n)) (L.cover.base i)).source :=
    contMDiffOn_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (n := (∞ : ℕ∞ω)) (x := L.cover.base i)
  have hsymmU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (∞ : ℕ∞ω) ck.symm (chart_overlap L i k) :=
    hSymm.mono (by intro z hz; exact hz.1)
  have hcomp : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (∞ : ℕ∞ω) (ci ∘ ck.symm)
      (chart_overlap L i k) := by
    exact hChart.comp hsymmU (by
      intro z hz
      simpa [ci, ck, extChartAt_source] using hz.2)
  exact hcomp.contDiffOn.of_le
    (inferInstance : ENat.LEInfty (2 : ℕ∞ω)).out

-- Ordinary Fréchet chain rule on an open overlap. The second term retains the
-- derivative of the source error multiplied by the second transition derivative.
private theorem second_fderivWithin_comp_formula
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {g : F → ℝ} {x : E}
    (hs : IsOpen s) (hx : x ∈ s)
    (hf : DifferentiableOn ℝ f s) (hg : Differentiable ℝ g)
    (hp : DifferentiableWithinAt ℝ (fun y => fderiv ℝ g (f y)) s x)
    (hq : DifferentiableWithinAt ℝ (fderivWithin ℝ f s) s x) :
    fderivWithin ℝ (fun y => fderivWithin ℝ (g ∘ f) s y) s x =
      (ContinuousLinearMap.compL ℝ E F ℝ).precompR E
        (fderiv ℝ g (f x)) (fderivWithin ℝ (fderivWithin ℝ f s) s x) +
      (ContinuousLinearMap.compL ℝ E F ℝ).precompL E
        (fderivWithin ℝ (fun y => fderiv ℝ g (f y)) s x) (fderivWithin ℝ f s x) := by
  let p : E → F →L[ℝ] ℝ := fun y => fderiv ℝ g (f y)
  let q : E → E →L[ℝ] F := fun y => fderivWithin ℝ f s y
  have hcomp (y : E) (hy : y ∈ s) :
      fderivWithin ℝ (g ∘ f) s y = (p y).comp (q y) := by
    have hgy : DifferentiableWithinAt ℝ g Set.univ (f y) :=
      hg.differentiableAt.differentiableWithinAt
    simpa [p, q, fderivWithin_univ] using
      (fderivWithin_comp (x := y) (g := g) (f := f) (s := s) (t := Set.univ)
        hgy (hf y hy) (by simp) (hs.uniqueDiffOn.uniqueDiffWithinAt hy))
  have hEq : Set.EqOn (fun y => fderivWithin ℝ (g ∘ f) s y)
      (fun y => (ContinuousLinearMap.compL ℝ E F ℝ) (p y) (q y)) s := by
    intro y hy
    simpa [p, q, fderivWithin_univ] using hcomp y hy
  have hEq' := fderivWithin_congr (𝕜 := ℝ) hEq (hcomp x hx)
  rw [hEq']
  have hp' : DifferentiableWithinAt ℝ p s x := by simpa [p] using hp
  have hq' : DifferentiableWithinAt ℝ q s x := by simpa [q] using hq
  simpa [p, q] using ContinuousLinearMap.fderivWithin_of_bilinear
    (ContinuousLinearMap.compL ℝ E F ℝ) hp' hq'
    (hs.uniqueDiffOn.uniqueDiffWithinAt hx)

private theorem norm_iteratedFDerivWithin_two_comp_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {g : F → ℝ} {x : E} {δ C D : ℝ}
    (hs : IsOpen s) (hx : x ∈ s)
    (hf : DifferentiableOn ℝ f s) (hg : Differentiable ℝ g)
    (hgp : DifferentiableAt ℝ (fderiv ℝ g) (f x))
    (hp : DifferentiableWithinAt ℝ (fun y => fderiv ℝ g (f y)) s x)
    (hq : DifferentiableWithinAt ℝ (fderivWithin ℝ f s) s x)
    (hg1 : ‖fderiv ℝ g (f x)‖ ≤ δ)
    (hg2 : ‖fderiv ℝ (fderiv ℝ g) (f x)‖ ≤ δ)
    (hf1 : ‖fderivWithin ℝ f s x‖ ≤ C)
    (hf2 : ‖fderivWithin ℝ (fderivWithin ℝ f s) s x‖ ≤ D) :
    ‖iteratedFDerivWithin ℝ 2 (g ∘ f) s x‖ ≤ δ * C ^ 2 + δ * D := by
  have hformula := second_fderivWithin_comp_formula hs hx hf hg hp hq
  have hpderiv : fderivWithin ℝ (fun y => fderiv ℝ g (f y)) s x =
      (fderiv ℝ (fderiv ℝ g) (f x)).comp (fderivWithin ℝ f s x) := by
    have hgy : DifferentiableWithinAt ℝ (fderiv ℝ g) Set.univ (f x) :=
      hgp.differentiableWithinAt
    simpa [fderivWithin_univ, Function.comp_def] using
      (fderivWithin_comp (x := x) (g := fderiv ℝ g) (f := f) (s := s) (t := Set.univ)
        hgy (hf x hx) (by simp) (hs.uniqueDiffOn.uniqueDiffWithinAt hx))
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hg1
  have hC : 0 ≤ C := (norm_nonneg _).trans hf1
  have hD : 0 ≤ D := (norm_nonneg _).trans hf2
  have hR (u : F →L[ℝ] ℝ) (v : E →L[ℝ] E →L[ℝ] F) :
      ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompR E u v‖ ≤ ‖u‖ * ‖v‖ := by
    calc
      ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompR E u v‖ ≤
          ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompR E u‖ * ‖v‖ :=
        (ContinuousLinearMap.precompR E (ContinuousLinearMap.compL ℝ E F ℝ) u).le_opNorm v
      _ ≤ (‖(ContinuousLinearMap.compL ℝ E F ℝ).precompR E‖ * ‖u‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (1 * ‖u‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right
            ((ContinuousLinearMap.norm_precompR_le E
              (ContinuousLinearMap.compL ℝ E F ℝ)).trans
                (ContinuousLinearMap.norm_compL_le ℝ E F ℝ)) (norm_nonneg _)
        · exact norm_nonneg _
      _ = ‖u‖ * ‖v‖ := by ring
  have hL (u : E →L[ℝ] F →L[ℝ] ℝ) (v : E →L[ℝ] F) :
      ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompL E u v‖ ≤ ‖u‖ * ‖v‖ := by
    calc
      ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompL E u v‖ ≤
          ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompL E u‖ * ‖v‖ :=
        (ContinuousLinearMap.precompL E (ContinuousLinearMap.compL ℝ E F ℝ) u).le_opNorm v
      _ ≤ (‖(ContinuousLinearMap.compL ℝ E F ℝ).precompL E‖ * ‖u‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (1 * ‖u‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right
            ((ContinuousLinearMap.norm_precompL_le E
              (ContinuousLinearMap.compL ℝ E F ℝ)).trans
                (ContinuousLinearMap.norm_compL_le ℝ E F ℝ)) (norm_nonneg _)
        · exact norm_nonneg _
      _ = ‖u‖ * ‖v‖ := by ring
  have hpbound : ‖fderivWithin ℝ (fun y => fderiv ℝ g (f y)) s x‖ ≤ δ * C := by
    rw [hpderiv]
    calc
      ‖(fderiv ℝ (fderiv ℝ g) (f x)).comp (fderivWithin ℝ f s x)‖ ≤
          ‖fderiv ℝ (fderiv ℝ g) (f x)‖ * ‖fderivWithin ℝ f s x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ δ * C := mul_le_mul hg2 hf1 (norm_nonneg _) hδ
  have hsecond :
      ‖fderivWithin ℝ (fun y => fderivWithin ℝ (g ∘ f) s y) s x‖ ≤
        δ * D + (δ * C) * C := by
    rw [hformula]
    calc
      ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompR E
            (fderiv ℝ g (f x)) (fderivWithin ℝ (fderivWithin ℝ f s) s x) +
          (ContinuousLinearMap.compL ℝ E F ℝ).precompL E
            (fderivWithin ℝ (fun y => fderiv ℝ g (f y)) s x) (fderivWithin ℝ f s x)‖
          ≤ ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompR E
              (fderiv ℝ g (f x)) (fderivWithin ℝ (fderivWithin ℝ f s) s x)‖ +
            ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompL E
              (fderivWithin ℝ (fun y => fderiv ℝ g (f y)) s x) (fderivWithin ℝ f s x)‖ :=
            norm_add_le _ _
      _ ≤ δ * D + (δ * C) * C := by
        apply add_le_add
        · calc
            ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompR E
                (fderiv ℝ g (f x)) (fderivWithin ℝ (fderivWithin ℝ f s) s x)‖ ≤
                ‖fderiv ℝ g (f x)‖ * ‖fderivWithin ℝ (fderivWithin ℝ f s) s x‖ := hR _ _
            _ ≤ δ * D := mul_le_mul hg1 hf2 (norm_nonneg _) hδ
        · calc
            ‖(ContinuousLinearMap.compL ℝ E F ℝ).precompL E
                (fderivWithin ℝ (fun y => fderiv ℝ g (f y)) s x) (fderivWithin ℝ f s x)‖ ≤
                ‖fderivWithin ℝ (fun y => fderiv ℝ g (f y)) s x‖ *
                  ‖fderivWithin ℝ f s x‖ := hL _ _
            _ ≤ (δ * C) * C := mul_le_mul hpbound hf1 (norm_nonneg _)
              (mul_nonneg hδ hC)
  calc
    ‖iteratedFDerivWithin ℝ 2 (g ∘ f) s x‖ =
        ‖iteratedFDerivWithin ℝ 1 (fun y => fderivWithin ℝ (g ∘ f) s y) s x‖ := by
      symm
      exact norm_iteratedFDerivWithin_fderivWithin hs.uniqueDiffOn hx
    _ = ‖fderivWithin ℝ (fun y => fderivWithin ℝ (g ∘ f) s y) s x‖ := by
      rw [norm_iteratedFDerivWithin_one _ (hs.uniqueDiffOn.uniqueDiffWithinAt hx)]
    _ ≤ δ * D + (δ * C) * C := hsecond
    _ = δ * C ^ 2 + δ * D := by ring

private theorem norm_iteratedFDerivWithin_one_comp_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {f : E → F} {g : F → ℝ} {x : E} {δ C : ℝ}
    (hs : IsOpen s) (hx : x ∈ s)
    (hf : DifferentiableOn ℝ f s) (hg : Differentiable ℝ g)
    (hg1 : ‖fderiv ℝ g (f x)‖ ≤ δ)
    (hf1 : ‖fderivWithin ℝ f s x‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ 1 (g ∘ f) s x‖ ≤ δ * C := by
  have hcomp : fderivWithin ℝ (g ∘ f) s x =
      (fderiv ℝ g (f x)).comp (fderivWithin ℝ f s x) := by
    have hgy : DifferentiableWithinAt ℝ g Set.univ (f x) :=
      hg.differentiableAt.differentiableWithinAt
    simpa [fderivWithin_univ] using
      (fderivWithin_comp (x := x) (g := g) (f := f) (s := s) (t := Set.univ)
        hgy (hf x hx) (by simp) (hs.uniqueDiffOn.uniqueDiffWithinAt hx))
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hg1
  calc
    ‖iteratedFDerivWithin ℝ 1 (g ∘ f) s x‖ =
        ‖fderivWithin ℝ (g ∘ f) s x‖ :=
      norm_iteratedFDerivWithin_one _ (hs.uniqueDiffOn.uniqueDiffWithinAt hx)
    _ = ‖(fderiv ℝ g (f x)).comp (fderivWithin ℝ f s x)‖ := by rw [hcomp]
    _ ≤ ‖fderiv ℝ g (f x)‖ * ‖fderivWithin ℝ f s x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ δ * C := mul_le_mul hg1 hf1 (norm_nonneg _) hδ

-- Each zero extension has its support in the image of the fixed Euclidean
-- support bound. This compact set is independent of the convolution index.
omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [CompactSpace M] in
private theorem approximation_tsupport_compact
    {φ : M → ℝ} (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A)
    (i : L.cover.ι) (j : ℕ) :
    IsCompact (tsupport (S.approximation i j)) := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)
  let K : Set M := c.symm '' (A i).supportBound
  have hK : IsCompact K := by
    dsimp [K, c]
    exact (A i).supportBound_compact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
        (L.cover.base i)).mono (A i).supportBound_subset)
  have hKclosed : IsClosed K := hK.isClosed
  have hsupp : Function.support (S.approximation i j) ⊆ K := by
    intro x hx
    change S.approximation i j x ≠ 0 at hx
    have hxs : x ∈ c.source := by
      by_contra hxs
      have hnot : x ∉ tsupport (S.approximation i j) :=
        fun ht => hxs (S.support_in_source i j ht)
      exact hnot (subset_closure (Function.mem_support.mpr hx))
    have hxt : c x ∈ c.target := c.map_source hxs
    have heq := S.coordinate_eq i j (c x) hxt
    have hzsup : c x ∈ Function.support ((A i).approximation j) := by
      apply Function.mem_support.mpr
      rw [← heq, c.left_inv hxs]
      exact hx
    have hzb : c x ∈ (A i).supportBound :=
      (A i).support_in_bound j (subset_tsupport _ hzsup)
    exact ⟨c x, hzb, c.left_inv hxs⟩
  have htsupp : tsupport (S.approximation i j) ⊆ K := by
    change closure (Function.support (S.approximation i j)) ⊆ K
    exact (closure_mono hsupp).trans hKclosed.closure_subset
  exact hK.of_isClosed_subset (isClosed_tsupport _) htsupp

private def fixed_error_support {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (i : L.cover.ι) : Set M :=
  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).symm ''
      (A i).supportBound ∪ tsupport (L.localizedFunction i)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] in
private theorem fixed_error_support_compact {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (i : L.cover.ι) : IsCompact (fixed_error_support L A i) := by
  apply IsCompact.union
  · exact (A i).supportBound_compact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) )
        (L.cover.base i)).mono (A i).supportBound_subset)
  · exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
      (Set.subset_univ _)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M] in
private theorem fixed_error_support_subset_source {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (i : L.cover.ι) :
    fixed_error_support L A i ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).source := by
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩ | hx
  · exact (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).map_target
      ((A i).supportBound_subset hz)
  · exact L.localizedSupportInSource i hx

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [CompactSpace M] in
private theorem approximation_tsupport_subset_fixed_image {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A)
    (i : L.cover.ι) (j : ℕ) :
    tsupport (S.approximation i j) ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).symm ''
        (A i).supportBound := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)
  let K : Set M := c.symm '' (A i).supportBound
  have hK : IsCompact K := by
    dsimp [K, c]
    exact (A i).supportBound_compact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
        (L.cover.base i)).mono (A i).supportBound_subset)
  have hKclosed : IsClosed K := hK.isClosed
  have hsupp : Function.support (S.approximation i j) ⊆ K := by
    intro x hx
    change S.approximation i j x ≠ 0 at hx
    have hxs : x ∈ c.source := by
      by_contra hxs
      have hnot : x ∉ tsupport (S.approximation i j) :=
        fun ht => hxs (S.support_in_source i j ht)
      exact hnot (subset_closure (Function.mem_support.mpr hx))
    have hxt : c x ∈ c.target := c.map_source hxs
    have heq := S.coordinate_eq i j (c x) hxt
    have hzsup : c x ∈ Function.support ((A i).approximation j) := by
      apply Function.mem_support.mpr
      rw [← heq, c.left_inv hxs]
      exact hx
    have hzb : c x ∈ (A i).supportBound :=
      (A i).support_in_bound j (subset_tsupport _ hzsup)
    exact ⟨c x, hzb, c.left_inv hxs⟩
  have htsupp : tsupport (S.approximation i j) ⊆ K := by
    change closure (Function.support (S.approximation i j)) ⊆ K
    exact (closure_mono hsupp).trans hKclosed.closure_subset
  simpa [K, c] using htsupp

private def chart_transition_piece_coordinates {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (i k : L.cover.ι) : Set (EuclideanSpace ℂ (Fin n)) :=
  let ck := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)
  ck '' (fixed_error_support L A i ∩ ck.symm '' L.cover.piece k)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem chart_transition_piece_coordinates_compact {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (i k : L.cover.ι) : IsCompact (chart_transition_piece_coordinates L A i k) := by
  let ck := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)
  have hK : IsCompact (fixed_error_support L A i) := fixed_error_support_compact L A i
  have hP : IsCompact (ck.symm '' L.cover.piece k) := compact_chart_piece_image L.cover k
  have hKP : IsCompact (fixed_error_support L A i ∩ ck.symm '' L.cover.piece k) := hK.inter hP
  apply hKP.image_of_continuousOn
  apply (continuousOn_extChartAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
    (L.cover.base k)).mono
  rintro x ⟨_, ⟨z, hz, rfl⟩⟩
  exact ck.map_target (L.cover.piece_in_target k hz)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M] in
private theorem chart_transition_piece_coordinates_subset_overlap {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (i k : L.cover.ι) :
    chart_transition_piece_coordinates L A i k ⊆ chart_overlap L i k := by
  let ci := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)
  let ck := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)
  intro z hz
  rcases hz with ⟨x, ⟨hxK, y, hy, rfl⟩, rfl⟩
  have hyT := L.cover.piece_in_target k hy
  have hySource : ck.symm y ∈ ck.source := ck.map_target hyT
  have hright : ck (ck.symm y) = y := ck.right_inv hyT
  rw [hright]
  constructor
  · exact hyT
  · change ck.symm y ∈ ci.source
    exact fixed_error_support_subset_source L A i hxK

private theorem transition_derivative_bounds_on_piece {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (i k : L.cover.ι) :
    ∃ C D : ℝ≥0, ∀ z ∈ chart_transition_piece_coordinates L A i k,
      ‖fderivWithin ℝ
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm)
          (chart_overlap L i k) z‖ ≤ C ∧
      ‖fderivWithin ℝ (fderivWithin ℝ
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm)
          (chart_overlap L i k)) (chart_overlap L i k) z‖ ≤ D := by
  classical
  let s := chart_overlap L i k
  let τ := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)) ∘
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm
  let K := chart_transition_piece_coordinates L A i k
  have hs : IsOpen s := chart_overlap_open L i k
  have hτ : ContDiffOn ℝ 2 τ s := by simpa [s, τ] using chart_transition_contDiffOn L i k
  have hKs : K ⊆ s := by
    simpa [K, s] using chart_transition_piece_coordinates_subset_overlap L A i k
  have hK : IsCompact K := by simpa [K] using chart_transition_piece_coordinates_compact L A i k
  have hcont1 : ContinuousOn (fun z => ‖iteratedFDerivWithin ℝ 1 τ s z‖) K :=
    (hτ.continuousOn_iteratedFDerivWithin (by norm_num) hs.uniqueDiffOn).norm.mono hKs
  have hcont2 : ContinuousOn (fun z => ‖iteratedFDerivWithin ℝ 2 τ s z‖) K :=
    (hτ.continuousOn_iteratedFDerivWithin (by norm_num) hs.uniqueDiffOn).norm.mono hKs
  obtain ⟨B, hB0, hB⟩ := (hK.bddAbove_image hcont1).exists_ge 0
  obtain ⟨D0, hD0, hD⟩ := (hK.bddAbove_image hcont2).exists_ge 0
  let C : ℝ≥0 := ⟨B, hB0⟩
  let D : ℝ≥0 := ⟨D0, hD0⟩
  refine ⟨C, D, fun z hz => ?_⟩
  have hCz : ‖iteratedFDerivWithin ℝ 1 τ s z‖ ≤ (C : ℝ) := by
    exact_mod_cast hB (‖iteratedFDerivWithin ℝ 1 τ s z‖) ⟨z, hz, rfl⟩
  have hDz : ‖iteratedFDerivWithin ℝ 2 τ s z‖ ≤ (D : ℝ) := by
    exact_mod_cast hD (‖iteratedFDerivWithin ℝ 2 τ s z‖) ⟨z, hz, rfl⟩
  have hzS := hKs hz
  constructor
  · rw [← norm_iteratedFDerivWithin_one τ (hs.uniqueDiffOn.uniqueDiffWithinAt hzS)]
    exact hCz
  · calc
      ‖fderivWithin ℝ (fderivWithin ℝ τ s) s z‖ =
          ‖iteratedFDerivWithin ℝ 1 (fderivWithin ℝ τ s) s z‖ := by
            symm
            exact norm_iteratedFDerivWithin_one _ (hs.uniqueDiffOn.uniqueDiffWithinAt hzS)
      _ = ‖iteratedFDerivWithin ℝ 2 τ s z‖ :=
          norm_iteratedFDerivWithin_fderivWithin hs.uniqueDiffOn hzS
      _ ≤ D := hDz

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M] in
private theorem chart_error_eq_source_transition {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A)
    (i k : L.cover.ι) (j : ℕ) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ chart_overlap L i k) :
    ((S.approximation i j - L.localizedFunction i) ∘
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm) z =
    ((A i).approximation j - L.localFunction i)
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i))
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm z)) := by
  let ci := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)
  let ck := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)
  have hx : ck.symm z ∈ ci.source := hz.2
  have hzTarget : ci (ck.symm z) ∈ ci.target := ci.map_source hx
  have hS : S.approximation i j (ck.symm z) =
      (A i).approximation j (ci (ck.symm z)) := by
    calc
      S.approximation i j (ck.symm z) =
          S.approximation i j (ci.symm (ci (ck.symm z))) := by rw [ci.left_inv hx]
      _ = (A i).approximation j (ci (ck.symm z)) :=
        S.coordinate_eq i j (ci (ck.symm z)) hzTarget
  have hL := L.coordinate_eq i (ck.symm z) hx
  change S.approximation i j (ck.symm z) - L.localizedFunction i (ck.symm z) =
    (A i).approximation j (ci (ck.symm z)) - L.localFunction i (ci (ck.symm z))
  rw [hS, hL]

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [CompactSpace M] in
private theorem chart_error_zero_eventually {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A)
    (i : L.cover.ι) (j : ℕ) {x : M}
    (hx : x ∉ fixed_error_support L A i) :
    (S.approximation i j - L.localizedFunction i) =ᶠ[𝓝 x] 0 := by
  have happrox : tsupport (S.approximation i j) ⊆ fixed_error_support L A i := by
    exact (approximation_tsupport_subset_fixed_image L A S i j).trans
      (Set.subset_union_left)
  have hA : S.approximation i j =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (happrox ht))
  have hL : L.localizedFunction i =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (Set.mem_union_right _ ht))
  filter_upwards [hA, hL] with y hyA hyL
  simp [hyA, hyL]

omit [CompactSpace M] in
private theorem chart_error_zero_jets_at {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A)
    (i k : L.cover.ι) (j r : ℕ) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).target)
    (hnot : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm z ∉
      fixed_error_support L A i) :
    iteratedFDeriv ℝ r
      ((S.approximation i j - L.localizedFunction i) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm) z = 0 := by
  have hzero := chart_error_zero_eventually L A S i j hnot
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm z :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      (L.cover.base k)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
          (L.cover.base k)).mem_nhds hz)
  have hcomp : (S.approximation i j - L.localizedFunction i) ∘
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm =ᶠ[𝓝 z]
      fun _ => 0 := by
    simpa [Function.comp_def] using hzero.comp_tendsto hsymm.continuousAt.tendsto
  have hderiv := (hcomp.iteratedFDeriv ℝ r).eq_of_nhds
  simpa using hderiv

omit [T2Space M] [CompactSpace M] in
private theorem chartwise_error_contDiffAt
    {φ : M → ℝ} (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A)
    (i : L.cover.ι) (j : ℕ) (k : L.cover.ι) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ L.cover.piece k) :
    ContDiffAt ℝ 2
      ((S.approximation i j - L.localizedFunction i) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm) z := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)
  have htop : (2 : ℕ∞ω) ≤ ∞ := by
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have herror : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
      (S.approximation i j - L.localizedFunction i) := by
    exact (S.smooth i j).of_le htop |>.sub (L.localizedC2 i)
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 c.symm z := by
    have hzT : z ∈ c.target := L.cover.piece_in_target k hz
    have hwithin := contMDiffWithinAt_extChartAt_symm_target
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (n := (2 : ℕ∞ω))
      (x := L.cover.base k) hzT
    have hopen := (isOpen_extChartAt_target
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (L.cover.base k)).mem_nhds hzT
    exact hwithin.contMDiffAt hopen
  have hcomp := herror.contMDiffAt.comp z (by simpa [c] using hsymm)
  have hgoal : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
      ((S.approximation i j - L.localizedFunction i) ∘ c.symm) z := by
    simpa [c] using hcomp
  exact hgoal.contDiffAt

private theorem transition_error_scale {ε C D : ℝ≥0} (hε : 0 < ε) :
    let η : ℝ≥0 := ε / (C ^ 2 + D + 1)
    0 < η ∧ η * (C ^ 2 + D) ≤ ε ∧ η * C ≤ ε ∧ η ≤ ε := by
  dsimp
  have hden : 0 < C ^ 2 + D + 1 := by positivity
  have heq : ε / (C ^ 2 + D + 1) * (C ^ 2 + D + 1) = ε :=
    div_mul_cancel₀ ε hden.ne'
  constructor
  · exact div_pos hε hden
  constructor
  · calc
      ε / (C ^ 2 + D + 1) * (C ^ 2 + D) ≤
          ε / (C ^ 2 + D + 1) * (C ^ 2 + D + 1) := by
            apply mul_le_mul_of_nonneg_left
            · nlinarith
            · positivity
      _ = ε := heq
  constructor
  · calc
      ε / (C ^ 2 + D + 1) * C ≤
          ε / (C ^ 2 + D + 1) * (C ^ 2 + D + 1) := by
            apply mul_le_mul_of_nonneg_left
            · nlinarith [sq_nonneg (C - (1 / 2 : ℝ≥0))]
            · positivity
      _ = ε := heq
  · calc
      ε / (C ^ 2 + D + 1) ≤
          ε / (C ^ 2 + D + 1) * (C ^ 2 + D + 1) := by
            calc
              ε / (C ^ 2 + D + 1) =
                  (ε / (C ^ 2 + D + 1)) * 1 := by ring
              _ ≤ (ε / (C ^ 2 + D + 1)) * (C ^ 2 + D + 1) :=
                mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = ε := heq

private theorem exists_chartwise_pair_transition_jets
    {φ : M → ℝ} (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A)
    (i k : L.cover.ι) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ N, ∀ j, N ≤ j → ∀ r ≤ 2, ∀ z ∈ L.cover.piece k,
      ‖iteratedFDeriv ℝ r
        ((S.approximation i j - L.localizedFunction i) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm) z‖ ≤ ε := by
  classical
  obtain ⟨C, D, htransition⟩ := transition_derivative_bounds_on_piece L A i k
  let η : ℝ≥0 := ε / (C ^ 2 + D + 1)
  have hscale := transition_error_scale (C := C) (D := D) hε
  have hη : 0 < η := by simpa [η] using hscale.1
  have hbudget2 : η * (C ^ 2 + D) ≤ ε := by simpa [η] using hscale.2.1
  have hbudget1 : η * C ≤ ε := by simpa [η] using hscale.2.2.1
  have hbudget0 : η ≤ ε := by simpa [η] using hscale.2.2.2
  obtain ⟨N, hN⟩ := (A i).jetsTendsto η hη
  refine ⟨N, ?_⟩
  intro j hj r hr z hzPiece
  let ci := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)
  let ck := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)
  let s := chart_overlap L i k
  let τ := ci ∘ ck.symm
  let g : EuclideanSpace ℂ (Fin n) → ℝ := (A i).approximation j - L.localFunction i
  let f : EuclideanSpace ℂ (Fin n) → ℝ :=
    (S.approximation i j - L.localizedFunction i) ∘ ck.symm
  by_cases hx : ck.symm z ∈ fixed_error_support L A i
  · have hzSource : ck.symm z ∈ ck.source := ck.map_target (L.cover.piece_in_target k hzPiece)
    have hzOverlap : z ∈ s := by
      change z ∈ chart_overlap L i k
      exact ⟨L.cover.piece_in_target k hzPiece, fixed_error_support_subset_source L A i hx⟩
    have hzCoordinates : z ∈ chart_transition_piece_coordinates L A i k := by
      change z ∈ ck '' (fixed_error_support L A i ∩ ck.symm '' L.cover.piece k)
      refine ⟨ck.symm z, ⟨hx, z, hzPiece, rfl⟩, ?_⟩
      exact ck.right_inv (L.cover.piece_in_target k hzPiece)
    have hs : IsOpen s := by simpa [s] using chart_overlap_open L i k
    have hτ : ContDiffOn ℝ 2 τ s := by simpa [s, τ, ci, ck] using chart_transition_contDiffOn L i k
    have hτ1 : ContDiffOn ℝ 1 τ s := hτ.of_le (by norm_num)
    have hτdiff : DifferentiableOn ℝ τ s := hτ.differentiableOn (by norm_num)
    have hAc2 : ContDiff ℝ 2 ((A i).approximation j) := by
      have htop : (2 : ℕ∞ω) ≤ ∞ := by
        change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top
      exact ((A i).smooth j).of_le htop
    have hg : ContDiff ℝ 2 g := by
      dsimp [g]
      exact hAc2.sub (L.localC2 i)
    have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
    have hgderiv : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
    have hgpDiff : Differentiable ℝ (fderiv ℝ g) := hgderiv.differentiable (by norm_num)
    have hgp : DifferentiableAt ℝ (fderiv ℝ g) (τ z) := hgpDiff (τ z)
    have hpCont : ContDiffOn ℝ 1 (fun y => fderiv ℝ g (τ y)) s := by
      exact hgderiv.contDiffOn.comp hτ1 (fun y hy => Set.mem_univ _)
    have hp : DifferentiableWithinAt ℝ (fun y => fderiv ℝ g (τ y)) s z :=
      hpCont.differentiableOn (by norm_num) z hzOverlap
    have hqCont : ContDiffOn ℝ 1 (fderivWithin ℝ τ s) s :=
      hτ.fderivWithin hs.uniqueDiffOn (by norm_num)
    have hq : DifferentiableWithinAt ℝ (fderivWithin ℝ τ s) s z :=
      hqCont.differentiableOn (by norm_num) z hzOverlap
    have htrans := htransition z hzCoordinates
    have hsource0 : ‖iteratedFDeriv ℝ 0 g (τ z)‖ ≤ (η : ℝ) :=
      hN j hj 0 (by omega) (τ z)
    have hsource1 : ‖fderiv ℝ g (τ z)‖ ≤ (η : ℝ) := by
      have ht := hN j hj 1 (by omega) (τ z)
      simpa only [norm_iteratedFDeriv_one] using ht
    have hsource2 : ‖fderiv ℝ (fderiv ℝ g) (τ z)‖ ≤ (η : ℝ) := by
      calc
        ‖fderiv ℝ (fderiv ℝ g) (τ z)‖ =
            ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) (τ z)‖ := by
          rw [norm_iteratedFDeriv_one]
        _ = ‖iteratedFDeriv ℝ 2 g (τ z)‖ :=
          norm_iteratedFDeriv_fderiv (f := g) (x := τ z) (n := 1)
        _ ≤ (η : ℝ) := hN j hj 2 (by omega) (τ z)
    have hEq : Set.EqOn f (g ∘ τ) s := by
      intro w hw
      simpa [f, g, τ, ci, ck, Function.comp_def] using
        chart_error_eq_source_transition L A S i k j hw
    have hcompJet (r : ℕ) :
        iteratedFDeriv ℝ r f z = iteratedFDeriv ℝ r (g ∘ τ) z := by
      have hWithin := hEq.iteratedFDerivWithin (𝕜 := ℝ) r
      have hLeft : iteratedFDerivWithin ℝ r f s z = iteratedFDeriv ℝ r f z :=
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) r hs hzOverlap
      have hRight : iteratedFDerivWithin ℝ r (g ∘ τ) s z =
          iteratedFDeriv ℝ r (g ∘ τ) z :=
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) r hs hzOverlap
      calc
        iteratedFDeriv ℝ r f z = iteratedFDerivWithin ℝ r f s z := hLeft.symm
        _ = iteratedFDerivWithin ℝ r (g ∘ τ) s z := hWithin hzOverlap
        _ = iteratedFDeriv ℝ r (g ∘ τ) z := hRight
    have hsourceVal : ‖(g ∘ τ) z‖ ≤ (η : ℝ) := by
      simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using hsource0
    have hsourceFirstComp :
        ‖iteratedFDerivWithin ℝ 1 (g ∘ τ) s z‖ ≤ (η : ℝ) * (C : ℝ) :=
      norm_iteratedFDerivWithin_one_comp_le hs hzOverlap hτdiff hgdiff hsource1 htrans.1
    have hsourceSecondComp :
        ‖iteratedFDerivWithin ℝ 2 (g ∘ τ) s z‖ ≤
          (η : ℝ) * (C : ℝ) ^ 2 + (η : ℝ) * (D : ℝ) := by
      exact norm_iteratedFDerivWithin_two_comp_le hs hzOverlap hτdiff hgdiff hgp hp hq
        hsource1 hsource2 htrans.1 htrans.2
    have hbudget0R : (η : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hbudget0
    have hbudget1R : (η : ℝ) * (C : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hbudget1
    have hbudget2R :
        (η : ℝ) * (C : ℝ) ^ 2 + (η : ℝ) * (D : ℝ) ≤ (ε : ℝ) := by
      exact_mod_cast (by nlinarith [hbudget2])
    have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
    rcases hrCases with rfl | rfl | rfl
    · have hnorm : ‖iteratedFDeriv ℝ 0 f z‖ ≤ (η : ℝ) := by
        rw [hcompJet 0]
        simpa [iteratedFDeriv_zero_eq_comp, Function.comp_def] using hsource0
      exact hnorm.trans hbudget0R
    · have hopen := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g ∘ τ) 1 hs hzOverlap
      have hnorm : ‖iteratedFDeriv ℝ 1 f z‖ ≤ (η : ℝ) * (C : ℝ) := by
        rw [hcompJet 1, ← hopen]
        exact hsourceFirstComp
      exact hnorm.trans hbudget1R
    · have hopen := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := g ∘ τ) 2 hs hzOverlap
      have hnorm :
          ‖iteratedFDeriv ℝ 2 f z‖ ≤
            (η : ℝ) * (C : ℝ) ^ 2 + (η : ℝ) * (D : ℝ) := by
        rw [hcompJet 2, ← hopen]
        exact hsourceSecondComp
      exact hnorm.trans hbudget2R
  · have hzero := chart_error_zero_jets_at L A S i k j r
      (L.cover.piece_in_target k hzPiece) hx
    rw [hzero]
    simpa using hε.le

private theorem uniform_chartwise_transition_jets
    {φ : M → ℝ} (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ N, ∀ j, N ≤ j → ∀ i k, ∀ r ≤ 2, ∀ z ∈ L.cover.piece k,
      ‖iteratedFDeriv ℝ r
        ((S.approximation i j - L.localizedFunction i) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm) z‖ ≤ ε := by
  classical
  let : Fintype L.cover.ι := L.cover.fintype_ι
  let P (p : L.cover.ι × L.cover.ι) (j : ℕ) : Prop :=
    ∀ r ≤ 2, ∀ z ∈ L.cover.piece p.2,
      ‖iteratedFDeriv ℝ r
        ((S.approximation p.1 j - L.localizedFunction p.1) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base p.2)).symm) z‖ ≤ ε
  have hP : ∀ p, ∃ N, ∀ j, N ≤ j → P p j := by
    intro p
    exact exists_chartwise_pair_transition_jets L A S p.1 p.2 ε hε
  choose N hN using hP
  refine ⟨Finset.univ.sup N, ?_⟩
  intro j hj i k r hr z hz
  exact hN (i, k) j (le_trans (Finset.le_sup (Finset.mem_univ (i, k))) hj) r hr z hz

-- Boundedness of the iterated derivatives on compact sets. For actual partial
-- chart transitions, first restrict to their open overlap or use a cutoff;
-- this global smoothness hypothesis must not be assumed for a partial map.
private theorem iteratedFDeriv_norm_bddAbove_on_isCompact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (hK : IsCompact K) (f : E → F)
    (hf : ContDiff ℝ 2 f) (r : ℕ) (hr : r ≤ 2) :
    BddAbove ((fun x : E => ‖iteratedFDeriv ℝ r f x‖) '' K) := by
  apply hK.bddAbove_image
  exact (hf.continuous_iteratedFDeriv (by exact_mod_cast hr)).norm.continuousOn

/-- The regularity and uniform full-jet estimate after passing an actual
zero-extended local convolution through every chart of a fixed finite cover.
The same threshold works for every pair of chart indices. -/
structure ChartwiseTransitionJetsData {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A) where
  error_contDiffAt : ∀ i j k z, z ∈ L.cover.piece k →
    ContDiffAt ℝ 2
      ((S.approximation i j - L.localizedFunction i) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm) z
  jetsTendsto : ∀ ε : ℝ≥0, 0 < ε →
    ∃ N, ∀ j, N ≤ j → ∀ i k, ∀ r ≤ 2, ∀ z ∈ L.cover.piece k,
      ‖iteratedFDeriv ℝ r
        ((S.approximation i j - L.localizedFunction i) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm) z‖ ≤ ε

set_option maxHeartbeats 800000 in
/-- Bounded transition jets on the relevant compact overlaps convert uniform
source-chart C² approximation to all-chart C² approximation. At points away
from the fixed compact support, the error vanishes in a neighborhood. -/
theorem exists_chartwiseTransitionJetsData
    {φ : M → ℝ} (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target)
    (S : ChartwiseSourceMollificationData L A) :
    Nonempty (ChartwiseTransitionJetsData L A S) := by
  refine ⟨⟨?_, ?_⟩⟩
  · exact chartwise_error_contDiffAt L A S
  · exact uniform_chartwise_transition_jets L A S

end KahlerForm
