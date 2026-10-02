-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Tools/ArzelaAscoli.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Tools.Convolution

@[expose] public section


noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BoundedContinuousFunction

namespace Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma restrict_mem_Icc_of_abs_le
    {K : Set E} {C : ℝ}
    {f : ℕ → E → ℝ}
    (hf_bdd : ∀ n, ∀ x, |f n x| ≤ C)
    (n : ℕ) (x : K) :
    f n (x : E) ∈ Set.Icc (-C) C := by
  have hbd := hf_bdd n (x : E)
  rcases abs_le.mp hbd with ⟨hL, hR⟩
  exact ⟨hL, hR⟩

omit [NeZero d] in
theorem tendsto_subseq_of_uniformly_lipschitz_uniformly_bounded
    {K : Set E} (hK_compact : IsCompact K)
    {f : ℕ → E → ℝ}
    (hf_cont : ∀ n, Continuous (f n))
    {C : ℝ} (hC_pos : 0 < C) (hf_bdd : ∀ n, ∀ x, |f n x| ≤ C)
    {L : ℝ} (hL_pos : 0 ≤ L)
    (hf_lip : ∀ n, LipschitzWith ⟨L, hL_pos⟩ (f n)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (fInf : E → ℝ),
        Continuous fInf ∧
        TendstoUniformlyOn (fun k => f (φ k)) fInf Filter.atTop K := by
  classical
  have _hC_le : (0 : ℝ) ≤ C := hC_pos.le
  by_cases hK_empty : K = ∅
  · subst hK_empty
    refine ⟨id, strictMono_id, fun _ => 0, continuous_const, ?_⟩
    exact tendstoUniformlyOn_empty
  · have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    have h_subtype_K_compact : CompactSpace K := isCompact_iff_compactSpace.mp hK_compact
    have h_subtype_K_nonempty : Nonempty K := hK_nonempty.to_subtype
    let f_boundedContinuousFunction : ℕ → (K →ᵇ ℝ) :=
      fun n => BoundedContinuousFunction.mkOfCompact
        ⟨fun x : K => f n (x : E), (hf_cont n).comp continuous_subtype_val⟩
    have h_range_compact : ∀ (g : K →ᵇ ℝ) (x : K),
        g ∈ Set.range f_boundedContinuousFunction → g x ∈ Set.Icc (-C) C := by
      rintro g x ⟨n, rfl⟩
      simpa [f_boundedContinuousFunction] using restrict_mem_Icc_of_abs_le hf_bdd n x
    have h_Icc_compact : IsCompact (Set.Icc (-C) C : Set ℝ) := isCompact_Icc
    have h_lip_restrict : ∀ n, LipschitzWith (NNReal.mk L hL_pos) ((f n) ∘ ((↑) : K → E)) := by
      intro n
      have hsubval : LipschitzWith 1 ((↑) : K → E) := LipschitzWith.subtype_val K
      have hcomp : LipschitzWith (NNReal.mk L hL_pos * 1)
          ((f n) ∘ ((↑) : K → E)) :=
        (hf_lip n).comp hsubval
      rw [mul_one] at hcomp
      exact hcomp
    have h_equicont : Equicontinuous ((↑) : (Set.range f_boundedContinuousFunction) → K → ℝ) := by
      refine Metric.equicontinuous_of_continuity_modulus
        (fun s => L * s) ?_ _ ?_
      · have : Tendsto (fun s : ℝ => L * s) (𝓝 0) (𝓝 (L * 0)) :=
          tendsto_const_nhds.mul tendsto_id
        simpa using this
      · rintro x y ⟨g, hg⟩
        rcases hg with ⟨n, rfl⟩
        have h_lip_n := h_lip_restrict n
        have : dist (f n (x : E)) (f n (y : E)) ≤ L * dist (x : E) (y : E) := by
          have := h_lip_n.dist_le_mul x y
          exact this
        simpa [f_boundedContinuousFunction, BoundedContinuousFunction.mkOfCompact_apply,
          Subtype.dist_eq] using this
    have h_compact_closure :
        IsCompact (closure (Set.range f_boundedContinuousFunction : Set (K →ᵇ ℝ))) :=
      BoundedContinuousFunction.arzela_ascoli (Set.Icc (-C) C) h_Icc_compact
        (Set.range f_boundedContinuousFunction) (fun g x hg => h_range_compact g x hg) h_equicont
    have h_in_closure : ∀ n, f_boundedContinuousFunction n ∈ closure (Set.range f_boundedContinuousFunction) := fun n =>
      subset_closure (Set.mem_range_self n)
    rcases h_compact_closure.tendsto_subseq h_in_closure with
      ⟨gInf, _, φ, hφ_mono, h_tendsto⟩
    set g : K → ℝ := gInf.toFun with hg_def
    have hg_cont : Continuous g := gInf.continuous
    have h_uniform_K :
        TendstoUniformly (fun k => fun x : K => f (φ k) x) g atTop := by
      have hTU :
          TendstoUniformly (fun k => fun x : K => (f_boundedContinuousFunction (φ k)) x)
            (fun x : K => gInf x) atTop :=
        BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp h_tendsto
      have hcoe : (fun k => fun x : K => (f_boundedContinuousFunction (φ k)) x) =
          (fun k => fun x : K => f (φ k) (x : E)) := by
        funext k x
        simp [f_boundedContinuousFunction]
      rw [hcoe] at hTU
      exact hTU
    have h_g_lip : LipschitzWith (NNReal.mk L hL_pos) g := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have h_pt_x : Tendsto (fun k => f (φ k) (x : E)) atTop (𝓝 (g x)) :=
        h_uniform_K.tendsto_at x
      have h_pt_y : Tendsto (fun k => f (φ k) (y : E)) atTop (𝓝 (g y)) :=
        h_uniform_K.tendsto_at y
      have h_pt_dist :
          Tendsto (fun k => dist (f (φ k) (x : E)) (f (φ k) (y : E))) atTop
            (𝓝 (dist (g x) (g y))) :=
        h_pt_x.dist h_pt_y
      have h_each : ∀ k,
          dist (f (φ k) (x : E)) (f (φ k) (y : E)) ≤ L * dist (x : E) (y : E) := by
        intro k
        have hL_n := hf_lip (φ k)
        have := hL_n.dist_le_mul (x : E) (y : E)
        exact this
      have h_le : dist (g x) (g y) ≤ L * dist (x : E) (y : E) :=
        le_of_tendsto_of_tendsto' h_pt_dist tendsto_const_nhds (fun k => h_each k)
      have h_subtype : dist (x : E) (y : E) = dist x y := rfl
      change dist (g x) (g y) ≤ L * dist x y
      rw [← h_subtype]
      exact h_le
    set g_set : E → ℝ := fun x => if hxK : x ∈ K then g ⟨x, hxK⟩ else 0
      with hg_set_def
    have h_g_set_lip : LipschitzOnWith (NNReal.mk L hL_pos) g_set K := by
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      have h_dist :=
        h_g_lip.dist_le_mul (⟨x, hx⟩ : K) (⟨y, hy⟩ : K)
      have h_g_set_x : g_set x = g ⟨x, hx⟩ := by simp [g_set, hx]
      have h_g_set_y : g_set y = g ⟨y, hy⟩ := by simp [g_set, hy]
      have h_subtype_dist : dist (⟨x, hx⟩ : K) (⟨y, hy⟩ : K) = dist x y := rfl
      have h_real : dist (g_set x) (g_set y) ≤ L * dist x y := by
        rw [h_g_set_x, h_g_set_y, ← h_subtype_dist]
        exact h_dist
      exact h_real
    rcases h_g_set_lip.extend_real with ⟨fInf, h_fInf_lip, h_fInf_eq⟩
    refine ⟨φ, hφ_mono, fInf, h_fInf_lip.continuous, ?_⟩
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [Metric.tendstoUniformly_iff] at h_uniform_K
    have h_ev := h_uniform_K ε hε
    filter_upwards [h_ev] with k hk x hx
    have h_fInf_x : fInf x = g ⟨x, hx⟩ := by
      have h1 : g_set x = g ⟨x, hx⟩ := by simp [g_set, hx]
      have h2 : fInf x = g_set x := by
        symm
        exact h_fInf_eq hx
      rw [h2, h1]
    rw [h_fInf_x]
    have hk_at_x := hk ⟨x, hx⟩
    simpa using hk_at_x

end Sobolev
