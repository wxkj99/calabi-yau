module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import CalabiYau.Topology.Compactness.ArzelaAscoli
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Uniform `C^{k,α}` bounds in charts

The a priori estimates of the continuity method are uniform bounds for **families** of functions
on a compact manifold. Rather than fixing a finite atlas and a norm, we express them atlas-free:
a family is bounded in `C^{k,α}` if, in every chart and on every compact subset of the chart
target, all derivatives of order `≤ k` are uniformly bounded and the `k`-th derivatives are
uniformly `α`-Hölder (`HolderBoundedInCharts`). For a finite atlas and smooth functions this is
equivalent to a bound on the usual `C^{k,α}` norm.

`HolderBoundOn k α C s f` is the corresponding local bound with an explicit constant on a subset
of the model space; it is used to state Schauder estimates with explicit constants.

**Caveats.** `HolderBoundOn` carries **no differentiability**: `iteratedFDeriv` takes the junk
value `0` where `f` is not differentiable, so for non-smooth `f` the bound says little (a
half-space indicator satisfies `HolderBoundOn 1 α C` near its jump for small `C`). For `α = 0`
the Hölder condition only bounds the oscillation of the `k`-th derivative, so `α = 0` together
with the sup bounds is a `C^k` bound. Consumers must assume smoothness separately (as all
statements of the project do); regularity-lowering lemmas such as `HolderBoundedInCharts.of_le`
therefore take smoothness and `α ≤ 1` as hypotheses.

This file is Mathlib-only. The global Hölder spaces of track S are expected to satisfy
`‖f‖_{C^{k,α}} bounded ↔ HolderBoundedInCharts` as a bridge lemma.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `f` has all derivatives of order `≤ k` bounded by `C` on `s` and its `k`-th derivative is
`α`-Hölder on `s` with constant `C`. Differentiability is not included: this is meant for smooth
`f` on an open neighbourhood of `s`. -/
def HolderBoundOn (k : ℕ) (α C : ℝ≥0) (s : Set E) (f : E → F) : Prop :=
  (∀ j ≤ k, ∀ z ∈ s, ‖iteratedFDeriv ℝ j f z‖ ≤ C) ∧
    HolderOnWith C α (iteratedFDeriv ℝ k f) s

theorem HolderBoundOn.mono_const {k : ℕ} {α C C' : ℝ≥0} {s : Set E} {f : E → F}
    (h : HolderBoundOn k α C s f) (hC : C ≤ C') : HolderBoundOn k α C' s f := by
  refine ⟨?_, h.2.mono_const hC⟩
  intro j hj z hz
  exact (h.1 j hj z hz).trans hC

theorem HolderBoundOn.mono_set {k : ℕ} {α C : ℝ≥0} {s t : Set E} {f : E → F}
    (h : HolderBoundOn k α C s f) (hts : t ⊆ s) : HolderBoundOn k α C t f := by
  refine ⟨?_, h.2.mono hts⟩
  intro j hj z hz
  exact h.1 j hj z (hts hz)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A family `S` of real functions on `M` is bounded in `C^{k,α}`: in every chart, on every
compact subset of the chart target, the coordinate expressions satisfy a common
`HolderBoundOn k α C` bound. -/
def HolderBoundedInCharts (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (k : ℕ) (α : ℝ≥0) (S : Set (M → ℝ)) : Prop :=
  ∀ x : M, ∀ K : Set E, IsCompact K → K ⊆ (extChartAt 𝓘(ℝ, E) x).target →
    ∃ C : ℝ≥0, ∀ f ∈ S, HolderBoundOn k α C K (f ∘ (extChartAt 𝓘(ℝ, E) x).symm)

namespace HolderBoundedInCharts

variable {k : ℕ} {α : ℝ≥0} {S T : Set (M → ℝ)}

theorem mono (h : HolderBoundedInCharts E k α S) (hTS : T ⊆ S) : HolderBoundedInCharts E k α T :=
  fun x K hK hKt ↦ (h x K hK hKt).imp fun _ hC f hf ↦ hC f (hTS hf)

private theorem exists_compact_segment_near_subset_of_open {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ S : Set E, IsCompact S ∧ S ⊆ U ∧
      ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ δ → segment ℝ x y ⊆ S := by
  classical
  by_cases hne : K.Nonempty
  · have hex : ∀ a : K, ∃ r : ℝ, 0 < r ∧ Metric.closedBall (a : E) (2 * r) ⊆ U := by
      intro a
      obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU a.property))
      refine ⟨R / 3, by positivity, ?_⟩
      intro z hz
      apply hball
      rw [Metric.mem_ball]
      have hz' : dist z (a : E) ≤ 2 * (R / 3) := by simpa using hz
      have hzR : dist z (a : E) < R := by
        calc
          dist z (a : E) ≤ 2 * (R / 3) := hz'
          _ < R := by nlinarith
      simpa [dist_comm] using hzR
    let r : K → ℝ := fun a => Classical.choose (hex a)
    have hr (a : K) : 0 < r a ∧ Metric.closedBall (a : E) (2 * r a) ⊆ U :=
      Classical.choose_spec (hex a)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : K => Metric.ball a (r a))
      (fun _ => Metric.isOpen_ball) (by
        intro z hz
        exact Set.mem_iUnion.2 ⟨⟨z, hz⟩, Metric.mem_ball_self (hr ⟨z, hz⟩).1⟩)
    have htne : t.Nonempty := by
      rcases hne with ⟨z, hz⟩
      have hz' := ht hz
      rcases Set.mem_iUnion₂.mp hz' with ⟨a, ha, hza⟩
      exact ⟨a, ha⟩
    let δ : ℝ := t.inf' htne fun a => r a
    have hδpos : 0 < δ := by
      change 0 < t.inf' htne (fun a => r a)
      rw [Finset.lt_inf'_iff]
      intro a ha
      exact (hr a).1
    have hδle (a : K) (ha : a ∈ t) : δ ≤ r a := by
      exact Finset.inf'_le (f := fun i => r i) ha
    let A (a : K) : Set E := K ∩ Metric.closedBall (a : E) (2 * r a)
    let segMap : E × E × ℝ → E := fun p => (1 - p.2.2) • p.1 + p.2.2 • p.2.1
    let segSet (a : K) : Set E := segMap '' (A a ×ˢ A a ×ˢ Set.Icc (0 : ℝ) 1)
    let S : Set E := ⋃ a : {a : K // a ∈ t}, segSet a.1
    have hA (a : K) : IsCompact (A a) := by
      exact hK.inter_right Metric.isClosed_closedBall
    have hsegSet (a : K) : IsCompact (segSet a) := by
      dsimp [segSet]
      apply IsCompact.image
      · exact (hA a).prod ((hA a).prod isCompact_Icc)
      · fun_prop
    have hScompact : IsCompact S := by
      dsimp [S]
      exact isCompact_iUnion fun a : {a : K // a ∈ t} => hsegSet a.1
    have hSsubset : S ⊆ U := by
      intro z hz
      rcases Set.mem_iUnion.mp hz with ⟨a, ha⟩
      rw [Set.mem_image] at ha
      rcases ha with ⟨p, hp, rfl⟩
      rcases p with ⟨x, y, θ⟩
      rcases hp with ⟨hxA, hyA, hθ⟩
      have hconv : Convex ℝ (Metric.closedBall (a.1 : E) (2 * r a.1)) :=
        convex_closedBall _ _
      have hx : x ∈ Metric.closedBall (a.1 : E) (2 * r a.1) := hxA.2
      have hy : y ∈ Metric.closedBall (a.1 : E) (2 * r a.1) := hyA.2
      have hzseg : (1 - θ) • x + θ • y ∈ segment ℝ x y := by
        rw [segment_eq_image]
        exact Set.mem_image_of_mem _ hθ
      exact (hr a.1).2 (hconv.segment_subset hx hy hzseg)
    have hnear (x : E) (hx : x ∈ K) (y : E) (hy : y ∈ K) (hxy : dist x y ≤ δ) :
        segment ℝ x y ⊆ S := by
      have hx' := ht hx
      rcases Set.mem_iUnion₂.mp hx' with ⟨a, ha, hxa⟩
      have hxa' : dist x (a : E) < r a := by simpa [Metric.mem_ball] using hxa
      have hxc : x ∈ Metric.closedBall (a : E) (2 * r a) := by
        rw [Metric.mem_closedBall]
        exact (le_of_lt hxa').trans (by nlinarith [(hr a).1])
      have hyc : y ∈ Metric.closedBall (a : E) (2 * r a) := by
        rw [Metric.mem_closedBall]
        calc
          dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
          _ ≤ δ + dist x a := add_le_add (by simpa [dist_comm] using hxy) le_rfl
          _ ≤ r a + r a := add_le_add (hδle a ha) (le_of_lt hxa')
          _ = 2 * r a := by ring
      intro z hz
      have hz' := hz
      rw [segment_eq_image] at hz'
      rcases hz' with ⟨θ, hθ, rfl⟩
      have hp : ((1 - θ) • x + θ • y) ∈ segSet a := by
        have htuple : (x, y, θ) ∈ A a ×ˢ A a ×ˢ Set.Icc (0 : ℝ) 1 := by
          simp [A, hx, hxc, hy, hyc, hθ]
        have himage := Set.mem_image_of_mem segMap htuple
        simpa [segSet, segMap] using himage
      exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, hp⟩
    exact ⟨δ, hδpos, S, hScompact, hSsubset, hnear⟩
  · refine ⟨1, by norm_num, ∅, isCompact_empty, empty_subset _, ?_⟩
    intro x hx y hy
    exact (hne ⟨x, hx⟩).elim

/-- Lower regularity: a `C^{k+1}` bound implies a `C^{k,α}` bound for every `α ≤ 1`. -/
theorem of_succ [IsManifold 𝓘(ℝ, E) ∞ M] (h : HolderBoundedInCharts E (k + 1) 0 S)
    (hS : ∀ f ∈ S, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (hα : α ≤ 1) : HolderBoundedInCharts E k α S := by
  by_cases hα0 : α = 0
  · subst α
    intro x K hK hKt
    obtain ⟨C, hC⟩ := h x K hK hKt
    refine ⟨2 * C, ?_⟩
    intro f hf
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hbound := (hC f hf).1 j (le_trans hj (Nat.le_succ k)) z hz
      exact hbound.trans (by
        calc
          (C : ℝ) = 1 * C := by simp
          _ ≤ 2 * C := by gcongr; norm_num)
    · intro z hz w hw
      have hzb := (hC f hf).1 k (Nat.le_succ k) z hz
      have hwb := (hC f hf).1 k (Nat.le_succ k) w hw
      change edist (iteratedFDeriv ℝ k (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) z)
          (iteratedFDeriv ℝ k (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) w) ≤
        (↑(2 * C) : ENNReal) * edist z w ^ (0 : ℝ)
      calc
        _ = ENNReal.ofReal (dist
            (iteratedFDeriv ℝ k (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) z)
            (iteratedFDeriv ℝ k (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) w)) := edist_dist _ _
        _ ≤ ENNReal.ofReal
            (‖iteratedFDeriv ℝ k (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) z‖ +
              ‖iteratedFDeriv ℝ k (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) w‖) :=
          ENNReal.ofReal_le_ofReal (dist_le_norm_add_norm _ _)
        _ ≤ ENNReal.ofReal ((C : ℝ) + C) :=
          ENNReal.ofReal_le_ofReal (add_le_add hzb hwb)
        _ = (↑(2 * C) : ENNReal) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          simp [two_mul]
        _ = (↑(2 * C) : ENNReal) * edist z w ^ (0 : ℝ) := by
          rw [ENNReal.rpow_zero, mul_one]
  · intro x K hK hKt
    let e := extChartAt 𝓘(ℝ, E) x
    have hopen : IsOpen e.target := isOpen_extChartAt_target x
    obtain ⟨δ, hδ, S₀, hS₀, hS₀t, hnear⟩ :=
      exists_compact_segment_near_subset_of_open hK hopen hKt
    obtain ⟨C₀, h₀⟩ := h x K hK hKt
    obtain ⟨C₁, h₁⟩ := h x S₀ hS₀ hS₀t
    have hδNN : 0 < Real.toNNReal δ := Real.toNNReal_pos.mpr hδ
    let δNN : ℝ≥0 := Real.toNNReal δ
    let Lfar : ℝ≥0 := 2 * C₀ / δNN
    have hLfar : (Lfar : ℝ) = 2 * (C₀ : ℝ) / δ := by
      simp [Lfar, δNN, Real.coe_toNNReal δ hδ.le]
    let L : ℝ≥0 := max C₁ Lfar
    have hdiamTop : Metric.ediam K ≠ ⊤ := hK.isBounded.ediam_ne_top
    let D : ℝ≥0 := (Metric.ediam K).toNNReal
    have hdiam (z : E) (hz : z ∈ K) (w : E) (hw : w ∈ K) :
        edist z w ≤ (D : ENNReal) := by
      have heq : (D : ENNReal) = Metric.ediam K := by
        change ↑(Metric.ediam K).toNNReal = Metric.ediam K
        exact ENNReal.coe_toNNReal hdiamTop
      rw [heq]
      exact Metric.edist_le_ediam_of_mem hz hw
    let Cα : ℝ≥0 := L * D ^ ((1 : ℝ) - (α : ℝ))
    let Ctot : ℝ≥0 := max C₀ Cα
    have htop (j : ℕ) : (↑j : ℕ∞ω) ≤ ∞ := by
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
    have hklt : (↑k : ℕ∞ω) < ∞ := by
      exact_mod_cast (show (k : ℕ∞) < ⊤ from WithTop.coe_lt_top k)
    let cf (f : M → ℝ) : E → ℝ := f ∘ e.symm
    have hcf (f : M → ℝ) (hf : f ∈ S) : ContDiffOn ℝ ∞ (cf f) e.target := by
      have h := (contMDiff_iff.mp (hS f hf)).2 x 0
      simpa [cf, e, extChartAt, chartAt_self_eq] using h
    have hnearLip (f : M → ℝ) (hf : f ∈ S) (z : E) (hz : z ∈ K)
        (w : E) (hw : w ∈ K) (hzw : dist z w ≤ δ) :
        dist (iteratedFDeriv ℝ k (cf f) z) (iteratedFDeriv ℝ k (cf f) w) ≤
          (C₁ : ℝ) * dist z w := by
      let g : E → _ := iteratedFDeriv ℝ k (cf f)
      have hseg := hnear z hz w hw hzw
      have hLipSeg : LipschitzOnWith C₁ g (segment ℝ z w) := by
        apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
        · intro y hy
          exact (hcf f hf).contDiffAt (hopen.mem_nhds (hS₀t (hseg hy))) |>.differentiableAt_iteratedFDeriv hklt
        · intro y hy
          have hbound := (h₁ f hf).1 (k + 1) le_rfl y (hseg hy)
          have hbound' : ‖fderiv ℝ g y‖ ≤ (C₁ : ℝ) := by
            rw [norm_fderiv_iteratedFDeriv]
            exact hbound
          exact_mod_cast hbound'
        · exact convex_segment z w
      exact (lipschitzOnWith_iff_dist_le_mul.mp hLipSeg) z (left_mem_segment ℝ z w)
        w (right_mem_segment ℝ z w)
    have hGlobal (f : M → ℝ) (hf : f ∈ S) :
        LipschitzOnWith L (fun z => iteratedFDeriv ℝ k (cf f) z) K := by
      apply LipschitzOnWith.of_dist_le_mul
      intro z hz w hw
      by_cases hzw : dist z w ≤ δ
      · exact (hnearLip f hf z hz w hw hzw).trans <|
          mul_le_mul_of_nonneg_right (by exact_mod_cast (le_max_left C₁ Lfar)) dist_nonneg
      · have hfar : δ ≤ dist z w := le_of_not_ge hzw
        have hzbound := (h₀ f hf).1 k (Nat.le_succ k) z hz
        have hwbound := (h₀ f hf).1 k (Nat.le_succ k) w hw
        have hfar' : 2 * (C₀ : ℝ) ≤ (Lfar : ℝ) * dist z w := by
          rw [hLfar]
          calc
            2 * (C₀ : ℝ) = (2 * (C₀ : ℝ) / δ) * δ := by
              field_simp [ne_of_gt hδ]
            _ ≤ (2 * (C₀ : ℝ) / δ) * dist z w :=
              mul_le_mul_of_nonneg_left hfar (by positivity)
        calc
          dist (iteratedFDeriv ℝ k (cf f) z) (iteratedFDeriv ℝ k (cf f) w) ≤
              ‖iteratedFDeriv ℝ k (cf f) z‖ + ‖iteratedFDeriv ℝ k (cf f) w‖ :=
            dist_le_norm_add_norm _ _
          _ ≤ (C₀ : ℝ) + C₀ := add_le_add hzbound hwbound
          _ = 2 * (C₀ : ℝ) := by ring
          _ ≤ (Lfar : ℝ) * dist z w := hfar'
          _ ≤ (L : ℝ) * dist z w :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (le_max_right C₁ Lfar)) dist_nonneg
    refine ⟨Ctot, ?_⟩
    intro f hf
    have hHolder : HolderOnWith Cα α (fun z => iteratedFDeriv ℝ k (cf f) z) K := by
      simpa [Cα] using (hGlobal f hf).holderOnWith.of_le hdiam hα
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hbound := (h₀ f hf).1 j (le_trans hj (Nat.le_succ k)) z hz
      exact hbound.trans (by exact_mod_cast (le_max_left C₀ Cα))
    · simpa [cf, e, extChartAt, chartAt_self_eq] using
        hHolder.mono_const (le_max_right C₀ Cα)

/-- A single smooth function is bounded in every `C^{k,α}`, `α ≤ 1`. -/
theorem singleton [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hα : α ≤ 1) : HolderBoundedInCharts E k α {f} := by
  intro x K hK hKt
  let e := extChartAt 𝓘(ℝ, E) x
  let cf : E → ℝ := f ∘ e.symm
  have hcf : ContDiffOn ℝ ∞ cf e.target := by
    have h := (contMDiff_iff.mp hf).2 x 0
    simpa [cf, e, extChartAt, chartAt_self_eq] using h
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  have hnorm : ∀ j ≤ k, ContinuousOn (fun z => ‖iteratedFDeriv ℝ j cf z‖) K := by
    intro j hj
    have hjtop : (↑j : ℕ∞ω) ≤ ∞ := by
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
    have hwithin : ContinuousOn (iteratedFDerivWithin ℝ j cf e.target) e.target :=
      hcf.continuousOn_iteratedFDerivWithin hjtop hopen.uniqueDiffOn
    have hderiv : EqOn (iteratedFDerivWithin ℝ j cf e.target) (iteratedFDeriv ℝ j cf) K := by
      intro z hz
      apply iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn
      · exact (hcf.contDiffAt (hopen.mem_nhds (hKt hz))).of_le hjtop
      · exact hKt hz
    exact (hwithin.mono hKt).congr hderiv.symm |>.norm
  let q : E → ℝ := fun z => ∑ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j cf z‖
  have hq : ContinuousOn q K := by
    dsimp [q]
    exact continuousOn_finsetSum (Finset.range (k + 1)) fun j hj =>
      hnorm j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  obtain ⟨B, hB0, hB⟩ := (hK.bddAbove_image hq).exists_ge 0
  let C : ℝ≥0 := ⟨B, hB0⟩
  have hq_bound (z : E) (hz : z ∈ K) : q z ≤ B :=
    hB (q z) (Set.mem_image_of_mem q hz)
  have hterm (j : ℕ) (hj : j ≤ k) (z : E) (hz : z ∈ K) :
      ‖iteratedFDeriv ℝ j cf z‖ ≤ q z := by
    dsimp [q]
    apply Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i cf z‖)
    · intro i hi
      exact norm_nonneg _
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hBtwo : B ≤ 2 * (C : ℝ) := by
    change B ≤ 2 * B
    rw [two_mul]
    exact le_add_of_nonneg_right hB0
  have hBtwo' : B ≤ (↑(2 * C) : ℝ) := by
    calc
      B ≤ 2 * (C : ℝ) := hBtwo
      _ = (↑(2 * C) : ℝ) := by simp [NNReal.coe_mul]
  have htop (j : ℕ) : (↑j : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  have hIterEq (j : ℕ) : EqOn (iteratedFDerivWithin ℝ j cf e.target)
      (iteratedFDeriv ℝ j cf) e.target := by
    intro z hz
    apply iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn
    · exact (hcf.contDiffAt (hopen.mem_nhds hz)).of_le (htop j)
    · exact hz
  have hDcontOn : ContinuousOn (iteratedFDeriv ℝ (k + 1) cf) e.target := by
    have hwithin := hcf.continuousOn_iteratedFDerivWithin (htop (k + 1)) hopen.uniqueDiffOn
    exact hwithin.congr (hIterEq (k + 1)).symm
  let g : E → _ := iteratedFDeriv ℝ k cf
  have hklt : (↑k : ℕ∞ω) < ∞ := by
    exact_mod_cast (show (k : ℕ∞) < ⊤ from WithTop.coe_lt_top k)
  have hgDiff (z : E) (hz : z ∈ e.target) : DifferentiableAt ℝ g z :=
    (hcf.contDiffAt (hopen.mem_nhds hz)).differentiableAt_iteratedFDeriv hklt
  have hFderivEq : fderiv ℝ g =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ ∘
        iteratedFDeriv ℝ (k + 1) cf := by
    simpa [g] using (fderiv_iteratedFDeriv (𝕜 := ℝ) (f := cf) (n := k))
  have hLoc : LocallyLipschitzOn K g := by
    intro z hz
    have hzU : z ∈ e.target := hKt hz
    have hDcont : ContinuousAt (iteratedFDeriv ℝ (k + 1) cf) z :=
      hDcontOn.continuousAt (hopen.mem_nhds hzU)
    have hFderivCont : ContinuousAt (fderiv ℝ g) z := by
      rw [hFderivEq]
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ).continuous
        |>.continuousAt.comp hDcont
    have hder : ∀ᶠ y in 𝓝 z, HasFDerivAt g (fderiv ℝ g y) y := by
      filter_upwards [hopen.mem_nhds hzU] with y hy
      exact (hgDiff y hy).hasFDerivAt
    have hstrict : HasStrictFDerivAt g (fderiv ℝ g z) z :=
      hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt hder hFderivCont
    obtain ⟨L, t, ht, hL⟩ := hstrict.exists_lipschitzOnWith
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨L, Metric.ball z r ∩ K, Metric.mem_nhdsWithin_iff.mpr ⟨r, hr, ?_⟩, ?_⟩
    · exact subset_rfl
    · exact hL.mono fun y hy => hrt hy.1
  obtain ⟨L, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hLoc
  have hdiamTop : Metric.ediam K ≠ ⊤ := hK.isBounded.ediam_ne_top
  let D : ℝ≥0 := (Metric.ediam K).toNNReal
  have hdist (z : E) (hz : z ∈ K) (w : E) (hw : w ∈ K) :
    edist z w ≤ (D : ENNReal) := by
    have heq : (D : ENNReal) = Metric.ediam K := by
      change ↑(Metric.ediam K).toNNReal = Metric.ediam K
      exact ENNReal.coe_toNNReal hdiamTop
    rw [heq]
    exact Metric.edist_le_ediam_of_mem hz hw
  have hHolder := hLip.holderOnWith.of_le hdist hα
  let Cα : ℝ≥0 := L * D ^ ((1 : ℝ) - (α : ℝ))
  let Ctot : ℝ≥0 := max (2 * C) Cα
  have hHolder' : HolderOnWith Ctot α g K := by
    apply hHolder.mono_const
    exact le_max_right _ _
  refine ⟨Ctot, ?_⟩
  intro g hg
  have hg_eq : g = f := Set.mem_singleton_iff.mp hg
  subst g
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hb := (hterm j hj z hz).trans (hq_bound z hz)
    have hb' : ‖iteratedFDeriv ℝ j cf z‖ ≤ (↑(2 * C) : ℝ) := hb.trans hBtwo'
    have hb'' : ‖iteratedFDeriv ℝ j cf z‖ ≤ (Ctot : ℝ) := by
      apply hb'.trans
      exact_mod_cast (le_max_left (2 * C) Cα)
    simpa [cf, e, extChartAt, chartAt_self_eq, Ctot, Cα] using hb''
  · simpa [g, e, cf, extChartAt, chartAt_self_eq, Ctot, Cα] using hHolder'

/-- Sums of bounded families are bounded. -/
theorem add [IsManifold 𝓘(ℝ, E) ∞ M] {T : Set (M → ℝ)} (hS : HolderBoundedInCharts E k α S)
    (hT : HolderBoundedInCharts E k α T) (hSs : ∀ f ∈ S, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f)
    (hTs : ∀ f ∈ T, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) :
    HolderBoundedInCharts E k α (Set.image2 (· + ·) S T) := by
  intro x K hK hKt
  obtain ⟨C₁, h₁⟩ := hS x K hK hKt
  obtain ⟨C₂, h₂⟩ := hT x K hK hKt
  refine ⟨C₁ + C₂, ?_⟩
  intro u hu
  rcases hu with ⟨f, hf, g, hg, rfl⟩
  let e := extChartAt 𝓘(ℝ, E) x
  let cf : E → ℝ := f ∘ e.symm
  let cg : E → ℝ := g ∘ e.symm
  have hcf : ContDiffOn ℝ ∞ cf e.target := by
    have h := (contMDiff_iff.mp (hSs f hf)).2 x 0
    simpa [cf, e, extChartAt, chartAt_self_eq] using h
  have hcg : ContDiffOn ℝ ∞ cg e.target := by
    have h := (contMDiff_iff.mp (hTs g hg)).2 x 0
    simpa [cg, e, extChartAt, chartAt_self_eq] using h
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hz' : z ∈ e.target := hKt hz
    have hjtop : (↑j : ℕ∞ω) ≤ ∞ := by
      exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
    have hfz : ContDiffAt ℝ j cf z :=
      (hcf.contDiffAt (hopen.mem_nhds hz')).of_le hjtop
    have hgz : ContDiffAt ℝ j cg z :=
      (hcg.contDiffAt (hopen.mem_nhds hz')).of_le hjtop
    have hadd := iteratedFDeriv_add_apply hfz hgz
    have hbound₁ := h₁ f hf |>.1 j hj z hz
    have hbound₂ := h₂ g hg |>.1 j hj z hz
    have hadd' : iteratedFDeriv ℝ j ((f + g) ∘ e.symm) z =
        iteratedFDeriv ℝ j cf z + iteratedFDeriv ℝ j cg z := by
      change iteratedFDeriv ℝ j (cf + cg) z = _
      exact hadd
    rw [hadd']
    have hbound₁' : ‖iteratedFDeriv ℝ j cf z‖ ≤ C₁ := by simpa [cf, e] using hbound₁
    have hbound₂' : ‖iteratedFDeriv ℝ j cg z‖ ≤ C₂ := by simpa [cg, e] using hbound₂
    calc
      ‖iteratedFDeriv ℝ j cf z + iteratedFDeriv ℝ j cg z‖ ≤
          ‖iteratedFDeriv ℝ j cf z‖ + ‖iteratedFDeriv ℝ j cg z‖ := norm_add_le _ _
      _ ≤ C₁ + C₂ := add_le_add hbound₁' hbound₂'
  · have hholder₁ : HolderWith C₁ α (fun z : K ↦ iteratedFDeriv ℝ k cf z) :=
      (h₁ f hf).2.holderWith
    have hholder₂ : HolderWith C₂ α (fun z : K ↦ iteratedFDeriv ℝ k cg z) :=
      (h₂ g hg).2.holderWith
    have hholder := hholder₁.add hholder₂
    have hderiv : ∀ z ∈ K,
        iteratedFDeriv ℝ k ((f + g) ∘ e.symm) z =
          iteratedFDeriv ℝ k cf z + iteratedFDeriv ℝ k cg z := by
      intro z hz
      have hz' : z ∈ e.target := hKt hz
      have hktop : (↑k : ℕ∞ω) ≤ ∞ := by
        exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)
      have hfz : ContDiffAt ℝ k cf z :=
        (hcf.contDiffAt (hopen.mem_nhds hz')).of_le hktop
      have hgz : ContDiffAt ℝ k cg z :=
        (hcg.contDiffAt (hopen.mem_nhds hz')).of_le hktop
      have hadd := iteratedFDeriv_add_apply hfz hgz
      change iteratedFDeriv ℝ k ((f + g) ∘ e.symm) z = _
      change iteratedFDeriv ℝ k (cf + cg) z = _ at hadd
      exact hadd
    intro z hz w hw
    have hdz := hderiv z hz
    have hdw := hderiv w hw
    rw [hdz, hdw]
    exact hholder ⟨z, hz⟩ ⟨w, hw⟩

end HolderBoundedInCharts

private theorem finiteDimensional_iteratedCML [FiniteDimensional ℝ E] (k : ℕ) :
    FiniteDimensional ℝ (E [×k]→L[ℝ] ℝ) := by
  induction k with
  | zero =>
      exact Module.Finite.equiv
        (continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.symm
  | succ k ih =>
      have : FiniteDimensional ℝ (E →L[ℝ] (E [×k]→L[ℝ] ℝ)) := by infer_instance
      exact Module.Finite.equiv
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ).toLinearEquiv.symm

private theorem hasFDerivAt_limit_of_iteratedFDeriv
    {k : ℕ} {U : Set E} (hU : IsOpen U) {f : ℕ → E → ℝ}
    {gk : E → E [×k]→L[ℝ] ℝ} {gk1 : E → E [×(k + 1)]→L[ℝ] ℝ}
    (hf : ∀ n, ContDiffOn ℝ ∞ (f n) U)
    (hconv : ∀ x ∈ U, Tendsto (fun n => iteratedFDeriv ℝ k (f n) x) atTop (𝓝 (gk x)))
    (hconv1 : TendstoLocallyUniformlyOn
      (fun n => iteratedFDeriv ℝ (k + 1) (f n)) gk1 atTop U) :
    ∀ x ∈ U, HasFDerivAt gk
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ (gk1 x)) x := by
  intro x hx
  let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ
  have hcurryLip : LipschitzWith 1 curry := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [curry.dist_map]
    simp
  have hconvF : TendstoLocallyUniformlyOn
      (fun n => curry ∘ iteratedFDeriv ℝ (k + 1) (f n)) (curry ∘ gk1) atTop U :=
    hcurryLip.uniformContinuous.comp_tendstoLocallyUniformlyOn hconv1
  have hder : ∀ n, ∀ y ∈ U, HasFDerivAt (iteratedFDeriv ℝ k (f n))
      ((fun z => curry (iteratedFDeriv ℝ (k + 1) (f n) z)) y) y := by
    intro n y hy
    have hAt : ContDiffAt ℝ ∞ (f n) y := (hf n).contDiffAt (hU.mem_nhds hy)
    have hklt : (↑k : ℕ∞ω) < ∞ := by
      exact_mod_cast (show (k : ℕ∞) < ⊤ from WithTop.coe_lt_top k)
    have hdiff := hAt.differentiableAt_iteratedFDeriv hklt
    have hhas := hdiff.hasFDerivAt
    have hfd := congrFun (fderiv_iteratedFDeriv (𝕜 := ℝ) (f := f n) (n := k)) y
    rw [hfd] at hhas
    exact hhas
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn hU hconvF hder hconv hx

private theorem continuousOn_iteratedFDeriv_comp_extChart
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (x : M)
    (K : Set E) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) x).target) (k : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ k (f ∘ (extChartAt 𝓘(ℝ, E) x).symm)) K := by
  let e := extChartAt 𝓘(ℝ, E) x
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  have htop (j : ℕ) : (↑j : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
  have hcf : ContDiffOn ℝ ∞ (f ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hf).2 x 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hwithin : ContinuousOn (iteratedFDerivWithin ℝ k (f ∘ e.symm) e.target) e.target :=
    hcf.continuousOn_iteratedFDerivWithin (htop k) hopen.uniqueDiffOn
  have hEq : EqOn (iteratedFDerivWithin ℝ k (f ∘ e.symm) e.target)
      (iteratedFDeriv ℝ k (f ∘ e.symm)) e.target := by
    intro z hz
    apply iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn
    · exact (hcf.contDiffAt (hopen.mem_nhds hz)).of_le (htop k)
    · exact hz
  exact (hwithin.congr hEq.symm).mono hKt

private noncomputable def iteratedFDerivOnCompactChart
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) (x : M) (K : Set E)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) x).target) (k : ℕ) : C(K, E [×k]→L[ℝ] ℝ) :=
  ⟨K.domRestrict (fun z =>
    iteratedFDeriv ℝ k (f ∘ (extChartAt 𝓘(ℝ, E) x).symm) z),
    (continuousOn_iteratedFDeriv_comp_extChart hf x K hKt k).domRestrict⟩

private theorem exists_subseq_tendsto_iteratedFDeriv_on_compact_chart
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] {f : ℕ → M → ℝ}
    (hf : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f m))
    (hb : ∀ k, HolderBoundedInCharts E k 0 (Set.range f)) (x : M)
    (K : Set E) (hK : IsCompact K) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) x).target) (k : ℕ) :
    ∃ (G : ℕ → C(K, E [×k]→L[ℝ] ℝ)) (σ : ℕ → ℕ) (g : C(K, E [×k]→L[ℝ] ℝ)),
      (∀ m z, G m z = iteratedFDeriv ℝ k (f m ∘ (extChartAt 𝓘(ℝ, E) x).symm) z) ∧
      StrictMono σ ∧ Tendsto (fun m => G (σ m)) atTop (𝓝 g) := by
  classical
  let e := extChartAt 𝓘(ℝ, E) x
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcont (m : ℕ) : ContinuousOn (iteratedFDeriv ℝ k (f m ∘ e.symm)) K :=
    continuousOn_iteratedFDeriv_comp_extChart (hf m) x K hKt k
  let G : ℕ → C(K, E [×k]→L[ℝ] ℝ) := fun m =>
    ⟨K.domRestrict (fun z => iteratedFDeriv ℝ k (f m ∘ e.symm) z), (hcont m).domRestrict⟩
  have hG (m : ℕ) (z : K) : G m z =
      iteratedFDeriv ℝ k (f m ∘ e.symm) z := rfl
  have hEqui : Equicontinuous (fun m => (G m : K → E [×k]→L[ℝ] ℝ)) := by
    have hfRange : ∀ g ∈ Set.range f, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g := by
      intro g hg
      rcases hg with ⟨m, rfl⟩
      exact hf m
    have h1 : HolderBoundedInCharts E k 1 (Set.range f) :=
      HolderBoundedInCharts.of_succ (hb (k + 1)) hfRange (by norm_num)
    obtain ⟨C, hC⟩ := h1 x K hK hKt
    have hLip (m : ℕ) : LipschitzWith C (G m : K → E [×k]→L[ℝ] ℝ) := by
      have hh := (hC (f m) (Set.mem_range_self m)).2.holderWith
      have hh' : HolderWith C 1 (K.domRestrict (fun z =>
          iteratedFDeriv ℝ k (f m ∘ e.symm) z)) := by
        simpa [G, e, extChartAt, chartAt_self_eq] using hh
      have hh'' : HolderWith C 1 (G m : K → E [×k]→L[ℝ] ℝ) := by
        simpa [G] using hh'
      exact holderWith_one.mp hh''
    exact (LipschitzWith.uniformEquicontinuous (fun m => (G m : K → E [×k]→L[ℝ] ℝ)) C hLip).equicontinuous
  have hpoint (z : K) : ∃ Q : Set (E [×k]→L[ℝ] ℝ), IsCompact Q ∧
      ∀ᶠ m in atTop, G m z ∈ Q := by
    obtain ⟨C, hC⟩ := hb k x {z.1} isCompact_singleton (Set.singleton_subset_iff.mpr (hKt z.2))
    have : FiniteDimensional ℝ (E [×k]→L[ℝ] ℝ) := finiteDimensional_iteratedCML k
    refine ⟨Metric.closedBall 0 C, isCompact_closedBall _ _, Filter.Eventually.of_forall ?_⟩
    intro m
    have hbound := (hC (f m) (Set.mem_range_self m)).1 k le_rfl z.1 (Set.mem_singleton _)
    have hbound' : ‖G m z‖ ≤ (C : ℝ) := by rw [hG m z]; exact hbound
    exact mem_closedBall_zero_iff.mpr hbound'
  obtain ⟨σ, g, hσ, hconv⟩ :=
    CalabiYau.arzela_ascoli_subseq_tendsto_of_pointwise_compact G hEqui hpoint
  exact ⟨G, σ, g, hG, hσ, hconv⟩

private theorem exists_finite_compact_chart_neighborhood_cover
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [CompactSpace M] :
    ∃ (s : Finset M) (K V : M → Set E),
      (∀ x ∈ s, IsCompact (K x) ∧ V x ⊆ K x ∧
        K x ⊆ (extChartAt 𝓘(ℝ, E) x).target ∧ IsOpen (V x)) ∧
      ∀ y : M, ∃ x ∈ s, y ∈ (extChartAt 𝓘(ℝ, E) x).source ∩
        (extChartAt 𝓘(ℝ, E) x) ⁻¹' V x := by
  classical
  let c (x : M) : E := extChartAt 𝓘(ℝ, E) x x
  have hr (x : M) : ∃ r : ℝ, 0 < r ∧ Metric.ball (c x) r ⊆
      (extChartAt 𝓘(ℝ, E) x).target := by
    exact Metric.isOpen_iff.mp (isOpen_extChartAt_target x) (c x)
      (mem_extChartAt_target x)
  let r (x : M) : ℝ := Classical.choose (hr x)
  have hrpos (x : M) : 0 < r x := (Classical.choose_spec (hr x)).1
  have hrball (x : M) : Metric.ball (c x) (r x) ⊆
      (extChartAt 𝓘(ℝ, E) x).target := (Classical.choose_spec (hr x)).2
  let K (x : M) : Set E := Metric.closedBall (c x) (r x / 2)
  let V (x : M) : Set E := Metric.ball (c x) (r x / 2)
  have hVopen (x : M) : IsOpen (V x) := Metric.isOpen_ball
  have hVK (x : M) : V x ⊆ K x := Metric.ball_subset_closedBall
  have hKtarget (x : M) : K x ⊆ (extChartAt 𝓘(ℝ, E) x).target := by
    intro z hz
    apply hrball x
    rw [Metric.mem_ball]
    have hz' : dist (c x) z ≤ r x / 2 := by
      simpa [K, dist_comm, Metric.mem_closedBall] using hz
    rw [dist_comm] at hz'
    linarith [hrpos x]
  have hUopen (x : M) : IsOpen ((extChartAt 𝓘(ℝ, E) x).source ∩
      (extChartAt 𝓘(ℝ, E) x) ⁻¹' V x) := by
    rw [extChartAt_source (I := 𝓘(ℝ, E)) x]
    exact isOpen_extChartAt_preimage (H := E) (I := 𝓘(ℝ, E)) x (hVopen x)
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M,
      (extChartAt 𝓘(ℝ, E) x).source ∩ (extChartAt 𝓘(ℝ, E) x) ⁻¹' V x := by
    intro y _
    refine Set.mem_iUnion.2 ⟨y, ?_⟩
    constructor
    · exact mem_extChartAt_source y
    · change extChartAt 𝓘(ℝ, E) y y ∈ V y
      rw [Metric.mem_ball]
      simp [c, dist_self, hrpos]
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (extChartAt 𝓘(ℝ, E) x).source ∩
      (extChartAt 𝓘(ℝ, E) x) ⁻¹' V x) hUopen hcover
  refine ⟨s, K, V, ?_, ?_⟩
  · intro x hx
    have hKcompact : IsCompact (K x) := isCompact_closedBall _ _
    exact ⟨hKcompact, hVK x, hKtarget x, hVopen x⟩
  · intro y
    have hy := hs (Set.mem_univ y)
    rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
    exact ⟨x, hx, hyx⟩

private theorem exists_diagonal_subsequence
    (P : ℕ → (ℕ → ℕ) → Prop)
    (hsub : ∀ (k : ℕ) (s : ℕ → ℕ), StrictMono s →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ P k (s ∘ τ))
    (hstable : ∀ (k : ℕ) (s τ : ℕ → ℕ), P k s → StrictMono τ → P k (s ∘ τ))
    (htail : ∀ (k : ℕ) (s : ℕ → ℕ), P k (fun n => s (n + k + 1)) → P k s) :
    ∃ σ, StrictMono σ ∧ ∀ k, P k σ := by
  classical
  let Stage := fun k => {s : ℕ → ℕ // StrictMono s ∧ ∀ j < k, P j s}
  let base : Stage 0 := ⟨id, strictMono_id, by omega⟩
  let advance : ∀ k, Stage k → Stage (k + 1) := fun k st => by
    let τ := Classical.choose (hsub k st.1 st.2.1)
    have hτ : StrictMono τ := (Classical.choose_spec (hsub k st.1 st.2.1)).1
    have hPk : P k (st.1 ∘ τ) := (Classical.choose_spec (hsub k st.1 st.2.1)).2
    refine ⟨st.1 ∘ τ, st.2.1.comp hτ, ?_⟩
    intro j hj
    by_cases hlt : j < k
    · exact hstable j st.1 τ (st.2.2 j hlt) hτ
    · have : j = k := by omega
      subst j
      exact hPk
  let stage : ∀ k, Stage k := Nat.rec base advance
  let τ (k : ℕ) : ℕ → ℕ := Classical.choose (hsub k (stage k).1 (stage k).2.1)
  have hτ (k : ℕ) : StrictMono (τ k) :=
    (Classical.choose_spec (hsub k (stage k).1 (stage k).2.1)).1
  have hrel (k : ℕ) : (stage (k + 1)).1 = (stage k).1 ∘ τ k := rfl
  let σ (n : ℕ) : ℕ := (stage n).1 n
  have hindex_le (φ : ℕ → ℕ) (hφ : StrictMono φ) : ∀ n, n ≤ φ n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self _)))
  have hσ : StrictMono σ := strictMono_nat_of_lt_succ (fun n => by
    change (stage n).1 n < (stage (n + 1)).1 (n + 1)
    rw [hrel n]
    apply (stage n).2.1
    exact lt_of_lt_of_le (Nat.lt_succ_self n) (hindex_le (τ n) (hτ n) _))
  have hfactor (k j : ℕ) (hkj : k + 1 ≤ j) :
      ∀ m, ∃ q, (stage j).1 m = (stage (k + 1)).1 q := by
    induction j, hkj using Nat.le_induction with
    | base =>
        intro m
        exact ⟨m, rfl⟩
    | succ j hkj ih =>
        intro m
        rw [hrel j]
        exact ih (τ j m)
  let ρ (k n : ℕ) : ℕ := Classical.choose (hfactor k (k + n + 1) (by omega) (k + n + 1))
  have hρ (k n : ℕ) :
      (stage (k + n + 1)).1 (k + n + 1) = (stage (k + 1)).1 (ρ k n) :=
    Classical.choose_spec (hfactor k (k + n + 1) (by omega) (k + n + 1))
  have hρmono (k : ℕ) : StrictMono (ρ k) := by
    intro n m hnm
    apply (stage (k + 1)).2.1.lt_iff_lt.mp
    rw [← hρ k n, ← hρ k m]
    exact hσ (by omega)
  refine ⟨σ, hσ, ?_⟩
  intro k
  have hPk : P k ((stage (k + 1)).1) := (stage (k + 1)).2.2 k (by omega)
  have htailPk : P k (fun n => σ (n + k + 1)) := by
    convert hstable k (stage (k + 1)).1 (ρ k) hPk (hρmono k) using 1
    funext n
    simpa [σ, Nat.add_comm n k] using hρ k n
  exact htail k σ htailPk

private theorem exists_subseq_tendsto_all_iteratedFDeriv_on_compact_chart
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] {f : ℕ → M → ℝ}
    (hf : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f m))
    (hb : ∀ k, HolderBoundedInCharts E k 0 (Set.range f)) (x : M)
    (K : Set E) (hK : IsCompact K) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) x).target) :
    ∃ σ, StrictMono σ ∧ ∀ k, ∃ g : C(K, E [×k]→L[ℝ] ℝ),
      Tendsto (fun n => iteratedFDerivOnCompactChart (hf (σ n)) x K hKt k) atTop (𝓝 g) ∧
      TendstoUniformly (fun (n : ℕ) (z : K) =>
        iteratedFDeriv ℝ k (f (σ n) ∘ (extChartAt 𝓘(ℝ, E) x).symm) z) g atTop := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let D (k m : ℕ) : C(K, E [×k]→L[ℝ] ℝ) :=
    iteratedFDerivOnCompactChart (hf m) x K hKt k
  let P (k : ℕ) (s : ℕ → ℕ) : Prop := ∃ g, Tendsto (fun n => D k (s n)) atTop (𝓝 g)
  have hsub : ∀ (k : ℕ) (s : ℕ → ℕ), StrictMono s → ∃ τ, StrictMono τ ∧ P k (s ∘ τ) := by
    intro k s hs
    have hfs : ∀ n, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f (s n)) := fun n => hf (s n)
    have hbs : ∀ j, HolderBoundedInCharts E j 0 (Set.range (fun n => f (s n))) := by
      intro j
      apply (hb j).mono
      rintro h ⟨n, rfl⟩
      exact ⟨s n, rfl⟩
    obtain ⟨G, τ, g, hG, hτ, hconv⟩ :=
      exists_subseq_tendsto_iteratedFDeriv_on_compact_chart hfs hbs x K hK hKt k
    refine ⟨τ, hτ, g, ?_⟩
    have hEq (n : ℕ) : G (τ n) = D k (s (τ n)) := by
      ext z v
      rw [hG (τ n) z]
      rfl
    exact hconv.congr' (Filter.Eventually.of_forall hEq)
  have hstable : ∀ (k : ℕ) (s τ : ℕ → ℕ), P k s → StrictMono τ → P k (s ∘ τ) := by
    intro k s τ hconv hτ
    obtain ⟨g, hconv⟩ := hconv
    exact ⟨g, hconv.comp hτ.tendsto_atTop⟩
  have htail : ∀ (k : ℕ) (s : ℕ → ℕ), P k (fun n => s (n + k + 1)) → P k s := by
    intro k s hconv
    obtain ⟨g, hconv⟩ := hconv
    refine ⟨g, ?_⟩
    rw [Filter.tendsto_def]
    intro U hU
    change ∀ᶠ n in atTop, D k (s n) ∈ U
    have heventually := hconv.eventually hU
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
    apply Filter.eventually_atTop.2
    refine ⟨N + k + 1, ?_⟩
    intro n hn
    have hn' : N ≤ n - (k + 1) := by omega
    have hEq : n - (k + 1) + k + 1 = n := by omega
    have hmem := hN (n - (k + 1)) hn'
    change U (D k (s n))
    simpa only [hEq] using hmem
  obtain ⟨σ, hσ, hP⟩ := exists_diagonal_subsequence P hsub hstable htail
  refine ⟨σ, hσ, ?_⟩
  intro k
  obtain ⟨g, hg⟩ := hP k
  refine ⟨g, hg, ?_⟩
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hg)
    Set.univ isCompact_univ
  have hunif : TendstoUniformly (fun n (z : K) => D k (σ n) z) g atTop :=
    tendstoUniformlyOn_univ.mp hu
  simpa [D, iteratedFDerivOnCompactChart] using hunif

private theorem exists_subseq_tendsto_all_derivs_on_finite_charts
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
    (s : Finset M) (K : M → Set E)
    (hK : ∀ x ∈ s, IsCompact (K x))
    (hKt : ∀ x ∈ s, K x ⊆ (extChartAt 𝓘(ℝ, E) x).target)
    {f : ℕ → M → ℝ} (hf : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f m))
    (hb : ∀ k, HolderBoundedInCharts E k 0 (Set.range f)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ x (hx : x ∈ s) (k : ℕ),
      ∃ g : C(K x, E [×k]→L[ℝ] ℝ),
        Tendsto (fun (n : ℕ) => iteratedFDerivOnCompactChart (hf (σ n)) x (K x) (hKt x hx) k)
          atTop (𝓝 g) := by
  classical
  induction s using Finset.induction_on generalizing K f hf hb with
  | empty =>
      refine ⟨id, strictMono_id, ?_⟩
      intro x hx
      simp at hx
  | @insert x s hxs ih =>
      have hKx : IsCompact (K x) := hK x (Finset.mem_insert_self x s)
      have hKxT : K x ⊆ (extChartAt 𝓘(ℝ, E) x).target :=
        hKt x (Finset.mem_insert_self x s)
      obtain ⟨σ₁, hσ₁, hxconv⟩ :=
        exists_subseq_tendsto_all_iteratedFDeriv_on_compact_chart hf hb x (K x) hKx hKxT
      let f₁ : ℕ → M → ℝ := fun n => f (σ₁ n)
      have hf₁ : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f₁ m) := fun m => hf (σ₁ m)
      have hb₁ : ∀ k, HolderBoundedInCharts E k 0 (Set.range f₁) := by
        intro k
        apply (hb k).mono
        rintro g ⟨n, rfl⟩
        exact ⟨σ₁ n, rfl⟩
      have hKs : ∀ y ∈ s, IsCompact (K y) := by
        intro y hy
        exact hK y (Finset.mem_insert_of_mem hy)
      have hKts : ∀ y ∈ s, K y ⊆ (extChartAt 𝓘(ℝ, E) y).target := by
        intro y hy
        exact hKt y (Finset.mem_insert_of_mem hy)
      obtain ⟨σ₂, hσ₂, hsconv⟩ :=
        ih (K := K) (hK := hKs) (hKt := hKts) (hf := hf₁) (hb := hb₁)
      refine ⟨σ₁ ∘ σ₂, hσ₁.comp hσ₂, ?_⟩
      intro y hy k
      rcases Finset.mem_insert.mp hy with hyx | hys
      · subst y
        obtain ⟨g, hconv, _⟩ := hxconv k
        let : CompactSpace (K x) := isCompact_iff_compactSpace.mp hKx
        refine ⟨g, ?_⟩
        have hconv' : Tendsto
            (fun n => iteratedFDerivOnCompactChart (hf (σ₁ (σ₂ n))) x (K x) hKxT k)
            atTop (𝓝 g) := hconv.comp hσ₂.tendsto_atTop
        simpa [f₁, Function.comp_def] using hconv'
      · have h := hsconv y hys k
        rcases h with ⟨g, hconv⟩
        exact ⟨g, by simpa [f₁, Function.comp_def] using hconv⟩

private theorem exists_subseq_pointwise_limit_of_holderBoundedInCharts
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [CompactSpace M]
    {f : ℕ → M → ℝ} (hf : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f m))
    (hb : ∀ k, HolderBoundedInCharts E k 0 (Set.range f)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : M → ℝ,
      ∀ y, Tendsto (fun n => f (σ n) y) atTop (𝓝 (g y)) := by
  classical
  obtain ⟨s, K, V, hcoverBounds, hcover⟩ :=
    exists_finite_compact_chart_neighborhood_cover (E := E) (M := M)
  have hK : ∀ x ∈ s, IsCompact (K x) := fun x hx => (hcoverBounds x hx).1
  have hKt : ∀ x ∈ s, K x ⊆ (extChartAt 𝓘(ℝ, E) x).target :=
    fun x hx => (hcoverBounds x hx).2.2.1
  obtain ⟨σ, hσ, hcharts⟩ :=
    exists_subseq_tendsto_all_derivs_on_finite_charts s K hK hKt hf hb
  have hpoint (y : M) : ∃ r : ℝ, Tendsto (fun n => f (σ n) y) atTop (𝓝 r) := by
    obtain ⟨x, hx, hy⟩ := hcover y
    obtain ⟨_, hVK, _, _⟩ := hcoverBounds x hx
    let e := extChartAt 𝓘(ℝ, E) x
    let z : K x := ⟨e y, hVK hy.2⟩
    obtain ⟨g, hconv⟩ := hcharts x hx 0
    let curry := continuousMultilinearCurryFin0 ℝ E ℝ
    have heval : Tendsto (fun n =>
        curry (iteratedFDerivOnCompactChart (hf (σ n)) x (K x) (hKt x hx) 0 z))
        atTop (𝓝 (curry (g z))) := by
      have h1 : Tendsto (fun n => iteratedFDerivOnCompactChart
          (hf (σ n)) x (K x) (hKt x hx) 0 z) atTop (𝓝 (g z)) :=
        (continuous_eval_const z).continuousAt.tendsto.comp hconv
      exact curry.continuous.continuousAt.tendsto.comp h1
    have hEq (n : ℕ) : curry (iteratedFDerivOnCompactChart
        (hf (σ n)) x (K x) (hKt x hx) 0 z) = f (σ n) y := by
      have hzy : (z : E) = e y := rfl
      change curry (iteratedFDeriv ℝ 0 (f (σ n) ∘ e.symm) (z : E)) = f (σ n) y
      rw [iteratedFDeriv_zero_eq_comp]
      simp only [Function.comp_def, hzy, e.left_inv hy.1]
      change curry (ContinuousMultilinearMap.uncurry0 ℝ E (f (σ n) y)) = f (σ n) y
      rw [← continuousMultilinearCurryFin0_symm_apply]
      exact curry.apply_symm_apply _
    refine ⟨curry (g z), ?_⟩
    exact heval.congr' (Filter.Eventually.of_forall hEq)
  refine ⟨σ, hσ, fun y => Classical.choose (hpoint y), ?_⟩
  intro y
  exact Classical.choose_spec (hpoint y)

private theorem contDiffOn_of_compact_chart_limit
    [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
    {f : ℕ → M → ℝ} {σ : ℕ → ℕ} {g : M → ℝ}
    (hf : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f m))
    (hpoint : ∀ y, Tendsto (fun n => f (σ n) y) atTop (𝓝 (g y)))
    (x : M) (K U : Set E) (hK : IsCompact K)
    (hUt : U ⊆ K) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) x).target)
    (hUopen : IsOpen U)
    (hcharts : ∀ k, ∃ G : C(K, E [×k]→L[ℝ] ℝ),
      Tendsto (fun n => iteratedFDerivOnCompactChart (hf (σ n)) x K hKt k) atTop (𝓝 G)) :
    ∃ G : ∀ k, C(K, E [×k]→L[ℝ] ℝ),
      (∀ k, Tendsto (fun n => iteratedFDerivOnCompactChart (hf (σ n)) x K hKt k) atTop
        (𝓝 (G k))) ∧
      ContDiffOn ℝ ∞ (fun z => g ((extChartAt 𝓘(ℝ, E) x).symm z)) U ∧
      ∀ k z (hz : z ∈ U),
        G k ⟨z, hUt hz⟩ = iteratedFDeriv ℝ k
          (fun z => g ((extChartAt 𝓘(ℝ, E) x).symm z)) z := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G (k : ℕ) : C(K, E [×k]→L[ℝ] ℝ) := Classical.choose (hcharts k)
  have hG (k : ℕ) : Tendsto
      (fun n => iteratedFDerivOnCompactChart (hf (σ n)) x K hKt k) atTop (𝓝 (G k)) :=
    Classical.choose_spec (hcharts k)
  let W (k : ℕ) (z : E) : E [×k]→L[ℝ] ℝ :=
    if hz : z ∈ K then G k ⟨z, hz⟩ else 0
  have hUk (z : E) (hz : z ∈ U) : z ∈ K := hUt hz
  have hpointD (k : ℕ) (z : E) (hz : z ∈ U) :
      Tendsto (fun n => iteratedFDeriv ℝ k (f (σ n) ∘ (extChartAt 𝓘(ℝ, E) x).symm) z)
        atTop (𝓝 (W k z)) := by
    have heval : Tendsto (fun n =>
        iteratedFDerivOnCompactChart (hf (σ n)) x K hKt k ⟨z, hUk z hz⟩)
        atTop (𝓝 (G k ⟨z, hUk z hz⟩)) :=
      (continuous_eval_const (⟨z, hUk z hz⟩ : K)).continuousAt.tendsto.comp (hG k)
    simpa [iteratedFDerivOnCompactChart, W, hUk z hz] using heval
  have huniform (k : ℕ) : TendstoUniformly
      (fun n (z : K) => iteratedFDerivOnCompactChart (hf (σ n)) x K hKt k z) (G k) atTop := by
    have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp (hG k))
      Set.univ isCompact_univ
    exact tendstoUniformlyOn_univ.mp hu
  have hloc (k : ℕ) : TendstoLocallyUniformlyOn
      (fun n z => iteratedFDeriv ℝ k (f (σ n) ∘ (extChartAt 𝓘(ℝ, E) x).symm) z)
      (W k) atTop U := by
    intro u hu z hz
    refine ⟨U, self_mem_nhdsWithin, ?_⟩
    have heventually := huniform k u hu
    filter_upwards [heventually] with n hn y hy
    simpa [iteratedFDerivOnCompactChart, W, hUk y hy] using hn ⟨y, hUk y hy⟩
  have hcoordSmooth (n : ℕ) : ContDiffOn ℝ ∞
      (f (σ n) ∘ (extChartAt 𝓘(ℝ, E) x).symm) U := by
    have h := (contMDiff_iff.mp (hf (σ n))).2 x 0
    have h' : ContDiffOn ℝ ∞ (f (σ n) ∘ (extChartAt 𝓘(ℝ, E) x).symm)
        (extChartAt 𝓘(ℝ, E) x).target := by
      simpa [extChartAt, chartAt_self_eq] using h
    exact h'.mono (Set.Subset.trans hUt hKt)
  have hcompat (k : ℕ) (z : E) (hz : z ∈ U) : HasFDerivAt (W k)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ) (W (k + 1) z)) z :=
    hasFDerivAt_limit_of_iteratedFDeriv hUopen hcoordSmooth (hpointD k) (hloc (k + 1)) z hz
  have hcontinuous (k : ℕ) : ContinuousOn (W k) U := by
    let φ : U → K := fun z => ⟨(z : E), hUk z z.property⟩
    have hmap : Continuous φ :=
      Continuous.subtype_mk continuous_subtype_val (fun z => hUk z z.property)
    have heq : U.domRestrict (W k) = (G k) ∘ φ := by
      ext z v
      change (W k (z : E)) v = (G k (φ z)) v
      simp [W, φ, hUk (z : E) z.property]
    rw [continuousOn_iff_continuous_domRestrict, heq]
    exact (G k).continuous.comp hmap
  have htower : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ n (W k) U := by
    intro n
    induction n with
    | zero =>
        intro k
        simpa using hcontinuous k
    | succ n ih =>
        intro k
        let : FiniteDimensional ℝ (E [×k]→L[ℝ] ℝ) := finiteDimensional_iteratedCML k
        let : FiniteDimensional ℝ (E [×(k + 1)]→L[ℝ] ℝ) :=
          finiteDimensional_iteratedCML (k + 1)
        change ContDiffOn ℝ ((n : ℕ∞) + 1) (W k) U
        rw [contDiffOn_succ_iff_fderiv_of_isOpen (n := (n : ℕ∞)) hUopen]
        refine ⟨?_, ?_, ?_⟩
        · intro z hz
          exact (hcompat k z hz).differentiableAt.differentiableWithinAt
        · simp
        · have hcomp : ContDiffOn ℝ n
              (fun z => (continuousMultilinearCurryLeftEquiv ℝ
                (fun _ : Fin (k + 1) => E) ℝ).toContinuousLinearMap (W (k + 1) z)) U :=
              (ih (k + 1)).continuousLinearMap_comp _
          apply hcomp.congr
          intro z hz
          convert (hcompat k z hz).fderiv using 1; rfl
  have hW : ContDiffOn ℝ ∞ (W 0) U := contDiffOn_infty.2 fun n => htower n 0
  let curry0 := continuousMultilinearCurryFin0 ℝ E ℝ
  have hbase (z : E) (hz : z ∈ U) : curry0 (W 0 z) = g ((extChartAt 𝓘(ℝ, E) x).symm z) := by
    have hEval : Tendsto (fun n => curry0 (iteratedFDeriv ℝ 0
        (f (σ n) ∘ (extChartAt 𝓘(ℝ, E) x).symm) z)) atTop
        (𝓝 (curry0 (W 0 z))) :=
      (curry0.continuous.continuousAt.tendsto.comp (hpointD 0 z hz))
    have hlim := hpoint ((extChartAt 𝓘(ℝ, E) x).symm z)
    have heq (n : ℕ) : curry0 (iteratedFDeriv ℝ 0
        (f (σ n) ∘ (extChartAt 𝓘(ℝ, E) x).symm) z) =
        f (σ n) ((extChartAt 𝓘(ℝ, E) x).symm z) := by
      rw [iteratedFDeriv_zero_eq_comp]
      exact curry0.apply_symm_apply _
    have hEval' : Tendsto (fun n => f (σ n) ((extChartAt 𝓘(ℝ, E) x).symm z)) atTop
        (𝓝 (curry0 (W 0 z))) := hEval.congr' (Filter.Eventually.of_forall heq)
    exact tendsto_nhds_unique hEval' hlim
  have hscalar : ContDiffOn ℝ ∞ (fun z => g ((extChartAt 𝓘(ℝ, E) x).symm z)) U := by
    have hcomp : ContDiffOn ℝ ∞ (fun z => curry0 (W 0 z)) U :=
      curry0.contDiff.comp_contDiffOn hW
    exact hcomp.congr fun z hz => (hbase z hz).symm
  have hjet (k : ℕ) : ∀ z ∈ U,
      W k z = iteratedFDeriv ℝ k (fun z => g ((extChartAt 𝓘(ℝ, E) x).symm z)) z := by
    induction k with
    | zero =>
        intro z hz
        have h0 : curry0 (iteratedFDeriv ℝ 0
            (fun z => g ((extChartAt 𝓘(ℝ, E) x).symm z)) z) =
            g ((extChartAt 𝓘(ℝ, E) x).symm z) := by
          rw [iteratedFDeriv_zero_eq_comp]
          change curry0 (ContinuousMultilinearMap.uncurry0 ℝ E
            (g ((extChartAt 𝓘(ℝ, E) x).symm z))) = _
          rw [← continuousMultilinearCurryFin0_symm_apply]
          exact curry0.apply_symm_apply _
        apply curry0.injective
        calc
          curry0 (W 0 z) = g ((extChartAt 𝓘(ℝ, E) x).symm z) := hbase z hz
          _ = curry0 (iteratedFDeriv ℝ 0
              (fun z => g ((extChartAt 𝓘(ℝ, E) x).symm z)) z) := h0.symm
    | succ k ih =>
        intro z hz
        let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ
        have hlocal : W k =ᶠ[𝓝 z]
            iteratedFDeriv ℝ k (fun z => g ((extChartAt 𝓘(ℝ, E) x).symm z)) := by
          filter_upwards [hUopen.mem_nhds hz] with w hw
          exact ih w hw
        have hderiv := (hcompat k z hz).fderiv
        rw [hlocal.fderiv_eq, fderiv_iteratedFDeriv] at hderiv
        exact curry.injective hderiv.symm
  refine ⟨G, (fun k => hG k), hscalar, ?_⟩
  intro k z hz
  simpa [W, hUk z hz] using hjet k z hz

/-- **Arzelà–Ascoli in `C^∞`.** On a compact manifold, a sequence of smooth functions which is
bounded in `C^k` for every `k` has a subsequence converging, with all derivatives, locally
uniformly in every chart, to a smooth function. -/
private theorem exists_subseq_tendsto_of_holderBoundedInCharts_aux
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [FiniteDimensional ℝ E] [CompactSpace M] {f : ℕ → M → ℝ}
    (hf : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f m))
    (hb : ∀ k, HolderBoundedInCharts E k 0 (Set.range f)) :
    ∃ (g : M → ℝ) (σ : ℕ → ℕ), StrictMono σ ∧ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g ∧
      ∀ (k : ℕ) (x : M), TendstoLocallyUniformlyOn
        (fun m ↦ iteratedFDeriv ℝ k (f (σ m) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (iteratedFDeriv ℝ k (g ∘ (extChartAt 𝓘(ℝ, E) x).symm)) atTop
        (extChartAt 𝓘(ℝ, E) x).target := by
  obtain ⟨σ, hσ, g, hpoint⟩ := exists_subseq_pointwise_limit_of_holderBoundedInCharts hf hb
  have hregular : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g ∧
      ∀ (k : ℕ) (x : M), TendstoLocallyUniformlyOn
        (fun m ↦ iteratedFDeriv ℝ k (f (σ m) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (iteratedFDeriv ℝ k (g ∘ (extChartAt 𝓘(ℝ, E) x).symm)) atTop
        (extChartAt 𝓘(ℝ, E) x).target := by
    classical
    obtain ⟨s, K, V, hcoverBounds, hcover⟩ :=
      exists_finite_compact_chart_neighborhood_cover (E := E) (M := M)
    have hK : ∀ x ∈ s, IsCompact (K x) := fun x hx => (hcoverBounds x hx).1
    have hKt : ∀ x ∈ s, K x ⊆ (extChartAt 𝓘(ℝ, E) x).target :=
      fun x hx => (hcoverBounds x hx).2.2.1
    let f₀ : ℕ → M → ℝ := fun n => f (σ n)
    have hf₀ : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f₀ m) := fun m => hf (σ m)
    have hb₀ : ∀ k, HolderBoundedInCharts E k 0 (Set.range f₀) := by
      intro k
      apply (hb k).mono
      rintro u ⟨m, rfl⟩
      exact ⟨σ m, rfl⟩
    obtain ⟨σ', hσ', hcharts⟩ :=
      exists_subseq_tendsto_all_derivs_on_finite_charts s K hK hKt hf₀ hb₀
    have hpoint' : ∀ y, Tendsto (fun n => f (σ (σ' n)) y) atTop (𝓝 (g y)) := by
      intro y
      exact (hpoint y).comp hσ'.tendsto_atTop
    have hchartSmooth (x : M) (hx : x ∈ s) :
        ContDiffOn ℝ ∞ (fun z => g ((extChartAt 𝓘(ℝ, E) x).symm z)) (V x) := by
      obtain ⟨_, _, hsmooth, _⟩ := contDiffOn_of_compact_chart_limit hf₀ hpoint' x
        (K x) (V x) (hK x hx) (hcoverBounds x hx).2.1 (hKt x hx)
        (hcoverBounds x hx).2.2.2 (fun k => hcharts x hx k)
      exact hsmooth
    have hAt (y : M) : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ g y := by
      obtain ⟨x, hx, hy⟩ := hcover y
      let e := extChartAt 𝓘(ℝ, E) x
      have hysource : y ∈ (chartAt E x).source := by
        simpa only [extChartAt_source] using hy.1
      have hyV : e y ∈ V x := by
        simpa [e] using hy.2
      have hcoord : ContDiffAt ℝ ∞ (fun z => g (e.symm z)) (e y) :=
        (hchartSmooth x hx).contDiffAt
          ((hcoverBounds x hx).2.2.2.mem_nhds hyV)
      have hcoord' : ContDiffAt ℝ ∞ (g ∘ (chartAt E x).symm) ((chartAt E x) y) := by
        simpa only [Function.comp_def] using
          (show ContDiffAt ℝ ∞ (fun z => g ((chartAt E x).symm z)) ((chartAt E x) y) by
            simpa [e, extChartAt_coe_symm, extChartAt_coe] using hcoord)
      have heCont : ContinuousAt e y :=
        ((continuousOn_extChartAt x).continuousWithinAt hy.1).continuousAt
          ((isOpen_extChartAt_source x).mem_nhds hy.1)
      let c : E → ℝ := fun z => g (e.symm z)
      have hcomp : ContinuousAt (c ∘ e) y := hcoord.continuousAt.comp heCont
      have hEq : c ∘ e =ᶠ[𝓝 y] g := by
        filter_upwards [(isOpen_extChartAt_source x).mem_nhds hy.1] with q hq
        simp only [Function.comp_apply, c]
        rw [e.left_inv hq]
      have hgySource : g y ∈ (chartAt ℝ (g y)).source := by simp
      apply (contMDiffAt_iff_of_mem_source
        (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ)) (x := x) (x' := y)
        (y := g y) hysource hgySource).2
      refine ⟨hcomp.congr_of_eventuallyEq hEq.symm, ?_⟩
      simpa [extChartAt, chartAt_self_eq, ModelWithCorners.range_eq_univ,
        contDiffWithinAt_univ] using hcoord'
    refine ⟨?_, ?_⟩
    · exact fun y => hAt y
    · have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g := fun y => hAt y
      intro k x
      let e := extChartAt 𝓘(ℝ, E) x
      have heOpen : IsOpen e.target := isOpen_extChartAt_target x
      apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
      intro z hz
      obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.mp (heOpen.mem_nhds hz)
      let L : Set E := Metric.closedBall z (R / 2)
      let U : Set E := Metric.ball z (R / 2)
      let K : Set E := Metric.closedBall z (R / 4)
      have hLcompact : IsCompact L := by
        exact isCompact_closedBall _ _
      have hLtarget : L ⊆ e.target := by
        intro w hw
        have hw' : dist w z ≤ R / 2 := by
          simpa [L, Metric.mem_closedBall] using hw
        have hlt : dist w z < R := lt_of_le_of_lt hw' (by linarith)
        exact hRball (Metric.mem_ball.mpr (by simpa [dist_comm] using hlt))
      have hUL : U ⊆ L := by
        intro w hw
        have hw' : dist w z < R / 2 := by
          simpa [U, Metric.mem_ball] using hw
        exact Metric.mem_closedBall.mpr hw'.le
      have hUopen : IsOpen U := Metric.isOpen_ball
      have hKcompact : IsCompact K := isCompact_closedBall _ _
      have hKU : K ⊆ U := by
        intro w hw
        have hw' : dist w z ≤ R / 4 := by
          simpa [K, Metric.mem_closedBall] using hw
        have hlt : dist w z < R / 2 := lt_of_le_of_lt hw' (by linarith)
        exact Metric.mem_ball.mpr (by simpa [dist_comm] using hlt)
      have hKtarget : K ⊆ e.target := Set.Subset.trans hKU (Set.Subset.trans hUL hLtarget)
      let q : ℕ → C(K, E [×k]→L[ℝ] ℝ) := fun n =>
        ⟨K.domRestrict (fun w => iteratedFDeriv ℝ k (f (σ n) ∘ e.symm) w),
          (continuousOn_iteratedFDeriv_comp_extChart (hf (σ n)) x K hKtarget k).domRestrict⟩
      let qlim : C(K, E [×k]→L[ℝ] ℝ) :=
        ⟨K.domRestrict (fun w => iteratedFDeriv ℝ k (g ∘ e.symm) w),
          (continuousOn_iteratedFDeriv_comp_extChart hg x K hKtarget k).domRestrict⟩
      have hq : Tendsto q atTop (𝓝 qlim) := by
        apply tendsto_of_subseq_tendsto
        intro ns hns
        let fns : ℕ → M → ℝ := fun m => f (σ (ns m))
        have hfns : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fns m) := fun m => hf (σ (ns m))
        have hbns : ∀ j, HolderBoundedInCharts E j 0 (Set.range fns) := by
          intro j
          apply (hb j).mono
          rintro u ⟨m, rfl⟩
          exact ⟨σ (ns m), rfl⟩
        obtain ⟨τ, hτ, hcharts⟩ :=
          exists_subseq_tendsto_all_iteratedFDeriv_on_compact_chart
            hfns hbns x L hLcompact hLtarget
        have hpointns : ∀ y, Tendsto (fun m => fns (τ m) y) atTop (𝓝 (g y)) := by
          intro y
          exact (hpoint y).comp (hns.comp hτ.tendsto_atTop)
        have hcharts' : ∀ j, ∃ G : C(L, E [×j]→L[ℝ] ℝ),
            Tendsto (fun m => iteratedFDerivOnCompactChart (hfns (τ m)) x L hLtarget j)
              atTop (𝓝 G) := by
          intro j
          obtain ⟨G, hG, _⟩ := hcharts j
          exact ⟨G, hG⟩
        obtain ⟨G, hG, _, hGjet⟩ := contDiffOn_of_compact_chart_limit
          hfns hpointns x L U hLcompact hUL hLtarget hUopen hcharts'
        have hGuniform : TendstoUniformly
            (fun m (w : L) => iteratedFDeriv ℝ k (fns (τ m) ∘ e.symm) w)
            (G k) atTop := by
          have hOn := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
            (hG k)) Set.univ isCompact_univ
          exact tendstoUniformlyOn_univ.mp hOn
        have hKuniform : TendstoUniformly
            (fun m (w : K) => iteratedFDeriv ℝ k (fns (τ m) ∘ e.symm) w)
            (fun w => iteratedFDeriv ℝ k (g ∘ e.symm) w) atTop := by
          rw [Metric.tendstoUniformly_iff]
          intro ε hε
          have hevent := Metric.tendstoUniformly_iff.mp hGuniform ε hε
          filter_upwards [hevent] with m hm
          intro w
          have hwU : (w : E) ∈ U := hKU w.property
          have hwL : (w : E) ∈ L := hUL hwU
          have hjet := hGjet k (w : E) hwU
          have hdist := hm ⟨(w : E), hwL⟩
          have hjet' : (G k) ⟨(w : E), hwL⟩ =
              iteratedFDeriv ℝ k (g ∘ e.symm) (w : E) := by
            calc
              (G k) ⟨(w : E), hwL⟩ = (G k) ⟨(w : E), hUL hwU⟩ := by
                congr 1
              _ = iteratedFDeriv ℝ k
                  (fun v => g ((extChartAt 𝓘(ℝ, E) x).symm v)) (w : E) := hjet
              _ = iteratedFDeriv ℝ k
                  (fun v => g ((chartAt E x).symm v)) (w : E) := by
                congr 1
              _ = iteratedFDeriv ℝ k (g ∘ e.symm) (w : E) := by
                have hcoord : (g ∘ e.symm) =
                    (fun v => g ((chartAt E x).symm v)) := by
                  funext v
                  simp [e]
                exact (congrArg (fun v => iteratedFDeriv ℝ k v (w : E)) hcoord).symm
          rw [hjet'] at hdist
          simpa [iteratedFDerivOnCompactChart, Function.comp_def] using hdist
        have hqsub : Tendsto (fun m => q (ns (τ m))) atTop (𝓝 qlim) := by
          rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
          intro A hA
          have hOn : TendstoUniformlyOn
              (fun m (w : K) => iteratedFDeriv ℝ k (fns (τ m) ∘ e.symm) w)
              (fun w => iteratedFDeriv ℝ k (g ∘ e.symm) w) atTop Set.univ :=
            tendstoUniformlyOn_univ.mpr hKuniform
          have hOnA := hOn.mono (Set.subset_univ A)
          change TendstoUniformlyOn
            (fun m (w : K) => iteratedFDeriv ℝ k (fns (τ m) ∘ e.symm) w)
            (fun (w : K) => iteratedFDeriv ℝ k (g ∘ e.symm) w) atTop A
          exact hOnA
        exact ⟨τ, hqsub⟩
      have hqunif : TendstoUniformly
          (fun m (w : K) => iteratedFDeriv ℝ k (f (σ m) ∘ e.symm) w)
          (fun w => iteratedFDeriv ℝ k (g ∘ e.symm) w) atTop := by
        have hOn := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
          hq) Set.univ isCompact_univ
        exact tendstoUniformlyOn_univ.mp hOn
      have hballUniform : TendstoUniformlyOn
          (fun m w => iteratedFDeriv ℝ k (f (σ m) ∘ e.symm) w)
          (iteratedFDeriv ℝ k (g ∘ e.symm)) atTop (Metric.ball z (R / 4)) := by
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        have hevent := Metric.tendstoUniformly_iff.mp hqunif ε hε
        filter_upwards [hevent] with m hm
        intro w hw
        exact hm ⟨w, by simpa [K, Metric.mem_closedBall] using (Metric.mem_ball.mp hw).le⟩
      have hballNhds : Metric.ball z (R / 4) ∈ 𝓝[e.target] z := by
        apply Metric.mem_nhdsWithin_iff.mpr
        refine ⟨R / 4, by positivity, ?_⟩
        intro w hw
        exact hw.1
      exact ⟨Metric.ball z (R / 4), hballNhds, hballUniform⟩
  exact ⟨g, σ, hσ, hregular.1, hregular.2⟩

/-- **Arzelà–Ascoli in `C^∞`.** On a compact manifold, a sequence of smooth functions which is
bounded in `C^k` for every `k` has a subsequence converging, with all derivatives, locally
uniformly in every chart, to a smooth function. -/
theorem exists_subseq_tendsto_of_holderBoundedInCharts [IsManifold 𝓘(ℝ, E) ∞ M]
    [FiniteDimensional ℝ E] [CompactSpace M] {f : ℕ → M → ℝ}
    (hf : ∀ m, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (f m))
    (hb : ∀ k, HolderBoundedInCharts E k 0 (Set.range f)) :
    ∃ (g : M → ℝ) (σ : ℕ → ℕ), StrictMono σ ∧ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g ∧
      ∀ (k : ℕ) (x : M), TendstoLocallyUniformlyOn
        (fun m ↦ iteratedFDeriv ℝ k (f (σ m) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (iteratedFDeriv ℝ k (g ∘ (extChartAt 𝓘(ℝ, E) x).symm)) atTop
        (extChartAt 𝓘(ℝ, E) x).target := by
  exact exists_subseq_tendsto_of_holderBoundedInCharts_aux hf hb
