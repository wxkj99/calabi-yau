module

public import CalabiYau.Analysis.Holder.Compactness
public import CalabiYau.Geometry.Complex.Holder
public import CalabiYau.Geometry.Complex.Schauder.HolderLimit
public import CalabiYau.Geometry.Complex.Schauder.SchauderCompactness.ConvexJetLipschitz

/-!
# Compactness of Schauder jets

A common `C^{2,α}` estimate on a compact interior set gives Arzelà–Ascoli compactness of its
second derivative jets. The exponent drops under Hölder interpolation; this module does not claim
compactness at the original exponent or existence of PDE solutions.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace CalabiYau.Schauder

private theorem exists_holder_bounds_lowerJets_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} (hK : IsCompact K) (hKconvex : Convex ℝ K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : ℕ → E → F}
    {α C : ℝ≥0} (hαone : α ≤ 1)
    (hsmooth : ∀ n, ContDiffOn ℝ 2 (f n) U)
    (hbound : ∀ n, HolderBoundOn 2 α C K (f n)) :
    ∃ C₀ C₁ : ℝ≥0, ∀ n,
      HolderWith C₀ α (fun x : K => iteratedFDeriv ℝ 1 (f n) (x : E)) ∧
      HolderWith C₁ α (fun x : K => f n (x : E)) := by
  let C' : ℝ≥0 := C * (Metric.ediam K).toNNReal ^ ((1 : ℝ) - (α : ℝ))
  refine ⟨C', C', ?_⟩
  intro n
  have hLip := lipschitzOnWith_function_and_firstDerivative_of_holderBoundOn
    hKconvex hU hKU (hsmooth n) (hbound n)
  have hZeroOn : HolderOnWith C' α (f n) K := by
    simpa [C'] using
      holderOnWith_of_lipschitzOnWith_of_compact hK hLip.1 hαone
  have hFirstOn : HolderOnWith C' α
      (fun x => iteratedFDeriv ℝ 1 (f n) x) K := by
    simpa [C'] using
      holderOnWith_of_lipschitzOnWith_of_compact hK hLip.2 hαone
  constructor
  · change HolderWith C' α
      (K.domRestrict (fun x => iteratedFDeriv ℝ 1 (f n) x))
    exact hFirstOn.holderWith
  · change HolderWith C' α (K.domRestrict (f n))
    exact hZeroOn.holderWith

/-- The common second-derivative Hölder bound and its supremum bound pass to a locally uniform
limit, using `holderOnWith_and_norm_le_of_tendstoLocallyUniformlyOn`. -/
theorem secondDerivative_holderBoundOn_of_tendstoLocallyUniformlyOn
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} [NeBot l]
    {K : Set E} {f : ι → E → F} {g : E → E [×2]→L[ℝ] F}
    {α C : ℝ≥0}
    (hbound : ∀ i, HolderBoundOn 2 α C K (f i))
    (hLimit : TendstoLocallyUniformlyOn
      (fun i x => iteratedFDeriv ℝ 2 (f i) x) g l K) :
    HolderOnWith C α g K ∧ ∀ x ∈ K, ‖g x‖ ≤ (C : ℝ) := by
  exact holderOnWith_and_norm_le_of_tendstoLocallyUniformlyOn
    (fun i => (hbound i).2)
    (fun i x hx => (hbound i).1 2 le_rfl x hx)
    hLimit

private theorem holderWith_lower_exponent_of_norm_le
    {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F]
    {α β C δ : ℝ≥0} {f : X → F}
    (hα : 0 < α) (hβα : β < α)
    (hf : HolderWith C α f) (hsmall : ∀ x, ‖f x‖ ≤ δ) :
    HolderWith
      (C ^ ((β / α : ℝ≥0) : ℝ) * (2 * δ) ^ ((1 - β / α : ℝ≥0) : ℝ))
      β f := by
  let θ₁ : ℝ≥0 := β / α
  let θ₂ : ℝ≥0 := 1 - β / α
  have hdiv : β / α < 1 := (div_lt_one₀ hα).2 hβα
  have hθ₂ : 0 < θ₂ := by
    dsimp [θ₂]
    exact tsub_pos_of_lt hdiv
  have hθ : θ₁ + θ₂ = 1 := by
    dsimp [θ₁, θ₂]
    exact add_tsub_cancel_of_le hdiv.le
  have hθt : α * θ₁ + 0 * θ₂ = β := by
    dsimp [θ₁]
    rw [zero_mul, add_zero, mul_comm]
    exact div_mul_cancel₀ β hα.ne'
  have hzero : HolderWith (2 * δ) 0 f := holderWith_zero_of_norm_le hsmall
  have hinterp := hf.interpolate hzero hθ
  rw [hθt] at hinterp
  simpa [θ₁, θ₂] using hinterp

private theorem tendsto_holderWith_lower_exponent_of_uniform
    {X F : Type*} [PseudoMetricSpace X] [NormedAddCommGroup F]
    {α β C : ℝ≥0} (hα : 0 < α) (hβα : β < α)
    {f : ℕ → X → F} {g : X → F}
    (hHolder : ∀ n, HolderWith C α (f n)) (hg : HolderWith C α g)
    (hUniform : TendstoUniformly f g atTop) :
    ∀ ε : ℝ≥0, 0 < ε → ∀ᶠ n in atTop,
      HolderWith ε β (fun x => f n x - g x) := by
  let θ₂ : ℝ≥0 := 1 - β / α
  have hdiv : β / α < 1 := (div_lt_one₀ hα).2 hβα
  have hθ₂ : 0 < θ₂ := by
    dsimp [θ₂]
    exact tsub_pos_of_lt hdiv
  let q : ℝ≥0 → ℝ≥0 := fun δ =>
    (2 * C) ^ ((β / α : ℝ≥0) : ℝ) * (2 * δ) ^ (θ₂ : ℝ)
  have hqcont : Continuous q := by
    dsimp [q]
    exact continuous_const.mul <|
      (NNReal.continuous_rpow_const hθ₂.le).comp (continuous_const.mul continuous_id)
  have hqzero : q 0 = 0 := by
    simp [q, hθ₂.ne']
  intro ε hε
  have hqevent : ∀ᶠ δ : ℝ≥0 in 𝓝 0, q δ < ε := by
    have h0ε : q 0 < ε := by rw [hqzero]; exact hε
    have hcont := hqcont.continuousAt.eventually (Iio_mem_nhds h0ε)
    simpa [hqzero] using hcont
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hqevent
  let δ : ℝ≥0 := Real.toNNReal (r / 2)
  have hδpos : 0 < δ := Real.toNNReal_pos.mpr (by linarith)
  have hδball : dist δ (0 : ℝ≥0) < r := by
    have hδcoe : (δ : ℝ) = r / 2 := by
      simp [δ, Real.coe_toNNReal (r / 2) (by linarith)]
    simp only [NNReal.dist_eq, NNReal.coe_zero, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg δ)]
    rw [hδcoe]
    linarith
  have hqδ : q δ < ε := hball (Metric.mem_ball.mpr hδball)
  have hclose : ∀ᶠ n in atTop, ∀ x, ‖f n x - g x‖ ≤ δ := by
    have ht := Metric.tendstoUniformly_iff.mp hUniform (δ : ℝ)
      (NNReal.coe_pos.mpr hδpos)
    filter_upwards [ht] with n hn x
    have hx := hn x
    rw [dist_eq_norm] at hx
    calc
      ‖f n x - g x‖ = ‖g x - f n x‖ := norm_sub_rev _ _
      _ ≤ δ := hx.le
  filter_upwards [hclose] with n hn
  apply (holderWith_lower_exponent_of_norm_le hα hβα
    (holderWith_sub (hHolder n) hg) (hn)).mono
  simpa [q, two_mul] using hqδ.le

private theorem secondDerivative_tendsto_holderWith_lower_exponent
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {f : ℕ → E → F} {g : K → E [×2]→L[ℝ] F}
    {α β C : ℝ≥0} (hα : 0 < α) (hβα : β < α)
    (hbound : ∀ n, HolderBoundOn 2 α C K (f n))
    (hUniform : TendstoUniformly
      (fun n (x : K) => iteratedFDeriv ℝ 2 (f n) (x : E)) g atTop) :
    ∀ ε : ℝ≥0, 0 < ε → ∀ᶠ n in atTop,
      HolderWith ε β (fun x : K =>
        iteratedFDeriv ℝ 2 (f n) (x : E) - g x) := by
  have hHolder (n : ℕ) : HolderWith C α
      (fun x : K => iteratedFDeriv ℝ 2 (f n) (x : E)) := by
    change HolderWith C α
      (K.domRestrict (fun x => iteratedFDeriv ℝ 2 (f n) x))
    exact (hbound n).2.holderWith
  have hlimitOn : HolderOnWith C α g Set.univ :=
    holderOnWith_of_tendsto (l := atTop)
      (Eventually.of_forall fun n => holderOnWith_univ.mpr (hHolder n))
      (fun x _ => hUniform.tendsto_at x)
  have hg : HolderWith C α g := holderOnWith_univ.mp hlimitOn
  exact tendsto_holderWith_lower_exponent_of_uniform hα hβα
    hHolder hg hUniform

private theorem tendstoUniformly_comp_subsequence
    {X Y : Type*} [PseudoMetricSpace Y]
    {f : ℕ → X → Y} {g : X → Y} {φ : ℕ → ℕ}
    (h : TendstoUniformly f g atTop) (hφ : StrictMono φ) :
    TendstoUniformly (fun n => f (φ n)) g atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  exact hφ.tendsto_atTop (h ε hε)

private theorem exists_subseq_tendstoUniformly_threeFamilies
    {X V₀ V₁ V₂ : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [LocallyCompactSpace X] [SigmaCompactSpace X]
    [NormedAddCommGroup V₀] [ProperSpace V₀]
    [NormedAddCommGroup V₁] [ProperSpace V₁]
    [NormedAddCommGroup V₂] [ProperSpace V₂]
    {f₀ : ℕ → X → V₀} {f₁ : ℕ → X → V₁} {f₂ : ℕ → X → V₂}
    {C₀ C₁ C₂ α : ℝ≥0} (hα : 0 < α)
    (hH₀ : ∀ n, HolderWith C₀ α (f₀ n))
    (hH₁ : ∀ n, HolderWith C₁ α (f₁ n))
    (hH₂ : ∀ n, HolderWith C₂ α (f₂ n))
    (hB₀ : ∀ x, ∃ M : ℝ, ∀ n, ‖f₀ n x‖ ≤ M)
    (hB₁ : ∀ x, ∃ M : ℝ, ∀ n, ‖f₁ n x‖ ≤ M)
    (hB₂ : ∀ x, ∃ M : ℝ, ∀ n, ‖f₂ n x‖ ≤ M) :
    ∃ (φ : ℕ → ℕ) (g₀ : X → V₀) (g₁ : X → V₁) (g₂ : X → V₂),
      StrictMono φ ∧ Continuous g₀ ∧ Continuous g₁ ∧ Continuous g₂ ∧
      TendstoUniformly (fun n => f₀ (φ n)) g₀ atTop ∧
      TendstoUniformly (fun n => f₁ (φ n)) g₁ atTop ∧
      TendstoUniformly (fun n => f₂ (φ n)) g₂ atTop := by
  obtain ⟨φ₀, g₀, hφ₀, hg₀, hconv₀⟩ :=
    arzela_ascoli_subseq_tendsto_locally_uniformly_of_holderWith f₀ hα hH₀ hB₀
  let f₁' : ℕ → X → V₁ := fun n => f₁ (φ₀ n)
  have hH₁' (n : ℕ) : HolderWith C₁ α (f₁' n) := hH₁ (φ₀ n)
  have hB₁' : ∀ x, ∃ M : ℝ, ∀ n, ‖f₁' n x‖ ≤ M := by
    intro x
    obtain ⟨M, hM⟩ := hB₁ x
    exact ⟨M, fun n => hM (φ₀ n)⟩
  obtain ⟨φ₁, g₁, hφ₁, hg₁, hconv₁⟩ :=
    arzela_ascoli_subseq_tendsto_locally_uniformly_of_holderWith f₁' hα hH₁' hB₁'
  let φ₀₁ : ℕ → ℕ := φ₀ ∘ φ₁
  have hφ₀₁ : StrictMono φ₀₁ := hφ₀.comp hφ₁
  have hconv₀U : TendstoUniformly (fun n => f₀ (φ₀ n)) g₀ atTop :=
    tendstoUniformlyOn_univ.mp (hconv₀ Set.univ isCompact_univ)
  have hconv₀₁ : TendstoUniformly (fun n => f₀ (φ₀₁ n)) g₀ atTop := by
    simpa [φ₀₁, Function.comp_def] using
      tendstoUniformly_comp_subsequence hconv₀U hφ₁
  have hconv₁U : TendstoUniformly (fun n => f₁' (φ₁ n)) g₁ atTop :=
    tendstoUniformlyOn_univ.mp (hconv₁ Set.univ isCompact_univ)
  have hconv₁₁ : TendstoUniformly (fun n => f₁ (φ₀₁ n)) g₁ atTop := by
    simpa [φ₀₁, f₁', Function.comp_def] using hconv₁U
  let f₂' : ℕ → X → V₂ := fun n => f₂ (φ₀₁ n)
  have hH₂' (n : ℕ) : HolderWith C₂ α (f₂' n) := hH₂ (φ₀₁ n)
  have hB₂' : ∀ x, ∃ M : ℝ, ∀ n, ‖f₂' n x‖ ≤ M := by
    intro x
    obtain ⟨M, hM⟩ := hB₂ x
    exact ⟨M, fun n => hM (φ₀₁ n)⟩
  obtain ⟨φ₂, g₂, hφ₂, hg₂, hconv₂⟩ :=
    arzela_ascoli_subseq_tendsto_locally_uniformly_of_holderWith f₂' hα hH₂' hB₂'
  have hconv₀₂ : TendstoUniformly (fun n => f₀ (φ₀₁ (φ₂ n))) g₀ atTop :=
    tendstoUniformly_comp_subsequence
      (f := fun n x => f₀ (φ₀₁ n) x) hconv₀₁ hφ₂
  have hconv₁₂ : TendstoUniformly (fun n => f₁ (φ₀₁ (φ₂ n))) g₁ atTop :=
    tendstoUniformly_comp_subsequence
      (f := fun n x => f₁ (φ₀₁ n) x) hconv₁₁ hφ₂
  have hconv₂U : TendstoUniformly (fun n => f₂' (φ₂ n)) g₂ atTop :=
    tendstoUniformlyOn_univ.mp (hconv₂ Set.univ isCompact_univ)
  refine ⟨φ₀₁ ∘ φ₂, g₀, g₁, g₂, hφ₀₁.comp hφ₂, hg₀, hg₁, hg₂, ?_, ?_, ?_⟩
  · simpa [φ₀₁, Function.comp_def] using hconv₀₂
  · simpa [φ₀₁, Function.comp_def] using hconv₁₂
  · simpa [f₂', Function.comp_def] using hconv₂U

/-- A uniform `C^{2,α}` bound on a compact convex interior set yields a subsequence whose jets
through order two converge uniformly and whose second-order jets converge in every lower Hölder
exponent. No compactness at the exponent `α` is asserted. The open-neighborhood smoothness
hypothesis ensures the derivatives are genuine jets on the compact set. -/
@[deprecated "unused hypothesis `hβ`; will be removed" (since := "2026-10-02")]
theorem exists_subseq_tendsto_in_C2Holder_of_holderBoundOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [ProperSpace F] [ProperSpace (E [×1]→L[ℝ] F)]
    [ProperSpace (E [×2]→L[ℝ] F)]
    {K U : Set E} (hK : IsCompact K) (hKconvex : Convex ℝ K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : ℕ → E → F}
    {α β C : ℝ≥0} (hα : 0 < α) (hαone : α ≤ 1)
    (hβ : 0 < β) (hβα : β < α)
    (hsmooth : ∀ n, ContDiffOn ℝ 2 (f n) U)
    (hbound : ∀ n, HolderBoundOn 2 α C K (f n)) :
    ∃ (φ : ℕ → ℕ) (g₀ : K → F)
      (g₁ : K → E [×1]→L[ℝ] F) (g₂ : K → E [×2]→L[ℝ] F),
      StrictMono φ ∧ Continuous g₀ ∧ Continuous g₁ ∧ Continuous g₂ ∧
      TendstoUniformly (fun n (x : K) => f (φ n) (x : E)) g₀ atTop ∧
      TendstoUniformly
        (fun n (x : K) => iteratedFDeriv ℝ 1 (f (φ n)) (x : E)) g₁ atTop ∧
      TendstoUniformly
        (fun n (x : K) => iteratedFDeriv ℝ 2 (f (φ n)) (x : E)) g₂ atTop ∧
      ∀ ε : ℝ≥0, 0 < ε → ∀ᶠ n in atTop,
        HolderWith ε β (fun x : K =>
          iteratedFDeriv ℝ 2 (f (φ n)) (x : E) - g₂ x) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨C₀, C₁, hLower⟩ :=
    exists_holder_bounds_lowerJets_on_compact hK hKconvex hU hKU hαone hsmooth hbound
  have hH₀ (n : ℕ) : HolderWith C₁ α (fun x : K => f n (x : E)) := (hLower n).2
  have hH₁ (n : ℕ) : HolderWith C₀ α
      (fun x : K => iteratedFDeriv ℝ 1 (f n) (x : E)) := (hLower n).1
  have hH₂ (n : ℕ) : HolderWith C α
      (fun x : K => iteratedFDeriv ℝ 2 (f n) (x : E)) := by
    change HolderWith C α
      (K.domRestrict (fun x => iteratedFDeriv ℝ 2 (f n) x))
    exact (hbound n).2.holderWith
  have hB₀ : ∀ x : K, ∃ M : ℝ, ∀ n, ‖f n (x : E)‖ ≤ M := by
    intro x
    refine ⟨C, ?_⟩
    intro n
    simpa only [norm_iteratedFDeriv_zero] using
      (hbound n).1 0 (by omega) (x : E) x.property
  have hB₁ : ∀ x : K, ∃ M : ℝ, ∀ n,
      ‖iteratedFDeriv ℝ 1 (f n) (x : E)‖ ≤ M := by
    intro x
    refine ⟨C, ?_⟩
    intro n
    exact (hbound n).1 1 (by omega) (x : E) x.property
  have hB₂ : ∀ x : K, ∃ M : ℝ, ∀ n,
      ‖iteratedFDeriv ℝ 2 (f n) (x : E)‖ ≤ M := by
    intro x
    refine ⟨C, ?_⟩
    intro n
    exact (hbound n).1 2 le_rfl (x : E) x.property
  obtain ⟨φ, g₀, g₁, g₂, hφ, hg₀, hg₁, hg₂, hconv₀, hconv₁, hconv₂⟩ :=
    exists_subseq_tendstoUniformly_threeFamilies hα hH₀ hH₁ hH₂ hB₀ hB₁ hB₂
  have hHolderβ := secondDerivative_tendsto_holderWith_lower_exponent hα hβα
    (fun n => hbound (φ n)) hconv₂
  exact ⟨φ, g₀, g₁, g₂, hφ, hg₀, hg₁, hg₂, hconv₀, hconv₁, hconv₂, hHolderβ⟩

end CalabiYau.Schauder
