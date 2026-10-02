module

public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.HolderConvolution
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.ScalarCovariance
public import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation.TraceConvolution

@[expose] public section

open Set Filter Matrix
open scoped ContDiff NNReal Topology

namespace CalabiYau.Schauder

private theorem localHolderBoundOn_zero_iff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α B : ℝ≥0} {s : Set E} {f : E → F} :
    HolderBoundOn 0 α B s f ↔
      (∀ z ∈ s, ‖f z‖ ≤ B) ∧ HolderOnWith B α f s := by
  constructor
  · intro hf
    refine ⟨fun z hz ↦ ?_, ?_⟩
    · simpa only [norm_iteratedFDeriv_zero] using hf.1 0 le_rfl z hz
    · intro x hx y hy
      have h := hf.2 x hx y hy
      rw [iteratedFDeriv_zero_eq_comp] at h
      exact ((continuousMultilinearCurryFin0 ℝ E F).symm.edist_map (f x) (f y)) ▸ h
  · rintro ⟨hNorm, hHolder⟩
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have : j = 0 := by omega
      subst j
      simpa only [norm_iteratedFDeriv_zero] using hNorm z hz
    · rw [iteratedFDeriv_zero_eq_comp]
      intro x hx y hy
      change edist ((continuousMultilinearCurryFin0 ℝ E F).symm (f x))
        ((continuousMultilinearCurryFin0 ℝ E F).symm (f y)) ≤ _
      rw [(continuousMultilinearCurryFin0 ℝ E F).symm.edist_map]
      exact hHolder x hx y hy

private theorem localHolderBoundOn_zero_add {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α B D : ℝ≥0} {s : Set E} {f g : E → F}
    (hf : HolderBoundOn 0 α B s f) (hg : HolderBoundOn 0 α D s g) :
    HolderBoundOn 0 α (B + D) s (fun z ↦ f z + g z) := by
  rcases localHolderBoundOn_zero_iff.mp hf with ⟨hfn, hfh⟩
  rcases localHolderBoundOn_zero_iff.mp hg with ⟨hgn, hgh⟩
  apply localHolderBoundOn_zero_iff.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    exact (norm_add_le _ _).trans (by simpa using add_le_add (hfn z hz) (hgn z hz))
  · intro x hx y hy
    calc
      edist (f x + g x) (f y + g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
        edist_add_add_le _ _ _ _
      _ ≤ (B : ENNReal) * edist x y ^ (α : ℝ) +
          (D : ENNReal) * edist x y ^ (α : ℝ) :=
        add_le_add (hfh x hx y hy) (hgh x hx y hy)
      _ = ↑(B + D) * edist x y ^ (α : ℝ) := by rw [ENNReal.coe_add, add_mul]

private theorem localHolderBoundOn_zero_sum {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ≥0} {s : Set E} (t : Finset ι) (B : ι → ℝ≥0) (f : ι → E → F)
    (hf : ∀ i ∈ t, HolderBoundOn 0 α (B i) s (f i)) :
    HolderBoundOn 0 α (∑ i ∈ t, B i) s (fun z ↦ ∑ i ∈ t, f i z) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    apply localHolderBoundOn_zero_iff.mpr
    exact ⟨by simp, by intro x hx y hy; simp⟩
  | @insert i t hi ih =>
    simpa only [Finset.sum_insert hi] using
      localHolderBoundOn_zero_add (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

private theorem localHolderBoundOn_zero_congr {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α B : ℝ≥0} {s : Set E} {f g : E → F}
    (hf : HolderBoundOn 0 α B s f) (hfg : ∀ z ∈ s, f z = g z) :
    HolderBoundOn 0 α B s g := by
  rcases localHolderBoundOn_zero_iff.mp hf with ⟨hNorm, hHolder⟩
  apply localHolderBoundOn_zero_iff.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    simpa only [hfg z hz] using hNorm z hz
  · intro x hx y hy
    simpa only [hfg x hx, hfg y hy] using hHolder x hx y hy

/-- The actual local source bound is assembled from scalar covariance and fixed trace commutation. -/
theorem localFixedMollify_sourceBound {n : ℕ}
    {α K K₁ : ℝ≥0} {U : Set (EuclideanSpace ℂ (Fin n))}
    {c : EuclideanSpace ℂ (Fin n)} {S η : ℝ}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hU : IsOpen U) (hS : 0 < S) (hη : 0 < η)
    (hCollar : Metric.thickening η (Metric.closedBall c S) ⊆ U)
    (hA₀ : ∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U)
    (hu : ContDiffOn ℝ 2 u U)
    (hAH : ∀ j l, HolderBoundOn 0 α K U fun z ↦ A z j l)
    (hL₀ : ContDiffOn ℝ 0 (complexEllipticOp A u) U)
    (hLH : HolderBoundOn 0 α K₁ U (complexEllipticOp A u)) :
    ∃ ε : ℕ → ℝ≥0, Tendsto ε atTop (𝓝 0) ∧
      ∀ m, HolderBoundOn 0 α (K₁ + ε m) (Metric.ball c S)
        (complexEllipticOp (localFixedCoefficientSeq U hη A m) (localFixedMollify U hη m u)) := by
  classical
  have hCov (i j : Fin n) := localMollificationCovariance_holderBound
    hα₀ hα₁ hS hη hCollar (hA₀ i j).continuousOn
    (continuousOn_complexHessian_entry hU hu j i) (hAH i j)
  choose ε hε hCovBound using hCov
  let err : ℕ → ℝ≥0 := fun m ↦ ∑ i, ∑ j, ε i j m
  have hErr : Tendsto err atTop (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ ↦
      tendsto_finsetSum Finset.univ (fun j _ ↦ hε i j))
    simpa only [Finset.sum_const_zero] using h
  refine ⟨err, hErr, ?_⟩
  intro m
  have hError : HolderBoundOn 0 α (err m) (Metric.ball c S)
      (fun z ↦ ∑ i, ∑ j, (localMollificationCovariance U hη m
        (fun y ↦ A y i j) (fun y ↦ complexHessian u y j i) z).re) := by
    apply localHolderBoundOn_zero_sum Finset.univ
    intro i _
    apply localHolderBoundOn_zero_sum Finset.univ
    intro j _
    exact hCovBound i j m
  have hSource := localFixedMollify_holderBoundOn_zero hU hS hη hCollar
    hL₀.continuousOn hLH m
  apply localHolderBoundOn_zero_congr (localHolderBoundOn_zero_add hSource hError)
  intro z hz
  exact (localFixedMollify_trace_covariance hU hη hCollar hA₀ hu m z hz).symm

end CalabiYau.Schauder
