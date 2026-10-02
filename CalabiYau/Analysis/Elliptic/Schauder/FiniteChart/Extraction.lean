module

public import CalabiYau.Analysis.Elliptic.Schauder.FiniteChart.Balls
public import CalabiYau.Analysis.Elliptic.Schauder.SchauderCompactness

/-!
# A common finite-chart subsequence for the three jets

GT, Lemma 6.36, p. 136: Arzelà–Ascoli applied to values, first derivatives and second
derivatives. The existing convex-set compactness theorem handles each ball. A finite diagonal
argument gives one strictly increasing subsequence for all balls, not separate chart subsequences.
-/

set_option autoImplicit false

@[expose] public section

open Filter
open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

/-- Raw Arzelà–Ascoli limits. These functions are not declared to be derivatives: that is a
separate identification step. All three families use the same subsequence `s`. -/
structure FiniteChartJetLimits {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    {cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M}
    (balls : FiniteChartBallRefinement cover) (u : ℕ → M → ℝ) (s : ℕ → ℕ) where
  value : ∀ p : balls.ι,
    Metric.closedBall (balls.center p) (balls.middleRadius p) → ℝ
  first : ∀ p : balls.ι, Metric.closedBall (balls.center p) (balls.middleRadius p) →
    EuclideanSpace ℂ (Fin n) [×1]→L[ℝ] ℝ
  second : ∀ p : balls.ι, Metric.closedBall (balls.center p) (balls.middleRadius p) →
    EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ
  continuous_value : ∀ p, Continuous (value p)
  continuous_first : ∀ p, Continuous (first p)
  continuous_second : ∀ p, Continuous (second p)
  uniform_value : ∀ p, TendstoUniformly
    (fun j (z : Metric.closedBall (balls.center p) (balls.middleRadius p)) =>
      u (s j) ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (cover.base (balls.chart p))).symm z)) (value p) atTop
  uniform_first : ∀ p, TendstoUniformly
    (fun j (z : Metric.closedBall (balls.center p) (balls.middleRadius p)) =>
      iteratedFDeriv ℝ 1 (u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (cover.base (balls.chart p))).symm) z) (first p) atTop
  uniform_second : ∀ p, TendstoUniformly
    (fun j (z : Metric.closedBall (balls.center p) (balls.middleRadius p)) =>
      iteratedFDeriv ℝ 2 (u (s j) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (cover.base (balls.chart p))).symm) z) (second p) atTop

private theorem uniform_subseq
    {X Y : Type*} [PseudoMetricSpace Y]
    {f : ℕ → X → Y} {g : X → Y} {φ : ℕ → ℕ}
    (h : TendstoUniformly f g atTop) (hφ : StrictMono φ) :
    TendstoUniformly (fun n => f (φ n)) g atTop := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  exact hφ.tendsto_atTop (h ε hε)

private theorem finite_subsequence
    {P : Type*} [Fintype P] {X : P → Type*}
    {Y₀ Y₁ Y₂ : P → Type*}
    [∀ p, TopologicalSpace (X p)]
    [∀ p, PseudoMetricSpace (Y₀ p)] [∀ p, PseudoMetricSpace (Y₁ p)]
    [∀ p, PseudoMetricSpace (Y₂ p)]
    [∀ p, Zero (Y₀ p)] [∀ p, Zero (Y₁ p)] [∀ p, Zero (Y₂ p)]
    (S : Finset P)
    (f₀ : ℕ → ∀ p, X p → Y₀ p)
    (f₁ : ℕ → ∀ p, X p → Y₁ p)
    (f₂ : ℕ → ∀ p, X p → Y₂ p)
    (extract : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ p,
      ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
      ∃ (g₀ : X p → Y₀ p) (g₁ : X p → Y₁ p) (g₂ : X p → Y₂ p),
        Continuous g₀ ∧ Continuous g₁ ∧ Continuous g₂ ∧
        TendstoUniformly (fun n x => f₀ (φ (ψ n)) p x) g₀ atTop ∧
        TendstoUniformly (fun n x => f₁ (φ (ψ n)) p x) g₁ atTop ∧
        TendstoUniformly (fun n x => f₂ (φ (ψ n)) p x) g₂ atTop) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (g₀ : ∀ p, X p → Y₀ p) (g₁ : ∀ p, X p → Y₁ p)
        (g₂ : ∀ p, X p → Y₂ p),
        ∀ p ∈ S, Continuous (g₀ p) ∧ Continuous (g₁ p) ∧ Continuous (g₂ p) ∧
          TendstoUniformly (fun n x => f₀ (φ n) p x) (g₀ p) atTop ∧
          TendstoUniformly (fun n x => f₁ (φ n) p x) (g₁ p) atTop ∧
          TendstoUniformly (fun n x => f₂ (φ n) p x) (g₂ p) atTop := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨id, strictMono_id, 0, 0, 0, ?_⟩
      simp
  | @insert a S ha ih =>
      obtain ⟨φ, hφ, g₀, g₁, g₂, hprevious⟩ := ih
      obtain ⟨ψ, hψ, g₀a, g₁a, g₂a, hg₀a, hg₁a, hg₂a, hc₀a, hc₁a, hc₂a⟩ :=
        extract φ hφ a
      let θ := φ ∘ ψ
      refine ⟨θ, hφ.comp hψ, Function.update g₀ a g₀a,
        Function.update g₁ a g₁a, Function.update g₂ a g₂a, ?_⟩
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hpS
      · simp only [Function.update_self]
        exact ⟨hg₀a, hg₁a, hg₂a, hc₀a, hc₁a, hc₂a⟩
      · have hprev := hprevious p hpS
        have hne : p ≠ a := by
          intro heq
          subst p
          exact ha hpS
        simp only [Function.update_of_ne hne]
        refine ⟨hprev.1, hprev.2.1, hprev.2.2.1, ?_, ?_, ?_⟩
        · simpa [θ, Function.comp_def] using
            uniform_subseq (f := fun n x => f₀ (φ n) p x) hprev.2.2.2.1 hψ
        · simpa [θ, Function.comp_def] using
            uniform_subseq (f := fun n x => f₁ (φ n) p x) hprev.2.2.2.2.1 hψ
        · simpa [θ, Function.comp_def] using
            uniform_subseq (f := fun n x => f₂ (φ n) p x) hprev.2.2.2.2.2 hψ

private theorem finiteDimensional_iteratedCML
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) :
    FiniteDimensional ℝ (E [×k]→L[ℝ] ℝ) := by
  induction k with
  | zero =>
      exact Module.Finite.equiv
        (continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.symm
  | succ k ih =>
      have : FiniteDimensional ℝ (E →L[ℝ] (E [×k]→L[ℝ] ℝ)) := by infer_instance
      exact Module.Finite.equiv
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ).toLinearEquiv.symm

/-- Compactness on finitely many buffered convex closed balls with one common strictly
increasing subsequence. The Hölder exponent is positive, and only uniform jet convergence
is asserted, not compactness at the original Hölder exponent. -/
theorem exists_common_subsequence_finiteChartJetLimits
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (balls : FiniteChartBallRefinement cover)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (u : ℕ → M → ℝ) (C : ℝ≥0)
    (hbound : ∀ p : balls.ι, ∀ j : ℕ,
      ContDiffOn ℝ 2
        (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm)
        (Metric.ball (balls.center p) (balls.outerRadius p)) ∧
      HolderBoundOn 2 α C
        (Metric.closedBall (balls.center p) (balls.middleRadius p))
        (u j ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (cover.base (balls.chart p))).symm)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ Nonempty (FiniteChartJetLimits balls u s) := by
  let E := EuclideanSpace ℂ (Fin n)
  have hfdE : FiniteDimensional ℝ E := inferInstance
  have hproperE : ProperSpace E := FiniteDimensional.proper ℝ E
  have hfd₁ : FiniteDimensional ℝ (E [×1]→L[ℝ] ℝ) :=
    finiteDimensional_iteratedCML (E := E) 1
  have hfd₂ : FiniteDimensional ℝ (E [×2]→L[ℝ] ℝ) :=
    finiteDimensional_iteratedCML (E := E) 2
  have : FiniteDimensional ℝ E := hfdE
  have : ProperSpace E := hproperE
  have : FiniteDimensional ℝ (E [×1]→L[ℝ] ℝ) := hfd₁
  have : FiniteDimensional ℝ (E [×2]→L[ℝ] ℝ) := hfd₂
  let β : ℝ≥0 := α / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβα : β < α := by dsimp [β]; exact half_lt_self hα₀
  let chart : balls.ι → E → M := fun p =>
    (extChartAt 𝓘(ℝ, E) (cover.base (balls.chart p))).symm
  let X : balls.ι → Type := fun p =>
    Metric.closedBall (balls.center p) (balls.middleRadius p)
  let f₀ : ℕ → ∀ p, X p → ℝ := fun j p z => u j (chart p z)
  let f₁ : ℕ → ∀ p, X p → E [×1]→L[ℝ] ℝ := fun j p z =>
    iteratedFDeriv ℝ 1 (u j ∘ chart p) (z : E)
  let f₂ : ℕ → ∀ p, X p → E [×2]→L[ℝ] ℝ := fun j p z =>
    iteratedFDeriv ℝ 2 (u j ∘ chart p) (z : E)
  have hExtract (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : balls.ι) :
      ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
        ∃ (g₀ : X p → ℝ) (g₁ : X p → E [×1]→L[ℝ] ℝ)
          (g₂ : X p → E [×2]→L[ℝ] ℝ),
          Continuous g₀ ∧ Continuous g₁ ∧ Continuous g₂ ∧
            TendstoUniformly (fun j z => f₀ (φ (ψ j)) p z) g₀ atTop ∧
            TendstoUniformly (fun j z => f₁ (φ (ψ j)) p z) g₁ atTop ∧
            TendstoUniformly (fun j z => f₂ (φ (ψ j)) p z) g₂ atTop := by
    have hK : IsCompact (Metric.closedBall (balls.center p) (balls.middleRadius p)) :=
      isCompact_closedBall _ _
    have hKconv : Convex ℝ (Metric.closedBall (balls.center p) (balls.middleRadius p)) :=
      convex_closedBall _ _
    have hU : IsOpen (Metric.ball (balls.center p) (balls.outerRadius p)) := Metric.isOpen_ball
    have hKU : Metric.closedBall (balls.center p) (balls.middleRadius p) ⊆
        Metric.ball (balls.center p) (balls.outerRadius p) :=
      Metric.closedBall_subset_ball (balls.middle_lt_outer p)
    have hsmooth (j : ℕ) : ContDiffOn ℝ 2
        (fun z : E => u (φ j) (chart p z))
        (Metric.ball (balls.center p) (balls.outerRadius p)) := by
      simpa [chart, Function.comp_def] using (hbound p (φ j)).1
    have hlocal (j : ℕ) : HolderBoundOn 2 α C
        (Metric.closedBall (balls.center p) (balls.middleRadius p))
        (fun z : E => u (φ j) (chart p z)) := by
      simpa [chart, X, Function.comp_def] using (hbound p (φ j)).2
    have hαone : α ≤ 1 := le_of_lt hα₁
    obtain ⟨ψ, g₀, g₁, g₂, hψ, hg₀, hg₁, hg₂, h₀, h₁, h₂, _⟩ :=
      CalabiYau.Schauder.exists_subseq_tendsto_in_C2Holder_of_holderBoundOn
        hK hKconv hU hKU hα₀ hαone hβα hsmooth hlocal
    refine ⟨ψ, hψ, g₀, g₁, g₂, hg₀, hg₁, hg₂, ?_, ?_, ?_⟩
    · simpa [f₀, chart, Function.comp_def] using h₀
    · simpa [f₁, chart, Function.comp_def] using h₁
    · simpa [f₂, chart, Function.comp_def] using h₂
  obtain ⟨s, hs, g₀, g₁, g₂, hglobal⟩ :=
    finite_subsequence Finset.univ f₀ f₁ f₂ hExtract
  refine ⟨s, hs, ⟨?_⟩⟩
  refine ⟨g₀, g₁, g₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (hglobal p (Finset.mem_univ p)).1
  · intro p
    exact (hglobal p (Finset.mem_univ p)).2.1
  · intro p
    exact (hglobal p (Finset.mem_univ p)).2.2.1
  · intro p
    simpa [f₀, chart, Function.comp_def] using (hglobal p (Finset.mem_univ p)).2.2.2.1
  · intro p
    simpa [f₁, chart, Function.comp_def] using (hglobal p (Finset.mem_univ p)).2.2.2.2.1
  · intro p
    simpa [f₂, chart, Function.comp_def] using (hglobal p (Finset.mem_univ p)).2.2.2.2.2

end KahlerForm
