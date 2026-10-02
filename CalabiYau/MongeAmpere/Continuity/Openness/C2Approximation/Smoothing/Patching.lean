module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.EuclideanMollification
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.Localization
public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing.TransitionJets

/-!
# Finite chart patching of local C² mollifications

Extend each compactly supported local convolution by zero through its chart and transfer its jet
estimates to every piece of the fixed compact chart cover. The parent performs the finite sum, using
its already-proved finite-sum jet estimate and the localization reconstruction identity.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M]

/-- Per-index global smoothings of the localized partition terms. Each approximation is extended by
zero through its source chart; its error jets converge uniformly on every piece of the fixed cover,
so the parent can apply its finite-sum jet estimate without repeating the transition-map argument. -/
structure ChartwiseLocalMollificationData {φ : M → ℝ}
    (L : CompactChartC2Localization (n := n) (M := M) φ) where
  approximation : L.cover.ι → ℕ → M → ℝ
  smooth : ∀ i j,
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (approximation i j)
  support_in_source : ∀ i j, tsupport (approximation i j) ⊆
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).source
  error_contDiffAt : ∀ i j k z, z ∈ L.cover.piece k →
    ContDiffAt ℝ 2
      ((approximation i j - L.localizedFunction i) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm) z
  jetsTendsto : ∀ ε : ℝ≥0, 0 < ε →
    ∃ N, ∀ j, N ≤ j → ∀ i k, ∀ r ≤ 2, ∀ z ∈ L.cover.piece k,
      ‖iteratedFDeriv ℝ r
        ((approximation i j - L.localizedFunction i) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base k)).symm) z‖ ≤ ε

/-- Compactly supported Euclidean mollifications yield per-index global chartwise smoothings.
The all-chart estimates include the smooth coordinate-transition bounds on the compact supports. -/
theorem exists_chartwiseLocalMollificationData_of_localMollifications
    {φ : M → ℝ} (L : CompactChartC2Localization (n := n) (M := M) φ)
    (A : ∀ i, EuclideanC2MollificationData
      (EuclideanSpace ℂ (Fin n)) (L.localFunction i)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (L.cover.base i)).target) :
    Nonempty (ChartwiseLocalMollificationData L) := by
  obtain ⟨S⟩ := exists_chartwiseSourceMollificationData L A
  obtain ⟨T⟩ := exists_chartwiseTransitionJetsData L A S
  exact ⟨⟨S.approximation, S.smooth, S.support_in_source,
    T.error_contDiffAt, T.jetsTendsto⟩⟩

end KahlerForm
