module

public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.Geometry.Kahler.Sobolev.RellichCompactness
public import CalabiYau.Geometry.Kahler.Sobolev.ZeroGradient
import CalabiYau.Geometry.Kahler.Sobolev.PoincareExistence.DimensionZero
import CalabiYau.Geometry.Kahler.Sobolev.PoincareExistence.LimitMoments
import CalabiYau.Geometry.Kahler.Sobolev.PoincareExistence.NormalizedSequence

/-!
# Existence of the Poincaré inequality on compact connected Kähler manifolds

For positive complex dimension, argue by contradiction with a normalized mean-zero sequence.
Rellich compactness gives a strong `L²` limit; vanishing gradient energy makes that limit a.e.
constant, while the limiting moments remain zero and one. The zero-dimensional case is handled
separately because the chart Rellich theorem requires a positive-dimensional real model.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory Filter Topology

namespace KahlerForm

/-- Every compact connected Kähler manifold admits a Poincaré inequality with a positive
constant. -/
theorem exists_poincareInequality
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] [ConnectedSpace M] (ω₀ : KahlerForm n M) :
    ∃ C : ℝ, 0 < C ∧ ω₀.PoincareInequality C := by
  classical
  by_cases hn0 : n = 0
  · subst n
    exact exists_poincareInequality_dimension_zero ω₀
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    by_contra hnot
    have hbad : ∀ C : ℝ, 0 < C → ¬ ω₀.PoincareInequality C := by
      intro C hC hP
      exact hnot ⟨C, hC, hP⟩
    obtain ⟨f, hf, hfmean, hfsq, henergyBound, henergy_tendsto⟩ :=
      ω₀.exists_normalized_sequence_of_no_poincare_constant hbad
    have hbound : ∀ k : ℕ,
        ∫ x, ((f k x) ^ 2 + ω₀.gradNormSq (f k) x) ∂ω₀.volume ≤ 2 := by
      intro k
      have henergy_le_one :
          ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume ≤ 1 := by
        have hden : 0 < (k : ℝ) + 1 := by positivity
        have hrecip : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
          apply (div_le_iff₀ hden).2
          nlinarith
        exact (henergyBound k).trans hrecip
      have hsqInt : Integrable (fun x => (f k x) ^ 2) ω₀.volume :=
        ((hf k).continuous.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hgradInt : Integrable (fun x => ω₀.gradNormSq (f k) x) ω₀.volume :=
        (ω₀.contMDiff_gradNormSq (hf k)).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      calc
        ∫ x, ((f k x) ^ 2 + ω₀.gradNormSq (f k) x) ∂ω₀.volume =
            (∫ x, (f k x) ^ 2 ∂ω₀.volume) +
              ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume := by
          rw [integral_add hsqInt hgradInt]
        _ ≤ 2 := by rw [hfsq k]; linarith
    obtain ⟨σ, hσ, u, hu, hL2⟩ :=
      ω₀.rellichCompactness hn f hf 2 (by norm_num) hbound
    have henergySubseq : Tendsto
        (fun j => ∫ x, ω₀.gradNormSq (f (σ j)) x ∂ω₀.volume) atTop (𝓝 0) :=
      henergy_tendsto.comp hσ.tendsto_atTop
    obtain ⟨c, hconst⟩ :=
      ω₀.ae_eq_const_of_l2_tendsto_and_gradNormSq_tendsto
        (fun j => f (σ j)) u (fun j => hf (σ j)) hu hL2 henergySubseq
    have hfLp : ∀ j : ℕ, MemLp (f (σ j)) (ENNReal.ofReal 2) ω₀.volume := by
      intro j
      exact (hf (σ j)).continuous.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hmom := MeasureTheory.tendsto_integral_moments_of_eLpNorm
      u (fun j => f (σ j)) hu hfLp hL2
      (fun j => hfmean (σ j)) (fun j => hfsq (σ j))
    have hmeanconst : ω₀.volume.real Set.univ * c = 0 := by
      have h := hmom.1
      rw [integral_congr_ae hconst, integral_const] at h
      simpa using h
    have hsqconst : ω₀.volume.real Set.univ * c ^ 2 = 1 := by
      have h := hmom.2
      have hconstsq : (fun x => u x ^ 2) =ᵐ[ω₀.volume] fun _ => c ^ 2 := by
        filter_upwards [hconst] with x hx
        rw [hx]
      rw [integral_congr_ae hconstsq, integral_const] at h
      simpa using h
    have hfactor : ω₀.volume.real Set.univ * c ^ 2 =
        (ω₀.volume.real Set.univ * c) * c := by ring
    rw [hfactor, hmeanconst] at hsqconst
    norm_num at hsqconst

end KahlerForm
