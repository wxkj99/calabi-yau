module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.MongeAmpere.Estimates.C0.PoweredRecurrence
public import CalabiYau.MongeAmpere.Estimates.C0.PoweredIteration

public section

open scoped Manifold ContDiff ENNReal
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

/-- Uniform powered recurrence and initial `L²` data for potentials with maximum `-1` control the
oscillation of an arbitrary Monge–Ampère potential.

Normalize an arbitrary solution by subtracting its maximum and one. Then `u = -φ` is at least
one, so PoweredRecurrence and PoweredIteration give a uniform pointwise bound for `u`. -/
theorem c0_oscillation_from_powered_data
    (ω₀ : KahlerForm n M) {κ C_S A L K : ℝ}
    (hκ : 1 < κ) (hS : ω₀.SobolevInequality κ C_S) (hA : 0 ≤ A)
    (_hK : 0 ≤ K)
    (hL2 : ∀ G φ : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G →
      (∀ x, |G x| ≤ K) → ω₀.SolvesMongeAmpere G φ →
      (∃ x₀, φ x₀ = -1) → (∀ x, 1 ≤ -φ x) →
      ∫ x, (-φ x) ^ 2 ∂ω₀.volume ≤ L)
    (henergy : ∀ G φ : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G →
      (∀ x, |G x| ≤ K) → ω₀.SolvesMongeAmpere G φ →
      (∀ x, 1 ≤ -φ x) → ∀ q : ℝ, 2 ≤ q →
        ∫ x, ω₀.gradNormSq (fun y => (-φ y) ^ (q / 2)) x ∂ω₀.volume ≤
          A * q * ∫ x, (-φ x) ^ q ∂ω₀.volume) :
    ∃ C : ℝ, ∀ G φ : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G →
      (∀ x, |G x| ≤ K) → ω₀.SolvesMongeAmpere G φ →
      ∀ x y, φ x - φ y ≤ C := by
  obtain ⟨B, hBne, hprod, C, hiter⟩ :=
    c0_powered_iteration_bound (ω₀ := ω₀) (C_S := C_S) (L := L) hκ hA
  refine ⟨C, ?_⟩
  intro G φ hG hbound hsol x y
  obtain ⟨x₀, hx₀, hmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hsol.1.1.continuous.continuousOn
  let c : ℝ := -φ x₀ - 1
  let ψ : M → ℝ := fun z => φ z + c
  have hψsol : ω₀.SolvesMongeAmpere G ψ := by
    simpa [ψ] using hsol.add_const c
  have hψnorm : ∀ z, 1 ≤ -ψ z := by
    intro z
    have hz : φ z ≤ φ x₀ := (isMaxOn_iff.mp hmax) z (Set.mem_univ z)
    dsimp [ψ, c]
    linarith
  have hψx₀ : ψ x₀ = -1 := by
    dsimp [ψ, c]
    ring
  have hL2' := hL2 G ψ hG hbound hψsol ⟨x₀, hψx₀⟩ hψnorm
  let u : M → ℝ := fun z => -ψ z
  have hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u :=
    contDiff_neg.contMDiff.comp hψsol.1.1
  have hu1 : ∀ z, 1 ≤ u z := by
    intro z
    exact hψnorm z
  have henergy' : ∀ q : ℝ, 2 ≤ q →
      ∫ z, ω₀.gradNormSq (fun w => u w ^ (q / 2)) z ∂ω₀.volume ≤
        A * q * ∫ z, u z ^ q ∂ω₀.volume := by
    intro q hq
    simpa [u] using henergy G ψ hG hbound hψsol hψnorm q hq
  have hrec := c0_powered_Lp_recurrence ω₀ hu hu1 hκ hS hA henergy'
  have hL2'' : ∫ z, u z ^ 2 ∂ω₀.volume ≤ L := by
    simpa [u] using hL2'
  have hboundu := hiter hu hu1 hrec hL2''
  have hψx : ψ x ≤ -1 := by
    have := hψnorm x
    linarith
  have hψy : -ψ y ≤ C := by
    simpa [u] using hboundu y
  have hdiff : φ x - φ y = ψ x - ψ y := by
    dsimp [ψ]
    ring
  rw [hdiff]
  linarith

end KahlerForm
