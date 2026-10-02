module

public import CalabiYau.Geometry.Kahler.Sobolev

/-!
# Sobolev inequality in complex dimension zero

A compact zero-dimensional manifold modeled on `EuclideanSpace ℂ (Fin 0)` is a finite discrete
space. Its Kähler volume is a finite measure supported on those points, with positive point masses
when the space is nonempty. Thus the finite-dimensional weighted `L⁴`-to-`L²` estimate gives the
Sobolev inequality; the gradient term is nonnegative and is not needed. The empty manifold is also
allowed. This case is independent of the positive-dimensional Sobolev embedding theorems.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory

namespace KahlerForm

private theorem compact_zero_dimensional_finite
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin 0)) M]
    [CompactSpace M] : Finite M := by
  let : DiscreteTopology (EuclideanSpace ℂ (Fin 0)) := inferInstance
  let : DiscreteTopology M :=
    ChartedSpace.discreteTopology (EuclideanSpace ℂ (Fin 0)) M
  exact finite_of_compact_of_discrete

/-- On a finite measure space with positive point masses, the quartic integral is controlled by
its quadratic integral, even after adding any nonnegative integrand on the right. The proof uses
only a finite weighted-sum estimate and also includes the empty space. -/
private theorem finite_atomic_l4_control
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (hμ : ∀ x, 0 < μ.real {x}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : α → ℝ, (∀ x, 0 ≤ g x) →
      (∫ x, |f x| ^ (2 * (2 : ℝ)) ∂μ) ^ (2 : ℝ)⁻¹ ≤
        C * ∫ x, (g x + f x ^ 2) ∂μ := by
  classical
  let w : α → ℝ := fun x => μ.real {x}
  let R : ℝ := ∑ x, (w x)⁻¹
  refine ⟨1 + R, by positivity, ?_⟩
  intro f g hg
  let q : ℝ := ∑ x, w x * f x ^ 2
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg fun x hx => inv_nonneg.mpr (le_of_lt (hμ x))
  have hw_pos (x : α) : 0 < w x := hμ x
  have hterm (x : α) : w x * f x ^ 4 ≤ q ^ 2 * (w x)⁻¹ := by
    have hle : w x * f x ^ 2 ≤ q := by
      dsimp [q]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun y => w y * f y ^ 2)
        (fun y hy => mul_nonneg (le_of_lt (hw_pos y)) (sq_nonneg (f y)))
        (Finset.mem_univ x)
    have ha_nonneg : 0 ≤ w x * f x ^ 2 :=
      mul_nonneg (le_of_lt (hw_pos x)) (sq_nonneg (f x))
    have hsq : (w x * f x ^ 2) ^ 2 ≤ q ^ 2 := by
      nlinarith [mul_self_le_mul_self ha_nonneg hle]
    have hmul : w x ^ 2 * f x ^ 4 ≤ q ^ 2 := by
      nlinarith [hsq]
    have hw0 : w x ≠ 0 := (hw_pos x).ne'
    calc
      w x * f x ^ 4 = (w x ^ 2 * f x ^ 4) / w x := by field_simp
      _ ≤ q ^ 2 / w x := div_le_div_of_nonneg_right hmul (le_of_lt (hw_pos x))
      _ = q ^ 2 * (w x)⁻¹ := by rw [div_eq_mul_inv]
  have hsum : (∑ x, w x * f x ^ 4) ≤ q ^ 2 * R := by
    calc
      (∑ x, w x * f x ^ 4) ≤ ∑ x, q ^ 2 * (w x)⁻¹ :=
        Finset.sum_le_sum fun x hx => hterm x
      _ = q ^ 2 * R := by simp [R, Finset.mul_sum]
  have hR_le : R ≤ (1 + R) ^ 2 := by nlinarith [sq_nonneg R]
  have hsum' : (∑ x, w x * f x ^ 4) ≤ ((1 + R) * q) ^ 2 := by
    calc
      (∑ x, w x * f x ^ 4) ≤ q ^ 2 * R := hsum
      _ ≤ q ^ 2 * (1 + R) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hR_le (sq_nonneg q)
      _ = ((1 + R) * q) ^ 2 := by ring
  have hq_integral : (∫ x, f x ^ 2 ∂μ) = q := by
    rw [MeasureTheory.integral_fintype
      (Integrable.of_finite : Integrable (fun x : α => f x ^ 2) μ)]
    simp [q, w, smul_eq_mul]
  have hpow (x : α) : |f x| ^ (2 * (2 : ℝ)) = f x ^ 4 := by
    have he : (2 : ℝ) * (2 : ℝ) = (4 : ℕ) := by norm_num
    rw [he, Real.rpow_natCast]
    by_cases hf : 0 ≤ f x
    · simp [abs_of_nonneg hf]
    · rw [abs_of_neg (lt_of_not_ge hf)]
      ring
  have hquartic_integral :
      (∫ x, |f x| ^ (2 * (2 : ℝ)) ∂μ) = ∑ x, w x * f x ^ 4 := by
    rw [MeasureTheory.integral_fintype (Integrable.of_finite :
      Integrable (fun x : α => |f x| ^ (2 * (2 : ℝ))) μ)]
    simp only [smul_eq_mul]
    apply Finset.sum_congr rfl
    intro x hx
    simpa [w] using congrArg (fun z : ℝ => μ.real {x} * z) (hpow x)
  have hsum_nonneg : 0 ≤ ∑ x, w x * f x ^ 4 := by
    refine Finset.sum_nonneg fun x hx => ?_
    exact mul_nonneg (le_of_lt (hw_pos x)) (by positivity)
  have hroot :
      (∑ x, w x * f x ^ 4) ^ (2 : ℝ)⁻¹ ≤ (1 + R) * q := by
    have hinv : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
    rw [hinv, ← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_iff).2 ⟨by positivity, hsum'⟩
  have hquad_le : q ≤ ∫ x, (g x + f x ^ 2) ∂μ := by
    rw [MeasureTheory.integral_fintype (Integrable.of_finite :
      Integrable (fun x : α => g x + f x ^ 2) μ)]
    simp only [smul_eq_mul, mul_add, Finset.sum_add_distrib]
    dsimp [q]
    apply le_add_of_nonneg_left
    exact Finset.sum_nonneg fun x hx =>
      mul_nonneg (le_of_lt (hμ x)) (hg x)
  refine (show (∫ x, |f x| ^ (2 * (2 : ℝ)) ∂μ) ^ (2 : ℝ)⁻¹ ≤
      (1 + R) * q from ?_).trans ?_
  · rw [hquartic_integral]
    exact hroot
  · exact mul_le_mul_of_nonneg_left hquad_le (by positivity)

/-- On a compact Kähler manifold of complex dimension zero, some finite constant gives the
inhomogeneous Sobolev inequality with exponent `2κ = 4`. -/
theorem exists_sobolevInequality_dimension_zero
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin 0)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 0)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] (ω₀ : KahlerForm 0 M) :
    ∃ C : ℝ, 0 ≤ C ∧ ω₀.SobolevInequality 2 C := by
  classical
  let : DiscreteTopology (EuclideanSpace ℂ (Fin 0)) := inferInstance
  let : DiscreteTopology M :=
    ChartedSpace.discreteTopology (EuclideanSpace ℂ (Fin 0)) M
  let : Finite M := compact_zero_dimensional_finite
  let : Fintype M := Fintype.ofFinite M
  have : IsFiniteMeasure ω₀.volume := inferInstance
  have hmass (x : M) : 0 < ω₀.volume.real {x} := by
    rw [MeasureTheory.measureReal_def]
    apply ENNReal.toReal_pos
    · exact (isOpen_discrete ({x} : Set M)).measure_ne_zero ω₀.volume
        ⟨x, by simp⟩
    · exact measure_ne_top ω₀.volume {x}
  obtain ⟨C, hC, hbound⟩ := finite_atomic_l4_control ω₀.volume hmass
  refine ⟨C, hC, ?_⟩
  intro f hf
  exact hbound f (fun x => ω₀.gradNormSq f x)
    (fun x => ω₀.gradNormSq_nonneg f x)

end KahlerForm
