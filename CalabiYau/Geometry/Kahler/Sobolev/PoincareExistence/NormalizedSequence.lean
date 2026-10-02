module

public import CalabiYau.Geometry.Kahler.Sobolev

/-!
# A normalized violating sequence for the Poincaré inequality

On a compact Kähler manifold, failure of every positive Poincaré constant gives smooth mean-zero
functions of unit squared norm whose gradient energies tend to zero. Select a smooth mean-zero
function violating the inequality at each constant `k + 1`, and divide it by the square root of its
squared integral. The normalized energy is then bounded by `1 / (k + 1)`.

Connectedness is deliberately not assumed: the hypothesis can hold on a disconnected union of
isometric components, where a nonzero locally constant mean-zero function has zero energy.
-/

@[expose] public section

open ContinuousAlternatingMap MeasureTheory Filter Topology
open scoped Manifold ContDiff

namespace KahlerForm

private theorem dWedgeDBar_smul_real {n : ℕ} (c : ℝ)
    (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) :
    dWedgeDBar (c • ℓ) = c ^ 2 • dWedgeDBar ℓ := by
  have hEval (m : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) (u v : EuclideanSpace ℂ (Fin n)) :
      (dWedgeDBar m) ![u, v] = (m (Complex.I • u) * m v - m (Complex.I • v) * m u) / 2 := by
    change ((1 / 2 : ℝ) • ContinuousAlternatingMap.alternatizeUncurryFin
      ((m.comp (Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)))).smulRight
        (ofSubsingleton ℝ (EuclideanSpace ℂ (Fin n)) ℝ (0 : Fin 1) m))) ![u, v] = _
    simp [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.removeNth]
    ring
  ext z
  have hz : z = ![z 0, z 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hz, hEval]
  change ((c • ℓ) (Complex.I • z 0) * (c • ℓ) (z 1) -
    (c • ℓ) (Complex.I • z 1) * (c • ℓ) (z 0)) / 2 =
      c ^ 2 * ((dWedgeDBar ℓ) ![z 0, z 1])
  rw [hEval]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

private theorem gradNormSq_const_mul
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (c : ℝ) (g : M → ℝ) (x : M) :
    ω₀.gradNormSq (fun y => c * g y) x = c ^ 2 * ω₀.gradNormSq g x := by
  simp only [gradNormSq, mdWedgeDBar, Function.comp_def]
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hfun : (fun y => c * g (e.symm y)) = c • (fun y => g (e.symm y)) := by
    funext y
    simp [smul_eq_mul]
  rw [hfun, fderiv_const_smul_field]
  change (ω₀.toFormField x).relTrace
    (dWedgeDBar (c • (fderiv ℝ (fun y => g (e.symm y)) (e x)))) =
      c ^ 2 * (ω₀.toFormField x).relTrace
        (dWedgeDBar (fderiv ℝ (fun y => g (e.symm y)) (e x)))
  rw [dWedgeDBar_smul_real]
  rw [relTrace_smul]

private theorem badFunction_exists
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (C : ℝ)
    (hbad : ¬ ω₀.PoincareInequality C) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g ∧
      (∫ x, g x ∂ω₀.volume = 0) ∧
      C * (∫ x, ω₀.gradNormSq g x ∂ω₀.volume) < ∫ x, g x ^ 2 ∂ω₀.volume := by
  unfold PoincareInequality at hbad
  push Not at hbad
  rcases hbad with ⟨g, hg, hmean, henergy⟩
  exact ⟨g, hg, hmean, henergy⟩

private theorem normalized_function_of_violation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] (ω₀ : KahlerForm n M) (C : ℝ) (hC : 0 < C)
    (g : M → ℝ)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g)
    (hmean : ∫ x, g x ∂ω₀.volume = 0)
    (hviolation : C * (∫ x, ω₀.gradNormSq g x ∂ω₀.volume) <
      ∫ x, g x ^ 2 ∂ω₀.volume) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f ∧
      (∫ x, f x ∂ω₀.volume = 0) ∧
      (∫ x, f x ^ 2 ∂ω₀.volume = 1) ∧
      ∫ x, ω₀.gradNormSq f x ∂ω₀.volume ≤ 1 / C := by
  have hsqInt : Integrable (fun x => g x ^ 2) ω₀.volume :=
    (hg.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgradInt : Integrable (fun x => ω₀.gradNormSq g x) ω₀.volume :=
    (ω₀.contMDiff_gradNormSq hg).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInt : Integrable g ω₀.volume :=
    hg.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have henergy_nonneg : 0 ≤ ∫ x, ω₀.gradNormSq g x ∂ω₀.volume :=
    integral_nonneg (fun x => ω₀.gradNormSq_nonneg g x)
  let A : ℝ := ∫ x, g x ^ 2 ∂ω₀.volume
  have hA : 0 < A := by
    dsimp [A]
    nlinarith [hviolation, henergy_nonneg, hC]
  let c : ℝ := (Real.sqrt A)⁻¹
  let f : M → ℝ := fun x => c * g x
  have hc_sq : c ^ 2 = A⁻¹ := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hA.le]
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f := by
    dsimp [f]
    exact contMDiff_const.mul hg
  have hmeanf : ∫ x, f x ∂ω₀.volume = 0 := by
    dsimp [f]
    rw [integral_const_mul, hmean]
    simp
  have hsqf : ∫ x, f x ^ 2 ∂ω₀.volume = 1 := by
    calc
      ∫ x, f x ^ 2 ∂ω₀.volume = c ^ 2 * A := by
        dsimp [f]
        calc
          _ = ∫ x, c ^ 2 * g x ^ 2 ∂ω₀.volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun x => by ring)
          _ = c ^ 2 * A := by rw [integral_const_mul]
      _ = 1 := by rw [hc_sq]; field_simp [ne_of_gt hA]
  have hgradf : ∫ x, ω₀.gradNormSq f x ∂ω₀.volume =
      c ^ 2 * ∫ x, ω₀.gradNormSq g x ∂ω₀.volume := by
    calc
      _ = ∫ x, c ^ 2 * ω₀.gradNormSq g x ∂ω₀.volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => gradNormSq_const_mul ω₀ c g x)
      _ = _ := by rw [integral_const_mul]
  refine ⟨f, hf, hmeanf, hsqf, ?_⟩
  rw [hgradf, hc_sq]
  calc
    A⁻¹ * (∫ x, ω₀.gradNormSq g x ∂ω₀.volume) =
        (∫ x, ω₀.gradNormSq g x ∂ω₀.volume) / A := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ 1 / C := (div_le_div_iff₀ hA hC).2 (by nlinarith [hviolation])

/-- If no positive Poincaré constant exists, there is a smooth mean-zero sequence of unit squared
norm whose gradient energies tend to zero. No connectedness or positive dimension is assumed. -/
theorem exists_normalized_sequence_of_no_poincare_constant
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] (ω₀ : KahlerForm n M)
    (hbad : ∀ C : ℝ, 0 < C → ¬ ω₀.PoincareInequality C) :
    ∃ f : ℕ → M → ℝ,
      (∀ k, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (f k)) ∧
      (∀ k, ∫ x, f k x ∂ω₀.volume = 0) ∧
      (∀ k, ∫ x, (f k x) ^ 2 ∂ω₀.volume = 1) ∧
      (∀ k, ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume ≤ 1 / ((k : ℝ) + 1)) ∧
      Tendsto (fun k => ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume) atTop (𝓝 0) := by
  classical
  have hsequence : ∀ k : ℕ, ∃ fk : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ fk ∧
      (∫ x, fk x ∂ω₀.volume = 0) ∧
      (∫ x, fk x ^ 2 ∂ω₀.volume = 1) ∧
      ∫ x, ω₀.gradNormSq fk x ∂ω₀.volume ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    let C : ℝ := (k : ℝ) + 1
    have hC : 0 < C := by positivity
    have hbadk : ¬ ω₀.PoincareInequality C := hbad C hC
    obtain ⟨g, hg, hmean, hviolation⟩ := badFunction_exists ω₀ C hbadk
    exact normalized_function_of_violation ω₀ C hC g hg hmean hviolation
  choose f hf hmeanf hsqf henergy using hsequence
  have hrecip : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [Nat.cast_one, Nat.cast_add] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have henergy_tendsto :
      Tendsto (fun k => ∫ x, ω₀.gradNormSq (f k) x ∂ω₀.volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrecip
      (fun k => integral_nonneg (fun x => ω₀.gradNormSq_nonneg (f k) x)) henergy
  exact ⟨f, hf, hmeanf, hsqf, henergy, henergy_tendsto⟩

end KahlerForm
