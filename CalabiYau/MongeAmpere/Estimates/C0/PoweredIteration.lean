module

public import CalabiYau.Analysis.MoserIteration.Iteration
public import CalabiYau.Geometry.Kahler.Volume
public import CalabiYau.Geometry.Kahler.Sobolev

public section

open scoped Manifold ContDiff ENNReal
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

omit [ConnectedSpace M] in
/-- Complete the powered Moser iteration, including its finite product and pointwise lift.

The theorem records the genuinely finite product bound before using the recurrence-to-essSup
lemma. Its product and pointwise constant are uniform over every input function with the displayed
recurrence and initial moment. Full support of Kähler volume converts the essential bound into a
pointwise one. -/
theorem c0_powered_iteration_bound
    (ω₀ : KahlerForm n M) {κ C_S A L : ℝ}
    (hκ : 1 < κ) (hA : 0 ≤ A) :
    ∃ B : ENNReal, B ≠ ⊤ ∧
      (∀ N, ∏ k ∈ Finset.range N,
        ENNReal.ofReal
          ((max C_S 1 * (1 + A * (2 * κ ^ k))) ^ ((2 * κ ^ k)⁻¹)) ≤ B) ∧
      ∃ C : ℝ, ∀ {u : M → ℝ},
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u →
        (∀ x, 1 ≤ u x) →
        (∀ k, eLpNorm u (ENNReal.ofReal (2 * κ ^ (k + 1))) ω₀.volume ≤
          ENNReal.ofReal
              ((max C_S 1 * (1 + A * (2 * κ ^ k))) ^ ((2 * κ ^ k)⁻¹)) *
            eLpNorm u (ENNReal.ofReal (2 * κ ^ k)) ω₀.volume) →
        (∫ x, u x ^ 2 ∂ω₀.volume ≤ L) → ∀ x, u x ≤ C := by
  let logMaj : ℕ → ℝ := fun k =>
    (Real.log (max C_S 1 * (1 + 2 * A)) / 2) * (κ⁻¹) ^ k +
      (Real.log κ / 2) * ((k : ℝ) * (κ⁻¹) ^ k)
  have hMajNonneg (k : ℕ) : 0 ≤ logMaj k := by
    have hD : 1 ≤ max C_S 1 * (1 + 2 * A) := by
      have hmax : 1 ≤ max C_S 1 := le_max_right _ _
      nlinarith
    have hlogD : 0 ≤ Real.log (max C_S 1 * (1 + 2 * A)) := Real.log_nonneg hD
    have hlogκ : 0 ≤ Real.log κ := Real.log_nonneg hκ.le
    dsimp [logMaj]
    positivity
  have hMajSummable : Summable logMaj := by
    let r : ℝ := κ⁻¹
    have hr0 : 0 ≤ r := inv_nonneg.mpr (le_of_lt (lt_trans zero_lt_one hκ))
    have hr1 : r < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hκ)).2 hκ
    have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
    have hgeom : Summable (fun k : ℕ => r ^ k) := summable_geometric_of_lt_one hr0 hr1
    have hnatNorm : Summable (fun k : ℕ => ‖(k : ℝ) * r ^ k‖) := by
      simpa [pow_one] using summable_norm_pow_mul_geometric_of_norm_lt_one 1 hrnorm
    have hnat : Summable (fun k : ℕ => (k : ℝ) * r ^ k) := hnatNorm.of_norm
    have hsum : Summable (fun k : ℕ =>
        (Real.log (max C_S 1 * (1 + 2 * A)) / 2) * r ^ k +
          (Real.log κ / 2) * ((k : ℝ) * r ^ k)) :=
      (hgeom.mul_left _).add (hnat.mul_left _)
    exact hsum.congr fun k => by simp [logMaj, r]
  have hProduct : ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ N,
      (∏ k ∈ Finset.range N, ENNReal.ofReal
        ((max C_S 1 * (1 + A * (2 * κ ^ k))) ^ ((2 * κ ^ k)⁻¹))) ≤ B := by
    have hLnonneg (k : ℕ) : 0 ≤ logMaj k := hMajNonneg k
    let S : ℝ := ∑' k, logMaj k
    have hS : 0 ≤ S := by
      dsimp [S]
      exact tsum_nonneg hLnonneg
    refine ⟨ENNReal.ofReal (Real.exp S), (ENNReal.ofReal_lt_top).ne, ?_⟩
    intro N
    have hsumN : (∑ k ∈ Finset.range N, logMaj k) ≤ S := by
      dsimp [S]
      exact hMajSummable.sum_le_tsum _ (fun k _ => hLnonneg k)
    let f : ℕ → ℝ := fun k =>
      (max C_S 1 * (1 + A * (2 * κ ^ k))) ^ ((2 * κ ^ k)⁻¹)
    have hprodReal : (∏ k ∈ Finset.range N, f k) ≤ Real.exp S := by
      calc
        (∏ k ∈ Finset.range N, f k) ≤
            ∏ k ∈ Finset.range N, Real.exp (logMaj k) := by
          apply Finset.prod_le_prod
          · intro k hk
            dsimp [f]
            positivity
          · intro k hk
            have hpow : 1 ≤ κ ^ k := one_le_pow₀ hκ.le
            have hq : 0 < 2 * κ ^ k := by positivity
            have hD : 0 < max C_S 1 * (1 + 2 * A) := by positivity
            have hbase : 0 < max C_S 1 * (1 + A * (2 * κ ^ k)) := by positivity
            have hbaseLe : max C_S 1 * (1 + A * (2 * κ ^ k)) ≤
                max C_S 1 * (1 + 2 * A) * κ ^ k := by
              have hinner : 1 + 2 * A * κ ^ k ≤ (1 + 2 * A) * κ ^ k := by
                nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)
                  (sub_nonneg.mpr hpow)]
              calc
                _ = max C_S 1 * (1 + 2 * A * κ ^ k) := by ring
                _ ≤ max C_S 1 * ((1 + 2 * A) * κ ^ k) :=
                  mul_le_mul_of_nonneg_left hinner (le_of_lt (lt_of_lt_of_le zero_lt_one
                    (le_max_right _ _)))
                _ = _ := by ring
            have hlog : Real.log (max C_S 1 * (1 + A * (2 * κ ^ k))) ≤
                Real.log (max C_S 1 * (1 + 2 * A)) + (k : ℝ) * Real.log κ := by
              calc
                _ ≤ Real.log (max C_S 1 * (1 + 2 * A) * κ ^ k) :=
                  Real.log_le_log hbase hbaseLe
                _ = Real.log (max C_S 1 * (1 + 2 * A)) + (k : ℝ) * Real.log κ := by
                  rw [Real.log_mul (ne_of_gt hD)
                    (pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hκ))), Real.log_pow]
            change (max C_S 1 * (1 + A * (2 * κ ^ k))) ^ ((2 * κ ^ k)⁻¹) ≤ _
            rw [Real.rpow_def_of_pos hbase]
            apply Real.exp_le_exp.mpr
            calc
              _ ≤ (Real.log (max C_S 1 * (1 + 2 * A)) +
                  (k : ℝ) * Real.log κ) * (2 * κ ^ k)⁻¹ :=
                mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr hq.le)
              _ = logMaj k := by
                simp [logMaj, div_eq_mul_inv, inv_pow]
                ring
        _ = Real.exp (∑ k ∈ Finset.range N, logMaj k) := by rw [← Real.exp_sum]
        _ ≤ Real.exp S := Real.exp_le_exp.mpr hsumN
    have hfnonneg : ∀ k ∈ Finset.range N, 0 ≤ f k := by
      intro k hk
      dsimp [f]
      positivity
    change (∏ k ∈ Finset.range N, ENNReal.ofReal (f k)) ≤ ENNReal.ofReal (Real.exp S)
    rw [← ENNReal.ofReal_prod_of_nonneg hfnonneg]
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg S)).2 hprodReal
  have initialNorm {u : M → ℝ} (hu : Continuous u) (hu1 : ∀ x, 1 ≤ u x)
      (hL : ∫ x, u x ^ 2 ∂ω₀.volume ≤ L) :
      eLpNorm u 2 ω₀.volume ≤ ENNReal.ofReal (Real.sqrt (max L 0)) := by
    have hu0 : ∀ x, 0 ≤ u x := fun x => le_trans (by norm_num) (hu1 x)
    have hnonneg : 0 ≤ ∫ x, u x ^ 2 ∂ω₀.volume :=
      integral_nonneg fun x => sq_nonneg (u x)
    have hsqint : Integrable (fun x => u x ^ 2) ω₀.volume :=
      (hu.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))
    have hlin : (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂ω₀.volume) =
        ENNReal.ofReal (∫ x, u x ^ 2 ∂ω₀.volume) := by
      calc
        _ = ∫⁻ x, ENNReal.ofReal (u x ^ 2) ∂ω₀.volume := by
          apply lintegral_congr
          intro x
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hu0 x)]
          rw [ENNReal.ofReal_rpow_of_nonneg (hu0 x) (by norm_num : 0 ≤ (2 : ℝ))]
          exact congrArg ENNReal.ofReal (Real.rpow_natCast (u x) 2)
        _ = ENNReal.ofReal (∫ x, u x ^ 2 ∂ω₀.volume) :=
          (ofReal_integral_eq_lintegral_ofReal hsqint
            (Filter.Eventually.of_forall fun x => sq_nonneg (u x))).symm
    have hnorm : eLpNorm u 2 ω₀.volume =
        ENNReal.ofReal (Real.sqrt (∫ x, u x ^ 2 ∂ω₀.volume)) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      change (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂ω₀.volume) ^ (1 / (2 : ℝ)) = _
      rw [hlin]
      rw [ENNReal.ofReal_rpow_of_nonneg hnonneg
        (by norm_num : 0 ≤ (1 / (2 : ℝ)))]
      rw [Real.sqrt_eq_rpow]
    rw [hnorm]
    exact ENNReal.ofReal_le_ofReal
      (Real.sqrt_le_sqrt (hL.trans (le_max_left L 0)))
  obtain ⟨B, hBtop, hprod⟩ := hProduct
  refine ⟨B, hBtop, hprod, ?_⟩
  let C : ℝ := (B * ENNReal.ofReal (Real.sqrt (max L 0))).toReal
  have hCnonneg : 0 ≤ C := ENNReal.toReal_nonneg
  have hq (k : ℕ) : 0 < 2 * κ ^ k :=
    mul_pos (by norm_num) (pow_pos (lt_trans zero_lt_one hκ) k)
  let p : ℕ → ENNReal := fun k => ENNReal.ofReal (2 * κ ^ k)
  let w : ℕ → ENNReal := fun k => ENNReal.ofReal
    ((max C_S 1 * (1 + A * (2 * κ ^ k))) ^ ((2 * κ ^ k)⁻¹))
  have hp0 : ∀ k, p k ≠ 0 := fun k => ENNReal.ofReal_ne_zero_iff.mpr (hq k)
  have hpTop : ∀ k, p k ≠ ⊤ := fun _ => (ENNReal.ofReal_lt_top).ne
  have hpEq : (fun k => (p k).toReal) = fun k => 2 * κ ^ k := by
    funext k
    change (ENNReal.ofReal (2 * κ ^ k)).toReal = 2 * κ ^ k
    exact ENNReal.toReal_ofReal (hq k).le
  have hpTendsto : Filter.Tendsto (fun k => (p k).toReal) Filter.atTop Filter.atTop := by
    rw [hpEq]
    exact Filter.Tendsto.const_mul_atTop (by norm_num : 0 < (2 : ℝ))
      (tendsto_pow_atTop_atTop_of_one_lt hκ)
  refine ⟨C, ?_⟩
  intro u hu hu1 hrec hL x
  have hrec' : ∀ k, eLpNorm u (p (k + 1)) ω₀.volume ≤
      w k * eLpNorm u (p k) ω₀.volume := by
    intro k
    simpa [p, w] using hrec k
  have hprod' : ∀ N, (∏ k ∈ Finset.range N, w k) ≤ B := by
    intro N
    simpa [w] using hprod N
  have hess := MeasureTheory.eLpNormEssSup_le_of_eLpNorm_recurrence
    hu.continuous.aestronglyMeasurable hp0 hpTop hpTendsto hrec' hprod'
  have hinit : eLpNorm u (p 0) ω₀.volume ≤ ENNReal.ofReal (Real.sqrt (max L 0)) := by
    simpa [p] using initialNorm hu.continuous hu1 hL
  have htotal : B * ENNReal.ofReal (Real.sqrt (max L 0)) < ⊤ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hBtop) ENNReal.ofReal_lt_top
  have hCeq : ENNReal.ofReal C = B * ENNReal.ofReal (Real.sqrt (max L 0)) := by
    dsimp [C]
    exact ENNReal.ofReal_toReal htotal.ne
  have hess' : eLpNormEssSup u ω₀.volume ≤ ENNReal.ofReal C := by
    rw [hCeq]
    exact hess.trans (mul_le_mul_right hinit B)
  have hae : ∀ᵐ y ∂ω₀.volume, u y ≤ C := by
    filter_upwards [ae_le_eLpNormEssSup (f := u) (μ := ω₀.volume)] with y hy
    have hnorm : ‖u y‖ₑ = ENNReal.ofReal (u y) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (le_trans (by norm_num) (hu1 y))]
    have hle : ENNReal.ofReal (u y) ≤ ENNReal.ofReal C := by
      rw [← hnorm]
      exact hy.trans hess'
    exact (ENNReal.ofReal_le_ofReal_iff hCnonneg).mp hle
  let U : Set M := {y | C < u y}
  have hUopen : IsOpen U := isOpen_lt continuous_const hu.continuous
  have hUzero : ω₀.volume U = 0 := by
    apply measure_mono_null (s := U) (t := {y | ¬ u y ≤ C})
    · intro y hy
      exact not_le_of_gt hy
    · exact ae_iff.mp hae
  have hUempty : U = ∅ := hUopen.eq_empty_of_measure_zero hUzero
  by_contra hx
  have hxU : x ∈ U := lt_of_not_ge hx
  rw [hUempty] at hxU
  exact hxU

end KahlerForm
