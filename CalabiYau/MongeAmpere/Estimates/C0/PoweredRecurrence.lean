module

public import CalabiYau.Geometry.Kahler.Sobolev
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

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
/-- Convert a power-energy inequality into the one-step Moser recurrence by Sobolev. -/
theorem c0_powered_Lp_recurrence
    (ω₀ : KahlerForm n M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    (hu1 : ∀ x, 1 ≤ u x) {κ C_S A : ℝ}
    (hκ : 1 < κ) (hS : ω₀.SobolevInequality κ C_S)
    (hA : 0 ≤ A)
    (henergy : ∀ q : ℝ, 2 ≤ q →
      ∫ x, ω₀.gradNormSq (fun y => u y ^ (q / 2)) x ∂ω₀.volume ≤
        A * q * ∫ x, u x ^ q ∂ω₀.volume) :
    ∀ k, eLpNorm u (ENNReal.ofReal (2 * κ ^ (k + 1))) ω₀.volume ≤
      ENNReal.ofReal
          ((max C_S 1 * (1 + A * (2 * κ ^ k))) ^ ((2 * κ ^ k)⁻¹)) *
        eLpNorm u (ENNReal.ofReal (2 * κ ^ k)) ω₀.volume := by
  intro k
  let q : ℝ := 2 * κ ^ k
  let r₀ : ℝ := q
  let r₁ : ℝ := q * κ
  let f : M → ℝ := fun x => u x ^ (q / 2)
  let D : ℝ := max C_S 1 * (1 + A * q)
  have hq : 2 ≤ q := by
    dsimp [q]
    have hk : 1 ≤ κ ^ k := one_le_pow₀ hκ.le
    nlinarith
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  have hfcont : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f := by
    have hid : ContDiffOn ℝ ∞ (id : ℝ → ℝ) {t : ℝ | 0 < t} :=
      contDiff_id.contDiffOn
    have hpow : ContDiffOn ℝ ∞ (fun t : ℝ => t ^ (q / 2)) {t | 0 < t} :=
      hid.rpow_const_of_ne (fun t ht => ne_of_gt (by simpa using ht))
    have hpowMD : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ) ∞
        (fun t : ℝ => t ^ (q / 2)) {t | 0 < t} := by
      simpa only [contMDiffOn_iff_contDiffOn] using hpow
    have huPos (x : M) : u x ∈ {t : ℝ | 0 < t} :=
      lt_of_lt_of_le zero_lt_one (hu1 x)
    apply contMDiffOn_univ.mp
    simpa [f, Function.comp_def] using
      hpowMD.comp hu.contMDiffOn (fun x _ => huPos x)
  have hfnonneg (x : M) : 0 ≤ f x := by
    dsimp [f]
    exact Real.rpow_nonneg (by linarith [hu1 x]) _
  have hfSq (x : M) : f x ^ 2 = u x ^ r₀ := by
    dsimp [f, r₀, q]
    calc
      (u x ^ (2 * κ ^ k / 2)) ^ 2 =
          (u x ^ (2 * κ ^ k / 2)) ^ (2 : ℝ) := by norm_cast
      _ = u x ^ ((2 * κ ^ k / 2) * 2) :=
        (Real.rpow_mul (by linarith [hu1 x]) _ _).symm
      _ = u x ^ (2 * κ ^ k) := by congr 1; ring
  have hfHigh (x : M) : |f x| ^ (2 * κ) = u x ^ r₁ := by
    dsimp [f, r₁, q]
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith [hu1 x]) _)]
    calc
      (u x ^ (2 * κ ^ k / 2)) ^ (2 * κ) =
          u x ^ ((2 * κ ^ k / 2) * (2 * κ)) :=
        (Real.rpow_mul (by linarith [hu1 x]) _ _).symm
      _ = u x ^ (2 * κ ^ k * κ) := by congr 1; ring
  have hfae : AEStronglyMeasurable f ω₀.volume := hfcont.continuous.measurable.aestronglyMeasurable
  have hcompactInt : ∀ {g : M → ℝ}, Continuous g → Integrable g ω₀.volume := by
    intro g hg
    exact hg.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))
  have hGradCont := ω₀.contMDiff_gradNormSq hfcont
  have hIntGrad : Integrable (fun x => ω₀.gradNormSq f x) ω₀.volume :=
    hcompactInt hGradCont.continuous
  have hIntSq : Integrable (fun x => f x ^ 2) ω₀.volume :=
    hcompactInt (hfcont.continuous.pow 2)
  have hsum : ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume =
      (∫ x, ω₀.gradNormSq f x ∂ω₀.volume) + ∫ x, f x ^ 2 ∂ω₀.volume :=
    integral_add hIntGrad hIntSq
  have hJnonneg (J : ℝ) (hJ : J = ∫ x, u x ^ r₀ ∂ω₀.volume) : 0 ≤ J := by
    rw [hJ]
    exact integral_nonneg fun x => Real.rpow_nonneg (by linarith [hu1 x]) _
  let I : ℝ := ∫ x, u x ^ r₁ ∂ω₀.volume
  let J : ℝ := ∫ x, u x ^ r₀ ∂ω₀.volume
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg fun x => Real.rpow_nonneg (by linarith [hu1 x]) _
  have hJ : 0 ≤ J := hJnonneg J rfl
  have henergy' : ∫ x, ω₀.gradNormSq f x ∂ω₀.volume ≤ A * q * J := by
    simpa [f, J, r₀, q] using henergy q hq
  have hbound : ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume ≤
      (1 + A * q) * J := by
    rw [hsum]
    have hsq : (∫ x, f x ^ 2 ∂ω₀.volume) = J := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => hfSq x
    rw [hsq]
    nlinarith [henergy', mul_nonneg hA hqpos.le, hJ]
  have hCS : 0 ≤ max C_S 1 := le_trans (by norm_num) (le_max_right _ _)
  have hS' : ω₀.SobolevInequality κ (max C_S 1) := hS.mono (le_max_left _ _)
  have hsob : I ^ κ⁻¹ ≤ D * J := by
    have h := hS' f hfcont
    have hleft : (∫ x, |f x| ^ (2 * κ) ∂ω₀.volume) ^ κ⁻¹ = I ^ κ⁻¹ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => hfHigh x
    have hright : (∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume) ≤
        (1 + A * q) * J := hbound
    calc
      I ^ κ⁻¹ = (∫ x, |f x| ^ (2 * κ) ∂ω₀.volume) ^ κ⁻¹ := hleft.symm
      _ ≤ max C_S 1 *
          ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume := h
      _ ≤ max C_S 1 * ((1 + A * q) * J) := mul_le_mul_of_nonneg_left hright hCS
      _ = D * J := by dsimp [D]; ring
  have hroot : I ^ r₁⁻¹ ≤ D ^ r₀⁻¹ * J ^ r₀⁻¹ := by
    have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hI _) hsob
      (inv_nonneg.mpr hqpos.le)
    have hmul : (D * J) ^ r₀⁻¹ = D ^ r₀⁻¹ * J ^ r₀⁻¹ :=
      Real.mul_rpow (mul_nonneg hCS (by positivity)) hJ
    rw [← Real.rpow_mul hI, hmul] at hpow
    have hexp : κ⁻¹ * r₀⁻¹ = r₁⁻¹ := by
      dsimp [r₀, r₁]
      field_simp
    rw [hexp] at hpow
    exact hpow
  have hp₀ : ENNReal.ofReal r₀ = ENNReal.ofReal (2 * κ ^ k) := by
    rfl
  have hp₁ : ENNReal.ofReal r₁ = ENNReal.ofReal (2 * κ ^ (k + 1)) := by
    congr 1
    dsimp [r₁, r₀, q]
    rw [pow_succ]
    ring
  have hucont : Continuous u := hu.continuous
  have huNonneg (x : M) : 0 ≤ u x := by linarith [hu1 x]
  obtain ⟨C, hC⟩ := (isCompact_range hucont).bddAbove
  have hubound (x : M) : ‖u x‖ ≤ max C 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (huNonneg x)]
    exact (hC (Set.mem_range_self x)).trans (le_max_left _ _)
  have huAEM : AEStronglyMeasurable u ω₀.volume := hucont.measurable.aestronglyMeasurable
  have hmem₀ : MemLp u (ENNReal.ofReal r₀) ω₀.volume :=
    MemLp.of_bound huAEM (max C 0) (Filter.Eventually.of_forall hubound)
  have hmem₁ : MemLp u (ENNReal.ofReal r₁) ω₀.volume :=
    MemLp.of_bound huAEM (max C 0) (Filter.Eventually.of_forall hubound)
  have hE₀ : eLpNorm u (ENNReal.ofReal r₀) ω₀.volume = ENNReal.ofReal (J ^ r₀⁻¹) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_ne_zero_iff.mpr hqpos)
      (ENNReal.ofReal_lt_top.ne) hmem₀]
    rw [ENNReal.toReal_ofReal hqpos.le]
    have hi : (∫ x, ‖u x‖ ^ r₀ ∂ω₀.volume) = J := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change |u x| ^ r₀ = u x ^ r₀
        rw [abs_of_nonneg (huNonneg x)]
    rw [hi]
  have hE₁ : eLpNorm u (ENNReal.ofReal r₁) ω₀.volume = ENNReal.ofReal (I ^ r₁⁻¹) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hqpos hκpos))
      (ENNReal.ofReal_lt_top.ne) hmem₁]
    rw [ENNReal.toReal_ofReal (mul_pos hqpos hκpos).le]
    have hi : (∫ x, ‖u x‖ ^ r₁ ∂ω₀.volume) = I := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change |u x| ^ r₁ = u x ^ r₁
        rw [abs_of_nonneg (huNonneg x)]
    rw [hi]
  have hfactorReal : D ^ r₀⁻¹ =
      (max C_S 1 * (1 + A * (2 * κ ^ k))) ^ ((2 * κ ^ k)⁻¹) := by
    dsimp [D, r₀, q]
  have hfactorENN : ENNReal.ofReal (D ^ r₀⁻¹) = ENNReal.ofReal
      ((max C_S 1 * (1 + A * (2 * κ ^ k))) ^ ((2 * κ ^ k)⁻¹)) := by
    rw [hfactorReal]
  have hErec : eLpNorm u (ENNReal.ofReal r₁) ω₀.volume ≤
      ENNReal.ofReal (D ^ r₀⁻¹) * eLpNorm u (ENNReal.ofReal r₀) ω₀.volume := by
    rw [hE₁, hE₀]
    have hD : 0 ≤ D ^ r₀⁻¹ := Real.rpow_nonneg (mul_nonneg hCS (by positivity)) _
    have hmul : ENNReal.ofReal (D ^ r₀⁻¹) * ENNReal.ofReal (J ^ r₀⁻¹) =
        ENNReal.ofReal (D ^ r₀⁻¹ * J ^ r₀⁻¹) :=
      (ENNReal.ofReal_mul hD).symm
    rw [hmul]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hD (Real.rpow_nonneg hJ _))).2 hroot
  rw [hp₁.symm, hp₀.symm, ← hfactorENN]
  exact hErec

end KahlerForm
