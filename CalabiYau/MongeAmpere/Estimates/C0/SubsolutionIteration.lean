module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Kahler.Sobolev

public section

open scoped Manifold ContDiff
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem gradNormSq_comp (ω₀ : KahlerForm n M) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (x : M) :
    ω₀.gradNormSq (h ∘ f) x = (deriv h (f x)) ^ 2 * ω₀.gradNormSq f x := by
  let q : ℝ → ℝ := fun t => h t ^ 2
  have h2le : (2 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hh2 : ContDiff ℝ 2 h := hh.of_le h2le
  have hD : Differentiable ℝ h := hh2.differentiable (by norm_num)
  have hq : ContDiff ℝ 2 q := by
    have hqTop : ContDiff ℝ ∞ q := by
      simpa [q, pow_two] using hh.mul hh
    exact hqTop.of_le h2le
  have hcomp : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (h ∘ f) :=
    hh.contMDiff.comp hf
  have hq' : ∀ t, deriv q t = 2 * (h t * deriv h t) := by
    intro t
    have hqeq : q = h * h := by
      funext s
      simp [q, pow_two]
    rw [hqeq, deriv_mul (hD.differentiableAt (x := t)) (hD.differentiableAt (x := t))]
    ring
  have hq'' : ∀ t, deriv (deriv q) t =
      2 * (deriv h t) ^ 2 + 2 * (h t * deriv (deriv h) t) := by
    intro t
    have hD' : Differentiable ℝ (deriv h) := hh2.differentiable_deriv_two
    have hderivh : DifferentiableAt ℝ (deriv h) t := hD'.differentiableAt (x := t)
    rw [show deriv q = fun t => 2 * (h t * deriv h t) from funext hq',
      deriv_const_mul_field,
      deriv_fun_mul (hD.differentiableAt (x := t)) hderivh]
    ring
  have hsquare : ContDiff ℝ 2 (fun t : ℝ => t ^ 2) :=
    (contDiff_id.pow 2).of_le h2le
  have hsquare' : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
    funext t
    change deriv ((fun t : ℝ => t) ^ 2) t = 2 * t
    rw [deriv_pow differentiableAt_id 2]
    norm_num
  have hsquare'' : deriv (deriv (fun t : ℝ => t ^ 2)) = fun _ => 2 := by
    rw [hsquare']
    funext t
    simp
  have hdouble : deriv (fun t : ℝ => 2 * t) = fun _ => 2 := by
    funext t
    simp
  have hlap_comp := ω₀.laplacian_comp hf hh2 x
  have hlap_square := ω₀.laplacian_comp hcomp hsquare x
  have hlap_q := ω₀.laplacian_comp hf hq x
  have hqcomp : q ∘ f = fun y => (h (f y)) ^ 2 := by
    funext y
    rfl
  have htwice : 2 * ω₀.gradNormSq (h ∘ f) x =
      2 * (deriv h (f x)) ^ 2 * ω₀.gradNormSq f x := by
    calc
      2 * ω₀.gradNormSq (h ∘ f) x =
        ω₀.laplacian (fun y => (h (f y)) ^ 2) x -
          2 * h (f x) * ω₀.laplacian (h ∘ f) x := by
        change 2 * ω₀.gradNormSq (h ∘ f) x =
          ω₀.laplacian ((fun t : ℝ => t ^ 2) ∘ h ∘ f) x -
            2 * h (f x) * ω₀.laplacian (h ∘ f) x
        rw [hlap_square]
        rw [hsquare', hdouble]
        simp only [Function.comp_apply]
        ring
      _ = ω₀.laplacian (q ∘ f) x -
            2 * h (f x) * ω₀.laplacian (h ∘ f) x := by rw [← hqcomp]
      _ = 2 * (deriv h (f x)) ^ 2 * ω₀.gradNormSq f x := by
        rw [hlap_q, hq' (f x), hq'' (f x), hlap_comp]
        ring
  nlinarith [htwice]
theorem integrable_of_continuous_volume (ω₀ : KahlerForm n M) {f : M → ℝ}
    (hf : Continuous f) : Integrable f ω₀.volume :=
  hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _)
      )
theorem sobolev_energy_step
    (ω₀ : KahlerForm n M) {κ C_S A : ℝ}
    (hS : ω₀.SobolevInequality κ C_S) (hCS : 0 ≤ C_S)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (henergy : ∫ x, ω₀.gradNormSq f x ∂ω₀.volume ≤
      A * ∫ x, f x ^ 2 ∂ω₀.volume) :
    (∫ x, |f x| ^ (2 * κ) ∂ω₀.volume) ^ κ⁻¹ ≤
      (C_S * (A + 1)) * ∫ x, f x ^ 2 ∂ω₀.volume := by
  have hContGrad := ω₀.contMDiff_gradNormSq hf
  have hIntGrad : Integrable (fun x => ω₀.gradNormSq f x) ω₀.volume :=
    integrable_of_continuous_volume ω₀ hContGrad.continuous
  have hIntSq : Integrable (fun x => f x ^ 2) ω₀.volume :=
    integrable_of_continuous_volume ω₀ ((hf.continuous).pow 2)
  have hsqNonneg : 0 ≤ ∫ x, f x ^ 2 ∂ω₀.volume :=
    integral_nonneg fun x => sq_nonneg (f x)
  have hsum : ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume =
      ∫ x, ω₀.gradNormSq f x ∂ω₀.volume + ∫ x, f x ^ 2 ∂ω₀.volume :=
    integral_add hIntGrad hIntSq
  have hbound : ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume ≤
      (A + 1) * ∫ x, f x ^ 2 ∂ω₀.volume := by
    rw [hsum]
    nlinarith
  calc
    _ ≤ C_S * ∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂ω₀.volume := hS f hf
    _ ≤ C_S * ((A + 1) * ∫ x, f x ^ 2 ∂ω₀.volume) :=
      mul_le_mul_of_nonneg_left hbound hCS
    _ = (C_S * (A + 1)) * ∫ x, f x ^ 2 ∂ω₀.volume := by ring
theorem integral_deriv_comp_laplacian_eq_neg_energy
    (ω₀ : KahlerForm n M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ∫ x, deriv F (u x) * ω₀.laplacian u x ∂ω₀.volume =
      -∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume := by
  have h2le : (2 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hF2 : ContDiff ℝ 2 F := hF.of_le h2le
  have hF' : ContDiff ℝ ∞ (deriv F) := contDiff_infty_iff_deriv.mp hF |>.2
  have hcontF' : Continuous (deriv F) := hF.continuous_deriv (by norm_num)
  have hcontF'' : Continuous (deriv (deriv F)) := hF'.continuous_deriv (by norm_num)
  have hcomp : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (F ∘ u) :=
    hF.contMDiff.comp hu
  have hLapComp : ∀ x, ω₀.laplacian (F ∘ u) x =
      deriv F (u x) * ω₀.laplacian u x + deriv (deriv F) (u x) * ω₀.gradNormSq u x := by
    intro x
    exact ω₀.laplacian_comp hu hF2 x
  have hLapCont := ω₀.contMDiff_laplacian hu
  have hGradCont := ω₀.contMDiff_gradNormSq hu
  have hInt₁ : Integrable (fun x => deriv F (u x) * ω₀.laplacian u x) ω₀.volume :=
    integrable_of_continuous_volume ω₀
      ((hcontF'.comp hu.continuous).mul hLapCont.continuous)
  have hInt₂ : Integrable
      (fun x => deriv (deriv F) (u x) * ω₀.gradNormSq u x) ω₀.volume :=
    integrable_of_continuous_volume ω₀
      ((hcontF''.comp hu.continuous).mul hGradCont.continuous)
  have hzero : ∫ x, ω₀.laplacian (F ∘ u) x ∂ω₀.volume = 0 :=
    ω₀.integral_laplacian hcomp
  rw [show (fun x => ω₀.laplacian (F ∘ u) x) =
      fun x => deriv F (u x) * ω₀.laplacian u x +
        deriv (deriv F) (u x) * ω₀.gradNormSq u x from funext hLapComp,
    integral_add hInt₁ hInt₂] at hzero
  linarith

theorem subsolution_weighted_energy_bound
    (ω₀ : KahlerForm n M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hsub : ∀ x, -(n : ℝ) ≤ ω₀.laplacian u x)
    (hF' : ∀ t, 0 ≤ deriv F t) :
    ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume ≤
      (n : ℝ) * ∫ x, deriv F (u x) ∂ω₀.volume := by
  have hF'cont : Continuous (deriv F) :=
    hF.continuous_deriv (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hF''cont : Continuous (deriv (deriv F)) := by
    have hFderiv : ContDiff ℝ ∞ (deriv F) := contDiff_infty_iff_deriv.mp hF |>.2
    exact hFderiv.continuous_deriv (by norm_num)
  have hLapCont := ω₀.contMDiff_laplacian hu
  have hGradCont := ω₀.contMDiff_gradNormSq hu
  have hIleft : Integrable (fun x => deriv F (u x) * ω₀.laplacian u x) ω₀.volume :=
    integrable_of_continuous_volume ω₀
      ((hF'cont.comp hu.continuous).mul hLapCont.continuous)
  have hItest : Integrable (fun x => deriv F (u x)) ω₀.volume :=
    integrable_of_continuous_volume ω₀ (hF'cont.comp hu.continuous)
  have hmono : ∫ x, (-(n : ℝ)) * deriv F (u x) ∂ω₀.volume ≤
      ∫ x, deriv F (u x) * ω₀.laplacian u x ∂ω₀.volume := by
    apply integral_mono_ae
      ((integrable_of_continuous_volume ω₀ (continuous_const.mul (hF'cont.comp hu.continuous))))
      hIleft
    exact Filter.Eventually.of_forall fun x => by
      calc
        (-(n : ℝ)) * deriv F (u x) = deriv F (u x) * (-(n : ℝ)) := by ring
        _ ≤ deriv F (u x) * ω₀.laplacian u x :=
          mul_le_mul_of_nonneg_left (hsub x) (hF' (u x))
  have henergy := integral_deriv_comp_laplacian_eq_neg_energy ω₀ hu hF
  rw [integral_const_mul] at hmono
  linarith

theorem subsolution_sobolev_step
    (ω₀ : KahlerForm n M) {κ C_S A δ : ℝ}
    (hS : ω₀.SobolevInequality κ C_S) (hCS : 0 ≤ C_S) (hA : 0 ≤ A) (hδ : 0 < δ)
    {u : M → ℝ} (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    (hsub : ∀ x, -(n : ℝ) ≤ ω₀.laplacian u x)
    {h F : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hF : ContDiff ℝ ∞ F)
    (hF'' : ∀ t, δ * (deriv h t) ^ 2 ≤ deriv (deriv F) t)
    (hF'nonneg : ∀ t, 0 ≤ deriv F t)
    (hF'le : ∀ t, deriv F t ≤ A * h t ^ 2) :
    (∫ x, |h (u x)| ^ (2 * κ) ∂ω₀.volume) ^ κ⁻¹ ≤
      (C_S * (δ⁻¹ * ((n : ℝ) * A) + 1)) * ∫ x, h (u x) ^ 2 ∂ω₀.volume := by
  let f : M → ℝ := h ∘ u
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f := hh.contMDiff.comp hu
  have hgradPoint : ∀ x, δ * ω₀.gradNormSq f x ≤
      deriv (deriv F) (u x) * ω₀.gradNormSq u x := by
    intro x
    rw [gradNormSq_comp ω₀ hu hh x]
    calc
      δ * ((deriv h (u x)) ^ 2 * ω₀.gradNormSq u x) =
          (δ * (deriv h (u x)) ^ 2) * ω₀.gradNormSq u x := by ring
      _ ≤ deriv (deriv F) (u x) * ω₀.gradNormSq u x :=
        mul_le_mul_of_nonneg_right (hF'' (u x)) (ω₀.gradNormSq_nonneg u x)
  have henergy := subsolution_weighted_energy_bound ω₀ hu hF hsub hF'nonneg
  have hgradInt : Integrable (fun x => ω₀.gradNormSq f x) ω₀.volume :=
    integrable_of_continuous_volume ω₀ (ω₀.contMDiff_gradNormSq hf).continuous
  have henergyInt : Integrable
      (fun x => deriv (deriv F) (u x) * ω₀.gradNormSq u x) ω₀.volume := by
    have hF''cont : Continuous (deriv (deriv F)) := by
      have hderiv : ContDiff ℝ ∞ (deriv F) := contDiff_infty_iff_deriv.mp hF |>.2
      exact hderiv.continuous_deriv (by norm_num)
    exact integrable_of_continuous_volume ω₀
      ((hF''cont.comp hu.continuous).mul (ω₀.contMDiff_gradNormSq hu).continuous)
  have hgradIntScaled : Integrable (fun x => δ * ω₀.gradNormSq f x) ω₀.volume :=
    hgradInt.const_mul δ
  have hgradIntLe : ∫ x, δ * ω₀.gradNormSq f x ∂ω₀.volume ≤
      ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume :=
    integral_mono_ae hgradIntScaled henergyInt (Filter.Eventually.of_forall hgradPoint)
  have hgradIntLe' : ∫ x, ω₀.gradNormSq f x ∂ω₀.volume ≤
      δ⁻¹ * ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume := by
    have hscaled : δ * ∫ x, ω₀.gradNormSq f x ∂ω₀.volume ≤
        ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume := by
      simpa only [integral_const_mul, mul_comm] using hgradIntLe
    calc
      ∫ x, ω₀.gradNormSq f x ∂ω₀.volume ≤
          (∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume) / δ :=
        (le_div_iff₀ hδ).2 (by simpa [mul_comm] using hscaled)
      _ = δ⁻¹ * ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume := by
        simp [div_eq_mul_inv, mul_comm]
  have hF'cont : Continuous (deriv F) :=
    hF.continuous_deriv (by norm_num : (1 : ℕ∞ω) ≤ ∞)
  have hIntF' : Integrable (fun x => deriv F (u x)) ω₀.volume :=
    integrable_of_continuous_volume ω₀ (hF'cont.comp hu.continuous)
  have hIntSq : Integrable (fun x => h (u x) ^ 2) ω₀.volume :=
    integrable_of_continuous_volume ω₀ ((hf.continuous).pow 2)
  have hbound : ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume ≤
      ((n : ℝ) * A) * ∫ x, h (u x) ^ 2 ∂ω₀.volume := by
    have hmono : ∫ x, deriv F (u x) ∂ω₀.volume ≤
        A * ∫ x, h (u x) ^ 2 ∂ω₀.volume := by
      have h := integral_mono_ae hIntF' (hIntSq.const_mul A)
        (Filter.Eventually.of_forall fun x => hF'le (u x))
      simpa [integral_const_mul] using h
    have hmono' := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg n)
    simpa only [mul_assoc] using henergy.trans hmono'
  have henergySq : ∫ x, ω₀.gradNormSq f x ∂ω₀.volume ≤
      ((δ⁻¹ * ((n : ℝ) * A))) * ∫ x, f x ^ 2 ∂ω₀.volume := by
    calc
      ∫ x, ω₀.gradNormSq f x ∂ω₀.volume ≤
          δ⁻¹ * ∫ x, deriv (deriv F) (u x) * ω₀.gradNormSq u x ∂ω₀.volume := hgradIntLe'
      _ ≤ δ⁻¹ * (((n : ℝ) * A) * ∫ x, f x ^ 2 ∂ω₀.volume) :=
        mul_le_mul_of_nonneg_left (by simpa [f] using hbound) (inv_nonneg.mpr hδ.le)
      _ = (δ⁻¹ * ((n : ℝ) * A)) * ∫ x, f x ^ 2 ∂ω₀.volume := by ring
  have hA₀ : 0 ≤ δ⁻¹ * ((n : ℝ) * A) :=
    mul_nonneg (inv_nonneg.mpr hδ.le) (mul_nonneg (Nat.cast_nonneg _) hA)
  simpa [f] using sobolev_energy_step ω₀ hS hCS hf henergySq

end KahlerForm
