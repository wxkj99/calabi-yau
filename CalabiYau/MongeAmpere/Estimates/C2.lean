module

public import CalabiYau.MongeAmpere.Operator
import CalabiYau.Geometry.Complex.Forms.Positive
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import CalabiYau.MongeAmpere.Estimates.C2.ChernLuFormula
import CalabiYau.MongeAmpere.Estimates.C2.MongeAmpereRicci
import CalabiYau.MongeAmpere.Estimates.C2.ReferenceRicciBound

/-!
# The `C²` estimate (Aubin–Yau)

If `(ω₀ + i∂∂̄φ)ⁿ = e^G ω₀ⁿ` with `|G| ≤ K`, `Δ_ω₀ G ≥ -K` and `osc φ ≤ K`, then
`ω_φ = ω₀ + i∂∂̄φ` is uniformly equivalent to `ω₀`: `tr_ω₀ ω_φ ≤ C` and `tr_{ω_φ} ω₀ ≤ C`, with
`C` depending only on `(M, ω₀)` and `K`. The dependence on `(M, ω₀)` is through a lower bound for
the holomorphic bisectional curvature of `ω₀`, which exists by compactness.

No global analytic input is needed: the proof is a maximum principle argument.

## Proof sketch (Yau 1978, §2; Aubin; Székelyhidi, Lemmas 3.7–3.8 (the Laplacian estimate);
Siu, *Lectures on Hermitian–Einstein metrics*, Ch. 2)

Let `ω₁ = ω_φ`, `u = tr_ω₀ ω₁ > 0`. In holomorphic normal coordinates for `ω₀` at a point where
`ω₁` is diagonal (`KahlerForm.metricInChart`, `metricInChart_perturb`), the Chern–Lu / Aubin–Yau
computation gives

  `Δ_{ω₁} log u ≥ (Δ_ω₀ G) / u - B tr_{ω₁} ω₀`,

where `-B` is a lower bound of the bisectional curvature of `ω₀`. Since `Δ_{ω₁} φ = n - tr_{ω₁} ω₀`,
for `A = B + 1` the function `log u - A φ` satisfies
`Δ_{ω₁} (log u - A φ) ≥ tr_{ω₁} ω₀ - A n - K / u`. At its maximum point
(`relTrace_mddbar_nonpos_of_isLocalMax` with `α = ω₁`) this bounds `tr_{ω₁} ω₀`, hence `u` there
(`relTrace_le_relTrace_pow_div_relDet`, `u ≥ n e^{-K/n}` by AM–GM), hence `u ≤ C e^{A osc φ}`
everywhere. The bound on `tr_{ω₁} ω₀` follows from `relTrace_le_relTrace_pow_div_relDet`.
-/

@[expose] public section

open scoped Manifold ContDiff
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
section

variable [T2Space M] [CompactSpace M]


private theorem c2_weighted_bisectional_sum_lower_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : κ → ℝ) (R : ι → κ → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hR : ∀ i j, -B ≤ R i j) :
    -B * (∑ i, a i) * (∑ j, b j) ≤ ∑ i, ∑ j, a i * b j * R i j := by
  calc
    -B * (∑ i, a i) * (∑ j, b j) =
        ∑ i, ∑ j, a i * b j * (-B) := by
      have hprod : (∑ i, a i) * (∑ j, b j) = ∑ i, ∑ j, a i * b j :=
        Fintype.sum_mul_sum a b
      calc
        -B * (∑ i, a i) * (∑ j, b j) =
            -B * ((∑ i, a i) * (∑ j, b j)) := by ring
        _ = -B * (∑ i, ∑ j, a i * b j) := by rw [hprod]
        _ = ∑ i, ∑ j, a i * b j * (-B) := by
          simp_rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
    _ ≤ ∑ i, ∑ j, a i * b j * R i j := by
      refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
      exact mul_le_mul_of_nonneg_left (hR i j) (mul_nonneg (ha i) (hb j))

/-- Componentwise normal-coordinate trace Laplacian expansion.  Here `referenceSecond` is
the second derivative of the reference metric coefficient and `curvature` uses the standard
minus convention `R_{p\bar p j\bar j} = -∂p∂̄p g_{j\bar j}` at a normal-coordinate center.
The differential identities that identify these arrays for the geometric metrics remain a
separate Chern–Lu input. -/
private theorem c2_normal_coordinate_trace_laplacian_expansion
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lambda : ι → ℝ) (referenceSecond perturbSecond curvature : ι → κ → ℝ)
    (hcurvature : ∀ p j, curvature p j = -referenceSecond p j) :
    (∑ p, ∑ j, (referenceSecond p j + perturbSecond p j) / lambda p) =
      (∑ p, ∑ j, perturbSecond p j / lambda p) -
        ∑ p, ∑ j, curvature p j / lambda p := by
  have hcurvatureSum : (∑ p, ∑ j, curvature p j / lambda p) =
      -(∑ p, ∑ j, referenceSecond p j / lambda p) := by
    simp_rw [hcurvature, neg_div, Finset.sum_neg_distrib]
  rw [hcurvatureSum]
  simp_rw [add_div, Finset.sum_add_distrib]
  ring

/-- Lower bound for the curvature contraction in the preceding normal-coordinate expansion.
The second index family contributes its cardinality because the raw trace Laplacian has no
additional eigenvalue weight on that index before the differentiated Monge–Ampère equation is
used. -/
private theorem c2_normal_coordinate_curvature_contraction_lower_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lambda : ι → ℝ) (curvature : ι → κ → ℝ) (B : ℝ)
    (hlambda : ∀ p, 0 < lambda p) (hcurvature : ∀ p j, -B ≤ curvature p j) :
    -B * (∑ p, (lambda p)⁻¹) * (Fintype.card κ : ℝ) ≤
      ∑ p, ∑ j, (lambda p)⁻¹ * curvature p j := by
  have h := c2_weighted_bisectional_sum_lower_bound
    (fun p ↦ (lambda p)⁻¹) (fun _ : κ ↦ (1 : ℝ)) curvature B
    (fun p ↦ inv_nonneg.mpr (hlambda p).le) (fun _ ↦ zero_le_one) hcurvature
  simpa [mul_assoc] using h

/-- The bisectional-curvature contraction with the eigenvalue weights that arise after the
differentiated Monge–Ampère equation is used: `R ≥ -B` implies
`∑_{p,j} (λⱼ / λₚ) R_{p\bar p j\bar j} ≥ -B (∑ λⱼ) (∑ λₚ⁻¹)`. -/
private theorem c2_weighted_curvature_trace_lower_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (lambda : ι → ℝ) (mu : κ → ℝ) (curvature : ι → κ → ℝ) (B : ℝ)
    (hlambda : ∀ p, 0 < lambda p) (hmu : ∀ j, 0 ≤ mu j)
    (hcurvature : ∀ p j, -B ≤ curvature p j) :
    -B * (∑ j, mu j) * (∑ p, (lambda p)⁻¹) ≤
      ∑ p, ∑ j, (lambda p)⁻¹ * mu j * curvature p j := by
  have h := c2_weighted_bisectional_sum_lower_bound
    (fun p ↦ (lambda p)⁻¹) mu curvature B
    (fun p ↦ inv_nonneg.mpr (hlambda p).le) hmu hcurvature
  calc
    -B * (∑ j, mu j) * (∑ p, (lambda p)⁻¹) =
        -B * (∑ p, (lambda p)⁻¹) * (∑ j, mu j) := by ring
    _ ≤ ∑ p, ∑ j, (lambda p)⁻¹ * mu j * curvature p j := h

/-- Absorb the bounded reference-Ricci scalar in the Chern–Lu pointwise inequality.  The
`n² ≤ u v` trace bridge turns `C/u` into `(C/n²) v`. -/
private theorem c2_absorb_reference_scalar_term
    {n : ℕ} (u v s C B K dG lap : ℝ)
    (hn : 0 < (n : ℝ)) (hu : 0 < u) (hC : 0 ≤ C)
    (huv : (n : ℝ) ^ 2 ≤ u * v) (hs : s ≤ C)
    (hdG : -K ≤ dG)
    (hCL : lap ≥ (dG - s) / u - B * v) :
    lap ≥ -K / u - (B + C / (n : ℝ) ^ 2) * v := by
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn
  have hscaled : (n : ℝ) ^ 2 / u ≤ v := (div_le_iff₀ hu).2 (by nlinarith)
  have hCscaled : C / u ≤ (C / (n : ℝ) ^ 2) * v := by
    calc
      C / u = (C / (n : ℝ) ^ 2) * ((n : ℝ) ^ 2 / u) := by
        field_simp [hn2.ne']
      _ ≤ (C / (n : ℝ) ^ 2) * v :=
        mul_le_mul_of_nonneg_left hscaled (div_nonneg hC hn2.le)
  have hsdiv : s / u ≤ C / u := div_le_div_of_nonneg_right hs hu.le
  have hdGdiv : -K / u ≤ dG / u := div_le_div_of_nonneg_right hdG hu.le
  have hsplit : (dG - s) / u = dG / u - s / u := by rw [sub_div]
  calc
    lap ≥ (dG - s) / u - B * v := hCL
    _ = dG / u - s / u - B * v := by rw [hsplit]
    _ ≥ -K / u - (C / (n : ℝ) ^ 2) * v - B * v := by linarith
    _ = -K / u - (B + C / (n : ℝ) ^ 2) * v := by ring

private noncomputable def c2TraceBoundConstant (n : ℕ) (K A δ : ℝ) : ℝ :=
  let T := A * (n : ℝ) + K / δ + 1
  let U := T ^ (n - 1) * Real.exp K * Real.exp (A * K)
  max U (U ^ (n - 1) * Real.exp K)

end

variable [CompactSpace M] in
private theorem c2_trace_bounds_of_chernLu
    (ω₀ : KahlerForm n M) (K A δ : ℝ) {G φ : M → ℝ}
    (hGbound : ∀ x, |G x| ≤ K) (hosc : ∀ x y, φ x - φ y ≤ K)
    (hsol : ω₀.SolvesMongeAmpere G φ) (hK : 0 ≤ K) (hA : 0 ≤ A) (hδ : 0 < δ)
    (htraceLower : ∀ x, δ ≤ relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x))
    (hF_smooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ Real.log (relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x)) - A * φ x))
    (hCL : ∀ x,
      (ω₀.perturb φ hsol.1).laplacian
        (fun y ↦ Real.log (relTrace (ω₀ y) ((ω₀.perturb φ hsol.1) y)) - A * φ y) x ≥
          relTrace ((ω₀.perturb φ hsol.1) x) (ω₀ x) -
            A * (n : ℝ) - K / relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x)) :
    ∀ x,
      relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x) ≤ c2TraceBoundConstant n K A δ ∧
        relTrace ((ω₀.perturb φ hsol.1) x) (ω₀ x) ≤ c2TraceBoundConstant n K A δ := by
  by_cases hM : Nonempty M
  · let ω₁ : KahlerForm n M := ω₀.perturb φ hsol.1
    let u : M → ℝ := fun x ↦ relTrace (ω₀ x) (ω₁ x)
    let v : M → ℝ := fun x ↦ relTrace (ω₁ x) (ω₀ x)
    let F : M → ℝ := fun x ↦ Real.log (u x) - A * φ x
    have hu_pos (x : M) : 0 < u x := lt_of_lt_of_le hδ (htraceLower x)
    have hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F := by
      simpa [F, u, ω₁] using hF_smooth
    obtain ⟨x₀, hx₀, hmax⟩ :=
      isCompact_univ.exists_isMaxOn Set.univ_nonempty hF.continuous.continuousOn
    have hlocal : IsLocalMax F x₀ := hmax.isLocalMax Filter.univ_mem
    have hΔF : (ω₁.laplacian F x₀) ≤ 0 := ω₁.laplacian_nonpos_of_isLocalMax hF hlocal
    have hKdiv : K / u x₀ ≤ K / δ := div_le_div_of_nonneg_left hK hδ (htraceLower x₀)
    have hv_bound : v x₀ ≤ A * (n : ℝ) + K / δ + 1 := by
      have hlow : v x₀ - A * (n : ℝ) - K / u x₀ ≤ 0 := (hCL x₀).trans hΔF
      linarith
    let T : ℝ := A * (n : ℝ) + K / δ + 1
    have hT : 0 < T := by
      dsimp [T]
      positivity
    have hv_nonneg : 0 ≤ v x₀ :=
      relTrace_nonneg (ω₁.isPositive x₀) (ω₀.isPositive x₀).isNonneg
    have htrace_at_max : u x₀ ≤ v x₀ ^ (n - 1) /
        relDet (ω₁ x₀) (ω₀ x₀) := by
      exact relTrace_le_relTrace_pow_div_relDet (ω₁.isPositive x₀) (ω₀.isPositive x₀)
    have hdet_mul : relDet (ω₀ x₀) (ω₁ x₀) * relDet (ω₁ x₀) (ω₀ x₀) =
        relDet (ω₀ x₀) (ω₀ x₀) :=
      relDet_mul_relDet (ω₀.isPositive x₀) (ω₁.isPositive x₀)
    rw [relDet_self (ω₀.isPositive x₀)] at hdet_mul
    have hdet_rev_pos : 0 < relDet (ω₁ x₀) (ω₀ x₀) :=
      relDet_pos (ω₁.isPositive x₀) (ω₀.isPositive x₀)
    have hdet_rev_ne : relDet (ω₁ x₀) (ω₀ x₀) ≠ 0 := hdet_rev_pos.ne'
    have hdet_eq : relDet (ω₀ x₀) (ω₁ x₀) = Real.exp (G x₀) := by
      change relDet (ω₀ x₀) (ω₀ x₀ + mddbar n φ x₀) = _
      simpa [mongeAmpere] using hsol.2 x₀
    have hdet_rev_inv : (relDet (ω₁ x₀) (ω₀ x₀))⁻¹ = relDet (ω₀ x₀) (ω₁ x₀) := by
      field_simp [hdet_rev_ne]
      nlinarith [hdet_mul]
    have hG_upper : G x₀ ≤ K := le_trans (le_abs_self _) (hGbound x₀)
    have hdet_rev_inv_bound : (relDet (ω₁ x₀) (ω₀ x₀))⁻¹ ≤ Real.exp K := by
      rw [hdet_rev_inv, hdet_eq]
      exact Real.exp_le_exp.mpr hG_upper
    have hv_T : v x₀ ≤ T := by simpa [T] using hv_bound
    have hv_pow : v x₀ ^ (n - 1) ≤ T ^ (n - 1) :=
      pow_le_pow_left₀ hv_nonneg hv_T _
    have hU0 : u x₀ ≤ T ^ (n - 1) * Real.exp K := by
      calc
        u x₀ ≤ v x₀ ^ (n - 1) / relDet (ω₁ x₀) (ω₀ x₀) := htrace_at_max
        _ = v x₀ ^ (n - 1) * (relDet (ω₁ x₀) (ω₀ x₀))⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ T ^ (n - 1) * Real.exp K := by
          exact mul_le_mul hv_pow hdet_rev_inv_bound (inv_nonneg.mpr hdet_rev_pos.le)
            (pow_nonneg hT.le _)
    let U₀ : ℝ := T ^ (n - 1) * Real.exp K
    have hU₀ : 0 < U₀ := by
      dsimp [U₀]
      positivity
    have hlog_max : Real.log (u x₀) ≤ Real.log U₀ := Real.log_le_log (hu_pos x₀) hU0
    let U : ℝ := U₀ * Real.exp (A * K)
    have hU : 0 < U := by
      dsimp [U]
      positivity
    have hu_bound (x : M) : u x ≤ U := by
      have hoscA : A * (φ x - φ x₀) ≤ A * K := mul_le_mul_of_nonneg_left (hosc x x₀) hA
      have hlog_bound : Real.log (u x) ≤ Real.log U₀ + A * K := by
        have hmaxx := hmax (Set.mem_univ x)
        change Real.log (u x) - A * φ x ≤ Real.log (u x₀) - A * φ x₀ at hmaxx
        nlinarith [hlog_max, hoscA]
      have hexp := Real.exp_le_exp.mpr hlog_bound
      rw [Real.exp_log (hu_pos x), Real.exp_add, Real.exp_log hU₀] at hexp
      simpa [U, mul_comm] using hexp
    have hG_lower (x : M) : -G x ≤ K := by
      simpa using neg_le_neg (abs_le.mp (hGbound x)).1
    have hdet_inv_bound (x : M) :
        (relDet (ω₀ x) (ω₁ x))⁻¹ ≤ Real.exp K := by
      calc
        (relDet (ω₀ x) (ω₁ x))⁻¹ = Real.exp (-G x) := by
          have hd : relDet (ω₀ x) (ω₁ x) = Real.exp (G x) := by
            change relDet (ω₀ x) (ω₀ x + mddbar n φ x) = _
            simpa [mongeAmpere] using hsol.2 x
          rw [hd, ← Real.exp_neg]
        _ ≤ Real.exp K := Real.exp_le_exp.mpr (hG_lower x)
    have hv_bound (x : M) : v x ≤ U ^ (n - 1) * Real.exp K := by
      have hω₀ : (ω₀ x).IsPositive := ω₀.isPositive x
      have hω₁ : (ω₁ x).IsPositive := ω₁.isPositive x
      have htrace_x : v x ≤ u x ^ (n - 1) / relDet (ω₀ x) (ω₁ x) :=
        relTrace_le_relTrace_pow_div_relDet hω₀ hω₁
      have hu_pow : u x ^ (n - 1) ≤ U ^ (n - 1) :=
        pow_le_pow_left₀ (le_of_lt (hu_pos x)) (hu_bound x) _
      calc
        v x ≤ u x ^ (n - 1) / relDet (ω₀ x) (ω₁ x) := htrace_x
        _ = u x ^ (n - 1) * (relDet (ω₀ x) (ω₁ x))⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ U ^ (n - 1) * Real.exp K := by
          exact mul_le_mul hu_pow (hdet_inv_bound x)
            (inv_nonneg.mpr (relDet_pos hω₀ hω₁).le) (pow_nonneg hU.le _)
    have hconstant : c2TraceBoundConstant n K A δ = max U (U ^ (n - 1) * Real.exp K) := by
      simp [c2TraceBoundConstant, U, U₀, T]
    intro x
    rw [hconstant]
    exact ⟨(hu_bound x).trans (le_max_left _ _), (hv_bound x).trans (le_max_right _ _)⟩
  · intro x
    exact (hM ⟨x⟩).elim

private theorem c2_trace_lower_bound_of_mongeAmpere
    [NeZero n] (ω₀ : KahlerForm n M) (K : ℝ) {G φ : M → ℝ}
    (hGbound : ∀ x, |G x| ≤ K) (hsol : ω₀.SolvesMongeAmpere G φ) (x : M) :
    (n : ℝ) * Real.exp (-K / (n : ℝ)) ≤
      relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x) := by
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hω : (ω₀ x).IsPositive := ω₀.isPositive x
  have hα : ((ω₀.perturb φ hsol.1) x).IsPositive := hsol.1.2 x
  have hdet : relDet (ω₀ x) ((ω₀.perturb φ hsol.1) x) = Real.exp (G x) := by
    change relDet (ω₀ x) (ω₀ x + mddbar n φ x) = _
    simpa [mongeAmpere] using hsol.2 x
  have hG_lower : -K ≤ G x := (abs_le.mp (hGbound x)).1
  have hdet_lower : Real.exp (-K) ≤ relDet (ω₀ x) ((ω₀.perturb φ hsol.1) x) := by
    rw [hdet]
    exact Real.exp_le_exp.mpr hG_lower
  have hdet_pos : 0 < relDet (ω₀ x) ((ω₀.perturb φ hsol.1) x) := relDet_pos hω hα
  have hlogdet : -K ≤ Real.log (relDet (ω₀ x) ((ω₀.perturb φ hsol.1) x)) := by
    have h := Real.log_le_log (Real.exp_pos (-K)) hdet_lower
    simpa using h
  let q : ℝ := (n : ℝ)⁻¹
  have hq : 0 < q := inv_pos.mpr hn
  have hroot : Real.exp (-K / (n : ℝ)) ≤
      relDet (ω₀ x) ((ω₀.perturb φ hsol.1) x) ^ q := by
    rw [Real.rpow_def_of_pos hdet_pos]
    apply Real.exp_le_exp.mpr
    calc
      -K / (n : ℝ) = -K * q := by simp [q, div_eq_mul_inv]
      _ ≤ Real.log (relDet (ω₀ x) ((ω₀.perturb φ hsol.1) x)) * q :=
        mul_le_mul_of_nonneg_right hlogdet hq.le
  have hAMGM := relDet_rpow_le_relTrace_div hω hα.isNonneg
  have hroot_trace : Real.exp (-K / (n : ℝ)) ≤
      relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x) / n := by
    exact hroot.trans (by simpa [q] using hAMGM)
  have hn_pos : 0 < (n : ℝ) := hn
  have hmul := (le_div_iff₀ hn_pos).mp hroot_trace
  calc
    (n : ℝ) * Real.exp (-K / (n : ℝ)) = Real.exp (-K / (n : ℝ)) * n := by ring
    _ ≤ relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x) := hmul

private theorem c2_relTrace_perturb_eq_dimension_add_laplacian
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    relTrace (ω₀ x) ((ω₀.perturb φ hφ) x) = (n : ℝ) + ω₀.laplacian φ x := by
  rw [ω₀.perturb_apply hφ x, relTrace_add, relTrace_self (ω₀.isPositive x)]
  rfl

private theorem c2_logTrace_smooth_of_laplacian_log_smooth
    (ω₀ : KahlerForm n M) (A : ℝ) {G φ : M → ℝ} (hsol : ω₀.SolvesMongeAmpere G φ)
    (hlog : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ Real.log ((n : ℝ) + ω₀.laplacian φ x))) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ Real.log (relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x)) - A * φ x) := by
  have hlogTrace : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ Real.log (relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x))) := by
    convert hlog using 1
    funext x
    rw [c2_relTrace_perturb_eq_dimension_add_laplacian ω₀ hsol.1 x]
  exact hlogTrace.sub (contMDiff_const.mul hsol.1.1)

private theorem c2_log_dimension_add_laplacian_smooth [NeZero n]
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ Real.log ((n : ℝ) + ω₀.laplacian φ x)) := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let f : M → ℝ := fun x ↦ (n : ℝ) + ω₀.laplacian φ x
  have hf : ContMDiff I 𝓘(ℝ) ∞ f := by
    have hconst : ContMDiff I 𝓘(ℝ) ∞ (fun _ : M ↦ (n : ℝ)) := contMDiff_const
    have hlap : ContMDiff I 𝓘(ℝ) ∞ (ω₀.laplacian φ) := by
      simpa [I] using ω₀.contMDiff_laplacian hφ.1
    convert hconst.add hlap using 1
    ext x
    rfl
  have hf_pos (x : M) : 0 < f x := by
    dsimp [f]
    rw [← c2_relTrace_perturb_eq_dimension_add_laplacian ω₀ hφ x]
    exact relTrace_pos (ω₀.isPositive x) ((ω₀.perturb φ hφ).isPositive x)
  have hchart (x : M) :
      ContDiffOn ℝ ∞ (fun z ↦ Real.log (f ((extChartAt I x).symm z)))
        (extChartAt I x).target := by
    let e := extChartAt I x
    have hfOn : ContMDiffOn I 𝓘(ℝ) ∞ f Set.univ := contMDiffOn_univ.mpr hf
    have hfChart : ContMDiffOn I 𝓘(ℝ) ∞ (fun z ↦ f (e.symm z)) e.target := by
      exact hfOn.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
    have hfChart' : ContDiffOn ℝ ∞ (fun z ↦ f (e.symm z)) e.target := hfChart.contDiffOn
    have hfMaps : Set.MapsTo (fun z ↦ f (e.symm z)) e.target {0}ᶜ := by
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (hf_pos (e.symm z)).ne'
    have hlog := ContDiffOn.comp Real.contDiffOn_log hfChart' hfMaps
    change ContDiffOn ℝ ∞ (Real.log ∘ fun z ↦ f (e.symm z)) e.target
    exact hlog
  rw [contMDiff_iff]
  refine ⟨?_, ?_⟩
  · apply continuous_iff_continuousAt.2
    intro x
    let e := extChartAt I x
    let g := fun z ↦ Real.log (f (e.symm z))
    have hg : ContDiffAt ℝ ∞ g (e x) :=
      (hchart x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    have hgcomp : ContinuousAt (fun p ↦ g (e p)) x :=
      hg.continuousAt.comp
        (contMDiffAt_extChartAt (I := I) (n := ∞) (x := x)).continuousAt
    have hEq : (fun p ↦ g (e p)) =ᶠ[nhds x] (fun p ↦ Real.log (f p)) := by
      filter_upwards [(isOpen_extChartAt_source (I := I) x).mem_nhds
        (mem_extChartAt_source (I := I) x)] with p hp
      dsimp [g]
      rw [e.left_inv hp]
    exact hgcomp.congr_of_eventuallyEq hEq.symm
  · intro x y
    simp only [mfld_simps, chartAt_self_eq]
    have hI : (I.symm : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)) = id := by rfl
    have hx := hchart x
    simp only [mfld_simps] at hx
    rw [hI] at hx
    change ContDiffOn ℝ ∞
      (fun z ↦ Real.log (f ((chartAt (EuclideanSpace ℂ (Fin n)) x).symm z)))
      (chartAt (EuclideanSpace ℂ (Fin n)) x).target
    simpa [f, Function.comp_apply, ModelWithCorners.range_eq_univ] using hx

private theorem c2_logTrace_is_smooth [NeZero n]
    (ω₀ : KahlerForm n M) (A : ℝ) {G φ : M → ℝ}
    (hsol : ω₀.SolvesMongeAmpere G φ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ Real.log (relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x)) - A * φ x) := by
  exact c2_logTrace_smooth_of_laplacian_log_smooth ω₀ A hsol
    (c2_log_dimension_add_laplacian_smooth ω₀ hsol.1)

variable [CompactSpace M] in
private theorem c2_chernLu_pointwise_input [NeZero n]
    (ω₀ : KahlerForm n M) (K : ℝ) (_hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ G φ : M → ℝ,
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G →
        (∀ x, |G x| ≤ K) → (∀ x, -K ≤ ω₀.laplacian G x) →
      (∀ x y, φ x - φ y ≤ K) → (hsol : ω₀.SolvesMongeAmpere G φ) →
        ∀ x,
          (ω₀.perturb φ hsol.1).laplacian
            (fun y ↦ Real.log (relTrace (ω₀ y) ((ω₀.perturb φ hsol.1) y)) - A * φ y) x ≥
              relTrace ((ω₀.perturb φ hsol.1) x) (ω₀ x) - A * (n : ℝ) -
                K / relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x) := by
  obtain ⟨B, hB, hCL⟩ := laplacian_log_relTrace_ge_chernLu ω₀
  obtain ⟨C, hC, hRicciBound⟩ := exists_abs_relTrace_ricciForm_le ω₀
  let A : ℝ := B + C / (n : ℝ) ^ 2 + 1
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hn2 : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨A, hA, ?_⟩
  intro G φ hG hGbound hΔ hosc hsol x
  let ω₁ : KahlerForm n M := ω₀.perturb φ hsol.1
  let u : M → ℝ := fun y ↦ relTrace (ω₀ y) (ω₁ y)
  let v : M → ℝ := fun y ↦ relTrace (ω₁ y) (ω₀ y)
  let s : M → ℝ := fun y ↦ relTrace (ω₀ y) (ω₀.ricciForm y)
  have hu : 0 < u x := relTrace_pos (ω₀.isPositive x) (ω₁.isPositive x)
  have huv : (n : ℝ) ^ 2 ≤ u x * v x := by
    exact ContinuousAlternatingMap.sq_le_relTrace_mul_relTrace
      (ω₀.isPositive x) (ω₁.isPositive x)
  have hs : s x ≤ C := by
    exact (abs_le.mp (hRicciBound x)).2
  have hdG : -K ≤ ω₀.laplacian G x := hΔ x
  have hricci :
      relTrace (ω₀ x) (ω₁.ricciForm x) = s x - ω₀.laplacian G x := by
    dsimp [ω₁, s]
    exact ricciForm_trace_perturb_eq_of_solvesMongeAmpere ω₀ hsol x
  have hlog :
      ω₁.laplacian (fun y ↦ Real.log (u y)) x ≥
        (ω₀.laplacian G x - s x) / u x - B * v x := by
    have h := hCL ω₁ x
    rw [hricci] at h
    have h' : ω₁.laplacian
        (fun y ↦ Real.log (relTrace (ω₀ y) (ω₁ y))) x ≥
          (ω₀.laplacian G x - s x) / relTrace (ω₀ x) (ω₁ x) -
            B * relTrace (ω₁ x) (ω₀ x) := by
      convert h using 1 ; ring
    simpa [u, v] using h'
  have habsorb := c2_absorb_reference_scalar_term
    (u x) (v x) (s x) C B K (ω₀.laplacian G x)
    (ω₁.laplacian (fun y ↦ Real.log (u y)) x)
    hn hu hC huv hs hdG hlog
  have hlogSmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun y ↦ Real.log (u y)) := by
    simpa [u, ω₁] using c2_logTrace_is_smooth ω₀ 0 hsol
  have hφSmooth := hsol.1.1
  have hlapφ : ω₁.laplacian φ x = (n : ℝ) - v x := by
    change relTrace (ω₁ x) (mddbar n φ x) = _
    have hform : mddbar n φ x = (ω₁ x) - ω₀ x := by
      dsimp [ω₁]
      abel
    rw [hform]
    simp [v, ContinuousAlternatingMap.relTrace_sub,
      ContinuousAlternatingMap.relTrace_self (ω₁.isPositive x)]
  have hlinear :
      ω₁.laplacian
          (fun y ↦ Real.log (u y) - A * φ y) x =
        ω₁.laplacian (fun y ↦ Real.log (u y)) x - A * ω₁.laplacian φ x := by
    let f : M → ℝ := fun y ↦ Real.log (u y)
    let g : M → ℝ := fun y ↦ -A * φ y
    have hfun : (fun y ↦ Real.log (u y) - A * φ y) = f + g := by
      funext y
      change Real.log (u y) - A * φ y = Real.log (u y) + (-A * φ y)
      ring
    have hscale : g = (-A) • φ := by
      funext y
      dsimp [g]
    calc
      ω₁.laplacian (fun y ↦ Real.log (u y) - A * φ y) x =
          ω₁.laplacian f x + ω₁.laplacian g x := by
        rw [hfun]
        exact congrFun
          (ω₁.laplacian_add hlogSmooth (contMDiff_const.mul hφSmooth)) x
      _ = ω₁.laplacian f x + (-A) * ω₁.laplacian φ x := by
        rw [hscale, ω₁.laplacian_smul hφSmooth (-A)]
        simp [smul_eq_mul]
      _ = ω₁.laplacian (fun y ↦ Real.log (u y)) x - A * ω₁.laplacian φ x := by
        dsimp [f]
        ring
  change ω₁.laplacian (fun y ↦ Real.log (u y) - A * φ y) x ≥
    v x - A * (n : ℝ) - K / u x
  rw [hlinear, hlapφ]
  calc
    ω₁.laplacian (fun y ↦ Real.log (u y)) x - A * ((n : ℝ) - v x) ≥
        (-K / u x - (B + C / (n : ℝ) ^ 2) * v x) - A * ((n : ℝ) - v x) :=
      sub_le_sub_right habsorb (A * ((n : ℝ) - v x))
    _ = v x - A * (n : ℝ) - K / u x := by
      dsimp [A]
      ring
section

variable [T2Space M] [CompactSpace M]


omit [T2Space M] in
private theorem c2_logTrace_estimate_inputs [NeZero n]
    (ω₀ : KahlerForm n M) (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ G φ : M → ℝ,
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G →
        (∀ x, |G x| ≤ K) → (∀ x, -K ≤ ω₀.laplacian G x) →
        (∀ x y, φ x - φ y ≤ K) → (hsol : ω₀.SolvesMongeAmpere G φ) →
        (ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
          (fun x ↦ Real.log (relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x)) - A * φ x) ∧
          (∀ x,
            (ω₀.perturb φ hsol.1).laplacian
              (fun y ↦ Real.log (relTrace (ω₀ y)
                ((ω₀.perturb φ hsol.1) y)) - A * φ y) x ≥
                  relTrace ((ω₀.perturb φ hsol.1) x) (ω₀ x) -
                    A * (n : ℝ) - K / relTrace (ω₀ x)
                      ((ω₀.perturb φ hsol.1) x))) := by
  obtain ⟨A, hA, hCL⟩ := c2_chernLu_pointwise_input ω₀ K hK
  refine ⟨A, hA, ?_⟩
  intro G φ hG hGbound hΔ hosc hsol
  exact ⟨c2_logTrace_is_smooth ω₀ A hsol,
    hCL G φ hG hGbound hΔ hosc hsol⟩

omit [T2Space M] in
/-- **The Aubin–Yau `C²` estimate.** Uniform equivalence of `ω₀ + i∂∂̄φ` with `ω₀`, in terms of
`(M, ω₀)`, `sup |G|`, `inf Δ_ω₀ G` and `osc φ`. -/
theorem exists_relTrace_le_of_solvesMongeAmpere (ω₀ : KahlerForm n M) (K : ℝ) :
    ∃ C : ℝ, ∀ G φ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G →
      (∀ x, |G x| ≤ K) → (∀ x, -K ≤ ω₀.laplacian G x) → (∀ x y, φ x - φ y ≤ K) →
      ω₀.SolvesMongeAmpere G φ →
      ∀ x, relTrace (ω₀ x) (ω₀ x + mddbar n φ x) ≤ C ∧
        relTrace (ω₀ x + mddbar n φ x) (ω₀ x) ≤ C := by
  by_cases hn : n = 0
  · subst n
    refine ⟨0, ?_⟩
    intro G φ hG hGbound hΔ hosc hsol x
    constructor <;> simp [ContinuousAlternatingMap.relTrace, Matrix.trace]
  · by_cases hn : n = 1
    · subst n
      refine ⟨Real.exp K, ?_⟩
      intro G φ hG hGbound hΔ hosc hsol x
      have hω : (ω₀ x).IsPositive := ω₀.isPositive x
      have hα : (ω₀ x + mddbar 1 φ x).IsPositive := hsol.1.2 x
      have hdet : relDet (ω₀ x) (ω₀ x + mddbar 1 φ x) = Real.exp (G x) := by
        simpa [mongeAmpere] using hsol.2 x
      have hmul :
          relDet (ω₀ x) (ω₀ x + mddbar 1 φ x) *
              relDet (ω₀ x + mddbar 1 φ x) (ω₀ x) = relDet (ω₀ x) (ω₀ x) :=
        relDet_mul_relDet hω hα
      rw [relDet_self hω] at hmul
      have hrevpos : 0 < relDet (ω₀ x + mddbar 1 φ x) (ω₀ x) :=
        relDet_pos hα hω
      have hrevne : relDet (ω₀ x + mddbar 1 φ x) (ω₀ x) ≠ 0 := hrevpos.ne'
      have htraceForward : relTrace (ω₀ x) (ω₀ x + mddbar 1 φ x) ≤
          relTrace (ω₀ x + mddbar 1 φ x) (ω₀ x) ^ (1 - 1) /
            relDet (ω₀ x + mddbar 1 φ x) (ω₀ x) := by
        exact relTrace_le_relTrace_pow_div_relDet hα hω
      have htraceReverse : relTrace (ω₀ x + mddbar 1 φ x) (ω₀ x) ≤
          relTrace (ω₀ x) (ω₀ x + mddbar 1 φ x) ^ (1 - 1) /
            relDet (ω₀ x) (ω₀ x + mddbar 1 φ x) := by
        exact relTrace_le_relTrace_pow_div_relDet hω hα
      have hGupper : G x ≤ K := le_trans (le_abs_self _) (hGbound x)
      have hGlower : -G x ≤ K := by
        simpa using neg_le_neg (abs_le.mp (hGbound x)).1
      have hboundForward : relTrace (ω₀ x) (ω₀ x + mddbar 1 φ x) ≤ Real.exp K := by
        have htrace : relTrace (ω₀ x) (ω₀ x + mddbar 1 φ x) ≤
            1 / relDet (ω₀ x + mddbar 1 φ x) (ω₀ x) := by
          simpa using htraceForward
        calc
          relTrace (ω₀ x) (ω₀ x + mddbar 1 φ x) ≤
              1 / relDet (ω₀ x + mddbar 1 φ x) (ω₀ x) := htrace
          _ = relDet (ω₀ x) (ω₀ x + mddbar 1 φ x) := by
            rw [← hmul]
            field_simp [hrevne]
          _ = Real.exp (G x) := hdet
          _ ≤ Real.exp K := Real.exp_le_exp.mpr hGupper
      have hboundReverse : relTrace (ω₀ x + mddbar 1 φ x) (ω₀ x) ≤ Real.exp K := by
        have htrace : relTrace (ω₀ x + mddbar 1 φ x) (ω₀ x) ≤
            1 / relDet (ω₀ x) (ω₀ x + mddbar 1 φ x) := by
          simpa using htraceReverse
        calc
          relTrace (ω₀ x + mddbar 1 φ x) (ω₀ x) ≤
              1 / relDet (ω₀ x) (ω₀ x + mddbar 1 φ x) := htrace
          _ = Real.exp (-G x) := by rw [hdet, one_div, ← Real.exp_neg]
          _ ≤ Real.exp K := Real.exp_le_exp.mpr hGlower
      exact ⟨hboundForward, hboundReverse⟩
    · by_cases hK : K = 0
      · refine ⟨(n : ℝ), ?_⟩
        intro G φ hG hGbound hΔ hosc hsol
        by_cases hm : Nonempty M
        · obtain ⟨x₀⟩ := hm
          have hosc0 : ∀ x y, φ x - φ y ≤ 0 := by
            intro x y
            simpa [hK] using hosc x y
          have hφconst : φ = fun _ => φ x₀ := by
            funext y
            have h₁ := hosc0 y x₀
            have h₂ := hosc0 x₀ y
            linarith
          have hmddbar : mddbar n φ = 0 := by
            rw [hφconst, mddbar_const]
          have hform (x : M) : ω₀ x + mddbar n φ x = ω₀ x := by
            rw [hmddbar]
            simp
          intro x
          rw [hform x]
          constructor <;> rw [relTrace_self (ω₀.isPositive x)]
        · intro x
          exact (hm ⟨x⟩).elim
      · by_cases hKneg : K < 0
        · refine ⟨0, ?_⟩
          intro G φ hG hGbound hΔ hosc hsol x
          have hKnonneg : 0 ≤ K := (abs_nonneg (G x)).trans (hGbound x)
          linarith
        · have hKnonneg : 0 ≤ K := le_of_not_gt hKneg
          have hn0 : n ≠ 0 := by omega
          let : NeZero n := ⟨hn0⟩
          obtain ⟨A, hA, hinputs⟩ := c2_logTrace_estimate_inputs ω₀ K hKnonneg
          let δ : ℝ := (n : ℝ) * Real.exp (-K / (n : ℝ))
          have hδ : 0 < δ := by dsimp [δ]; positivity
          refine ⟨c2TraceBoundConstant n K A δ, ?_⟩
          intro G φ hG hGbound hΔ hosc hsol
          obtain ⟨hF, hCL⟩ := hinputs G φ hG hGbound hΔ hosc hsol
          have htraceLower : ∀ x, δ ≤ relTrace (ω₀ x) ((ω₀.perturb φ hsol.1) x) := by
            intro x
            simpa [δ] using c2_trace_lower_bound_of_mongeAmpere ω₀ K hGbound hsol x
          exact c2_trace_bounds_of_chernLu ω₀ K A δ hGbound hosc hsol hKnonneg hA hδ
            htraceLower hF hCL

end

end KahlerForm
