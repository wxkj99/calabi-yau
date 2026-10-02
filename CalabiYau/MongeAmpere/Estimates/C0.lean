module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Kahler.Sobolev
import CalabiYau.Geometry.Complex.Forms.Positive
import CalabiYau.Analysis.MoserIteration.Iteration
import CalabiYau.MongeAmpere.Estimates.C0.Softplus
import CalabiYau.MongeAmpere.Estimates.C0.CenteredMean
import CalabiYau.MongeAmpere.Estimates.C0.PoweredEnergy
import CalabiYau.MongeAmpere.Estimates.C0.PoweredOscillation
import CalabiYau.MongeAmpere.Estimates.C0.MoserLpIteration
import CalabiYau.MongeAmpere.Estimates.C0.SubsolutionIteration
import CalabiYau.MongeAmpere.Estimates.C0.SoftplusRecurrence
import CalabiYau.MongeAmpere.Estimates.C0.PathEnergy

/-!
# The `C⁰` estimate (Yau)

If `(ω₀ + i∂∂̄φ)ⁿ = e^G ω₀ⁿ` with `|G| ≤ K`, then the oscillation of `φ` is bounded by a constant
depending only on `(M, ω₀)` (through the Sobolev and Poincaré constants) and on `K`.

The dependence of the constant is encoded by the order of quantifiers: `C` is chosen after `ω₀`,
the Sobolev data `κ, C_S`, the Poincaré constant `C_P` and the bound `K`, and before `G` and `φ`.

Normalize `sup φ = -1` and use the segment energy identity for the powered-test recurrence.
For the centered potential `ψ = φ - average(φ)`, positivity gives `Δψ ≥ -n`. Moser iteration
on the smooth softplus of `ψ` bounds its essential supremum by its second moment. Softplus has
linear growth, while the `p = 1` energy estimate and Poincaré bound that moment in terms of the
mean of `-φ`; the resulting scalar inequality controls the mean. A separate powered iteration
from the full Monge–Ampère equation bounds `-φ` pointwise and gives the oscillation estimate.
-/

@[expose] public section

open scoped Manifold ContDiff Interval ComplexOrder MatrixOrder
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M]

private theorem laplacian_energy_le_mean_of_solvesMongeAmpere
    (ω₀ : KahlerForm n M) {G φ : M → ℝ} (hsol : ω₀.SolvesMongeAmpere G φ)
    (K : ℝ) (hG : ∀ x, |G x| ≤ K)
    (hn : 1 ≤ n) (hφnorm : ∀ x, 1 ≤ -φ x) :
    ∫ x, ω₀.gradNormSq φ x ∂ω₀.volume ≤
      (2 : ℝ) ^ n * (Real.exp K - 1) * ∫ x, -φ x ∂ω₀.volume := by
  let F : ℝ → ℝ := fun t => (1 / 2 : ℝ) * t ^ 2
  have hF : ContDiff ℝ ∞ F := by
    change ContDiff ℝ ∞ (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2)
    fun_prop
  have hF' : deriv F = fun t => t := by
    funext t
    change deriv (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) t = t
    rw [deriv_const_mul_field]
    have hpow : deriv (fun t : ℝ => t ^ 2) t = 2 * t := by
      change deriv ((fun t : ℝ => t) ^ 2) t = 2 * t
      rw [deriv_pow differentiableAt_id 2]
      norm_num
    rw [hpow]
    ring
  have hF'' : deriv (deriv F) = fun _ => 1 := by
    rw [hF']
    funext t
    simp
  have henergy := normalized_mongeAmpere_energy_bound ω₀ hsol.1 hn hF (by
    intro x
    rw [hF'']
    norm_num)
  have hWcont : Continuous (fun x => -φ x) := continuous_neg.comp hsol.1.1.continuous
  have hMAcont : Continuous (ω₀.mongeAmpere φ) :=
    (ω₀.contMDiff_mongeAmpere hsol.1.1).continuous
  have hI₁ : Integrable (fun x => (-φ x) * (ω₀.mongeAmpere φ x - 1)) ω₀.volume :=
    integrable_of_continuous_volume ω₀ (hWcont.mul (hMAcont.sub continuous_const))
  have hI₂ : Integrable (fun x => (-φ x) * (Real.exp K - 1)) ω₀.volume :=
    integrable_of_continuous_volume ω₀ (hWcont.mul continuous_const)
  have hMAle : ∀ x, ω₀.mongeAmpere φ x - 1 ≤ Real.exp K - 1 := by
    intro x
    have hGx : G x ≤ K := (le_abs_self _).trans (hG x)
    rw [hsol.2 x]
    exact sub_le_sub_right (Real.exp_le_exp.mpr hGx) 1
  have hpt : ∀ x, (-φ x) * (ω₀.mongeAmpere φ x - 1) ≤
      (-φ x) * (Real.exp K - 1) := by
    intro x
    exact mul_le_mul_of_nonneg_left (hMAle x) (by linarith [hφnorm x])
  have hmono := MeasureTheory.integral_mono_ae hI₁ hI₂
    (Filter.Eventually.of_forall hpt)
  have hupper : ∫ x, (-φ x) * (Real.exp K - 1) ∂ω₀.volume =
      (Real.exp K - 1) * ∫ x, -φ x ∂ω₀.volume := by
    calc
      ∫ x, (-φ x) * (Real.exp K - 1) ∂ω₀.volume =
          ∫ x, (Real.exp K - 1) * (-φ x) ∂ω₀.volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = (Real.exp K - 1) * ∫ x, -φ x ∂ω₀.volume := integral_const_mul _ _
  have hmono' : ∫ x, -φ x * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume ≤
      (Real.exp K - 1) * ∫ x, -φ x ∂ω₀.volume := by
    rw [hupper] at hmono
    simpa only [mul_assoc] using hmono
  have hpow : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left henergy (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  rw [← mul_assoc, hpow, one_mul] at hscaled
  have hmono'' := mul_le_mul_of_nonneg_left hmono'
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  have hmono''' : (2 : ℝ) ^ n *
      ∫ x, deriv F (-φ x) * (ω₀.mongeAmpere φ x - 1) ∂ω₀.volume ≤
      (2 : ℝ) ^ n * ((Real.exp K - 1) * ∫ x, -φ x ∂ω₀.volume) := by
    simpa [hF'] using hmono''
  simpa [hF'', mul_one, mul_assoc] using hscaled.trans hmono'''
variable [ConnectedSpace M] in

omit [ConnectedSpace M] in
private theorem poincare_variance_le_mean_of_solvesMongeAmpere
    (ω₀ : KahlerForm n M) {G φ : M → ℝ} (hsol : ω₀.SolvesMongeAmpere G φ)
    {C_P K : ℝ} (hP : ω₀.PoincareInequality C_P) (hG : ∀ x, |G x| ≤ K)
    (hn : 1 ≤ n) (hφnorm : ∀ x, 1 ≤ -φ x) :
    ∫ x, (φ x - ⨍ y, φ y ∂ω₀.volume) ^ 2 ∂ω₀.volume ≤
      (max C_P 0) * ((2 : ℝ) ^ n * (Real.exp K - 1)) *
        ∫ x, -φ x ∂ω₀.volume := by
  let C_P' : ℝ := max C_P 0
  have hP' : ω₀.PoincareInequality C_P' := hP.mono (le_max_left _ _)
  have hCp : 0 ≤ C_P' := by dsimp [C_P']; exact le_max_right _ _
  have henergy := laplacian_energy_le_mean_of_solvesMongeAmpere
    ω₀ hsol K hG hn hφnorm
  have hvariance := hP'.integral_sub_average_sq_le hsol.1.1
  calc
    _ ≤ C_P' * ∫ x, ω₀.gradNormSq φ x ∂ω₀.volume := hvariance
    _ ≤ C_P' * ((2 : ℝ) ^ n * (Real.exp K - 1) *
        ∫ x, -φ x ∂ω₀.volume) := mul_le_mul_of_nonneg_left henergy hCp
    _ = C_P' * ((2 : ℝ) ^ n * (Real.exp K - 1)) *
        ∫ x, -φ x ∂ω₀.volume := by ring

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
/-- A smooth MA solution is a subsolution by positivity of the perturbed form. -/
private theorem laplacian_lower_bound_of_solvesMongeAmpere
    (ω₀ : KahlerForm n M) {G φ : M → ℝ} (hsol : ω₀.SolvesMongeAmpere G φ) :
    ∀ x, -(n : ℝ) ≤ ω₀.laplacian φ x := by
  intro x
  have htrace := ContinuousAlternatingMap.relTrace_nonneg (ω₀.isPositive x)
    (hsol.1.2 x).isNonneg
  change 0 ≤ ContinuousAlternatingMap.relTrace (ω₀ x) (ω₀ x + mddbar n φ x) at htrace
  have htrace_eq : ContinuousAlternatingMap.relTrace (ω₀ x)
      (ω₀ x + mddbar n φ x) = (n : ℝ) + ω₀.laplacian φ x := by
    rw [ContinuousAlternatingMap.relTrace_add,
      ContinuousAlternatingMap.relTrace_self (ω₀.isPositive x)]
    simp [KahlerForm.laplacian]
  rw [htrace_eq] at htrace
  linarith

/-- A powered-test recurrence for a smooth subsolution softplus. -/
private theorem c0_centered_softplus_moment_recurrence
    (ω₀ : KahlerForm n M) {u : M → ℝ}
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    (hsub : ∀ x, -(n : ℝ) ≤ ω₀.laplacian u x)
    {κ C_S : ℝ} (hκ : 1 < κ) (hS : ω₀.SobolevInequality κ C_S) :
    ∀ k, eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ (k + 1)) ω₀.volume ≤
      c0MomentFactor n κ C_S k *
        eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ k) ω₀.volume := by
  exact c0_softplus_powered_recurrence ω₀ hu hsub hκ hS
section

variable [ConnectedSpace M]


private theorem c0_centered_softplus_product_bound
    {κ C_S : ℝ} (hκ : 1 < κ) :
    ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ N,
      (∏ k ∈ Finset.range N, c0MomentFactor n κ C_S k) ≤ B := by
  have hLsum := c0_moment_log_majorant_summable (n := n) (κ := κ) (C_S := C_S) hκ
  have hLnonneg (k : ℕ) : 0 ≤ c0MomentLogMajorant (n := n) κ C_S k :=
    c0MomentLogMajorant_nonneg (n := n) hκ k
  let S : ℝ := ∑' k, c0MomentLogMajorant (n := n) κ C_S k
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg hLnonneg
  refine ⟨ENNReal.ofReal (Real.exp S), (ENNReal.ofReal_lt_top).ne, ?_⟩
  intro N
  have hsumN : (∑ k ∈ Finset.range N, c0MomentLogMajorant (n := n) κ C_S k) ≤ S := by
    dsimp [S]
    exact hLsum.sum_le_tsum _ (fun k _ => hLnonneg k)
  let f : ℕ → ℝ := fun k =>
    (max C_S 1 * (1 + (n : ℝ) * (2 * κ ^ k) / 4)) ^ ((2 * κ ^ k)⁻¹)
  have hprodReal : (∏ k ∈ Finset.range N, f k) ≤ Real.exp S := by
    calc
      (∏ k ∈ Finset.range N, f k) ≤
          ∏ k ∈ Finset.range N, Real.exp (c0MomentLogMajorant (n := n) κ C_S k) := by
        apply Finset.prod_le_prod
        · intro k hk
          dsimp [f]
          positivity
        · intro k hk
          simpa [f] using c0_moment_factor_le_exp_logMajorant (n := n) hκ k
      _ = Real.exp (∑ k ∈ Finset.range N, c0MomentLogMajorant (n := n) κ C_S k) := by
        rw [← Real.exp_sum]
      _ ≤ Real.exp S := Real.exp_le_exp.mpr hsumN
  have hfnonneg : ∀ k ∈ Finset.range N, 0 ≤ f k := by
    intro k hk
    dsimp [f]
    positivity
  change (∏ k ∈ Finset.range N, ENNReal.ofReal (f k)) ≤ ENNReal.ofReal (Real.exp S)
  rw [← ENNReal.ofReal_prod_of_nonneg hfnonneg]
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg S)).2 hprodReal

omit [ConnectedSpace M] in
/-- Bound the softplus starting moment by Poincaré and the p=1 energy estimate. -/
private theorem c0_centered_softplus_second_moment_le
    (ω₀ : KahlerForm n M) {G φ : M → ℝ} (hsol : ω₀.SolvesMongeAmpere G φ)
    {C_P K : ℝ} (hP : ω₀.PoincareInequality C_P) (hG : ∀ x, |G x| ≤ K)
    (hn : 1 ≤ n) (hφnorm : ∀ x, 1 ≤ -φ x) :
    ∫ x, c0CenteredSoftplus (fun y => φ y - ⨍ z, φ z ∂ω₀.volume) x ^ 2 ∂ω₀.volume ≤
      (2 * (1 + Real.log 2) ^ 2 + 2) *
        (ω₀.volume.real Set.univ + (max C_P 0) *
          ((2 : ℝ) ^ n * (Real.exp K - 1)) * ∫ x, -φ x ∂ω₀.volume) := by
  let ψ : M → ℝ := fun x => φ x - ⨍ y, φ y ∂ω₀.volume
  have hψcont : Continuous ψ := hsol.1.1.continuous.sub continuous_const
  have hsoft := c0_softplus_integral_sq_le ω₀ hψcont
  have hvariance := poincare_variance_le_mean_of_solvesMongeAmpere ω₀ hsol hP hG hn hφnorm
  have hconst : 0 ≤ 2 * (1 + Real.log 2) ^ 2 + 2 := by positivity
  calc
    ∫ x, c0CenteredSoftplus ψ x ^ 2 ∂ω₀.volume ≤
        (2 * (1 + Real.log 2) ^ 2 + 2) *
          (ω₀.volume.real Set.univ + ∫ x, ψ x ^ 2 ∂ω₀.volume) := by
        simpa [c0CenteredSoftplus, ψ] using hsoft
    _ ≤ (2 * (1 + Real.log 2) ^ 2 + 2) *
          (ω₀.volume.real Set.univ + (max C_P 0) *
            ((2 : ℝ) ^ n * (Real.exp K - 1)) * ∫ x, -φ x ∂ω₀.volume) := by
        apply mul_le_mul_of_nonneg_left _ hconst
        linarith [hvariance]

/-- **Yau's `C⁰` estimate.** The oscillation of a solution of `(ω₀ + i∂∂̄φ)ⁿ = e^G ω₀ⁿ` is bounded
in terms of `(M, ω₀)` and `sup |G|`. -/
theorem exists_osc_le_of_solvesMongeAmpere (ω₀ : KahlerForm n M) {κ C_S C_P : ℝ} (hκ : 1 < κ)
    (hS : ω₀.SobolevInequality κ C_S) (hP : ω₀.PoincareInequality C_P) (K : ℝ) :
    ∃ C : ℝ, ∀ G φ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G →
      (∀ x, |G x| ≤ K) → ω₀.SolvesMongeAmpere G φ → ∀ x y, φ x - φ y ≤ C := by
  classical
  by_cases hM : IsEmpty M
  · refine ⟨0, ?_⟩
    intro G φ hG hbound hsol x y
    exact False.elim (hM.false x)
  · by_cases hK : K < 0
    · have hne : Nonempty M := not_isEmpty_iff.mp hM
      obtain ⟨z⟩ := hne
      refine ⟨0, ?_⟩
      intro G φ hG hbound hsol x y
      have hk : 0 ≤ K := (abs_nonneg (G z)).trans (hbound z)
      linarith
    · by_cases hn : n = 0
      · subst n
        let : Unique (EuclideanSpace ℂ (Fin 0)) := inferInstance
        let : DiscreteTopology (EuclideanSpace ℂ (Fin 0)) := inferInstance
        let : DiscreteTopology M :=
          ChartedSpace.discreteTopology (H := EuclideanSpace ℂ (Fin 0)) M
        let : Subsingleton M := by
          refine ⟨fun x y => ?_⟩
          have hy : ({y} : Set M).Nonempty := ⟨y, rfl⟩
          have hxy : ({y} : Set M) = Set.univ :=
            IsClopen.eq_univ (isClopen_discrete _) hy
          apply Set.mem_singleton_iff.mp
          rw [hxy]
          exact Set.mem_univ x
        refine ⟨0, ?_⟩
        intro G φ hG hbound hsol x y
        have hxy : x = y := Subsingleton.elim _ _
        subst y
        simp
      · by_cases hK0 : K = 0
        · let : NeZero n := ⟨hn⟩
          refine ⟨0, ?_⟩
          intro G φ hG hbound hsol x y
          have hG0 : ∀ z, G z = 0 := by
            intro z
            have hgz : |G z| ≤ 0 := by simpa [hK0] using hbound z
            exact abs_eq_zero.mp (le_antisymm hgz (abs_nonneg _))
          have hma : ∀ z, ω₀.mongeAmpere φ z = 1 := by
            intro z
            rw [hsol.2 z, hG0 z]
            simp
          have hlap_nonneg : ∀ z, 0 ≤ ω₀.laplacian φ z := by
            intro z
            have hAM := ContinuousAlternatingMap.relDet_rpow_le_relTrace_div
              (ω₀.isPositive z) (hsol.1.2 z).isNonneg
            have hdet : ContinuousAlternatingMap.relDet (ω₀ z)
                (ω₀ z + mddbar n φ z) = 1 := by
              calc
                ContinuousAlternatingMap.relDet (ω₀ z) (ω₀ z + mddbar n φ z) =
                    ω₀.mongeAmpere φ z :=
                  (ω₀.mongeAmpere_eq_relDet_perturb hsol.1 z).symm
                _ = 1 := hma z
            have hAM' : 1 ≤ ContinuousAlternatingMap.relTrace (ω₀ z)
                (ω₀ z + mddbar n φ z) / n := by
              simpa [hdet] using hAM
            have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
            have htr : (n : ℝ) ≤ ContinuousAlternatingMap.relTrace (ω₀ z)
                (ω₀ z + mddbar n φ z) := by
              rcases (one_le_div_iff).mp hAM' with h | ⟨hneg, _⟩
              · exact h.2
              · exact False.elim (lt_asymm hneg hnpos)
            have htrace : ContinuousAlternatingMap.relTrace (ω₀ z)
                (ω₀ z + mddbar n φ z) =
                n + ω₀.laplacian φ z := by
              calc
                ContinuousAlternatingMap.relTrace (ω₀ z) (ω₀ z + mddbar n φ z) =
                    ContinuousAlternatingMap.relTrace (ω₀ z) (ω₀ z) +
                      ContinuousAlternatingMap.relTrace (ω₀ z) (mddbar n φ z) :=
                  ContinuousAlternatingMap.relTrace_add
                _ = n + ω₀.laplacian φ z := by
                  rw [ContinuousAlternatingMap.relTrace_self (ω₀.isPositive z)]
                  rfl
            rw [htrace] at htr
            linarith
          have hInt : ∫ z, ω₀.laplacian φ z ∂ω₀.volume = 0 :=
            ω₀.integral_laplacian hsol.1.1
          have hLapCont : Continuous (ω₀.laplacian φ) :=
            (ω₀.contMDiff_laplacian hsol.1.1).continuous
          have hLapInt : Integrable (ω₀.laplacian φ) ω₀.volume :=
            hLapCont.integrable_of_hasCompactSupport
              (HasCompactSupport.of_support_subset_isCompact isCompact_univ (Set.subset_univ _))
          have hLapZero : ω₀.laplacian φ = 0 := by
            funext z
            by_contra hne
            have hpos := MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
              hLapCont hLapInt hlap_nonneg hne
            rw [hInt] at hpos
            exact (lt_irrefl 0) hpos
          obtain ⟨c, hc⟩ := ω₀.eq_const_of_laplacian_eq_zero hsol.1.1 hLapZero
          rw [hc x, hc y]
          norm_num
        · have hKpos : 0 ≤ K := le_of_not_gt hK
          have hnle : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          obtain ⟨Bsoft, hBsoft, hprodsoft⟩ :=
            c0_centered_softplus_product_bound (n := n) (κ := κ) (C_S := C_S) hκ
          have hrecUniform : ∀ {u : M → ℝ},
              ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u →
              (∀ z, -(n : ℝ) ≤ ω₀.laplacian u z) →
              ∀ k, eLpNorm (c0CenteredSoftplus u)
                  (c0MomentExponent κ (k + 1)) ω₀.volume ≤
                c0MomentFactor n κ C_S k *
                  eLpNorm (c0CenteredSoftplus u) (c0MomentExponent κ k) ω₀.volume := by
            intro u hu hsub
            exact c0_centered_softplus_moment_recurrence ω₀ hu hsub hκ hS
          obtain ⟨L, hL⟩ := c0_normalized_potential_L2_bound
            (ω₀ := ω₀) hP hKpos hκ hBsoft hprodsoft hrecUniform
          obtain ⟨A, hA, henergy⟩ := c0_mongeAmpere_powered_energy ω₀ hKpos hnle
          have hL2uniform : ∀ G' φ' : M → ℝ,
              ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G' →
              (∀ z, |G' z| ≤ K) → ω₀.SolvesMongeAmpere G' φ' →
              (∃ z₀, φ' z₀ = -1) → (∀ z, 1 ≤ -φ' z) →
              ∫ z, (-φ' z) ^ 2 ∂ω₀.volume ≤ L := by
            intro G' φ' hG' hbound' hsol' hmin' hφnorm'
            exact hL G' φ' hG' hbound' hsol' hnle hmin' hφnorm'
          obtain ⟨C, hosc⟩ := c0_oscillation_from_powered_data
            (ω₀ := ω₀) (K := K) hκ hS hA hKpos hL2uniform henergy
          refine ⟨C, ?_⟩
          intro G φ hG hbound hsol x y
          exact hosc G φ hG hbound hsol x y

end

end KahlerForm
