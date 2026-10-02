module

public import CalabiYau.MongeAmpere.Continuity.Basic
public import CalabiYau.Geometry.Kahler.Poisson
public import CalabiYau.Geometry.Complex.Schauder
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity
import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap

/-!
# Openness of the continuity set

If the continuity path `(ω₀ + i∂∂̄φₜ)ⁿ = e^{tF + cₜ} ω₀ⁿ` has a smooth solution at `t₀ ∈ [0, 1]`,
it has smooth solutions for all `t ∈ [0, 1]` close to `t₀`.

The analytic inputs are taken as explicit hypotheses: solvability of the Poisson equation for
every Kähler form (`KahlerForm.PoissonSolvable`) and the interior Schauder estimate
(`InteriorSchauderEstimate`).

## Proof sketch (Yau 1978, §6; Székelyhidi, *An Introduction to Extremal Kähler Metrics*,
Lemma 3.3 and §3.4; Aubin, §7.3)

Fix `α ∈ (0, 1)` and let `ω₁ = ω₀ + i∂∂̄φ_{t₀}`. On the Banach spaces
`X = {u ∈ C^{2,α}(M) : ∫ u ω₁ⁿ = 0}` and `Y = {f ∈ C^{0,α}(M) : ∫ f ω₁ⁿ = 0}` (built from
`HolderBoundOn` in a finite atlas; completeness by Arzelà–Ascoli), consider
`Φ(u, t) = log MA_{ω₁}(u) - (t - t₀) F - (c_t - c_{t₀})`, adjusted by a constant so that it takes
values in functions with `∫ e^{…} ω₁ⁿ = ∫ ω₁ⁿ`. It is `C¹` near `(0, t₀)` with
`D_u Φ(0, t₀) = Δ_{ω₁}` (`hasDerivAt_log_mongeAmpere`, `mongeAmpere_add`). `Δ_{ω₁} : X → Y` is
injective (`eq_add_const_of_laplacian_eq`), surjective (Poisson solvability for smooth data,
global Schauder estimates from `InteriorSchauderEstimate` and approximation) and bounded below
(Schauder); Mathlib's implicit function theorem (`ImplicitFunctionData`,
`HasStrictFDerivAt.implicitFunction`) gives `u(t) ∈ X` for `t` near `t₀`, and `φ_{t₀} + u(t)`
solves the path at `t` in `C^{2,α}`. The computations with `C^{2,α}` functions use the `C²`
versions `chartRep_mddbar_of_contMDiff_two`, `mddbar_add_of_contMDiff_two`,
`mongeAmpere_eq_inChart_of_contMDiff_two`, `hasDerivAt_log_mongeAmpere_of_contMDiff_two`.

Smoothness of `u(t)` does **not** come from `Estimates/Higher` (which assumes smooth solutions)
but from the regularity half of `InteriorSchauderEstimate`, by a difference-quotient bootstrap:
in a chart, for `v = φ_{t₀} + u(t)` and a real direction `e`, the difference quotient
`D_h v = (v(· + h e) - v)/h` satisfies `L_{A_h}(D_h v) = D_h (G + log det g) - (terms in D_h g)`
with `A_h = ∫₀¹ (g + v_{jk̄} + s h D_h v_{jk̄})⁻¹ ds` (up to transposition), uniformly elliptic and
`C^{k,α}`-bounded uniformly in `h`; Schauder bounds `D_h v` in `C^{k+2,α}` uniformly in `h`, so
`v ∈ C^{k+3}`; induct on `k`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

private theorem exists_nearby_zero_of_banach_ift
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (L : X ≃L[ℝ] Y) (B : ℝ →L[ℝ] Y) (R : X × ℝ → Y) (t₀ : ℝ)
    (hR : HasStrictFDerivAt R
      (L.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ X ℝ) +
        B.comp (ContinuousLinearMap.snd ℝ X ℝ)) (0, t₀))
    (hR0 : R (0, t₀) = 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε > 0, ∀ s ∈ Metric.ball t₀ ε,
      ∃ x : X, ‖x‖ < ρ ∧ R (x, s) = 0 := by
  let leftDeriv : (X × ℝ) →L[ℝ] Y :=
    L.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ X ℝ) +
      B.comp (ContinuousLinearMap.snd ℝ X ℝ)
  let rightDeriv : (X × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ X ℝ
  let data : ImplicitFunctionData ℝ (X × ℝ) Y ℝ := {
    leftFun := R
    leftDeriv := leftDeriv
    rightFun := Prod.snd
    rightDeriv := rightDeriv
    pt := (0, t₀)
    hasStrictFDerivAt_leftFun := hR
    hasStrictFDerivAt_rightFun := hasStrictFDerivAt_snd
    range_leftDeriv := by
      apply LinearMap.range_eq_top.2
      intro y
      refine ⟨(L.symm y, 0), ?_⟩
      simp [leftDeriv]
    range_rightDeriv := by
      apply LinearMap.range_eq_top.2
      intro t
      exact ⟨(0, t), by simp [rightDeriv]⟩
    isCompl_ker := by
      constructor
      · rw [disjoint_iff_inf_le]
        intro p hp
        have hp' : p ∈ leftDeriv.ker ∧ p ∈ rightDeriv.ker := by simpa using hp
        rcases hp' with ⟨hpL, hpR⟩
        change leftDeriv p = 0 at hpL
        change rightDeriv p = 0 at hpR
        have ht : p.2 = 0 := by simpa [rightDeriv] using hpR
        have hx : p.1 = 0 := by
          apply L.injective
          have hLp : L p.1 + B p.2 = 0 := by
            simpa [leftDeriv, ContinuousLinearMap.comp_apply] using hpL
          simpa [ht] using hLp
        rcases p with ⟨x, t⟩
        simp_all
      · rw [codisjoint_iff_le_sup]
        intro p _
        rw [Submodule.mem_sup']
        refine ⟨⟨(-L.symm (B p.2), p.2), ?_⟩,
          ⟨(p.1 + L.symm (B p.2), 0), ?_⟩, ?_⟩
        · change leftDeriv (-L.symm (B p.2), p.2) = 0
          simp [leftDeriv, ContinuousLinearMap.comp_apply]
        · change rightDeriv (p.1 + L.symm (B p.2), 0) = 0
          simp [rightDeriv]
        · ext <;> simp
  }
  have hbase : data.prodFun data.pt = (0, t₀) := by
    rw [data.prodFun_apply]
    simp [data, hR0]
  have hparameter : Filter.Tendsto (fun s : ℝ ↦ ((0 : Y), s)) (𝓝 t₀)
      (𝓝 (data.prodFun data.pt)) := by
    rw [hbase]
    exact (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ ↦ (0 : Y)) (𝓝 t₀) (𝓝 (0 : Y))).prodMk_nhds
      (Filter.tendsto_id : Filter.Tendsto (fun s : ℝ ↦ s) (𝓝 t₀) (𝓝 t₀))
  have hbranch : ∀ᶠ s in 𝓝 t₀,
      data.prodFun (data.implicitFunction 0 s) = (0, s) :=
    hparameter.eventually data.prodFun_implicitFunction
  have hmapPt : data.toOpenPartialHomeomorph data.pt = (0, t₀) := by
    simpa only [data.toOpenPartialHomeomorph_coe] using hbase
  have htarget : (0, t₀) ∈ data.toOpenPartialHomeomorph.target := by
    simpa only [hmapPt] using
      data.toOpenPartialHomeomorph.map_source data.pt_mem_toOpenPartialHomeomorph_source
  have hsymm : ContinuousAt data.toOpenPartialHomeomorph.symm (0, t₀) :=
    data.toOpenPartialHomeomorph.continuousAt_symm htarget
  have hparameter' : Filter.Tendsto (fun s : ℝ ↦ ((0 : Y), s)) (𝓝 t₀)
      (𝓝 (0, t₀)) := by simpa only [hbase] using hparameter
  have hsymmpt : data.toOpenPartialHomeomorph.symm (0, t₀) = data.pt := by
    rw [← hmapPt]
    exact data.toOpenPartialHomeomorph.left_inv data.pt_mem_toOpenPartialHomeomorph_source
  have hlimit' : Filter.Tendsto
      (fun s : ℝ ↦ data.toOpenPartialHomeomorph.symm (0, s)) (𝓝 t₀) (𝓝 data.pt) := by
    rw [← hsymmpt]
    exact hsymm.tendsto.comp hparameter'
  have hfun : (fun s : ℝ ↦ data.implicitFunction 0 s) =
      fun s ↦ data.toOpenPartialHomeomorph.symm (0, s) := by
    funext s
    exact data.implicitFunction_apply
  have hpt : data.pt = (0, t₀) := rfl
  have hlimit : Filter.Tendsto (fun s : ℝ ↦ data.implicitFunction 0 s) (𝓝 t₀)
      (𝓝 (0, t₀)) := by
    simpa only [hfun, hpt] using hlimit'
  have hsmall : ∀ᶠ s in 𝓝 t₀, ‖(data.implicitFunction 0 s).1‖ < ρ := by
    have hfst : Filter.Tendsto (fun s : ℝ ↦ (data.implicitFunction 0 s).1) (𝓝 t₀)
        (𝓝 (0 : X)) := by
      exact continuous_fst.continuousAt.tendsto.comp hlimit
    have hball : Metric.ball (0 : X) ρ ∈ 𝓝 (0 : X) := Metric.ball_mem_nhds _ hρ
    filter_upwards [hfst.eventually hball] with s hs
    simpa [Metric.mem_ball, dist_zero_right] using hs
  have hlocal : ∀ᶠ s in 𝓝 t₀,
      ∃ x : X, ‖x‖ < ρ ∧ R (x, s) = 0 := by
    filter_upwards [hbranch, hsmall] with s hs hnorm
    rw [data.prodFun_apply] at hs
    have hsleft : data.leftFun (data.implicitFunction 0 s) = 0 := congrArg Prod.fst hs
    have hsright : data.rightFun (data.implicitFunction 0 s) = s := congrArg Prod.snd hs
    let q := data.implicitFunction (0 : Y) s
    have hqleft : R q = 0 := by
      change data.leftFun q = 0 at hsleft
      exact hsleft
    have hqright : q.2 = s := by
      change data.rightFun q = s at hsright
      exact hsright
    refine ⟨q.1, hnorm, ?_⟩
    rw [← hqright]
    exact hqleft
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  exact ⟨ε, hε, fun s hs ↦ hball hs⟩
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [ConnectedSpace M] in
private theorem exists_linearized_mongeAmpere_direction [Nonempty M]
    (hPoisson : ∀ ω₁ : KahlerForm n M, ω₁.PoissonSolvable) (ω₀ : KahlerForm n M)
    {F : M → ℝ} (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (φ : M → ℝ) (hφ : ω₀.IsPotential φ) :
    ∃ ψ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ ∧
      ∀ x, HasDerivAt (fun s : ℝ ↦ Real.log (ω₀.mongeAmpere (φ + s • ψ) x))
        (F x - (∫ y, F y ∂(ω₀.perturb φ hφ).volume) /
          (ω₀.perturb φ hφ).volume.real univ) 0 := by
  let ω₁ := ω₀.perturb φ hφ
  let m := (∫ y, F y ∂ω₁.volume) / ω₁.volume.real univ
  have hvol : 0 < ω₁.volume.real univ := by
    have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₁.volume := by
      simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : M ↦ (1 : ℝ)) ω₁.volume)
    have h := integral_exp_pos (μ := ω₁.volume) (f := fun _ : M ↦ (0 : ℝ)) hint
    simpa using h
  have hFint : Integrable F ω₁.volume :=
    hF.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hmsmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ F x - m) := by
    exact hF.sub contMDiff_const
  have hmzero : ∫ x, (F x - m) ∂ω₁.volume = 0 := by
    rw [integral_sub hFint (integrable_const m)]
    simp only [integral_const]
    dsimp [m]
    field_simp [ne_of_gt hvol]
    ring
  obtain ⟨ψ, hψ, hψlap⟩ := hPoisson ω₁ (fun x ↦ F x - m) hmsmooth hmzero
  refine ⟨ψ, hψ, ?_⟩
  intro x
  have hderiv := ω₀.hasDerivAt_log_mongeAmpere hφ hψ x
  rw [show (ω₀.perturb φ hφ).laplacian ψ = ω₁.laplacian ψ from rfl, hψlap] at hderiv
  simpa [m, ω₁] using hderiv

omit [ConnectedSpace M] in
private theorem hasDerivAt_integral_exp_mul [Nonempty M]
    (ω₀ : KahlerForm n M) {F : M → ℝ}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∫ x, Real.exp (s * F x) ∂ω₀.volume)
      (∫ x, F x * Real.exp (t * F x) ∂ω₀.volume) t := by
  have hFc : Continuous F := hF.continuous
  have hFcOn : ContinuousOn F (Set.univ : Set M) := hFc.continuousOn
  obtain ⟨C, hC⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_bound_of_continuousOn hFcOn
  have hCnonneg : 0 ≤ C := by
    obtain ⟨x₀⟩ := ‹Nonempty M›
    exact (norm_nonneg (F x₀)).trans (hC x₀ (Set.mem_univ x₀))
  let K : ℝ := C + 1
  have hKnonneg : 0 ≤ K := by dsimp [K]; linarith
  have hFnorm : ∀ x, ‖F x‖ ≤ K := by
    intro x
    exact (hC x (Set.mem_univ x)).trans (by dsimp [K]; linarith)
  have hFabs : ∀ x, |F x| ≤ K := fun x ↦ by
    simpa [Real.norm_eq_abs] using hFnorm x
  let B : ℝ := K * Real.exp ((|t| + 1) * K)
  have hBound : ∀ x s, s ∈ Metric.ball t 1 →
      ‖F x * Real.exp (s * F x)‖ ≤ B := by
    intro x s hs
    have hst : |s - t| < 1 := by
      simpa [Real.dist_eq] using Metric.mem_ball.mp hs
    have hsabs : |s| ≤ |t| + 1 := by
      have hst' := abs_lt.mp hst
      rw [abs_le]
      constructor <;> linarith [hst'.1, hst'.2, neg_abs_le t, le_abs_self t]
    have harg : s * F x ≤ (|t| + 1) * K := by
      calc
        s * F x ≤ |s * F x| := le_abs_self _
        _ = |s| * |F x| := abs_mul _ _
        _ ≤ (|t| + 1) * K :=
          mul_le_mul hsabs (hFabs x) (abs_nonneg _) (by positivity)
    calc
      ‖F x * Real.exp (s * F x)‖ = ‖F x‖ * Real.exp (s * F x) := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (s * F x))]
      _ ≤ K * Real.exp (s * F x) :=
        mul_le_mul_of_nonneg_right (hFnorm x) (Real.exp_nonneg _)
      _ ≤ B := by
        dsimp [B]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) hKnonneg
  have hmeas : ∀ᶠ s in 𝓝 t,
      AEStronglyMeasurable (fun x : M ↦ Real.exp (s * F x)) ω₀.volume := by
    filter_upwards [] with s
    exact (Real.continuous_exp.comp (continuous_const.mul hFc)).aestronglyMeasurable
  have hint : Integrable (fun x : M ↦ Real.exp (t * F x)) ω₀.volume := by
    apply (Real.continuous_exp.comp (continuous_const.mul hFc)).integrable_of_hasCompactSupport
    exact HasCompactSupport.of_compactSpace _
  have hprime_meas : AEStronglyMeasurable
      (fun x : M ↦ F x * Real.exp (t * F x)) ω₀.volume := by
    apply (hFc.mul (Real.continuous_exp.comp (continuous_const.mul hFc))).aestronglyMeasurable
  have hdiff : ∀ᵐ x ∂ω₀.volume, ∀ s ∈ Metric.ball t 1,
      HasDerivAt (fun r : ℝ ↦ Real.exp (r * F x))
        (F x * Real.exp (s * F x)) s := by
    filter_upwards [] with x s hs
    simpa [Real.exp_eq_exp_ℝ, smul_eq_mul] using
      (hasDerivAt_exp_smul_const' (x := F x) s)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (s : ℝ) (x : M) ↦ Real.exp (s * F x)) (x₀ := t) (s := Metric.ball t 1)
    (hs := Metric.ball_mem_nhds t (by norm_num)) (hF_meas := hmeas) (hF_int := hint)
    (F' := fun (s : ℝ) (x : M) ↦ F x * Real.exp (s * F x)) (hF'_meas := hprime_meas)
    (h_bound := Filter.Eventually.of_forall fun x ↦ hBound x)
    (bound_integrable := integrable_const B) (h_diff := hdiff)
  simpa using hmain.2

omit [ConnectedSpace M] in
private theorem hasDerivAt_pathConstant [Nonempty M]
    (ω₀ : KahlerForm n M) {F : M → ℝ}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F) (t : ℝ) :
    letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
    HasDerivAt (fun s : ℝ ↦ ω₀.pathConstant F s)
      (-(∫ x, F x * Real.exp (t * F x) ∂ω₀.volume) /
        (∫ x, Real.exp (t * F x) ∂ω₀.volume)) t := by
  let : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  let : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  have hFc : Continuous F := hF.continuous
  have hvol : 0 < ω₀.volume.real univ := by
    have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₀.volume := by
      simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : M ↦ (1 : ℝ)) ω₀.volume)
    simpa using integral_exp_pos (μ := ω₀.volume) (f := fun _ : M ↦ (0 : ℝ)) hint
  have hIpos (s : ℝ) : 0 < ∫ x, Real.exp (s * F x) ∂ω₀.volume := by
    apply integral_exp_pos
    exact (Real.continuous_exp.comp (continuous_const.mul hFc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun : (fun s : ℝ ↦ ω₀.pathConstant F s) =
      fun s ↦ Real.log (ω₀.volume.real univ) -
        Real.log (∫ x, Real.exp (s * F x) ∂ω₀.volume) := by
    funext s
    simp only [pathConstant]
    exact Real.log_div (ne_of_gt hvol) (ne_of_gt (hIpos s))
  have hI := hasDerivAt_integral_exp_mul ω₀ hF t
  have hlogI := hI.log (ne_of_gt (hIpos t))
  have hconst : HasDerivAt (fun _ : ℝ ↦ Real.log (ω₀.volume.real univ)) 0 t :=
    hasDerivAt_const t _
  rw [hfun]
  have hsub := (hconst.sub hlogI).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s : ℝ ↦ rfl)
  convert hsub using 1
  · funext s
    rfl
  · rw [div_eq_mul_inv]
    ring

omit [ConnectedSpace M] in
private theorem hasDerivAt_pathExponent [Nonempty M]
    (ω₀ : KahlerForm n M) {F : M → ℝ}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (x : M) :
    letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
    HasDerivAt (fun s : ℝ ↦ s * F x + ω₀.pathConstant F s)
      (F x - (∫ y, F y * Real.exp (t * F y + ω₀.pathConstant F t) ∂ω₀.volume) /
        ω₀.volume.real univ) t := by
  let : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  let : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  have hFc : Continuous F := hF.continuous
  have hIpos : 0 < ∫ y, Real.exp (t * F y) ∂ω₀.volume := by
    apply integral_exp_pos
    exact (Real.continuous_exp.comp (continuous_const.mul hFc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlinear : HasDerivAt (fun s : ℝ ↦ s * F x) (F x) t := by
    simpa using (hasDerivAt_id t).mul_const (F x)
  have hconstant := hasDerivAt_pathConstant ω₀ hF t
  have hbare : HasDerivAt (fun s : ℝ ↦ s * F x + ω₀.pathConstant F s)
      (F x - (∫ y, F y * Real.exp (t * F y) ∂ω₀.volume) /
        (∫ y, Real.exp (t * F y) ∂ω₀.volume)) t := by
    convert hlinear.add hconstant using 1
    · rfl
    · ring
  have hmass := ω₀.integral_exp_path hF t
  have hmassFactor :
      (∫ y, Real.exp (t * F y) ∂ω₀.volume) * Real.exp (ω₀.pathConstant F t) =
        ω₀.volume.real univ := by
    calc
      _ = ∫ y, Real.exp (t * F y) * Real.exp (ω₀.pathConstant F t) ∂ω₀.volume := by
        rw [integral_mul_const]
      _ = ∫ y, Real.exp (t * F y + ω₀.pathConstant F t) ∂ω₀.volume := by
        congr 1
        funext y
        rw [← Real.exp_add]
      _ = ω₀.volume.real univ := hmass
  have hnum :
      (∫ y, F y * Real.exp (t * F y + ω₀.pathConstant F t) ∂ω₀.volume) =
        (∫ y, F y * Real.exp (t * F y) ∂ω₀.volume) *
          Real.exp (ω₀.pathConstant F t) := by
    have hexp (y : M) : Real.exp (t * F y + ω₀.pathConstant F t) =
        Real.exp (t * F y) * Real.exp (ω₀.pathConstant F t) := Real.exp_add _ _
    calc
      ∫ y, F y * Real.exp (t * F y + ω₀.pathConstant F t) ∂ω₀.volume =
          ∫ y, F y * (Real.exp (t * F y) * Real.exp (ω₀.pathConstant F t)) ∂ω₀.volume := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [hexp]
      _ = ∫ y, (F y * Real.exp (t * F y)) * Real.exp (ω₀.pathConstant F t) ∂ω₀.volume := by
        congr 1
        funext y
        ring
      _ = (∫ y, F y * Real.exp (t * F y) ∂ω₀.volume) *
          Real.exp (ω₀.pathConstant F t) := by
        rw [integral_mul_const]
  have hratio :
      (∫ y, F y * Real.exp (t * F y + ω₀.pathConstant F t) ∂ω₀.volume) /
          ω₀.volume.real univ =
        (∫ y, F y * Real.exp (t * F y) ∂ω₀.volume) /
          (∫ y, Real.exp (t * F y) ∂ω₀.volume) := by
    calc
      _ = ((∫ y, F y * Real.exp (t * F y) ∂ω₀.volume) *
          Real.exp (ω₀.pathConstant F t)) /
          ((∫ y, Real.exp (t * F y) ∂ω₀.volume) *
            Real.exp (ω₀.pathConstant F t)) := by
        rw [hnum, hmassFactor]
      _ = _ := mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos (ω₀.pathConstant F t)))
  convert hbare using 1
  · rw [hratio]

omit [ConnectedSpace M] in
private theorem integral_eq_integral_exp_mul_of_solvesMongeAmpere
    (ω₀ : KahlerForm n M) {G φ F : M → ℝ}
    (hsol : ω₀.SolvesMongeAmpere G φ) (hG : Continuous G) :
    ∫ x, F x ∂(ω₀.perturb φ hsol.1).volume =
      ∫ x, F x * Real.exp (G x) ∂ω₀.volume := by
  have hden : (fun x ↦ ENNReal.ofReal (ω₀.mongeAmpere φ x)) =
      fun x ↦ ENNReal.ofReal (Real.exp (G x)) := by
    funext x
    rw [hsol.2 x]
  have hmeas : Measurable (fun x ↦ ENNReal.ofReal (Real.exp (G x))) := by
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hG).measurable
  rw [ω₀.volume_perturb hsol.1, hden,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos (G x)))]
  simp [smul_eq_mul, mul_comm]

omit [ConnectedSpace M] in
private theorem average_F_perturb_eq_weighted_path_average [Nonempty M]
    (ω₀ : KahlerForm n M) {F : M → ℝ}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F) (t : ℝ)
    (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere
      (fun x ↦ t * F x + ω₀.pathConstant F t) φ) :
    (∫ x, F x ∂(ω₀.perturb φ hsol.1).volume) /
        (ω₀.perturb φ hsol.1).volume.real univ =
      (∫ x, F x * Real.exp (t * F x + ω₀.pathConstant F t) ∂ω₀.volume) /
        ω₀.volume.real univ := by
  let G : M → ℝ := fun x ↦ t * F x + ω₀.pathConstant F t
  have hG : Continuous G := by
    exact (continuous_const.mul hF.continuous).add continuous_const
  have hnum : ∫ x, F x ∂(ω₀.perturb φ hsol.1).volume =
      ∫ x, F x * Real.exp (G x) ∂ω₀.volume :=
    integral_eq_integral_exp_mul_of_solvesMongeAmpere ω₀ hsol hG
  have hmass : (ω₀.perturb φ hsol.1).volume.real univ =
      ∫ x, Real.exp (G x) ∂ω₀.volume := by
    calc
      (ω₀.perturb φ hsol.1).volume.real univ =
          ∫ x, (1 : ℝ) ∂(ω₀.perturb φ hsol.1).volume := by simp
      _ = ∫ x, (1 : ℝ) * Real.exp (G x) ∂ω₀.volume :=
        integral_eq_integral_exp_mul_of_solvesMongeAmpere ω₀ hsol hG
      _ = ∫ x, Real.exp (G x) ∂ω₀.volume := by simp
  change (∫ x, F x ∂(ω₀.perturb φ hsol.1).volume) /
      (ω₀.perturb φ hsol.1).volume.real univ =
    (∫ x, F x * Real.exp (G x) ∂ω₀.volume) / ω₀.volume.real univ
  rw [hnum, hmass]
  rw [ω₀.integral_exp_path hF t]

omit [ConnectedSpace M] in
private theorem exists_tangent_direction_for_path_solution [Nonempty M]
    (hPoisson : ∀ ω₁ : KahlerForm n M, ω₁.PoissonSolvable) (ω₀ : KahlerForm n M)
    {F : M → ℝ} (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere
      (fun x ↦ t * F x + ω₀.pathConstant F t) φ) :
    ∃ ψ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ ∧
      ∀ x, HasDerivAt (fun s : ℝ ↦ Real.log (ω₀.mongeAmpere (φ + s • ψ) x))
        (F x - (∫ y, F y * Real.exp (t * F y + ω₀.pathConstant F t) ∂ω₀.volume) /
          ω₀.volume.real univ) 0 := by
  obtain ⟨ψ, hψ, hdir⟩ :=
    exists_linearized_mongeAmpere_direction hPoisson ω₀ hF φ hsol.1
  have havg := average_F_perturb_eq_weighted_path_average ω₀ hF t φ hsol
  refine ⟨ψ, hψ, ?_⟩
  intro x
  simpa only [havg] using hdir x

omit [ConnectedSpace M] in
private theorem exists_path_residual_direction [Nonempty M]
    (hPoisson : ∀ ω₁ : KahlerForm n M, ω₁.PoissonSolvable) (ω₀ : KahlerForm n M)
    {F : M → ℝ} (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere
      (fun x ↦ t * F x + ω₀.pathConstant F t) φ) :
    letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
    ∃ ψ : M → ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ ∧
      ∀ x, HasDerivAt (fun s : ℝ ↦
        Real.log (ω₀.mongeAmpere (φ + (s - t) • ψ) x) -
          (s * F x + ω₀.pathConstant F s)) 0 t := by
  let : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  let : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  obtain ⟨ψ, hψ, hdir⟩ :=
    exists_tangent_direction_for_path_solution hPoisson ω₀ hF t φ hsol
  refine ⟨ψ, hψ, ?_⟩
  intro x
  have hdirAt : HasDerivAt (fun s : ℝ ↦ Real.log (ω₀.mongeAmpere (φ + s • ψ) x))
      (F x - (∫ y, F y * Real.exp (t * F y + ω₀.pathConstant F t) ∂ω₀.volume) /
        ω₀.volume.real univ) (t - t) := by
    simpa using hdir x
  have hdirection := hdirAt.comp_sub_const t t
  have hpath := hasDerivAt_pathExponent ω₀ hF t x
  have hres := hdirection.sub hpath
  convert hres using 1
  · funext s
    rfl
  · ring

private theorem exists_path_solution_on_ball [Nonempty M]
    (hSch : InteriorSchauderEstimate n)
    (hPoisson : ∀ ω₁ : KahlerForm n M, ω₁.PoissonSolvable) (ω₀ : KahlerForm n M)
    {F : M → ℝ} (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    {t : ℝ} (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere
      (fun x ↦ t * F x + ω₀.pathConstant F t) φ) :
    ∃ ε > 0, ∀ s ∈ Metric.ball t ε,
      ∃ ψ, ω₀.SolvesMongeAmpere (fun x ↦ s * F x + ω₀.pathConstant F s) ψ := by
  let α : ℝ≥0 := 1 / 2
  have hα₀ : 0 < α := by norm_num [α]
  have hα₁ : α < 1 := by norm_num [α]
  let ω₁ := ω₀.perturb φ hsol.1
  obtain ⟨cover⟩ := exists_compactChartCover
    (E := EuclideanSpace ℂ (Fin n)) (M := M)
  obtain ⟨N2⟩ := exists_smoothChartHolderNormedData cover 2 α hα₀ hα₁
  obtain ⟨N0⟩ := exists_smoothChartHolderNormedData cover 0 α hα₀ hα₁
  let P : ContinuityHolderPair ω₁ α := ⟨cover, N2, N0⟩
  let : ContinuityHolderPair ω₁ α := P
  have hvol : 0 < ω₁.volume.real Set.univ := by
    have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₁.volume := by
      simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : M ↦ (1 : ℝ)) ω₁.volume)
    simpa using integral_exp_pos (μ := ω₁.volume) (f := fun _ : M ↦ (0 : ℝ)) hint
  have hSmoothDense := closure_smoothMeanZeroChartHolderCore_coe
    ω₁ cover 0 α hα₀ hα₁ P.normedDataC0 hvol
  obtain ⟨L, hL⟩ := exists_laplacian_equiv ω₁ α hα₀ hα₁ hSch (hPoisson ω₁) hSmoothDense
  obtain ⟨D⟩ := exists_centeredPathResidualData ω₀ F hF t φ hsol α hα₀ hα₁
  obtain ⟨b, _hb, T, hT, hD⟩ :=
    exists_centeredResidual_strictDerivative ω₀ F hF t φ hsol α hα₀ hα₁ D L hL
  let B : ℝ →L[ℝ] P.C0 := (1 : ℝ →L[ℝ] ℝ).smulRight b
  have hR : HasStrictFDerivAt D.residual
      (L.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ P.C2 ℝ) +
        B.comp (ContinuousLinearMap.snd ℝ P.C2 ℝ)) (0, 0) := by
    convert hD using 1
    apply ContinuousLinearMap.ext
    intro p
    rcases p with ⟨u, δ⟩
    simp [B, hT u δ]
  obtain ⟨ε, hε, hbranch⟩ := exists_nearby_zero_of_banach_ift
    L B D.residual 0 hR D.residual_base D.radius_pos
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have hδ : s - t ∈ Metric.ball (0 : ℝ) ε := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hs
  obtain ⟨u, huNorm, hu⟩ := hbranch (s - t) hδ
  let Q : ContinuityHolderPair ω₁ α := this
  obtain ⟨huHolder, huC2⟩ := D.residual_zero_solution u (s - t) huNorm hu
  have hEvalC2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
      (this.evalC2 u) := by
    have hreg := littleHolderOrderTwoEvaluation_contMDiff this.finiteChartCover α
      hα₀ hα₁ this.normedDataC2 u.1
    have heval : this.evalC2 u = littleHolderOrderTwoEvaluation
        this.finiteChartCover α this.normedDataC2 u.1 := by
      funext x
      rfl
    rw [heval]
    exact hreg
  have hφreg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ := by
    have hle : (↑(2 : ℕ∞) : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    exact hsol.1.1.of_le hle
  have hu' : ω₀.SolvesMongeAmpereC2
      (fun x ↦ s * F x + ω₀.pathConstant F s) (φ + this.evalC2 u) := by
    refine ⟨⟨hφreg.add hEvalC2, huC2.1.2⟩, ?_⟩
    simpa only [show t + (s - t) = s by ring] using huC2.2
  have hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
      (fun x ↦ s * F x + ω₀.pathConstant F s) := by
    convert (contMDiff_const.mul hF).add contMDiff_const using 1
    funext x
    rfl
  let ψ := φ + this.evalC2 u
  have hcover : ∀ i, ∃ C : ℝ≥0,
      HolderBoundOn 2 α C (Q.finiteChartCover.piece i)
        (ψ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
          (Q.finiteChartCover.base i)).symm) := by
    intro i
    obtain ⟨C, hC⟩ := huHolder (Q.finiteChartCover.base i)
      (Q.finiteChartCover.piece i) (Q.finiteChartCover.isCompact_piece i)
      (Q.finiteChartCover.piece_in_target i)
    exact ⟨C, hC ψ (by simp [ψ])⟩
  classical
  choose C hC using hcover
  let Cmax : ℝ≥0 := Finset.univ.sup C
  have hCmax : ∀ i, C i ≤ Cmax := by
    intro i
    exact Finset.le_sup (Finset.mem_univ i)
  have hchart : HolderBoundedOnChartCover Q.finiteChartCover 2 α ψ := by
    refine ⟨Cmax, ?_⟩
    intro i
    exact (hC i).mono_const (hCmax i)
  have hGauge : HasFiniteChartHolderGauge Q.finiteChartCover 2 α ψ :=
    (finiteChartHolderGauge_lt_top_iff Q.finiteChartCover 2 α ψ).2 hchart
  exact ⟨ψ,
    solvesMongeAmpere_of_c2 hSch ω₀ α hα₀ hα₁ hG hu' Q.finiteChartCover hGauge⟩

/-- **Openness.** The continuity set is a neighbourhood, within `[0, 1]`, of each of its points. -/
theorem continuitySet_mem_nhdsWithin (hSch : InteriorSchauderEstimate n)
    (hPoisson : ∀ ω₁ : KahlerForm n M, ω₁.PoissonSolvable) (ω₀ : KahlerForm n M) {F : M → ℝ}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F) {t : ℝ}
    (ht : t ∈ ω₀.continuitySet F) : ω₀.continuitySet F ∈ 𝓝[Icc 0 1] t := by
  classical
  by_cases hM : IsEmpty M
  · have hset : ω₀.continuitySet F = Icc (0 : ℝ) 1 := by
      ext s
      constructor
      · exact fun hs ↦ hs.1
      · intro hs
        refine ⟨hs, ?_⟩
        refine ⟨fun _ ↦ 0, ?_⟩
        refine ⟨⟨contMDiff_const, ?_⟩, ?_⟩
        · intro x
          exact False.elim (hM.false x)
        · intro x
          exact False.elim (hM.false x)
    rw [hset]
    exact self_mem_nhdsWithin
  · have : Nonempty M := not_isEmpty_iff.mp hM
    by_cases hFc : ∃ c : ℝ, ∀ x, F x = c
    · obtain ⟨c, hFc⟩ := hFc
      have hvol : 0 < ω₀.volume.real univ := by
        have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₀.volume := by
          simpa using (integrable_const (1 : ℝ) : Integrable (fun _ : M ↦ (1 : ℝ)) ω₀.volume)
        have h := integral_exp_pos (μ := ω₀.volume) (f := fun _ : M ↦ (0 : ℝ)) hint
        simpa using h
      have hpath : ∀ s : ℝ, ω₀.pathConstant F s = -s * c := by
        intro s
        have hI : ∫ x, Real.exp (s * F x) ∂ω₀.volume =
            Real.exp (s * c) * ω₀.volume.real univ := by
          calc
            ∫ x, Real.exp (s * F x) ∂ω₀.volume =
                ∫ x, Real.exp (s * c) ∂ω₀.volume := by
                  congr 1
                  funext x
                  rw [hFc x]
            _ = Real.exp (s * c) * ω₀.volume.real univ := by
              simp [integral_const, mul_comm]
        rw [pathConstant, hI]
        have hratio : ω₀.volume.real univ /
            (Real.exp (s * c) * ω₀.volume.real univ) = Real.exp (-(s * c)) := by
          field_simp [ne_of_gt hvol, ne_of_gt (Real.exp_pos (s * c))]
          rw [← Real.exp_add]
          simp
        rw [hratio, Real.log_exp]
        ring
      have hset : ω₀.continuitySet F = Icc (0 : ℝ) 1 := by
        ext s
        constructor
        · exact fun hs ↦ hs.1
        · intro hs
          refine ⟨hs, ?_⟩
          refine ⟨fun _ ↦ 0, ?_⟩
          refine ⟨ω₀.isPotential_zero, ?_⟩
          intro x
          change ω₀.mongeAmpere (fun _ : M ↦ (0 : ℝ)) x =
            Real.exp (s * F x + ω₀.pathConstant F s)
          rw [hFc x, hpath s]
          have hzero : s * c + (-s * c) = 0 := by ring
          rw [hzero, Real.exp_zero]
          exact congrFun ω₀.mongeAmpere_zero x
      rw [hset]
      exact self_mem_nhdsWithin
    · rcases ht.2 with ⟨φ, hsol⟩
      obtain ⟨ε, hε, hbranch⟩ := exists_path_solution_on_ball hSch hPoisson ω₀ hF φ hsol
      apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      refine ⟨Metric.ball t ε, Metric.ball_mem_nhds t hε, ?_⟩
      intro s hs
      rcases hs with ⟨hsball, hsIcc⟩
      exact ⟨hsIcc, hbranch s hsball⟩

end KahlerForm
