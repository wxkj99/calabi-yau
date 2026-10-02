module

public import CalabiYau.MongeAmpere.Continuity.Basic
public import CalabiYau.Geometry.Kahler.Poisson
public import CalabiYau.Analysis.Elliptic.Schauder
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
  obtain ⟨N2⟩ := exists_smoothChartHolderNormedData cover 2 α hα₁
  obtain ⟨N0⟩ := exists_smoothChartHolderNormedData cover 0 α hα₁
  let P : ContinuityHolderPair ω₁ α := ⟨cover, N2, N0⟩
  let : ContinuityHolderPair ω₁ α := P
  have hvol : 0 < ω₁.volume.real Set.univ := by
    have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₁.volume := by
      simp
    simp
  have hSmoothDense := closure_smoothMeanZeroChartHolderCore_coe
    ω₁ cover 0 α P.normedDataC0 hvol
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
          simp
        have h := integral_exp_pos (μ := ω₀.volume) (f := fun _ : M ↦ (0 : ℝ)) hint
        simp
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
