module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.Basic
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.SmoothOutputs
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.ChartMatrixControl
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.PositiveLimitTail
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.GaugeCauchy
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder.PointwiseLimit

/-!
# Log-determinant residual in the little-Hölder completion

Realize the uncentered logarithmic Monge–Ampère difference as a function in the actual fixed-cover
little-`C^{0,α}` completion.  Positivity on the ball is an input; the neighboring-ball radius is
chosen using `exists_c2Potential_radius`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- An uncentered residual represented in the full little-Hölder completion on a positive ball. -/
structure LittleHolderUncenteredResidualData (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (radius : ℝ) where
  uncentered : P.C2 × ℝ → LittleHolder P.finiteChartCover 0 α P.normedDataC0
  eval_uncentered : ∀ (u : P.C2) (δ : ℝ), ‖u‖ < radius → ∀ x,
    smoothChartHolderContinuousMapExtension P.finiteChartCover 0 α P.normedDataC0
      (uncentered (u, δ)) x =
        uncenteredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ x
  uncentered_base : uncentered (0, 0) = 0

/-- The smooth order-two core is dense in its fixed-cover completion, hence every element of the
C² carrier admits smooth-core approximants in the actual `C^{2,α}` norm. -/
private theorem exists_smoothCore_C2_approximation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α] (u : P.C2) :
    ∃ v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α,
      Filter.Tendsto (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2))
        Filter.atTop (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) := by
  let : NormedAddCommGroup (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 2 α P.normedDataC2
  let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 2 α P.normedDataC2
  have hdense : Dense (Set.range fun f : SmoothChartHolderCore P.finiteChartCover 2 α =>
      (f : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) :=
    UniformSpace.Completion.denseRange_coe
  have huclose : (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) ∈
      closure (Set.range fun f : SmoothChartHolderCore P.finiteChartCover 2 α =>
        (f : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) := hdense _
  have hclose := Metric.mem_closure_range_iff_nat.mp huclose
  let v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α := fun j =>
    Classical.choose (hclose j)
  have hv (j : ℕ) : dist (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)
      (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) < 1 / ((j : ℝ) + 1) :=
    Classical.choose_spec (hclose j)
  refine ⟨v, Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_comm]
  calc
    dist (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)
        (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) <
        1 / ((j : ℝ) + 1) := hv j
    _ ≤ 1 / ((N : ℝ) + 1) := by
      gcongr
    _ < ε := by
      have hN' : 1 < (N : ℝ) * ε := by
        have hh := hN
        rw [div_lt_iff₀ hε] at hh
        exact hh
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith

/-- A convergent order-two completion sequence has uniformly convergent canonical second jets on
each compact chart piece. This packages the operator-valued part of the positivity-tail argument. -/
private theorem smoothCore_approximation_secondJet_tendstoUniformly
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α] (u : P.C2)
    (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hv : Filter.Tendsto
      (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2))
      Filter.atTop (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)))
    (i : P.finiteChartCover.ι) :
    TendstoUniformly
      (fun j z => smoothChartHolderJetCanonicalExtension P.finiteChartCover 2 α
        P.normedDataC2 2 (by norm_num)
        (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) i z)
      (fun z => smoothChartHolderJetCanonicalExtension P.finiteChartCover 2 α
        P.normedDataC2 2 (by norm_num)
        (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) i z)
      Filter.atTop := by
  let : NormedAddCommGroup (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 2 α P.normedDataC2
  let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 2 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 2 α P.normedDataC2
  let J := smoothChartHolderJetCanonicalExtension P.finiteChartCover 2 α
    P.normedDataC2 2 (by norm_num)
  have hJ : Filter.Tendsto
      (fun j => J (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2))
      Filter.atTop (𝓝 (J (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2))) :=
    (J.continuous.tendsto _).comp hv
  have hi := (continuous_apply i).tendsto _ |>.comp hJ
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mp hi

/-- The quadratic evaluation of a C²-positive form is continuous on one compact chart piece and
its unit-vector sphere. -/
private theorem c2Potential_chartQuadratic_continuousOn
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) {ψ : M → ℝ}
    (hψ : ω₀.IsC2Potential ψ) (x : M) {K : Set (EuclideanSpace ℂ (Fin n))}
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        ((ω₀.toFormField + mddbar n ψ).chartRep x p.1) ![p.2, Complex.I • p.2])
      (K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ)) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f := ψ ∘ e.symm
  let U := K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ)
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  have hcf : ContDiffOn ℝ 2 f e.target := by
    have h := (contMDiff_iff.mp hψ.1).2 x 0
    simpa [f, e, extChartAt, chartAt_self_eq] using h
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ f) e.target :=
    hcf.fderiv_of_isOpen hopen (by norm_num)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ f)) e.target :=
    hD1.continuousOn_fderiv_of_isOpen hopen (by norm_num)
  have hD2U : ContinuousOn (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
      fderiv ℝ (fderiv ℝ f) p.1) U := by
    apply hD2.comp continuous_fst.continuousOn
    intro p hp
    exact hKt hp.1
  have hfirstV : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => p.2) U :=
    continuous_snd.continuousOn
  have hJV : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) => Complex.I • p.2) U := by
    fun_prop
  have hJJV : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        Complex.I • (Complex.I • p.2)) U := by
    fun_prop
  have hterm₁ : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        fderiv ℝ (fderiv ℝ f) p.1 (Complex.I • p.2) (Complex.I • p.2)) U :=
    (hD2U.clm_apply hJV).clm_apply hJV
  have hterm₂ : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        fderiv ℝ (fderiv ℝ f) p.1 p.2 (Complex.I • (Complex.I • p.2))) U :=
    (hD2U.clm_apply hfirstV).clm_apply hJJV
  have hddbar : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        ddbar f p.1 ![p.2, Complex.I • p.2]) U := by
    have hcomb : ContinuousOn
        (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
          (fderiv ℝ (fderiv ℝ f) p.1 (Complex.I • p.2) (Complex.I • p.2) -
            fderiv ℝ (fderiv ℝ f) p.1 p.2 (Complex.I • (Complex.I • p.2))) / 2) U :=
      (hterm₁.sub hterm₂).div_const 2
    apply hcomb.congr
    intro p hp
    have hAt : ContDiffAt ℝ 2 f p.1 := hcf.contDiffAt (hopen.mem_nhds (hKt hp.1))
    simpa [Function.comp_def] using ddbar_apply hAt p.2 (Complex.I • p.2)
  have hωrep : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        ω₀.toFormField.chartRep x p.1) U := by
    apply (ω₀.isSmooth x).continuousOn.comp continuous_fst.continuousOn
    intro p hp
    exact hKt hp.1
  have hωtuple : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        ![p.2, Complex.I • p.2]) U := by
    fun_prop
  have hωpair : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        (ω₀.toFormField.chartRep x p.1, ![p.2, Complex.I • p.2])) U :=
    hωrep.prodMk hωtuple
  have hωeval : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        (ω₀.toFormField.chartRep x p.1) ![p.2, Complex.I • p.2]) U :=
    ContinuousEval.continuous_eval.continuousOn.comp hωpair (fun _ _ => Set.mem_univ _)
  have hrepr (p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n)) (hp : p ∈ U) :
      ((ω₀.toFormField + mddbar n ψ).chartRep x p.1) ![p.2, Complex.I • p.2] =
        (ω₀.toFormField.chartRep x p.1) ![p.2, Complex.I • p.2] +
          ddbar f p.1 ![p.2, Complex.I • p.2] := by
    change (ω₀.toFormField.chartRep x p.1 + (mddbar n ψ).chartRep x p.1)
        ![p.2, Complex.I • p.2] = _
    rw [ContinuousAlternatingMap.add_apply,
      chartRep_mddbar_of_contMDiff_two hψ.1 x (hKt hp.1)]
  exact (hωeval.add hddbar).congr (fun p hp => hrepr p hp)

/-- A chart representation is the value of a form at the represented point pulled back by the
complex-linear tangent-coordinate equivalence. -/
private theorem formField_chartRep_eq_comp_tangentEquiv
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (θ : FormField (EuclideanSpace ℂ (Fin n)) M 2) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n),
      θ.chartRep x z =
        (θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).compContinuousLinearMap
          (A.restrictScalars ℝ) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  have hyx : y ∈ e.source := e.map_target hz
  have hyyℝ : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyx
  have hyyℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyℝ
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v) ⟨⟨hyxℂ, hyyℂ⟩, hyxℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxℂ
  have hAB : ∀ v, A (B v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v) ⟨⟨hyyℂ, hyxℂ⟩, hyyℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyℂ
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toLinearEquiv :=
        { toFun := A
          invFun := B
          left_inv := hBA
          right_inv := hAB
          map_add' := A.map_add
          map_smul' := A.map_smul }
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
    tangentCoordChange_real_eq ⟨hyx, hyyℝ⟩
  have hchart : θ.chartRep x z =
      (θ y).compContinuousLinearMap (A.restrictScalars ℝ) := by
    calc
      θ.chartRep x z = (θ y).compContinuousLinearMap
          (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) := rfl
      _ = (θ y).compContinuousLinearMap (A.restrictScalars ℝ) := by rw [hAreal]
  have hARestrict : (AEquiv.restrictScalars ℝ :
      EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) = A.restrictScalars ℝ := by
    ext v
    rfl
  refine ⟨AEquiv, ?_⟩
  rw [hARestrict]
  simpa [e, y] using hchart

private theorem c2Potential_chartRep_isPositive
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (θ : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hθ : ∀ x, (θ x).IsPositive) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (θ.chartRep x z).IsPositive := by
  obtain ⟨A, hchart⟩ := formField_chartRep_eq_comp_tangentEquiv θ x hz
  rw [hchart]
  exact (hθ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
    |>.compContinuousLinearMap A

private theorem compact_continuous_positive_margin
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (q : X × Y → ℝ) (hq : Continuous q) (hpos : ∀ p, 0 < q p) :
    ∃ δ > 0, ∀ p, δ ≤ q p := by
  obtain ⟨p, hp, hpmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hq.continuousOn
  refine ⟨q p, hpos p, ?_⟩
  intro q'
  exact hpmin (Set.mem_univ q')

/-- A C²-positive potential has a uniform positive quadratic margin over the fixed chart pieces. -/
private theorem exists_c2Potential_uniform_chart_margin
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [Nonempty M]
    (ω₀ : KahlerForm n M) {ψ : M → ℝ} (hψ : ω₀.IsC2Potential ψ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (hn : 0 < n) :
    ∃ δ > 0, ∀ i z (_hz : z ∈ cover.piece i) v,
      δ * ‖v‖ ^ 2 ≤
        ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) z) ![v, Complex.I • v] := by
  classical
  let X := Σ i : cover.ι, cover.piece i
  let S := {v : EuclideanSpace ℂ (Fin n) // ‖v‖ = 1}
  let : ∀ i, CompactSpace (cover.piece i) := fun i =>
    isCompact_iff_compactSpace.mp (cover.isCompact_piece i)
  let : CompactSpace X := by dsimp [X]; infer_instance
  have hXne : Nonempty X := by
    obtain ⟨x⟩ := ‹Nonempty M›
    obtain ⟨i, z, hz, hzx⟩ := cover.interior_covers x
    exact ⟨⟨i, ⟨z, interior_subset hz⟩⟩⟩
  let : Nonempty X := hXne
  have hScompact : IsCompact {v : EuclideanSpace ℂ (Fin n) | ‖v‖ = 1} := by
    simpa [Metric.sphere] using
      (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ))
  let : CompactSpace S := isCompact_iff_compactSpace.mp hScompact
  have hSne : Nonempty S := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hn
    refine ⟨⟨EuclideanSpace.single i (1 : ℂ), ?_⟩⟩
    simp
  let : Nonempty S := hSne
  let qσ : (Σ i : cover.ι, cover.piece i × S) → ℝ := fun p =>
    ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base p.1) p.2.1.1)
      ![p.2.2.1, Complex.I • p.2.2.1]
  let e : X × S ≃ₜ (Σ i : cover.ι, cover.piece i × S) :=
    Homeomorph.sigmaProdDistrib (X := fun i : cover.ι => cover.piece i) (Y := S)
  let q : X × S → ℝ := fun p => qσ (e p)
  have hqσ : Continuous qσ := by
    apply continuous_sigma
    intro i
    let coordPair : cover.piece i × S →
        EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) :=
      fun p => (p.1.1, (show {w : EuclideanSpace ℂ (Fin n) // ‖w‖ = 1} from p.2).1)
    have hg : Continuous coordPair := by fun_prop
    have hcont := c2Potential_chartQuadratic_continuousOn ω₀ hψ (cover.base i)
      (cover.piece_in_target i)
    have hmaps : Set.MapsTo coordPair Set.univ
        (cover.piece i ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1) := by
      rintro ⟨⟨z, hz⟩, ⟨w, hw⟩⟩ hp
      refine ⟨hz, ?_⟩
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    have hcomp : ContinuousOn
        ((fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
          ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) p.1)
            ![p.2, Complex.I • p.2]) ∘ coordPair) Set.univ :=
      hcont.comp hg.continuousOn hmaps
    have hglobal : ContinuousOn (fun a : cover.piece i × S => qσ ⟨i, a⟩) Set.univ := by
      change ContinuousOn ((fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) p.1)
          ![p.2, Complex.I • p.2]) ∘ coordPair) Set.univ
      exact hcomp
    exact continuousOn_univ.mp hglobal
  have hq : Continuous q := hqσ.comp e.continuous
  have hq_eval (i : cover.ι) (z : cover.piece i) (w : S) :
      q ((⟨i, z⟩, w)) =
        ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) z.1)
          ![w.1, Complex.I • w.1] := by
    simp [q, qσ, e, Homeomorph.sigmaProdDistrib, Equiv.sigmaProdDistrib]
  have hqpos : ∀ p, 0 < q p := by
    rintro ⟨⟨i, z⟩, w⟩
    rw [hq_eval]
    have hchart := c2Potential_chartRep_isPositive
      (ω₀.toFormField + mddbar n ψ) hψ.2 (cover.base i)
      (cover.piece_in_target i z.2)
    have hwne : w.1 ≠ 0 := by
      intro hz
      have hnorm : ‖w.1‖ = 1 := w.2
      rw [hz] at hnorm
      norm_num at hnorm
    exact hchart.2 w.1 hwne
  obtain ⟨δ, hδ, hmin⟩ := compact_continuous_positive_margin q hq hqpos
  refine ⟨δ, hδ, ?_⟩
  intro i z hz v
  by_cases hv : v = 0
  · have hzero : ![(0 : EuclideanSpace ℂ (Fin n)),
        Complex.I • (0 : EuclideanSpace ℂ (Fin n))] = 0 := by
      funext k
      fin_cases k <;> simp
    rw [hv, hzero]
    simp
  · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : EuclideanSpace ℂ (Fin n) := ‖v‖⁻¹ • v
    have hwnorm : ‖w‖ = 1 := by
      dsimp [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm)]
      exact inv_mul_cancel₀ hvnorm.ne'
    have hunit := hmin ((⟨i, ⟨z, hz⟩⟩, ⟨w, hwnorm⟩))
    have hvw : v = ‖v‖ • w := by
      dsimp [w]
      rw [smul_smul, mul_inv_cancel₀ hvnorm.ne', one_smul]
    have hIv : Complex.I • v = ‖v‖ • (Complex.I • w) := by
      calc
        Complex.I • v = Complex.I • (‖v‖ • w) := congrArg (fun q => Complex.I • q) hvw
        _ = ‖v‖ • (Complex.I • w) := smul_comm Complex.I ‖v‖ w
    have htuple : ![v, Complex.I • v] =
        (fun k : Fin 2 => ‖v‖ • (![w, Complex.I • w] k)) := by
      funext k
      fin_cases k
      · exact hvw
      · exact hIv
    have hscale :
        ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) z)
          ![v, Complex.I • v] = ‖v‖ ^ 2 *
            q ((⟨i, ⟨z, hz⟩⟩, ⟨w, hwnorm⟩)) := by
      rw [hq_eval, htuple]
      have h := ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) z).map_smul_univ
        (fun _ : Fin 2 => ‖v‖) ![w, Complex.I • w]
      simpa [Fin.prod_univ_succ, pow_two, smul_eq_mul] using h
    calc
      δ * ‖v‖ ^ 2 = ‖v‖ ^ 2 * δ := by ring
      _ ≤ ‖v‖ ^ 2 * q ((⟨i, ⟨z, hz⟩⟩, ⟨w, hwnorm⟩)) :=
        mul_le_mul_of_nonneg_left hunit (sq_nonneg ‖v‖)
      _ = ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) z)
          ![v, Complex.I • v] := hscale.symm
/-- The actual chart derivatives of the completed evaluations converge uniformly on each chart
interior. This follows by identifying them with the canonical completed jets there. -/
private theorem smoothCore_approximation_secondDerivative_tendstoUniformlyOn
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α] (u : P.C2)
    (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hv : Filter.Tendsto
      (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) Filter.atTop
      (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)))
    (i : P.finiteChartCover.ι) :
    TendstoUniformlyOn
      (fun j z => iteratedFDeriv ℝ 2
        ((smoothChartHolderContinuousMapExtension P.finiteChartCover 2 α P.normedDataC2
          (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2) : M → ℝ) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm) z)
      (fun z => iteratedFDeriv ℝ 2
        ((smoothChartHolderContinuousMapExtension P.finiteChartCover 2 α P.normedDataC2
          (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) : M → ℝ) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm) z)
      Filter.atTop (interior (P.finiteChartCover.piece i)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hjet := smoothCore_approximation_secondJet_tendstoUniformly ω₁ α u v hv i
  rw [Metric.tendstoUniformly_iff] at hjet
  filter_upwards [hjet ε hε] with j hj
  intro z hz
  have h₁ := smoothChartHolderCompletedJetIdentity P.finiteChartCover α P.normedDataC2
    (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2)
    2 (by norm_num) i z hz
  have h₂ := smoothChartHolderCompletedJetIdentity P.finiteChartCover α P.normedDataC2
    (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)
    2 (by norm_num) i z hz
  rw [h₁, h₂]
  simpa [dist_comm] using hj ⟨z, interior_subset hz⟩

private theorem ddbar_lower_bound_of_secondJet
    {n : ℕ} (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (C : ℝ)
    (hjet : ‖iteratedFDeriv ℝ 2 f z‖ ≤ C) :
    ∀ v, -C * ‖v‖ ^ 2 ≤ ddbar f z ![v, Complex.I • v] := by
  have hbilinear (a b : EuclideanSpace ℂ (Fin n)) :
      |fderiv ℝ (fderiv ℝ f) z a b| ≤ C * ‖a‖ * ‖b‖ := by
    have heq : iteratedFDeriv ℝ 2 f z ![a, b] =
        fderiv ℝ (fderiv ℝ f) z a b := by
      simpa using (iteratedFDeriv_two_apply (𝕜 := ℝ) f z ![a, b])
    have h := ContinuousMultilinearMap.le_opNorm
      (iteratedFDeriv ℝ 2 f z) ![a, b]
    calc
      |fderiv ℝ (fderiv ℝ f) z a b| =
          ‖iteratedFDeriv ℝ 2 f z ![a, b]‖ := by rw [heq, Real.norm_eq_abs]
      _ ≤ ‖iteratedFDeriv ℝ 2 f z‖ * (‖a‖ * ‖b‖) := by simpa using h
      _ ≤ C * (‖a‖ * ‖b‖) :=
          mul_le_mul_of_nonneg_right hjet (mul_nonneg (norm_nonneg a) (norm_nonneg b))
      _ = C * ‖a‖ * ‖b‖ := by ring
  intro v
  rw [ddbar_apply hf v (Complex.I • v)]
  have hI : Complex.I • (Complex.I • v) = -v := by simp [smul_smul]
  have hfirst :
      -C * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) z (Complex.I • v) (Complex.I • v) := by
    have hb := hbilinear (Complex.I • v) (Complex.I • v)
    have hnorm : ‖Complex.I • v‖ = ‖v‖ := by
      calc
        ‖Complex.I • v‖ = ‖Complex.I‖ * ‖v‖ := norm_smul _ _
        _ = ‖v‖ := by norm_num
    rw [hnorm] at hb
    nlinarith [neg_le_of_abs_le hb]
  have hsecond :
      -C * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) z v v := by
    have hb := hbilinear v v
    nlinarith [neg_le_of_abs_le hb]
  rw [hI]
  simp only [ContinuousLinearMap.map_neg]
  nlinarith

private theorem positive_add_of_uniform_quadratic_bound
    {n : ℕ} (α β : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hα : α.IsPositive) (hβ : β.IsOneOne) (δ C : ℝ)
    (hC : C < δ)
    (hmargin : ∀ v, δ * ‖v‖ ^ 2 ≤ α ![v, Complex.I • v])
    (hperturb : ∀ v, -C * ‖v‖ ^ 2 ≤ β ![v, Complex.I • v]) :
    (α + β).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro v w
    simp only [ContinuousAlternatingMap.add_apply]
    rw [hα.1 v w, hβ v w]
  · intro v hv
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hnormsq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hvnorm
    have hbase := hmargin v
    have hpert := hperturb v
    have hsum : δ * ‖v‖ ^ 2 - C * ‖v‖ ^ 2 ≤
        (α + β) ![v, Complex.I • v] := by
      rw [ContinuousAlternatingMap.add_apply]
      linarith
    have hδC : 0 < δ - C := sub_pos.mpr hC
    have hfinal : 0 < (δ - C) * ‖v‖ ^ 2 := mul_pos hδC hnormsq
    nlinarith [hsum]

private theorem chartRep_positive_implies_pointwise
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (θ : FormField (EuclideanSpace ℂ (Fin n)) M 2) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hchart : (θ.chartRep x z).IsPositive) :
    (θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).IsPositive := by
  obtain ⟨A, hrep⟩ := formField_chartRep_eq_comp_tangentEquiv θ x hz
  rw [hrep] at hchart
  have hback := hchart.compContinuousLinearMap A.symm
  have hback_eq :
      ((θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).compContinuousLinearMap
        ((A.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) =
          θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) := by
    ext v
    apply congrArg (θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
    funext k
    simp []
  change (((θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).compContinuousLinearMap
      ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).compContinuousLinearMap
      ((A.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)).IsPositive at hback
  rw [hback_eq] at hback
  exact hback

private theorem chartRep_approximation_positive
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) {ψ : M → ℝ}
    (hψ : ω₀.IsC2Potential ψ) (approx : M → ℝ)
    (hApprox : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 approx)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ cover.piece i)
    (δ C : ℝ)
    (hmargin : ∀ v, δ * ‖v‖ ^ 2 ≤
      ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) z) ![v, Complex.I • v])
    (hCδ : C < δ)
    (hjet : ‖iteratedFDeriv ℝ 2
      (approx ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z‖ ≤ C) :
    ((ω₀.toFormField + mddbar n (ψ + approx)).chartRep (cover.base i) z).IsPositive := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  let f := approx ∘ e.symm
  have hψ2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ := hψ.1
  have hApproxChart : ContDiffOn ℝ 2 (approx ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hApprox).2 (cover.base i) 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hψChart : ContDiffOn ℝ 2 (ψ ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hψ2).2 (cover.base i) 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hf : ContDiffOn ℝ 2 f e.target := by
    simpa [f, Function.comp_def] using hApproxChart
  have hfAt : ContDiffAt ℝ 2 f z :=
    hf.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
      (cover.piece_in_target i hz))
  have hβone : (ddbar f z).IsOneOne := isOneOne_ddbar hfAt
  have hβlower : ∀ v, -C * ‖v‖ ^ 2 ≤ ddbar f z ![v, Complex.I • v] :=
    ddbar_lower_bound_of_secondJet f z hfAt C hjet
  have hαpos : ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) z).IsPositive :=
    c2Potential_chartRep_isPositive (ω₀.toFormField + mddbar n ψ) hψ.2
      (cover.base i) (cover.piece_in_target i hz)
  have hsumpos := positive_add_of_uniform_quadratic_bound
    ((ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) z) (ddbar f z)
    hαpos hβone δ C hCδ hmargin hβlower
  have hApproxAt : ContDiffAt ℝ 2 (approx ∘ e.symm) z :=
    hApproxChart.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
      (cover.piece_in_target i hz))
  have hψAt : ContDiffAt ℝ 2 (ψ ∘ e.symm) z :=
    hψChart.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
      (cover.piece_in_target i hz))
  have hsumAt : ContDiffAt ℝ 2 ((ψ + approx) ∘ e.symm) z := by
    have h := hψAt.add hApproxAt
    simpa [Function.comp_def] using h
  have hddadd : ddbar ((ψ + approx) ∘ e.symm) z =
      ddbar (ψ ∘ e.symm) z + ddbar (approx ∘ e.symm) z := by
    rw [show (ψ + approx) ∘ e.symm = (ψ ∘ e.symm) + (approx ∘ e.symm) by rfl]
    exact ddbar_add hψAt hApproxAt
  have hform :
      (ω₀.toFormField + mddbar n (ψ + approx)).chartRep (cover.base i) z =
        (ω₀.toFormField + mddbar n ψ).chartRep (cover.base i) z + ddbar f z := by
    rw [FormField.chartRep_add, FormField.chartRep_add]
    simp only [Pi.add_apply]
    rw [chartRep_mddbar_of_contMDiff_two (hψ2.add hApprox) (cover.base i)
        (cover.piece_in_target i hz),
      chartRep_mddbar_of_contMDiff_two hψ2 (cover.base i) (cover.piece_in_target i hz)]
    rw [hddadd]
    abel
  rw [hform]
  exact hsumpos

/-- Positive definiteness is stable along a convergent smooth-core `C^{2,α}` approximation:
a tail of the approximants stays in the positive cone of the perturbed Kähler form. -/
private theorem exists_smoothCore_C2_approximation_positive_tail
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hv : Filter.Tendsto
      (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) Filter.atTop
      (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)))
    (hpositive : ω₀.IsC2Potential (φ + P.evalC2 u)) :
    ∃ N : ℕ, ∀ j, ω₀.IsC2Potential (φ + fun x =>
      smoothChartHolderContinuousMapLinearMap P.finiteChartCover 2 α (v (j + N)) x) := by
  classical
  let cover := P.finiteChartCover
  let a : ℕ → M → ℝ := fun j x =>
    smoothChartHolderContinuousMapLinearMap cover 2 α (v j) x
  have hφ2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ :=
    hφ.1.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hcore (j : ℕ) :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (a j) := by
    change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (v j).smoothMap
    exact (v j).smoothMap.contMDiff
  have hEval : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u) := by
    have h := hpositive.1.sub hφ2
    have hEq : (φ + P.evalC2 u) - φ = P.evalC2 u := by
      funext x
      simp
    rw [← hEq]
    exact h
  by_cases hM : Nonempty M
  · let : Nonempty M := hM
    by_cases hn : 0 < n
    · obtain ⟨δ, hδpos, hmargin⟩ := exists_c2Potential_uniform_chart_margin
        ω₀ hpositive cover hn
      let ψ : M → ℝ := φ + P.evalC2 u
      let η : ℕ → M → ℝ := fun j => a j - P.evalC2 u
      have hη (j : ℕ) :
          ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (η j) := by
        exact ((hcore j).of_le
          (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).sub hEval
      have hlocal (i : cover.ι) :
          ∀ᶠ j in Filter.atTop, ∀ z ∈ interior (cover.piece i),
            dist
              (iteratedFDeriv ℝ 2
                ((smoothChartHolderContinuousMapExtension cover 2 α P.normedDataC2
                  (v j : LittleHolder cover 2 α P.normedDataC2) : M → ℝ) ∘
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z)
              (iteratedFDeriv ℝ 2
                ((smoothChartHolderContinuousMapExtension cover 2 α P.normedDataC2
                  (u : LittleHolder cover 2 α P.normedDataC2) : M → ℝ) ∘
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z) < δ / 2 := by
        have hconv := smoothCore_approximation_secondDerivative_tendstoUniformlyOn
          (ω₀.perturb φ hφ) α u v hv i
        rw [Metric.tendstoUniformlyOn_iff] at hconv
        simpa [dist_comm] using hconv (δ / 2) (by positivity)
      have hlocalAll :
          ∀ᶠ j in Filter.atTop, ∀ i ∈ Finset.univ,
            ∀ z ∈ interior (cover.piece i),
              dist
                (iteratedFDeriv ℝ 2
                  ((smoothChartHolderContinuousMapExtension cover 2 α P.normedDataC2
                    (v j : LittleHolder cover 2 α P.normedDataC2) : M → ℝ) ∘
                    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z)
                (iteratedFDeriv ℝ 2
                  ((smoothChartHolderContinuousMapExtension cover 2 α P.normedDataC2
                    (u : LittleHolder cover 2 α P.normedDataC2) : M → ℝ) ∘
                    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z) < δ / 2 := by
        simpa using (Finset.eventually_all (I := Finset.univ) (l := Filter.atTop)
          (p := fun i j => ∀ z ∈ interior (cover.piece i),
            dist
              (iteratedFDeriv ℝ 2
                ((smoothChartHolderContinuousMapExtension cover 2 α P.normedDataC2
                  (v j : LittleHolder cover 2 α P.normedDataC2) : M → ℝ) ∘
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z)
              (iteratedFDeriv ℝ 2
                ((smoothChartHolderContinuousMapExtension cover 2 α P.normedDataC2
                  (u : LittleHolder cover 2 α P.normedDataC2) : M → ℝ) ∘
                  (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z) < δ / 2)).2
          (by intro i hi; exact hlocal i)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hlocalAll
      refine ⟨N, ?_⟩
      intro j
      let k := j + N
      have hk : N ≤ k := by dsimp [k]; omega
      have hpotential : ω₀.IsC2Potential (φ + a k) := by
        refine ⟨hφ2.add ((hcore k).of_le
          (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))), ?_⟩
        intro x
        obtain ⟨i, hx⟩ := cover.interior_covers x
        obtain ⟨z, hz, hzx⟩ := hx
        have hzpiece : z ∈ cover.piece i := interior_subset hz
        have hclose := hN k hk i (Finset.mem_univ i) z hz
        have hEvalEq : P.evalC2 u =
            smoothChartHolderContinuousMapExtension cover 2 α P.normedDataC2
              (u : LittleHolder cover 2 α P.normedDataC2) := by
          funext y
          rfl
        have hcoreChartOn : ContDiffOn ℝ 2
            (a k ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target := by
          have hchart := (contMDiff_iff.mp (hcore k)).2 (cover.base i) 0
          simpa [a, extChartAt, chartAt_self_eq] using hchart.of_le
            (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
        have hcoreChart : ContDiffAt ℝ 2
            (a k ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z :=
          hcoreChartOn.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
            (cover.piece_in_target i hzpiece))
        have hEvalChartOn : ContDiffOn ℝ 2
            (P.evalC2 u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target := by
          have hchart := (contMDiff_iff.mp hEval).2 (cover.base i) 0
          simpa [extChartAt, chartAt_self_eq] using hchart
        have hEvalChart : ContDiffAt ℝ 2
            (P.evalC2 u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z :=
          hEvalChartOn.contDiffAt ((isOpen_extChartAt_target (cover.base i)).mem_nhds
            (cover.piece_in_target i hzpiece))
        have hsub := iteratedFDeriv_sub_apply hcoreChart hEvalChart
        have hjet : ‖iteratedFDeriv ℝ 2
            (η k ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z‖ ≤ δ / 2 := by
          change ‖iteratedFDeriv ℝ 2
            ((a k - P.evalC2 u) ∘
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z‖ ≤ δ / 2
          rw [show (a k - P.evalC2 u) ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm =
              (a k ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) -
                (P.evalC2 u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
            by rfl, hsub]
          exact le_of_lt (by simpa [a, hEvalEq, smoothChartHolderContinuousMapExtension_coe,
            smoothChartHolderContinuousMapLinearMap, dist_eq_norm] using hclose)
        have hchartpos := chartRep_approximation_positive ω₀ hpositive (η k) (hη k)
          cover i z hzpiece δ (δ / 2)
          (fun w => hmargin i z hzpiece w) (by linarith [hδpos]) hjet
        have hpoint := chartRep_positive_implies_pointwise
          (ω₀.toFormField + mddbar n (ψ + η k)) (cover.base i)
          (cover.piece_in_target i hzpiece) hchartpos
        rw [← hzx]
        simpa [ψ, η, a, smoothChartHolderContinuousMapLinearMap] using hpoint
      simpa [k, a, smoothChartHolderContinuousMapLinearMap] using hpotential
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      refine ⟨0, ?_⟩
      intro j
      refine ⟨hφ2.add ((hcore j).of_le
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))), ?_⟩
      intro x
      constructor
      · intro v w
        have hv : v = 0 := Subsingleton.elim _ _
        have hw : w = 0 := Subsingleton.elim _ _
        simp [hv, hw]
      · intro w hw
        have hw0 : w = 0 := Subsingleton.elim _ _
        exact (hw hw0).elim
  · let : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨0, ?_⟩
    intro j
    refine ⟨hφ2.add ((hcore j).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))), ?_⟩
    intro x
    exact isEmptyElim x

/-- Approximate a carrier perturbation by smooth order-two core elements while staying inside
its positive-potential cone.  The convergence is in the actual `C^{2,α}` completion, so its
continuous chart-jet extensions converge as well. -/
private theorem exists_positive_smoothCore_C2_approximation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hφ) α]
    (u : P.C2) (hpositive : ω₀.IsC2Potential (φ + P.evalC2 u)) :
    ∃ v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α,
      Filter.Tendsto (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2))
        Filter.atTop
        (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) ∧
      ∀ j, ω₀.IsC2Potential (φ + fun x =>
        smoothChartHolderContinuousMapLinearMap P.finiteChartCover 2 α (v j) x) := by
  obtain ⟨v, hv⟩ := exists_smoothCore_C2_approximation (ω₀.perturb φ hφ) α u
  obtain ⟨N, hpositiveTail⟩ := exists_smoothCore_C2_approximation_positive_tail
    ω₀ φ hφ α u v hv hpositive
  refine ⟨fun j => v (j + N), ?_, hpositiveTail⟩
  have hshift : Filter.Tendsto (fun j : ℕ => j + N) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    apply Filter.eventually_atTop.2
    exact ⟨b, fun j hj => le_trans hj (Nat.le_add_right j N)⟩
  exact hv.comp hshift

private theorem exists_littleHolder_completion_limit_with_evaluation
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α]
    (g : ℕ → SmoothChartHolderCore P.finiteChartCover 0 α)
    (hg : CauchySeq (fun j =>
      (g j : LittleHolder P.finiteChartCover 0 α P.normedDataC0)))
    (f : M → ℝ)
    (hpoint : ∀ x, Filter.Tendsto (fun j => g j x) Filter.atTop (𝓝 (f x))) :
    ∃ q : LittleHolder P.finiteChartCover 0 α P.normedDataC0, ∀ x,
      smoothChartHolderContinuousMapExtension P.finiteChartCover 0 α P.normedDataC0 q x = f x := by
  let : NormedAddCommGroup (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 0 α P.normedDataC0
  let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 0 α P.normedDataC0
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hg
  refine ⟨q, ?_⟩
  intro x
  let F := smoothChartHolderContinuousMapExtension P.finiteChartCover 0 α P.normedDataC0
  have hF : Filter.Tendsto (fun j => F (g j : LittleHolder P.finiteChartCover 0 α P.normedDataC0))
      Filter.atTop (𝓝 (F q)) := F.continuous.tendsto q |>.comp hq
  have hEval : Filter.Tendsto (fun j => F (g j : LittleHolder P.finiteChartCover 0 α
      P.normedDataC0) x) Filter.atTop (𝓝 (F q x)) :=
    ((ContinuousMap.evalCLM (R := ℝ) x).continuous.tendsto (F q)).comp hF
  have hEq (j : ℕ) : F (g j : LittleHolder P.finiteChartCover 0 α P.normedDataC0) x = g j x := by
    dsimp [F]
    rw [smoothChartHolderContinuousMapExtension_coe]
    rfl
  have hEval' : Filter.Tendsto (fun j => g j x) Filter.atTop (𝓝 (F q x)) :=
    hEval.congr' (Filter.Eventually.of_forall hEq)
  exact tendsto_nhds_unique hEval' (hpoint x)

/-- A Cauchy estimate in the actual finite-atlas gauge produces the little-Hölder completion
representative with the prescribed pointwise limit.  The sign convention `-g i + g j` is the one
in the normed-group distance formula; the gauge is exactly the norm on this smooth core. -/
private theorem exists_littleHolder_completion_limit_of_finiteGaugeCauchy
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α]
    (g : ℕ → SmoothChartHolderCore P.finiteChartCover 0 α)
    (hGaugeCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i j, N ≤ i → N ≤ j →
      (smoothChartHolderGauge P.finiteChartCover 0 α (-g i + g j)).toReal < ε)
    (f : M → ℝ)
    (hpoint : ∀ x, Filter.Tendsto (fun j => g j x) Filter.atTop (𝓝 (f x))) :
    ∃ q : LittleHolder P.finiteChartCover 0 α P.normedDataC0, ∀ x,
      smoothChartHolderContinuousMapExtension P.finiteChartCover 0 α P.normedDataC0 q x = f x := by
  let : NormedAddCommGroup (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedAddCommGroup P.finiteChartCover 0 α P.normedDataC0
  let : NormedSpace ℝ (SmoothChartHolderCore P.finiteChartCover 0 α) :=
    smoothChartHolderCoreNormedSpace P.finiteChartCover 0 α P.normedDataC0
  have hg : CauchySeq (fun j =>
      (g j : LittleHolder P.finiteChartCover 0 α P.normedDataC0)) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hGaugeCauchy ε hε
    refine ⟨N, fun i hi => ?_⟩
    rw [dist_eq_norm_neg_add, ← UniformSpace.Completion.coe_neg,
      ← UniformSpace.Completion.coe_add, UniformSpace.Completion.norm_coe,
      smoothChartHolderCore_norm_eq_gauge P.finiteChartCover 0 α P.normedDataC0]
    exact hN i N hi le_rfl
  exact exists_littleHolder_completion_limit_with_evaluation ω₁ α g hg f hpoint

private theorem exists_littleHolder_logDet_positiveCone_composition
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (_hα₀ : 0 < α) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (u : P.C2) (δ : ℝ)
    (v : ℕ → SmoothChartHolderCore P.finiteChartCover 2 α)
    (hv : Filter.Tendsto
      (fun j => (v j : LittleHolder P.finiteChartCover 2 α P.normedDataC2)) Filter.atTop
      (𝓝 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)))
    (hpositive : ∀ j, ω₀.IsC2Potential (φ + fun x =>
      smoothChartHolderContinuousMapLinearMap P.finiteChartCover 2 α (v j) x))
    (hpositiveLimit : ω₀.IsC2Potential (φ + P.evalC2 u)) :
    ∃ q : LittleHolder P.finiteChartCover 0 α P.normedDataC0, ∀ x,
      smoothChartHolderContinuousMapExtension P.finiteChartCover 0 α P.normedDataC0 q x =
        uncenteredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ x := by
  let cover := P.finiteChartCover
  let ω₁ := ω₀.perturb φ hsol.1
  let A := fun j => smoothCorePerturbedChartMatrix ω₁ cover α (v j)
  have hpositive' : ∀ j,
      ω₀.IsC2Potential (φ + fun x => (v j).smoothMap x) := by
    simpa [smoothChartHolderContinuousMapLinearMap] using hpositive
  obtain ⟨g, houtput, hchart⟩ :=
    exists_smoothCore_uncenteredResidual_outputs ω₀ F hF t φ hsol α hα₁ δ v hpositive'
  have hφ₂ := hsol.1.1.of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have huC2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u) := by
    simpa only [Pi.add_apply, add_sub_cancel_left] using hpositiveLimit.1.sub hφ₂
  obtain ⟨hsup, hdiffHolder, hclose⟩ :=
    smoothCore_chartMatrix_control ω₀ φ hsol.1 α u v huC2
  obtain ⟨N, K, H, htail⟩ :=
    exists_smoothCore_chartMatrix_common_tail ω₀ φ hsol.1 α hα₁
      u v hv hpositive' hpositiveLimit hdiffHolder hclose
  have hGaugeCauchy :=
    smoothCore_residual_finiteGaugeCauchy_of_chartMatrix_control
      cover α P.normedDataC2 P.normedDataC0
      (fun j => (v j : LittleHolder cover 2 α P.normedDataC2)) hv.cauchySeq
      g A N K H (n + 1 : ℝ≥0) hchart
      (fun j k i z hz => hsup k j i z hz) (fun j k i => hdiffHolder k j i) htail
  have hpoint := smoothCore_uncenteredResidual_outputs_tendsto
    ω₀ F t φ hsol α u δ v hv hpositiveLimit hclose g houtput
  exact exists_littleHolder_completion_limit_of_finiteGaugeCauchy ω₁ α g hGaugeCauchy
    (uncenteredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ) hpoint

/-- Assemble the C²α smooth-core approximation with positive-cone logarithmic composition for one
input. -/
private theorem exists_littleHolder_uncenteredValue
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M]
    [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (u : P.C2) (δ : ℝ)
    (hpositive : ω₀.IsC2Potential (φ + P.evalC2 u)) :
    ∃ q : LittleHolder P.finiteChartCover 0 α P.normedDataC0, ∀ x,
      smoothChartHolderContinuousMapExtension P.finiteChartCover 0 α P.normedDataC0 q x =
        uncenteredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ x := by
  obtain ⟨v, hv, hpositiveApprox⟩ :=
    exists_positive_smoothCore_C2_approximation ω₀ φ hsol.1 α u hpositive
  exact exists_littleHolder_logDet_positiveCone_composition ω₀ F hF t φ hsol α hα₀ hα₁
    u δ v hv hpositiveApprox hpositive

/-- The log-determinant residual of a positive `C²` carrier perturbation belongs to the full
little-`C^{0,α}` completion.  The theorem isolates nonlinear chartwise composition and its
little-Hölder approximation from the later bounded mean projection. -/
theorem exists_littleHolderUncenteredResidual (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (radius : ℝ) (hradius : 0 < radius)
    (hpositive : ∀ (u : P.C2), ‖u‖ < radius →
      ω₀.IsC2Potential (φ + P.evalC2 u)) :
    Nonempty (LittleHolderUncenteredResidualData ω₀ F hF t φ hsol α radius) := by
  classical
  let q : P.C2 × ℝ → LittleHolder P.finiteChartCover 0 α P.normedDataC0 := fun p =>
    if hu : ‖p.1‖ < radius then
      if hb : p.1 = 0 ∧ p.2 = 0 then 0 else
        Classical.choose (exists_littleHolder_uncenteredValue ω₀ F hF t φ hsol α
          hα₀ hα₁ p.1 p.2 (hpositive p.1 hu))
    else 0
  refine ⟨⟨q, ?_, ?_⟩⟩
  · intro u δ hu x
    by_cases hb : u = 0 ∧ δ = 0
    · rcases hb with ⟨rfl, rfl⟩
      simp [q, uncenteredContinuityPathResidual]
    · simp only [q, dif_pos hu, dif_neg hb]
      exact Classical.choose_spec (exists_littleHolder_uncenteredValue ω₀ F hF t φ hsol α
        hα₀ hα₁ u δ (hpositive u hu)) x
  · simp [q, hradius]

end KahlerForm
