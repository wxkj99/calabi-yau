module

public import CalabiYau.MongeAmpere.Continuity.Openness.C2Approximation.Smoothing

/-!
# Positivity of sufficiently close smooth potentials

Strict positivity of the perturbed Hermitian form is open in the uniform topology on the second
coordinate jets over a compact finite chart cover.  This is a separate, finite-dimensional
positivity step after manifold smoothing.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

section

variable [T2Space M] [CompactSpace M]

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

private theorem compact_continuous_positive_margin_on
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (q : X → ℝ)
    (hq : ContinuousOn q K) (hpos : ∀ x ∈ K, 0 < q x) :
    ∃ δ > 0, ∀ x ∈ K, δ ≤ q x := by
  obtain ⟨x, hx, hxmin⟩ := hK.exists_isMinOn hne hq
  refine ⟨q x, hpos x hx, ?_⟩
  intro y hy
  exact hxmin hy

private theorem exists_uniform_chartQuadratic_margin
    {n : ℕ} (hn : n ≠ 0) {K : Set (EuclideanSpace ℂ (Fin n))}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (α : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hcont : ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        α p.1 ![p.2, Complex.I • p.2])
      (K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ)))
    (hpos : ∀ z ∈ K, ∀ v, v ≠ 0 → 0 < α z ![v, Complex.I • v]) :
    ∃ δ > 0, ∀ z ∈ K, ∀ v,
      δ * ‖v‖ ^ 2 ≤ α z ![v, Complex.I • v] := by
  have hsphere : (Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1).Nonempty := by
    obtain ⟨e⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    refine ⟨EuclideanSpace.single e 1, ?_⟩
    simp [PiLp.norm_single]
  have hKprod : IsCompact
      (K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ)) :=
    hK.prod (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1)
  have hKprodne :
      (K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ)).Nonempty :=
    hKne.prod hsphere
  let q : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) → ℝ :=
    fun p => α p.1 ![p.2, Complex.I • p.2]
  have hqpos : ∀ p ∈ K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ), 0 < q p := by
    intro p hp
    have hpv : p.2 ∈ Metric.sphere 0 1 := hp.2
    have hpvnorm : ‖p.2‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hpv
    have hpvne : p.2 ≠ 0 := by
      intro hz
      simp [hz] at hpvnorm
    exact hpos p.1 hp.1 p.2 hpvne
  obtain ⟨δ, hδpos, hδ⟩ :=
    compact_continuous_positive_margin_on hKprod hKprodne q hcont hqpos
  refine ⟨δ, hδpos, ?_⟩
  intro z hz v
  by_cases hv : v = 0
  · subst v
    have hzero : ![(0 : EuclideanSpace ℂ (Fin n)),
        Complex.I • (0 : EuclideanSpace ℂ (Fin n))] = 0 := by
      funext i
      fin_cases i <;> simp
    rw [hzero]
    simp
  · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u := ‖v‖⁻¹ • v
    have hunorm : ‖u‖ = 1 := by
      calc
        ‖u‖ = ‖‖v‖⁻¹‖ * ‖v‖ := norm_smul _ _
        _ = ‖v‖⁻¹ * ‖v‖ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm)]
        _ = 1 := inv_mul_cancel₀ hvnorm.ne'
    have hu : (z, u) ∈
        K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ) := by
      refine ⟨hz, ?_⟩
      simpa [Metric.mem_sphere, dist_eq_norm] using hunorm
    have hunit := hδ (z, u) hu
    have hv_eq : v = ‖v‖ • u := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hvnorm.ne', one_smul]
    have hscale : α z ![v, Complex.I • v] =
        ‖v‖ ^ 2 * α z ![u, Complex.I • u] := by
      have htuple : ![v, Complex.I • v] =
          ![‖v‖ • u, Complex.I • (‖v‖ • u)] := by
        funext i
        fin_cases i
        · exact hv_eq
        · exact congrArg (fun w => Complex.I • w) hv_eq
      have hJ : Complex.I • (‖v‖ • u) = ‖v‖ • (Complex.I • u) := by
        change EuclideanSpace.complexStructure n (‖v‖ • u) = _
        exact (EuclideanSpace.complexStructure n).map_smul _ _
      calc
        α z ![v, Complex.I • v] =
            α z ![‖v‖ • u, ‖v‖ • (Complex.I • u)] := by rw [← hJ, ← htuple]
        _ = (∏ _i : Fin 2, ‖v‖) • α z ![u, Complex.I • u] := by
          have htuple' : ![‖v‖ • u, ‖v‖ • (Complex.I • u)] =
              (fun i : Fin 2 => ‖v‖ • (![u, Complex.I • u] i)) := by
            funext i
            fin_cases i <;> simp
          rw [htuple', (α z).map_smul_univ]
        _ = ‖v‖ ^ 2 * α z ![u, Complex.I • u] := by simp [pow_two]
    calc
      δ * ‖v‖ ^ 2 ≤ α z ![u, Complex.I • u] * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hunit (sq_nonneg ‖v‖)
      _ = ‖v‖ ^ 2 * α z ![u, Complex.I • u] := by ring
      _ = α z ![v, Complex.I • v] := hscale.symm

end

private theorem chartQuadratic_continuousOn
    (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsC2Potential φ) (x : M) {K : Set (EuclideanSpace ℂ (Fin n))}
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ContinuousOn
      (fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) =>
        ((ω₀.toFormField + mddbar n φ).chartRep x p.1) ![p.2, Complex.I • p.2])
      (K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ)) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f := φ ∘ e.symm
  let U := K ×ˢ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ)
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  have hcf : ContDiffOn ℝ 2 f e.target := by
    have h := (contMDiff_iff.mp hφ.1).2 x 0
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
            fderiv ℝ (fderiv ℝ f) p.1 p.2 (Complex.I • (Complex.I • p.2))) / 2) U := by
      exact (hterm₁.sub hterm₂).div_const 2
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
    ContinuousEval.continuous_eval.continuousOn.comp hωpair
      (fun _ _ => Set.mem_univ _)
  have hrepr (p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n))
      (hp : p ∈ U) :
      ((ω₀.toFormField + mddbar n φ).chartRep x p.1) ![p.2, Complex.I • p.2] =
        (ω₀.toFormField.chartRep x p.1) ![p.2, Complex.I • p.2] +
          ddbar f p.1 ![p.2, Complex.I • p.2] := by
    change (ω₀.toFormField.chartRep x p.1 + (mddbar n φ).chartRep x p.1)
        ![p.2, Complex.I • p.2] = _
    rw [ContinuousAlternatingMap.add_apply,
      chartRep_mddbar_of_contMDiff_two hφ.1 x (hKt hp.1)]
  exact (hωeval.add hddbar).congr (fun p hp => hrepr p hp)

section

variable [T2Space M] [CompactSpace M]

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

private theorem chartRep_isPositive_of_pointwise
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (α : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hα : ∀ x, (α x).IsPositive) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (α.chartRep x z).IsPositive := by
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
          (w := x) (x := y) (y := x) (z := y) (v := v)
          ⟨⟨hyxℂ, hyyℂ⟩, hyxℂ⟩
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
          (w := y) (x := x) (y := y) (z := y) (v := v)
          ⟨⟨hyyℂ, hyxℂ⟩, hyyℂ⟩
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
  have hchart : α.chartRep x z =
      (α y).compContinuousLinearMap (A.restrictScalars ℝ) := by
    change (α y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hAreal]
  rw [hchart]
  exact (hα y).compContinuousLinearMap AEquiv

private theorem pointwise_isPositive_of_chartRep
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (α : FormField (EuclideanSpace ℂ (Fin n)) M 2) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hpos : (α.chartRep x z).IsPositive) :
    (α ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).IsPositive := by
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
          (w := x) (x := y) (y := x) (z := y) (v := v)
          ⟨⟨hyxℂ, hyyℂ⟩, hyxℂ⟩
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
          (w := y) (x := x) (y := y) (z := y) (v := v)
          ⟨⟨hyyℂ, hyxℂ⟩, hyyℂ⟩
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
  have hchart : α.chartRep x z =
      (α y).compContinuousLinearMap (A.restrictScalars ℝ) := by
    change (α y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hAreal]
  have hposA : ((α y).compContinuousLinearMap (A.restrictScalars ℝ)).IsPositive := by
    rw [← hchart]
    exact hpos
  let Ainv : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (AEquiv.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ
  have hAinv : (A.restrictScalars ℝ).comp Ainv =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin n)) := by
    apply ContinuousLinearMap.ext
    intro v
    change A (AEquiv.symm v) = v
    exact AEquiv.apply_symm_apply v
  have hback := hposA.compContinuousLinearMap AEquiv.symm
  have hbackEq :
      ((α y).compContinuousLinearMap (A.restrictScalars ℝ)).compContinuousLinearMap Ainv = α y := by
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext i
    have hi := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ]
        EuclideanSpace ℂ (Fin n) => L (v i)) hAinv
    simpa [ContinuousLinearMap.comp_apply] using hi
  rw [hbackEq] at hback
  exact hback

end

private theorem chartRep_approximation_positive
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsC2Potential φ)
    (A : ChartwiseC2SmoothingData (n := n) (M := M) φ)
    (i : A.cover.ι) (j : ℕ) (δ C : ℝ)
    (hmargin : ∀ z ∈ A.cover.piece i, ∀ v,
      δ * ‖v‖ ^ 2 ≤
        ((ω₀.toFormField + mddbar n φ).chartRep (A.cover.base i) z) ![v, Complex.I • v])
    (hCδ : C < δ)
    (hjet : ∀ z ∈ A.cover.piece i,
      ‖iteratedFDeriv ℝ 2
        ((A.approximation j - φ) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (A.cover.base i)).symm) z‖ ≤ C) :
    ∀ z ∈ A.cover.piece i,
      ((ω₀.toFormField + mddbar n (A.approximation j)).chartRep (A.cover.base i) z).IsPositive := by
  intro z hz
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (A.cover.base i)
  let f := (A.approximation j - φ) ∘ e.symm
  have hA2 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (A.approximation j) :=
    (A.smooth j).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hApproxChart : ContDiffOn ℝ 2 (A.approximation j ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hA2).2 (A.cover.base i) 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hφChart : ContDiffOn ℝ 2 (φ ∘ e.symm) e.target := by
    have h := (contMDiff_iff.mp hφ.1).2 (A.cover.base i) 0
    simpa [e, extChartAt, chartAt_self_eq] using h
  have hf : ContDiffOn ℝ 2 f e.target := by
    have h := hApproxChart.sub hφChart
    simpa [f, Function.comp_def] using h
  have hfAt : ContDiffAt ℝ 2 f z :=
    hf.contDiffAt ((isOpen_extChartAt_target (A.cover.base i)).mem_nhds
      (A.cover.piece_in_target i hz))
  have hjet' : ‖iteratedFDeriv ℝ 2 f z‖ ≤ C := by
    change ‖iteratedFDeriv ℝ 2
      ((A.approximation j - φ) ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (A.cover.base i)).symm) z‖ ≤ C
    exact hjet z hz
  have hβone : (ddbar f z).IsOneOne := isOneOne_ddbar hfAt
  have hβlower : ∀ v, -C * ‖v‖ ^ 2 ≤ ddbar f z ![v, Complex.I • v] :=
    ddbar_lower_bound_of_secondJet f z hfAt C hjet'
  have hαpos : ((ω₀.toFormField + mddbar n φ).chartRep (A.cover.base i) z).IsPositive :=
    chartRep_isPositive_of_pointwise (ω₀.toFormField + mddbar n φ) hφ.2
      (A.cover.base i) (A.cover.piece_in_target i hz)
  have hsumpos := positive_add_of_uniform_quadratic_bound
    ((ω₀.toFormField + mddbar n φ).chartRep (A.cover.base i) z) (ddbar f z)
    hαpos hβone δ C hCδ (hmargin z hz) hβlower
  have hfEq : f = (A.approximation j ∘ e.symm) - (φ ∘ e.symm) := by
    funext w
    rfl
  have hApproxAt : ContDiffAt ℝ 2 (A.approximation j ∘ e.symm) z :=
    hApproxChart.contDiffAt ((isOpen_extChartAt_target (A.cover.base i)).mem_nhds
      (A.cover.piece_in_target i hz))
  have hφAt : ContDiffAt ℝ 2 (φ ∘ e.symm) z :=
    hφChart.contDiffAt ((isOpen_extChartAt_target (A.cover.base i)).mem_nhds
      (A.cover.piece_in_target i hz))
  have hddsub : ddbar f z =
      ddbar (A.approximation j ∘ e.symm) z - ddbar (φ ∘ e.symm) z := by
    rw [hfEq]
    exact ddbar_sub hApproxAt hφAt
  have hform :
      (ω₀.toFormField + mddbar n (A.approximation j)).chartRep (A.cover.base i) z =
        (ω₀.toFormField + mddbar n φ).chartRep (A.cover.base i) z + ddbar f z := by
    rw [FormField.chartRep_add, FormField.chartRep_add]
    simp only [Pi.add_apply]
    rw [chartRep_mddbar_of_contMDiff_two hA2 (A.cover.base i) (A.cover.piece_in_target i hz),
      chartRep_mddbar_of_contMDiff_two hφ.1 (A.cover.base i) (A.cover.piece_in_target i hz)]
    rw [hddsub]
    abel
  rw [hform]
  exact hsumpos

private theorem exists_chartPiece_positiveMargin
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsC2Potential φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι)
    (hn : n ≠ 0) :
    ∃ δ > 0, ∀ z ∈ cover.piece i, ∀ v,
      δ * ‖v‖ ^ 2 ≤
        ((ω₀.toFormField + mddbar n φ).chartRep (cover.base i) z) ![v, Complex.I • v] := by
  classical
  by_cases hne : (cover.piece i).Nonempty
  · exact exists_uniform_chartQuadratic_margin hn (cover.isCompact_piece i) hne
      (fun z => (ω₀.toFormField + mddbar n φ).chartRep (cover.base i) z)
      (chartQuadratic_continuousOn ω₀ hφ (cover.base i) (cover.piece_in_target i))
      (by
        intro z hz v hv
        exact (chartRep_isPositive_of_pointwise
          (ω₀.toFormField + mddbar n φ) hφ.2 (cover.base i)
          (cover.piece_in_target i hz)).2 v hv)
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz v
    exact (hne ⟨z, hz⟩).elim

/-- A chartwise `C²`-convergent smooth approximation to a strictly positive `C²` potential is
positive from some index onward. -/
theorem ChartwiseC2SmoothingData.eventually_isPotential
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsC2Potential φ)
    (A : ChartwiseC2SmoothingData (n := n) (M := M) φ) :
    ∃ N, ∀ j, N ≤ j → ω₀.IsPotential (A.approximation j) := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨0, ?_⟩
    intro j hj
    constructor
    · exact A.smooth j
    · intro x
      constructor
      · intro u v
        have huv : u = (0 : EuclideanSpace ℂ (Fin 0)) := Subsingleton.elim _ _
        have hv : v = (0 : EuclideanSpace ℂ (Fin 0)) := Subsingleton.elim _ _
        subst u
        subst v
        simp
      · intro v hv
        exact (hv (Subsingleton.elim _ _)).elim
  · by_cases hM : IsEmpty M
    · refine ⟨0, ?_⟩
      intro j hj
      constructor
      · exact A.smooth j
      · intro x
        exact (hM.false x).elim
    ·
      let cover := A.cover
      let hmargins (i : cover.ι) := exists_chartPiece_positiveMargin ω₀ hφ cover i hn
      let δ (i : cover.ι) : ℝ := Classical.choose (hmargins i)
      have hδpos (i : cover.ι) : 0 < δ i := (Classical.choose_spec (hmargins i)).1
      have hmargin (i : cover.ι) : ∀ z ∈ cover.piece i, ∀ v,
          δ i * ‖v‖ ^ 2 ≤
            ((ω₀.toFormField + mddbar n φ).chartRep (cover.base i) z) ![v, Complex.I • v] :=
        (Classical.choose_spec (hmargins i)).2
      let ε (i : cover.ι) : ℝ≥0 := ⟨δ i / 2, le_of_lt (half_pos (hδpos i))⟩
      have hεpos (i : cover.ι) : 0 < ε i := by
        change 0 < δ i / 2
        exact half_pos (hδpos i)
      have hεδ (i : cover.ι) : (ε i : ℝ) < δ i := by
        change δ i / 2 < δ i
        linarith [hδpos i]
      let hconvergence (i : cover.ι) := A.jetsTendsto (ε i) (hεpos i)
      let Nchart (i : cover.ι) : ℕ := Classical.choose (hconvergence i)
      have hjets (i : cover.ι) : ∀ j, Nchart i ≤ j → ∀ i' : cover.ι, ∀ k, k ≤ 2 →
          ∀ z ∈ cover.piece i',
            ‖iteratedFDeriv ℝ k
              ((A.approximation j - φ) ∘
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i')).symm) z‖ ≤ ε i :=
        Classical.choose_spec (hconvergence i)
      let N := Finset.univ.sup Nchart
      refine ⟨N, ?_⟩
      intro j hj
      constructor
      · exact A.smooth j
      · intro y
        obtain ⟨i, hzimg⟩ := cover.interior_covers y
        obtain ⟨z, hzinterior, hzy⟩ := hzimg
        have hzpiece : z ∈ cover.piece i := interior_subset hzinterior
        have hNi : Nchart i ≤ j := le_trans (Finset.le_sup (Finset.mem_univ i)) hj
        have hchart := chartRep_approximation_positive ω₀ hφ A i j (δ i) (ε i)
          (hmargin i) (hεδ i) (by
            intro w hw
            have h := hjets i j hNi i 2 (by norm_num) w hw
            simpa [ε] using h)
        have hyTarget : z ∈
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
          cover.piece_in_target i hzpiece
        have hfield := pointwise_isPositive_of_chartRep
          (ω₀.toFormField + mddbar n (A.approximation j)) (cover.base i) hyTarget
          (hchart z hzpiece)
        rw [hzy] at hfield
        exact hfield

end KahlerForm
