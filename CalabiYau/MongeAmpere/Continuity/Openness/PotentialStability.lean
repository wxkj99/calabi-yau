module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces

import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.ChartJets

/-!
# Stability of positivity under small `C²` perturbations

On a compact manifold, strict positivity of a Kähler form is open in the `C²` topology.  The
two-sided chart-norm characterization in `ContinuityHolderPair` identifies the carrier norm with
the finite-chart Hölder topology, so a sufficiently small element preserves positivity.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M]
section

variable [ConnectedSpace M]

/-- A continuous strictly positive function on a compact product has a uniform positive margin. -/
private theorem compact_continuous_positive_margin
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (q : X × Y → ℝ) (hq : Continuous q) (hpos : ∀ p, 0 < q p) :
    ∃ δ > 0, ∀ p, δ ≤ q p := by
  obtain ⟨p, hp, hpmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hq.continuousOn
  refine ⟨q p, hpos p, ?_⟩
  intro q'
  exact hpmin (Set.mem_univ q')

/-- A lower bound on the unit sphere extends to a quadratic lower bound on all vectors. -/
private theorem quadratic_bound_of_unit_sphere
    {n : ℕ} (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (δ : ℝ)
    (hunit : ∀ v, ‖v‖ = 1 → δ ≤ α ![v, Complex.I • v]) :
    ∀ v, δ * ‖v‖ ^ 2 ≤ α ![v, Complex.I • v] := by
  intro v
  by_cases hv : v = 0
  · subst v
    have hzero : ![(0 : EuclideanSpace ℂ (Fin n)), Complex.I • (0 : EuclideanSpace ℂ (Fin n))] = 0 := by
      ext i
      fin_cases i <;> simp
    rw [hzero]
    simp
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : EuclideanSpace ℂ (Fin n) := (‖v‖⁻¹ : ℝ) • v
  have hw : ‖w‖ = 1 := by
    calc
      ‖w‖ = ‖(‖v‖⁻¹ : ℝ)‖ * ‖v‖ := norm_smul _ _
      _ = 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm)]
        exact inv_mul_cancel₀ hvnorm.ne'
  have hvw : v = ‖v‖ • w := by
    dsimp [w]
    rw [smul_smul]
    simp [hvnorm.ne']
  have hIw : Complex.I • v = ‖v‖ • (Complex.I • w) := by
    calc
      Complex.I • v = Complex.I • (‖v‖ • w) := congrArg (fun u => Complex.I • u) hvw
      _ = ‖v‖ • (Complex.I • w) := smul_comm Complex.I ‖v‖ w
  have hvec : ![v, Complex.I • v] =
      (fun i : Fin 2 => ‖v‖ • ![w, Complex.I • w] i) := by
    funext i
    fin_cases i
    · simpa using hvw
    · simpa using hIw
  have hscale : α ![v, Complex.I • v] = ‖v‖ ^ 2 * α ![w, Complex.I • w] := by
    rw [hvec]
    have h := α.map_smul_univ (fun _ : Fin 2 => ‖v‖) ![w, Complex.I • w]
    simpa [Fin.prod_univ_succ, pow_two, smul_eq_mul] using h
  calc
    δ * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 * α ![w, Complex.I • w] := by
      calc
        δ * ‖v‖ ^ 2 = ‖v‖ ^ 2 * δ := by ring
        _ ≤ ‖v‖ ^ 2 * α ![w, Complex.I • w] :=
          mul_le_mul_of_nonneg_left (hunit w hw) (sq_nonneg ‖v‖)
    _ = α ![v, Complex.I • v] := hscale.symm

/-- A compact continuous family of positive `(1,1)`-forms has one uniform positive margin over
its unit vectors. This is the positive-cone estimate to apply on the finite chart-piece space. -/
private theorem exists_uniform_positive_quadratic_margin
    {n : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (A : X → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hquadcont : Continuous (fun p : X ×
      {v : EuclideanSpace ℂ (Fin n) // ‖v‖ = 1} =>
      A p.1 ![p.2.1, Complex.I • p.2.1]))
    (hApos : ∀ x, (A x).IsPositive) (hn : 0 < n) :
    ∃ δ > 0, ∀ x v, δ * ‖v‖ ^ 2 ≤ A x ![v, Complex.I • v] := by
  let S := {v : EuclideanSpace ℂ (Fin n) // ‖v‖ = 1}
  have hsphere : IsCompact {v : EuclideanSpace ℂ (Fin n) | ‖v‖ = 1} := by
    simpa [Metric.sphere] using
      (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) (1 : ℝ))
  let : CompactSpace S := isCompact_iff_compactSpace.mp hsphere
  have hSnonempty : Nonempty S := by
    obtain ⟨i⟩ := (Fin.pos_iff_nonempty.mp hn)
    refine ⟨⟨EuclideanSpace.single i (1 : ℂ), ?_⟩⟩
    simp
  let : Nonempty S := hSnonempty
  let q : X × S → ℝ := fun p => A p.1 ![p.2.1, Complex.I • p.2.1]
  have hqcont : Continuous q := hquadcont
  have hqpos : ∀ p, 0 < q p := by
    rintro ⟨x, v⟩
    have hv : ‖v.1‖ = 1 := v.2
    have hvpos : 0 < ‖v.1‖ := by rw [hv]; norm_num
    exact (hApos x).2 v.1 (norm_pos_iff.mp hvpos)
  obtain ⟨δ, hδ, hmargin⟩ := compact_continuous_positive_margin q hqcont hqpos
  refine ⟨δ, hδ, ?_⟩
  intro x v
  exact quadratic_bound_of_unit_sphere (A x) δ
    (fun w hw => hmargin (x, ⟨w, hw⟩)) v

/-- A chart representation of a form field is its value at the represented point pulled back
by a complex-linear chart-coordinate equivalence. -/
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
          (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) := by
        rfl
      _ = (θ y).compContinuousLinearMap (A.restrictScalars ℝ) := by rw [hAreal]
  have hARestrict : (AEquiv.restrictScalars ℝ :
      EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) =
      A.restrictScalars ℝ := by
    ext v
    rfl
  refine ⟨AEquiv, ?_⟩
  rw [hARestrict]
  simpa [e, y] using hchart

/-- Positivity of a Kähler form is preserved in any holomorphic chart representation. -/
private theorem kahler_chartRep_isPositive
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (ω₁.toFormField.chartRep x z).IsPositive := by
  obtain ⟨A, hchart⟩ := formField_chartRep_eq_comp_tangentEquiv ω₁.toFormField x hz
  rw [hchart]
  exact (ω₁.isPositive ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
    |>.compContinuousLinearMap A

/-- Positivity of a chart representation pulls back to positivity of the represented form value. -/
private theorem formField_isPositive_of_chartRep
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (θ : FormField (EuclideanSpace ℂ (Fin n)) M 2) (x : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hchart : (θ.chartRep x z).IsPositive) :
    (θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).IsPositive := by
  obtain ⟨A, hrep⟩ := formField_chartRep_eq_comp_tangentEquiv θ x hz
  have hcancel :
      ((θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).compContinuousLinearMap
        (A.restrictScalars ℝ)).compContinuousLinearMap
          ((A.symm : EuclideanSpace ℂ (Fin n) →L[ℂ]
            EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) =
        θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) := by
    ext v
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext j
    simp
  have hpull := hchart.compContinuousLinearMap A.symm
  rw [hrep, hcancel] at hpull
  exact hpull

/-- The quadratic evaluation of a smooth Kähler form is continuous on the sigma of the fixed
compact chart pieces times the unit sphere. This isolates the chart-evaluation continuity needed by
the compact positive-cone argument. -/
private theorem continuous_kahler_chart_piece_form_eval
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) :
    Continuous (fun p : (Σ i : cover.ι, cover.piece i) ×
        {v : EuclideanSpace ℂ (Fin n) // ‖v‖ = 1} =>
      ω₁.toFormField.chartRep (cover.base p.1.1) p.1.2.1
        ![p.2.1, Complex.I • p.2.1]) := by
  let X := Σ i : cover.ι, cover.piece i
  let S := {v : EuclideanSpace ℂ (Fin n) // ‖v‖ = 1}
  let A : X → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
    fun p => ω₁.toFormField.chartRep (cover.base p.1) p.2.1
  have hAcont : Continuous A := by
    apply continuous_sigma
    intro i
    have hchart : ContDiffOn ℝ ∞
        (ω₁.toFormField.chartRep (cover.base i))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target :=
      ω₁.isSmooth (cover.base i)
    exact (hchart.continuousOn.mono (cover.piece_in_target i)).domRestrict
  have hmult : Continuous (fun p : X × S =>
      (A p.1).toContinuousMultilinearMap) := by
    exact ContinuousAlternatingMap.continuous_toContinuousMultilinearMap.comp
      (hAcont.comp continuous_fst)
  have hv : Continuous (fun p : X × S => (p.2.1 : EuclideanSpace ℂ (Fin n))) :=
    continuous_subtype_val.comp continuous_snd
  have hIv : Continuous (fun p : X × S => Complex.I • (p.2.1 : EuclideanSpace ℂ (Fin n))) := by
    change Continuous (fun p : X × S => EuclideanSpace.complexStructure n p.2.1)
    exact (EuclideanSpace.complexStructure n).continuous.comp hv
  have hvec : Continuous (fun p : X × S => ![p.2.1, Complex.I • p.2.1]) := by
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using hv
    · simpa using hIv
  have hEval : Continuous (fun p : X × S =>
      (A p.1).toContinuousMultilinearMap ![p.2.1, Complex.I • p.2.1]) :=
    hmult.eval hvec
  change Continuous (fun p : X × S =>
    ω₁.toFormField.chartRep (cover.base p.1.1) p.1.2.1
      ![p.2.1, Complex.I • p.2.1])
  exact hEval

/-- A smooth Kähler form has a uniform positive quadratic margin over the finite compact chart
pieces. The chart-evaluation continuity premise is proved from its smoothness above; compactness of
the sigma of the pieces and the unit sphere supplies the margin. -/
private theorem exists_uniform_chart_piece_positive_margin
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) [Nonempty M]
    (hApos : ∀ i z, z ∈ cover.piece i →
      (ω₁.toFormField.chartRep (cover.base i) z).IsPositive) (hn : 0 < n) :
    ∃ δ > 0, ∀ i z (_hz : z ∈ cover.piece i) v,
      δ * ‖v‖ ^ 2 ≤
        (ω₁.toFormField.chartRep (cover.base i) z) ![v, Complex.I • v] := by
  let X := Σ i : cover.ι, cover.piece i
  let : ∀ i, CompactSpace (cover.piece i) := fun i =>
    isCompact_iff_compactSpace.mp (cover.isCompact_piece i)
  let : CompactSpace X := by
    dsimp [X]
    infer_instance
  have hXnonempty : Nonempty X := by
    obtain ⟨x⟩ := ‹Nonempty M›
    rcases cover.interior_covers x with ⟨i, hx⟩
    rcases hx with ⟨z, hz, hzx⟩
    exact ⟨⟨i, ⟨z, interior_subset hz⟩⟩⟩
  let : Nonempty X := hXnonempty
  let A' : X → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
    fun p => ω₁.toFormField.chartRep (cover.base p.1) p.2.1
  have hA'cont : Continuous (fun p : X ×
      {v : EuclideanSpace ℂ (Fin n) // ‖v‖ = 1} =>
      A' p.1 ![p.2.1, Complex.I • p.2.1]) := by
    change Continuous (fun p : (Σ i : cover.ι, cover.piece i) ×
      {v : EuclideanSpace ℂ (Fin n) // ‖v‖ = 1} =>
      ω₁.toFormField.chartRep (cover.base p.1.1) p.1.2.1
        ![p.2.1, Complex.I • p.2.1])
    exact continuous_kahler_chart_piece_form_eval ω₁ cover
  obtain ⟨δ, hδ, hmargin⟩ :=
    exists_uniform_positive_quadratic_margin A' hA'cont
      (fun p => hApos p.1 p.2.1 p.2.2) hn
  refine ⟨δ, hδ, ?_⟩
  intro i z hz v
  exact hmargin ⟨i, ⟨z, hz⟩⟩ v

/-- A uniform quadratic margin makes a small Hermitian-form perturbation positive. This is the
pointwise positive-cone estimate used after taking a compact minimum over chart pieces and unit
vectors. -/
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

/-- A compact-chart margin and a conditional second-jet lower bound imply positivity of the
sum on every chart piece. The `hBbound` premise is supplied by
`ddbar_lower_bound_of_secondJet`, not assumed from a separate global form norm. -/
private theorem positive_add_on_chart_pieces_of_jet_bound
    {n : ℕ} {ι : Type*} {E : ι → Type*}
    (piece : ∀ i, Set (E i))
    (A B : ∀ i, piece i → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (δ C : ℝ) (hC : C < δ)
    (hmargin : ∀ i z v, δ * ‖v‖ ^ 2 ≤ A i z ![v, Complex.I • v])
    (hApos : ∀ i z, (A i z).IsPositive)
    (hBone : ∀ i z, (B i z).IsOneOne)
    (hBbound : ∀ i z v, -C * ‖v‖ ^ 2 ≤ B i z ![v, Complex.I • v]) :
    ∀ i z, (A i z + B i z).IsPositive := by
  intro i z
  exact positive_add_of_uniform_quadratic_bound (A i z) (B i z)
    (hApos i z) (hBone i z) δ C hC (hmargin i z) (hBbound i z)

/-- A chartwise order-two bound controls the negative part of the corresponding `i∂∂̄` quadratic
form. This is the analytic bridge from a supplied second-jet estimate to the positive-cone margin. -/
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
  have hI : Complex.I • (Complex.I • v) = -v := by
    simp [smul_smul]
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

/-- A globally `C²` function remains `C²` after reading it in any target chart. -/
private theorem chart_comp_contDiffAt_two
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M]
    (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f)
    (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ContDiffAt ℝ 2
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e.symm z := by
    have hSymmSmooth : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm z :=
      (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).mem_nhds hz)
    exact hSymmSmooth.of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  exact (contMDiffAt_iff_contDiffAt).mp
    ((hf (e.symm z)).comp_of_eq hsymm rfl)

end

/-- Mean-zero carrier evaluation is the same function as the completed smooth-chart
extension after coercing to the ambient little-Hölder space. -/
private theorem continuityHolderPair_evalC2_eq_completed
    {ω₁ : KahlerForm n M} {α : ℝ≥0} [P : ContinuityHolderPair ω₁ α]
    (u : P.C2) :
    P.evalC2 u = smoothChartHolderContinuousMapExtension P.finiteChartCover 2 α
      P.normedDataC2 (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) := by
  funext x
  rfl

/-- The completed-jet identity and norm bound give finite `C²` regularity of the actual
mean-zero evaluation. -/
private theorem continuityHolderPair_evalC2_contMDiff_two
    {ω₁ : KahlerForm n M} {α : ℝ≥0} [P : ContinuityHolderPair ω₁ α]
    (u : P.C2) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 (P.evalC2 u) := by
  rw [continuityHolderPair_evalC2_eq_completed]
  exact smoothChartHolderContinuousMapExtension_contMDiff_orderTwo_of_completedJets
    P.finiteChartCover α P.normedDataC2
    (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)
    (fun j hj i z hz =>
      smoothChartHolderContinuousMapExtension_completedJet_eq
        P.finiteChartCover α P.normedDataC2
        (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2) j hj i z hz)

/-- The same bridge bounds the actual second chart derivatives of the mean-zero evaluation. -/
private theorem continuityHolderPair_evalC2_secondJet_norm_le
    {ω₁ : KahlerForm n M} {α : ℝ≥0} [P : ContinuityHolderPair ω₁ α]
    (u : P.C2) (i : P.finiteChartCover.ι) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ interior (P.finiteChartCover.piece i)) :
    ‖iteratedFDeriv ℝ 2
      (P.evalC2 u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (P.finiteChartCover.base i)).symm) z‖ ≤ ‖u‖ := by
  rw [continuityHolderPair_evalC2_eq_completed]
  rw [smoothChartHolderContinuousMapExtension_completedJet_eq
    P.finiteChartCover α P.normedDataC2
    (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)
    2 (by omega) i z hz]
  simpa using (smoothChartHolderContinuousMapExtension_completedJet_norm_le
    P.finiteChartCover α P.normedDataC2
    (u : LittleHolder P.finiteChartCover 2 α P.normedDataC2)
    2 (by omega) i z hz)

/-- A sufficiently small mean-zero little `C^{2,α}` perturbation of a smooth potential remains a
positive `C²` potential. -/
theorem exists_c2Potential_radius (ω₀ ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α] (φ : M → ℝ)
    (hφ : ω₀.IsPotential φ) (hω : ω₀.perturb φ hφ = ω₁) :
    ∃ ε > 0, ∀ u : P.C2, ‖u‖ < ε → ω₀.IsC2Potential (φ + P.evalC2 u) := by
  have hφtwo : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ :=
    hφ.1.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  have hsumreg (u : P.C2) :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
        (φ + P.evalC2 u) :=
    hφtwo.add (continuityHolderPair_evalC2_contMDiff_two u)
  by_cases hn : 0 < n
  · by_cases hM : Nonempty M
    · let : Nonempty M := hM
      let cover := P.finiteChartCover
      have hbaseChartPositive : ∀ i z, z ∈ cover.piece i →
          (ω₁.toFormField.chartRep (cover.base i) z).IsPositive := by
        intro i z hz
        exact kahler_chartRep_isPositive ω₁ (cover.base i)
          (cover.piece_in_target i hz)
      obtain ⟨δ, hδ, hmargin⟩ :=
        exists_uniform_chart_piece_positive_margin ω₁ cover hbaseChartPositive hn
      refine ⟨δ / 2, half_pos hδ, ?_⟩
      intro u hu
      have huReg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
          (P.evalC2 u) := continuityHolderPair_evalC2_contMDiff_two u
      have huJet := continuityHolderPair_evalC2_secondJet_norm_le u
      have huδ : ‖u‖ < δ := by linarith
      have hbase : ω₀.toFormField + mddbar n φ = ω₁.toFormField := by
        have h := congrArg (fun η : KahlerForm n M => η.toFormField) hω
        simpa [KahlerForm.perturb] using h
      have hfields : ω₀.toFormField + mddbar n (φ + P.evalC2 u) =
          ω₁.toFormField + mddbar n (P.evalC2 u) := by
        calc
          _ = ω₀.toFormField +
              (mddbar n φ + mddbar n (P.evalC2 u)) := by
                rw [mddbar_add_of_contMDiff_two hφtwo huReg]
          _ = (ω₀.toFormField + mddbar n φ) + mddbar n (P.evalC2 u) := by
                rw [← add_assoc]
          _ = ω₁.toFormField + mddbar n (P.evalC2 u) := by rw [hbase]
      let pieces : cover.ι → Set (EuclideanSpace ℂ (Fin n)) :=
        fun i => interior (cover.piece i)
      let A : ∀ i, pieces i → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
        fun i z => ω₁.toFormField.chartRep (cover.base i) z.1
      let B : ∀ i, pieces i → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
        fun i z => ddbar
          (P.evalC2 u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base i)).symm) z.1
      have hchartSum : ∀ i (z : pieces i), (A i z + B i z).IsPositive := by
        apply positive_add_on_chart_pieces_of_jet_bound pieces A B δ ‖u‖ huδ
        · intro i z v
          exact hmargin i z.1 (interior_subset z.2) v
        · intro i z
          exact kahler_chartRep_isPositive ω₁ (cover.base i)
            (cover.piece_in_target i (interior_subset z.2))
        · intro i z
          exact isOneOne_ddbar (chart_comp_contDiffAt_two (P.evalC2 u) huReg
            (cover.base i) (z := z.1)
            (cover.piece_in_target i (interior_subset z.2)))
        · intro i z v
          exact ddbar_lower_bound_of_secondJet
            (P.evalC2 u ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
              (cover.base i)).symm) z.1
            (chart_comp_contDiffAt_two (P.evalC2 u) huReg (cover.base i) (z := z.1)
              (cover.piece_in_target i (interior_subset z.2)))
            ‖u‖ (huJet i z.1 z.2) v
      have hformPositive :
          (ω₀.toFormField + mddbar n (φ + P.evalC2 u)).IsPositive := by
        intro x
        rcases cover.interior_covers x with ⟨i, hx⟩
        rcases hx with ⟨z, hz, hzx⟩
        let zi : pieces i := ⟨z, hz⟩
        have hzTarget : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (cover.base i)).target := cover.piece_in_target i (interior_subset hz)
        have hchartMddbar : (mddbar n (P.evalC2 u)).chartRep (cover.base i) z =
            ddbar (P.evalC2 u ∘
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) z :=
          chartRep_mddbar_of_contMDiff_two huReg (cover.base i) hzTarget
        have hchartEq :
            (ω₀.toFormField + mddbar n (φ + P.evalC2 u)).chartRep (cover.base i) z =
              A i zi + B i zi := by
          dsimp [A, B, zi]
          rw [hfields, FormField.chartRep_add]
          simp only [Pi.add_apply]
          rw [hchartMddbar]
          rfl
        have hchartPos :
            ((ω₀.toFormField + mddbar n (φ + P.evalC2 u)).chartRep
              (cover.base i) z).IsPositive := by
          rw [hchartEq]
          exact hchartSum i zi
        have hpointPos := formField_isPositive_of_chartRep
          (ω₀.toFormField + mddbar n (φ + P.evalC2 u)) (cover.base i) hzTarget hchartPos
        rw [← hzx]
        exact hpointPos
      exact ⟨hsumreg u, hformPositive⟩
    · let : IsEmpty M := not_nonempty_iff.mp hM
      refine ⟨1, by norm_num, ?_⟩
      intro u hu
      refine ⟨hsumreg u, ?_⟩
      intro x
      exact isEmptyElim x
  · have hn0 : n = 0 := by omega
    subst n
    let : Subsingleton (EuclideanSpace ℂ (Fin 0)) := inferInstance
    refine ⟨1, by norm_num, ?_⟩
    intro u hu
    refine ⟨hsumreg u, ?_⟩
    intro x
    constructor
    · intro v w
      have hv : v = 0 := Subsingleton.elim _ _
      have hw : w = 0 := Subsingleton.elim _ _
      subst v
      subst w
      simp
    · intro v hv
      have hv0 : v = 0 := Subsingleton.elim _ _
      exact (hv hv0).elim

end KahlerForm
