module

public import CalabiYau.Analysis.Sobolev.Chart.Defs
public import CalabiYau.Geometry.Kahler.Riemannian.Laplacian
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic

/-!
# Compact chart ellipticity for the Kähler gradient

On a compact subset of the realification of a complex chart, the induced real metric and its
inverse are uniformly comparable with the Euclidean metric. Consequently each real coordinate
derivative of a smooth function is controlled pointwise by its Kähler gradient energy, with one
constant valid at every point of the compact set. The constant depends only on the chart, compact
set, Kähler form, and coordinate index, not on the function.

The normalization is nontrivial: for the flat complex curve with `ω = i dz ∧ dż`, the real metric
is `2 I` and `gradNormSq f = (f_x ^ 2 + f_y ^ 2) / 4`; the coefficient `4` suffices for either
unit real coordinate vector. When `n = 0` there are no coordinate indices, so the statement has
no instances; for an empty compact set one may take the constant to be zero.
-/

@[expose] public section

open scoped Manifold ContDiff Topology

namespace KahlerForm

private theorem realified_coordinate_derivative_eq_mfderiv
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (a : M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))
    (hy : y ∈ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a) :
    fderiv ℝ
      (fun z => f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
      (EuclideanSpace.single i 1) =
    mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) f
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
        ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y))
      (CalabiYau.Tensor.Coordinates.chartBasisVecFiber
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) a i
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
          ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y))) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let E := EuclideanSpace ℂ (Fin n)
  let c := extChartAt I a
  let z := (toEuclidean (E := E)).symm y
  let x := c.symm z
  have hz : z ∈ c.target := by
    change y ∈ (toEuclidean (E := E)) '' c.target at hy
    rcases hy with ⟨w, hw, hwy⟩
    have hzw : z = w := by
      dsimp [z]
      rw [← hwy]
      exact (toEuclidean (E := E)).symm_apply_apply w
    rw [hzw]
    exact hw
  have hxsource : x ∈ c.source := c.map_target hz
  have hxchart : x ∈ (chartAt E a).source := by
    rw [← CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source (I := I) (M := M)]
    exact hxsource
  have hxint : c x ∈ interior c.target := by
    rw [(isOpen_extChartAt_target (I := I) a).interior_eq]
    exact c.map_source hxsource
  have hcx : c x = z := c.right_inv hz
  have hfmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := hf.mdifferentiable (by simp) x
  have hpartial := CalabiYau.Riemannian.mfderiv_chartBasisVecFiber_of_mdifferentiableAt
    (I := I) (M := M) a hfmd hxchart hxint i
  have hscalar_diff : DifferentiableAt ℝ
      (CalabiYau.Tensor.Coordinates.scalarOnE (I := I) a f) z := by
    have hcontOn := CalabiYau.Tensor.Coordinates.scalarOnE_contDiffOn (I := I) a hf
    have hcontAt : ContDiffAt ℝ ∞
        (CalabiYau.Tensor.Coordinates.scalarOnE (I := I) a f) z :=
      (hcontOn.contDiffWithinAt hz).contDiffAt ((isOpen_extChartAt_target (I := I) a).mem_nhds hz)
    exact hcontAt.differentiableAt (by simp)
  have hsymm_diff : DifferentiableAt ℝ (fun q : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ E)) => (toEuclidean (E := E)).symm q) y :=
    ((toEuclidean (E := E)).symm).differentiable.differentiableAt
  have hcomp : fderiv ℝ
      (fun q : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        (CalabiYau.Tensor.Coordinates.scalarOnE (I := I) a f)
          ((toEuclidean (E := E)).symm q)) y =
      (fderiv ℝ (CalabiYau.Tensor.Coordinates.scalarOnE (I := I) a f) z).comp
        (fderiv ℝ (fun q : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (toEuclidean (E := E)).symm q) y) :=
    fderiv_comp y hscalar_diff hsymm_diff
  have hsymm_fderiv : fderiv ℝ (fun q : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ E)) => (toEuclidean (E := E)).symm q) y =
      ((toEuclidean (E := E)).symm : EuclideanSpace ℝ
        (Fin (Module.finrank ℝ E)) →L[ℝ] E) :=
    ((toEuclidean (E := E)).symm).fderiv
  change fderiv ℝ
      (fun q => (CalabiYau.Tensor.Coordinates.scalarOnE (I := I) a f)
        ((toEuclidean (E := E)).symm q)) y (EuclideanSpace.single i 1) = _
  rw [hcomp, hsymm_fderiv]
  change fderiv ℝ (CalabiYau.Tensor.Coordinates.scalarOnE (I := I) a f) z
      ((toEuclidean (E := E)).symm (EuclideanSpace.single i 1)) = _
  rw [← CalabiYau.Tensor.Coordinates.chartModelBasis_apply]
  rw [hcx] at hpartial
  unfold TangentSpace at hpartial
  exact hpartial.symm

private theorem riemannian_inner_cauchy_schwarz_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : CalabiYau.SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    (g.inner x v w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
  classical
  set a := g.inner x v v
  set b := g.inner x w w
  set c := g.inner x v w
  have ha_nn : 0 ≤ a := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · have heq : a = 0 := by change g.inner x v v = 0; rw [hv0]; simp
      rw [heq]
    · exact (g.pos x v hv0).le
  have hb_nn : 0 ≤ b := by
    rcases eq_or_ne w 0 with hw0 | hw0
    · have heq : b = 0 := by change g.inner x w w = 0; rw [hw0]; simp
      rw [heq]
    · exact (g.pos x w hw0).le
  have hquad : ∀ t : ℝ, 0 ≤ t * t * a + 2 * t * c + b := by
    intro t
    have hpos : 0 ≤ g.inner x (t • v + w) (t • v + w) := by
      rcases eq_or_ne (t • v + w) 0 with hz | hnz
      · have heqz : g.inner x (t • v + w) (t • v + w) = 0 := by rw [hz]; simp
        rw [heqz]
      · exact (g.pos x _ hnz).le
    have h_expand : g.inner x (t • v + w) (t • v + w) =
        t * t * a + 2 * t * c + b := by
      have h1 : g.inner x (t • v + w) (t • v + w) =
          g.inner x (t • v) (t • v + w) + g.inner x w (t • v + w) := by
        rw [map_add (g.inner x), add_apply]
      have h2 : g.inner x (t • v) (t • v + w) =
          g.inner x (t • v) (t • v) + g.inner x (t • v) w :=
        map_add (g.inner x (t • v)) (t • v) w
      have h3 : g.inner x w (t • v + w) =
          g.inner x w (t • v) + g.inner x w w := map_add (g.inner x w) (t • v) w
      have h4 : g.inner x (t • v) (t • v) = t * (t * a) := by
        rw [map_smul (g.inner x), smul_apply,
          map_smul (g.inner x v), smul_eq_mul, smul_eq_mul]
      have h5 : g.inner x (t • v) w = t * c := by
        rw [map_smul (g.inner x), smul_apply, smul_eq_mul]
      have h6 : g.inner x w (t • v) = t * c := by
        rw [map_smul (g.inner x w), smul_eq_mul, g.symm x w v]
      rw [h1, h2, h3, h4, h5, h6]
      ring
    rw [h_expand] at hpos
    exact hpos
  rcases lt_or_eq_of_le ha_nn with ha_pos | ha_zero
  · have hroot := hquad (-c / a)
    have hsimp : -c / a * (-c / a) * a + 2 * (-c / a) * c + b = b - c^2 / a := by
      field_simp
      ring
    rw [hsimp] at hroot
    have hcsa : c ^ 2 / a ≤ b := by linarith
    have h1 : c ^ 2 = a * (c ^ 2 / a) := by field_simp
    rw [h1]
    exact mul_le_mul_of_nonneg_left hcsa ha_nn
  · have ha_eq : a = 0 := ha_zero.symm
    have hv_zero : v = 0 := by
      by_contra hne
      exact (lt_irrefl (0 : ℝ)) (ha_eq ▸ g.pos x v hne)
    have hc_eq : c = 0 := by change g.inner x v w = 0; rw [hv_zero]; simp
    rw [hc_eq, ha_eq]
    simp

private theorem exists_uniform_chart_basis_metric_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M) (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K,
      ω₀.toRiemannianMetric.inner
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
          ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y))
        (CalabiYau.Tensor.Coordinates.chartBasisVecFiber
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) a i
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)))
        (CalabiYau.Tensor.Coordinates.chartBasisVecFiber
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) a i
          ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
            ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y))) ≤ B := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let E := EuclideanSpace ℂ (Fin n)
  let V := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let c := extChartAt I a
  let p : V → M := fun y => c.symm ((toEuclidean (E := E)).symm y)
  let q : V → ℝ := fun y =>
    CalabiYau.Tensor.Coordinates.chartGramMatrix ω₀.toRiemannianMetric a (p y) i i
  have hyTarget : ∀ y ∈ K, (toEuclidean (E := E)).symm y ∈ c.target := by
    intro y hy
    have hty := hK hy
    change y ∈ (toEuclidean (E := E)) '' c.target at hty
    rcases hty with ⟨z, hz, hzy⟩
    have hEq : (toEuclidean (E := E)).symm y = z := by
      rw [← hzy]
      exact (toEuclidean (E := E)).symm_apply_apply z
    rw [hEq]
    exact hz
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target := by
    simpa [c] using (contMDiffOn_extChartAt_symm (I := I) a)
  have hpcont : ContinuousOn p K := by
    dsimp [p]
    exact hsymm.continuousOn.comp
      ((toEuclidean (E := E)).symm.continuous.continuousOn) hyTarget
  have hpmem : ∀ y ∈ K,
      p y ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
    intro y hy
    have hsource : p y ∈ c.source := c.map_target (hyTarget y hy)
    rw [CalabiYau.Tensor.Coordinates.trivializationAt_baseSet_eq_chartAt_source]
    rw [← CalabiYau.RiemannianVolume.extChartAt_source_eq_chartAt_source (I := I) (M := M)]
    exact hsource
  have hentry := (CalabiYau.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn
    (I := I) ω₀.toRiemannianMetric a i i).continuousOn
  have hqcont : ContinuousOn q K := by
    dsimp [q]
    exact hentry.comp hpcont hpmem
  obtain ⟨B, hB0, hB⟩ := (hKcompact.bddAbove_image hqcont).exists_ge 0
  refine ⟨B, hB0, ?_⟩
  intro y hy
  have hbound : q y ≤ B := hB (q y) (Set.mem_image_of_mem q hy)
  have hqeq : q y = ω₀.toRiemannianMetric.inner (p y)
      (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) a i (p y))
      (CalabiYau.Tensor.Coordinates.chartBasisVecFiber (I := I) a i (p y)) := by
    simp [q, CalabiYau.Tensor.Coordinates.chartGramMatrix]
  rw [hqeq] at hbound
  simpa [p, I, E, c] using hbound

/-- On a compact subset of a realified complex chart, each coordinate derivative is bounded
pointwise by a uniform multiple of the Kähler gradient energy. The estimate is uniform over all
smooth real-valued functions. -/
theorem chartLocal_derivative_sq_le_gradNormSq
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M]
    [CompactSpace M] [SigmaCompactSpace M]
    (ω₀ : KahlerForm n M)
    (a : M)
    (K : Set (EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))))
    (hKcompact : IsCompact K)
    (hK : K ⊆ Sobolev.Chart.chartTargetEuclid
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) a)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f' : M → ℝ),
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f' →
        ∀ y ∈ K,
          (fderiv ℝ
            (fun z => f' ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
              ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
            (EuclideanSpace.single i 1)) ^ 2 ≤
          C * ω₀.gradNormSq f'
            ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
              ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)) := by
  classical
  obtain ⟨B, hBnonneg, hB⟩ :=
    exists_uniform_chart_basis_metric_bound ω₀ a K hKcompact hK i
  refine ⟨2 * B, mul_nonneg (by norm_num) hBnonneg, ?_⟩
  intro f' hf' y hy
  let x := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
    ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm y)
  let g := ω₀.toRiemannianMetric
  let v := CalabiYau.Tensor.Coordinates.chartBasisVecFiber
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) a i x
  have hderiv :
      (fderiv ℝ
        (fun z => f' ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) a).symm
          ((toEuclidean (E := EuclideanSpace ℂ (Fin n))).symm z))) y
        (EuclideanSpace.single i 1)) =
        g.inner x (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f' x) v := by
    rw [realified_coordinate_derivative_eq_mfderiv a f' hf' i y (hK hy)]
    exact (CalabiYau.Riemannian.inner_gradFun
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f' x v).symm
  have hCS := riemannian_inner_cauchy_schwarz_sq
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g x
    (CalabiYau.Riemannian.gradFun
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f' x) v
  rw [hderiv]
  have henergy := ω₀.riemannian_gradFun_energy_eq_two_mul_gradNormSq f' hf' x
  have hv_nonneg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  have hgrad_nonneg : 0 ≤ 2 * ω₀.gradNormSq f' x :=
    mul_nonneg (by norm_num) (ω₀.gradNormSq_nonneg f' x)
  have hmetric_bound := hB y hy
  calc
    (g.inner x (CalabiYau.Riemannian.gradFun
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f' x) v) ^ 2 ≤
        g.inner x (CalabiYau.Riemannian.gradFun
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f' x)
          (CalabiYau.Riemannian.gradFun
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f' x) * g.inner x v v := hCS
    _ ≤ (2 * ω₀.gradNormSq f' x) * B :=
      mul_le_mul henergy.le hmetric_bound hv_nonneg hgrad_nonneg
    _ = (2 * B) * ω₀.gradNormSq f' x := by ring

end KahlerForm
