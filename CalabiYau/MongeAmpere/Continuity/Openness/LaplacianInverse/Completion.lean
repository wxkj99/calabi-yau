module

public import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.PoissonInverse

/-!
# Completed Poisson inverse laws

Given the already-constructed bounded forward map and bounded smooth mean-zero Poisson solver,
extend the inverse map to the concrete mean-zero little-Hölder completion. Smooth mean-zero cores
are dense at both orders; the order-two density uses positive total volume. Faithfulness of both
evaluation maps lets pointwise identities identify completed elements.

The completed forward-evaluation identity is not stated here. That requires a
separate quantitative second-jet compatibility result, proved in
`ForwardEvaluation` rather than hidden inside the inverse-law proof.

As a flat complex-dimension-one check, on the unit flat torus the mean-zero mode
`cos (2πx)` has `Δω cos (2πx) = -π² cos (2πx)`, and the normalized inverse is multiplication by
`-π⁻²`. Thus neither inverse law may carry an extra constant mode.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- Given the completed forward map, the bounded smooth Poisson inverse extends to a continuous
linear map on the target completion, inverse to the forward map on both sides. -/
theorem exists_completed_poisson_inverse_laws [Nonempty M]
    (ω₁ : KahlerForm n M) (α : ℝ≥0)
    [P : ContinuityHolderPair ω₁ α]
    (hEvalC2 : Function.Injective P.evalC2)
    (hEvalC0 : Function.Injective P.evalC0)
    (hPoissonInverse : HasBoundedSmoothMeanZeroPoissonInverse ω₁
      P.finiteChartCover α)
    (A : P.C2 →L[ℝ] P.C0)
    (hAeval : ∀ u, P.evalC0 (A u) = ω₁.laplacian (P.evalC2 u))
    (hSmoothDense : closure (Set.range fun f :
      smoothMeanZeroChartHolderCore ω₁ P.finiteChartCover 0 α P.normedDataC0 =>
        ((f : SmoothChartHolderCore P.finiteChartCover 0 α) :
          LittleHolder P.finiteChartCover 0 α P.normedDataC0)) =
      (P.C0 : Set (LittleHolder P.finiteChartCover 0 α P.normedDataC0)))
    (hvol : 0 < ω₁.volume.real Set.univ) :
    ∃ B : P.C0 →L[ℝ] P.C2,
      (∀ u, B (A u) = u) ∧ (∀ f, A (B f) = f) := by
  classical
  let cover := P.finiteChartCover
  let N₂ := P.normedDataC2
  let N₀ := P.normedDataC0
  let : NormedAddCommGroup (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 2 α N₂
  let : NormedSpace ℝ (SmoothChartHolderCore cover 2 α) :=
    smoothChartHolderCoreNormedSpace cover 2 α N₂
  let : NormedAddCommGroup (SmoothChartHolderCore cover 0 α) :=
    smoothChartHolderCoreNormedAddCommGroup cover 0 α N₀
  let : NormedSpace ℝ (SmoothChartHolderCore cover 0 α) :=
    smoothChartHolderCoreNormedSpace cover 0 α N₀
  have hTcore₀ (f : SmoothChartHolderCore cover 0 α) :
      littleHolderMeanFunctional ω₁ cover 0 α N₀
          (f : LittleHolder cover 0 α N₀) =
        (continuousVolumeIntegralCLM ω₁)
          (smoothChartHolderContinuousMapLinearMap cover 0 α f) := by
    simp [littleHolderMeanFunctional, smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  have hTcore₂ (f : SmoothChartHolderCore cover 2 α) :
      littleHolderMeanFunctional ω₁ cover 2 α N₂
          (f : LittleHolder cover 2 α N₂) =
        (continuousVolumeIntegralCLM ω₁)
          (smoothChartHolderContinuousMapLinearMap cover 2 α f) := by
    simp [littleHolderMeanFunctional, smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  have hMeanMap (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
      (continuousVolumeIntegralCLM ω₁)
        (smoothChartHolderContinuousMapLinearMap cover 0 α
          (f : SmoothChartHolderCore cover 0 α)) = 0 := by
    change ((continuousVolumeIntegralCLM ω₁).comp
      (smoothChartHolderContinuousMapCLM cover 0 α N₀)).toLinearMap f = 0
    exact f.property
  have hMeanZeroUnique {u v : M → ℝ}
      (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
      (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v)
      (hum : ∫ x, u x ∂ω₁.volume = 0) (hvm : ∫ x, v x ∂ω₁.volume = 0)
      (hlap : ω₁.laplacian u = ω₁.laplacian v) : u = v := by
    obtain ⟨c, hc⟩ := ω₁.eq_add_const_of_laplacian_eq hu hv hlap
    have uint : Integrable u ω₁.volume :=
      hu.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)
    have hintEq : ∫ x, v x ∂ω₁.volume = ∫ x, u x ∂ω₁.volume +
        ∫ _ : M, c ∂ω₁.volume := by
      calc
        ∫ x, v x ∂ω₁.volume = ∫ x, u x + c ∂ω₁.volume := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hc x
        _ = _ := integral_add uint (integrable_const c)
    have hc0 : c = 0 := by
      have hmul : c * ω₁.volume.real Set.univ = 0 := by
        simpa [hvm, hum, integral_const, smul_eq_mul, mul_comm] using hintEq
      exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hvol)
    funext x
    rw [hc x, hc0, add_zero]
  rcases hPoissonInverse with ⟨C, hPoisson⟩
  let pick (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) : M → ℝ :=
    Classical.choose (hPoisson (f : SmoothChartHolderCore cover 0 α).smoothMap
      (f : SmoothChartHolderCore cover 0 α).smoothMap.contMDiff
      (by
        have hf := hMeanMap f
        simpa [continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
          boundedContinuousVolumeIntegralLinearMap,
          smoothChartHolderContinuousMapLinearMap] using hf))
  have pick_spec (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (pick f) ∧
      (∫ x, pick f x ∂ω₁.volume = 0) ∧
      ω₁.laplacian (pick f) = (f : SmoothChartHolderCore cover 0 α).smoothMap ∧
      finiteChartHolderGauge cover 2 α (pick f) < ⊤ ∧
      finiteChartHolderGauge cover 0 α (f : SmoothChartHolderCore cover 0 α).smoothMap < ⊤ ∧
      (finiteChartHolderGauge cover 2 α (pick f)).toReal ≤
        (C : ℝ) * (finiteChartHolderGauge cover 0 α
          (f : SmoothChartHolderCore cover 0 α).smoothMap).toReal := by
    exact (Classical.choose_spec (hPoisson
      (f : SmoothChartHolderCore cover 0 α).smoothMap
      (f : SmoothChartHolderCore cover 0 α).smoothMap.contMDiff
      (by
        have hf := hMeanMap f
        simpa [continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
          boundedContinuousVolumeIntegralLinearMap,
          smoothChartHolderContinuousMapLinearMap] using hf))).1
  let out (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) : P.C2 :=
    ⟨((⟨⟨pick f, (pick_spec f).1⟩⟩ : SmoothChartHolderCore cover 2 α) :
        LittleHolder cover 2 α N₂), by
      change littleHolderMeanFunctional ω₁ cover 2 α N₂
        ((⟨⟨pick f, (pick_spec f).1⟩⟩ : SmoothChartHolderCore cover 2 α) :
          LittleHolder cover 2 α N₂) = 0
      rw [hTcore₂]
      simpa [continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
        boundedContinuousVolumeIntegralLinearMap,
        smoothChartHolderContinuousMapLinearMap] using (pick_spec f).2.1⟩
  have hpoint₂ (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
      P.evalC2 (out f) = pick f := by
    funext x
    simp [ContinuityHolderPair.evalC2, out,
      littleHolderMeanZeroEvaluationCLM,
      smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  let L : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀ →ₗ[ℝ] P.C2 :=
    { toFun := out
      map_add' := by
        intro f g
        apply hEvalC2
        rw [map_add, hpoint₂ (f + g), hpoint₂ f, hpoint₂ g]
        apply hMeanZeroUnique
          (pick_spec (f + g)).1 ((pick_spec f).1.add (pick_spec g).1)
          (pick_spec (f + g)).2.1
          (by
            have hf : Integrable (pick f) ω₁.volume :=
              (pick_spec f).1.continuous.integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace (pick f))
            have hg : Integrable (pick g) ω₁.volume :=
              (pick_spec g).1.continuous.integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace (pick g))
            change (∫ x, pick f x + pick g x ∂ω₁.volume) = 0
            rw [integral_add hf hg, (pick_spec f).2.1, (pick_spec g).2.1]
            simp)
          (by
            calc
              ω₁.laplacian (pick (f + g)) =
                  ((f + g : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
                    SmoothChartHolderCore cover 0 α).smoothMap :=
                (pick_spec (f + g)).2.2.1
              _ = (f : SmoothChartHolderCore cover 0 α).smoothMap +
                  (g : SmoothChartHolderCore cover 0 α).smoothMap := rfl
              _ = ω₁.laplacian (pick f) + ω₁.laplacian (pick g) := by
                rw [← (pick_spec f).2.2.1, ← (pick_spec g).2.2.1]
              _ = ω₁.laplacian (pick f + pick g) :=
                (ω₁.laplacian_add (pick_spec f).1 (pick_spec g).1).symm)
      map_smul' := by
        intro r f
        apply hEvalC2
        rw [map_smul, hpoint₂ (r • f), hpoint₂ f]
        apply hMeanZeroUnique
          (pick_spec (r • f)).1 (by
            change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
              (fun x => r * pick f x)
            exact contMDiff_const.mul (pick_spec f).1)
          (pick_spec (r • f)).2.1
          (by
            have hf : Integrable (pick f) ω₁.volume :=
              (pick_spec f).1.continuous.integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace (pick f))
            change (∫ x, r * pick f x ∂ω₁.volume) = 0
            rw [integral_const_mul, (pick_spec f).2.1]
            simp)
          (by
            calc
              ω₁.laplacian (pick (r • f)) =
                  ((r • f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
                    SmoothChartHolderCore cover 0 α).smoothMap :=
                (pick_spec (r • f)).2.2.1
              _ = r • (f : SmoothChartHolderCore cover 0 α).smoothMap := rfl
              _ = ω₁.laplacian (r • pick f) := by
                rw [ω₁.laplacian_smul (pick_spec f).1 r,
                  (pick_spec f).2.2.1]) }
  have hBound (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
      ‖L f‖ ≤ (C : ℝ) * ‖f‖ := by
    dsimp [L, out]
    change ‖((⟨⟨pick f, (pick_spec f).1⟩⟩ : SmoothChartHolderCore cover 2 α) :
        LittleHolder cover 2 α N₂)‖ ≤ (C : ℝ) * ‖f‖
    rw [UniformSpace.Completion.norm_coe,
      smoothChartHolderCore_norm_eq_gauge cover 2 α N₂ ⟨⟨pick f, (pick_spec f).1⟩⟩]
    have hfNorm : ‖f‖ =
        (finiteChartHolderGauge cover 0 α
          (f : SmoothChartHolderCore cover 0 α).smoothMap).toReal := by
      change ‖(f : SmoothChartHolderCore cover 0 α)‖ = _
      exact smoothChartHolderCore_norm_eq_gauge cover 0 α N₀
        (f : SmoothChartHolderCore cover 0 α)
    rw [hfNorm]
    exact (pick_spec f).2.2.2.2.2
  let Lc : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀ →L[ℝ] P.C2 :=
    L.mkContinuous C hBound
  let e : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀ →ₗ[ℝ] P.C0 :=
    { toFun := fun f =>
        ⟨((f : SmoothChartHolderCore cover 0 α) : LittleHolder cover 0 α N₀), by
          change littleHolderMeanFunctional ω₁ cover 0 α N₀
            ((f : SmoothChartHolderCore cover 0 α) : LittleHolder cover 0 α N₀) = 0
          rw [hTcore₀]
          exact hMeanMap f⟩
      map_add' := by intro f g; apply Subtype.ext; simp [UniformSpace.Completion.coe_add]
      map_smul' := by intro r f; apply Subtype.ext; simp [UniformSpace.Completion.coe_smul] }
  have hDense : DenseRange e := by
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_iff_forall.2
    intro x
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hx : (x : LittleHolder cover 0 α N₀) ∈ closure (Set.range fun f :
        smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀ =>
          ((f : SmoothChartHolderCore cover 0 α) : LittleHolder cover 0 α N₀)) := by
      rw [hSmoothDense]
      exact x.property
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hx ε hε
    rcases hy with ⟨f, rfl⟩
    refine ⟨e f, ⟨f, rfl⟩, ?_⟩
    convert hdist using 1 ; simp [e, Subtype.dist_eq]
  have hBoundE (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
      ‖L f‖ ≤ (C : ℝ) * ‖e f‖ := by
    have heNorm : ‖e f‖ = ‖f‖ := by
      simp [e, UniformSpace.Completion.norm_coe,
        smoothChartHolderCore_norm_eq_gauge cover 0 α N₀]
    rw [heNorm]
    exact hBound f
  let B : P.C0 →L[ℝ] P.C2 := Lc.toLinearMap.extendOfNorm e
  have hBcore (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
      B (e f) = out f := by
    change Lc.toLinearMap.extendOfNorm e (e f) = Lc f
    exact LinearMap.extendOfNorm_eq hDense ⟨C, by simpa [Lc] using hBoundE⟩ f
  have hSmoothDense₂ :
      closure (Set.range fun f : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂ =>
        ((f : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N₂)) =
        (P.C2 : Set (LittleHolder cover 2 α N₂)) := by
    classical
    let T₂ := littleHolderMeanFunctional ω₁ cover 2 α N₂
    let oneCore : SmoothChartHolderCore cover 2 α :=
      ⟨ContMDiffMap.const (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
        (I' := modelWithCornersSelf ℝ ℝ) (M := M) (M' := ℝ) (n := ∞) 1⟩
    let oneComp : LittleHolder cover 2 α N₂ := oneCore
    let V : ℝ := ω₁.volume.real Set.univ
    have hTone : T₂ oneComp = V := by
      simp [T₂, oneComp, oneCore, littleHolderMeanFunctional,
        continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
        boundedContinuousVolumeIntegralLinearMap,
        smoothChartHolderContinuousMapExtension_coe,
        smoothChartHolderContinuousMapLinearMap]
      change (∫ _ : M, (1 : ℝ) ∂ω₁.volume) = V
      rw [integral_const, smul_eq_mul, mul_one]
    let A₂ : SmoothChartHolderCore cover 2 α →ₗ[ℝ] ℝ :=
      (continuousVolumeIntegralCLM ω₁).toLinearMap.comp
        (smoothChartHolderContinuousMapLinearMap cover 2 α)
    let Q₂ : LittleHolder cover 2 α N₂ →L[ℝ] LittleHolder cover 2 α N₂ :=
      ContinuousLinearMap.id ℝ _ - (V⁻¹) • T₂.smulRight oneComp
    have hQker (x : LittleHolder cover 2 α N₂)
        (hx : T₂ x = 0) : Q₂ x = x := by
      simp [Q₂, hx]
    have hQcore (f : SmoothChartHolderCore cover 2 α) :
        Q₂ (f : LittleHolder cover 2 α N₂) ∈
          Set.range (fun g : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂ =>
            ((g : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N₂)) := by
      let g : SmoothChartHolderCore cover 2 α :=
        f - (V⁻¹ * T₂ (f : LittleHolder cover 2 α N₂)) • oneCore
      have hAf : A₂ f = T₂ (f : LittleHolder cover 2 α N₂) := (hTcore₂ f).symm
      have hAone : A₂ oneCore = V := by
        calc
          A₂ oneCore = T₂ (oneCore : LittleHolder cover 2 α N₂) :=
            (hTcore₂ oneCore).symm
          _ = V := hTone
      have hgmean : A₂ g = 0 := by
        rw [map_sub, map_smul, hAf, hAone]
        simp
        field_simp [V, ne_of_gt hvol]
        ring
      have hg : g ∈ smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂ := by
        change A₂ g = 0
        exact hgmean
      refine ⟨⟨g, hg⟩, ?_⟩
      change (g : LittleHolder cover 2 α N₂) = Q₂ (f : LittleHolder cover 2 α N₂)
      let inc : SmoothChartHolderCore cover 2 α →L[ℝ] LittleHolder cover 2 α N₂ :=
        UniformSpace.Completion.toComplL
      change inc (f - (V⁻¹ * T₂ (f : LittleHolder cover 2 α N₂)) • oneCore) =
        (f : LittleHolder cover 2 α N₂) -
          V⁻¹ • (T₂ (f : LittleHolder cover 2 α N₂) • oneComp)
      rw [inc.map_sub, inc.map_smul, smul_smul]
      simp [inc, oneComp]
    have hdense : Dense (Set.range fun f : SmoothChartHolderCore cover 2 α =>
        (f : LittleHolder cover 2 α N₂)) :=
      UniformSpace.Completion.denseRange_coe
    have hQimage : Set.range (Q₂ : LittleHolder cover 2 α N₂ → LittleHolder cover 2 α N₂) ⊆
        closure (Q₂ '' Set.range (fun f : SmoothChartHolderCore cover 2 α =>
          (f : LittleHolder cover 2 α N₂))) :=
      Q₂.continuous.range_subset_closure_image_dense hdense
    apply le_antisymm
    · apply closure_minimal
      · intro x hx
        rcases hx with ⟨f, rfl⟩
        change T₂ (f : LittleHolder cover 2 α N₂) = 0
        rw [hTcore₂]
        change A₂ f = 0
        exact f.property
      · exact T₂.isClosed_ker
    · intro x hx
      have hxT : T₂ x = 0 := by
        exact hx
      have hxQ : Q₂ x = x := hQker x hxT
      have hxRange : x ∈ closure (Q₂ '' Set.range (fun f : SmoothChartHolderCore cover 2 α =>
          (f : LittleHolder cover 2 α N₂))) := by
        rw [← hxQ]
        exact hQimage ⟨x, rfl⟩
      refine closure_mono ?_ hxRange
      rintro y ⟨z, hz, rfl⟩
      rcases hz with ⟨f, rfl⟩
      exact hQcore f
  let e₂ : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂ →ₗ[ℝ] P.C2 :=
    { toFun := fun f =>
        ⟨((f : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N₂), by
          change littleHolderMeanFunctional ω₁ cover 2 α N₂
            ((f : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N₂) = 0
          rw [hTcore₂]
          have hf : (continuousVolumeIntegralCLM ω₁)
              (smoothChartHolderContinuousMapLinearMap cover 2 α
                (f : SmoothChartHolderCore cover 2 α)) = 0 := by
            change ((continuousVolumeIntegralCLM ω₁).comp
              (smoothChartHolderContinuousMapCLM cover 2 α N₂)).toLinearMap f = 0
            exact f.property
          exact hf⟩
      map_add' := by intro f g; apply Subtype.ext; simp [UniformSpace.Completion.coe_add]
      map_smul' := by intro r f; apply Subtype.ext; simp [UniformSpace.Completion.coe_smul] }
  have hDense₂ : DenseRange e₂ := by
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_iff_forall.2
    intro x
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hx : (x : LittleHolder cover 2 α N₂) ∈ closure (Set.range fun f :
        smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂ =>
          ((f : SmoothChartHolderCore cover 2 α) : LittleHolder cover 2 α N₂)) := by
      rw [hSmoothDense₂]
      exact x.property
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hx ε hε
    rcases hy with ⟨f, rfl⟩
    refine ⟨e₂ f, ⟨f, rfl⟩, ?_⟩
    convert hdist using 1 ; simp [e₂, Subtype.dist_eq]
  have hpoint₀ (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
      P.evalC0 (e f) = (f : SmoothChartHolderCore cover 0 α).smoothMap := by
    funext x
    simp [ContinuityHolderPair.evalC0, e,
      littleHolderMeanZeroEvaluationCLM,
      smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  have hpoint₂core (f : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂) :
      P.evalC2 (e₂ f) = (f : SmoothChartHolderCore cover 2 α).smoothMap := by
    funext x
    simp [ContinuityHolderPair.evalC2, e₂,
      littleHolderMeanZeroEvaluationCLM,
      smoothChartHolderContinuousMapExtension_coe,
      smoothChartHolderContinuousMapLinearMap]
  have hMeanMap₂ (f : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂) :
      (continuousVolumeIntegralCLM ω₁)
        (smoothChartHolderContinuousMapLinearMap cover 2 α
          (f : SmoothChartHolderCore cover 2 α)) = 0 := by
    change ((continuousVolumeIntegralCLM ω₁).comp
      (smoothChartHolderContinuousMapCLM cover 2 α N₂)).toLinearMap f = 0
    exact f.property
  have hMeanInt₂ (f : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂) :
      ∫ x, (f : SmoothChartHolderCore cover 2 α).smoothMap x ∂ω₁.volume = 0 := by
    simpa [continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
      boundedContinuousVolumeIntegralLinearMap,
      smoothChartHolderContinuousMapLinearMap] using hMeanMap₂ f
  let lapCore (f : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂) :
      smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀ :=
    ⟨⟨⟨ω₁.laplacian (f : SmoothChartHolderCore cover 2 α).smoothMap,
        ω₁.contMDiff_laplacian (f : SmoothChartHolderCore cover 2 α).smoothMap.contMDiff⟩⟩,
      by
        change ((continuousVolumeIntegralCLM ω₁).comp
          (smoothChartHolderContinuousMapCLM cover 0 α N₀)).toLinearMap
            ⟨⟨ω₁.laplacian (f : SmoothChartHolderCore cover 2 α).smoothMap,
              ω₁.contMDiff_laplacian (f : SmoothChartHolderCore cover 2 α).smoothMap.contMDiff⟩⟩ = 0
        simpa [continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
          boundedContinuousVolumeIntegralLinearMap, smoothChartHolderContinuousMapCLM,
          smoothChartHolderContinuousMapLinearMap] using
            ω₁.integral_laplacian (f : SmoothChartHolderCore cover 2 α).smoothMap.contMDiff⟩
  have hA_lap (f : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂) :
      A (e₂ f) = e (lapCore f) := by
    apply hEvalC0
    calc
      P.evalC0 (A (e₂ f)) =
          ω₁.laplacian (P.evalC2 (e₂ f)) := hAeval (e₂ f)
      _ = ω₁.laplacian (f : SmoothChartHolderCore cover 2 α).smoothMap := by
        rw [hpoint₂core]
      _ = P.evalC0 (e (lapCore f)) := by
        rw [hpoint₀]
        rfl
  have hABcore (f : smoothMeanZeroChartHolderCore ω₁ cover 0 α N₀) :
      A (B (e f)) = e f := by
    apply hEvalC0
    calc
      P.evalC0 (A (B (e f))) =
          ω₁.laplacian (P.evalC2 (B (e f))) := hAeval (B (e f))
      _ = ω₁.laplacian (P.evalC2 (out f)) := by rw [hBcore f]
      _ = ω₁.laplacian (pick f) := by rw [hpoint₂ f]
      _ = (f : SmoothChartHolderCore cover 0 α).smoothMap := (pick_spec f).2.2.1
      _ = P.evalC0 (e f) := (hpoint₀ f).symm
  have hAB : ∀ f : P.C0, A (B f) = f := by
    intro f
    refine hDense.induction ?_ ?_ f
    · rintro _ ⟨g, rfl⟩
      exact hABcore g
    · exact isClosed_eq (by fun_prop) continuous_id
  have hBAcore (f : smoothMeanZeroChartHolderCore ω₁ cover 2 α N₂) :
      B (A (e₂ f)) = e₂ f := by
    apply hEvalC2
    calc
      P.evalC2 (B (A (e₂ f))) = P.evalC2 (out (lapCore f)) := by
        rw [hA_lap f, hBcore (lapCore f)]
      _ = pick (lapCore f) := hpoint₂ (lapCore f)
      _ = (f : SmoothChartHolderCore cover 2 α).smoothMap := by
        apply hMeanZeroUnique (pick_spec (lapCore f)).1
          (f : SmoothChartHolderCore cover 2 α).smoothMap.contMDiff
          (pick_spec (lapCore f)).2.1 (hMeanInt₂ f)
        rw [(pick_spec (lapCore f)).2.2.1]
        rfl
      _ = P.evalC2 (e₂ f) := (hpoint₂core f).symm
  have hBA : ∀ u : P.C2, B (A u) = u := by
    intro u
    refine hDense₂.induction ?_ ?_ u
    · rintro _ ⟨f, rfl⟩
      exact hBAcore f
    · exact isClosed_eq (by fun_prop) continuous_id
  exact ⟨B, hBA, hAB⟩

end KahlerForm
