module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization.LogDetLittleHolder

/-!
# Project the residual to the bounded mean-zero carrier

Use the bounded volume functional and the constant smooth core element to center a full little-Hölder
residual.  This is the separate mean-projection step after its nonlinear log-determinant realization.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The centered pointwise residual, obtained from the uncentered residual by subtracting its
`ω₁`-volume average. -/
noncomputable def centeredContinuityPathResidual (ω₀ : KahlerForm n M) (F : M → ℝ)
    (t : ℝ) (φ : M → ℝ) (hsol : ω₀.SolvesMongeAmpere
      (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (u : M → ℝ) (δ : ℝ) : M → ℝ :=
  let ω₁ := ω₀.perturb φ hsol.1
  let q := uncenteredContinuityPathResidual ω₀ F t φ hsol u δ
  fun x ↦ q x - (∫ y, q y ∂ω₁.volume) / ω₁.volume.real Set.univ

omit [ConnectedSpace M] in

/-- Center a full little-Hölder residual into the mean-zero kernel, preserving its pointwise
formula and the zero at the base point. -/
theorem exists_centeredResidualProjection (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (radius : ℝ)
    (Q : LittleHolderUncenteredResidualData ω₀ F hF t φ hsol α radius) :
    ∃ residual : P.C2 × ℝ → P.C0,
      (∀ (u : P.C2) (δ : ℝ), ‖u‖ < radius → ∀ x,
        P.evalC0 (residual (u, δ)) x =
          centeredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ x) ∧
      residual (0, 0) = 0 := by
  by_cases hM : Nonempty M
  · let : Nonempty M := hM
    let ω₁ := ω₀.perturb φ hsol.1
    let cover := P.finiteChartCover
    let N := P.normedDataC0
    let : NormedAddCommGroup (SmoothChartHolderCore cover 0 α) :=
      smoothChartHolderCoreNormedAddCommGroup cover 0 α N
    let : NormedSpace ℝ (SmoothChartHolderCore cover 0 α) :=
      smoothChartHolderCoreNormedSpace cover 0 α N
    let V : ℝ := ω₁.volume.real Set.univ
    let T := littleHolderMeanFunctional ω₁ cover 0 α N
    have hvol : 0 < V := by
      have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₁.volume := by
        simp
      have h := integral_exp_pos (μ := ω₁.volume) (f := fun _ : M ↦ (0 : ℝ)) hint
      simp [V]
    let oneCore : SmoothChartHolderCore cover 0 α :=
      ⟨ContMDiffMap.const (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
        (I' := modelWithCornersSelf ℝ ℝ) (M := M) (M' := ℝ) (n := ∞) 1⟩
    let oneComp : LittleHolder cover 0 α N := oneCore
    have hTone : T oneComp = V := by
      simp [T, oneComp, oneCore, V, littleHolderMeanFunctional,
        continuousVolumeIntegralCLM, boundedContinuousVolumeIntegralCLM,
        boundedContinuousVolumeIntegralLinearMap,
        smoothChartHolderContinuousMapExtension_coe,
        smoothChartHolderContinuousMapLinearMap]
      change (∫ _ : M, (1 : ℝ) ∂ω₁.volume) = V
      rw [integral_const, smul_eq_mul, mul_one]
    have hT_eval (q : LittleHolder cover 0 α N) :
        T q = ∫ y, smoothChartHolderContinuousMapExtension cover 0 α N q y ∂ω₁.volume := by
      rfl
    let residual : P.C2 × ℝ → P.C0 := fun p => by
      let q := Q.uncentered p
      refine ⟨q - (V⁻¹ * T q) • oneComp, ?_⟩
      change T (q - (V⁻¹ * T q) • oneComp) = 0
      rw [map_sub, map_smul, hTone]
      calc
        T q - (V⁻¹ * T q) * V = T q - T q := by
          congr 1
          calc
            (V⁻¹ * T q) * V = T q * (V⁻¹ * V) := by ring
            _ = T q := by rw [inv_mul_cancel₀ (ne_of_gt hvol)]; ring
        _ = 0 := sub_self _
    refine ⟨residual, ?_, ?_⟩
    · intro u δ hu x
      let q := Q.uncentered (u, δ)
      have honeval : smoothChartHolderContinuousMapExtension cover 0 α N oneComp x = 1 := by
        change smoothChartHolderContinuousMapExtension cover 0 α N
          (oneCore : SmoothChartHolderCore cover 0 α) x = 1
        rw [smoothChartHolderContinuousMapExtension_coe]
        rfl
      have hq : P.evalC0 (residual (u, δ)) x =
          smoothChartHolderContinuousMapExtension cover 0 α N q x -
            (V⁻¹ * T q) := by
        change smoothChartHolderContinuousMapExtension cover 0 α N
          (residual (u, δ)).val x = _
        simp [residual, q]
        rw [honeval]
        ring
      rw [hq]
      change smoothChartHolderContinuousMapExtension cover 0 α N q x -
          (V⁻¹ * T q) =
        uncenteredContinuityPathResidual ω₀ F t φ hsol (P.evalC2 u) δ x -
          ((∫ y, uncenteredContinuityPathResidual ω₀ F t φ hsol
            (P.evalC2 u) δ y ∂ω₁.volume) / V)
      have hIntegral :
          (∫ y, smoothChartHolderContinuousMapExtension cover 0 α N q y
            ∂ω₁.volume) =
          ∫ y, uncenteredContinuityPathResidual ω₀ F t φ hsol
            (P.evalC2 u) δ y ∂ω₁.volume := by
        apply integral_congr_ae
        filter_upwards with y
        exact Q.eval_uncentered u δ hu y
      rw [Q.eval_uncentered u δ hu x, hT_eval, hIntegral]
      simp [div_eq_mul_inv]
      ring
    · apply Subtype.ext
      simp [residual, Q.uncentered_base]
  · let : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨fun _ => 0, ?_, by simp⟩
    intro u δ hu x
    exact False.elim (hM ⟨x⟩)

end KahlerForm
