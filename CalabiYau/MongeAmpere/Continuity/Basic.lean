module

public import CalabiYau.MongeAmpere.Operator

/-!
# The continuity path

To solve `(ω₀ + i∂∂̄φ)ⁿ = e^F ω₀ⁿ` we follow Yau's continuity method along

  `(ω₀ + i∂∂̄φₜ)ⁿ = e^{tF + cₜ} ω₀ⁿ`,  `t ∈ [0, 1]`,

where `cₜ = log (∫ ω₀ⁿ / ∫ e^{tF} ω₀ⁿ)` (`KahlerForm.pathConstant`) is the constant making the
right-hand side have the correct total mass. `KahlerForm.continuitySet ω₀ F ⊆ [0, 1]` is the set
of times at which a smooth solution exists. It contains `0` (`φ₀ = 0`), and when
`∫ e^F ω₀ⁿ = ∫ ω₀ⁿ`, `c₁ = 0`, so `1` belongs to it iff the original equation is solvable. The
continuity method shows that it is open (`Continuity/Openness`) and closed
(`Continuity/Closedness`) in `[0, 1]`.
-/

@[expose] public section

open scoped Manifold ContDiff Topology
open Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [SigmaCompactSpace M] (ω₀ : KahlerForm n M)

/-- The normalizing constant `cₜ = log (∫ ω₀ⁿ / ∫ e^{tF} ω₀ⁿ)` of the continuity path. -/
noncomputable def pathConstant (F : M → ℝ) (t : ℝ) : ℝ :=
  Real.log (ω₀.volume.real univ / ∫ x, Real.exp (t * F x) ∂ω₀.volume)

/-- The times `t ∈ [0, 1]` for which `(ω₀ + i∂∂̄φ)ⁿ = e^{tF + cₜ} ω₀ⁿ` has a smooth solution. -/
def continuitySet (F : M → ℝ) : Set ℝ :=
  {t | t ∈ Icc (0 : ℝ) 1 ∧
    ∃ φ : M → ℝ, ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ}

variable {ω₀} [CompactSpace M] {F : M → ℝ}

/-- The right-hand side along the path has the correct total mass. -/
theorem integral_exp_path [Nonempty M]
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F) (t : ℝ) :
    ∫ x, Real.exp (t * F x + ω₀.pathConstant F t) ∂ω₀.volume = ω₀.volume.real univ := by
  let g : M → ℝ := fun x ↦ Real.exp (t * F x)
  have hFc : Continuous F := hF.continuous
  have hg_cont : Continuous g := by
    change Continuous (fun x : M ↦ Real.exp (t * F x))
    exact Real.continuous_exp.comp (continuous_const.mul hFc)
  have hg_int : Integrable g ω₀.volume :=
    hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have hg_pos : 0 < ∫ x, g x ∂ω₀.volume := by
    simpa [g] using (integral_exp_pos (μ := ω₀.volume) (f := fun x ↦ t * F x) hg_int)
  have hv_pos : 0 < ω₀.volume.real univ := by
    have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₀.volume := by
      simpa only [Real.exp_zero] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : M ↦ (1 : ℝ)) ω₀.volume)
    have h := integral_exp_pos (μ := ω₀.volume) (f := fun _ : M ↦ (0 : ℝ))
      hint
    simp_all
  have hc : Real.exp (ω₀.pathConstant F t) = ω₀.volume.real univ / ∫ x, g x ∂ω₀.volume := by
    rw [pathConstant, Real.exp_log (div_pos hv_pos hg_pos)]
  have heq : (fun x ↦ Real.exp (t * F x + ω₀.pathConstant F t)) =
      fun x ↦ g x * Real.exp (ω₀.pathConstant F t) := by
    funext x
    simp [g, Real.exp_add]
  calc
    ∫ x, Real.exp (t * F x + ω₀.pathConstant F t) ∂ω₀.volume
        = ∫ x, g x * Real.exp (ω₀.pathConstant F t) ∂ω₀.volume := by rw [heq]
    _ = (∫ x, g x ∂ω₀.volume) * Real.exp (ω₀.pathConstant F t) := by
      rw [integral_mul_const]
    _ = ω₀.volume.real univ := by
      rw [hc]
      field_simp

theorem continuous_pathConstant [Nonempty M]
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F) :
    Continuous (ω₀.pathConstant F) := by
  have hFc : Continuous F := hF.continuous
  have h_integrand : Continuous (Function.uncurry fun (t : ℝ) (x : M) ↦ Real.exp (t * F x)) := by
    change Continuous (fun p : ℝ × M ↦ Real.exp (p.1 * F p.2))
    exact Real.continuous_exp.comp (continuous_fst.mul (hFc.comp continuous_snd))
  have h_integral_cont : Continuous (fun t ↦ ∫ x, Real.exp (t * F x) ∂ω₀.volume) := by
    simpa using (continuous_parametric_integral_of_continuous h_integrand
      (isCompact_univ : IsCompact (Set.univ : Set M)))
  have h_integral_pos : ∀ t, 0 < ∫ x, Real.exp (t * F x) ∂ω₀.volume := by
    intro t
    apply integral_exp_pos
    have hc : Continuous fun x : M ↦ Real.exp (t * F x) :=
      Real.continuous_exp.comp (continuous_const.mul hFc)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h_ratio_cont : Continuous (fun t ↦ ω₀.volume.real univ /
      ∫ x, Real.exp (t * F x) ∂ω₀.volume) :=
    continuous_const.div h_integral_cont fun t ↦ ne_of_gt (h_integral_pos t)
  have h_vol_pos : 0 < ω₀.volume.real univ := by
    have hint : Integrable (fun x : M ↦ Real.exp ((0 : ℝ) : ℝ)) ω₀.volume := by
      simpa only [Real.exp_zero] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : M ↦ (1 : ℝ)) ω₀.volume)
    have h := integral_exp_pos (μ := ω₀.volume) (f := fun _ : M ↦ (0 : ℝ)) hint
    simp_all
  have h_ratio_pos : ∀ t, 0 < ω₀.volume.real univ /
      ∫ x, Real.exp (t * F x) ∂ω₀.volume := fun t ↦
        div_pos h_vol_pos (h_integral_pos t)
  have h_log_cont : Continuous (fun t ↦ Real.log
      (ω₀.volume.real univ / ∫ x, Real.exp (t * F x) ∂ω₀.volume)) :=
    h_ratio_cont.log fun t ↦ ne_of_gt (h_ratio_pos t)
  change Continuous (fun t : ℝ ↦ Real.log
    (ω₀.volume.real univ / ∫ x, Real.exp (t * F x) ∂ω₀.volume))
  exact h_log_cont

omit [BorelSpace M] [CompactSpace M] in
@[simp]
theorem pathConstant_zero [Nonempty M] : ω₀.pathConstant F 0 = 0 := by
  simp [pathConstant, integral_const]

omit [BorelSpace M] [CompactSpace M] in
theorem pathConstant_one (hF : ∫ x, Real.exp (F x) ∂ω₀.volume = ω₀.volume.real univ) :
    ω₀.pathConstant F 1 = 0 := by
  by_cases hv : ω₀.volume.real univ = 0
  · simp [pathConstant, hF, hv]
  · simp [pathConstant, hF, hv]

omit [BorelSpace M] [CompactSpace M] in
/-- `t = 0` is solved by `φ = 0`. -/
theorem zero_mem_continuitySet [Nonempty M] : 0 ∈ ω₀.continuitySet F := by
  refine ⟨by simp, 0, ?_⟩
  refine ⟨ω₀.isPotential_zero, ?_⟩
  intro x
  simp [pathConstant_zero]

omit [BorelSpace M] [CompactSpace M] in
/-- For normalized `F`, reaching `t = 1` solves the original equation. -/
theorem solvesMongeAmpere_of_one_mem_continuitySet
    (hF : ∫ x, Real.exp (F x) ∂ω₀.volume = ω₀.volume.real univ)
    (h : 1 ∈ ω₀.continuitySet F) : ∃ φ, ω₀.SolvesMongeAmpere F φ := by
  rcases h.2 with ⟨φ, hφ⟩
  refine ⟨φ, hφ.1, ?_⟩
  intro x
  simpa [pathConstant_one hF] using hφ.2 x

omit [BorelSpace M] [CompactSpace M] in
/-- A nonempty subset of `[0, 1]` which is open in `[0, 1]` and closed contains `1`. -/
theorem one_mem_continuitySet_of_isClosed [Nonempty M]
    (hopen : ∀ t ∈ ω₀.continuitySet F, ω₀.continuitySet F ∈ 𝓝[Icc 0 1] t)
    (hclosed : IsClosed (ω₀.continuitySet F)) : 1 ∈ ω₀.continuitySet F := by
  let S : Set (Icc (0 : ℝ) 1) := Subtype.val ⁻¹' ω₀.continuitySet F
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    exact preimage_coe_mem_nhds_subtype.mpr (hopen t.1 ht)
  have hS_closed : IsClosed S := by
    dsimp [S]
    exact hclosed.preimage continuous_subtype_val
  let : ConnectedSpace (Icc (0 : ℝ) 1) :=
    Subtype.connectedSpace ⟨nonempty_Icc.mpr zero_le_one, isPreconnected_Icc⟩
  have hS_nonempty : S.Nonempty := by
    refine ⟨⟨0, by simp⟩, ?_⟩
    exact zero_mem_continuitySet
  have hS_univ : S = univ :=
    (isClopen_iff.mp ⟨hS_closed, hS_open⟩).resolve_left hS_nonempty.ne_empty
  have hone : (⟨1, by simp⟩ : Icc (0 : ℝ) 1) ∈ S := by rw [hS_univ]; simp
  simpa [S] using hone

end KahlerForm
