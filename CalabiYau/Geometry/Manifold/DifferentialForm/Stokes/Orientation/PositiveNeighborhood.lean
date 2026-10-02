module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.ChartCoefficient
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Positive reference-form neighborhoods and finite orientation partitions

Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 15.3,
p. 379, and Proposition 15.5, p. 381: a nonzero smooth top form has a locally
constant orientation sign. Equation (16.2), p. 405, and Proposition 16.5,
pp. 405–406, then use a finite subordinate partition for integration.

The coordinate chart is the existing canonical chart. Only the selected open
neighborhood is required to have one sign: an arbitrary disconnected canonical
chart source may have oppositely oriented components. The reference form is an
actual bundled smooth form, not a plain field or an assumed integral.

The construction records neighborhoods of constant sign together with the center
points they contain. Center membership is a property of this covering construction,
not a condition on arbitrary restricted charts or common refinements. It makes no
claim about a global integration functional, measure identification, or Stokes theorem.
-/

@[expose] public section

open Set Function
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

omit [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] in
private theorem chartAt_eq_extChartAt (x p : M) :
    (chartAt (Fin d → ℝ) x) p = (extChartAt 𝓘(ℝ, Fin d → ℝ) x) p := by
  simp [extChartAt]

omit [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M] in
private theorem chartAt_center_eq_extChartAt_center (x : M) :
    (chartAt (Fin d → ℝ) x) x = (extChartAt 𝓘(ℝ, Fin d → ℝ) x) x := by
  exact chartAt_eq_extChartAt x x

private theorem topCoeff_nonzero_of_value_nonzero
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) (x : M)
    (hη : η x ≠ 0) :
    chartTopCoefficient x η ((extChartAt 𝓘(ℝ, Fin d → ℝ) x) x) ≠ 0 := by
  classical
  unfold chartTopCoefficient
  rw [if_pos (mem_extChartAt_target x)]
  rw [continuousAlternatingMap_trivializationAt_apply]
  rw [show (extChartAt 𝓘(ℝ, Fin d → ℝ) x).symm
      ((extChartAt 𝓘(ℝ, Fin d → ℝ) x) x) = x by
        exact (extChartAt 𝓘(ℝ, Fin d → ℝ) x).left_inv (mem_extChartAt_source x)]
  let tr := trivializationAt (Fin d → ℝ) (TangentSpace 𝓘(ℝ, Fin d → ℝ)) x
  let hb : x ∈ tr.baseSet := mem_baseSet_trivializationAt (Fin d → ℝ)
    (TangentSpace 𝓘(ℝ, Fin d → ℝ)) x
  let T := tr.symmL ℝ x
  have hcomp : (η x).compContinuousLinearMap T ≠ 0 := by
    intro hzero
    have hηzero : η x = 0 := by
      apply ContinuousAlternatingMap.ext
      intro v
      change (η x) v = 0
      let u : Fin d → (Fin d → ℝ) := fun i => tr.continuousLinearMapAt ℝ x (v i)
      have hval := congrArg (fun g : (Fin d → ℝ) [⋀^Fin d]→L[ℝ] ℝ => g u) hzero
      have hv : T ∘ u = v := by
        funext i
        exact Bundle.Trivialization.symmL_continuousLinearMapAt (R := ℝ) tr hb (v i)
      have hval' : (η x) (T ∘ u) = 0 := by
        simpa [ContinuousAlternatingMap.compContinuousLinearMap_apply] using hval
      rw [hv] at hval'
      exact hval'
    exact hη hηzero
  have hmapzero : ((η x).compContinuousLinearMap T).toAlternatingMap ≠ 0 := by
    intro hz
    apply hcomp
    exact ContinuousAlternatingMap.toAlternatingMap_injective hz
  have hmap := (AlternatingMap.map_basis_ne_zero_iff
    (Pi.basisFun ℝ (Fin d)) ((η x).compContinuousLinearMap T).toAlternatingMap).2 hmapzero
  have hvec : (Pi.basisFun ℝ (Fin d) : Fin d → (Fin d → ℝ)) =
      fun i => Pi.single i 1 := by
    funext i
    exact Pi.basisFun_apply ℝ (Fin d) i
  rw [hvec] at hmap
  exact hmap

private theorem chartTopCoefficient_continuousOn_ext
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) (x : M) :
    ContinuousOn (chartTopCoefficient x η) (extChartAt 𝓘(ℝ, Fin d → ℝ) x).target := by
  let b : Fin d → (Fin d → ℝ) := fun i => Pi.single i 1
  let rep : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin d]→L[ℝ] ℝ := fun y =>
    (trivializationAt ((Fin d → ℝ) [⋀^Fin d]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin d) (Fin d → ℝ)
        (TangentSpace (𝓘(ℝ, Fin d → ℝ))) ℝ (Bundle.Trivial M ℝ)) x
      ⟨(extChartAt 𝓘(ℝ, Fin d → ℝ) x).symm y,
        η ((extChartAt 𝓘(ℝ, Fin d → ℝ) x).symm y)⟩).2
  have hrep : ContDiffOn ℝ ∞ rep (extChartAt 𝓘(ℝ, Fin d → ℝ) x).target :=
    DifferentialForm.localRep_contDiffOn η x
  have hEval : Continuous fun f : (Fin d → ℝ) [⋀^Fin d]→L[ℝ] ℝ => f b :=
    continuous_eval_const b
  have hcont : ContinuousOn (fun y => rep y b) (extChartAt 𝓘(ℝ, Fin d → ℝ) x).target :=
    hEval.comp_continuousOn hrep.continuousOn
  refine hcont.congr ?_
  intro y hy
  unfold chartTopCoefficient
  rw [if_pos hy]

private theorem chartTopCoefficient_continuousOn_chart
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) (x : M) :
    ContinuousOn (chartTopCoefficient x η) (chartAt (Fin d → ℝ) x).target := by
  simpa [extChartAt_target] using chartTopCoefficient_continuousOn_ext η x

/-- A nonzero reference top form at the chart center has positive signed
coefficient throughout some open neighborhood inside that chart. The sign is
normalized to ±1; the dimension-zero case uses scalar evaluation on the empty
basis. No compactness or connectedness hypothesis is needed locally. -/
theorem orientation_form_chart_neighborhood
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (x : M) (hνx : ν x ≠ 0) :
    ∃ (V : Set M) (σ : {s : ℝ // s = 1 ∨ s = -1}),
      And (IsOpen V) (And (x ∈ V)
        (And (V ⊆ (chartAt (Fin d → ℝ) x).source)
          (∀ p ∈ V, 0 < (σ : ℝ) *
            chartTopCoefficient x ν ((chartAt (Fin d → ℝ) x) p)))) := by
  let c := chartAt (Fin d → ℝ) x
  let c₀ := chartTopCoefficient x ν (c x)
  have hc₀ : c₀ ≠ 0 := by
    change chartTopCoefficient x ν ((chartAt (Fin d → ℝ) x) x) ≠ 0
    rw [chartAt_center_eq_extChartAt_center]
    exact topCoeff_nonzero_of_value_nonzero ν x hνx
  let s : ℝ := if 0 < c₀ then 1 else -1
  have hs : s = 1 ∨ s = -1 := by
    by_cases hp : 0 < c₀
    · left
      simp [s, hp]
    · right
      simp [s, hp]
  have hsc₀ : 0 < s * c₀ := by
    by_cases hp : 0 < c₀
    · simp [s, hp]
    · have hle : c₀ ≤ 0 := le_of_not_gt hp
      have hn : c₀ < 0 := lt_of_le_of_ne hle hc₀
      simp [s, hp, hn]
  have hcoeff := chartTopCoefficient_continuousOn_chart ν x
  have hscoeff : ContinuousOn (fun y => s * chartTopCoefficient x ν y) c.target :=
    continuousOn_const.mul hcoeff
  let W : Set (Fin d → ℝ) := c.target ∩
    (fun y => s * chartTopCoefficient x ν y) ⁻¹' Set.Ioi (0 : ℝ)
  have hW : IsOpen W := by
    dsimp [W]
    exact hscoeff.isOpen_inter_preimage c.open_target isOpen_Ioi
  let V : Set M := c.source ∩ c ⁻¹' W
  have hVopen : IsOpen V := by
    dsimp [V]
    exact c.isOpen_inter_preimage hW
  have hxV : x ∈ V := by
    refine ⟨mem_chart_source (H := Fin d → ℝ) x, ?_⟩
    change c x ∈ W
    refine ⟨c.map_source (mem_chart_source (H := Fin d → ℝ) x), ?_⟩
    change 0 < s * chartTopCoefficient x ν (c x)
    exact hsc₀
  refine ⟨V, ⟨s, hs⟩, hVopen, hxV, ?_, ?_⟩
  · exact Set.inter_subset_left
  · intro p hp
    have hWp : c p ∈ W := hp.2
    simpa using hWp.2

/-- On a compact Hausdorff manifold, an everywhere nonzero smooth reference
form supplies a finite partition whose closed supports lie in canonical-chart
neighborhoods with positive signed reference coefficient at every point.
The finite sum and center membership are valid even when the manifold is empty. -/
theorem exists_finite_orientation_form_chart_partition
    [T2Space M] [CompactSpace M]
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hν : ∀ p : M, ν p ≠ 0) :
    ∃ (V : M → Set M)
      (σ : M → {s : ℝ // s = 1 ∨ s = -1})
      (ρ : SmoothPartitionOfUnity M 𝓘(ℝ, Fin d → ℝ) M Set.univ)
      (s : Finset M),
      And (∀ x : M, And (IsOpen (V x)) (And (x ∈ V x)
        (V x ⊆ (chartAt (Fin d → ℝ) x).source)))
        (And (∀ (x p : M), p ∈ V x → 0 < (σ x : ℝ) *
          chartTopCoefficient x ν ((chartAt (Fin d → ℝ) x) p))
          (And (ρ.IsSubordinate V) (∀ p : M, ∑ i ∈ s, ρ i p = 1))) := by
  classical
  choose V σ hV using fun x : M =>
    orientation_form_chart_neighborhood ν x (hν x)
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Fin d → ℝ) isClosed_univ V (fun x => (hV x).1)
    (by
      intro p hp
      exact mem_iUnion_of_mem p (hV p).2.1)
  let fs : Set M := {i | (support (ρ i)).Nonempty}
  have hfs : fs.Finite := by
    dsimp [fs]
    exact ρ.locallyFinite.finite_nonempty_of_compact
  refine ⟨V, σ, ρ, hfs.toFinset, ?_, ?_, hρ, ?_⟩
  · intro x
    exact ⟨(hV x).1, (hV x).2.1, (hV x).2.2.1⟩
  · intro x p hp
    exact (hV x).2.2.2 p hp
  · intro p
    rw [← ρ.sum_finsupport p (mem_univ p)]
    symm
    apply Finset.sum_subset ?_ (fun i hi hnot => ?_)
    · intro i hi
      have hip : i ∈ ρ.finsupport p := hi
      have hne : (support (ρ i)).Nonempty := ⟨p, (mem_support).2 (by
        simpa [SmoothPartitionOfUnity.mem_finsupport] using hip)⟩
      exact hfs.mem_toFinset.mpr hne
    · have hip : i ∉ ρ.finsupport p := hnot
      have : ρ i p = 0 := by
        by_contra hne
        have : i ∈ ρ.finsupport p := by
          simpa [SmoothPartitionOfUnity.mem_finsupport, mem_support] using hne
        exact hip this
      simp [this]

end CalabiYau.DifferentialForm
