module

public import CalabiYau.Geometry.Kahler.Volume

/-!
# Assemble almost-everywhere constants along overlapping open neighborhoods

Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, §7.1,
and Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Ch. 4, Thm. 4.7:
constants on overlapping balls agree when open sets have positive measure; connectedness
propagates equality and compactness supplies a finite cover for the a.e. statement.
No individual chart target is assumed connected.
-/

@[expose] public section

open MeasureTheory Topology

namespace KahlerForm

private theorem ae_const_eq_of_open_overlap
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) [μ.IsOpenPosMeasure] (u : M → ℝ)
    {V W : Set M} (hV : IsOpen V) (hW : IsOpen W)
    {c d : ℝ}
    (hcv : ∀ᵐ y ∂(μ.restrict V), u y = c)
    (hdw : ∀ᵐ y ∂(μ.restrict W), u y = d)
    (hVW : (V ∩ W).Nonempty) : c = d := by
  by_contra hne
  have hv := (ae_restrict_iff' hV.measurableSet).1 hcv
  have hw := (ae_restrict_iff' hW.measurableSet).1 hdw
  have he : ∀ᵐ z ∂(μ.restrict (V ∩ W)), False := by
    apply (ae_restrict_iff' (hV.measurableSet.inter hW.measurableSet)).2
    filter_upwards [hv, hw] with z hzv hzw hzi
    exact hne ((hzv hzi.1).symm.trans (hzw hzi.2))
  have hzero : μ (V ∩ W) = 0 := by
    have := (ae_iff.mp he)
    simpa using this
  exact (hV.inter hW).measure_ne_zero μ hVW hzero

/-- A compact connected space supports one almost-everywhere constant if every point
has an open neighborhood on which the function is almost everywhere constant and every
nonempty open set has positive measure. `u` itself need not be pointwise continuous. -/
theorem ae_eq_const_of_locally_ae_const
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [CompactSpace M] [ConnectedSpace M]
    (μ : Measure M) [μ.IsOpenPosMeasure] (u : M → ℝ)
    (hlocal : ∀ a : M, ∃ V : Set M, IsOpen V ∧ a ∈ V ∧
      ∃ c : ℝ, ∀ᵐ y ∂(μ.restrict V), u y = c) :
    ∃ c : ℝ, u =ᵐ[μ] fun _ => c := by
  classical
  by_cases hM : Nonempty M
  · let V : M → Set M := fun x => Classical.choose (hlocal x)
    let c : M → ℝ := fun x => Classical.choose ((Classical.choose_spec (hlocal x)).2.2)
    have hVopen (x : M) : IsOpen (V x) :=
      (Classical.choose_spec (hlocal x)).1
    have hxV (x : M) : x ∈ V x :=
      (Classical.choose_spec (hlocal x)).2.1
    have haeV (x : M) : ∀ᵐ y ∂(μ.restrict (V x)), u y = c x := by
      exact Classical.choose_spec ((Classical.choose_spec (hlocal x)).2.2)
    have hc : IsLocallyConstant c := by
      apply (IsLocallyConstant.iff_exists_open c).2
      intro x
      refine ⟨V x, hVopen x, hxV x, ?_⟩
      intro y hy
      exact (ae_const_eq_of_open_overlap μ u (hVopen x) (hVopen y)
        (haeV x) (haeV y) ⟨y, hy, hxV y⟩).symm
    let x₀ : M := Classical.choice hM
    have hceq (x : M) : c x = c x₀ :=
      IsLocallyConstant.apply_eq_of_preconnectedSpace hc x x₀
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVopen (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨x, hxV x⟩)
    have hae : ∀ᵐ y ∂μ, ∀ i : {i // i ∈ t}, y ∈ V i → u y = c x₀ := by
      rw [ae_all_iff]
      intro i
      have hlocal' : ∀ᵐ y ∂μ, y ∈ V i → u y = c i :=
        (ae_restrict_iff' (hVopen i).measurableSet).1 (haeV i)
      filter_upwards [hlocal'] with y hy hyi
      simpa [hceq i] using hy hyi
    refine ⟨c x₀, ?_⟩
    filter_upwards [hae] with y hy
    obtain ⟨i, hit, hyi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
    exact hy ⟨i, hit⟩ hyi
  · refine ⟨0, ?_⟩
    have hE : IsEmpty M := not_nonempty_iff.mp hM
    filter_upwards [] with y
    exact isEmptyElim y

end KahlerForm
