-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Spectral/Scalar/Enumeration.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Spectral.Scalar.EigenBasis

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

def nonzeroLaplacianEigenvalueSet (g : SmoothRiemannianMetric I M) : Set ℝ :=
  { lam : ℝ | ∃ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      μ.val < 1 ∧ laplacianEigenvalueOf μ.val = lam }

omit [NeZero (Module.finrank ℝ E)] in
theorem nonzeroLaplacianEigenvalueSet_pos
    (g : SmoothRiemannianMetric I M) {lam : ℝ}
    (h : lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) :
    0 < lam := by
  rcases h with ⟨μ, hμ_lt, hlam⟩
  rw [← hlam]
  unfold laplacianEigenvalueOf
  have h_pos : 0 < μ.val := nonzeroResolventEigenvalue_pos μ
  have h_num_pos : 0 < 1 - μ.val := by linarith
  exact div_pos h_num_pos h_pos

private lemma resolvent_val_eq_of_laplacianEigenvalueOf
    {μ : ℝ} (hμ_pos : 0 < μ) (hμ_lt : μ < 1) (lam : ℝ)
    (hlam_eq : (1 - μ) / μ = lam) :
    μ = 1 / (lam + 1) := by
  have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
  have h1 : 1 - μ = lam * μ := by
    have h2 : ((1 - μ) / μ) * μ = lam * μ := by rw [hlam_eq]
    rwa [div_mul_cancel₀ _ hμ_ne] at h2
  have h_sum : 1 = (lam + 1) * μ := by linarith
  have h_lam1_pos : 0 < lam + 1 := by
    have h_lam_nn : 0 ≤ lam := by
      rw [← hlam_eq]
      have h_num : 0 ≤ 1 - μ := by linarith
      exact div_nonneg h_num hμ_pos.le
    linarith
  have h_lam1_ne : (lam + 1 : ℝ) ≠ 0 := ne_of_gt h_lam1_pos
  field_simp
  linarith

theorem nonzeroLaplacianEigenvalueSet_finite_below
    (g : SmoothRiemannianMetric I M) (N : ℝ) :
    Set.Finite { lam : ℝ |
      lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ N } := by
  by_cases hN : 0 < N
  · set ε : ℝ := 1 / (N + 1) with hε_def
    have hN1_pos : 0 < N + 1 := by linarith
    have hε_pos : 0 < ε := by rw [hε_def]; positivity
    have h_shell_fin :
        Set.Finite { μ : ℝ |
          Module.End.HasEigenvalue
            ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧ ε ≤ |μ| } :=
      resolvent_eigenvalues_finite_above_on_closed
        (I := I) (M := M) g hε_pos
    set S : Set ℝ := { lam : ℝ |
        lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ N }
    set fmap : ℝ → ℝ := fun lam => 1 / (lam + 1) with hfmap_def
    have h_image_subset : fmap '' S ⊆
        { μ : ℝ |
          Module.End.HasEigenvalue
            ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧ ε ≤ |μ| } := by
      rintro y ⟨lam, ⟨h_lam_S, h_lam_le_N⟩, hflam⟩
      rcases h_lam_S with ⟨μ, hμ_lt, hlam_eq⟩
      have hμ_pos : 0 < μ.val := nonzeroResolventEigenvalue_pos μ
      have hμ_le_one : μ.val ≤ 1 := nonzeroResolventEigenvalue_le_one μ
      have ellipticity_pos : 0 < lam := by
        rw [← hlam_eq]
        unfold laplacianEigenvalueOf
        have h_num_pos : 0 < 1 - μ.val := by linarith
        exact div_pos h_num_pos hμ_pos
      have h_mu_eq : μ.val = 1 / (lam + 1) := by
        unfold laplacianEigenvalueOf at hlam_eq
        exact resolvent_val_eq_of_laplacianEigenvalueOf hμ_pos hμ_lt lam hlam_eq
      have h_y_eq : y = μ.val := by
        rw [← hflam, hfmap_def, h_mu_eq]
      have hlam_eq_unfold : (1 - μ.val) / μ.val = lam := by
        unfold laplacianEigenvalueOf at hlam_eq; exact hlam_eq
      refine ⟨?_, ?_⟩
      · rw [h_y_eq]; exact μ.hasEigenvalue
      · rw [h_y_eq, abs_of_pos hμ_pos]
        have h_div_le : (1 - μ.val) / μ.val ≤ N := by
          rw [hlam_eq_unfold]; exact h_lam_le_N
        have h_mul : 1 - μ.val ≤ N * μ.val := by
          have h := (div_le_iff₀ hμ_pos).mp h_div_le
          linarith
        have h_total : 1 ≤ (N + 1) * μ.val := by linarith
        rw [hε_def]
        exact (div_le_iff₀ hN1_pos).mpr (by linarith)
    have h_image_finite : (fmap '' S).Finite :=
      h_shell_fin.subset h_image_subset
    have h_inj_on : Set.InjOn fmap S := by
      intro a ha b hb hab
      have ha_pos : 0 < a := nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g ha.1
      have hb_pos : 0 < b := nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g hb.1
      have ha1_pos : 0 < a + 1 := by linarith
      have hb1_pos : 0 < b + 1 := by linarith
      have ha1_ne : (a + 1 : ℝ) ≠ 0 := ne_of_gt ha1_pos
      have hb1_ne : (b + 1 : ℝ) ≠ 0 := ne_of_gt hb1_pos
      have h_eq : (a + 1) = (b + 1) := by
        rw [hfmap_def] at hab
        field_simp at hab
        linarith
      linarith
    exact Set.Finite.of_finite_image h_image_finite h_inj_on
  · push Not at hN
    have h_empty : { lam : ℝ |
        lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ N } = ∅ := by
      ext lam
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h_in_S, h_le_N⟩
      have h_pos := nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g h_in_S
      linarith
    rw [h_empty]
    exact Set.finite_empty

theorem nonzeroLaplacianEigenvalueSet_inter_Iic_finite
    (g : SmoothRiemannianMetric I M) (N : ℝ) :
    Set.Finite ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Iic N) := by
  refine Set.Finite.subset
    (nonzeroLaplacianEigenvalueSet_finite_below (I := I) (M := M) g N) ?_
  intro lam hlam
  exact ⟨hlam.1, hlam.2⟩

noncomputable def laplacianEigenvalueAscending
    (g : SmoothRiemannianMetric I M) : ℕ → ℝ
  | 0 =>
      open Classical in
      if (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Nonempty then
        sInf (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g)
      else 0
  | n + 1 =>
      let prev := laplacianEigenvalueAscending g n
      open Classical in
      if ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
              Set.Ioi prev).Nonempty then
        sInf ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
              Set.Ioi prev)
      else 0

omit [NeZero (Module.finrank ℝ E)] in
lemma laplacianEigenvalueAscending_zero
    (g : SmoothRiemannianMetric I M) :
    laplacianEigenvalueAscending (I := I) (M := M) g 0 =
      (open Classical in
       if (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Nonempty then
         sInf (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g)
       else 0) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma laplacianEigenvalueAscending_succ
    (g : SmoothRiemannianMetric I M) (n : ℕ) :
    laplacianEigenvalueAscending (I := I) (M := M) g (n + 1) =
      (open Classical in
       if ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
            Set.Ioi (laplacianEigenvalueAscending (I := I) (M := M) g n)).Nonempty then
         sInf ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
              Set.Ioi (laplacianEigenvalueAscending (I := I) (M := M) g n))
       else 0) := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianEigenvalueAscending_zero_eq_sInf
    (g : SmoothRiemannianMetric I M)
    (h_nonempty : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Nonempty) :
    laplacianEigenvalueAscending (I := I) (M := M) g 0 =
      sInf (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) := by
  rw [laplacianEigenvalueAscending_zero, ite_eq_left h_nonempty]

private lemma csInf_mem_of_finite_slice
    {T : Set ℝ} (hT_bddBelow : BddBelow T) (a : ℝ) (ha : a ∈ T)
    (hT_slice_fin : Set.Finite (T ∩ Set.Iic a)) :
    sInf T ∈ T := by
  set Tslice : Set ℝ := T ∩ Set.Iic a
  have hTslice_nonempty : Tslice.Nonempty := ⟨a, ha, le_refl a⟩
  have h_csInf_in_slice : sInf Tslice ∈ Tslice :=
    hTslice_nonempty.csInf_mem hT_slice_fin
  have h_lb : ∀ x ∈ T, sInf Tslice ≤ x := by
    intro x hx
    by_cases hxa : x ≤ a
    · exact csInf_le hT_slice_fin.bddBelow ⟨hx, hxa⟩
    · push Not at hxa
      have h_le_a : sInf Tslice ≤ a :=
        csInf_le hT_slice_fin.bddBelow ⟨ha, le_refl a⟩
      linarith
  have h_eq : sInf T = sInf Tslice := by
    apply le_antisymm
    · exact csInf_le hT_bddBelow h_csInf_in_slice.1
    · exact le_csInf ⟨a, ha⟩ h_lb
  rw [h_eq]
  exact h_csInf_in_slice.1

private lemma nonzeroLaplacianEigenvalueSet_inter_Ioi_infinite
    (g : SmoothRiemannianMetric I M)
    (h_inf : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Infinite)
    (t : ℝ) :
    ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t).Infinite := by
  intro h_fin
  apply h_inf
  have h_below_fin : Set.Finite { lam |
      lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ t } :=
    nonzeroLaplacianEigenvalueSet_finite_below (I := I) (M := M) g t
  have h_S_eq :
      nonzeroLaplacianEigenvalueSet (I := I) (M := M) g =
        { lam | lam ∈ nonzeroLaplacianEigenvalueSet (I := I) (M := M) g ∧ lam ≤ t } ∪
        ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t) := by
    ext lam
    constructor
    · intro hlam
      by_cases hle : lam ≤ t
      · left; exact ⟨hlam, hle⟩
      · right
        push Not at hle
        exact ⟨hlam, hle⟩
    · rintro (⟨hS, _⟩ | ⟨hS, _⟩)
      · exact hS
      · exact hS
  rw [h_S_eq]
  exact h_below_fin.union h_fin

private lemma sInf_inter_Ioi_mem
    (g : SmoothRiemannianMetric I M) (t : ℝ)
    (h_nonempty : ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
                   Set.Ioi t).Nonempty) :
    sInf ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t) ∈
      (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t := by
  obtain ⟨a, ha_S, ha_gt⟩ := h_nonempty
  set T : Set ℝ := (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩ Set.Ioi t
  have ha_T : a ∈ T := ⟨ha_S, ha_gt⟩
  have hT_bddBelow : BddBelow T := by
    refine ⟨t, ?_⟩
    intro x hx; exact (Set.mem_Ioi.mp hx.2).le
  have hT_slice_fin : Set.Finite (T ∩ Set.Iic a) := by
    apply (nonzeroLaplacianEigenvalueSet_finite_below
      (I := I) (M := M) g a).subset
    rintro lam ⟨⟨hlam_S, _⟩, hlam_a⟩
    exact ⟨hlam_S, hlam_a⟩
  exact csInf_mem_of_finite_slice hT_bddBelow a ha_T hT_slice_fin

theorem laplacianEigenvalueAscending_mem_of_infinite
    (g : SmoothRiemannianMetric I M)
    (h_inf : (nonzeroLaplacianEigenvalueSet (I := I) (M := M) g).Infinite)
    (n : ℕ) :
    laplacianEigenvalueAscending (I := I) (M := M) g n ∈
      nonzeroLaplacianEigenvalueSet (I := I) (M := M) g := by
  induction n with
  | zero =>
      rw [laplacianEigenvalueAscending_zero, ite_eq_left h_inf.nonempty]
      set S : Set ℝ := nonzeroLaplacianEigenvalueSet (I := I) (M := M) g
      obtain ⟨a, ha_S⟩ := h_inf.nonempty
      have h_S_bddBelow : BddBelow S := by
        refine ⟨0, ?_⟩
        intro x hx
        exact (nonzeroLaplacianEigenvalueSet_pos (I := I) (M := M) g hx).le
      have h_slice_fin : Set.Finite (S ∩ Set.Iic a) :=
        nonzeroLaplacianEigenvalueSet_inter_Iic_finite (I := I) (M := M) g a
      exact csInf_mem_of_finite_slice h_S_bddBelow a ha_S h_slice_fin
  | succ n ih =>
      rw [laplacianEigenvalueAscending_succ]
      set prev := laplacianEigenvalueAscending (I := I) (M := M) g n
      have h_inter_inf : ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
                          Set.Ioi prev).Infinite :=
        nonzeroLaplacianEigenvalueSet_inter_Ioi_infinite
          (I := I) (M := M) g h_inf prev
      have h_inter_nonempty : ((nonzeroLaplacianEigenvalueSet (I := I) (M := M) g) ∩
                                Set.Ioi prev).Nonempty := h_inter_inf.nonempty
      rw [ite_eq_left h_inter_nonempty]
      exact (sInf_inter_Ioi_mem (I := I) (M := M) g prev h_inter_nonempty).1

end Laplacian
end CalabiYau

end
