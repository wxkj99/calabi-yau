module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Basic
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.OverlapIntegral
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Common refinement by actual smooth localized forms

Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 16.5,
pp. 405–406. Products of two finite partitions give actual smooth forms
whose row and column sums recover the two original localizations.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

def smoothMulForm {k : ℕ}
    (f : C^∞⟮𝓘(ℝ, Fin d → ℝ), M; 𝓘(ℝ), ℝ⟯)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k) :
    DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k :=
  ⟨fun p => f p • η p, f.contMDiff.smul_section η.contMDiff_toFun⟩

theorem smoothMulForm_add {k : ℕ}
    (f : C^∞⟮𝓘(ℝ, Fin d → ℝ), M; 𝓘(ℝ), ℝ⟯)
    (η ζ : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k) :
    smoothMulForm f (η + ζ) = smoothMulForm f η + smoothMulForm f ζ := by
  apply ContMDiffSection.ext
  intro p
  change f p • (η p + ζ p) = f p • η p + f p • ζ p
  exact smul_add _ _ _

theorem smoothMulForm_smul {k : ℕ}
    (f : C^∞⟮𝓘(ℝ, Fin d → ℝ), M; 𝓘(ℝ), ℝ⟯) (c : ℝ)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k) :
    smoothMulForm f (c • η) = c • smoothMulForm f η := by
  apply ContMDiffSection.ext
  intro p
  change f p • (c • η p) = c • (f p • η p)
  simp only [smul_smul, mul_comm]

theorem smoothMulForm_closedSupport_subset {k : ℕ}
    (f : C^∞⟮𝓘(ℝ, Fin d → ℝ), M; 𝓘(ℝ), ℝ⟯)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k) :
    closure {p : M | smoothMulForm f η p ≠ 0} ⊆
      tsupport f ∩ closure {p : M | η p ≠ 0} := by
  have hsub : {p : M | smoothMulForm f η p ≠ 0} ⊆
      {p : M | f p ≠ 0} ∩ {p : M | η p ≠ 0} := by
    intro p hp
    change f p • η p ≠ 0 at hp
    constructor
    · intro hf
      apply hp
      simp [hf]
    · intro hη
      apply hp
      simp [hη]
  exact (closure_mono hsub).trans closure_inter_subset

theorem sum_smoothMulForm_eq {ι : Type*} {k : ℕ}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin d → ℝ) M Set.univ)
    (s : Finset ι) (hs : ∀ p : M, ∑ i ∈ s, ρ i p = 1)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k) :
    (∑ i ∈ s, smoothMulForm (ρ i) η) = η := by
  apply ContMDiffSection.ext
  intro p
  let ev : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k →+
      Bundle.continuousAlternatingMap ℝ (Fin k) (Fin d → ℝ)
        (TangentSpace 𝓘(ℝ, Fin d → ℝ)) ℝ (Bundle.Trivial M ℝ) p :=
    { toFun := fun α => α p
      map_zero' := rfl
      map_add' := fun α β => rfl }
  change ev (∑ i ∈ s, smoothMulForm (ρ i) η) = ev η
  rw [map_sum]
  change (∑ i ∈ s, ρ i p • η p) = η p
  rw [← Finset.sum_smul, hs p, one_smul]

theorem two_partition_refinement {ι κ : Type*} {k : ℕ}
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin d → ℝ) M Set.univ)
    (τ : SmoothPartitionOfUnity κ 𝓘(ℝ, Fin d → ℝ) M Set.univ)
    (s : Finset ι) (t : Finset κ)
    (hs : ∀ p : M, ∑ i ∈ s, ρ i p = 1)
    (ht : ∀ p : M, ∑ j ∈ t, τ j p = 1)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k) :
    (∀ i, smoothMulForm (ρ i) η =
      ∑ j ∈ t, smoothMulForm (τ j) (smoothMulForm (ρ i) η)) ∧
    (∀ j, smoothMulForm (τ j) η =
      ∑ i ∈ s, smoothMulForm (τ j) (smoothMulForm (ρ i) η)) ∧
    (∀ i j, closure {p : M |
      smoothMulForm (τ j) (smoothMulForm (ρ i) η) p ≠ 0} ⊆
      tsupport (ρ i) ∩ tsupport (τ j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (sum_smoothMulForm_eq τ t ht (smoothMulForm (ρ i) η)).symm
  · intro j
    apply ContMDiffSection.ext
    intro p
    let ev : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M k →+
        Bundle.continuousAlternatingMap ℝ (Fin k) (Fin d → ℝ)
          (TangentSpace 𝓘(ℝ, Fin d → ℝ)) ℝ (Bundle.Trivial M ℝ) p :=
      { toFun := fun α => α p
        map_zero' := rfl
        map_add' := fun α β => rfl }
    change ev (smoothMulForm (τ j) η) =
      ev (∑ i ∈ s, smoothMulForm (τ j) (smoothMulForm (ρ i) η))
    rw [map_sum]
    change τ j p • η p = ∑ i ∈ s, τ j p • (ρ i p • η p)
    rw [← Finset.smul_sum, ← Finset.sum_smul, hs p, one_smul]
  · intro i j p hp
    have hτ := smoothMulForm_closedSupport_subset (τ j) (smoothMulForm (ρ i) η)
    have hρ := smoothMulForm_closedSupport_subset (ρ i) η
    exact ⟨(hρ (hτ hp).2).1, (hτ hp).1⟩

section ChartIntegral

variable [T2Space M] [CompactSpace M]

/-- A common refinement compares actual signed chart integrals term by term. -/
theorem chart_sum_eq_of_common_refinement {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (C : ι → OrientedLocalChart d M) (D : κ → OrientedLocalChart d M)
    (β : ι → DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (δ : κ → DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (Γ : ι → κ → DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hrow : ∀ i ∈ s, β i = ∑ j ∈ t, Γ i j)
    (hcol : ∀ j ∈ t, δ j = ∑ i ∈ s, Γ i j)
    (hΓ : ∀ i ∈ s, ∀ j ∈ t,
      closure {p : M | Γ i j p ≠ 0} ⊆ (C i).domain ∩ (D j).domain)
    (hCD : ∀ i ∈ s, ∀ j ∈ t, (C i).Compatible (D j)) :
    (∑ i ∈ s, signedChartIntegral (C i) (β i)) =
      ∑ j ∈ t, signedChartIntegral (D j) (δ j) := by
  classical
  calc
    (∑ i ∈ s, signedChartIntegral (C i) (β i)) =
        ∑ i ∈ s, ∑ j ∈ t, signedChartIntegral (C i) (Γ i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrow i hi]
      exact signedChartIntegral_finsetSum (C i) t (Γ i)
        (fun j hj => (hΓ i hi j hj).trans Set.inter_subset_left)
    _ = ∑ i ∈ s, ∑ j ∈ t, signedChartIntegral (D j) (Γ i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact signedChartIntegral_eq_of_compatible
        (C i) (D j) (hCD i hi j hj) (Γ i j) (hΓ i hi j hj)
    _ = ∑ j ∈ t, ∑ i ∈ s, signedChartIntegral (D j) (Γ i j) :=
      Finset.sum_comm
    _ = ∑ j ∈ t, signedChartIntegral (D j) (δ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcol j hj]
      exact (signedChartIntegral_finsetSum (D j) s (fun i => Γ i j)
        (fun i hi => (hΓ i hi j hj).trans Set.inter_subset_right)).symm

/-- A finite sum of supported chart integrals, not yet a constructed global linear map. -/
def partitionChartIntegral {ι : Type*}
    (C : ι → OrientedLocalChart d M)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin d → ℝ) M Set.univ)
    (s : Finset ι) (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) : ℝ :=
  ∑ i ∈ s, signedChartIntegral (C i) (smoothMulForm (ρ i) η)

/-- Finite sums associated with two compatible subordinate partitions agree. -/
theorem partitionChartIntegral_eq {ι κ : Type*}
    (C : ι → OrientedLocalChart d M) (D : κ → OrientedLocalChart d M)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin d → ℝ) M Set.univ)
    (τ : SmoothPartitionOfUnity κ 𝓘(ℝ, Fin d → ℝ) M Set.univ)
    (s : Finset ι) (t : Finset κ)
    (hs : ∀ p : M, ∑ i ∈ s, ρ i p = 1)
    (ht : ∀ p : M, ∑ j ∈ t, τ j p = 1)
    (hρ : ∀ i ∈ s, tsupport (ρ i) ⊆ (C i).domain)
    (hτ : ∀ j ∈ t, tsupport (τ j) ⊆ (D j).domain)
    (hCD : ∀ i ∈ s, ∀ j ∈ t, (C i).Compatible (D j))
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) :
    partitionChartIntegral C ρ s η = partitionChartIntegral D τ t η := by
  classical
  obtain ⟨hrow, hcol, hΓ⟩ := two_partition_refinement ρ τ s t hs ht η
  unfold partitionChartIntegral
  apply chart_sum_eq_of_common_refinement s t C D
    (fun i => smoothMulForm (ρ i) η) (fun j => smoothMulForm (τ j) η)
    (fun i j => smoothMulForm (τ j) (smoothMulForm (ρ i) η))
    (fun i _ => hrow i) (fun j _ => hcol j) ?_ hCD
  intro i hi j hj
  exact (hΓ i j).trans (Set.inter_subset_inter (hρ i hi) (hτ j hj))

/-- The same finite chart sum has the local formula on an admissible restricted chart. -/
theorem partitionChartIntegral_eq_of_supported {ι : Type*}
    (C : ι → OrientedLocalChart d M)
    (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, Fin d → ℝ) M Set.univ)
    (s : Finset ι) (hs : ∀ p : M, ∑ i ∈ s, ρ i p = 1)
    (hρ : ∀ i ∈ s, tsupport (ρ i) ⊆ (C i).domain)
    (D : OrientedLocalChart d M) (hCD : ∀ i ∈ s, (C i).Compatible D)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hη : closure {p : M | η p ≠ 0} ⊆ D.domain) :
    partitionChartIntegral C ρ s η = signedChartIntegral D η := by
  classical
  have hD : ∀ i ∈ s,
      closure {p : M | smoothMulForm (ρ i) η p ≠ 0} ⊆ D.domain :=
    fun i hi => ((smoothMulForm_closedSupport_subset (ρ i) η).trans
      Set.inter_subset_right).trans hη
  calc
    partitionChartIntegral C ρ s η =
        ∑ i ∈ s, signedChartIntegral (C i) (smoothMulForm (ρ i) η) := rfl
    _ = ∑ i ∈ s, signedChartIntegral D (smoothMulForm (ρ i) η) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply signedChartIntegral_eq_of_compatible (C i) D (hCD i hi)
      exact (smoothMulForm_closedSupport_subset (ρ i) η).trans
        (Set.inter_subset_inter (hρ i hi) hη)
    _ = signedChartIntegral D (∑ i ∈ s, smoothMulForm (ρ i) η) :=
      (signedChartIntegral_finsetSum D s (fun i => smoothMulForm (ρ i) η) hD).symm
    _ = signedChartIntegral D η := by
      rw [sum_smoothMulForm_eq ρ s hs η]

end ChartIntegral

end CalabiYau.DifferentialForm
