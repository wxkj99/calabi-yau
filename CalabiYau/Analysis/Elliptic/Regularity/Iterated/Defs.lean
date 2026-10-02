-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/Iterated/Defs.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Operator.VariationalLaplacian
public import CalabiYau.Analysis.Spectral.Scalar.Resolvent

@[expose] public section


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def iteratedResolventL2 (g : SmoothRiemannianMetric I M) (k : ℕ) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  Nat.recAux (motive := fun _ =>
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (ContinuousLinearMap.id ℝ _)
    (fun _ prev => (resolventL2 (I := I) (M := M) g).comp prev) k

@[simp] lemma iteratedResolventL2_zero (g : SmoothRiemannianMetric I M) :
    iteratedResolventL2 (I := I) (M := M) g 0 =
      ContinuousLinearMap.id ℝ _ := rfl

@[simp] lemma iteratedResolventL2_succ (g : SmoothRiemannianMetric I M) (k : ℕ) :
    iteratedResolventL2 (I := I) (M := M) g (k + 1) =
      (resolventL2 (I := I) (M := M) g).comp
        (iteratedResolventL2 (I := I) (M := M) g k) := rfl

lemma iteratedResolventL2_one (g : SmoothRiemannianMetric I M) :
    iteratedResolventL2 (I := I) (M := M) g 1 =
      resolventL2 (I := I) (M := M) g := by
  rw [iteratedResolventL2_succ]
  rw [iteratedResolventL2_zero]
  exact ContinuousLinearMap.comp_id _

@[simp] lemma iteratedResolventL2_zero_apply (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    iteratedResolventL2 (I := I) (M := M) g 0 f = f := rfl

lemma iteratedResolventL2_succ_apply (g : SmoothRiemannianMetric I M) (k : ℕ)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    iteratedResolventL2 (I := I) (M := M) g (k + 1) f =
      resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k f) := rfl

lemma iteratedResolventL2_add (g : SmoothRiemannianMetric I M) (j k : ℕ) :
    iteratedResolventL2 (I := I) (M := M) g (j + k) =
      (iteratedResolventL2 (I := I) (M := M) g j).comp
        (iteratedResolventL2 (I := I) (M := M) g k) := by
  induction j with
  | zero => simp [iteratedResolventL2_zero]
  | succ j ih =>
    rw [Nat.succ_add, iteratedResolventL2_succ, iteratedResolventL2_succ, ih]
    rw [ContinuousLinearMap.comp_assoc]

noncomputable def laplacianDomainPow (g : SmoothRiemannianMetric I M) (k : ℕ) :
    Submodule ℝ (H1Compl (I := I) (M := M) g) :=
  Nat.recAux (motive := fun _ => Submodule ℝ (H1Compl (I := I) (M := M) g))
    ⊤
    (fun k _ => LinearMap.range
      ((resolvent (I := I) (M := M) g).toLinearMap.comp
        (iteratedResolventL2 (I := I) (M := M) g k).toLinearMap)) k

@[simp] lemma laplacianDomainPow_zero (g : SmoothRiemannianMetric I M) :
    laplacianDomainPow (I := I) (M := M) g 0 = ⊤ := rfl

lemma laplacianDomainPow_succ (g : SmoothRiemannianMetric I M) (k : ℕ) :
    laplacianDomainPow (I := I) (M := M) g (k + 1) =
      LinearMap.range
        ((resolvent (I := I) (M := M) g).toLinearMap.comp
          (iteratedResolventL2 (I := I) (M := M) g k).toLinearMap) := rfl

lemma laplacianDomainPow_one (g : SmoothRiemannianMetric I M) :
    laplacianDomainPow (I := I) (M := M) g 1 =
      laplacianDomain (I := I) (M := M) g := by
  rw [laplacianDomainPow_succ]
  unfold laplacianDomain
  rw [iteratedResolventL2_zero]
  rfl

lemma laplacianDomainPow_succ_mem_iff (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u : H1Compl (I := I) (M := M) g} :
    u ∈ laplacianDomainPow (I := I) (M := M) g (k + 1) ↔
      ∃ f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g),
        u = resolvent (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k f) := by
  rw [laplacianDomainPow_succ]
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe] at hf
    exact hf.symm
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe]
    exact hf.symm

lemma laplacianDomainPow_succ_subset_laplacianDomain
    (g : SmoothRiemannianMetric I M) (k : ℕ) :
    (laplacianDomainPow (I := I) (M := M) g (k + 1) : Set (H1Compl g)) ⊆
      (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) := by
  intro u hu
  rw [SetLike.mem_coe, laplacianDomainPow_succ_mem_iff] at hu
  obtain ⟨f, hf⟩ := hu
  rw [SetLike.mem_coe]
  rw [laplacianDomain_mem_iff]
  exact ⟨iteratedResolventL2 (I := I) (M := M) g k f, hf⟩

lemma laplacianDomainPow_succ_preimage_in_range
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1)) :
    laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g k hu_h⟩ ∈
      LinearMap.range
        (iteratedResolventL2 (I := I) (M := M) g k).toLinearMap := by
  rw [laplacianDomainPow_succ_mem_iff] at hu_h
  obtain ⟨f, hf⟩ := hu_h
  rw [LinearMap.mem_range]
  refine ⟨f, ?_⟩
  apply resolvent_injective (I := I) (M := M) g
  rw [resolvent_laplacianDomain_preimage_eq]
  exact hf.symm

end Laplacian
end Analysis
end CalabiYau

end
