-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Regularity/Iterated/Bootstrap/H2RegularitySuccessor.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2Regularity

@[expose] public section


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open _root_.Sobolev
open _root_.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianDomainPow_two_preimage_eq
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    ∃ w_h : H1Compl (I := I) (M := M) g,
      w_h ∈ laplacianDomain (I := I) (M := M) g ∧
      H1ComplToLp (I := I) (M := M) g w_h =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ := by
  rw [show (2 : ℕ) = 1 + 1 from rfl] at hu_h
  rw [laplacianDomainPow_succ_mem_iff] at hu_h
  obtain ⟨f, hf⟩ := hu_h
  rw [iteratedResolventL2_one] at hf
  refine ⟨resolvent (I := I) (M := M) g f, ?_, ?_⟩
  · rw [laplacianDomain_mem_iff]
    exact ⟨f, rfl⟩
  · have h_resolventL2_apply : resolventL2 (I := I) (M := M) g f =
        H1ComplToLp (I := I) (M := M) g (resolvent (I := I) (M := M) g f) := by
      rfl
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
    rw [← h_resolventL2_apply]
    exact hf.symm

theorem laplacianDomainPow_two_h2_plus_rhs_h2
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    (Sobolev.Chart.MemWkpChart
        (I := I) (M := M) 2 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      Sobolev.Chart.wkpNormChart
        (I := I) (M := M) 2 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) ∧
    (Sobolev.Chart.MemWkpChart
        (I := I) (M := M) 2 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
      Sobolev.Chart.wkpNormChart
        (I := I) (M := M) 2 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤) := by
  have hu_h_dom : u_h ∈ laplacianDomain (I := I) (M := M) g :=
    laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h
  have hu_h_in_pow_one : u_h ∈ laplacianDomainPow (I := I) (M := M) g 1 := by
    rw [laplacianDomainPow_one]; exact hu_h_dom
  have h_u_h2 := iteratedH2Regularity_one (I := I) (M := M) g hu_h_in_pow_one
  obtain ⟨w_h, hw_h_dom, hw_h_eq⟩ :=
    laplacianDomainPow_two_preimage_eq (I := I) (M := M) g hu_h
  have hw_h_in_pow_one : w_h ∈ laplacianDomainPow (I := I) (M := M) g 1 := by
    rw [laplacianDomainPow_one]; exact hw_h_dom
  have h_w_h2 := iteratedH2Regularity_one (I := I) (M := M) g hw_h_in_pow_one
  refine ⟨h_u_h2, ?_⟩
  rw [show (laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩) =
      H1ComplToLp (I := I) (M := M) g w_h from hw_h_eq.symm]
  exact h_w_h2

theorem laplacianDomainPow_two_iterated_h2
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    Sobolev.Chart.MemWkpChart
      (I := I) (M := M) 2 2
      ((laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  have h := laplacianDomainPow_two_h2_plus_rhs_h2 (I := I) (M := M) g hu_h
  exact ⟨h.1.1, h.2.1⟩

end Laplacian
end Analysis
end CalabiYau

end
