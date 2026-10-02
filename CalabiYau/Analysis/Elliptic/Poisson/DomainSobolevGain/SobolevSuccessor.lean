module

public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.FiniteGainAssembly
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.PrecompactInteriorH2
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.Reconstruction
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.BaseForcingResidual
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.BaseForcingDecomposition
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.BaseForcingSupport
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.MixedPartialConsIdentity
public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.CompactSupportExtension

/-!
# One chart Sobolev gain for the resolvent equation

Let `u ∈ laplacianDomain` with chart representative in `H^(m+1)` and `(1 - Δ)u ∈ H^m`.

1. The chart forcing `fChart = ρ·(1 - Δ)u - 2⟨∇ρ, ∇u⟩ - (Δρ)u` splits a.e. as the push-forward
   of the preimage plus a residual (`baseFChart_ae_eq_preimage_add_residual`); the residual lies
   in `H^m` (`fChartResidual_memWkp_of_memWkpChart`), hence so does `fChart`, and it vanishes
   off the image of the partition-of-unity support (`baseFChart_ae_zero_off_chartImagePOUTsupport`).
2. `ordinaryDomain_all_direction_data_of_initial_forcing` provides, for every sequence of
   directions `dirs : Fin m → _`, the weak equation satisfied by the differentiated solution.
3. The prepending identity `chosenMthMixedPartialChartPushedU_cons_ae_eq` makes
   `iterated_memWkp_two_on_precompact_neighborhood_of_gradient_identification` applicable:
   each chosen mixed partial derivative of order `m` is `H^2` on a precompact neighbourhood of
   the image of the partition-of-unity support.
4. These derivatives vanish off that image
   (`chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport`), so
   `memWkp_extend_of_ae_zero_outside_compact` extends the bound to the whole chart target.
5. `chartPushed_memWkp_m_plus_two_step` reconstructs `H^(m+2)` from `H^(m+1)` and the `H^2`
   bounds on all order-`m` mixed partial derivatives.

This follows the elliptic bootstrap in differential-geometry (commit `7a48598d`) and
Gilbarg–Trudinger, Theorem 8.10.
-/

@[expose] public section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
open CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian.MetricExtension hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl Sobolev.Chart Sobolev.Euclidean
open CalabiYau.Analysis.Laplacian.LaplacianDomainChartData
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The base chart forcing is in `H^m` when `u` is chart `H^(m+1)` and its preimage chart `H^m`. -/
theorem baseFChart_memWkp_of_preimage
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (hu : MemWkpChart (I := I) (M := M) (m + 1) 2
      ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
    (hsrc : MemWkpChart (I := I) (M := M) m 2
      ((laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_h⟩ :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    MemWkp (d := Module.finrank ℝ E) m 2
      (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α hu_h).fChart
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hΩ := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hsum := MemWkp.add (by norm_num) hΩ (hsrc α)
    (fChartResidual_memWkp_of_memWkpChart g α m hu)
  exact (MemWkp_congr_ae (by norm_num) hΩ
    (baseFChart_ae_eq_preimage_add_residual g α hu_h)).mpr hsum

/-- Chart `H^(m+2)` of a domain element from chart `H^(m+1)` and a chart `H^m` preimage. -/
theorem chartPushed_memWkp_succ_of_preimage
    (g : SmoothRiemannianMetric I M) (α : M)
    (u : laplacianDomain (I := I) (M := M) g) (m : ℕ)
    (hu : MemWkpChart (I := I) (M := M) (m + 1) 2
      ((h1ComplToLp (I := I) (M := M) g (u : H1Compl g)) : M → ℝ))
    (hsrc : MemWkpChart (I := I) (M := M) m 2
      ((laplacianDomain.preimage (I := I) (M := M) g u :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    MemWkp (d := Module.finrank ℝ E) (m + 2) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g (u : H1Compl g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_initial := baseFChart_memWkp_of_preimage g α m u.property hu hsrc
  have h_support := baseFChart_ae_zero_off_chartImagePOUTsupport g α u.property
  have hdata := ordinaryDomain_all_direction_data_of_initial_forcing g α u m hu
    h_initial h_support
  have hΩ := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_top : ∀ idx : Fin m → Fin (Module.finrank ℝ E),
      MemWkp (d := Module.finrank ℝ E) 2 2
        (chosenMthMixedPartialChartPushedU g α (u : H1Compl g) m idx)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro idx
    obtain ⟨D, hdirs, -⟩ := hdata m le_rfl idx
    obtain ⟨U, hU_open, hK_U, -, hU_cl, hU_mem⟩ :=
      iterated_memWkp_two_on_precompact_neighborhood_of_gradient_identification g α D (hu α)
        (fun i => chosenMthMixedPartialChartPushedU_cons_ae_eq g α (u : H1Compl g) m
          D.directions i (hu α))
    rw [hdirs] at hU_mem
    exact memWkp_extend_of_ae_zero_outside_compact 2 hΩ hU_open
      (fun y hy => hU_cl (subset_closure hy))
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α) hK_U hU_mem
      (chosenMthMixedPartialChartPushedU_ae_zero_off_chartImagePOUTsupport g α
        (u : H1Compl g) m (hu α) idx)
  exact chartPushed_memWkp_m_plus_two_step g α (u : H1Compl g) m (hu α) h_top

end CalabiYau.PoissonDomainRegularity
