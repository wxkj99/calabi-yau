module

public import CalabiYau.Geometry.Kahler.Poisson
import CalabiYau.Geometry.Kahler.Poisson.RiemannianTransfer
import CalabiYau.Analysis.Spectral.Scalar.PoissonSolvability
import CalabiYau.Analysis.Spectral.Scalar.SpectralGap
import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain
import CalabiYau.Analysis.Elliptic.Poisson.GlobalRepresentative

/-!
# Poisson solvability on compact Kähler manifolds

The compact-manifold input used by the continuity method: each Kähler form on a compact connected
complex manifold has solvable mean-zero Poisson equation.
-/

@[expose] public section

open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace lp
open MeasureTheory
open CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian

namespace CalabiYau

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- Spectral gap turns orthogonality to the actual zero eigenspace into a weak variational
Poisson solution. This is the Fredholm-range part; smooth elliptic regularity is separate. -/
private theorem riemannianWeakSolver_of_basis_orthogonality
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (ω₀ : KahlerForm n M)
    (w : Lp ℝ 2 (CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) ω₀.toRiemannianMetric))
    (horth : ∀ i : Σ μ : NonzeroResolventEigenvalue
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) ω₀.toRiemannianMetric,
        Fin (Module.finrank ℝ (resolventEigenspace
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
          ω₀.toRiemannianMetric μ.val)),
        laplacianEigenvalueOf i.1.val = 0 →
        ⟪resolventHilbertEigenbasisSigma
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
          ω₀.toRiemannianMetric i, w⟫_ℝ = 0) :
    ∃ u_h : laplacianDomain
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
        ω₀.toRiemannianMetric,
      laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
        ω₀.toRiemannianMetric u_h = w := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_le_nonzeroLaplacianEigenvalueSet
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
      ω₀.toRiemannianMetric
  exact exists_laplacianDomain_laplacianOp_eq_of_inner_eigenbasis_eq_zero
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
    ω₀.toRiemannianMetric hc hgap w horth

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- The remaining regularity step: a weak variational solution with smooth source has a smooth
representative solving the pointwise Laplace--Beltrami equation. -/
private theorem smoothToLp_inner_one_of_integral_zero
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (hmean : ∫ x, f x ∂CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g = 0) :
    ⟪smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        ⟨fun _ => (1 : ℝ), contMDiff_const⟩,
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨f, hf⟩⟫_ℝ = 0 := by
  rw [L2.inner_def]
  have hone : (smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
      ⟨fun _ => (1 : ℝ), contMDiff_const⟩ : M → ℝ) =ᵐ[
        CalabiYau.RiemannianVolume.riemannianVolumeMeasure
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g] fun _ => (1 : ℝ) := by
    exact MemLp.coeFn_toLp (SmoothScalar.memLp_two
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (g := g)
      ⟨fun _ => (1 : ℝ), contMDiff_const⟩)
  have hf' : (smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
      ⟨f, hf⟩ : M → ℝ) =ᵐ[
        CalabiYau.RiemannianVolume.riemannianVolumeMeasure
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g] f := by
    exact MemLp.coeFn_toLp (SmoothScalar.memLp_two
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (g := g) ⟨f, hf⟩)
  have hfun : (fun x : M => @inner ℝ ℝ _
      ((smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        ⟨fun _ => (1 : ℝ), contMDiff_const⟩ : M → ℝ) x)
      ((smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨f, hf⟩ : M → ℝ) x)) =ᵐ[
        CalabiYau.RiemannianVolume.riemannianVolumeMeasure
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g] f := by
    filter_upwards [hone, hf'] with x hx₁ hx₂
    rw [hx₁, hx₂]
    simp
  calc
    _ = ∫ x, f x ∂CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g := integral_congr_ae hfun
    _ = 0 := hmean

open scoped ENNReal

open scoped ENNReal

omit [ConnectedSpace M] in
omit [MeasurableSpace M] [BorelSpace M] in
private theorem smooth_representative_of_laplacianDomain
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (u_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
    (hweak : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨f, hf⟩) :
    ∃ (u : M → ℝ), ∃ hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u,
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨u, hu⟩ =
        h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
          (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) := by
  let u := h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
    (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
  have htwo : Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) 2 2 (u : M → ℝ) :=
    (laplacianDomain_memWkpChart_two
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h.property).1
  have hsucc : ∀ k : ℕ, Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (k + 1) 2 (u : M → ℝ) := by
    intro k
    induction k with
    | zero => exact Sobolev.Chart.MemWkpChart.le_of_le (by omega) htwo
    | succ k ih =>
        have hk : Sobolev.Chart.MemWkpChart
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) k 2 (u : M → ℝ) :=
          Sobolev.Chart.MemWkpChart.le_of_le (by omega) ih
        exact poisson_domain_memWkpChart_succ g u_h k ih
          (poisson_domainSource_memWkpChart g u_h ⟨f, hf⟩ hweak k hk)
  have heven : ∀ k : ℕ, Sobolev.Chart.MemWkpChart
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) (2 * k) 2 (u : M → ℝ) := by
    intro k
    exact Sobolev.Chart.MemWkpChart.le_of_le (by omega) (hsucc (2 * k))
  obtain ⟨q, hq⟩ := poisson_exists_smoothScalar_of_all_even_orders g u heven
  exact ⟨q.toFun, q.smooth, hq⟩

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem pointwise_riemannian_laplacian_of_domain_solution_with_smooth_representative
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (u : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    (u_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
    (hrep : smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        ⟨u, hu⟩ = h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
          (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g))
    (hweak : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨f, hf⟩) :
    ∀ x, CalabiYau.Riemannian.ΔG
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g ⟨u, hu⟩ x = f x := by
  let us : SmoothScalar g := ⟨u, hu⟩
  let us_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g :=
    ⟨smoothToH1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g us,
      smoothToH1Compl_mem_laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) us⟩
  have hrep' : h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        (us_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) =
      h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) := by
    rw [h1ComplToLp_smoothToH1Compl]
    exact hrep
  have hu_h_eq : (us_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) =
      (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) :=
    h1ComplToLp_injective_on_laplacianDomain
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g hrep'
  have hdom_eq : us_h = u_h := Subtype.ext hu_h_eq
  have hlap : smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g us.laplacian =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨f, hf⟩ := by
    calc
      _ = laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g us_h :=
        (laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) us).symm
      _ = laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h :=
        congrArg (laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) hdom_eq
      _ = _ := hweak
  have hsm : us.laplacian = (⟨f, hf⟩ : SmoothScalar g) :=
    smoothToLp_injective (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g hlap
  intro x
  have hx := congrArg (fun v : SmoothScalar g => v.toFun x) hsm
  simpa [us] using hx

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem smooth_solution_representative_of_laplacianDomain
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (u_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
    (hweak : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨f, hf⟩) :
    ∃ (u : M → ℝ), ∃ hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u,
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨u, hu⟩ =
        h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
          (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) ∧
      ∀ x, CalabiYau.Riemannian.ΔG
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g ⟨u, hu⟩ x = f x := by
  obtain ⟨u, hu, hrep⟩ := smooth_representative_of_laplacianDomain g f hf u_h hweak
  refine ⟨u, hu, hrep, ?_⟩
  exact pointwise_riemannian_laplacian_of_domain_solution_with_smooth_representative
    g f hf u hu u_h hrep hweak

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem smooth_solution_of_laplacianDomain
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (u_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
    (hu : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨f, hf⟩) :
    ∃ (u : M → ℝ), ∃ hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u,
      ∀ x, CalabiYau.Riemannian.ΔG
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g ⟨u, hu⟩ x = f x := by
  obtain ⟨u, hu, _, hsol⟩ :=
    smooth_solution_representative_of_laplacianDomain g f hf u_h hu
  exact ⟨u, hu, hsol⟩

private theorem poissonSolvable_zero_dimensional
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin 0)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 0)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M] (ω₀ : KahlerForm 0 M) : ω₀.PoissonSolvable := by
  classical
  let : DiscreteTopology (EuclideanSpace ℂ (Fin 0)) := inferInstance
  let : DiscreteTopology M :=
    ChartedSpace.discreteTopology (EuclideanSpace ℂ (Fin 0)) M
  have hsub : Subsingleton M := by
    refine ⟨fun x y => ?_⟩
    have hconn := (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace M)).2
    have hcl : IsClopen ({x} : Set M) := isClopen_discrete {x}
    rcases hconn {x} hcl with hempty | huniv
    · have hx : x ∈ ({x} : Set M) := by simp
      rw [hempty] at hx
      simp at hx
    · have hy : y ∈ ({x} : Set M) := by rw [huniv]; simp
      exact hy.symm
  let : Subsingleton M := hsub
  let : Nonempty M := (connectedSpace_iff_clopen.mp
    (inferInstance : ConnectedSpace M)).1
  let : Unique M :=
    ⟨⟨Classical.choice ‹Nonempty M›⟩, fun a => Subsingleton.elim _ _⟩
  have hmass : 0 < ω₀.volume.real Set.univ := by
    rw [MeasureTheory.measureReal_def]
    apply ENNReal.toReal_pos
    · exact (isOpen_discrete (Set.univ : Set M)).measure_ne_zero ω₀.volume
        ⟨default, Set.mem_univ _⟩
    · exact MeasureTheory.measure_ne_top ω₀.volume Set.univ
  intro f hf hmean
  have hmean' : ω₀.volume.real Set.univ * f default = 0 := by
    simpa [MeasureTheory.integral_unique] using hmean
  have hfzero : f default = 0 := by
    rcases mul_eq_zero.mp hmean' with hmasszero | hfzero
    · exact (hmass.ne' hmasszero).elim
    · exact hfzero
  have hconst : f = fun _ => (0 : ℝ) := by
    funext x
    have hx : x = default := Subsingleton.elim _ _
    rw [hx]
    exact hfzero
  refine ⟨fun _ => 0, contMDiff_const, ?_⟩
  rw [hconst]
  exact ω₀.laplacian_const 0

/-- Positive-dimensional compact Poisson existence reduces to smooth elliptic Fredholm/Hodge
surjectivity for the canonical real Riemannian metric. The conditional transfer handles volume
comparison and the normalization `ΔG = 2 * Δω`; it does not supply analytic existence. The remaining
hole is precisely a real-smooth solution for every Riemannian mean-zero source. -/
private theorem zeroEigenbasis_is_constant
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (ω₀ : KahlerForm n M)
    (i : Σ μ : NonzeroResolventEigenvalue
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) ω₀.toRiemannianMetric,
      Fin (Module.finrank ℝ (resolventEigenspace
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
        ω₀.toRiemannianMetric μ.val)))
    (hzero : laplacianEigenvalueOf i.1.val = 0) :
    ∃ c : ℝ, resolventHilbertEigenbasisSigma
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
        ω₀.toRiemannianMetric i =
      c • smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
        ω₀.toRiemannianMetric ⟨fun _ => (1 : ℝ), contMDiff_const⟩ := by
  let g := ω₀.toRiemannianMetric
  let u_h := laplacianEigenfunction (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i
  have hzeroOp : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h = 0 := by
    rw [show u_h = laplacianEigenfunction
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i from rfl,
      laplacianOp_laplacianEigenfunction]
    simp [hzero]
  obtain ⟨u, hu, hrep, hpoint⟩ := smooth_solution_representative_of_laplacianDomain g
    (fun _ => (0 : ℝ)) contMDiff_const u_h hzeroOp
  have hcomplex : ω₀.laplacian u = 0 := by
    funext x
    have hbridge := ω₀.riemannian_laplacian_eq_two_mul_laplacian u hu x
    rw [hpoint x] at hbridge
    have hx : (2 : ℝ) * ω₀.laplacian u x = 0 := hbridge.symm
    rcases mul_eq_zero.mp hx with htwo | hzero
    · norm_num at htwo
    · exact hzero
  obtain ⟨c, hc⟩ := ω₀.eq_const_of_laplacian_eq_zero hu hcomplex
  let one : SmoothScalar g := ⟨fun _ => (1 : ℝ), contMDiff_const⟩
  let u_s : SmoothScalar g := ⟨u, hu⟩
  have hu_s : u_s = c • one := by
    apply SmoothScalar.ext
    funext x
    simp [u_s, one, hc x]
  have hmap := h1ComplToLp_laplacianEigenfunction
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i
  refine ⟨c, ?_⟩
  calc
    resolventHilbertEigenbasisSigma
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i =
        h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
          (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) := by
      calc
        resolventHilbertEigenbasisSigma
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i =
            resolventEigenbasisVec
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i :=
          resolventHilbertEigenbasisSigma_apply
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i
        _ = resolventEigenbasisSigma
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i :=
          (resolventEigenbasisSigma_eq_resolventEigenbasisVec
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i).symm
        _ = h1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
              (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) := by
          simpa [u_h] using hmap.symm
    _ = smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_s := hrep.symm
    _ = c • smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g one := by
      rw [hu_s, map_smul]
    _ = c • smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
          ⟨fun _ => (1 : ℝ), contMDiff_const⟩ := by rfl

private theorem poissonSolvable_positive_dimensional
    (hn : n ≠ 0) (ω₀ : KahlerForm n M) : ω₀.PoissonSolvable := by
  have : NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))) := by
    have hdim : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
      exact Module.finrank_pos
    exact ⟨hdim.ne'⟩
  apply poissonSolvable_of_riemannian_solver ω₀
  intro f hf hmean
  show ∃ (u : M → ℝ), ∃ hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u,
    ∀ x, CalabiYau.Riemannian.ΔG
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric ⟨u, hu⟩ x = f x
  let w := smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
    ω₀.toRiemannianMetric ⟨f, hf⟩
  have horth : ∀ i : Σ μ : NonzeroResolventEigenvalue
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) ω₀.toRiemannianMetric,
      Fin (Module.finrank ℝ (resolventEigenspace
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
        ω₀.toRiemannianMetric μ.val)),
      laplacianEigenvalueOf i.1.val = 0 →
      ⟪resolventHilbertEigenbasisSigma
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
        ω₀.toRiemannianMetric i, w⟫_ℝ = 0 := by
    intro i hi
    obtain ⟨c, hc⟩ := zeroEigenbasis_is_constant ω₀ i hi
    rw [hc, real_inner_smul_left]
    simpa [w] using congrArg (fun z : ℝ => c * z)
      (smoothToLp_inner_one_of_integral_zero ω₀.toRiemannianMetric f hf hmean)
  obtain ⟨u_h, hu_h⟩ := riemannianWeakSolver_of_basis_orthogonality ω₀ w horth
  have hu : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
      ω₀.toRiemannianMetric u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M)
        ω₀.toRiemannianMetric ⟨f, hf⟩ := by
    simpa [w] using hu_h
  obtain ⟨u, hu, hsol⟩ :=
    smooth_solution_of_laplacianDomain ω₀.toRiemannianMetric f hf u_h hu
  exact ⟨u, hu, hsol⟩

/-- Every Kähler form on a compact connected complex manifold has solvable Poisson equation. -/
theorem poissonSolvable_of_compact :
    ∀ ω₀ : KahlerForm n M, ω₀.PoissonSolvable := by
  classical
  intro ω₀
  by_cases hn : n = 0
  · subst n
    exact poissonSolvable_zero_dimensional ω₀
  · exact poissonSolvable_positive_dimensional hn ω₀

end CalabiYau
