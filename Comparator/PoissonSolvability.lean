module

public import CalabiYau.Geometry.Kahler.Poisson
import Comparator.PoissonSolvability.RiemannianTransfer
import CalabiYau.Geometry.Kahler.Sobolev.PoincareExistence
import CalabiYau.Analysis.Spectral.Scalar.PoissonSolvability
import CalabiYau.Analysis.Spectral.Scalar.SpectralGap
import Comparator.PoissonSolvability.DomainSobolevGain
import Comparator.PoissonSolvability.GlobalRepresentative

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

private abbrev PoissonBasisIndex
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M) :=
  Σ μ : NonzeroResolventEigenvalue
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g,
    Fin (Module.finrank ℝ (resolventEigenspace
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g μ.val))

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
private theorem inner_oneSubLapClassical_sigma
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (q : SmoothScalar g) (i : PoissonBasisIndex g) :
    ⟪resolventHilbertEigenbasisSigma
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i,
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q.oneSubLapClassical⟫_ℝ =
      (1 + laplacianEigenvalueOf i.1.val) *
        ⟪resolventHilbertEigenbasisSigma
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i,
          smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ := by
  let u_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g :=
    ⟨smoothToH1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q,
      smoothToH1Compl_mem_laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) q⟩
  have hLap := laplacianOp_inner_eigenbasis
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h i
  rw [show laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q.laplacian from by
        exact laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) q] at hLap
  dsimp only [u_h] at hLap
  rw [H1ComplToLp_smoothToH1Compl] at hLap
  have hq : q.oneSubLapClassical = q - q.laplacian := by
    apply SmoothScalar.ext
    funext x
    rfl
  rw [hq, map_sub, inner_sub_right]
  rw [hLap]
  ring

private theorem inner_oneSubLapClassical_iterate_sigma
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (k : ℕ) (q : SmoothScalar g) (i : PoissonBasisIndex g) :
    ⟪resolventHilbertEigenbasisSigma
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i,
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        ((SmoothScalar.oneSubLapClassical (g := g))^[k] q)⟫_ℝ =
      (1 + laplacianEigenvalueOf i.1.val) ^ k *
        ⟪resolventHilbertEigenbasisSigma
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i,
          smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ := by
  induction k generalizing q with
  | zero => simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rw [inner_oneSubLapClassical_sigma, ih, pow_succ]
      ring

private theorem summable_weighted_coeff_of_smooth_sigma
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (k : ℕ) (q : SmoothScalar g) :
    Summable (fun i : PoissonBasisIndex g =>
      (1 + laplacianEigenvalueOf i.1.val) ^ (2 * k) *
        ⟪resolventHilbertEigenbasisSigma
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i,
          smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ ^ 2) := by
  let b := resolventHilbertEigenbasisSigma
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
  let w := smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
    ((SmoothScalar.oneSubLapClassical (g := g))^[k] q)
  have hsum : Summable (fun i : PoissonBasisIndex g => ⟪b i, w⟫_ℝ ^ 2) := by
    have h := b.summable_inner_mul_inner w w
    refine h.congr (fun i => ?_)
    rw [real_inner_comm]
    ring
  refine hsum.congr (fun i => ?_)
  rw [inner_oneSubLapClassical_iterate_sigma g k q i]
  dsimp [b, w]
  rw [mul_pow, ← pow_mul]
  congr 1
  exact congrArg (fun m : ℕ => (1 + laplacianEigenvalueOf i.1.val) ^ m)
    (Nat.mul_comm k 2)

private theorem summable_coeff_of_laplacianOp_eq_smooth_sigma
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    {u_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g}
    {q : SmoothScalar g}
    (h : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q)
    (k : ℕ) :
    Summable (fun i : PoissonBasisIndex g =>
      (1 + laplacianEigenvalueOf i.1.val) ^ (2 * k) *
        ⟪resolventHilbertEigenbasisSigma
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i,
          H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
            (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)⟫_ℝ ^ 2) := by
  obtain ⟨c₀, hc₀pos, hgap⟩ := exists_pos_le_nonzeroLaplacianEigenvalueSet
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
  have hcoeff : ∀ i : PoissonBasisIndex g,
      ⟪resolventHilbertEigenbasisSigma
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i,
        smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ =
        -laplacianEigenvalueOf i.1.val *
          ⟪resolventHilbertEigenbasisSigma
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i,
            H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
              (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)⟫_ℝ := by
    intro i
    have h2 := laplacianOp_inner_eigenbasis
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h i
    rw [h] at h2
    exact h2
  have hsum_q := summable_weighted_coeff_of_smooth_sigma (g := g) k q
  let b := resolventHilbertEigenbasisSigma
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
  let u := H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
    (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
  have hsum_u : Summable (fun i : PoissonBasisIndex g => ⟪b i, u⟫_ℝ ^ 2) := by
    have h := b.summable_inner_mul_inner u u
    refine h.congr (fun i => ?_)
    rw [real_inner_comm]
    ring
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    ((hsum_q.mul_left (c₀⁻¹ ^ 2)).add hsum_u)
  · have hLam : 0 ≤ laplacianEigenvalueOf i.1.val :=
        laplacianEigenvalueOf_nonneg
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) i.1
    exact mul_nonneg (pow_nonneg (by linarith) _) (sq_nonneg _)
  · rcases eq_or_ne (laplacianEigenvalueOf i.1.val) 0 with h0 | h0
    · rw [h0]
      simp only [add_zero, one_pow, one_mul]
      exact le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · have hgap_i : c₀ ≤ laplacianEigenvalueOf i.1.val :=
        hgap _ (mem_nonzeroLaplacianEigenvalueSet_of_laplacianEigenvalueOf_ne_zero
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) i.1 h0)
      have hA2 : c₀ ^ 2 ≤ laplacianEigenvalueOf i.1.val ^ 2 := by nlinarith
      have hb : ⟪b i, u⟫_ℝ =
          -(⟪b i, smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ) /
            laplacianEigenvalueOf i.1.val := by
        rw [hcoeff i]
        field_simp [h0]
        ring
      have hstep :
          (⟪b i, smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ) ^ 2 /
            laplacianEigenvalueOf i.1.val ^ 2 ≤
          c₀⁻¹ ^ 2 *
            (⟪b i, smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ) ^ 2 := by
        have h1 : (laplacianEigenvalueOf i.1.val ^ 2)⁻¹ ≤ (c₀ ^ 2)⁻¹ := by
          rw [← one_div, ← one_div]
          exact one_div_le_one_div_of_le (by positivity) hA2
        have h2 :
            (⟪b i, smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ) ^ 2 *
              (laplacianEigenvalueOf i.1.val ^ 2)⁻¹ ≤
            (⟪b i, smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ) ^ 2 *
              (c₀ ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        rw [div_eq_mul_inv]
        calc
          _ ≤ _ := h2
          _ = _ := by rw [inv_pow]; ring
      rw [hb, neg_div, neg_sq, div_pow]
      calc
        _ ≤ (1 + laplacianEigenvalueOf i.1.val) ^ (2 * k) *
              (c₀⁻¹ ^ 2 *
                (⟪b i, smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ) ^ 2) := by
          have hLam : 0 ≤ laplacianEigenvalueOf i.1.val :=
            laplacianEigenvalueOf_nonneg
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) i.1
          exact mul_le_mul_of_nonneg_left hstep
            (pow_nonneg (by linarith) _)
        _ = c₀⁻¹ ^ 2 *
              ((1 + laplacianEigenvalueOf i.1.val) ^ (2 * k) *
                (⟪b i, smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ) ^ 2) := by ring
        _ ≤ _ + (⟪b i, smoothToLp
                (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q⟫_ℝ) ^ 2 /
                laplacianEigenvalueOf i.1.val ^ 2 :=
          le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (sq_nonneg _))

private noncomputable def poissonIteratedResolventL2
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M) :
    ℕ → Lp ℝ 2 (CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) →L[ℝ]
      Lp ℝ 2 (CalabiYau.RiemannianVolume.riemannianVolumeMeasure
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (resolventL2
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g).comp
      (poissonIteratedResolventL2 g k)

private theorem poissonIteratedResolventL2_apply_basis
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (k : ℕ) (i : PoissonBasisIndex g) :
    poissonIteratedResolventL2 g k
      (resolventHilbertEigenbasisSigma
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i) =
      (i.1.val ^ k) • resolventHilbertEigenbasisSigma
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i := by
  induction k with
  | zero => simp [poissonIteratedResolventL2, pow_zero]
  | succ k ih =>
      change resolventL2 (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        (poissonIteratedResolventL2 g k
          (resolventHilbertEigenbasisSigma
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i)) =
        i.1.val ^ (k + 1) • resolventHilbertEigenbasisSigma
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i
      rw [ih, (resolventL2
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g).map_smul]
      have h_basis : resolventL2
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
            (resolventHilbertEigenbasisSigma
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i) =
          i.1.val • resolventHilbertEigenbasisSigma
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i := by
        have h_eq : resolventEigenbasisSigma
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i =
          resolventHilbertEigenbasisSigma
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i :=
          (resolventEigenbasisSigma_eq_resolventEigenbasisVec
            (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i).trans
            (resolventHilbertEigenbasisSigma_apply
              (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i).symm
        have h := resolventL2_apply_resolventEigenbasisSigma
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i
        rw [h_eq] at h
        exact h
      rw [h_basis, smul_smul]
      rw [show i.1.val ^ k * i.1.val = i.1.val ^ (k + 1) from by ring]

private theorem poissonResolventEigenvalue_mul_one_add
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (i : PoissonBasisIndex g) :
    i.1.val * (1 + laplacianEigenvalueOf i.1.val) = 1 := by
  have hpos := nonzeroResolventEigenvalue_pos i.1
  have hne : i.1.val ≠ 0 := hpos.ne'
  unfold laplacianEigenvalueOf
  field_simp
  linarith

private theorem map_eq_of_hilbertBasis_diagonal_poisson
    {ι X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (b : HilbertBasis ι ℝ X) (T : X →L[ℝ] X) (d : ι → ℝ) (u v : X)
    (hbasis : ∀ i, T (b i) = d i • b i)
    (hcoeff : ∀ i, (b.repr v) i * d i = (b.repr u) i) : T v = u := by
  have hmap : HasSum (fun i => (b.repr v) i • T (b i)) (T v) := by
    simpa only [map_smul] using (b.hasSum_repr v).mapL T
  have hsummand : (fun i => (b.repr v) i • T (b i)) =
      fun i => (b.repr u) i • b i := by
    funext i
    rw [hbasis i, smul_smul, hcoeff i]
  rw [hsummand] at hmap
  exact HasSum.unique hmap (b.hasSum_repr u)

private lemma real_pow_mul_rearrange_poisson (a x y : ℝ) (k : ℕ) :
    a ^ k * x * y ^ k = (a ^ k * y ^ k) * x := by
  ring

open scoped ENNReal

open scoped ENNReal

set_option maxHeartbeats 800000 in
private theorem exists_poissonIteratedResolventL2_preimage_of_weighted_coeff_summable
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    (u : Lp ℝ 2 (CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g))
    (k : ℕ)
    (hsum : Summable (fun i : PoissonBasisIndex g =>
      (1 + laplacianEigenvalueOf i.1.val) ^ (2 * k) *
        ⟪resolventHilbertEigenbasisSigma
          (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i, u⟫_ℝ ^ 2)) :
    ∃ v, poissonIteratedResolventL2 g k v = u := by
  classical
  let b := resolventHilbertEigenbasisSigma
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
  let c : PoissonBasisIndex g → ℝ := fun i =>
    (1 + laplacianEigenvalueOf i.1.val) ^ k * (b.repr u) i
  have hc_sq : Summable (fun i => (c i) ^ 2) := by
    have heq : (fun i => (c i) ^ 2) = fun i =>
        (1 + laplacianEigenvalueOf i.1.val) ^ (2 * k) *
          ⟪b i, u⟫_ℝ ^ 2 := by
      funext i
      simp only [c, b.repr_apply_apply]
      rw [mul_pow, ← pow_mul]
      congr 1
      exact congrArg (fun m : ℕ => (1 + laplacianEigenvalueOf i.1.val) ^ m)
        (Nat.mul_comm k 2)
    rw [heq]
    exact hsum
  have hc_mem : Memℓp c 2 := by
    apply memℓp_gen
    have hpr : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have heq : (fun i => ‖c i‖ ^ (2 : ℝ≥0∞).toReal) = fun i => c i ^ 2 := by
      funext i
      rw [hpr, Real.norm_eq_abs, ← sq_abs]
      norm_num
    rw [heq]
    exact hc_sq
  let v : Lp ℝ 2 (CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) :=
    b.repr.symm ⟨c, hc_mem⟩
  have hv_coeff : ∀ i, (b.repr v) i = c i := by
    intro i
    have hv_repr : b.repr v = ⟨c, hc_mem⟩ := LinearIsometryEquiv.apply_symm_apply _ _
    exact congrArg (fun w => w i) hv_repr
  refine ⟨v, map_eq_of_hilbertBasis_diagonal_poisson b
    (poissonIteratedResolventL2 g k) (fun i => i.1.val ^ k) u v
    (poissonIteratedResolventL2_apply_basis g k) ?_⟩
  intro i
  calc
    (b.repr v) i * i.1.val ^ k = c i * i.1.val ^ k :=
      congrArg (fun z => z * i.1.val ^ k) (hv_coeff i)
    _ = (b.repr u) i := by
      dsimp [c]
      have hmul : (1 + laplacianEigenvalueOf i.1.val) * i.1.val = 1 := by
        calc
          _ = i.1.val * (1 + laplacianEigenvalueOf i.1.val) := mul_comm _ _
          _ = 1 := poissonResolventEigenvalue_mul_one_add g i
      have hpow : (1 + laplacianEigenvalueOf i.1.val) ^ k * i.1.val ^ k = 1 := by
        rw [← mul_pow, hmul, one_pow]
      calc
        (1 + laplacianEigenvalueOf i.1.val) ^ k * (b.repr u) i * i.1.val ^ k =
            ((1 + laplacianEigenvalueOf i.1.val) ^ k * i.1.val ^ k) * (b.repr u) i :=
          real_pow_mul_rearrange_poisson (1 + laplacianEigenvalueOf i.1.val)
            ((b.repr u) i) i.1.val k
        _ = (b.repr u) i := by rw [hpow, one_mul]

private theorem weak_poisson_solution_has_iterated_resolvent_preimages
    [NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))]
    (g : CalabiYau.SmoothRiemannianMetric
      (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) M)
    {u_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g}
    {q : SmoothScalar g}
    (hweak : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g q) :
    ∀ k : ℕ, ∃ v, poissonIteratedResolventL2 g k v =
      H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) := by
  intro k
  exact exists_poissonIteratedResolventL2_preimage_of_weighted_coeff_summable g
    (H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
      (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)) k
    (summable_coeff_of_laplacianOp_eq_smooth_sigma g hweak k)

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
        H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
          (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) := by
  let u := H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
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
        ⟨u, hu⟩ = H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
          (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g))
    (hweak : laplacianOp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_h =
      smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g ⟨f, hf⟩) :
    ∀ x, CalabiYau.Riemannian.ΔG
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g ⟨u, hu⟩ x = f x := by
  let us : SmoothScalar g := ⟨u, hu⟩
  let us_h : laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g :=
    ⟨smoothToH1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g us,
      smoothToH1Compl_mem_laplacianDomain (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) us⟩
  have hrep' : H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        (us_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) =
      H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
        (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) := by
    rw [H1ComplToLp_smoothToH1Compl]
    exact hrep
  have hu_h_eq : (us_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) =
      (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) :=
    H1ComplToLp_injective_on_laplacianDomain
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
        H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
          (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) ∧
      ∀ x, CalabiYau.Riemannian.ΔG
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g ⟨u, hu⟩ x = f x := by
  obtain ⟨u, hu, hrep⟩ := smooth_representative_of_laplacianDomain g f hf u_h hweak
  refine ⟨u, hu, hrep, ?_⟩
  exact pointwise_riemannian_laplacian_of_domain_solution_with_smooth_representative
    g f hf u hu u_h hrep hweak

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
  letI : DiscreteTopology (EuclideanSpace ℂ (Fin 0)) := inferInstance
  letI : DiscreteTopology M :=
    ChartedSpace.discreteTopology (EuclideanSpace ℂ (Fin 0)) M
  have hsub : Subsingleton M := by
    refine ⟨fun x y => ?_⟩
    have hconn := (connectedSpace_iff_clopen.mp (inferInstance : ConnectedSpace M)).2
    have hcl : IsClopen ({x} : Set M) := isClopen_discrete {x}
    rcases hconn {x} hcl with hempty | huniv
    · have hx : x ∈ ({x} : Set M) := by simp
      rw [hempty] at hx
      simpa using hx
    · have hy : y ∈ ({x} : Set M) := by rw [huniv]; simp
      exact hy.symm
  letI : Subsingleton M := hsub
  letI : Nonempty M := (connectedSpace_iff_clopen.mp
    (inferInstance : ConnectedSpace M)).1
  letI : Unique M :=
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
  have hmap := H1ComplToLp_laplacianEigenfunction
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i
  refine ⟨c, ?_⟩
  calc
    resolventHilbertEigenbasisSigma
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g i =
        H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
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
        _ = H1ComplToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
              (u_h : H1Compl (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g) := by
          simpa [u_h] using hmap.symm
    _ = smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g u_s := hrep.symm
    _ = c • smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g one := by
      rw [hu_s, map_smul]
    _ = c • smoothToLp (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g
          ⟨fun _ => (1 : ℝ), contMDiff_const⟩ := by rfl

private theorem poissonSolvable_positive_dimensional
    (hn : n ≠ 0) (ω₀ : KahlerForm n M) : ω₀.PoissonSolvable := by
  haveI : NeZero (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))) := by
    have hdim : 0 < Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      letI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
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
