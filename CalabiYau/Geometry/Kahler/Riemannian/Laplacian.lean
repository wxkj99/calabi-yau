module

import CalabiYau.Geometry.Kahler.Laplacian.Cofactor
import CalabiYau.Geometry.Riemannian.Operator.Laplacian.SelfChartWeightedGram
import CalabiYau.Geometry.Kahler.Riemannian.Laplacian.ComplexTrace
public import CalabiYau.Geometry.Kahler.Laplacian
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Kahler.Riemannian.Metric

/-!
# The Kähler and Riemannian Laplacians

For `I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))`, the Riemannian metric induced by a Kähler form
satisfies `ΔG f = 2 * ω₀.laplacian f` and
`g.inner x (∇g f) (∇g f) = 2 * ω₀.gradNormSq f`. The Riemannian gradient here is a vector in
the real tangent space; the factor of two is the convention relating the complex trace to the
real metric. In complex dimension one with `ω = i dz ∧ dż`, the metric is
`2 (dx² + dy²)`, so these factors agree with the flat coordinate calculation.

The `gradFun` form of the energy identity below matches the pointwise gradient energy used by
the Sobolev transfer results; `gradG` is the corresponding smooth-section API used by `ΔG`.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The Riemannian Laplace–Beltrami operator of the metric induced by a Kähler form is twice
its complex trace Laplacian. -/
theorem riemannian_laplacian_eq_two_mul_laplacian
    (ω₀ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) (x : M) :
    CalabiYau.Riemannian.ΔG
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric ⟨f, hf⟩ x =
      2 * ω₀.laplacian f x := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  have hreal := CalabiYau.Riemannian.deltaG_eq_self_chart_weighted_inverse_gram
    (I := I) ω₀.toRiemannianMetric f hf x
  have hcomplex := ω₀.real_chart_weighted_divergence_eq_complex_trace f hf x
  have hchart : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by simp
  have hkahler := ω₀.laplacian_eq_inChart hf x (y := x) hchart
  calc
    CalabiYau.Riemannian.ΔG (I := I) ω₀.toRiemannianMetric ⟨f, hf⟩ x =
        (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
          CalabiYau.Tensor.Coordinates.partialDeriv (E := EuclideanSpace ℂ (Fin n)) i
            (fun w : EuclideanSpace ℂ (Fin n) =>
              CalabiYau.RiemannianVolume.chartDensityOnE (I := I)
                ω₀.toRiemannianMetric x w *
              ∑ j : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
                CalabiYau.Riemannian.chartInvGramMatrix (I := I)
                  ω₀.toRiemannianMetric x ((extChartAt I x).symm w) i j *
                  CalabiYau.Tensor.Coordinates.partialDeriv
                    (E := EuclideanSpace ℂ (Fin n)) j (f ∘ (extChartAt I x).symm) w)
          (extChartAt I x x)) /
          CalabiYau.RiemannianVolume.chartDensity (I := I) ω₀.toRiemannianMetric x x :=
      hreal
    _ = 2 * RCLike.re
        (((ω₀.metricInChart x (extChartAt I x x))⁻¹ *
          complexHessian (f ∘ (extChartAt I x).symm) (extChartAt I x x)).trace) :=
      hcomplex
    _ = 2 * ω₀.laplacian f x := by rw [hkahler]

open scoped ComplexOrder MatrixOrder

private theorem pointwise_duality_energy
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    (hα : α.IsPositive) (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ)
    (y : EuclideanSpace ℂ (Fin n))
    (hℓ : ∀ v, ℓ v = α ![v, EuclideanSpace.complexStructure n y]) :
    ContinuousAlternatingMap.relTrace α (ContinuousAlternatingMap.dWedgeDBar ℓ) =
      ℓ y / 2 := by
  classical
  let A : Matrix (Fin n) (Fin n) ℂ := α.coeffMatrix
  let p : Fin n → ℂ := fun j ↦
    ((ℓ (EuclideanSpace.single j 1) : ℂ) -
      Complex.I * ℓ (Complex.I • EuclideanSpace.single j 1)) / 2
  have hp : p = Matrix.mulVec A (star y.ofLp) := by
    funext j
    let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
    have h1 : ℓ e = α ![e, Complex.I • y] := by
      simpa [EuclideanSpace.complexStructure] using hℓ e
    have h2 : ℓ (Complex.I • e) = α ![e, y] := by
      calc
        ℓ (Complex.I • e) = α ![Complex.I • e, Complex.I • y] := by
          simpa [EuclideanSpace.complexStructure] using hℓ (Complex.I • e)
        _ = α ![e, y] := hα.1 e y
    rw [hα.1.apply_eq e (Complex.I • y)] at h1
    rw [hα.1.apply_eq e y] at h2
    simp [Matrix.mulVec, p, A, e, EuclideanSpace.complexStructure] at *
    apply Complex.ext
    · change _ = (∑ x, α.coeffMatrix j x * star (y x)).re
      simp [h1, Complex.mul_re, Complex.conj_re, Finset.sum_add_distrib]
    · change _ = (∑ x, α.coeffMatrix j x * star (y x)).im
      simp [h2, Complex.mul_im, Complex.conj_im, Finset.sum_add_distrib]
  have hApos := (ContinuousAlternatingMap.isPositive_iff (α := α)).mp hα |>.2
  have hAherm := hApos.isHermitian
  have hpstar : (fun k ↦ ((ℓ (EuclideanSpace.single k 1) : ℂ) +
      Complex.I * ℓ (Complex.I • EuclideanSpace.single k 1)) / 2) = star p := by
    funext k
    simp [p]
  change RCLike.re ((α.coeffMatrix)⁻¹ *
      (ContinuousAlternatingMap.dWedgeDBar ℓ).coeffMatrix).trace = ℓ y / 2
  rw [ContinuousAlternatingMap.coeffMatrix_dWedgeDBar, hpstar]
  change RCLike.re (A⁻¹ * Matrix.vecMulVec p (star p)).trace = ℓ y / 2
  have hmul : A⁻¹ * Matrix.vecMulVec p (star p) =
      Matrix.vecMulVec (A⁻¹.mulVec p) (star p) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec, Matrix.mulVec_eq_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  change RCLike.re (A⁻¹ * Matrix.vecMulVec p (star p)).trace = ℓ y / 2
  rw [hmul, Matrix.trace_vecMulVec, dotProduct_comm]
  have hdet : IsUnit (α.coeffMatrix).det := isUnit_iff_ne_zero.mpr (by
    intro hd
    have hr := congrArg RCLike.re hd
    have hpos := (RCLike.pos_iff.mp hApos.det_pos).1
    simp at hr
    exact hpos.ne' hr)
  have hcancel : A⁻¹ * A = 1 := by
    simpa [A] using Matrix.nonsing_inv_mul A hdet
  have hinv : A⁻¹.mulVec p = star y.ofLp := by
    rw [hp]
    simp [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  rw [hinv]
  have hstarA (j k : Fin n) : star (A j k) = A k j := by
    simpa [A] using (hAherm.apply k j)
  have hdist (j : Fin n) :
      (∑ k : Fin n, y.ofLp k * star (A j k)) * star (y.ofLp j) =
        ∑ k, y.ofLp k * star (A j k) * star (y.ofLp j) := by
    rw [Finset.sum_mul]
  have hquad : star p ⬝ᵥ star y.ofLp =
      ∑ j, ∑ k, α.coeffMatrix j k * y.ofLp j * star (y.ofLp k) := by
    change ∑ j, star (p j) * star (y.ofLp j) = _
    rw [hp]
    change ∑ j, star (∑ k, A j k * star (y.ofLp k)) * star (y.ofLp j) = _
    calc
      _ = ∑ j, ∑ k, star (A j k) * y.ofLp k * star (y.ofLp j) := by
        simp only [star_sum, star_mul, star_star]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hdist j]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ∑ j, ∑ k, A k j * y.ofLp k * star (y.ofLp j) := by
        simp_rw [hstarA]
      _ = ∑ j, ∑ k, A j k * y.ofLp j * star (y.ofLp k) := by
        rw [Finset.sum_comm]
  rw [hquad]
  have hy : ℓ y = α ![y, Complex.I • y] := by
    simpa [EuclideanSpace.complexStructure] using hℓ y
  rw [hy, hα.1.apply_I_smul]
  change (∑ j, ∑ k, α.coeffMatrix j k * y.ofLp j * star (y.ofLp k)).re =
    2 * (∑ j, ∑ k, α.coeffMatrix j k * y.ofLp j * star (y.ofLp k)).re / 2
  ring

/-- The gradient-energy identity in the pointwise `gradFun` form used by the Sobolev
inequalities. -/
theorem riemannian_gradFun_energy_eq_two_mul_gradNormSq
    (ω₀ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f) (x : M) :
    ω₀.toRiemannianMetric.inner x
        (CalabiYau.Riemannian.gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric f x)
        (CalabiYau.Riemannian.gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric f x) =
      2 * ω₀.gradNormSq f x := by
  let y := CalabiYau.Riemannian.gradFun
    (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric f x
  let ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) f x)
  have hdual (v : EuclideanSpace ℂ (Fin n)) :
      ℓ v = ω₀ x ![v, EuclideanSpace.complexStructure n y] := by
    have h := CalabiYau.Riemannian.inner_gradFun_right
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric f x v
    rw [ω₀.toRiemannianMetric_inner_apply x v y] at h
    unfold KahlerForm.innerAt at h
    simp only [CalabiYau.tangentSpaceModelContinuousLinearEquiv_apply] at h
    have h' := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)) h
    convert h'.symm using 1 <;> rfl
  have hchart : fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) f x := by
    have hdiff : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) f x :=
      hf.mdifferentiableAt (by norm_num)
    simp [mfderiv, hdiff, writtenInExtChartAt, chartAt_self_eq]
  have hform : mdWedgeDBar n f x = ContinuousAlternatingMap.dWedgeDBar ℓ := by
    change ContinuousAlternatingMap.dWedgeDBar
      (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) = _
    rw [hchart]
    rfl
  have hpt := pointwise_duality_energy (ω₀.isPositive x) ℓ y hdual
  have henergy : ω₀.toRiemannianMetric.inner x y y = ℓ y := by
    have h := CalabiYau.Riemannian.inner_gradFun_right
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) ω₀.toRiemannianMetric f x y
    have h' := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x)) h
    convert h' using 1 <;> rfl
  calc
    _ = ℓ y := henergy
    _ = 2 * ω₀.gradNormSq f x := by
      rw [KahlerForm.gradNormSq, hform]
      nlinarith [hpt]

end KahlerForm
