module

public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor

/-!
# Holomorphic quadratic patch

A prescribed invertible complex-linear first jet and symmetric complex-bilinear second jet are
realized by a quadratic holomorphic polynomial. Restricting it to the inverse image of an open
coordinate target gives an actual local chart map with image in that target. This is the patching
step in Székelyhidi, §1.3, Proposition 1.16.

The statement records smoothness in the underlying real coordinates and complex differentiability
separately, because `YauNormalFrame` requires both. The patch need not be chosen uniformly in the
point: only its existence around the coordinate center is used. In dimension zero the map is the
unique map on the zero-dimensional space. In dimension one, the symmetric bilinear second jet is a
single complex coefficient, and the derivative at zero is still exactly the prescribed linear map.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

/-- The quadratic polynomial with linear part `A` and symmetric bilinear second jet `Q`. -/
noncomputable def quadraticChartMap {n : ℕ}
    (z₀ : EuclideanSpace ℂ (Fin n))
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
  fun v ↦ z₀ + A v + (1 / 2 : ℂ) • Q v v

/-- The complex Jacobian matrix of a map between the coordinate model and itself. -/
noncomputable def holomorphicJacobianMatrix
    {n : ℕ} (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  EuclideanSpace.clmMatrix (fderiv ℂ ψ z)

/-- The coefficient matrix of the pullback of a Kähler metric by a local holomorphic coordinate
map, in the convention `J.transpose * G * J.map star`. -/
noncomputable def pulledBackMetricInChart {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.transpose (holomorphicJacobianMatrix ψ z) *
    ω₀.metricInChart x (ψ z) * (holomorphicJacobianMatrix ψ z).map star

/-- The quadratic holomorphic map has an open patch around zero whose image lies in the requested
target. It retains the prescribed derivative at the center. -/
theorem exists_quadratic_chart_patch {n : ℕ}
    (U : Set (EuclideanSpace ℂ (Fin n))) (z₀ : EuclideanSpace ℂ (Fin n))
    (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (_hQ : ∀ u v, Q u v = Q v u) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ 0 ∈ V ∧
      (∀ v ∈ V, quadraticChartMap z₀ A.toContinuousLinearMap Q v ∈ U) ∧
      ContDiffOn ℝ ∞ (quadraticChartMap z₀ A.toContinuousLinearMap Q) V ∧
      DifferentiableOn ℂ (quadraticChartMap z₀ A.toContinuousLinearMap Q) V ∧
      quadraticChartMap z₀ A.toContinuousLinearMap Q 0 = z₀ ∧
      fderiv ℂ (quadraticChartMap z₀ A.toContinuousLinearMap Q) 0 =
        A.toContinuousLinearMap := by
  let f := quadraticChartMap z₀ A.toContinuousLinearMap Q
  have hquadSmooth : ContDiff ℝ ∞ (fun v : EuclideanSpace ℂ (Fin n) ↦ Q v v) := by
    let Qr := Q.bilinearRestrictScalars ℝ
    have hQr : ContDiff ℝ ∞ (fun p : EuclideanSpace ℂ (Fin n) ×
        EuclideanSpace ℂ (Fin n) ↦ Qr p.1 p.2) := Qr.isBoundedBilinearMap.contDiff
    convert hQr.comp (contDiff_id.prodMk contDiff_id) using 1 ;
      ext v; rfl
  have hfSmooth : ContDiff ℝ ∞ f := by
    change ContDiff ℝ ∞
      ((fun v : EuclideanSpace ℂ (Fin n) ↦ z₀ + A.toContinuousLinearMap v) +
        fun v ↦ (1 / 2 : ℂ) • Q v v)
    let Ar := A.toContinuousLinearMap.restrictScalars ℝ
    have hcoef : ContDiff ℝ ∞ (fun _ : EuclideanSpace ℂ (Fin n) ↦ (1 / 2 : ℂ)) :=
      contDiff_const
    have hleft : ContDiff ℝ ∞ (fun v ↦ z₀ + Ar v) := contDiff_const.add Ar.contDiff
    have hright : ContDiff ℝ ∞ (fun v ↦ (1 / 2 : ℂ) • Q v v) := hcoef.smul hquadSmooth
    convert hleft.add hright using 1; ext v; rfl
  have hquadHol : Differentiable ℂ (fun v : EuclideanSpace ℂ (Fin n) ↦ Q v v) := by
    exact Q.differentiable.clm_apply differentiable_id
  have hfHol : Differentiable ℂ f := by
    change Differentiable ℂ
      ((fun v : EuclideanSpace ℂ (Fin n) ↦ z₀ + A.toContinuousLinearMap v) +
        fun v ↦ (1 / 2 : ℂ) • Q v v)
    have hcoef : Differentiable ℂ (fun _ : EuclideanSpace ℂ (Fin n) ↦ (1 / 2 : ℂ)) :=
      differentiable_const _
    have hleft : Differentiable ℂ (fun v ↦ z₀ + A.toContinuousLinearMap v) :=
      (differentiable_const z₀).add A.toContinuousLinearMap.differentiable
    have hright : Differentiable ℂ (fun v ↦ (1 / 2 : ℂ) • Q v v) := hcoef.smul hquadHol
    exact hleft.add hright
  have hquadDeriv : HasFDerivAt (fun v : EuclideanSpace ℂ (Fin n) ↦ Q v v)
      (0 : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) 0 := by
    have hbilinear := Q.hasFDerivAt_of_bilinear
      (hasFDerivAt_id (0 : EuclideanSpace ℂ (Fin n)))
      (hasFDerivAt_id (0 : EuclideanSpace ℂ (Fin n)))
    have hzero : Q.precompR (EuclideanSpace ℂ (Fin n)) 0
          (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) +
        Q.precompL (EuclideanSpace ℂ (Fin n))
          (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) 0 = 0 := by
      ext v
      simp
    simpa [hzero] using hbilinear
  have hfDeriv : HasFDerivAt f A.toContinuousLinearMap 0 := by
    convert (((hasFDerivAt_const z₀ 0).add A.toContinuousLinearMap.hasFDerivAt).add
      (hquadDeriv.const_smul (1 / 2 : ℂ))) using 1
    all_goals first
    | rfl
    | simp
  let V := f ⁻¹' U
  refine ⟨V, hU.preimage hfSmooth.continuous, ?_, ?_, hfSmooth.contDiffOn,
    hfHol.differentiableOn, ?_, hfDeriv.fderiv⟩
  · change f 0 ∈ U
    simpa [f, quadraticChartMap] using hz₀
  · intro v hv
    exact hv
  · simp [quadraticChartMap]

end KahlerForm
