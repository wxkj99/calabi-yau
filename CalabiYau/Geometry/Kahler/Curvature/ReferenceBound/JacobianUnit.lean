module

public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.Basic

/-!
# Nonsingularity of the centered holomorphic chart transition

The inverse transition is defined near `y`; the tangent-coordinate changes compose to the
identity. Thus the complex Jacobian has an inverse and its finite matrix has a unit
determinant. No assertion is made about the globally extended transition outside the overlap.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The Jacobian of the centered chart change `y → x` has a unit determinant at `y`.
This is the complex version of local invertibility of coordinate changes. -/
theorem referenceTransitionMatrix_isUnit_det (x y : M)
    (hy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source) :
    IsUnit (referenceTransitionMatrix (n := n) x y).det := by
  let Iℂ := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
  let f := referenceChartTransition (n := n) x y
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange Iℂ y x y
  let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange Iℂ x y y
  have hySelf : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := by
    exact mem_extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) y
  have hySelfC : y ∈ (extChartAt Iℂ y).source := by
    change y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source
    rw [← extChartAt_real_eq y]
    exact hySelf
  have hyXC : y ∈ (extChartAt Iℂ x).source := by
    change y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source
    rw [← extChartAt_real_eq x]
    exact hy
  have hcommon : y ∈ (extChartAt Iℂ y).source ∩ (extChartAt Iℂ x).source ∩
      (extChartAt Iℂ y).source := ⟨⟨hySelfC, hyXC⟩, hySelfC⟩
  have hcomp (v : EuclideanSpace ℂ (Fin n)) : B (A v) = v := by
    change tangentCoordChange Iℂ x y y (tangentCoordChange Iℂ y x y v) = v
    rw [tangentCoordChange_comp (I := Iℂ) (w := y) (x := x) (y := y)
      (z := y) (v := v) hcommon]
    exact tangentCoordChange_self (I := Iℂ) (x := y) (z := y) (v := v) hySelfC
  have htransition : f = extChartAt Iℂ x ∘ (extChartAt Iℂ y).symm := by
    dsimp [f, referenceChartTransition, Iℂ]
  have hderiv : fderiv ℂ f z = A := by
    calc
      fderiv ℂ f z = fderiv ℂ
          (extChartAt Iℂ x ∘ (extChartAt Iℂ y).symm) (extChartAt Iℂ y y) := by
        rw [htransition]
        simp [z, Iℂ]
      _ = tangentCoordChange Iℂ y x y := by
        rw [tangentCoordChange_def]
        change fderiv ℂ (extChartAt Iℂ x ∘ (extChartAt Iℂ y).symm) (extChartAt Iℂ y y) =
          fderivWithin ℂ (extChartAt Iℂ x ∘ (extChartAt Iℂ y).symm) (Set.range Iℂ)
            (extChartAt Iℂ y y)
        rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
      _ = A := rfl
  have hAexp (j : Fin n) : A (EuclideanSpace.single j (1 : ℂ)) =
      ∑ k, (EuclideanSpace.clmMatrix A k j) • EuclideanSpace.single k (1 : ℂ) := by
    ext i
    simp [EuclideanSpace.clmMatrix, Pi.single_apply]
  have hmatrix : (EuclideanSpace.clmMatrix B) * (EuclideanSpace.clmMatrix A) = 1 := by
    ext i j
    have hv : (B (A (EuclideanSpace.single j (1 : ℂ)))).ofLp i =
        (EuclideanSpace.single j (1 : ℂ)).ofLp i := by
      simpa only [ContinuousLinearMap.comp_apply] using
        congrArg (fun v : EuclideanSpace ℂ (Fin n) => v.ofLp i)
          (hcomp (EuclideanSpace.single j (1 : ℂ)))
    rw [hAexp j] at hv
    simp only [map_sum, map_smul] at hv
    simpa [EuclideanSpace.clmMatrix, Matrix.mul_apply, Pi.single_apply,
      mul_comm, mul_left_comm, mul_assoc, Matrix.one_apply] using hv
  change IsUnit (EuclideanSpace.clmMatrix (fderiv ℂ f z)).det
  rw [hderiv]
  exact Matrix.isUnit_det_of_left_inverse hmatrix

end KahlerForm
