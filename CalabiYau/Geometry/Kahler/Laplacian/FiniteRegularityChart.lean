module

public import CalabiYau.Geometry.Kahler.Laplacian

/-!
# The chart formula for the complex Laplacian at finite regularity

The coordinate formula underlying GT, Lemma 6.36, p. 136, needs only two derivatives.
This is the C² version of `KahlerForm.laplacian_eq_inChart`; it does not assert that
the harmonic limit is smooth. The contraction is `re tr(g⁻¹ H)`, with matrix indices in
that order, and `H_{j k} = ∂_j ∂̄_k f` uses the project's quarter-real-Laplacian convention.
-/

set_option autoImplicit false

@[expose] public section

open scoped Manifold ContDiff
open ContinuousAlternatingMap

namespace KahlerForm

/-- The existing complex Laplacian agrees with its fixed-chart formula for a C² function.
The proof must use the C² transformation rule for `mddbar`, rather than the smooth-only
chart lemma as a hypothesis. In dimension one with `g=1` this is `(f_xx+f_yy)/4`. -/
theorem laplacian_eq_inChart_of_contMDiff_two
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (⊤ : ℕ∞ω) M]
    (ω₁ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f)
    (x : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₁.laplacian f y = RCLike.re
      ((ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))⁻¹ *
        complexHessian (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).trace := by
  have hIsOneOne : (mddbar n f).IsOneOne := by
    intro p
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) p
    have hz : e p ∈ e.target := mem_extChartAt_target p
    have hsymm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 e.symm (e p) := by
      exact ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) p).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds hz)).of_le
          (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    have hfM : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2
        (f ∘ e.symm) (e p) := (hf p).comp_of_eq hsymm (e.left_inv (mem_extChartAt_source p))
    have hfC : ContDiffAt ℝ 2 (f ∘ e.symm) (e p) :=
      (contMDiffAt_iff_contDiffAt).mp hfM
    change (ddbar (f ∘ e.symm) (e p)).IsOneOne
    exact isOneOne_ddbar hfC
  let ψ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := ψ y
  have hy' : y ∈ ψ.source := by simpa [ψ, ← extChartAt_source] using hy
  have hz : z ∈ ψ.target := ψ.map_source hy'
  have hzpoint : ψ.symm z = y := ψ.left_inv hy'
  have hychart : y ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [extChartAt_real_eq, ← extChartAt_source] using hy
  have hyCy : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hOverlap : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∩
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := ⟨hy', hychart⟩
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    toLinearEquiv := {
      toFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
      invFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
      left_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
          exact ⟨⟨hyC, hyCy⟩, hyC⟩
        have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v) htriple
        calc
          _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := hc
          _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (x := x) (z := y) hyC
      right_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
          exact ⟨⟨hyCy, hyC⟩, hyCy⟩
        have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v) htriple
        calc
          _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := hc
          _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (x := y) (z := y) (by simp)
      map_add' := by intro u v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_add u v
      map_smul' := by intro c v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_smul c v
    }
    continuous_toFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).continuous
    continuous_invFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y).continuous
  }
  have hA : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    have hdef : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
        fderiv ℝ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
      rw [tangentCoordChange_def]
      simp [z, ψ]
    calc
      _ = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y := hdef.symm
      _ = (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ :=
        tangentCoordChange_real_eq hOverlap
      _ = _ := rfl
  have hrep (β : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
      β.chartRep x z = (β y).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    rw [FormField.chartRep_eq_chartRep_comp (x := x) (x' := y) (z := z) hz]
    · rw [hzpoint, FormField.chartRep_self, hA]
    · have heq : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z = y := by
        simpa [ψ] using hzpoint
      rw [heq]
      exact hychart
  have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap
    (ω₁.isOneOne y) (hIsOneOne y) A
  have hddbar := chartRep_mddbar_of_contMDiff_two hf x hz
  calc
    ω₁.laplacian f y = relTrace (ω₁ y) (mddbar n f y) := rfl
    _ = relTrace ((ω₁ y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        ((mddbar n f y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) :=
      htrace.symm
    _ = RCLike.re
        ((ω₁.metricInChart x z)⁻¹ * complexHessian (f ∘ ψ.symm) z).trace := by
      rw [← hrep ω₁.toFormField, ← hrep (mddbar n f), hddbar]
      rfl

end KahlerForm
