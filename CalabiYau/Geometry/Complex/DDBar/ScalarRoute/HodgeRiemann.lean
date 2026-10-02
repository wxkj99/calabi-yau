module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.HodgeRiemann.PrimitiveDiagonal
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.HodgeRiemann.WedgeQuadratic
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.HodgeRiemann.MetricNorm
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TraceWedge.PullbackNaturality

/-!
# Pointwise Hodge–Riemann identity for primitive real `(1,1)`-forms

For `n ≥ 2`, a primitive real `(1,1)`-form has negative square under the
unnormalized wedge pairing. The coefficient is `1/[n(n-1)]`; the norm is the
squared norm induced by the Kähler metric (equivalently the Hermitian matrix
trace square), with the exterior norm normalized by `2!`.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §4.1,
Lemma 4.7; Huybrechts, *Complex Geometry: An Introduction*, §3.3,
Proposition 3.3.15.
-/

open scoped Manifold ContDiff

@[expose] public section

namespace ContinuousAlternatingMap

private theorem hodgePullback_injective {n k : ℕ}
    (A : V n ≃L[ℂ] V n) :
    Function.Injective (fun φ : Form n k => φ.compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)) := by
  intro α β h
  ext v
  have hv := congrArg (fun φ : Form n k => φ (fun i => A.symm (v i))) h
  change α (fun i => A (A.symm (v i))) = β (fun i => A (A.symm (v i))) at hv
  simpa only [A.apply_symm_apply] using hv

private theorem hodgeTrace_eq_sum_of_normalFrame {n : ℕ}
    (ω₀ γ : Form n 2) (hω₀ : ω₀.IsPositive) (hγ : γ.IsOneOne)
    (A : V n ≃L[ℂ] V n) (lam : Fin n → ℝ)
    (hAω₀ : (ω₀.compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix = 1)
    (hAγ : (γ.compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix =
        Matrix.diagonal (fun i => (lam i : ℂ))) :
    (∑ i, lam i) = ω₀.relTrace γ := by
  rw [← relTrace_compContinuousLinearMap hω₀.1 hγ A]
  unfold relTrace
  rw [hAω₀, hAγ, inv_one, one_mul, Matrix.trace_diagonal]
  simp

private theorem hodgeWedgeEigenvalueContraction {n : ℕ} (hn : 2 ≤ n)
    (ω₀ γ : Form n 2) (hω₀ : ω₀.IsPositive) (hγ : γ.IsOneOne)
    (A : V n ≃L[ℂ] V n) (lam : Fin n → ℝ)
    (hAω₀ : (ω₀.compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix = 1)
    (hAγ : (γ.compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix =
        Matrix.diagonal (fun i => (lam i : ℂ))) :
    hodgeWedgeSquare hn ω₀ γ =
      (((∑ i, lam i) ^ 2 - ∑ i, lam i ^ 2) / ((n : ℝ) * (n - 1)) ) •
        wedgePow ω₀ n := by
  apply hodgePullback_injective A
  change (hodgeWedgeSquare hn ω₀ γ).compContinuousLinearMap _ =
    (_ • wedgePow ω₀ n).compContinuousLinearMap _
  rw [hodgeWedgeSquare_compContinuousLinearMap,
    ContinuousAlternatingMap.compContinuousLinearMap_smul, wedgePow_pullback]
  exact hodgeWedgeQuadraticNormalized hn _ _
    (hω₀.1.compContinuousLinearMap A.toContinuousLinearMap)
    (hγ.compContinuousLinearMap A.toContinuousLinearMap) lam hAω₀ hAγ

/-- Pointwise Hodge–Riemann identity for a primitive real `(1,1)`-form.
The raw wedge powers are not factorial-divided. -/
public theorem hodgeRiemann_primitive_oneOne {n : ℕ} (hn : 2 ≤ n)
    (ω₀ γ : Form n 2) (hω₀ : ω₀.IsPositive) (hγ : γ.IsOneOne)
    (htrace : ω₀.relTrace γ = 0) :
    hodgeWedgeSquare hn ω₀ γ =
      (-(1 / ((n : ℝ) * (n - 1))) * hodgeNormSq ω₀ γ) • wedgePow ω₀ n := by
  obtain ⟨A, lam, hAω₀, hAγ⟩ :=
    exists_normalFrame_diagonal_equiv ω₀ γ hω₀ hγ
  have htr := hodgeTrace_eq_sum_of_normalFrame ω₀ γ hω₀ hγ A lam hAω₀ hAγ
  have hw := hodgeWedgeEigenvalueContraction hn ω₀ γ hω₀ hγ A lam hAω₀ hAγ
  have hnorm := hodgeNormSq_eq_eigenvalues ω₀ γ hω₀ hγ A lam hAω₀ hAγ
  rw [hw, hnorm, htr, htrace]
  ring_nf

/-- The same primitive identity for a two-form field, using the actual
`ω₀`-induced Riemannian metric and its exterior norm divided by `2!`. -/
public theorem hodgeRiemann_pointwise {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (V n) M]
    [IsManifold 𝓘(ℂ, V n) ω M]
    (hn : 2 ≤ n) (ω₀ : KahlerForm n M)
    (γ : FormField (V n) M 2) (hγ : γ.IsOneOne)
    (x : M) (htrace : (ω₀ x).relTrace (γ x) = 0) :
    hodgeWedgeSquare hn (ω₀ x) (γ x) =
      (-(1 / ((n : ℝ) * (n - 1))) *
        FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ) •
          wedgePow (ω₀ x) n := by
  obtain ⟨A, lam, hAω₀, hAγ⟩ :=
    exists_normalFrame_diagonal_equiv (ω₀ x) (γ x) (ω₀.isPositive x) (hγ x)
  have hbridge := hodgeNormSq_eq_pointwiseRealInner_of_normalFrame
    ω₀ γ x lam A hAω₀ (hγ x) hAγ
  rw [hodgeRiemann_primitive_oneOne hn (ω₀ x) (γ x)
    (ω₀.isPositive x) (hγ x) htrace, hbridge]

end ContinuousAlternatingMap

end
