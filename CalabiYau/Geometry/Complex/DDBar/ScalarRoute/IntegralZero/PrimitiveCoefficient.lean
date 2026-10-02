module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.HodgeRiemann
public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.Basic

/-!
# Primitive top-form coefficient relative to Kähler volume

The pointwise Hodge–Riemann identity gives the signed coefficient of the raw
primitive square wedge. This module converts its coefficient relative to
`ω^n` into the coefficient relative to the actual normalized top form
`ω^n/n!`. No smoothness, exactness, or global Stokes hypothesis is required.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, Lemma 4.7;
Huybrechts, *Complex Geometry*, §3.3, Proposition 3.3.15.
-/

open scoped Manifold ContDiff

@[expose] public section

namespace ContinuousAlternatingMap

private theorem factorial_coefficient (n : ℕ) (hn : 2 ≤ n) (q z : ℝ) :
    (-(1 / ((n : ℝ) * (n - 1))) * q) * z =
      (-((n - 2).factorial : ℝ) * q) * ((n.factorial : ℝ)⁻¹ * z) := by
  have hf : n.factorial = n * (n - 1) * (n - 2).factorial := by
    have hn' : n = (n - 2) + 2 := by omega
    conv_lhs => rw [hn']
    rw [show (n - 2) + 2 = ((n - 2) + 1) + 1 by omega,
      Nat.factorial_succ, Nat.factorial_succ]
    rw [show n - 2 + 1 + 1 = n by omega,
      show n - 2 + 1 = n - 1 by omega]
    ring
  have hfR : (n.factorial : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n - 2).factorial : ℝ) := by
    rw [hf, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]
    simp
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hNm : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    linarith
  have hF : ((n - 2).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - 2)
  rw [hfR]
  field_simp

private theorem right_wedge_eq_hodgeWedgeSquare {n : ℕ} (hn : 2 ≤ n)
    (ωform γ : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    (γ ∧[ℝ] (γ ∧[ℝ] wedgePow ωform (n - 2))).domDomCongr
      (Fin.castOrderIso (by omega : 2 + (2 + 2 * (n - 2)) = 2 * n)) =
      hodgeWedgeSquare hn ωform γ := by
  unfold hodgeWedgeSquare
  rw [← wedge_mul_assoc γ γ (wedgePow ωform (n - 2))]
  ext v
  simp only [domDomCongr_apply]
  apply congrArg (γ ∧[ℝ] (γ ∧[ℝ] wedgePow ωform (n - 2)))
  funext i
  apply congrArg v
  apply Fin.ext
  rfl

end ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Signed coefficient of the raw primitive square wedge relative to the actual
Kähler top form `ω₀^n/n!`. This is pointwise: `γ` need not be smooth or exact. -/
theorem primitive_exact_wedge_topFormCoeff (hn : 2 ≤ n) (ω₀ : KahlerForm n M)
    {γ : FormField (EuclideanSpace ℂ (Fin n)) M 2} (hγ : γ.IsOneOne) (x : M)
    (htrace : (ω₀ x).relTrace (γ x) = 0) :
    ContinuousAlternatingMap.topFormCoeff
        ((γ x ∧[ℝ] (γ x ∧[ℝ]
          ContinuousAlternatingMap.wedgePow (ω₀ x) (n - 2))).domDomCongr
          (Fin.castOrderIso
            (by omega : 2 + (2 + 2 * (n - 2)) = 2 * n))) =
      -((n - 2).factorial : ℝ) *
        FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ *
        ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume x) := by
  rw [ContinuousAlternatingMap.right_wedge_eq_hodgeWedgeSquare hn]
  rw [ContinuousAlternatingMap.hodgeRiemann_pointwise hn ω₀ γ hγ x htrace]
  simp only [ContinuousAlternatingMap.topFormCoeff, KahlerForm.topFormVolume]
  exact ContinuousAlternatingMap.factorial_coefficient n hn
    (FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ)
    (ContinuousAlternatingMap.wedgePow (ω₀ x) n
      (ContinuousAlternatingMap.complexInterleavedBasis n))

end KahlerForm
