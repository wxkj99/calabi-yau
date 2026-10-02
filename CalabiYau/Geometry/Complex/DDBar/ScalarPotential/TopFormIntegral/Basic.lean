module

public import CalabiYau.Geometry.Kahler.Basic
public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.WedgePowers

/-!
# Signed top-form coefficients and the actual Kähler top form

The positive real frame is interleaved `(e₀, Ie₀, …, eₙ₋₁, Ieₙ₋₁)`.
`topFormCoeff` is evaluation of the actual alternating form, not the absolute
measure associated to a form. `topFormVolume` is the actual field `ωⁿ/n!`;
`signedTopFormDensity` is its signed scalar coefficient ratio. Identifying this
ratio with a coordinate integral is a separate theorem, not part of its definition.

Sources: Morita, *Geometry of Differential Forms*, §3.2(a), pp. 104–107
(oriented top-form integration); Wells, *Differential Analysis on Complex
Manifolds*, V §1, pp. 157–159 (complex orientation and `ωⁿ/n!`).
-/

@[expose] public section

namespace ContinuousAlternatingMap

/-- Real coordinate basis in positive complex orientation, in interleaved order. -/
noncomputable def complexInterleavedBasis (n : ℕ) :
    Module.Basis (Fin (2 * n)) ℝ (EuclideanSpace ℂ (Fin n)) :=
  (Complex.basisOneI.smulTower' ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)).reindex
    ((finProdFinEquiv (m := n) (n := 2)).trans
      (Equiv.cast (congrArg Fin (by omega : n * 2 = 2 * n))))

/-- The signed coefficient of a real top form in the positive complex frame. -/
noncomputable def topFormCoeff {n : ℕ}
    (Θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * n)]→L[ℝ] ℝ) : ℝ :=
  Θ (complexInterleavedBasis n)

/-- Top-form pullback multiplies the coefficient by the signed real determinant. -/
theorem topFormCoeff_compContinuousLinearMap {n : ℕ}
    (Θ : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * n)]→L[ℝ] ℝ)
    (L : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) :
    topFormCoeff (Θ.compContinuousLinearMap L) = L.det * topFormCoeff Θ := by
  let b := complexInterleavedBasis n
  have hΘ := congrArg
    (fun f : EuclideanSpace ℂ (Fin n) [⋀^Fin (2 * n)]→ₗ[ℝ] ℝ =>
      f (L.toLinearMap ∘ b)) (Θ.toAlternatingMap.eq_smul_basis_det b)
  have hdet : b.det (L.toLinearMap ∘ b) = L.det := by
    rw [Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  unfold topFormCoeff
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change Θ.toAlternatingMap (L.toLinearMap ∘ b) = L.det * Θ.toAlternatingMap b
  rw [hΘ]
  simp only [AlternatingMap.smul_apply]
  rw [hdet]
  ring

-- The empty wedge is the nonzero top-degree unit in complex dimension zero.
private example : topFormCoeff (wedgePow
    (0 : EuclideanSpace ℂ (Fin 0) [⋀^Fin 2]→L[ℝ] ℝ) 0) = 1 := by
  simp [topFormCoeff, wedgePow]

-- Positive complex-line orientation is `(e, Ie)`, not `(Ie, e)`.
private example : complexInterleavedBasis 1 0 = EuclideanSpace.single 0 (1 : ℂ) := by
  simp [complexInterleavedBasis, Module.Basis.reindex_apply, Module.Basis.smulTower'_apply,
    EuclideanSpace.basisFun_apply, finProdFinEquiv, Fin.modNat, Fin.divNat]

private example : complexInterleavedBasis 1 1 =
    Complex.I • EuclideanSpace.single 0 (1 : ℂ) := by
  simp [complexInterleavedBasis, Module.Basis.reindex_apply, Module.Basis.smulTower'_apply,
    EuclideanSpace.basisFun_apply, finProdFinEquiv, Fin.modNat, Fin.divNat]

-- In dimension two the second pair starts at index two, not after all real parts.
private example : complexInterleavedBasis 2 2 = EuclideanSpace.single 1 (1 : ℂ) := by
  simp [complexInterleavedBasis, Module.Basis.reindex_apply, Module.Basis.smulTower'_apply,
    EuclideanSpace.basisFun_apply, finProdFinEquiv, Fin.modNat, Fin.divNat]

end ContinuousAlternatingMap

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The actual real top-degree field `ωⁿ/n!`, using unnormalized wedge powers. -/
noncomputable def topFormVolume (ω₀ : KahlerForm n M) :
    FormField (EuclideanSpace ℂ (Fin n)) M (2 * n) :=
  fun y => (Nat.factorial n : ℝ)⁻¹ • ContinuousAlternatingMap.wedgePow (ω₀ y) n

/-- Signed scalar density relative to the actual Kähler top form at the same point.
The coordinate and integration bridges are proved in separate modules. -/
noncomputable def signedTopFormDensity (ω₀ : KahlerForm n M)
    (Θ : FormField (EuclideanSpace ℂ (Fin n)) M (2 * n)) : M → ℝ :=
  fun y => ContinuousAlternatingMap.topFormCoeff (Θ y) /
    ContinuousAlternatingMap.topFormCoeff (ω₀.topFormVolume y)

end KahlerForm
