module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.Basic
public import CalabiYau.Geometry.Complex.Schauder.RealCoordinateEquiv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

open MeasureTheory

namespace HTopFormVolumeBridge

/-- The positive interleaved complex frame agrees with the product real coordinate frame,
reindexed from `Fin n × Fin 2` to `Fin (2 * n)`. -/
theorem complexInterleavedBasis_image {n : ℕ} (p : Fin n × Fin 2) :
    ContinuousAlternatingMap.complexInterleavedBasis n
      (((finProdFinEquiv (m := n) (n := 2)).trans
        (Equiv.cast (congrArg Fin (by omega : n * 2 = 2 * n))) p)) =
    complexRealCoordinateBasis p := by
  classical
  unfold ContinuousAlternatingMap.complexInterleavedBasis
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  rcases p with ⟨i, a⟩
  fin_cases a <;> simp [Module.Basis.smulTower'_apply,
    EuclideanSpace.basisFun_apply, complexRealCoordinateBasis]

/-- The positive interleaved complex frame maps to the product real coordinate frame.
Thus the signed orientation is positive in this ordering, unlike grouped real/imaginary blocks. -/
theorem realification_interleaved_basis_image {n : ℕ} (p : Fin n × Fin 2) :
    complexToRealCoordinateEquiv
      (ContinuousAlternatingMap.complexInterleavedBasis n
        (((finProdFinEquiv (m := n) (n := 2)).trans
          (Equiv.cast (congrArg Fin (by omega : n * 2 = 2 * n))) p))) =
    EuclideanSpace.basisFun (Fin n × Fin 2) ℝ p := by
  rw [complexInterleavedBasis_image]
  ext q
  rcases p with ⟨i, a⟩
  rcases q with ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [complexToRealCoordinateEquiv_apply, complexRealCoordinateBasis,
      Complex.coe_basisOneI_repr, EuclideanSpace.basisFun_apply] <;>
    split_ifs <;> norm_num [Complex.I_re, Complex.I_im]

/-- The complex-to-real coordinate isometry preserves the canonical Euclidean volume measures. -/
theorem complexToRealCoordinateEquiv_measurePreserving {n : ℕ} :
    MeasurePreserving (complexToRealCoordinateEquiv (n := n)) := by
  exact LinearIsometryEquiv.measurePreserving _

/-- Realification also preserves volume when its target is written as the plain product function
space. The final `WithLp.ofLp` conversion is continuous-linear, not an isometry to the Pi-sup norm. -/
theorem complexToRealCoordinateEquiv_toPi_measurePreserving {n : ℕ} :
    MeasurePreserving (fun z : EuclideanSpace ℂ (Fin n) =>
      ((complexToRealCoordinateEquiv z : EuclideanSpace ℝ (Fin n × Fin 2)) :
        Fin n × Fin 2 → ℝ)) := by
  change MeasurePreserving
    ((@WithLp.ofLp 2 (Fin n × Fin 2 → ℝ)) ∘ complexToRealCoordinateEquiv)
  have h₁ : MeasurePreserving (complexToRealCoordinateEquiv (n := n))
      (volume : Measure (EuclideanSpace ℂ (Fin n)))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) :=
    complexToRealCoordinateEquiv_measurePreserving (n := n)
  have h₂ : MeasurePreserving (@WithLp.ofLp 2 (Fin n × Fin 2 → ℝ))
      (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))
      (volume : Measure (Fin n × Fin 2 → ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin n × Fin 2)
  exact h₂.comp h₁

end HTopFormVolumeBridge
