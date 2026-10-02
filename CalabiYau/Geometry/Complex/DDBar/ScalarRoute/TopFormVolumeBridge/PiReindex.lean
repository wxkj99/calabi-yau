module

public import CalabiYau.Geometry.Complex.DDBar.ScalarRoute.TopFormVolumeBridge.Realification
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Interleaved real Pi coordinates and complex Euclidean volume

The index `(j, a)` corresponds to `2 * j + a`, where `a = 0` is the real part
and `a = 1` the imaginary part. The plain Pi space has its sup norm: its conversion
to real Euclidean space is continuous-linear, not an inner-product isometry.

The measure proof follows `volume_measurePreserving_piCongrLeft`, then the public
realification volume theorem, and finally `MeasurePreserving.symm`. It also holds
in dimension zero; no positivity assumption from Stokes is needed here.
-/

@[expose] public section

open MeasureTheory

namespace HTopFormVolumeBridge

/-- The interleaved index order, real then imaginary within each complex coordinate. -/
def hTopFrameIndex (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  (finProdFinEquiv (m := n) (n := 2)).trans
    (Equiv.cast (congrArg Fin (by omega : n * 2 = 2 * n)))

/-- The interleaved finite-Pi reindexing preserves product Lebesgue measure. -/
theorem hTopFrameIndex_measurePreserving (n : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * n) => ℝ) (hTopFrameIndex n)) := by
  exact volume_measurePreserving_piCongrLeft
    (fun _ : Fin (2 * n) => ℝ) (hTopFrameIndex n)

/-- Reindex plain real coordinates and equip them with the Euclidean norm.
This equivalence is not asserted to preserve the Pi-sup norm. -/
noncomputable def hTopPiToRealEquiv (n : ℕ) :
    (Fin (2 * n) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin 2) := by
  let e₁ : (Fin n × Fin 2 → ℝ) ≃ₗ[ℝ] (Fin (2 * n) → ℝ) :=
    LinearEquiv.piCongrLeft ℝ (fun _ : Fin (2 * n) => ℝ) (hTopFrameIndex n)
  exact e₁.symm.toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin n × Fin 2) ℝ).symm

/-- The actual continuous-linear coordinate equivalence from interleaved real Pi
coordinates to complex Euclidean space. -/
noncomputable def hTopPiToComplexEquiv (n : ℕ) :
    (Fin (2 * n) → ℝ) ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (hTopPiToRealEquiv n).trans
    (complexToRealCoordinateEquiv (n := n)).symm.toContinuousLinearEquiv

/-- The actual Pi-to-complex coordinate equivalence preserves canonical volume.
No extra realification or analytic hypothesis is required. -/
theorem hTopPiToComplexEquiv_measurePreserving {n : ℕ} :
    MeasurePreserving (hTopPiToComplexEquiv n) := by
  let e : MeasurableEquiv (Fin n × Fin 2 → ℝ) (Fin (2 * n) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (2 * n) => ℝ) (hTopFrameIndex n)
  have hPerm : MeasurePreserving e := hTopFrameIndex_measurePreserving n
  let m : MeasurableEquiv (EuclideanSpace ℂ (Fin n)) (Fin (2 * n) → ℝ) :=
    (complexToRealCoordinateEquiv (n := n)).toMeasurableEquiv.trans
      ((EuclideanSpace.equiv (Fin n × Fin 2) ℝ).toHomeomorph.toMeasurableEquiv.trans e)
  have hm : MeasurePreserving m := by
    change MeasurePreserving (fun z : EuclideanSpace ℂ (Fin n) =>
      e (((complexToRealCoordinateEquiv z : EuclideanSpace ℝ (Fin n × Fin 2)) :
        Fin n × Fin 2 → ℝ)))
    exact hPerm.comp (complexToRealCoordinateEquiv_toPi_measurePreserving (n := n))
  have hEq : (hTopPiToComplexEquiv n : (Fin (2 * n) → ℝ) →
      EuclideanSpace ℂ (Fin n)) = m.symm := by
    funext y
    change (complexToRealCoordinateEquiv (n := n)).symm
        ((EuclideanSpace.equiv (Fin n × Fin 2) ℝ).symm
          ((LinearEquiv.piCongrLeft ℝ (fun _ : Fin (2 * n) => ℝ)
            (hTopFrameIndex n)).symm y)) =
      (complexToRealCoordinateEquiv (n := n)).symm
        ((EuclideanSpace.equiv (Fin n × Fin 2) ℝ).symm (e.symm y))
    apply (complexToRealCoordinateEquiv (n := n)).injective
    apply (EuclideanSpace.equiv (Fin n × Fin 2) ℝ).injective
    ext p
    rfl
  rw [hEq]
  exact hm.symm

end HTopFormVolumeBridge
