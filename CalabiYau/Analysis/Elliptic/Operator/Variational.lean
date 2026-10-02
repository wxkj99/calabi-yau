-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Operator/Variational.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.L2
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def h1ComplBilin (g : SmoothRiemannianMetric I M) :
    H1Compl g →L[ℝ] H1Compl g →L[ℝ] ℝ :=
  innerSL ℝ

@[simp] lemma h1ComplBilin_apply (g : SmoothRiemannianMetric I M)
    (u v : H1Compl g) :
    h1ComplBilin (I := I) (M := M) g u v = ⟪u, v⟫_ℝ := rfl

noncomputable def lpFunctionalCLM (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      (H1Compl g →L[ℝ] ℝ) :=
  let applyL : (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ) →L[ℝ]
      (H1Compl g →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) →L[ℝ]
        (H1Compl g →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (H1Compl g)
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) ℝ
  ((applyL.flip) (h1ComplToLp (I := I) (M := M) g)).comp
    (innerSL ℝ : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] ℝ)

@[simp] lemma lpFunctionalCLM_apply (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (v : H1Compl g) :
    lpFunctionalCLM (I := I) (M := M) g f v =
      ⟪h1ComplToLp (I := I) (M := M) g v, f⟫_ℝ := by
  change (innerSL ℝ f) (h1ComplToLp (I := I) (M := M) g v) =
    ⟪h1ComplToLp (I := I) (M := M) g v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (h1ComplToLp (I := I) (M := M) g v) f

noncomputable def h1ComplRieszRepr (g : SmoothRiemannianMetric I M) :
    (H1Compl g →L[ℝ] ℝ) →L[ℝ] H1Compl g :=
  LinearMap.mkContinuous
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (H1Compl g)).symm φ
      map_add' := fun φ ψ => by
        exact (InnerProductSpace.toDual ℝ (H1Compl g)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (H1Compl g)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (H1Compl g)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (H1Compl g)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (H1Compl g)).symm φ‖ ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq ((InnerProductSpace.toDual ℝ (H1Compl g)).symm.norm_map φ))

lemma h1ComplRieszRepr_inner (g : SmoothRiemannianMetric I M)
    (φ : H1Compl g →L[ℝ] ℝ) (w : H1Compl g) :
    ⟪h1ComplRieszRepr (I := I) (M := M) g φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (H1Compl g)).symm φ, w⟫_ℝ = φ w
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H1Compl g) (x := w) (y := φ)

noncomputable def resolvent (g : SmoothRiemannianMetric I M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) →L[ℝ] H1Compl g :=
  (h1ComplRieszRepr (I := I) (M := M) g).comp
    (lpFunctionalCLM (I := I) (M := M) g)

theorem resolvent_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric I M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    (v : H1Compl g) :
    ⟪resolvent (I := I) (M := M) g f, v⟫_ℝ =
      ⟪h1ComplToLp (I := I) (M := M) g v, f⟫_ℝ := by
  unfold resolvent
  rw [ContinuousLinearMap.comp_apply, h1ComplRieszRepr_inner,
    lpFunctionalCLM_apply]

end Laplacian
end Analysis
end CalabiYau

end
