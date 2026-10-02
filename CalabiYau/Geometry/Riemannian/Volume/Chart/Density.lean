-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/Measure/Chart/Density.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import CalabiYau.Geometry.Riemannian.Metric.Coordinates.ChartGram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace CalabiYau.RiemannianVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def chartDensity (g : SmoothRiemannianMetric I M) (x₀ : M) : M → ℝ :=
  fun x => Real.sqrt (CalabiYau.Tensor.Coordinates.chartGramMatrix g x₀ x).det

lemma chartDensity_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < chartDensity g x₀ x :=
  Real.sqrt_pos.mpr (CalabiYau.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g x₀ hx)
lemma chartDensity_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  intro x hx
  have hdet := CalabiYau.Tensor.Coordinates.chartGramMatrix_det_contMDiffOn (I := I) g x₀ x hx
  have hpos_ne : (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x).det ≠ 0 :=
    ne_of_gt (CalabiYau.Tensor.Coordinates.chartGramMatrix_det_pos (I := I) g x₀ hx)
  have hsqrt : ContDiffAt ℝ ∞ Real.sqrt
      (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ x).det :=
    Real.contDiffAt_sqrt hpos_ne
  have := hsqrt.comp_contMDiffWithinAt (f :=
      fun y : M => (CalabiYau.Tensor.Coordinates.chartGramMatrix (I := I) g x₀ y).det) hdet
  exact this

def chartDensityOnE (g : SmoothRiemannianMetric I M) (x₀ : M) : E → ℝ :=
  fun y => chartDensity (I := I) g x₀ ((extChartAt I x₀).symm y)

lemma chartDensityOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g x₀)
      (extChartAt I x₀).target := by
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞ (chartDensity (I := I) g x₀)
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    chartDensity_contMDiffOn (I := I) g x₀
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm
      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm (I := I) x₀
  have hsubset : (extChartAt I x₀).target ⊆
      (extChartAt I x₀).symm ⁻¹'
        (trivializationAt E (TangentSpace I) x₀).baseSet :=
    fun _ hy =>
      CalabiYau.Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet
        (I := I) x₀ hy
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((chartDensity (I := I) g x₀) ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

noncomputable def modelHaar : MeasureTheory.Measure E := (CalabiYau.Tensor.Coordinates.chartModelBasis E).addHaar

instance modelHaar_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure (modelHaar (E := E)) := by
  unfold modelHaar
  infer_instance

theorem map_toEuclidean_modelHaar_eq_volume :
    MeasureTheory.Measure.map (toEuclidean (E := E)) (modelHaar (E := E)) =
      (MeasureTheory.volume :
        MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  have h₁ :
      MeasureTheory.Measure.map (toEuclidean (E := E))
          (modelHaar (E := E)) =
        ((CalabiYau.Tensor.Coordinates.chartModelBasis E).map
            (toEuclidean (E := E)).toLinearEquiv).addHaar := by
    unfold modelHaar
    exact Module.Basis.map_addHaar (CalabiYau.Tensor.Coordinates.chartModelBasis E)
      (toEuclidean (E := E))
  rw [h₁]
  have hcancel :
      (CalabiYau.Tensor.Coordinates.chartModelBasis E).map (toEuclidean (E := E)).toLinearEquiv
        = (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis := by
    refine Module.Basis.eq_of_apply_eq ?_
    intro i
    have hb_i : (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis i
        = EuclideanSpace.single i (1 : ℝ) := by
      simp [OrthonormalBasis.coe_toBasis,
        EuclideanSpace.basisFun_apply (𝕜 := ℝ) (ι := Fin (Module.finrank ℝ E))]
    rw [Module.Basis.map_apply, CalabiYau.Tensor.Coordinates.chartModelBasis_apply, hb_i]
    simp
  rw [hcancel]
  exact (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).addHaar_eq_volume

def chartLocalMeasure
    (g : SmoothRiemannianMetric I M) (x₀ : M) : MeasureTheory.Measure M :=
  MeasureTheory.Measure.map (extChartAt I x₀).symm
    (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
      (fun y : E =>
        ENNReal.ofReal
          (chartDensity g x₀ ((extChartAt I x₀).symm y))))

lemma chartLocalMeasure_def
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    chartLocalMeasure (I := I) g x₀ =
      MeasureTheory.Measure.map (extChartAt I x₀).symm
        (((modelHaar (E := E)).restrict (extChartAt I x₀).target).withDensity
          (fun y : E =>
            ENNReal.ofReal
              (chartDensity g x₀ ((extChartAt I x₀).symm y)))) := rfl

end CalabiYau.RiemannianVolume
