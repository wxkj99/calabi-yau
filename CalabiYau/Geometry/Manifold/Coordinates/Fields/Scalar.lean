-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Coordinates/Fields/Scalar.lean
-- Locally modified.
module
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

noncomputable section

open Manifold Set
open scoped Manifold Topology ContDiff

namespace CalabiYau.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def scalarOnE (x₀ : M) (f : M → ℝ) : E → ℝ :=
  fun y => f ((extChartAt I x₀).symm y)

omit [IsManifold I ∞ M] in
lemma scalarOnE_def (x₀ : M) (f : M → ℝ) (y : E) :
    scalarOnE (I := I) x₀ f y = f ((extChartAt I x₀).symm y) := rfl

omit [IsManifold I ∞ M] in
lemma scalarOnE_extChartAt (x₀ : M) (f : M → ℝ) {x : M}
    (hx : x ∈ (extChartAt I x₀).source) :
    scalarOnE (I := I) x₀ f (extChartAt I x₀ x) = f x := by
  change f ((extChartAt I x₀).symm (extChartAt I x₀ x)) = f x
  rw [(extChartAt I x₀).left_inv hx]

lemma scalarOnE_contDiffOn (x₀ : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (scalarOnE (I := I) x₀ f)
      (extChartAt I x₀).target := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm
      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm (I := I) x₀
  have hf_on : ContMDiffOn I 𝓘(ℝ) ∞ f univ := hf.contMDiffOn
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target :=
    hf_on.comp hsymm (fun _ _ => mem_univ _)
  exact hcomp.contDiffOn

lemma scalarOnE_contDiffWithinAt
    (x₀ : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffWithinAt ℝ ∞ (scalarOnE (I := I) x₀ f)
      (extChartAt I x₀).target y :=
  scalarOnE_contDiffOn (I := I) x₀ hf y hy

end CalabiYau.Tensor.Coordinates
