-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Metric/Coordinates/ChartGram.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Metric.Basic
public import CalabiYau.Geometry.Manifold.Coordinates.Frame.Chart
public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace CalabiYau.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

export CalabiYau (SmoothRiemannianMetric)

def chartGramMatrix (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) x₀ i x)
      (chartBasisVecFiber (I := I) x₀ j x)

@[simp] lemma chartGramMatrix_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g x₀ x i j =
      g.inner x
        (chartBasisVecFiber (I := I) x₀ i x)
        (chartBasisVecFiber (I := I) x₀ j x) := rfl

lemma chartGramMatrix_isHermitian
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M) :
    (chartGramMatrix g x₀ x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (chartGramMatrix g x₀ x j i) = chartGramMatrix g x₀ x i j
  rw [chartGramMatrix_apply, chartGramMatrix_apply, star_trivial]
  exact g.symm x
    (chartBasisVecFiber (I := I) x₀ j x)
    (chartBasisVecFiber (I := I) x₀ i x)

lemma chartGramMatrix_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M) (x₀ : M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (chartGramMatrix g x₀ x) *ᵥ c =
      g.inner x
        (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
        (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x) := by
  have hexpand' :
      g.inner x
          (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
          (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x)
        = ∑ i, ∑ j, (c i * c j) *
            g.inner x
              (chartBasisVecFiber (I := I) x₀ i x)
              (chartBasisVecFiber (I := I) x₀ j x) := by
    have hL :
        g.inner x (∑ i, c i • chartBasisVecFiber (I := I) x₀ i x)
          = ∑ i, c i • g.inner x (chartBasisVecFiber (I := I) x₀ i x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    rw [hL]
    rw [sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [smul_apply]
    have hR :
        g.inner x (chartBasisVecFiber (I := I) x₀ i x)
            (∑ j, c j • chartBasisVecFiber (I := I) x₀ j x)
          = ∑ j, c j *
              g.inner x
                (chartBasisVecFiber (I := I) x₀ i x)
                (chartBasisVecFiber (I := I) x₀ j x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand']
  simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

lemma chartGramMatrix_posDef
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (chartGramMatrix g x₀ x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (chartGramMatrix_isHermitian (I := I) g x₀ x) ?_
  intro c hc
  set w : TangentSpace I x :=
    ∑ i, c i • chartBasisVecFiber (I := I) x₀ i x with hw_def
  have heq := chartGramMatrix_dotProduct_mulVec (I := I) g x₀ x c
  rw [heq]
  have hwnz : w ≠ 0 := by
    intro hw0
    have hli := chartBasisFamily_linearIndependent (I := I) x₀ hx
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hw0)
    exact hc this
  exact g.pos x w hwnz

lemma chartGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    0 < (chartGramMatrix g x₀ x).det :=
  (chartGramMatrix_posDef (I := I) g x₀ hx).det_pos

lemma chartGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix g x₀ x i j)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b))
      (trivializationAt E (TangentSpace I) x₀).baseSet :=
    g.contMDiff.contMDiffOn
  have hv := chartBasisVec_contMDiffOn (I := I) x₀ i
  have hw := chartBasisVec_contMDiffOn (I := I) x₀ j
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m
              (chartBasisVecFiber (I := I) x₀ i m)
              (chartBasisVecFiber (I := I) x₀ j m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) x₀).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hv hw
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

lemma chartGramMatrix_det_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => (chartGramMatrix g x₀ x).det)
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  classical
  have hexp :
      (fun x : M => (chartGramMatrix g x₀ x).det)
        = (fun x : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ i, chartGramMatrix g x₀ x (σ i) i) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd (fun i _ => ?_)
  exact chartGramMatrix_entry_contMDiffOn (I := I) g x₀ (σ i) i

end CalabiYau.Tensor.Coordinates

namespace CalabiYau.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

end CalabiYau.Riemannian
