-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Geometry/Operator/Gradient/NormSquared.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.Operator.Hessian.Basic
public import CalabiYau.Geometry.Riemannian.Curvature.Riemann.Defs
public import CalabiYau.Geometry.Riemannian.TensorInner.Tangent.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

@[expose] public section

noncomputable section

open CalabiYau.DivergenceTheorem
open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace CalabiYau.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

def normGradSqFun (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) : ℝ :=
  g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)


namespace BochnerInternal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma contMDiff_g_inner
    (g : SmoothRiemannianMetric I M)
    {v w : ∀ x : M, TangentSpace I x}
    (hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (v x)))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (w x))) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b (v b) (w b)) := by
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := ContMDiff.inner_bundle (F := E) (B := M) (E := (TangentSpace I : M → Type _))
    (b := fun x => x) (v := v) (w := w) hv hw
  refine h.congr ?_
  intro b
  rfl

end BochnerInternal

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem contMDiff_g_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M)
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b (X b) (Y b)) := by
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (X x)) := X.contMDiff
  have hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _)) x (Y x)) := Y.contMDiff
  exact BochnerInternal.contMDiff_g_inner (I := I) (M := M) g hX hY


omit [NeZero (Module.finrank ℝ E)] in
theorem normGradSqFun_contMDiff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (normGradSqFun (I := I) g f) := by
  let fs : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
  have h :=
    contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (gradG (I := I) g fs) (gradG (I := I) g fs)
  refine h.congr ?_
  intro b
  change g.inner b (gradFun (I := I) g f b) (gradFun (I := I) g f b) =
    normGradSqFun (I := I) g f b
  rfl

end CalabiYau.Riemannian
