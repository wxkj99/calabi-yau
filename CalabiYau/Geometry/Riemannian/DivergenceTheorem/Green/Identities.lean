-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/DivergenceTheorem/Green/Identities.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.Formula
public import CalabiYau.Geometry.Riemannian.Operator.Gradient.Basic
public import CalabiYau.Geometry.Riemannian.Operator.Laplacian.Basic
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.IntegrationByParts
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.CompactSupport
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.Support
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Green.GradientFormula

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

open CalabiYau.Riemannian
namespace CalabiYau.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
private theorem contMDiff_exp_neg {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => Real.exp (-f x)) := by
  have h := Real.contDiff_exp.contMDiff.comp hf.neg
  convert h using 1
  · with_reducible_and_instances rfl
  · rfl

theorem green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f h : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h)
    (hh_support : HasCompactSupport h) :
    ∫ x, g.inner x ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨_, hh⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * ΔG (I := I) g ⟨_, hh⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG (I := I) g ⟨_, hh⟩ with hX_def
  have hX_cs : HasCompactSupport X := hasCompactSupport_grad_g (I := I) g ⟨_, hh⟩ hh_support
  have h_ibp := integral_tangentSectionAction_eq_neg_integral_smul_divergence
    (I := I) g hf X hX_cs
  have hLHS_eq : ∀ x : M,
      tangentSectionAction (I := I) X f x =
        g.inner x ((gradG (I := I) g ⟨_, hf⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((gradG (I := I) g ⟨_, hh⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro x
    let fb : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
    change tangentSectionAction (I := I) X (⇑fb) x =
      g.inner x ((gradG (I := I) g fb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g ⟨_, hh⟩ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
    rw [tangentSectionAction_eq_inner_grad_g (I := I) g fb X x]
    change g.inner x (X x) ((gradG (I := I) g fb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) =
      g.inner x ((gradG (I := I) g fb : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) (X x)
    exact g.symm x _ _
  have hRHS_eq : ∀ x : M,
      f x * divergenceG (I := I) g X x = f x * ΔG (I := I) g ⟨_, hh⟩ x := by
    intro x
    rfl
  have hLHS_int : ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, g.inner x ((gradG (I := I) g ⟨_, hf⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g ⟨_, hh⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hLHS_eq)
  have hRHS_int : ∫ x, f x * divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ x, f x * ΔG (I := I) g ⟨_, hh⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_congr_ae (Filter.Eventually.of_forall hRHS_eq)
  rw [← hLHS_int, h_ibp, hRHS_int]

end CalabiYau.DivergenceTheorem
