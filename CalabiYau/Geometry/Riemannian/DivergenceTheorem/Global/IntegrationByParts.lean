-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Integration/DivergenceTheorem/Global/IntegrationByParts.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Local.Formula
public import CalabiYau.Geometry.Riemannian.Operator.DirectionalDerivative
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.PartitionOfUnity
public import CalabiYau.Geometry.Riemannian.DivergenceTheorem.Global.Support
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Topology.Algebra.Support

@[expose] public section


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace CalabiYau.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

lemma Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact hf.integrable_of_hasCompactSupport hcs

theorem integral_tangentSectionAction_eq_neg_integral_smul_divergence
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : HasCompactSupport X) :
    ∫ x, tangentSectionAction (I := I) X f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      -∫ x, f x * divergenceG (I := I) g X x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := smoothSmul (I := I) f hf X with hY_def
  have hY_support : Function.support (Y : ∀ x, TangentSpace I x) ⊆
      Function.support (X : ∀ x, TangentSpace I x) := by
    intro x hx
    by_contra hneX
    have hXx : X x = 0 := Function.notMem_support.mp hneX
    have hYx : (Y : ∀ x, TangentSpace I x) x = (0 : TangentSpace I x) := by
      change f x • X x = (0 : TangentSpace I x)
      rw [hXx]
      exact smul_zero _
    exact hx hYx
  have hY_cs : HasCompactSupport Y := by
    refine HasCompactSupport.of_support_subset_isCompact (hX : IsCompact (tsupport X)) ?_
    exact hY_support.trans (subset_tsupport _)
  have hY_div : ∀ x : M,
      divergenceG (I := I) g Y x =
        f x * divergenceG (I := I) g X x + tangentSectionAction (I := I) X f x :=
    divergence_g_smoothSmul (I := I) g f hf X
  have hf_cont : Continuous f := hf.continuous
  have hX_div_cont : Continuous (divergenceG (I := I) g X) :=
    (divergence_g_contMDiff (I := I) g X).continuous
  have hAct_cont : Continuous (tangentSectionAction (I := I) X f) :=
    (tangentSectionAction_contMDiff (I := I) X hf).continuous
  have hX_div_cs : HasCompactSupport (divergenceG (I := I) g X) :=
    hasCompactSupport_divergence_g (I := I) g hX
  have hAct_cs : HasCompactSupport (tangentSectionAction (I := I) X f) :=
    hasCompactSupport_tangentSectionAction (I := I) hX f
  have hMul_cont : Continuous (fun x : M => f x * divergenceG (I := I) g X x) :=
    hf_cont.mul hX_div_cont
  have hMul_cs : HasCompactSupport (fun x : M => f x * divergenceG (I := I) g X x) :=
    hX_div_cs.mul_left
  have h_div_Y_zero :
      ∫ x, divergenceG (I := I) g Y x ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Y hY_cs
  have h_eq_pointwise : ∀ x : M, divergenceG (I := I) g Y x =
      f x * divergenceG (I := I) g X x + tangentSectionAction (I := I) X f x :=
    hY_div
  have h_div_Y_split :
      ∫ x, divergenceG (I := I) g Y x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, (f x * divergenceG (I := I) g X x +
                tangentSectionAction (I := I) X f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_eq_pointwise x
  have h_int_mul : Integrable (fun x : M => f x * divergenceG (I := I) g X x)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hMul_cont hMul_cs
  have h_int_act : Integrable (tangentSectionAction (I := I) X f)
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hAct_cont hAct_cs
  have h_int_split :
      ∫ x, (f x * divergenceG (I := I) g X x +
              tangentSectionAction (I := I) X f x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∫ x, f x * divergenceG (I := I) g X x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
          ∫ x, tangentSectionAction (I := I) X f x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    integral_add h_int_mul h_int_act
  have h_sum_zero :
      ∫ x, f x * divergenceG (I := I) g X x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
        ∫ x, tangentSectionAction (I := I) X f x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    rw [← h_int_split, ← h_div_Y_split]; exact h_div_Y_zero
  linarith [h_sum_zero]

end CalabiYau.DivergenceTheorem
