module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.OverlapCoefficient
public import Mathlib.Data.Sign.Basic

/-!
# Restricted oriented local charts

Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 16.4,
pp. 404–405, using the coordinate pullback of Proposition 14.20 and
Corollary 14.21. Compatibility is required at every point of every component
of the restricted overlap. A refinement need not contain its chart center.
-/

@[expose] public section

open Set
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

structure OrientedLocalChart (d : ℕ) (M : Type*)
    [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M] where
  center : M
  domain : Set M
  sign : {σ : ℝ // σ = 1 ∨ σ = -1}
  isOpen_domain : IsOpen domain
  domain_subset : domain ⊆ (chartAt (Fin d → ℝ) center).source

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℝ) M]

def OrientedLocalChart.chart (C : OrientedLocalChart d M) :
    OpenPartialHomeomorph M (Fin d → ℝ) :=
  chartAt (Fin d → ℝ) C.center

theorem OrientedLocalChart.sign_mul_self (C : OrientedLocalChart d M) :
    (C.sign : ℝ) * (C.sign : ℝ) = 1 := by
  rcases C.sign.property with h | h <;> simp [h]

variable [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

def OrientedLocalChart.IsPositiveFor (C : OrientedLocalChart d M)
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) : Prop :=
  ∀ p ∈ C.domain,
    0 < (C.sign : ℝ) * chartTopCoefficient C.center ν (C.chart p)

def OrientedLocalChart.Compatible (C D : OrientedLocalChart d M) : Prop :=
  ∀ y ∈ C.chart '' (C.domain ∩ D.domain),
    0 < (C.sign : ℝ) * (D.sign : ℝ) *
      (fderiv ℝ (D.chart ∘ C.chart.symm) y).det

theorem OrientedLocalChart.compatible_of_isPositiveFor
    (C D : OrientedLocalChart d M)
    (ν : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hC : C.IsPositiveFor ν) (hD : D.IsPositiveFor ν) :
    C.Compatible D := by
  rintro y ⟨p, hp, rfl⟩
  have hpC : p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).source := by
    simpa [extChartAt_source] using C.domain_subset hp.1
  have hpD : p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) D.center).source := by
    simpa [extChartAt_source] using D.domain_subset hp.2
  have hb : (extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).symm
      ((extChartAt 𝓘(ℝ, Fin d → ℝ) C.center) p) ∈
      (extChartAt 𝓘(ℝ, Fin d → ℝ) D.center).source := by
    rw [(extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).left_inv hpC]
    exact hpD
  have ht := chartTopCoefficient_transition_fderiv ν C.center D.center
    ((extChartAt 𝓘(ℝ, Fin d → ℝ) C.center) p)
    ((extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).map_source hpC) hb
  rw [(extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).left_inv hpC] at ht
  have ht' : chartTopCoefficient C.center ν (C.chart p) =
      (fderiv ℝ (D.chart ∘ C.chart.symm) (C.chart p)).det *
        chartTopCoefficient D.center ν (D.chart p) := by
    simpa [OrientedLocalChart.chart, extChartAt_coe, extChartAt_coe_symm,
      Function.comp_def] using ht
  have heq : (C.sign : ℝ) * chartTopCoefficient C.center ν (C.chart p) =
      ((C.sign : ℝ) * (D.sign : ℝ) *
        (fderiv ℝ (D.chart ∘ C.chart.symm) (C.chart p)).det) *
      ((D.sign : ℝ) * chartTopCoefficient D.center ν (D.chart p)) := by
    rw [ht']
    calc
      (C.sign : ℝ) *
          ((fderiv ℝ (D.chart ∘ C.chart.symm) (C.chart p)).det *
            chartTopCoefficient D.center ν (D.chart p)) =
          ((C.sign : ℝ) *
            ((fderiv ℝ (D.chart ∘ C.chart.symm) (C.chart p)).det *
              chartTopCoefficient D.center ν (D.chart p))) *
          ((D.sign : ℝ) * (D.sign : ℝ)) := by
        rw [D.sign_mul_self]
        ring
      _ = _ := by ring
  exact (mul_pos_iff_of_pos_right (hD p hp.2)).mp
    (by rw [← heq]; exact hC p hp.1)

end CalabiYau.DifferentialForm

section ConcreteChecks

open CalabiYau.DifferentialForm

-- Dimension zero is a genuine singleton coordinate space, with determinant one.
example (C D : OrientedLocalChart 0 (Fin 0 → ℝ))
    (hsign : (C.sign : ℝ) = (D.sign : ℝ)) : C.Compatible D := by
  intro y _hy
  have hdet : (fderiv ℝ (D.chart ∘ C.chart.symm) y).det = 1 := by
    simp [OrientedLocalChart.chart, chartAt_self_eq]
    exact LinearMap.det_id
  rw [hdet, ← hsign, C.sign_mul_self]
  norm_num

-- A real-line reflection has determinant minus one and reverses the chart sign.
example {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin 1 → ℝ) M]
    (C D : OrientedLocalChart 1 M)
    (hC : (C.sign : ℝ) = 1) (hD : (D.sign : ℝ) = -1)
    (hdet : ∀ y ∈ C.chart '' (C.domain ∩ D.domain),
      (fderiv ℝ (D.chart ∘ C.chart.symm) y).det = -1) :
    C.Compatible D := by
  intro y hy
  rw [hC, hD, hdet y hy]
  norm_num

-- Opposite determinant signs at two overlap points cannot share fixed chart signs.
example {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℝ) M] (C D : OrientedLocalChart d M)
    (u v : Fin d → ℝ)
    (hu : u ∈ C.chart '' (C.domain ∩ D.domain))
    (hv : v ∈ C.chart '' (C.domain ∩ D.domain))
    (hdu : (fderiv ℝ (D.chart ∘ C.chart.symm) u).det = 1)
    (hdv : (fderiv ℝ (D.chart ∘ C.chart.symm) v).det = -1) :
    ¬ C.Compatible D := by
  intro h
  have hp := h u hu
  have hm := h v hv
  rw [hdu] at hp
  rw [hdv] at hm
  nlinarith

end ConcreteChecks
