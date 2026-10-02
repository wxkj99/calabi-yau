module
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.LocalChart
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.CompactCoefficient
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.Integral.OverlapCoefficient
public import CalabiYau.Geometry.Manifold.DifferentialForm.Stokes.ChartTransition.OrientedJacobian

/-!
# Equality of actual signed integrals on a restricted chart overlap

Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 16.4,
pp. 404–405. The integral takes the actual bundled top form's coefficient;
it is chart-local, not a global functional. The closed support lies in both
restricted domains, and compatibility holds on every overlap component.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology Manifold ContDiff

noncomputable section

namespace CalabiYau.DifferentialForm

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Fin d → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

def signedChartIntegral (C : OrientedLocalChart d M)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) : ℝ :=
  (C.sign : ℝ) * ∫ y : Fin d → ℝ, chartTopCoefficient C.center η y ∂volume

theorem signedChartIntegral_smul (C : OrientedLocalChart d M) (c : ℝ)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d) :
    signedChartIntegral C (c • η) = c * signedChartIntegral C η := by
  have hcoeff : chartTopCoefficient C.center (c • η) =
      fun y => c * chartTopCoefficient C.center η y := by
    funext y
    exact chartTopCoefficient_smul C.center c η y
  unfold signedChartIntegral
  rw [hcoeff, integral_const_mul]
  ring

variable  [CompactSpace M]

theorem signedChartIntegral_add (C : OrientedLocalChart d M)
    (η ζ : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hη : closure {p : M | η p ≠ 0} ⊆ C.domain)
    (hζ : closure {p : M | ζ p ≠ 0} ⊆ C.domain) :
    signedChartIntegral C (η + ζ) =
      signedChartIntegral C η + signedChartIntegral C ζ := by
  have hiη : Integrable (chartTopCoefficient C.center η)
      (volume : Measure (Fin d → ℝ)) := by
    apply integrable_chartTopCoefficient C.center η
    simpa [extChartAt_source] using hη.trans C.domain_subset
  have hiζ : Integrable (chartTopCoefficient C.center ζ)
      (volume : Measure (Fin d → ℝ)) := by
    apply integrable_chartTopCoefficient C.center ζ
    simpa [extChartAt_source] using hζ.trans C.domain_subset
  have hcoeff : chartTopCoefficient C.center (η + ζ) =
      fun y => chartTopCoefficient C.center η y + chartTopCoefficient C.center ζ y := by
    funext y
    exact chartTopCoefficient_add C.center η ζ y
  unfold signedChartIntegral
  rw [hcoeff, integral_add hiη hiζ, mul_add]

theorem signedChartIntegral_finsetSum {ι : Type*}
    (C : OrientedLocalChart d M) (s : Finset ι)
    (β : ι → DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hβ : ∀ i ∈ s, closure {p : M | β i p ≠ 0} ⊆ C.domain) :
    signedChartIntegral C (∑ i ∈ s, β i) =
      ∑ i ∈ s, signedChartIntegral C (β i) := by
  classical
  have hint : ∀ i ∈ s, Integrable (chartTopCoefficient C.center (β i))
      (volume : Measure (Fin d → ℝ)) := by
    intro i hi
    apply integrable_chartTopCoefficient C.center (β i)
    simpa [extChartAt_source] using (hβ i hi).trans C.domain_subset
  have hcoeff : chartTopCoefficient C.center (∑ i ∈ s, β i) =
      fun y => ∑ i ∈ s, chartTopCoefficient C.center (β i) y := by
    funext y
    let ev : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d →ₗ[ℝ] ℝ :=
      { toFun := fun η => chartTopCoefficient C.center η y
        map_add' := fun η ζ => chartTopCoefficient_add C.center η ζ y
        map_smul' := fun c η => chartTopCoefficient_smul C.center c η y }
    change ev (∑ i ∈ s, β i) = ∑ i ∈ s, ev (β i)
    rw [map_sum]
  unfold signedChartIntegral
  rw [hcoeff, integral_finsetSum s hint, Finset.mul_sum]

theorem signedChartIntegral_eq_of_compatible
    (C D : OrientedLocalChart d M) (hCD : C.Compatible D)
    (η : DifferentialForm 𝓘(ℝ, Fin d → ℝ) M d)
    (hη : closure {p : M | η p ≠ 0} ⊆ C.domain ∩ D.domain) :
    signedChartIntegral C η = signedChartIntegral D η := by
  let U : Set M := C.domain ∩ D.domain
  let s : Set (Fin d → ℝ) := C.chart '' U
  let f : (Fin d → ℝ) → (Fin d → ℝ) := D.chart ∘ C.chart.symm
  let ε : ℝ := (C.sign : ℝ) * (D.sign : ℝ)
  have hU : IsOpen U := C.isOpen_domain.inter D.isOpen_domain
  have hUsource : U ⊆ C.chart.source := by
    exact fun p hp => C.domain_subset hp.1
  have hs : IsOpen s := by
    dsimp [s, U]
    rw [(C.chart).isOpen_image_iff_of_subset_source hUsource]
    exact hU
  have hmeas : MeasurableSet s := hs.measurableSet
  have hInj : InjOn f s := by
    intro x hx y hy hxy
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨q, hq, rfl⟩ := hy
    have hpD : p ∈ D.chart.source := D.domain_subset hp.2
    have hqD : q ∈ D.chart.source := D.domain_subset hq.2
    have hxy' : D.chart p = D.chart q := by
      change D.chart (C.chart.symm (C.chart p)) =
        D.chart (C.chart.symm (C.chart q)) at hxy
      rwa [C.chart.left_inv (C.domain_subset hp.1),
        C.chart.left_inv (C.domain_subset hq.1)] at hxy
    exact congrArg C.chart (D.chart.injOn hpD hqD hxy')
  have himage : f '' s = D.chart '' U := by
    ext z
    constructor
    · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
      refine ⟨p, hp, ?_⟩
      change D.chart p = D.chart (C.chart.symm (C.chart p))
      exact congrArg D.chart (C.chart.left_inv (C.domain_subset hp.1)).symm
    · rintro ⟨p, hp, rfl⟩
      refine ⟨C.chart p, ⟨p, hp, rfl⟩, ?_⟩
      change D.chart (C.chart.symm (C.chart p)) = D.chart p
      exact congrArg D.chart (C.chart.left_inv (C.domain_subset hp.1))
  let gC := chartTopCoefficient C.center η
  let gD := chartTopCoefficient D.center η
  have hzeroC : ∀ x ∉ s, gC x = 0 := by
    intro x hx
    by_cases hxt : x ∈ C.chart.target
    · have hpη : η (C.chart.symm x) = 0 := by
        by_contra hpη
        apply hx
        have hclose := hη (subset_closure hpη)
        refine ⟨C.chart.symm x, hclose, ?_⟩
        exact C.chart.right_inv hxt
      unfold gC chartTopCoefficient
      have hext : x ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).target := by
        simpa [extChartAt_target, OrientedLocalChart.chart] using hxt
      rw [if_pos hext]
      have hsimp : (extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).symm x = C.chart.symm x := by
        rfl
      rw [hsimp, hpη]
      rw [CalabiYau.continuousAlternatingMap_trivializationAt_apply]
      simp
    · unfold gC chartTopCoefficient
      have hext : x ∉ (extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).target := by
        simpa [OrientedLocalChart.chart] using hxt
      rw [if_neg hext]
  have hzeroD : ∀ x ∉ D.chart '' U, gD x = 0 := by
    intro x hx
    by_cases hxt : x ∈ D.chart.target
    · have hpη : η (D.chart.symm x) = 0 := by
        by_contra hpη
        apply hx
        have hclose := hη (subset_closure hpη)
        refine ⟨D.chart.symm x, hclose, ?_⟩
        exact D.chart.right_inv hxt
      unfold gD chartTopCoefficient
      have hext : x ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) D.center).target := by
        simpa [extChartAt_target, OrientedLocalChart.chart] using hxt
      rw [if_pos hext]
      have hsimp : (extChartAt 𝓘(ℝ, Fin d → ℝ) D.center).symm x = D.chart.symm x := by
        rfl
      rw [hsimp, hpη]
      rw [CalabiYau.continuousAlternatingMap_trivializationAt_apply]
      simp
    · unfold gD chartTopCoefficient
      have hext : x ∉ (extChartAt 𝓘(ℝ, Fin d → ℝ) D.center).target := by
        simpa [OrientedLocalChart.chart] using hxt
      rw [if_neg hext]
  have hcoef : ∀ x ∈ s,
      gC x = (fderiv ℝ f x).det * gD (f x) := by
    rintro x ⟨p, hp, rfl⟩
    have hpC : p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).source := by
      simpa [extChartAt_source] using C.domain_subset hp.1
    have hpD : p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) D.center).source := by
      simpa [extChartAt_source] using D.domain_subset hp.2
    have hxC : C.chart p ∈ (extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).target := by
      simpa [OrientedLocalChart.chart, extChartAt_target] using
        C.chart.map_source (C.domain_subset hp.1)
    have hpEq : (extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).symm (C.chart p) = p := by
      simpa [OrientedLocalChart.chart, extChartAt_coe_symm, extChartAt_coe] using
        C.chart.left_inv (C.domain_subset hp.1)
    have hb : (extChartAt 𝓘(ℝ, Fin d → ℝ) C.center).symm (C.chart p) ∈
        (extChartAt 𝓘(ℝ, Fin d → ℝ) D.center).source := by
      rw [hpEq]
      exact hpD
    have ht := chartTopCoefficient_transition_fderiv η C.center D.center
      (C.chart p) hxC hb
    simpa [gC, gD, f, OrientedLocalChart.chart, extChartAt_coe,
      Function.comp_def] using ht
  have hf' : ∀ x ∈ s, HasFDerivAt f (fderiv ℝ f x) x := by
    rintro x ⟨p, hp, rfl⟩
    have hchartD : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
        ∞ D.chart p := by
      simpa [OrientedLocalChart.chart] using
        (contMDiffOn_chart (I := 𝓘(ℝ, Fin d → ℝ)) (x := D.center)).contMDiffAt
          (D.chart.open_source.mem_nhds (D.domain_subset hp.2))
    have hchartCsymm : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
        ∞ C.chart.symm (C.chart p) := by
      simpa [OrientedLocalChart.chart] using
        (contMDiffOn_chart_symm (I := 𝓘(ℝ, Fin d → ℝ)) (x := C.center)).contMDiffAt
          (C.chart.open_target.mem_nhds (C.chart.map_source (C.domain_subset hp.1)))
    have hpEq : C.chart.symm (C.chart p) = p :=
      C.chart.left_inv (C.domain_subset hp.1)
    have hchartD' : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
        ∞ D.chart (C.chart.symm (C.chart p)) := by
      rw [hpEq]
      exact hchartD
    have hcomp : ContMDiffAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ)
        ∞ f (C.chart p) := by
      simpa [f] using hchartD'.comp (C.chart p) hchartCsymm
    exact ((hcomp.mdifferentiableAt (by simp)).differentiableAt).hasFDerivAt
  have hIntC : Integrable gC (volume : Measure (Fin d → ℝ)) := by
    apply integrable_chartTopCoefficient C.center η
    simpa [extChartAt_source] using
      (hη.trans Set.inter_subset_left).trans C.domain_subset
  have hIC : (∫ x, gC x ∂(volume : Measure (Fin d → ℝ))) =
      ∫ x in s, gC x ∂(volume : Measure (Fin d → ℝ)) := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hzeroC).symm
  have hID : (∫ x, gD x ∂(volume : Measure (Fin d → ℝ))) =
      ∫ x in f '' s, gD x ∂(volume : Measure (Fin d → ℝ)) := by
    calc
      _ = ∫ x in D.chart '' U, gD x ∂(volume : Measure (Fin d → ℝ)) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzeroD).symm
      _ = ∫ x in f '' s, gD x ∂(volume : Measure (Fin d → ℝ)) := by rw [himage]
  have hε : ε = 1 ∨ ε = -1 := by
    rcases C.sign.property with hc | hc <;>
      rcases D.sign.property with hd | hd <;> simp [ε, hc, hd]
  have hpos : ∀ x ∈ s, 0 < ε * (fderiv ℝ f x).det := by
    intro x hx
    simpa [ε, f] using hCD x hx
  have hcv := MeasureTheory.integral_image_eq_integral_signed_det_fderiv
    s hmeas f hf' hInj ε hε hpos gD
  have hmul : (∫ y in f '' s, ε * gD y ∂(volume : Measure (Fin d → ℝ))) =
      ε * ∫ y in f '' s, gD y ∂(volume : Measure (Fin d → ℝ)) := by
    simpa only [smul_eq_mul] using
      (integral_smul (μ := (volume : Measure (Fin d → ℝ)).restrict (f '' s)) ε gD)
  have hcoefInt : (∫ x in s, gC x ∂(volume : Measure (Fin d → ℝ))) =
      ∫ x in s, (fderiv ℝ f x).det * gD (f x)
        ∂(volume : Measure (Fin d → ℝ)) := by
    apply setIntegral_congr_fun hmeas
    intro x hx
    exact hcoef x hx
  have hsignε : (C.sign : ℝ) * ε = (D.sign : ℝ) := by
    dsimp [ε]
    calc
      (C.sign : ℝ) * ((C.sign : ℝ) * (D.sign : ℝ)) =
          ((C.sign : ℝ) * (C.sign : ℝ)) * (D.sign : ℝ) := by ring
      _ = (D.sign : ℝ) := by rw [C.sign_mul_self, one_mul]
  unfold signedChartIntegral
  rw [hIC, hID]
  calc
    (C.sign : ℝ) * ∫ x in s, gC x ∂(volume : Measure (Fin d → ℝ)) =
        (C.sign : ℝ) * ∫ x in s, (fderiv ℝ f x).det * gD (f x)
          ∂(volume : Measure (Fin d → ℝ)) := by rw [hcoefInt]
    _ = (C.sign : ℝ) * (ε * ∫ y in f '' s, gD y
          ∂(volume : Measure (Fin d → ℝ))) := by rw [← hcv, hmul]
    _ = (D.sign : ℝ) * ∫ y in f '' s, gD y ∂(volume : Measure (Fin d → ℝ)) := by
      rw [← mul_assoc, hsignε]

end CalabiYau.DifferentialForm
