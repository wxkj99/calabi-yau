module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Analysis.Elliptic.Schauder
import CalabiYau.Geometry.Complex.Forms.Positive
import CalabiYau.Mathlib.Analysis.Matrix.Order
import CalabiYau.Mathlib.Analysis.Matrix.PosDef.EigenvalueBounds

/-!
# Uniform ellipticity of the inverse perturbed metric

A trace upper bound on the reference metric and the relative trace bound on a Monge–Ampère
solution give a uniform upper bound for the perturbed metric. Matrix order reversal then gives the
uniform ellipticity lower bound for its inverse, on any chart domain whose compact closure stays
inside the chart.

Source: Yau, “On the Ricci curvature of a compact Kähler manifold and the complex
Monge–Ampère equation”, §4; Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
proof of Proposition 3.11, p. 47.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder MatrixOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The relative trace bound and a uniform reference-metric trace bound yield uniform ellipticity
of the inverse perturbed metric on the chart domain. -/
theorem exists_uniform_inverse_metric_ellipticity
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    {x : M} {Λ Cref : ℝ} (hΛpos : 0 < Λ) (hCref : 0 < Cref)
    (hΛ : ∀ p ∈ S, ∀ y, relTrace (ω₀ y) (ω₀ y + mddbar n p.2 y) ≤ Λ)
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hUtarget : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hTraceBound : ∀ z ∈ closure U,
      RCLike.re ((ω₀.metricInChart x z).trace) ≤ Cref) :
    ∃ lam : ℝ≥0, 0 < lam ∧ ∀ p ∈ S, IsUniformlyEllipticOn
      (fun z ↦ (ω₀.metricInChart x z +
        complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹)
      lam U := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hUniformFormUpper : ∀ p ∈ S, ∀ z ∈ closure U,
      (Λ • ω₀ (e.symm z) -
        (ω₀ (e.symm z) + mddbar n p.2 (e.symm z))).IsNonneg := by
    intro p hp z hz
    let y := e.symm z
    let α := ω₀ y + mddbar n p.2 y
    have hαpos : α.IsPositive := by
      simpa [α] using ((hS p hp).2.1.2 y)
    have hTrace : relTrace (ω₀ y) α ≤ Λ := by
      simpa [α] using hΛ p hp y
    have hFirst : (relTrace (ω₀ y) α • ω₀ y - α).IsNonneg :=
      ContinuousAlternatingMap.isNonneg_relTrace_smul_sub
        (ω₀.isPositive y) hαpos.isNonneg
    have hωnonneg : (ω₀ y).IsNonneg := (ω₀.isPositive y).isNonneg
    have hSecond : ((Λ - relTrace (ω₀ y) α) • ω₀ y).IsNonneg := by
      refine ⟨hωnonneg.1.smul _, ?_⟩
      intro v
      simpa using mul_nonneg (sub_nonneg.mpr hTrace) (hωnonneg.2 v)
    have hdecomp : Λ • ω₀ y - α =
        (relTrace (ω₀ y) α • ω₀ y - α) +
          (Λ - relTrace (ω₀ y) α) • ω₀ y := by
      module
    rw [hdecomp]
    refine ⟨hFirst.1.add hSecond.1, ?_⟩
    intro v
    exact add_nonneg (hFirst.2 v) (hSecond.2 v)
  let c : ℝ := Λ * Cref
  have hc : 0 < c := mul_pos hΛpos hCref
  let lam : ℝ≥0 := ⟨c⁻¹, inv_nonneg.mpr hc.le⟩
  have hlam : 0 < lam := NNReal.coe_pos.mp (inv_pos.mpr hc)
  have hUniformElliptic : ∀ p ∈ S, IsUniformlyEllipticOn
      (fun z ↦ (ω₀.metricInChart x z +
        complexHessian (p.2 ∘ e.symm) z)⁻¹) lam U := by
    intro p hp
    let hPot : ω₀.IsPotential p.2 := (hS p hp).2.1
    let ωφ := ω₀.perturb p.2 hPot
    intro z hz
    have hz' : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
      hUtarget (subset_closure hz)
    let y := e.symm z
    let g₀ : Matrix (Fin n) (Fin n) ℂ := ω₀.metricInChart x z
    let gφ : Matrix (Fin n) (Fin n) ℂ :=
      ω₀.metricInChart x z + complexHessian (p.2 ∘ e.symm) z
    have hg₀pos : g₀.PosDef := ω₀.posDef_metricInChart x hz'
    have hgφpos : gφ.PosDef := by
      have hPos : (ωφ.metricInChart x z).PosDef := ωφ.posDef_metricInChart x hz'
      rw [KahlerForm.metricInChart_perturb hPot x hz'] at hPos
      simpa [gφ, e] using hPos
    have hFormUpper := hUniformFormUpper p hp z (subset_closure hz)
    let β : FormField (EuclideanSpace ℂ (Fin n)) M 2 :=
      fun y ↦ Λ • ω₀ y - ωφ y
    have hβ : (β y).IsNonneg := by
      simpa [β, ωφ, KahlerForm.perturb] using hFormUpper
    let IC := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
    let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
      tangentCoordChange IC x y y
    have hyx : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source :=
      e.map_target hz'
    have hyy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
      mem_extChartAt_source y
    have hxy : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∩
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := ⟨hyx, hyy⟩
    have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
        A.restrictScalars ℝ := tangentCoordChange_real_eq hxy
    have hrep (γ : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
        γ.chartRep x z = (γ y).compContinuousLinearMap (A.restrictScalars ℝ) := by
      change (γ y).compContinuousLinearMap
        (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
      rw [hAreal]
    have hβcomp : (β y).compContinuousLinearMap (A.restrictScalars ℝ) |>.IsNonneg := by
      refine ⟨hβ.1.compContinuousLinearMap A, ?_⟩
      intro v
      have hcomp :
          (A.restrictScalars ℝ) ∘ ![v, Complex.I • v] = ![A v, Complex.I • A v] := by
        funext i
        fin_cases i <;> simp [map_smul]
      simpa only [ContinuousAlternatingMap.compContinuousLinearMap_apply, hcomp] using
        hβ.2 (A v)
    have hβchart : (β.chartRep x z).IsNonneg := by
      rw [hrep]
      exact hβcomp
    have hg₀ : (ω₀.toFormField.chartRep x z).coeffMatrix = g₀ := rfl
    have hgφ : (ωφ.toFormField.chartRep x z).coeffMatrix = gφ := by
      change ωφ.metricInChart x z = gφ
      rw [KahlerForm.metricInChart_perturb hPot x hz']
    have hβchartEqFun : β.chartRep x =
        Λ • (ω₀.toFormField.chartRep x) - ωφ.toFormField.chartRep x := by
      have hfield : β = Λ • ω₀.toFormField + (-1 : ℝ) • ωφ.toFormField := by
        funext y'
        simp [β, sub_eq_add_neg]
      rw [hfield, FormField.chartRep_add]
      simp only [FormField.chartRep_smul]
      simp [sub_eq_add_neg]
    have hβchartEq : β.chartRep x z =
        Λ • (ω₀.toFormField.chartRep x z) - ωφ.toFormField.chartRep x z :=
      congrFun hβchartEqFun z
    have hMatrixPSD : (Λ • g₀ - gφ).PosSemidef := by
      have h := (ContinuousAlternatingMap.isNonneg_iff.mp hβchart).2
      rw [hβchartEq, ContinuousAlternatingMap.coeffMatrix_sub,
        ContinuousAlternatingMap.coeffMatrix_smul, hg₀, hgφ] at h
      exact h
    have hMatrixUpper : gφ ≤ Λ • g₀ := Matrix.le_iff.mpr hMatrixPSD
    have hTrace₀ : RCLike.re g₀.trace ≤ Cref := by
      simpa [g₀] using hTraceBound z (subset_closure hz)
    have hTraceMatrix :
        g₀ ≤ RCLike.re g₀.trace • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      simpa [g₀] using
        (Matrix.PosDef.le_trace_inv_mul_smul Matrix.PosDef.one hg₀pos.posSemidef)
    have hIdentityUpper : g₀ ≤ Cref • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [Matrix.le_iff]
      have hTracePSD := Matrix.le_iff.mp hTraceMatrix
      have hScalarPSD :
          ((Cref - RCLike.re g₀.trace) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
        Matrix.PosSemidef.one.smul (sub_nonneg.mpr hTrace₀)
      have hdecomp : Cref • (1 : Matrix (Fin n) (Fin n) ℂ) - g₀ =
          (Cref - RCLike.re g₀.trace) • (1 : Matrix (Fin n) (Fin n) ℂ) +
            (RCLike.re g₀.trace • (1 : Matrix (Fin n) (Fin n) ℂ) - g₀) := by
        module
      rw [hdecomp]
      exact hScalarPSD.add hTracePSD
    have hMetricUpper : gφ ≤ c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      calc
        gφ ≤ Λ • g₀ := hMatrixUpper
        _ ≤ Λ • (Cref • (1 : Matrix (Fin n) (Fin n) ℂ)) :=
          smul_le_smul_of_nonneg_left hIdentityUpper hΛpos.le
        _ = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [c, smul_smul]
    have hInvOrder : (c • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ ≤ gφ⁻¹ :=
      Matrix.PosDef.inv_le_inv hgφpos hMetricUpper
    let : Invertible (c : ℂ) := invertibleOfNonzero (by exact_mod_cast hc.ne')
    have hInvId :
        (c • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ =
          (c⁻¹ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [show c • (1 : Matrix (Fin n) (Fin n) ℂ) =
          (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) by ext i j ; simp]
      apply Matrix.inv_eq_left_inv
      ext i j
      simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply,
        hc.ne']
    have hInvPSD :
        (gφ⁻¹ - (c⁻¹ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
      have h := Matrix.le_iff.mp hInvOrder
      simpa [hInvId] using h
    constructor
    · exact hgφpos.inv.isHermitian
    · intro v
      have hq := hInvPSD.dotProduct_mulVec_nonneg v
      have hqRe := (RCLike.nonneg_iff.mp hq).1
      have hIdentity : RCLike.re
          (dotProduct (star v)
            (Matrix.mulVec ((c⁻¹ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v)) =
            c⁻¹ * ∑ i, ‖v i‖ ^ 2 := by
        simp [Matrix.mulVec, Matrix.one_apply, dotProduct, Complex.normSq_apply,
          ← Complex.normSq_eq_norm_sq]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [hc.ne']
      have hqRe' : c⁻¹ * ∑ i, ‖v i‖ ^ 2 ≤
          RCLike.re (dotProduct (star v) (Matrix.mulVec gφ⁻¹ v)) := by
        rw [← hIdentity]
        have hsub : 0 ≤ RCLike.re (dotProduct (star v)
            (Matrix.mulVec gφ⁻¹ v)) -
            RCLike.re (dotProduct (star v)
              (Matrix.mulVec ((c⁻¹ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) v)) := by
          simpa [Matrix.sub_mulVec, dotProduct_sub] using hqRe
        linarith
      change c⁻¹ * ∑ i, ‖v i‖ ^ 2 ≤
        RCLike.re (dotProduct (star v) (Matrix.mulVec gφ⁻¹ v))
      exact hqRe'
  exact ⟨lam, hlam, hUniformElliptic⟩

end KahlerForm

end
