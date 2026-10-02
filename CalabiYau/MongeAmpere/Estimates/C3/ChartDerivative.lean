module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy
import CalabiYau.Geometry.Complex.Forms.Positive
import CalabiYau.Mathlib.Analysis.Matrix.Order

/-!
# From Calabi energy to chartwise derivatives

A bound for the covariant derivative of the perturbed metric implies a bound for ordinary
coordinate derivatives of `i∂∂̄φ`: write the covariant derivative as the ordinary derivative
minus the fixed background Christoffel term, use two-sided metric comparison, and cover a
compact chart piece by finitely many normal-coordinate neighborhoods. See Aubin,
*Some Nonlinear Problems in Riemannian Geometry*, §7.5, and Székelyhidi, §3.3,
Proposition 3.11, pp. 45–46.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

/-- A global Calabi-energy bound transfers to any chart representation of the energy. -/
private theorem calabiEnergyInChart_le_of_global_bound (ω₀ : KahlerForm n M)
    (φ G : M → ℝ)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (B : ℝ)
    (hEnergy : ∀ x, calabiEnergy ω₀ φ x ≤ B) (x₀ : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    calabiEnergyInChart ω₀ φ x₀ z ≤ B := by
  obtain ⟨_, hchart, _⟩ := calabiEnergy_chartFormula_is_intrinsic ω₀ φ G hφ hsol
  calc
    calabiEnergyInChart ω₀ φ x₀ z =
        calabiEnergy ω₀ φ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z) :=
      (hchart x₀ z hz).symm
    _ ≤ B := hEnergy _

open scoped MatrixOrder ComplexOrder
open ContinuousAlternatingMap

/-- Relative trace bounds the diagonal entries of a positive `(1,1)`-form. -/
private theorem form_diag_le_relTrace {n : ℕ} [NeZero n]
    (eta theta : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (heta : eta.IsPositive) (htheta : theta.IsPositive) (i : Fin n) :
    RCLike.re (theta.coeffMatrix i i) ≤
      relTrace eta theta * RCLike.re (eta.coeffMatrix i i) := by
  have h := isNonneg_relTrace_smul_sub heta htheta.isNonneg
  have hm := (isNonneg_iff.mp h).2
  have hd := hm.diag_nonneg (i := i)
  have hdr := (RCLike.nonneg_iff.mp hd).1
  have hs : 0 ≤ relTrace eta theta * RCLike.re (eta.coeffMatrix i i) -
      RCLike.re (theta.coeffMatrix i i) := by
    simpa [coeffMatrix_sub, coeffMatrix_smul, Matrix.sub_apply, Matrix.smul_apply,
      Complex.real_smul, RCLike.re_ofReal_mul] using hdr
  exact (sub_nonneg.mp hs)

omit [T2Space M] [CompactSpace M] in
private theorem relTrace_chartRep_eq (α β : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (x y : M) (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source)
    (hα : (α y).IsOneOne) (hβ : (β y).IsOneOne) :
    relTrace (α y) (β y) =
      relTrace (α.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
        (β.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) := by
  have hyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source := by
    rw [extChartAt_source]
    exact hy
  have hyyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyR
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    exact (tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
      (w := x) (x := y) (y := x) (z := y) (v := v)
      ⟨⟨hyxC, hyyC⟩, hyxC⟩).trans
      (tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxC)
  have hAB : ∀ v, A (B v) = v := by
    intro v
    exact (tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
      (w := y) (x := x) (y := y) (z := y) (v := v)
      ⟨⟨hyyC, hyxC⟩, hyyC⟩).trans
      (tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyC)
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    toLinearEquiv := {
      toFun := A
      invFun := B
      left_inv := hBA
      right_inv := hAB
      map_add' := A.map_add
      map_smul' := A.map_smul }
    continuous_toFun := A.continuous
    continuous_invFun := B.continuous }
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hyz : c y ∈ c.target := c.map_source hyR
  have hrepα := FormField.chartRep_eq_chartRep_comp (α := α) hyz
    (by rw [c.left_inv hyR]; exact hyyR)
  have hrepβ := FormField.chartRep_eq_chartRep_comp (α := β) hyz
    (by rw [c.left_inv hyR]; exact hyyR)
  have hderiv : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘ c.symm) (c y) =
        A.restrictScalars ℝ := by
    have h := tangentCoordChange_real_eq ⟨hyR, hyyR⟩
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    dsimp [c, A]
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  have hcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
      (c.symm (c y)) = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y := by
    rw [c.left_inv hyR]
  rw [hcenter, FormField.chartRep_self] at hrepα hrepβ
  rw [hderiv] at hrepα hrepβ
  have hAEquiv : (AEquiv : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  have htrace := relTrace_compContinuousLinearMap hα hβ AEquiv
  rw [hrepα, hrepβ]
  simpa only [hAEquiv] using htrace.symm

private theorem isNonneg_smul_sub_of_trace_le {n : ℕ}
    (eta theta : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (heta : eta.IsPositive) (htheta : theta.IsPositive) (D : ℝ)
    (htrace : relTrace theta eta ≤ D) : (D • theta - eta).IsNonneg := by
  have hrel := isNonneg_relTrace_smul_sub htheta heta.isNonneg
  have hscale : ((D - relTrace theta eta) • theta).IsNonneg := by
    refine ⟨htheta.1.smul _, ?_⟩
    intro v
    change 0 ≤ (D - relTrace theta eta) * theta ![v, Complex.I • v]
    exact mul_nonneg (sub_nonneg.mpr htrace) (htheta.isNonneg.2 v)
  refine ⟨(htheta.1.smul D).sub heta.1, ?_⟩
  intro v
  have h1 := hrel.2 v
  have h2 := hscale.2 v
  change 0 ≤ (D • theta - eta) ![v, Complex.I • v]
  calc
    0 ≤ ((relTrace theta eta • theta - eta) +
        ((D - relTrace theta eta) • theta)) ![v, Complex.I • v] := by
      rw [ContinuousAlternatingMap.add_apply]
      exact add_nonneg h1 h2
    _ = (D • theta - eta) ![v, Complex.I • v] := by
      congr 1
      ext u
      simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sub_apply,
        ContinuousAlternatingMap.smul_apply]
      ring

omit [T2Space M] [CompactSpace M] in
private theorem chartRep_isPositive (α : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (x y : M) (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source)
    (hα : (α y).IsPositive) :
    (α.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).IsPositive := by
  have hyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source := by
    rw [extChartAt_source]
    exact hy
  have hyyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyR
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    exact (tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
      (w := x) (x := y) (y := x) (z := y) (v := v)
      ⟨⟨hyxC, hyyC⟩, hyxC⟩).trans
      (tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxC)
  have hAB : ∀ v, A (B v) = v := by
    intro v
    exact (tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
      (w := y) (x := x) (y := y) (z := y) (v := v)
      ⟨⟨hyyC, hyxC⟩, hyyC⟩).trans
      (tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyC)
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    toLinearEquiv := {
      toFun := A
      invFun := B
      left_inv := hBA
      right_inv := hAB
      map_add' := A.map_add
      map_smul' := A.map_smul }
    continuous_toFun := A.continuous
    continuous_invFun := B.continuous }
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hyz : c y ∈ c.target := c.map_source hyR
  have hrep := FormField.chartRep_eq_chartRep_comp (α := α) hyz
    (by rw [c.left_inv hyR]; exact hyyR)
  have hderiv : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘ c.symm) (c y) =
        A.restrictScalars ℝ := by
    have h := tangentCoordChange_real_eq ⟨hyR, hyyR⟩
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    dsimp [c, A]
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  have hcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
      (c.symm (c y)) = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y := by
    rw [c.left_inv hyR]
  rw [hcenter, FormField.chartRep_self] at hrep
  rw [hderiv] at hrep
  have hAEquiv : (AEquiv : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  rw [hrep]
  simpa only [hAEquiv] using hα.compContinuousLinearMap AEquiv

private theorem isNonneg_compContinuousLinearMap_of_commutesWithI
    {n : ℕ} (alpha : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (halpha : alpha.IsNonneg)
    (A : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
    (hA : ∀ v, A (Complex.I • v) = Complex.I • A v) :
    (alpha.compContinuousLinearMap A).IsNonneg := by
  have hmap (u v : EuclideanSpace ℂ (Fin n)) : A ∘ ![u, v] = ![A u, A v] := by
    funext i
    fin_cases i <;> simp
  constructor
  · intro u v
    change alpha (A ∘ ![Complex.I • u, Complex.I • v]) = alpha (A ∘ ![u, v])
    rw [hmap, hmap, hA u, hA v]
    exact halpha.1 (A u) (A v)
  · intro v
    change 0 ≤ alpha (A ∘ ![v, Complex.I • v])
    rw [hmap, hA v]
    exact halpha.2 (A v)

omit [T2Space M] [CompactSpace M] in
private theorem chartRep_isNonneg_at
    (alpha : FormField (EuclideanSpace ℂ (Fin n)) M 2) (x : M)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (halpha : (alpha ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).IsNonneg) :
    (alpha.chartRep x z).IsNonneg := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  let A := tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y
  have hOverlap : y ∈ e.source ∩ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    ⟨e.map_target hz, mem_extChartAt_source y⟩
  have hA := tangentCoordChange_I_smul hOverlap
  change ((alpha y).compContinuousLinearMap A).IsNonneg
  exact isNonneg_compContinuousLinearMap_of_commutesWithI (alpha y) halpha A hA

omit [T2Space M] [CompactSpace M] in
private theorem chartRep_neg (eta : FormField (EuclideanSpace ℂ (Fin n)) M 2) (x : M) :
    (-eta).chartRep x = -eta.chartRep x := by
  ext z v
  simp [FormField.chartRep, ContinuousAlternatingMap.compContinuousLinearMap_apply]

omit [T2Space M] [CompactSpace M] in
private theorem chartRep_order_of_reverse_relTrace
    (eta theta : FormField (EuclideanSpace ℂ (Fin n)) M 2) (x : M)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (heta : (eta ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).IsPositive)
    (htheta : (theta ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)).IsPositive)
    {D : ℝ} (htrace : relTrace
      (theta ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z))
      (eta ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z)) ≤ D) :
    (eta.chartRep x z).coeffMatrix ≤ D • (theta.chartRep x z).coeffMatrix := by
  let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z
  let gamma : FormField (EuclideanSpace ℂ (Fin n)) M 2 := D • theta - eta
  have hgamma : (gamma y).IsNonneg :=
    isNonneg_smul_sub_of_trace_le (eta y) (theta y) heta htheta D htrace
  have hgammaChart : (gamma.chartRep x z).IsNonneg :=
    chartRep_isNonneg_at gamma x hz hgamma
  have hmatrix : (gamma.chartRep x z).coeffMatrix.PosSemidef :=
    (isNonneg_iff.mp hgammaChart).2
  have hcoeff : (gamma.chartRep x z).coeffMatrix =
      D • (theta.chartRep x z).coeffMatrix - (eta.chartRep x z).coeffMatrix := by
    calc
      _ = ((D • theta - eta).chartRep x z).coeffMatrix := rfl
      _ = (D • theta.chartRep x z + -(eta.chartRep x z)).coeffMatrix := by
        rw [sub_eq_add_neg, FormField.chartRep_add, FormField.chartRep_smul, chartRep_neg]
        rfl
      _ = _ := by
        rw [ContinuousAlternatingMap.coeffMatrix_add,
          ContinuousAlternatingMap.coeffMatrix_smul,
          ContinuousAlternatingMap.coeffMatrix_neg]
        simp only [sub_eq_add_neg]
  rw [hcoeff] at hmatrix
  exact Matrix.le_iff.mpr (by simpa using hmatrix)

private theorem posDef_diag_norm_eq_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosDef) (i : ι) :
    ‖A i i‖ = RCLike.re (A i i) := by
  have hstar : star (A i i) = A i i := hA.isHermitian.apply i i
  have him : (A i i).im = 0 := Complex.conj_eq_iff_im.mp (by simpa using hstar)
  have hre : 0 ≤ RCLike.re (A i i) := (RCLike.pos_iff.mp hA.diag_pos).1.le
  have hre' : 0 ≤ (A i i).re := by exact_mod_cast hre
  rw [show A i i = (RCLike.ofReal (RCLike.re (A i i)) : ℂ) by
    apply Complex.ext <;> simp [him]]
  simp [Real.norm_eq_abs, abs_of_nonneg hre']

private theorem inverse_le_scaled_inverse_of_scaled_lower_bound {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B : Matrix ι ι ℂ) (hA : A.PosDef) (D : ℝ) (hD : 0 < D)
    (hAB : A ≤ D • B) : B⁻¹ ≤ D • A⁻¹ := by
  have hscale : D⁻¹ • A ≤ B := by
    have h := smul_le_smul_of_nonneg_left hAB (inv_nonneg.mpr hD.le)
    calc
      _ ≤ D⁻¹ • (D • B) := h
      _ = B := by rw [smul_smul, inv_mul_cancel₀ hD.ne', one_smul]
  have hscaledPos : (D⁻¹ • A).PosDef := hA.smul (inv_pos.mpr hD)
  have hinv := Matrix.PosDef.inv_le_inv hscaledPos hscale
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hinvScale : (D⁻¹ • A)⁻¹ = D • A⁻¹ := by
    have hconvert : D⁻¹ • A = (D⁻¹ : ℂ) • A := by
      ext i j
      simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    have hscalar : IsUnit (D⁻¹ : ℂ) := isUnit_iff_ne_zero.mpr (by
      exact_mod_cast inv_ne_zero hD.ne')
    let : Invertible (D⁻¹ : ℂ) := hscalar.invertible
    rw [hconvert, Matrix.inv_smul A (D⁻¹ : ℂ) hdet]
    have hscalarEq : ⅟ (D⁻¹ : ℂ) = (D : ℂ) := by
      rw [invOf_eq_inv]
      simp [inv_inv]
    rw [hscalarEq]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) D (A⁻¹)).symm
  rw [hinvScale] at hinv
  exact hinv

open Matrix in
open scoped BigOperators in
private theorem c3_trace_quadratic_eq {m : Type*} [Fintype m] [DecidableEq m]
    (W : Matrix m m ℂ) (v : m → ℂ) :
    star v ⬝ᵥ (W *ᵥ v) = (W * Matrix.vecMulVec v (star v)).trace := by
  simp only [dotProduct, Matrix.trace, Matrix.vecMulVec, Matrix.mulVec,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [Matrix.vecMulVec]
  ring

open Matrix in
open scoped InnerProductSpace in
private theorem c3_component_normSq_le_quadratic_mul_inverse_diag {m : Type*}
    [Fintype m] [DecidableEq m] (W : Matrix m m ℂ) (hW : W.PosDef)
    (v : m → ℂ) (i : m) :
    Complex.normSq (v i) ≤
      RCLike.re (star v ⬝ᵥ (W *ᵥ v)) * RCLike.re (W⁻¹ i i) := by
  let : SeminormedAddCommGroup (m → ℂ) := Matrix.toSeminormedAddCommGroup W hW.posSemidef
  let : InnerProductSpace ℂ (m → ℂ) := Matrix.toInnerProductSpace W hW.posSemidef
  let : PreInnerProductSpace.Core ℂ (m → ℂ) := PreInnerProductSpace.toCore
  let : Norm (m → ℂ) := InnerProductSpace.Core.toNorm (𝕜 := ℂ)
  let N : (m → ℂ) → ℝ := fun x ↦ ‖x‖
  let e : m → ℂ := Pi.single i 1
  let y : m → ℂ := W⁻¹ *ᵥ e
  have hdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).1 hW.isUnit
  have hwy : W *ᵥ y = e := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv W hdet]
    ext j
    by_cases hji : j = i <;> simp [e,  hji]
  have hinner : ⟪v, y⟫_ℂ = star (v i) := by
    change (W *ᵥ y) ⬝ᵥ star v = star (v i)
    rw [hwy]
    simp [e, dotProduct, Pi.single_apply]
  have hvnorm : N v ^ 2 = RCLike.re (star v ⬝ᵥ (W *ᵥ v)) := by
    calc
      N v ^ 2 = RCLike.re ⟪v, v⟫_ℂ := by
        simpa [N] using (inner_self_eq_norm_sq (𝕜 := ℂ) v).symm
      _ = RCLike.re (star v ⬝ᵥ (W *ᵥ v)) := by
        change Complex.re ((W *ᵥ v) ⬝ᵥ star v) = Complex.re (star v ⬝ᵥ (W *ᵥ v))
        rw [dotProduct_comm]
  have hynorm : N y ^ 2 = RCLike.re (W⁻¹ i i) := by
    calc
      N y ^ 2 = RCLike.re ⟪y, y⟫_ℂ := by
        simpa [N] using (inner_self_eq_norm_sq (𝕜 := ℂ) y).symm
      _ = RCLike.re (W⁻¹ i i) := by
        change Complex.re ((W *ᵥ y) ⬝ᵥ star y) = Complex.re (W⁻¹ i i)
        rw [hwy]
        simp [e, y, dotProduct, Pi.single_apply]
  have hCS0 := InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℂ) v y
  have hCS : ‖⟪v, y⟫_ℂ‖ ≤ N v * N y := by simpa [N] using hCS0
  have hNv : 0 ≤ N v := by
    change 0 ≤ Real.sqrt (RCLike.re ⟪v, v⟫_ℂ)
    exact Real.sqrt_nonneg _
  have hNy : 0 ≤ N y := by
    change 0 ≤ Real.sqrt (RCLike.re ⟪y, y⟫_ℂ)
    exact Real.sqrt_nonneg _
  have hCSsq : ‖⟪v, y⟫_ℂ‖ ^ 2 ≤ (N v * N y) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hNv hNy)).2 hCS
  have hleft : Complex.normSq (v i) = ‖⟪v, y⟫_ℂ‖ ^ 2 := by
    calc
      Complex.normSq (v i) = ‖v i‖ ^ 2 := Complex.normSq_eq_norm_sq _
      _ = ‖star (v i)‖ ^ 2 := by rw [norm_star]
      _ = ‖⟪v, y⟫_ℂ‖ ^ 2 := by rw [hinner]
  calc
    Complex.normSq (v i) = ‖⟪v, y⟫_ℂ‖ ^ 2 := hleft
    _ ≤ (N v * N y) ^ 2 := hCSsq
    _ = (N v) ^ 2 * (N y) ^ 2 := by ring
    _ = RCLike.re (star v ⬝ᵥ (W *ᵥ v)) * RCLike.re (W⁻¹ i i) := by
      rw [hvnorm, hynorm]

open Matrix in
open scoped BigOperators Kronecker in
private theorem c3_tensor_trace_eq_energy {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) :
    RCLike.re ((Matrix.kronecker gᵀ (Matrix.kronecker g⁻¹ g⁻¹) *
      Matrix.vecMulVec (fun p : Fin n × (Fin n × Fin n) ↦ T p.1 p.2.1 p.2.2)
        (star (fun p : Fin n × (Fin n × Fin n) ↦ T p.1 p.2.1 p.2.2))).trace) =
      RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
          g i a * g⁻¹ b j * g⁻¹ c k * T i j k * star (T a b c)) := by
  classical
  have hswap {F : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ} :
      (∑ a : Fin n, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k, F a b c i j k) =
        ∑ i : Fin n, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, F a b c i j k := by
    have h := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun q p : Fin n × (Fin n × Fin n) ↦
        F q.1 q.2.1 q.2.2 p.1 p.2.1 p.2.2)
    simpa only [Fintype.sum_prod_type] using h
  have htrace : RCLike.re ((Matrix.kronecker gᵀ (Matrix.kronecker g⁻¹ g⁻¹) *
      Matrix.vecMulVec (fun p : Fin n × (Fin n × Fin n) ↦ T p.1 p.2.1 p.2.2)
        (star (fun p : Fin n × (Fin n × Fin n) ↦ T p.1 p.2.1 p.2.2))).trace) =
      ∑ a : Fin n, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k,
        RCLike.re (g i a * g⁻¹ b j * g⁻¹ c k * T i j k * star (T a b c)) := by
    simp [Matrix.kronecker, Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.transpose_apply, Matrix.diag_apply, Fintype.sum_prod_type,
      mul_assoc, mul_left_comm, mul_comm]
  calc
    _ = ∑ a : Fin n, ∑ b, ∑ c, ∑ i, ∑ j, ∑ k,
        RCLike.re (g i a * g⁻¹ b j * g⁻¹ c k * T i j k * star (T a b c)) := htrace
    _ = ∑ i : Fin n, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        RCLike.re (g i a * g⁻¹ b j * g⁻¹ c k * T i j k * star (T a b c)) := hswap
    _ = RCLike.re (∑ i : Fin n, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
        g i a * g⁻¹ b j * g⁻¹ c k * T i j k * star (T a b c)) := by
      simp only [_root_.map_sum]

open Matrix in
open scoped Kronecker in
private theorem c3_weight_matrix_inv_diag {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : g.PosDef) (i j k : Fin n) :
    (Matrix.kronecker gᵀ (Matrix.kronecker g⁻¹ g⁻¹))⁻¹ (i, (j, k)) (i, (j, k)) =
      g⁻¹ i i * g j j * g k k := by
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg.isUnit
  have hinvInv : (g⁻¹)⁻¹ = g := by
    apply Matrix.inv_eq_left_inv
    exact Matrix.mul_nonsing_inv g hdet
  have hinvKr : (Matrix.kronecker gᵀ (Matrix.kronecker g⁻¹ g⁻¹))⁻¹ =
      (gᵀ)⁻¹ ⊗ₖ ((g⁻¹)⁻¹ ⊗ₖ (g⁻¹)⁻¹) := by
    simp only [Matrix.kronecker, Matrix.inv_kronecker]
  rw [hinvKr, ← Matrix.transpose_nonsing_inv, hinvInv]
  simp [Matrix.transpose_apply, mul_assoc]

open Matrix in
open scoped BigOperators Kronecker in
private theorem c3_tensor_weight_inv_diag_le {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g.PosDef) (Cinv C : ℝ)
    (hCinv : 0 ≤ Cinv) (hC : 0 ≤ C)
    (hgi : ∀ i, ‖g⁻¹ i i‖ ≤ Cinv) (hgdiag : ∀ i, ‖g i i‖ ≤ C) :
    ∀ i j k, RCLike.re
      ((Matrix.kronecker gᵀ (Matrix.kronecker g⁻¹ g⁻¹))⁻¹ (i, (j, k)) (i, (j, k))) ≤
        Cinv * C * C := by
  intro i j k
  rw [c3_weight_matrix_inv_diag g hg i j k]
  calc
    RCLike.re (g⁻¹ i i * g j j * g k k) ≤
        ‖g⁻¹ i i * g j j * g k k‖ := RCLike.re_le_norm _
    _ = ‖g⁻¹ i i‖ * ‖g j j‖ * ‖g k k‖ := by rw [norm_mul, norm_mul]
    _ = ‖g⁻¹ i i‖ * (‖g j j‖ * ‖g k k‖) := by ring
    _ ≤ Cinv * (C * C) := by
      have hjk : ‖g j j‖ * ‖g k k‖ ≤ C * C :=
        mul_le_mul (hgdiag j) (hgdiag k) (norm_nonneg _) hC
      exact mul_le_mul (hgi i) hjk
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCinv
    _ = Cinv * C * C := by ring

open Matrix in
open scoped BigOperators Kronecker in
private theorem c3_tensor_connection_bound_of_energy {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (T : Fin n → Fin n → Fin n → ℂ)
    (hg : g.PosDef) (B C : ℝ) (hC : 0 ≤ C)
    (hEnergy : RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
        g i a * g⁻¹ b j * g⁻¹ c k * T i j k * star (T a b c)) ≤ B)
    (hDiag : ∀ p : Fin n × (Fin n × Fin n),
      RCLike.re ((Matrix.kronecker gᵀ (Matrix.kronecker g⁻¹ g⁻¹))⁻¹ p p) ≤ C)
    (i j k : Fin n) : ‖T i j k‖ ≤ Real.sqrt (max B 0 * C) := by
  let ι := Fin n × (Fin n × Fin n)
  let W : Matrix ι ι ℂ := Matrix.kronecker gᵀ (Matrix.kronecker g⁻¹ g⁻¹)
  let v : ι → ℂ := fun p ↦ T p.1 p.2.1 p.2.2
  have hW : W.PosDef := by
    exact Matrix.PosDef.kronecker hg.transpose
      (Matrix.PosDef.kronecker hg.inv hg.inv)
  have hDiagW : ∀ p, RCLike.re (W⁻¹ p p) ≤ C := by
    intro p
    exact hDiag p
  have hQuad : RCLike.re (star v ⬝ᵥ (W *ᵥ v)) ≤ max B 0 := by
    calc
      RCLike.re (star v ⬝ᵥ (W *ᵥ v)) =
          RCLike.re ((W * Matrix.vecMulVec v (star v)).trace) := by
        exact congrArg RCLike.re (c3_trace_quadratic_eq W v)
      _ = RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
            g i a * g⁻¹ b j * g⁻¹ c k * T i j k * star (T a b c)) := by
        simpa [W, v] using c3_tensor_trace_eq_energy g T
      _ ≤ max B 0 := le_trans hEnergy (le_max_left B 0)
  have hDiagNonneg (p : ι) : 0 ≤ RCLike.re (W⁻¹ p p) := by
    exact (RCLike.pos_iff.mp hW.inv.diag_pos).1.le
  have hcomp := c3_component_normSq_le_quadratic_mul_inverse_diag W hW v (i, (j, k))
  have hsq : ‖T i j k‖ ^ 2 ≤ max B 0 * C := by
    have hmul := mul_le_mul hQuad (hDiagW (i, (j, k)))
      (hDiagNonneg (i, (j, k))) (le_max_right B 0)
    simpa [v, Complex.normSq_eq_norm_sq] using hcomp.trans hmul
  have harg : 0 ≤ max B 0 * C := mul_nonneg (le_max_right B 0) hC
  have hsqrt : 0 ≤ Real.sqrt (max B 0 * C) := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) hsqrt).1
  calc
    ‖T i j k‖ ^ 2 ≤ max B 0 * C := hsq
    _ = Real.sqrt (max B 0 * C) ^ 2 := (Real.sq_sqrt harg).symm

omit [T2Space M] [CompactSpace M] in
private theorem chartRep_diag_le_of_relTrace [NeZero n]
    (eta theta : FormField (EuclideanSpace ℂ (Fin n)) M 2) (x y : M)
    (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source)
    (heta : (eta y).IsPositive) (htheta : (theta y).IsPositive) {D : ℝ}
    (htrace : relTrace (eta y) (theta y) ≤ D) (i : Fin n) :
    RCLike.re ((theta.chartRep x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).coeffMatrix i i) ≤
    D * RCLike.re ((eta.chartRep x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).coeffMatrix i i) := by
  let ηc := eta.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)
  let θc := theta.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)
  have hηc : ηc.IsPositive := chartRep_isPositive eta x y hy heta
  have hθc : θc.IsPositive := chartRep_isPositive theta x y hy htheta
  have htraceChart := relTrace_chartRep_eq eta theta x y hy heta.1 htheta.1
  have hdiag := form_diag_le_relTrace ηc θc hηc hθc i
  have hηdiag : 0 ≤ RCLike.re (ηc.coeffMatrix i i) := by
    exact (RCLike.pos_iff.mp ((isPositive_iff.mp hηc).2.diag_pos)).1.le
  calc
    RCLike.re (θc.coeffMatrix i i) ≤
        relTrace ηc θc * RCLike.re (ηc.coeffMatrix i i) := hdiag
    _ ≤ D * RCLike.re (ηc.coeffMatrix i i) :=
      mul_le_mul_of_nonneg_right (by rw [← htraceChart]; exact htrace) hηdiag

omit [T2Space M] [CompactSpace M] in
private theorem exists_metricChart_entry_bound_on_compact
    (ω₀ : KahlerForm n M) (x₀ : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ C, ∀ z ∈ K, ∀ j k, ‖ω₀.metricInChart x₀ z j k‖ ≤ C := by
  classical
  have hentry_bound : ∀ j k, ∃ C, ∀ z ∈ K,
      ‖ω₀.metricInChart x₀ z j k‖ ≤ C := by
    intro j k
    exact hK.exists_bound_of_continuousOn
      ((ω₀.contDiffOn_metricInChart x₀ j k).continuousOn.mono hKt)
  let Cjk : Fin n × Fin n → ℝ := fun jk ↦ Classical.choose (hentry_bound jk.1 jk.2)
  have hCjk (jk : Fin n × Fin n) : ∀ z ∈ K,
      ‖ω₀.metricInChart x₀ z jk.1 jk.2‖ ≤ Cjk jk :=
    Classical.choose_spec (hentry_bound jk.1 jk.2)
  obtain ⟨C, hC⟩ := (Set.finite_range Cjk).bddAbove
  refine ⟨C, ?_⟩
  intro z hz j k
  exact (hCjk (j, k) z hz).trans (hC (Set.mem_range_self (j, k)))

omit [T2Space M] [CompactSpace M] in
private theorem exists_metricInvChart_entry_bound_on_compact
    (ω₀ : KahlerForm n M) (x₀ : M)
    (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ C, ∀ z ∈ K, ∀ j k,
      ‖(ω₀.metricInChart x₀ z)⁻¹ j k‖ ≤ C := by
  classical
  let T := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target
  have hmatrix : ContinuousOn (fun z ↦ ω₀.metricInChart x₀ z) T := by
    refine continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦ ?_
    exact (ω₀.contDiffOn_metricInChart x₀ j k).continuousOn
  have hmatrix' : Continuous (fun z : T ↦ ω₀.metricInChart x₀ z.1) :=
    continuousOn_iff_continuous_domRestrict.1 hmatrix
  have hdet : Continuous (fun z : T ↦ (ω₀.metricInChart x₀ z.1).det) :=
    hmatrix'.matrix_det
  have hadjugate : Continuous (fun z : T ↦ (ω₀.metricInChart x₀ z.1).adjugate) :=
    hmatrix'.matrix_adjugate
  have hinv_entry : ∀ j k, Continuous (fun z : T ↦ (ω₀.metricInChart x₀ z.1)⁻¹ j k) := by
    intro j k
    have hdet_ne : ∀ z : T, (ω₀.metricInChart x₀ z.1).det ≠ 0 := by
      intro z
      have hpos := ω₀.posDef_metricInChart x₀ z.2
      have hdet_pos : 0 < RCLike.re (ω₀.metricInChart x₀ z.1).det :=
        (RCLike.pos_iff.mp hpos.det_pos).1
      intro hdet_zero
      exact hdet_pos.ne' (by simp [hdet_zero])
    have hentry (z : T) : (ω₀.metricInChart x₀ z.1)⁻¹ j k =
        ((ω₀.metricInChart x₀ z.1).det)⁻¹ *
          (ω₀.metricInChart x₀ z.1).adjugate j k := by
      rw [Matrix.inv_def]
      simp [Matrix.smul_apply, Ring.inverse_eq_inv']
    have hfun : (fun z : T ↦ (ω₀.metricInChart x₀ z.1)⁻¹ j k) =
        fun z ↦ ((ω₀.metricInChart x₀ z.1).det)⁻¹ *
          (ω₀.metricInChart x₀ z.1).adjugate j k := by
      funext z
      exact hentry z
    rw [hfun]
    exact (hdet.inv₀ hdet_ne).mul (hadjugate.matrix_elem j k)
  have hinv : ContinuousOn (fun z ↦ (ω₀.metricInChart x₀ z)⁻¹) T := by
    refine continuousOn_pi.2 fun j ↦ continuousOn_pi.2 fun k ↦ ?_
    exact continuousOn_iff_continuous_domRestrict.2 (hinv_entry j k)
  have hentry_bound : ∀ j k, ∃ C, ∀ z ∈ K,
      ‖(ω₀.metricInChart x₀ z)⁻¹ j k‖ ≤ C := by
    intro j k
    have hentry_cont : ContinuousOn (fun z ↦ (ω₀.metricInChart x₀ z)⁻¹ j k) T :=
      (continuousOn_pi.1 (continuousOn_pi.1 hinv j) k)
    exact hK.exists_bound_of_continuousOn (hentry_cont.mono hKt)
  let Cjk : Fin n × Fin n → ℝ := fun jk ↦ Classical.choose (hentry_bound jk.1 jk.2)
  have hCjk (jk : Fin n × Fin n) : ∀ z ∈ K,
      ‖(ω₀.metricInChart x₀ z)⁻¹ jk.1 jk.2‖ ≤ Cjk jk :=
    Classical.choose_spec (hentry_bound jk.1 jk.2)
  obtain ⟨C, hC⟩ := (Set.finite_range Cjk).bddAbove
  refine ⟨C, ?_⟩
  intro z hz j k
  exact (hCjk (j, k) z hz).trans (hC (Set.mem_range_self (j, k)))

omit [T2Space M] [CompactSpace M] in
private theorem c3_chart_perturbed_metric_diagonal_bounds [NeZero n]
    (ω₀ : KahlerForm n M) (φ : M → ℝ)
    (hφ : ω₀.IsPotential φ) (x₀ : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target)
    (D C₀ Cinv : ℝ) (hD : 0 < D)
    (hbase : ∀ i, ‖ω₀.metricInChart x₀ z i i‖ ≤ C₀)
    (hbaseInv : ∀ i, ‖(ω₀.metricInChart x₀ z)⁻¹ i i‖ ≤ Cinv)
    (htrace : relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z))
      (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z) +
        mddbar n φ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z)) ≤ D)
    (htraceInv : relTrace
      (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z) +
        mddbar n φ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z))
      (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z)) ≤ D) :
    ∀ i : Fin n,
      ‖(ω₀.metricInChart x₀ z + complexHessian
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) z) i i‖ ≤ D * C₀ ∧
      ‖((ω₀.metricInChart x₀ z + complexHessian
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) z)⁻¹ i i)‖ ≤ D * Cinv := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let y := e.symm z
  let η : FormField (EuclideanSpace ℂ (Fin n)) M 2 := ω₀.toFormField
  let θ : FormField (EuclideanSpace ℂ (Fin n)) M 2 := ω₀.toFormField + mddbar n φ
  let g : Matrix (Fin n) (Fin n) ℂ := ω₀.metricInChart x₀ z +
    complexHessian (φ ∘ e.symm) z
  have hyR : y ∈ e.source := e.map_target hz
  have hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
    rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))]
    exact hyR
  have hyz : e y = z := e.right_inv hz
  have hη : (η y).IsPositive := ω₀.isPositive y
  have hθ : (θ y).IsPositive := hφ.2 y
  have htraceFwd : relTrace (η y) (θ y) ≤ D := by
    change relTrace (ω₀ y) (ω₀ y + mddbar n φ y) ≤ D
    exact htrace
  have htraceRev : relTrace (θ y) (η y) ≤ D := by
    change relTrace (ω₀ y + mddbar n φ y) (ω₀ y) ≤ D
    exact htraceInv
  have hA : (ω₀.metricInChart x₀ z).PosDef := ω₀.posDef_metricInChart x₀ hz
  have hG : g.PosDef := by
    change (ω₀.metricInChart x₀ z + complexHessian (φ ∘ e.symm) z).PosDef
    have hpos := (ω₀.perturb φ hφ).posDef_metricInChart x₀ hz
    rw [ω₀.metricInChart_perturb hφ x₀ hz] at hpos
    exact hpos
  have hηcoeff : (η.chartRep x₀ z).coeffMatrix = ω₀.metricInChart x₀ z := rfl
  have hθcoeff : (θ.chartRep x₀ z).coeffMatrix = g := by
    change ((ω₀.toFormField.chartRep x₀ z + (mddbar n φ).chartRep x₀ z).coeffMatrix) = g
    rw [ContinuousAlternatingMap.coeffMatrix_add, hηcoeff,
      chartRep_mddbar hφ.1 x₀ hz]
    rfl
  have hdiagTrace := chartRep_diag_le_of_relTrace η θ x₀ y hy hη hθ htraceFwd
  rw [hyz, hηcoeff, hθcoeff] at hdiagTrace
  have hbaseRe (i : Fin n) : RCLike.re ((ω₀.metricInChart x₀ z) i i) ≤ C₀ := by
    calc
      _ = ‖(ω₀.metricInChart x₀ z) i i‖ :=
        (posDef_diag_norm_eq_re (ω₀.metricInChart x₀ z) hA i).symm
      _ ≤ C₀ := hbase i
  have hinvOrder : (ω₀.metricInChart x₀ z) ≤ D • g := by
    have h := chartRep_order_of_reverse_relTrace η θ x₀ hz hη hθ htraceRev
    rw [hηcoeff, hθcoeff] at h
    exact h
  have hinvOrder' := inverse_le_scaled_inverse_of_scaled_lower_bound
    (ω₀.metricInChart x₀ z) g hA D hD hinvOrder
  have hInvPos : (g⁻¹).PosDef := hG.inv
  have hinvBaseRe (i : Fin n) : RCLike.re ((ω₀.metricInChart x₀ z)⁻¹ i i) ≤ Cinv := by
    calc
      _ = ‖(ω₀.metricInChart x₀ z)⁻¹ i i‖ :=
        (posDef_diag_norm_eq_re _ hA.inv i).symm
      _ ≤ Cinv := hbaseInv i
  intro i
  constructor
  · calc
      ‖g i i‖ = RCLike.re (g i i) := posDef_diag_norm_eq_re g hG i
      _ ≤ D * RCLike.re ((ω₀.metricInChart x₀ z) i i) := hdiagTrace i
      _ ≤ D * C₀ := mul_le_mul_of_nonneg_left (hbaseRe i) hD.le
  · have hdiag := (Matrix.le_iff.mp hinvOrder').diag_nonneg (i := i)
    have hdiagR := (RCLike.nonneg_iff.mp hdiag).1
    have hdiagSc : 0 ≤ D * RCLike.re ((ω₀.metricInChart x₀ z)⁻¹ i i) -
        RCLike.re (g⁻¹ i i) := by
      simpa [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
        RCLike.re_ofReal_mul] using hdiagR
    have hInvRe : RCLike.re (g⁻¹ i i) ≤ D * Cinv := by
      calc
        RCLike.re (g⁻¹ i i) ≤ D *
            RCLike.re ((ω₀.metricInChart x₀ z)⁻¹ i i) := (sub_nonneg.mp hdiagSc)
        _ ≤ D * Cinv := mul_le_mul_of_nonneg_left (hinvBaseRe i) hD.le
    calc
      ‖g⁻¹ i i‖ = RCLike.re (g⁻¹ i i) := posDef_diag_norm_eq_re (g⁻¹) hInvPos i
      _ ≤ D * Cinv := hInvRe

/-- A pointwise Calabi-energy bound controls every component of the difference of the two
holomorphic connections, uniformly on a compact chart piece. This is the finite-dimensional
coercivity step for the weighted contraction defining `calabiEnergyInChart`. -/
private theorem exists_uniform_c3ConnectionDifference_bound_of_calabiEnergy
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hMetric : ∃ D : ℝ, 0 < D ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ D ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ D)
    (B : ℝ) (hEnergy : ∀ p ∈ S, ∀ x, calabiEnergy ω₀ p.2 x ≤ B)
    (x₀ : M) (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ T : ℝ, ∀ p ∈ S, ∀ z ∈ K, ∀ i j k : Fin n,
      ‖c3ConnectionDifferenceInChart ω₀ p.2 x₀ z i j k‖ ≤ T := by
  classical
  by_cases hKne : K.Nonempty
  · by_cases hSne : S.Nonempty
    · by_cases hn : n = 0
      · subst n
        refine ⟨0, ?_⟩
        intro p hp z hz i j k
        exact Fin.elim0 i
      · obtain ⟨D, hD, htr⟩ := hMetric
        obtain ⟨C₀, hC₀⟩ := exists_metricChart_entry_bound_on_compact ω₀ x₀ K hK hKt
        obtain ⟨Cinv, hCinv⟩ :=
          exists_metricInvChart_entry_bound_on_compact ω₀ x₀ K hK hKt
        let C₀' := max C₀ 0
        let Cinv' := max Cinv 0
        have hC₀' : 0 ≤ C₀' := le_max_right _ _
        have hCinv' : 0 ≤ Cinv' := le_max_right _ _
        let Cg := D * C₀'
        let Cginv := D * Cinv'
        have hCg : 0 ≤ Cg := mul_nonneg hD.le hC₀'
        have hCginv : 0 ≤ Cginv := mul_nonneg hD.le hCinv'
        let C := Cginv * Cg * Cg
        have hC : 0 ≤ C := by positivity
        refine ⟨Real.sqrt (max B 0 * C), ?_⟩
        intro p hp z hz i j k
        obtain ⟨_, hsol⟩ := hS p hp
        let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
        have hzTarget : z ∈ e.target := hKt hz
        let g : Matrix (Fin n) (Fin n) ℂ := ω₀.metricInChart x₀ z +
          complexHessian (p.2 ∘ e.symm) z
        let T : Fin n → Fin n → Fin n → ℂ := fun a b c ↦
          c3ConnectionDifferenceInChart ω₀ p.2 x₀ z a b c
        have hg : g.PosDef := by
          change (ω₀.metricInChart x₀ z + complexHessian (p.2 ∘ e.symm) z).PosDef
          have hpos := (ω₀.perturb p.2 hsol.1).posDef_metricInChart x₀ hzTarget
          rw [ω₀.metricInChart_perturb hsol.1 x₀ hzTarget] at hpos
          exact hpos
        have hEnergyChart := calabiEnergyInChart_le_of_global_bound ω₀ p.2 p.1
          hsol.1.1 hsol B (fun x ↦ hEnergy p hp x) x₀ hzTarget
        have hEnergyTensor : RCLike.re
            (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
                g i a * g⁻¹ b j * g⁻¹ c k * T i j k * star (T a b c)) ≤ B := by
          have hEq : calabiEnergyInChart ω₀ p.2 x₀ z =
              RCLike.re (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                ∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n,
                  g i a * g⁻¹ b j * g⁻¹ c k * T i j k * star (T a b c)) := by
            rfl
          rw [← hEq]
          exact hEnergyChart
        rcases htr p hp (e.symm z) with ⟨htrace, htraceInv⟩
        let : NeZero n := ⟨hn⟩
        have hdiag := c3_chart_perturbed_metric_diagonal_bounds ω₀ p.2 hsol.1 x₀ hzTarget
          D C₀' Cinv' hD
          (fun a ↦ (hC₀ z hz a a).trans (le_max_left _ _))
          (fun a ↦ (hCinv z hz a a).trans (le_max_left _ _)) htrace htraceInv
        have hWdiag : ∀ q : Fin n × (Fin n × Fin n),
            RCLike.re ((Matrix.kronecker (Matrix.transpose g)
              (Matrix.kronecker (g⁻¹) (g⁻¹)))⁻¹ q q) ≤ C := by
          intro q
          rcases q with ⟨a, ⟨b, c⟩⟩
          rw [c3_weight_matrix_inv_diag g hg a b c]
          calc
            RCLike.re (g⁻¹ a a * g b b * g c c) ≤
                ‖g⁻¹ a a * g b b * g c c‖ := RCLike.re_le_norm _
            _ = ‖g⁻¹ a a‖ * ‖g b b‖ * ‖g c c‖ := by rw [norm_mul, norm_mul]
            _ = ‖g⁻¹ a a‖ * (‖g b b‖ * ‖g c c‖) := by ring
            _ ≤ Cginv * (Cg * Cg) := by
              have hbc : ‖g b b‖ * ‖g c c‖ ≤ Cg * Cg :=
                mul_le_mul (hdiag b).1 (hdiag c).1 (norm_nonneg _) hCg
              exact mul_le_mul (hdiag a).2 hbc
                (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCginv
            _ = C := by dsimp [C, Cginv, Cg]; ring
        exact c3_tensor_connection_bound_of_energy g T hg B C hC
          hEnergyTensor hWdiag i j k
    · refine ⟨0, ?_⟩
      intro p hp z hz i j k
      exact (hSne ⟨p, hp⟩).elim
  · refine ⟨0, ?_⟩
    intro p hp z hz i j k
    exact (hKne ⟨z, hz⟩).elim

/-- Recover a metric derivative from the difference of the two connection coefficients. -/
private theorem c3_recover_complex_derivative_from_connection_difference {n : ℕ}
    (g g₀ : Matrix (Fin n) (Fin n) ℂ) (q q₀ T : Fin n → ℂ)
    (hdet : IsUnit g.det) (m : Fin n)
    (hT : ∀ i, T i =
      (∑ l : Fin n, g⁻¹ l i * q l) - (∑ l : Fin n, g₀⁻¹ l i * q₀ l)) :
    q m = ∑ i : Fin n, g i m *
      (T i + ∑ l : Fin n, g₀⁻¹ l i * q₀ l) := by
  have hmatrix (l : Fin n) : ∑ i : Fin n, g⁻¹ l i * g i m = if l = m then 1 else 0 := by
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul g hdet]
    simp only [Matrix.one_apply]
  have hrecover : ∑ i : Fin n, g i m * (∑ l : Fin n, g⁻¹ l i * q l) = q m := by
    calc
      _ = ∑ i : Fin n, ∑ l : Fin n, g i m * (g⁻¹ l i * q l) := by
        simp [Finset.mul_sum]
      _ = ∑ l : Fin n, ∑ i : Fin n, g i m * (g⁻¹ l i * q l) := by
        rw [Finset.sum_comm]
      _ = ∑ l : Fin n, (∑ i : Fin n, g⁻¹ l i * g i m) * q l := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = q m := by simp [hmatrix]
  calc
    q m = ∑ i : Fin n, g i m * (∑ l : Fin n, g⁻¹ l i * q l) := hrecover.symm
    _ = ∑ i : Fin n, g i m *
        ((∑ l : Fin n, g⁻¹ l i * q l) -
          (∑ l : Fin n, g₀⁻¹ l i * q₀ l) + ∑ l : Fin n, g₀⁻¹ l i * q₀ l) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [sub_add_cancel]
    _ = ∑ i : Fin n, g i m * (T i + ∑ l : Fin n, g₀⁻¹ l i * q₀ l) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hT i]

/-- Component bounds on the metric and connection control the recovered derivative. -/
private theorem c3_norm_recovered_derivative_le {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℂ) (q r T : Fin n → ℂ)
    (G A R : ℝ) (hG : 0 ≤ G)
    (hrec : ∀ m, q m = ∑ i : Fin n, g i m * (T i + r i))
    (hg : ∀ i m, ‖g i m‖ ≤ G)
    (hT : ∀ i, ‖T i‖ ≤ A) (hr : ∀ i, ‖r i‖ ≤ R)
    (m : Fin n) :
    ‖q m‖ ≤ (Fintype.card (Fin n) : ℝ) * G * (A + R) := by
  rw [hrec m]
  calc
    ‖∑ i : Fin n, g i m * (T i + r i)‖ ≤
        ∑ i : Fin n, ‖g i m * (T i + r i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, G * (A + R) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖g i m * (T i + r i)‖ = ‖g i m‖ * ‖T i + r i‖ := norm_mul _ _
        _ ≤ G * (A + R) := mul_le_mul (hg i m)
          (le_trans (norm_add_le _ _) (add_le_add (hT i) (hr i)))
          (norm_nonneg _) hG
    _ = (Fintype.card (Fin n) : ℝ) * G * (A + R) := by simp [mul_assoc]

private theorem differentiableAt_coeffMatrix_local {n : ℕ}
    {α : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    {z : EuclideanSpace ℂ (Fin n)} (hα : DifferentiableAt ℝ α z) :
    DifferentiableAt ℝ (fun w j k ↦ (α w).coeffMatrix j k) z := by
  change DifferentiableAt ℝ (fun w j k ↦
    ((α w ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] : ℂ) -
      Complex.I * (α w ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℂ)) / 2) z
  fun_prop (disch := assumption)

private theorem fderiv_coeffMatrix_local {n : ℕ}
    {α : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    {z v : EuclideanSpace ℂ (Fin n)} (hα : DifferentiableAt ℝ α z) :
    fderiv ℝ (fun w j k ↦ (α w).coeffMatrix j k) z v =
      (fun j k ↦ (fderiv ℝ α z v).coeffMatrix j k) := by
  have hcoeff := differentiableAt_coeffMatrix_local hα
  rw [fderiv_pi (fun j => differentiableAt_pi.mp hcoeff j)]
  ext j k
  rw [ContinuousLinearMap.pi_apply]
  rw [fderiv_pi (fun k => differentiableAt_pi.mp (differentiableAt_pi.mp hcoeff j) k)]
  rw [ContinuousLinearMap.pi_apply]
  let u₁ : Fin 2 → EuclideanSpace ℂ (Fin n) := ![EuclideanSpace.single j 1,
    Complex.I • EuclideanSpace.single k 1]
  let u₂ : Fin 2 → EuclideanSpace ℂ (Fin n) := ![EuclideanSpace.single j 1,
    EuclideanSpace.single k 1]
  have hA : DifferentiableAt ℝ (fun w ↦ α w u₁) z := hα.continuousAlternatingMap_apply_const u₁
  have hB : DifferentiableAt ℝ (fun w ↦ α w u₂) z := hα.continuousAlternatingMap_apply_const u₂
  have hAcast : (fun w ↦ ((α w u₁ : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun w ↦ α w u₁) := rfl
  have hBcast : (fun w ↦ ((α w u₂ : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun w ↦ α w u₂) := rfl
  have hAcomplex : DifferentiableAt ℝ (fun w ↦ ((α w u₁ : ℝ) : ℂ)) z := by
    rw [hAcast]
    exact Complex.ofRealCLM.differentiableAt.comp z hA
  have hBcomplex : DifferentiableAt ℝ (fun w ↦ ((α w u₂ : ℝ) : ℂ)) z := by
    rw [hBcast]
    exact Complex.ofRealCLM.differentiableAt.comp z hB
  have hAderiv : fderiv ℝ (fun w ↦ ((α w u₁ : ℝ) : ℂ)) z =
      Complex.ofRealCLM.comp (fderiv ℝ (fun w ↦ α w u₁) z) := by
    rw [hAcast]
    exact (Complex.ofRealCLM.hasFDerivAt.comp z hA.hasFDerivAt).fderiv
  have hBderiv : fderiv ℝ (fun w ↦ ((α w u₂ : ℝ) : ℂ)) z =
      Complex.ofRealCLM.comp (fderiv ℝ (fun w ↦ α w u₂) z) := by
    rw [hBcast]
    exact (Complex.ofRealCLM.hasFDerivAt.comp z hB.hasFDerivAt).fderiv
  change fderiv ℝ (fun w ↦
      (((α w u₁ : ℝ) : ℂ) - Complex.I * (α w u₂ : ℝ)) / 2) z v =
    ((((fderiv ℝ α z v) u₁ : ℝ) : ℂ) - Complex.I * ((fderiv ℝ α z v) u₂ : ℝ)) / 2
  have hnum : DifferentiableAt ℝ
      (fun w ↦ ((α w u₁ : ℝ) : ℂ) - Complex.I * (α w u₂ : ℝ)) z :=
    hAcomplex.sub (hBcomplex.const_mul Complex.I)
  rw [show (fun w ↦ (((α w u₁ : ℝ) : ℂ) - Complex.I * (α w u₂ : ℝ)) / 2) =
      (fun w ↦ (2 : ℂ)⁻¹ * (((α w u₁ : ℝ) : ℂ) - Complex.I * (α w u₂ : ℝ))) by
    funext w
    simp only [div_eq_mul_inv]
    ring]
  rw [fderiv_const_mul hnum (2 : ℂ)⁻¹]
  rw [fderiv_fun_sub hAcomplex (hBcomplex.const_mul Complex.I)]
  rw [fderiv_const_mul hBcomplex Complex.I, hAderiv, hBderiv]
  simp only [_root_.sub_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, Complex.ofRealCLM_apply]
  rw [fderiv_continuousAlternatingMap_apply_const_apply hα u₁ v,
    fderiv_continuousAlternatingMap_apply_const_apply hα u₂ v]
  ring_nf

private theorem isOneOne_fderiv_local {n : ℕ}
    {α : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    {z v : EuclideanSpace ℂ (Fin n)} (hα : DifferentiableAt ℝ α z)
    (hOne : ∀ᶠ w in 𝓝 z, (α w).IsOneOne) : (fderiv ℝ α z v).IsOneOne := by
  intro u w
  let a : Fin 2 → EuclideanSpace ℂ (Fin n) := ![Complex.I • u, Complex.I • w]
  let b : Fin 2 → EuclideanSpace ℂ (Fin n) := ![u, w]
  have heq : (fun x ↦ α x a) =ᶠ[𝓝 z] fun x ↦ α x b := by
    filter_upwards [hOne] with x hx
    exact hx u w
  have hderiv := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L v) heq.fderiv_eq
  rw [fderiv_continuousAlternatingMap_apply_const_apply hα a v,
    fderiv_continuousAlternatingMap_apply_const_apply hα b v] at hderiv
  exact hderiv

private theorem norm_le_coeffMatrix_local {n : ℕ}
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ} (hα : α.IsOneOne) :
    ‖α‖ ≤ 2 * (n : ℝ) ^ 2 * ‖(fun j k ↦ α.coeffMatrix j k)‖ := by
  classical
  open Complex in
  let C : ℝ := ‖(fun j k ↦ α.coeffMatrix j k)‖
  have hC : 0 ≤ C := norm_nonneg _
  have hcoeff (j k : Fin n) : ‖α.coeffMatrix j k‖ ≤ C := by
    dsimp [C]
    exact (norm_le_pi_norm (α.coeffMatrix j) k).trans (norm_le_pi_norm α.coeffMatrix j)
  have hcoord (u : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ‖u j‖ ≤ ‖u‖ := PiLp.norm_apply_le u j
  have hterm (u v : EuclideanSpace ℂ (Fin n)) (j k : Fin n) :
      ‖α.coeffMatrix j k * u j * star (v k)‖ ≤ C * ‖u‖ * ‖v‖ := by
    calc
      ‖α.coeffMatrix j k * u j * star (v k)‖ =
          ‖α.coeffMatrix j k‖ * ‖u j‖ * ‖v k‖ := by simp
      _ ≤ C * ‖u‖ * ‖v‖ := by
        exact mul_le_mul (mul_le_mul (hcoeff j k) (hcoord u j) (norm_nonneg _) (norm_nonneg _))
          (hcoord v k) (by positivity) (by positivity)
  have hsum (u v : EuclideanSpace ℂ (Fin n)) :
      ‖∑ j : Fin n, ∑ k : Fin n, α.coeffMatrix j k * u j * star (v k)‖ ≤
        (n : ℝ) ^ 2 * (C * ‖u‖ * ‖v‖) := by
    calc
      ‖∑ j : Fin n, ∑ k : Fin n, α.coeffMatrix j k * u j * star (v k)‖ ≤
          ∑ j : Fin n, ∑ k : Fin n, ‖α.coeffMatrix j k * u j * star (v k)‖ := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ norm_sum_le _ _)
      _ ≤ ∑ j : Fin n, ∑ k : Fin n, (C * ‖u‖ * ‖v‖) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact hterm u v j k
      _ = (n : ℝ) ^ 2 * (C * ‖u‖ * ‖v‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring_nf
  have heval (u v : EuclideanSpace ℂ (Fin n)) :
      ‖α ![u, v]‖ ≤ 2 * (n : ℝ) ^ 2 * C * ‖u‖ * ‖v‖ := by
    rw [hα.apply_eq]
    change |(-2 * (∑ j : Fin n, ∑ k : Fin n,
      α.coeffMatrix j k * u j * star (v k)).im)| ≤ _
    calc
      |(-2 * (∑ j : Fin n, ∑ k : Fin n,
          α.coeffMatrix j k * u j * star (v k)).im)| ≤
          2 * ‖∑ j : Fin n, ∑ k : Fin n,
            α.coeffMatrix j k * u j * star (v k)‖ := by
        simpa [abs_mul] using
          (mul_le_mul_of_nonneg_left
            (Complex.abs_im_le_norm (∑ j : Fin n, ∑ k : Fin n,
              α.coeffMatrix j k * u j * star (v k))) (by norm_num : 0 ≤ (2 : ℝ)))
      _ ≤ 2 * ((n : ℝ) ^ 2 * (C * ‖u‖ * ‖v‖)) := mul_le_mul_of_nonneg_left (hsum u v) (by norm_num)
      _ = 2 * (n : ℝ) ^ 2 * C * ‖u‖ * ‖v‖ := by ring
  refine ContinuousAlternatingMap.opNorm_le_bound α (by positivity) ?_
  intro m
  have hm : ‖α m‖ ≤ 2 * (n : ℝ) ^ 2 * C * ‖m 0‖ * ‖m 1‖ := by
    have hvec : m = ![m 0, m 1] := by funext i; fin_cases i <;> rfl
    rw [hvec]
    exact heval (m 0) (m 1)
  rw [Fin.prod_univ_two]
  calc
    ‖α m‖ ≤ 2 * (n : ℝ) ^ 2 * C * ‖m 0‖ * ‖m 1‖ := hm
    _ = 2 * (n : ℝ) ^ 2 * ‖(fun j k ↦ α.coeffMatrix j k)‖ * (‖m 0‖ * ‖m 1‖) := by
      simp only [C]
      ring

private theorem eventually_isOneOne_ddbar_local {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 3 f z) : ∀ᶠ w in 𝓝 z, (ddbar f w).IsOneOne := by
  have hf2 : ContDiffAt ℝ 2 f z := hf.of_le (by norm_num)
  filter_upwards [hf2.eventually (by norm_num)] with w hw
  exact isOneOne_ddbar hw

private theorem complexHessian_fderiv_isHermitian_local {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 3 f z) (hdd : DifferentiableAt ℝ (ddbar f) z)
    (v : EuclideanSpace ℂ (Fin n)) :
    Matrix.IsHermitian (fderiv ℝ (fun w j k ↦ complexHessian f w j k) z v) := by
  let hdiff := hdd
  have hOne := eventually_isOneOne_ddbar_local hf
  change Matrix.IsHermitian (fderiv ℝ (fun w j k ↦ (ddbar f w).coeffMatrix j k) z v)
  rw [fderiv_coeffMatrix_local (z := z) (v := v) hdiff]
  exact ContinuousAlternatingMap.IsOneOne.isHermitian_coeffMatrix
    (isOneOne_fderiv_local (v := v) hdiff hOne)

private theorem norm_le_wirtinger_of_isHermitian_local {n : ℕ}
    (L : EuclideanSpace ℂ (Fin n) →L[ℝ] (Fin n → Fin n → ℂ))
    (hL : ∀ v, Matrix.IsHermitian (L v)) (A : ℝ) (hA : 0 ≤ A)
    (hpartial : ∀ i j k : Fin n,
      ‖((L (EuclideanSpace.single i 1)) j k -
        Complex.I * (L (Complex.I • EuclideanSpace.single i 1)) j k) / 2‖ ≤ A) :
    ‖L‖ ≤ 4 * (n : ℝ) * A := by
  let e (i : Fin n) : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  have hcoords : ∀ i j k : Fin n,
      ‖(L (e i)) j k‖ ≤ 2 * A ∧ ‖(L (Complex.I • e i)) j k‖ ≤ 2 * A := by
    intro i j k
    let p : ℂ := ((L (e i)) j k - Complex.I * (L (Complex.I • e i)) j k) / 2
    let q : ℂ := ((L (e i)) k j - Complex.I * (L (Complex.I • e i)) k j) / 2
    have hp : ‖p‖ ≤ A := by simpa [p, e] using hpartial i j k
    have hq : ‖q‖ ≤ A := by simpa [q, e] using hpartial i k j
    have he : star ((L (e i)) k j) = (L (e i)) j k := (hL (e i)).apply j k
    have hiy : star ((L (Complex.I • e i)) k j) = (L (Complex.I • e i)) j k :=
      (hL (Complex.I • e i)).apply j k
    have hx : (L (e i)) j k = p + star q := by
      dsimp [p, q]
      simp only [map_div₀, map_sub, map_mul, starRingEnd_apply, map_ofNat]
      rw [he, hiy]
      simp only [Complex.star_def, Complex.conj_I]
      ring_nf
    have hy : (L (Complex.I • e i)) j k = Complex.I * (p - star q) := by
      dsimp [p, q]
      simp only [map_div₀, map_sub, map_mul, starRingEnd_apply, map_ofNat]
      rw [he, hiy]
      simp only [Complex.star_def, Complex.conj_I]
      ring_nf
      rw [Complex.I_sq]
      ring
    constructor
    · calc
        ‖(L (e i)) j k‖ = ‖p + star q‖ := by rw [hx]
        _ ≤ ‖p‖ + ‖star q‖ := norm_add_le _ _
        _ = ‖p‖ + ‖q‖ := by rw [norm_star]
        _ ≤ A + A := add_le_add hp hq
        _ = 2 * A := by ring
    · calc
        ‖(L (Complex.I • e i)) j k‖ = ‖Complex.I * (p - star q)‖ := by rw [hy]
        _ = ‖p - star q‖ := by simp
        _ ≤ ‖p‖ + ‖star q‖ := norm_sub_le _ _
        _ = ‖p‖ + ‖q‖ := by rw [norm_star]
        _ ≤ A + A := add_le_add hp hq
        _ = 2 * A := by ring
  have hdecomp (v : EuclideanSpace ℂ (Fin n)) :
      v = ∑ i : Fin n, (((v i).re : ℝ) • e i + ((v i).im : ℝ) • (Complex.I • e i)) := by
    ext j
    simp [e, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_add_distrib, Complex.re_add_im]
  have hentry (v : EuclideanSpace ℂ (Fin n)) (j k : Fin n) :
      ‖(L v) j k‖ ≤ 4 * (n : ℝ) * A * ‖v‖ := by
    have hv := congrArg (fun x : EuclideanSpace ℂ (Fin n) => (L x) j k) (hdecomp v)
    rw [_root_.map_sum] at hv
    simp only [map_add, map_smul, Fintype.sum_apply] at hv
    rw [hv]
    calc
      ‖∑ i : Fin n, (((v i).re : ℝ) • (L (e i)) j k +
          ((v i).im : ℝ) • (L (Complex.I • e i)) j k)‖
          ≤ ∑ i : Fin n, (‖(v i).re‖ * ‖(L (e i)) j k‖ +
            ‖(v i).im‖ * ‖(L (Complex.I • e i)) j k‖) := by
          refine (norm_sum_le _ _).trans ?_
          apply Finset.sum_le_sum
          intro i hi
          calc
            ‖((v i).re : ℝ) • (L (e i)) j k + ((v i).im : ℝ) • (L (Complex.I • e i)) j k‖
                ≤ ‖((v i).re : ℝ) • (L (e i)) j k‖ + ‖((v i).im : ℝ) • (L (Complex.I • e i)) j k‖ := norm_add_le _ _
            _ = ‖(v i).re‖ * ‖(L (e i)) j k‖ + ‖(v i).im‖ * ‖(L (Complex.I • e i)) j k‖ := by simp
      _ ≤ ∑ i : Fin n, (4 * A * ‖v‖) := by
          apply Finset.sum_le_sum
          intro i hi
          have hvi : ‖v i‖ ≤ ‖v‖ := PiLp.norm_apply_le v i
          have hre : ‖(v i).re‖ ≤ ‖v‖ := (Complex.abs_re_le_norm _).trans hvi
          have him : ‖(v i).im‖ ≤ ‖v‖ := (Complex.abs_im_le_norm _).trans hvi
          have hri := hcoords i j k
          calc
            ‖(v i).re‖ * ‖(L (e i)) j k‖ + ‖(v i).im‖ * ‖(L (Complex.I • e i)) j k‖
                ≤ ‖(v i).re‖ * (2 * A) + ‖(v i).im‖ * (2 * A) := by
                  apply add_le_add
                  · exact mul_le_mul_of_nonneg_left hri.1 (norm_nonneg _)
                  · exact mul_le_mul_of_nonneg_left hri.2 (norm_nonneg _)
            _ ≤ ‖v‖ * (2 * A) + ‖v‖ * (2 * A) := by
                  apply add_le_add
                  · exact mul_le_mul_of_nonneg_right hre (by positivity)
                  · exact mul_le_mul_of_nonneg_right him (by positivity)
            _ = 4 * A * ‖v‖ := by ring
      _ = 4 * (n : ℝ) * A * ‖v‖ := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  exact L.opNorm_le_bound (by positivity) (fun v => by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro j
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    exact hentry v j k)

private theorem norm_fderiv_ddbar_le_coeffDerivative_local {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 3 f z) (hdd : DifferentiableAt ℝ (ddbar f) z) :
    ‖fderiv ℝ (ddbar f) z‖ ≤ 2 * (n : ℝ) ^ 2 *
      ‖fderiv ℝ (fun w j k ↦ complexHessian f w j k) z‖ := by
  let hdiff := hdd
  have hOne := eventually_isOneOne_ddbar_local hf
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hOneOne : (fderiv ℝ (ddbar f) z v).IsOneOne :=
    isOneOne_fderiv_local (v := v) hdiff hOne
  have hnorm := norm_le_coeffMatrix_local hOneOne
  have hcoeff := fderiv_coeffMatrix_local (z := z) (v := v) hdiff
  change fderiv ℝ (fun w j k ↦ complexHessian f w j k) z v = _ at hcoeff
  rw [← hcoeff] at hnorm
  calc
    ‖fderiv ℝ (ddbar f) z v‖ ≤
        2 * (n : ℝ) ^ 2 * ‖fderiv ℝ (fun w j k ↦ complexHessian f w j k) z v‖ := hnorm
    _ ≤ 2 * (n : ℝ) ^ 2 *
        (‖fderiv ℝ (fun w j k ↦ complexHessian f w j k) z‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ v) (by positivity)
    _ = (2 * (n : ℝ) ^ 2 *
        ‖fderiv ℝ (fun w j k ↦ complexHessian f w j k) z‖) * ‖v‖ := by ring

private theorem norm_fderiv_ddbar_le_partialZ_local {n : ℕ}
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 3 f z) (hdd : DifferentiableAt ℝ (ddbar f) z)
    (A : ℝ) (hA : 0 ≤ A)
    (hpartial : ∀ i j k : Fin n,
      ‖(fderiv ℝ (fun w ↦ complexHessian f w j k) z (EuclideanSpace.single i 1) -
        Complex.I * fderiv ℝ (fun w ↦ complexHessian f w j k) z
          (Complex.I • EuclideanSpace.single i 1)) / 2‖ ≤ A) :
    ‖fderiv ℝ (ddbar f) z‖ ≤ 8 * (n : ℝ) ^ 3 * A := by
  have hcoeff := differentiableAt_coeffMatrix_local hdd
  change DifferentiableAt ℝ (fun w j k ↦ complexHessian f w j k) z at hcoeff
  have hmatrix : ‖fderiv ℝ (fun w j k ↦ complexHessian f w j k) z‖ ≤
      4 * (n : ℝ) * A := by
    apply norm_le_wirtinger_of_isHermitian_local
      (fderiv ℝ (fun w j k ↦ complexHessian f w j k) z)
      (complexHessian_fderiv_isHermitian_local hf hdd) A hA
    intro i j k
    have hj := differentiableAt_pi.mp hcoeff j
    have hentry (v : EuclideanSpace ℂ (Fin n)) :
        fderiv ℝ (fun w ↦ complexHessian f w j k) z v =
          (fderiv ℝ (fun w j k ↦ complexHessian f w j k) z v) j k := by
      rw [fderiv_apply hj k, fderiv_apply hcoeff j]
      rfl
    simpa only [← hentry] using hpartial i j k
  calc
    ‖fderiv ℝ (ddbar f) z‖ ≤
        2 * (n : ℝ) ^ 2 * ‖fderiv ℝ (fun w j k ↦ complexHessian f w j k) z‖ :=
      norm_fderiv_ddbar_le_coeffDerivative_local hf hdd
    _ ≤ 2 * (n : ℝ) ^ 2 * (4 * (n : ℝ) * A) :=
      mul_le_mul_of_nonneg_left hmatrix (by positivity)
    _ = 8 * (n : ℝ) ^ 3 * A := by ring

omit [T2Space M] [CompactSpace M] in
private theorem exists_uniform_metric_c3PartialZ_bound
    (ω₀ : KahlerForm n M) (x₀ : M) (K : Set (EuclideanSpace ℂ (Fin n)))
    (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ i j k : Fin n,
      ‖c3PartialZ (fun w ↦ ω₀.metricInChart x₀ w j k) z i‖ ≤ C := by
  classical
  let T := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target
  have hTopen : IsOpen T := isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀
  have hentry : ∀ j k : Fin n,
      ContDiffOn ℝ ∞ (fun z ↦ ω₀.metricInChart x₀ z j k) T := by
    intro j k
    exact (ω₀.contDiffOn_metricInChart x₀ j k)
  have hderiv : ∀ j k : Fin n,
      ContinuousOn (fun z ↦ fderiv ℝ (fun w ↦ ω₀.metricInChart x₀ w j k) z) T := by
    intro j k
    exact (hentry j k).continuousOn_fderiv_of_isOpen hTopen (by simp)
  have hpartial : ∀ i j k : Fin n,
      ContinuousOn (fun z ↦ c3PartialZ (fun w ↦ ω₀.metricInChart x₀ w j k) z i) T := by
    intro i j k
    have hx : ContinuousOn (fun z ↦ fderiv ℝ
        (fun w ↦ ω₀.metricInChart x₀ w j k) z (EuclideanSpace.single i 1)) T :=
      (hderiv j k).clm_apply continuousOn_const
    have hy : ContinuousOn (fun z ↦ fderiv ℝ
        (fun w ↦ ω₀.metricInChart x₀ w j k) z (Complex.I • EuclideanSpace.single i 1)) T :=
      (hderiv j k).clm_apply continuousOn_const
    dsimp [c3PartialZ]
    exact (hx.sub (continuousOn_const.mul hy)).div_const _
  have hb : ∀ i j k : Fin n, ∃ C : ℝ, ∀ z ∈ K,
      ‖c3PartialZ (fun w ↦ ω₀.metricInChart x₀ w j k) z i‖ ≤ C := by
    intro i j k
    exact hK.exists_bound_of_continuousOn ((hpartial i j k).mono hKt)
  let Cijk : Fin n × (Fin n × Fin n) → ℝ := fun p ↦ Classical.choose (hb p.1 p.2.1 p.2.2)
  have hCijk (p : Fin n × (Fin n × Fin n)) : ∀ z ∈ K,
      ‖c3PartialZ (fun w ↦ ω₀.metricInChart x₀ w p.2.1 p.2.2) z p.1‖ ≤ Cijk p :=
    Classical.choose_spec (hb p.1 p.2.1 p.2.2)
  obtain ⟨C, hC⟩ := (Set.finite_range Cijk).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz i j k
  exact (hCijk (i, (j, k)) z hz).trans (le_trans (hC (Set.mem_range_self (i, (j, k)))) (le_max_left _ _))

private theorem psd_entry_normSq_le_local {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (i j : Fin n) :
    Complex.normSq (A i j) ≤ (A i i).re * (A j j).re := by
  by_cases hij : i = j
  · subst j
    have hd := hA.diag_nonneg (i := i)
    have hdre : 0 ≤ (A i i).re := (RCLike.nonneg_iff.mp hd).1
    have him : (A i i).im = 0 := by
      have hh := hA.isHermitian.apply i i
      exact Complex.conj_eq_iff_im.mp (by simpa using hh)
    rw [Complex.normSq_eq_norm_sq]
    have heq : A i i = (A i i).re := by
      apply Complex.ext <;> simp [him]
    rw [heq]
    simp [sq, Real.norm_eq_abs, abs_of_nonneg hdre]
  · let e : Fin 2 → Fin n := ![i, j]
    have hs := hA.submatrix e
    have hd := (RCLike.nonneg_iff.mp hs.det_nonneg).1
    have hdetEq : (A.submatrix e e).det = A i i * A j j - A i j * A j i := by
      rw [Matrix.det_fin_two]
      simp [e, Matrix.submatrix_apply]
    have hdet : 0 ≤ (A i i * A j j - A i j * A j i).re := by
      rw [← hdetEq]
      exact hd
    have hii : A i i = (A i i).re := by
      have hh := hA.isHermitian.apply i i
      have him := Complex.conj_eq_iff_im.mp (by simpa using hh)
      apply Complex.ext <;> simp [him]
    have hjj : A j j = (A j j).re := by
      have hh := hA.isHermitian.apply j j
      have him := Complex.conj_eq_iff_im.mp (by simpa using hh)
      apply Complex.ext <;> simp [him]
    have hji : A j i = star (A i j) := (hA.isHermitian.apply j i).symm
    rw [hii, hjj, hji] at hdet
    simpa [Complex.normSq_eq_norm_sq, Complex.mul_conj, sq] using hdet

private theorem posDef_entry_norm_le_of_diag_norm_le_local {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (C : ℝ) (hC : 0 ≤ C)
    (hdiag : ∀ i : Fin n, ‖A i i‖ ≤ C) (i j : Fin n) : ‖A i j‖ ≤ C := by
  have hi : RCLike.re (A i i) ≤ C := by
    rw [← posDef_diag_norm_eq_re A hA i]
    exact hdiag i
  have hj : RCLike.re (A j j) ≤ C := by
    rw [← posDef_diag_norm_eq_re A hA j]
    exact hdiag j
  have hrj : 0 ≤ (A j j).re := (RCLike.pos_iff.mp hA.diag_pos).1.le
  have hprod : (A i i).re * (A j j).re ≤ C * C := by
    calc
      (A i i).re * (A j j).re ≤ C * (A j j).re := mul_le_mul_of_nonneg_right hi hrj
      _ ≤ C * C := mul_le_mul_of_nonneg_left hj hC
  have hsquare : ‖A i j‖ ^ 2 ≤ C ^ 2 := by
    calc
      ‖A i j‖ ^ 2 ≤ C * C := by
        simpa [Complex.normSq_eq_norm_sq] using
          (psd_entry_normSq_le_local A hA.posSemidef i j).trans hprod
      _ = C ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) hC).1 (by simpa [pow_two] using hsquare)

/-- The coordinate formula for a Kähler connection difference turns its uniform component bound
into an ordinary derivative bound for the complex Hessian on a compact chart piece. -/
private theorem c3PartialZ_hessian_difference {n : ℕ}
    (g0 : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (j k l : Fin n)
    (hdd : DifferentiableAt ℝ (ddbar ψ) z)
    (hg0 : DifferentiableAt ℝ (fun w ↦ g0 w k l) z) :
    c3PartialZ (fun w ↦ (g0 w + complexHessian ψ w) k l) z j -
        c3PartialZ (fun w ↦ g0 w k l) z j =
      c3PartialZ (fun w ↦ complexHessian ψ w k l) z j := by
  have hcoeff := differentiableAt_coeffMatrix_local hdd
  change DifferentiableAt ℝ (fun w j k ↦ complexHessian ψ w j k) z at hcoeff
  have hH : DifferentiableAt ℝ (fun w ↦ complexHessian ψ w k l) z :=
    differentiableAt_pi.mp (differentiableAt_pi.mp hcoeff k) l
  have hsum : DifferentiableAt ℝ
      (fun w ↦ g0 w k l + complexHessian ψ w k l) z := hg0.add hH
  have hEq : (fun w ↦ (g0 w + complexHessian ψ w) k l) =
      (fun w ↦ g0 w k l + complexHessian ψ w k l) := by funext w; simp
  rw [hEq]
  unfold c3PartialZ
  have hadd (e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ g0 w k l + complexHessian ψ w k l) z e =
        fderiv ℝ (fun w ↦ g0 w k l) z e +
          fderiv ℝ (fun w ↦ complexHessian ψ w k l) z e := by
    have hfun : (fun w ↦ g0 w k l + complexHessian ψ w k l) =
        (fun w ↦ g0 w k l) + (fun w ↦ complexHessian ψ w k l) := rfl
    rw [hfun, fderiv_add hg0 hH]
    rfl
  rw [hadd (EuclideanSpace.single j 1), hadd (Complex.I • EuclideanSpace.single j 1)]
  ring

omit [T2Space M] [CompactSpace M] in
/-- The coordinate formula for a Kähler connection difference turns its uniform component bound
into an ordinary derivative bound for the complex Hessian on a compact chart piece. -/
private theorem exists_uniform_fderiv_ddbar_bound_of_c3ConnectionDifference
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hMetric : ∃ D : ℝ, 0 < D ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ D ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ D)
    (x₀ : M) (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target)
    (hn : n ≠ 0)
    (T : ℝ) (hT : ∀ p ∈ S, ∀ z ∈ K, ∀ i j k : Fin n,
      ‖c3ConnectionDifferenceInChart ω₀ p.2 x₀ z i j k‖ ≤ T) :
    ∃ C : ℝ, ∀ p ∈ S, ∀ z ∈ K,
      ‖fderiv ℝ (ddbar (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ C := by
  classical
  let : NeZero n := ⟨hn⟩
  obtain ⟨D, hD, htrace⟩ := hMetric
  obtain ⟨C₀, hC₀⟩ := exists_metricChart_entry_bound_on_compact ω₀ x₀ K hK hKt
  obtain ⟨Cinv, hCinv⟩ := exists_metricInvChart_entry_bound_on_compact ω₀ x₀ K hK hKt
  obtain ⟨Cq0, hCq0, hq0⟩ := exists_uniform_metric_c3PartialZ_bound ω₀ x₀ K hK hKt
  let C₀' := max C₀ 0; let Cinv' := max Cinv 0; let T' := max T 0
  have hC₀' : 0 ≤ C₀' := le_max_right _ _; have hCinv' : 0 ≤ Cinv' := le_max_right _ _
  have hT' : 0 ≤ T' := le_max_right _ _
  let G := D * C₀'
  let R := (n : ℝ) * Cinv' * Cq0
  let A := (n : ℝ) * G * (T' + R) + Cq0
  have hG : 0 ≤ G := mul_nonneg hD.le hC₀'
  have hR : 0 ≤ R := by positivity
  have hA : 0 ≤ A := by positivity
  refine ⟨8 * (n : ℝ) ^ 3 * A, ?_⟩
  intro p hp z hz
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let ψ := p.2 ∘ e.symm
  let g₀f : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x₀ w
  let gφf : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ g₀f w + complexHessian ψ w
  let g₀ := g₀f z
  let g := gφf z
  have hzTarget : z ∈ e.target := hKt hz
  have htargetOpen : IsOpen e.target :=
    isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀
  have hztop : e.target ∈ 𝓝 z := htargetOpen.mem_nhds hzTarget
  have hsol : ω₀.SolvesMongeAmpere p.1 p.2 := (hS p hp).2
  have hpotential : ω₀.IsPotential p.2 := hsol.1
  have hφ_on : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.2 Set.univ :=
    hsol.1.1.contMDiffOn
  have hsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ e.symm e.target :=
    contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₀
  have hψ_md : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ e.target :=
    hφ_on.comp hsymm (fun _ _ ↦ Set.mem_univ _)
  have hψ_chart : ContDiffOn ℝ ∞ ψ e.target := hψ_md.contDiffOn
  have hψ3 : ContDiffAt ℝ 3 ψ z := (hψ_chart.contDiffAt hztop).of_le
    (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top 3).le)
  have horder1 : (1 : ℕ∞ω) ≤ ∞ := by
    exact WithTop.coe_le_coe.mpr (ENat.natCast_lt_top 1).le
  have hddbarOn : ContDiffOn ℝ ∞ (ddbar ψ) e.target :=
    ContDiffOn.ddbar htargetOpen hψ_chart
  have hddbarAt : ContDiffAt ℝ 1 (ddbar ψ) z :=
    (hddbarOn.contDiffAt hztop).of_le horder1
  have hddbar : DifferentiableAt ℝ (ddbar ψ) z :=
    hddbarAt.differentiableAt (by norm_num)
  have hGpos : g.PosDef := by
    change (ω₀.metricInChart x₀ z + complexHessian ψ z).PosDef
    have hpos := (ω₀.perturb p.2 hpotential).posDef_metricInChart x₀ hzTarget
    rw [ω₀.metricInChart_perturb hpotential x₀ hzTarget] at hpos
    exact hpos
  rcases htrace p hp (e.symm z) with ⟨htraceFwd, htraceRev⟩
  have hdiag := c3_chart_perturbed_metric_diagonal_bounds ω₀ p.2 hpotential x₀ hzTarget
    D C₀' Cinv' hD
    (fun i ↦ (hC₀ z hz i i).trans (le_max_left _ _))
    (fun i ↦ (hCinv z hz i i).trans (le_max_left _ _)) htraceFwd htraceRev
  have hGentry (i m : Fin n) : ‖g i m‖ ≤ G := by
    dsimp [G]
    exact posDef_entry_norm_le_of_diag_norm_le_local g hGpos (D * C₀')
      (mul_nonneg hD.le hC₀') (fun a ↦ (hdiag a).1) i m
  have hq0_entry (b c l : Fin n) :
      ‖c3PartialZ (fun w ↦ g₀f w c l) z b‖ ≤ Cq0 :=
    hq0 z hz b c l
  have hg₀smooth (c l : Fin n) :
      ContDiffAt ℝ 1 (fun w ↦ g₀f w c l) z := by
    have hentry : ContDiffOn ℝ ∞ (fun w ↦ ω₀.metricInChart x₀ w c l) e.target :=
      ω₀.contDiffOn_metricInChart x₀ c l
    exact (hentry.contDiffAt hztop).of_le horder1
  have hpartial (b c l : Fin n) :
      ‖c3PartialZ (fun w ↦ complexHessian ψ w c l) z b‖ ≤ A := by
    let q₀ : Fin n → ℂ := fun a ↦ c3PartialZ (fun w ↦ g₀f w c a) z b
    let q : Fin n → ℂ := fun a ↦ c3PartialZ (fun w ↦ gφf w c a) z b
    let Tvec : Fin n → ℂ := fun i ↦
      c3ConnectionDifferenceInChart ω₀ p.2 x₀ z i b c
    let r : Fin n → ℂ := fun i ↦ ∑ a : Fin n, g₀⁻¹ a i * q₀ a
    have hq₀ (a : Fin n) : ‖q₀ a‖ ≤ Cq0 := by
      dsimp [q₀]
      exact hq0_entry b c a
    have hTvec (i : Fin n) : ‖Tvec i‖ ≤ T' := by
      dsimp [Tvec, T']
      exact (hT p hp z hz i b c).trans (le_max_left _ _)
    have hr (i : Fin n) : ‖r i‖ ≤ R := by
      dsimp [r, R]
      calc
        ‖∑ a : Fin n, g₀⁻¹ a i * q₀ a‖ ≤
            ∑ a : Fin n, ‖g₀⁻¹ a i * q₀ a‖ := norm_sum_le _ _
        _ ≤ ∑ a : Fin n, Cinv' * Cq0 := by
          apply Finset.sum_le_sum
          intro a ha
          rw [norm_mul]
          exact mul_le_mul
            ((hCinv z hz a i).trans (le_max_left _ _)) (hq₀ a)
            (norm_nonneg _) hCinv'
        _ = (n : ℝ) * Cinv' * Cq0 := by simp [mul_assoc]
    have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hGpos.isUnit
    have hTidentity (i : Fin n) :
        Tvec i = (∑ a : Fin n, g⁻¹ a i * q a) -
          (∑ a : Fin n, g₀⁻¹ a i * q₀ a) := by
      have hψchart : ψ = p.2 ∘ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).symm := by
        funext w
        dsimp [ψ, e]
      dsimp [Tvec, q, q₀, g, g₀, gφf, g₀f]
      rw [hψchart]
      simp [c3ConnectionDifferenceInChart, c3ChristoffelInChart]
    have hrec (m : Fin n) : q m =
        ∑ i : Fin n, g i m * (Tvec i + r i) := by
      exact c3_recover_complex_derivative_from_connection_difference
        g g₀ q q₀ Tvec hdet m hTidentity
    have hq_bound : ‖q l‖ ≤ (n : ℝ) * G * (T' + R) := by
      simpa only [Fintype.card_fin] using
        c3_norm_recovered_derivative_le g q r Tvec G T' R hG hrec hGentry hTvec hr l
    have hsplit := c3PartialZ_hessian_difference g₀f ψ z b c l hddbar
      ((hg₀smooth c l).differentiableAt (by norm_num))
    have hsplit' : q l - q₀ l = c3PartialZ
        (fun w ↦ complexHessian ψ w c l) z b := by
      simpa [q, q₀, gφf] using hsplit
    calc
      ‖c3PartialZ (fun w ↦ complexHessian ψ w c l) z b‖ = ‖q l - q₀ l‖ := by
        rw [← hsplit']
      _ ≤ ‖q l‖ + ‖q₀ l‖ := norm_sub_le _ _
      _ ≤ (n : ℝ) * G * (T' + R) + Cq0 :=
        add_le_add hq_bound (hq₀ l)
      _ = A := by simp [A]
  have hbound := norm_fderiv_ddbar_le_partialZ_local hψ3 hddbar A hA (by
    intro b c l
    simpa only [c3PartialZ] using hpartial b c l)
  exact hbound

/-- Translate a uniform bound on the Calabi energy and metric equivalence into a uniform
first derivative bound for `i∂∂̄φ` on a compact chart piece. -/
theorem exists_uniform_fderiv_ddbar_bound_of_calabiEnergy (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hMetric : ∃ D : ℝ, 0 < D ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ D ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ D)
    (B : ℝ) (hEnergy : ∀ p ∈ S, ∀ x, calabiEnergy ω₀ p.2 x ≤ B)
    (x₀ : M) (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target) :
    ∃ C : ℝ, ∀ p ∈ S, ∀ z ∈ K,
      ‖fderiv ℝ (ddbar (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ C := by
  classical
  by_cases hK_nonempty : K.Nonempty
  · by_cases hS_nonempty : S.Nonempty
    · by_cases hn : n = 0
      · subst n
        exact ⟨0, by intro p hp z hz; simp⟩
      · obtain ⟨T, hT⟩ := exists_uniform_c3ConnectionDifference_bound_of_calabiEnergy
          ω₀ S hS hMetric B hEnergy x₀ K hK hKt
        exact exists_uniform_fderiv_ddbar_bound_of_c3ConnectionDifference
          ω₀ S hS hMetric x₀ K hK hKt hn T hT
    · exact ⟨0, fun p hp z hz ↦ (hS_nonempty ⟨p, hp⟩).elim⟩
  · exact ⟨0, fun p hp z hz ↦ (hK_nonempty ⟨z, hz⟩).elim⟩

end KahlerForm
