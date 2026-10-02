module

public import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.Basic
public import CalabiYau.Geometry.Kahler.Volume
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TopFormIntegral.FlatAbsoluteCoefficient
import CalabiYau.Mathlib.LinearAlgebra.Matrix.Realification
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.HodgeRiemann.PrimitiveDiagonal
import CalabiYau.Geometry.Complex.DDBar.ScalarPotential.TraceWedge.PullbackNaturality

/-!
# Actual top-form coefficients versus Kähler chart density

Wells, *Differential Analysis on Complex Manifolds*, V §1, pp. 157–159,
identifies `ωⁿ/n!` with positive volume. Under the project's convention
`ω = i ∑ gⱼₖ dzⱼ ∧ dbarzₖ`, its interleaved real coefficient is `2ⁿ Re(det g)`.
The standing positivity is supplied by the actual `KahlerForm`, not by an
extra assumed volume or Stokes theorem. The second theorem cancels the signed
Jacobian in the numerator and denominator of a general real top form.
-/

open ContinuousAlternatingMap
open Matrix

@[expose] public section

open scoped Manifold ContDiff
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- The normalized actual Kähler wedge has precisely the existing positive chart density.
This requires the alternating-form determinant expansion; it is not definitional. -/
theorem topFormVolume_chartCoeff (ω₀ : KahlerForm n M) (c : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).target) :
    topFormCoeff (ω₀.topFormVolume.chartRep c z) = ω₀.volumeDensityInChart c z := by
  have hChartClmMatrixEqToMatrixBasisFun : ∀ {n : ℕ}
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      EuclideanSpace.clmMatrix A =
        LinearMap.toMatrix ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)
          ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis) A.toLinearMap := by
    intro n A
    ext i j
    rfl
  have hChartClmDetRestrictScalarsEqNormSq : ∀ {n : ℕ}
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      (A.restrictScalars ℝ).det = Complex.normSq (EuclideanSpace.clmMatrix A).det := by
    intro n A
    let bC : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    let bR := Complex.basisOneI.smulTower' bC
    have hclm : LinearMap.toMatrix bC bC A.toLinearMap = EuclideanSpace.clmMatrix A := by
      exact (hChartClmMatrixEqToMatrixBasisFun (n := n) A).symm
    have hreal : LinearMap.toMatrix bR bR (A.toLinearMap.restrictScalars ℝ) =
        (EuclideanSpace.clmMatrix A).realify := by
      rw [LinearMap.restrictScalars_toMatrix]
      rw [hclm]
      ext ⟨i, a⟩ ⟨j, b⟩
      rw [Matrix.comp_apply, Matrix.realify_apply]
      simp only [Matrix.map_apply, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
        Complex.coe_basisOneI, Complex.coe_basisOneI_repr, Algebra.coe_lmul_eq_mul,
        LinearMap.mul_apply']
      fin_cases a <;> fin_cases b <;> norm_num
    change (A.toLinearMap.restrictScalars ℝ).det = _
    calc
      (A.toLinearMap.restrictScalars ℝ).det =
          Matrix.det (LinearMap.toMatrix bR bR (A.toLinearMap.restrictScalars ℝ)) := by
        rw [LinearMap.det_toMatrix]
      _ = (EuclideanSpace.clmMatrix A).realify.det := congrArg Matrix.det hreal
      _ = Complex.normSq (EuclideanSpace.clmMatrix A).det := Matrix.det_realify _
  have hPositiveWedgeTopFormCoeffEqDetOfFlatCount : ∀ {n : ℕ}
      (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (hα : α.IsPositive)
      (hflat : topFormCoeff (wedgePow (omegaFlat (n := n)) n) =
        (n.factorial : ℝ) * 2 ^ n),
      topFormCoeff ((n.factorial : ℝ)⁻¹ • wedgePow α n) =
        2 ^ n * RCLike.re α.coeffMatrix.det := by
    intro n α hα hflat
    have hstd : topFormCoeff ((n.factorial : ℝ)⁻¹ •
        wedgePow (omegaFlat (n := n)) n) = 2 ^ n := by
      change (n.factorial : ℝ)⁻¹ *
        topFormCoeff (wedgePow (omegaFlat (n := n)) n) = 2 ^ n
      rw [hflat]
      have hn : (n.factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero n
      field_simp
    obtain ⟨A, d, hαI, _⟩ :=
      exists_normalFrame_diagonal_equiv α α hα hα.1
    let α' := α.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)
    have hα' : α'.IsOneOne := hα.1.compContinuousLinearMap A.toContinuousLinearMap
    have hα'eq : α' = omegaFlat := omegaFlat_eq_of_coeffMatrix_one α' hα' hαI
    have hpull :
        ((n.factorial : ℝ)⁻¹ • wedgePow α n).compContinuousLinearMap
          (A.toContinuousLinearMap.restrictScalars ℝ) =
        (n.factorial : ℝ)⁻¹ • wedgePow (omegaFlat (n := n)) n := by
      rw [ContinuousAlternatingMap.compContinuousLinearMap_smul, wedgePow_pullback]
      change (n.factorial : ℝ)⁻¹ • wedgePow α' n = _
      rw [hα'eq]
    have hcoeffPull := congrArg topFormCoeff hpull
    rw [topFormCoeff_compContinuousLinearMap] at hcoeffPull
    let B := EuclideanSpace.clmMatrix
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    have hframe : Bᵀ * α.coeffMatrix * B.map star = 1 := by
      have hcomp := hα.1.coeffMatrix_compContinuousLinearMap
        (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      change Bᵀ * α.coeffMatrix * B.map star = 1
      rw [← hcomp]
      exact hαI
    have hdetFrame := congrArg Matrix.det hframe
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdetFrame
    have hBstar : (B.map star).det = star B.det := by
      exact ((starRingEnd ℂ).map_det B).symm
    rw [hBstar] at hdetFrame
    simp only [Matrix.det_one] at hdetFrame
    have hdetFrame' : (B.det * star B.det) * α.coeffMatrix.det = 1 := by
      calc
        (B.det * star B.det) * α.coeffMatrix.det =
            B.det * α.coeffMatrix.det * star B.det := by ring
        _ = 1 := hdetFrame
    have hnorm : B.det * star B.det = (Complex.normSq B.det : ℂ) :=
      Complex.mul_conj B.det
    have hdetFrame'' : (Complex.normSq B.det : ℂ) * α.coeffMatrix.det = 1 := by
      rw [← hnorm]
      exact hdetFrame'
    have hdetReal : (A.toContinuousLinearMap.restrictScalars ℝ).det =
        Complex.normSq B.det :=
      hChartClmDetRestrictScalarsEqNormSq
        (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    have hdetRe : RCLike.re α.coeffMatrix.det *
        (A.toContinuousLinearMap.restrictScalars ℝ).det = 1 := by
      have h := congrArg Complex.re hdetFrame''
      have h' : Complex.normSq B.det * Complex.re α.coeffMatrix.det = 1 := by
        simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero, Complex.one_re] using h
      rw [hdetReal]
      change Complex.re α.coeffMatrix.det * Complex.normSq B.det = 1
      calc
        Complex.re α.coeffMatrix.det * Complex.normSq B.det =
            Complex.normSq B.det * Complex.re α.coeffMatrix.det := by ring
        _ = 1 := h'
    rw [← hcoeffPull] at hstd
    change (A.toContinuousLinearMap.restrictScalars ℝ).det *
        topFormCoeff ((n.factorial : ℝ)⁻¹ • wedgePow α n) = 2 ^ n at hstd
    calc
      topFormCoeff ((n.factorial : ℝ)⁻¹ • wedgePow α n) =
          topFormCoeff ((n.factorial : ℝ)⁻¹ • wedgePow α n) * 1 := by ring
      _ = topFormCoeff ((n.factorial : ℝ)⁻¹ • wedgePow α n) *
          (RCLike.re α.coeffMatrix.det *
            (A.toContinuousLinearMap.restrictScalars ℝ).det) := by rw [hdetRe]
      _ = ((A.toContinuousLinearMap.restrictScalars ℝ).det *
          topFormCoeff ((n.factorial : ℝ)⁻¹ • wedgePow α n)) *
          RCLike.re α.coeffMatrix.det := by ring
      _ = 2 ^ n * RCLike.re α.coeffMatrix.det := by rw [hstd]
  have hActualChartDensityOfFlatCount
      (hflat : ∀ k : ℕ,
        topFormCoeff (wedgePow (omegaFlat (n := k)) k) = (k.factorial : ℝ) * 2 ^ k) :
      topFormCoeff (ω₀.topFormVolume.chartRep c z) = ω₀.volumeDensityInChart c z := by
    let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).symm z
    let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) c y y
    have hyc : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).source :=
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).map_target hz
    have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c y y =
        A.restrictScalars ℝ := tangentCoordChange_real_eq ⟨hyc, mem_extChartAt_source y⟩
    have htop : topFormCoeff (ω₀.topFormVolume.chartRep c z) =
        (A.restrictScalars ℝ).det *
          topFormCoeff ((n.factorial : ℝ)⁻¹ • wedgePow (ω₀ y) n) := by
      change topFormCoeff ((ω₀.topFormVolume y).compContinuousLinearMap
        (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c y y)) = _
      rw [hAreal, topFormCoeff_compContinuousLinearMap]
      rfl
    have hmetric : ω₀.metricInChart c z =
        (EuclideanSpace.clmMatrix A)ᵀ * (ω₀ y).coeffMatrix *
          (EuclideanSpace.clmMatrix A).map star := by
      change ((ω₀ y).compContinuousLinearMap
        (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c y y)).coeffMatrix = _
      rw [hAreal]
      exact (ω₀.isOneOne y).coeffMatrix_compContinuousLinearMap A
    have hstar : ((EuclideanSpace.clmMatrix A).map star).det =
        star (EuclideanSpace.clmMatrix A).det := by
      exact ((starRingEnd ℂ).map_det (EuclideanSpace.clmMatrix A)).symm
    have hdet : (ω₀.metricInChart c z).det =
        (Complex.normSq (EuclideanSpace.clmMatrix A).det : ℂ) *
          (ω₀ y).coeffMatrix.det := by
      rw [hmetric, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hstar]
      rw [← Complex.mul_conj]
      change (EuclideanSpace.clmMatrix A).det * (ω₀ y).coeffMatrix.det *
          star (EuclideanSpace.clmMatrix A).det =
        ((EuclideanSpace.clmMatrix A).det * star (EuclideanSpace.clmMatrix A).det) *
          (ω₀ y).coeffMatrix.det
      ring
    have hre := congrArg Complex.re hdet
    rw [htop, hPositiveWedgeTopFormCoeffEqDetOfFlatCount _ (ω₀.isPositive y)
        (hflat n), hChartClmDetRestrictScalarsEqNormSq]
    change _ = 2 ^ n * Complex.re (ω₀.metricInChart c z).det
    rw [hre]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change Complex.normSq (EuclideanSpace.clmMatrix A).det *
        (2 ^ n * Complex.re (ω₀ y).coeffMatrix.det) =
      2 ^ n * (Complex.normSq (EuclideanSpace.clmMatrix A).det *
        Complex.re (ω₀ y).coeffMatrix.det)
    ring
  by_cases hn0 : n = 0
  · subst n
    let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin 0)) c).symm z
    let A := tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin 0)) c y y
    have hvol : ω₀.topFormVolume y =
        constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin 0)) (Fin 0) (1 : ℝ) := by
      change (Nat.factorial 0 : ℝ)⁻¹ • ContinuousAlternatingMap.wedgePow (ω₀ y) 0 = _
      change (Nat.factorial 0 : ℝ)⁻¹ •
        constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin 0)) (Fin 0) (1 : ℝ) = _
      norm_num
    have hcomp : topFormCoeff
        ((constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin 0)) (Fin 0) (1 : ℝ)).compContinuousLinearMap A) = 1 := by
      change 1 = 1
      rfl
    change topFormCoeff ((ω₀.topFormVolume y).compContinuousLinearMap A) =
      2 ^ 0 * RCLike.re (ω₀.metricInChart c z).det
    rw [hvol, hcomp, Matrix.det_fin_zero]
    norm_num
  · by_cases hn1 : n = 1
    · subst n
      let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) c).symm z
      let A := tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) c y y
      have hpow : ContinuousAlternatingMap.wedgePow (ω₀ y) 1 = ω₀ y := by
        change ((ω₀ y ∧[ℝ] constOfIsEmpty ℝ (EuclideanSpace ℂ (Fin 1)) (Fin 0) (1 : ℝ)).domDomCongr
          (Fin.castOrderIso (by decide : 2 + 2 * 0 = 2 * (0 + 1)))) = ω₀ y
        rw [ContinuousAlternatingMap.wedge_right_unit]
        ext v
        rfl
      have htop : ω₀.topFormVolume y = (1 : ℝ)⁻¹ • ω₀ y := by
        change (Nat.factorial 1 : ℝ)⁻¹ • ContinuousAlternatingMap.wedgePow (ω₀ y) 1 = _
        rw [hpow]
        norm_num
      have hchart : ω₀.topFormVolume.chartRep c z = ω₀.toFormField.chartRep c z := by
        change (ω₀.topFormVolume y).compContinuousLinearMap A =
          (ω₀.toFormField y).compContinuousLinearMap A
        rw [htop]
        norm_num
      rw [hchart]
      change topFormCoeff (ω₀.toFormField.chartRep c z) =
        2 ^ 1 * RCLike.re ((ω₀.toFormField.chartRep c z).coeffMatrix).det
      have hcoeff (α : EuclideanSpace ℂ (Fin 1) [⋀^Fin 2]→L[ℝ] ℝ) :
          topFormCoeff α = 2 * RCLike.re (α.coeffMatrix).det := by
        let e : EuclideanSpace ℂ (Fin 1) := EuclideanSpace.single 0 1
        have h0 : ContinuousAlternatingMap.complexInterleavedBasis 1 0 =
            EuclideanSpace.single 0 (1 : ℂ) := by
          change (((Complex.basisOneI.smulTower'
              ((EuclideanSpace.basisFun (Fin 1) ℂ).toBasis)).reindex
              ((finProdFinEquiv (m := 1) (n := 2)).trans
                (Equiv.cast (congrArg Fin (by decide : 1 * 2 = 2 * 1))))) 0) = _
          rw [Module.Basis.reindex_apply]
          let E : Fin 1 × Fin 2 ≃ Fin 2 :=
            (finProdFinEquiv (m := 1) (n := 2)).trans
              (Equiv.cast (congrArg Fin (by decide : 1 * 2 = 2 * 1)))
          have hforward : E (0, 0) = 0 := by decide
          have hE : E.symm 0 = (0, 0) := by
            apply E.injective
            rw [Equiv.apply_symm_apply, hforward]
          rw [hE, Module.Basis.smulTower'_apply]
          rw [EuclideanSpace.basisFun_toBasis, PiLp.basisFun_apply]
          simp
        have h1 : ContinuousAlternatingMap.complexInterleavedBasis 1 1 =
            Complex.I • EuclideanSpace.single 0 (1 : ℂ) := by
          change (((Complex.basisOneI.smulTower'
              ((EuclideanSpace.basisFun (Fin 1) ℂ).toBasis)).reindex
              ((finProdFinEquiv (m := 1) (n := 2)).trans
                (Equiv.cast (congrArg Fin (by decide : 1 * 2 = 2 * 1))))) 1) = _
          rw [Module.Basis.reindex_apply]
          let E : Fin 1 × Fin 2 ≃ Fin 2 :=
            (finProdFinEquiv (m := 1) (n := 2)).trans
              (Equiv.cast (congrArg Fin (by decide : 1 * 2 = 2 * 1)))
          have hforward : E (0, 1) = 1 := by decide
          have hE : E.symm 1 = (0, 1) := by
            apply E.injective
            rw [Equiv.apply_symm_apply, hforward]
          rw [hE, Module.Basis.smulTower'_apply]
          rw [EuclideanSpace.basisFun_toBasis, PiLp.basisFun_apply]
          simp
        have hb : ContinuousAlternatingMap.complexInterleavedBasis 1 = ![e, Complex.I • e] := by
          funext i
          fin_cases i
          · simpa [e] using h0
          · simpa [e] using h1
        change α (ContinuousAlternatingMap.complexInterleavedBasis 1) = _
        rw [hb]
        simp [ContinuousAlternatingMap.coeffMatrix, e]
        ring
      rw [hcoeff]
      norm_num
    · exact hActualChartDensityOfFlatCount
        (fun k => ContinuousAlternatingMap.omegaFlat_topFormCoeff k)

/-- Same-centre target covariance of the signed ratio. Its denominator is evaluated
at the inverse-chart point, never at the chart centre. No smoothness of `Θ` is needed. -/
theorem topFormCoeff_chartRep_eq_density_mul (ω₀ : KahlerForm n M)
    (Θ : FormField (EuclideanSpace ℂ (Fin n)) M (2 * n)) (c : M)
    {z : EuclideanSpace ℂ (Fin n)}
    (_hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).target) :
    topFormCoeff (Θ.chartRep c z) =
      ω₀.signedTopFormDensity Θ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).symm z) *
        topFormCoeff (ω₀.topFormVolume.chartRep c z) := by
  let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c).symm z
  let A := tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) c y y
  have hpos : 0 < topFormCoeff (ω₀.topFormVolume y) := by
    rw [← FormField.chartRep_self ω₀.topFormVolume y,
      ω₀.topFormVolume_chartCoeff y (mem_extChartAt_target y)]
    rw [volumeDensityInChart]
    exact mul_pos (by positivity)
      (RCLike.pos_iff.mp (ω₀.posDef_metricInChart y (mem_extChartAt_target y)).det_pos).1
  have hnum : topFormCoeff (Θ.chartRep c z) = A.det * topFormCoeff (Θ y) := by
    change topFormCoeff ((Θ y).compContinuousLinearMap A) = _
    rw [topFormCoeff_compContinuousLinearMap]
  have hden : topFormCoeff (ω₀.topFormVolume.chartRep c z) =
      A.det * topFormCoeff (ω₀.topFormVolume y) := by
    change topFormCoeff ((ω₀.topFormVolume y).compContinuousLinearMap A) = _
    rw [topFormCoeff_compContinuousLinearMap]
  change topFormCoeff (Θ.chartRep c z) =
    (topFormCoeff (Θ y) / topFormCoeff (ω₀.topFormVolume y)) *
      topFormCoeff (ω₀.topFormVolume.chartRep c z)
  rw [hnum, hden]
  have hden_ne : topFormCoeff (ω₀.topFormVolume y) ≠ 0 := ne_of_gt hpos
  field_simp

end KahlerForm
