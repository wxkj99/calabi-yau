module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Basic
import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.ChartInvariance.Transition

/-!
# Chart invariance of the Calabi third-order energy

The connection difference is a tensor. Its norm uses the inverse Hermitian metric with the
covariant index order `(g⁻¹)ᵦⱼ (g⁻¹)ᶜₖ`; this makes the displayed coordinate contraction invariant
under holomorphic coordinate changes (including shears). See Székelyhidi, *An Introduction to
Extremal Kähler Metrics*, §3.3, equation (3.13), p. 45, and Yau 1978, §3.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder

namespace KahlerForm

open ChartInvariance

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

private theorem calabiEnergy_clmMatrix_comp {m : ℕ}
    (A B : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    EuclideanSpace.clmMatrix (A.comp B) =
      EuclideanSpace.clmMatrix A * EuclideanSpace.clmMatrix B := by
  classical
  ext i j
  change (A (B (EuclideanSpace.single j 1))).ofLp i =
    ∑ k, (A (EuclideanSpace.single k 1)).ofLp i *
      (B (EuclideanSpace.single j 1)).ofLp k
  have hB : B (EuclideanSpace.single j 1) =
      ∑ k, (B (EuclideanSpace.single j 1)).ofLp k • EuclideanSpace.single k 1 := by
    ext k
    simp [EuclideanSpace.single, Pi.single_apply]
  rw [hB]
  simp [EuclideanSpace.single, Pi.single_apply, mul_comm]

omit [T2Space M] [CompactSpace M] in
private theorem calabiEnergy_chartJacobian_matrix_inverse {x₀ x₁ y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    (let A := EuclideanSpace.clmMatrix
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)
     let B := EuclideanSpace.clmMatrix
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₁ x₀ y)
     A * B = 1 ∧ B * A = 1) := by
  classical
  have hy₀R : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).source := by
    rw [extChartAt_source]
    exact hy₀
  have hy₁R : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).source := by
    rw [extChartAt_source]
    exact hy₁
  have hy₀C : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).source := by
    simpa only [← extChartAt_real_eq] using hy₀R
  have hy₁C : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₁).source := by
    simpa only [← extChartAt_real_eq] using hy₁R
  let C := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y
  let D := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₁ x₀ y
  have hCD : C.comp D = ContinuousLinearMap.id ℂ _ := by
    ext v i
    change (C (D v)).ofLp i = (ContinuousLinearMap.id ℂ _ v).ofLp i
    have hv : C (D v) = v := by
      calc
        C (D v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₁ x₁ y v := by
          exact tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (w := x₁) (x := x₀) (y := x₁) (z := y) (v := v)
            ⟨⟨hy₁C, hy₀C⟩, hy₁C⟩
        _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (x := x₁) (z := y) (v := v) hy₁C
    simpa using congrArg (fun w : EuclideanSpace ℂ (Fin n) => w.ofLp i) hv
  have hDC : D.comp C = ContinuousLinearMap.id ℂ _ := by
    ext v i
    change (D (C v)).ofLp i = (ContinuousLinearMap.id ℂ _ v).ofLp i
    have hv : D (C v) = v := by
      calc
        D (C v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₀ y v := by
          exact tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (w := x₀) (x := x₁) (y := x₀) (z := y) (v := v)
            ⟨⟨hy₀C, hy₁C⟩, hy₀C⟩
        _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (x := x₀) (z := y) (v := v) hy₀C
    simpa using congrArg (fun w : EuclideanSpace ℂ (Fin n) => w.ofLp i) hv
  have hmatCD : EuclideanSpace.clmMatrix C * EuclideanSpace.clmMatrix D = 1 := by
    calc
      _ = EuclideanSpace.clmMatrix (C.comp D) :=
        (calabiEnergy_clmMatrix_comp C D).symm
      _ = EuclideanSpace.clmMatrix (ContinuousLinearMap.id ℂ _) := congrArg
        EuclideanSpace.clmMatrix hCD
      _ = 1 := by
        ext i j
        simp [EuclideanSpace.clmMatrix, Matrix.one_apply]
  have hmatDC : EuclideanSpace.clmMatrix D * EuclideanSpace.clmMatrix C = 1 := by
    calc
      _ = EuclideanSpace.clmMatrix (D.comp C) :=
        (calabiEnergy_clmMatrix_comp D C).symm
      _ = EuclideanSpace.clmMatrix (ContinuousLinearMap.id ℂ _) := congrArg
        EuclideanSpace.clmMatrix hDC
      _ = 1 := by
        ext i j
        simp [EuclideanSpace.clmMatrix, Matrix.one_apply]
  exact ⟨hmatCD, hmatDC⟩

omit [T2Space M] [CompactSpace M] in
private theorem calabiEnergy_chartRep_isOneOne (form : KahlerForm n M) (x : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    (form.toFormField.chartRep x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).IsOneOne := by
  have hyxR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source := by
    rw [extChartAt_source]
    exact hy
  have hyyR : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyxR
  have hyyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyR
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    calc
      B (A v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := by
        exact tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v)
          ⟨⟨hyxC, hyyC⟩, hyxC⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxC
  have hAB : ∀ v, A (B v) = v := by
    intro v
    calc
      A (B v) = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := by
        exact tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v)
          ⟨⟨hyyC, hyxC⟩, hyyC⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyC
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
  have hrep := FormField.chartRep_eq_chartRep_comp (α := form.toFormField)
    (x := x) (x' := y) (z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)
    ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source hyxR)
    (by rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).left_inv hyxR]; exact hyyR)
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      A.restrictScalars ℝ := tangentCoordChange_real_eq ⟨hyxR, hyyR⟩
  have hderiv : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) = A.restrictScalars ℝ := by
    have h := hAreal
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  rw [hderiv] at hrep
  have hcenter : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) =
      extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y := by
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).left_inv hyxR]
  rw [hcenter, FormField.chartRep_self] at hrep
  have hbase := (form.isOneOne y).compContinuousLinearMap AEquiv
  have hAEquiv : (AEquiv : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n)) = A := by
    ext v
    rfl
  rw [hAEquiv] at hbase
  rw [← hrep] at hbase
  exact hbase

omit [T2Space M] [CompactSpace M] in
private theorem calabiEnergy_metric_transition
    (form : KahlerForm n M) (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    form.metricInChart x₀ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) =
      Matrix.transpose (EuclideanSpace.clmMatrix
        (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)) *
        form.metricInChart x₁ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y) *
        (EuclideanSpace.clmMatrix
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)).map star := by
  let c₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let c₁ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁
  let A := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y
  have hy₀' : y ∈ c₀.source := by
    rw [extChartAt_source]
    exact hy₀
  have hy₁' : y ∈ c₁.source := by
    rw [extChartAt_source]
    exact hy₁
  have hz₀ : c₀ y ∈ c₀.target := c₀.map_source hy₀'
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y =
      A.restrictScalars ℝ := by
    exact tangentCoordChange_real_eq ⟨hy₀', hy₁'⟩
  have hderiv : fderiv ℝ (c₁ ∘ c₀.symm) (c₀ y) = A.restrictScalars ℝ := by
    have h := hAreal
    dsimp [A, c₀, c₁] at h ⊢
    rw [tangentCoordChange_def, extChartAt_real_eq] at h
    simpa [ModelWithCorners.range_eq_univ, fderivWithin_univ] using h
  have hrep := FormField.chartRep_eq_chartRep_comp (α := form.toFormField)
    (x := x₀) (x' := x₁) (z := c₀ y) hz₀
    (by rw [c₀.left_inv hy₀']; exact hy₁')
  rw [hderiv] at hrep
  have hcenter : c₁ (c₀.symm (c₀ y)) = c₁ y := by
    rw [c₀.left_inv hy₀']
  rw [hcenter] at hrep
  have hcoeff := congrArg
    (fun α : _ [⋀^Fin 2]→L[ℝ] ℝ => α.coeffMatrix) hrep
  rw [ContinuousAlternatingMap.IsOneOne.coeffMatrix_compContinuousLinearMap
    (calabiEnergy_chartRep_isOneOne form x₁ hy₁) A] at hcoeff
  change (form.toFormField.chartRep x₀ (c₀ y)).coeffMatrix =
    (EuclideanSpace.clmMatrix A).transpose *
      (form.toFormField.chartRep x₁ (c₁ y)).coeffMatrix *
      (EuclideanSpace.clmMatrix A).map star
  exact hcoeff

omit [T2Space M] [CompactSpace M] in
private theorem calabiEnergy_perturbed_metric_transition
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
    (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    (ω₀.perturb φ hφ).metricInChart x₀
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) =
      Matrix.transpose (EuclideanSpace.clmMatrix
        (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)) *
        (ω₀.metricInChart x₁ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y) +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).symm)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y)) *
        (EuclideanSpace.clmMatrix
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)).map star := by
  simpa only [KahlerForm.metricInChart_perturb hφ x₀
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).map_source
        (by rw [extChartAt_source]; exact hy₀)),
    KahlerForm.metricInChart_perturb hφ x₁
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).map_source
        (by rw [extChartAt_source]; exact hy₁))] using
    calabiEnergy_metric_transition (ω₀.perturb φ hφ) x₀ x₁ hy₀ hy₁

private abbrev CalabiEnergyPair (ι : Type*) := ι × ι
private abbrev CalabiEnergyTriple (ι : Type*) := ι × ι × ι
private abbrev CalabiEnergyPairTriple (ι : Type*) :=
  CalabiEnergyPair ι × CalabiEnergyPair ι × CalabiEnergyPair ι

private def calabiEnergyTensorContract {ι : Type*} [Fintype ι]
    (g h : ι → ι → ℂ) (T : ι → ι → ι → ℂ) : ℂ :=
  ∑ x : CalabiEnergyPairTriple ι,
    g x.1.1 x.1.2 * h x.2.1.1 x.2.1.2 * h x.2.2.1 x.2.2.2 *
      T x.1.1 x.2.1.2 x.2.2.2 * star (T x.1.2 x.2.1.1 x.2.2.1)

private def calabiEnergyTensorChange {ι : Type*} [Fintype ι]
    (A B : ι → ι → ℂ) (T : ι → ι → ι → ℂ) (i j k : ι) : ℂ :=
  ∑ p : CalabiEnergyTriple ι,
    B i p.1 * A p.2.1 j * A p.2.2 k * T p.1 p.2.1 p.2.2

private theorem calabiEnergy_sumThreeFactor
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a * g b * h c) =
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) := by
  have hp :
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) =
        ∑ a, ∑ b, ∑ c, f a * g b * h c := by
    calc
      _ = (∑ p : α × β, f p.1 * g p.2) * (∑ c, h c) := by
        rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
      _ = ∑ p : α × β, ∑ c, (f p.1 * g p.2) * h c := by
        rw [Fintype.sum_mul_sum]
      _ = _ := by simp only [Fintype.sum_prod_type]
  exact hp.symm

private theorem calabiEnergy_sumPairTripleFactor {ι : Type*} [Fintype ι]
    (f g h : CalabiEnergyPair ι → ℂ) (d : ℂ) :
    (∑ x : CalabiEnergyPairTriple ι, f x.1 * g x.2.1 * h x.2.2 * d) =
      (∑ x, f x) * (∑ x, g x) * (∑ x, h x) * d := by
  rw [← Finset.sum_mul]
  have hh :
      (∑ x : CalabiEnergyPairTriple ι, f x.1 * g x.2.1 * h x.2.2) =
        (∑ x, f x) * (∑ x, g x) * (∑ x, h x) := by
    simpa only [Fintype.sum_prod_type] using calabiEnergy_sumThreeFactor f g h
  exact congrArg (fun z : ℂ => z * d) hh

private def calabiEnergyPairTripleEquiv (ι : Type*) :
    CalabiEnergyTriple ι × CalabiEnergyTriple ι ≃ CalabiEnergyPairTriple ι where
  toFun v := ((v.1.1, v.2.1), (v.2.2.1, v.1.2.1), (v.2.2.2, v.1.2.2))
  invFun z := ((z.1.1, (z.2.1.2, z.2.2.2)), (z.1.2, (z.2.1.1, z.2.2.1)))
  left_inv := by
    rintro ⟨⟨i, j, k⟩, ⟨a, b, c⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨i, a⟩, ⟨b, j⟩, ⟨c, k⟩⟩
    rfl

private theorem calabiEnergy_tensorContract_reindex {ι : Type*} [Fintype ι]
    (g h : ι → ι → ℂ) (T : ι → ι → ι → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g i a * h b j * h c k * T i j k * star (T a b c)) =
      calabiEnergyTensorContract g h T := by
  unfold calabiEnergyTensorContract
  calc
    _ = ∑ p : CalabiEnergyTriple ι, ∑ q : CalabiEnergyTriple ι,
        g p.1 q.1 * h q.2.1 p.2.1 * h q.2.2 p.2.2 *
          T p.1 p.2.1 p.2.2 * star (T q.1 q.2.1 q.2.2) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ v : CalabiEnergyTriple ι × CalabiEnergyTriple ι,
        g v.1.1 v.2.1 * h v.2.2.1 v.1.2.1 * h v.2.2.2 v.1.2.2 *
          T v.1.1 v.1.2.1 v.1.2.2 * star (T v.2.1 v.2.2.1 v.2.2.2) := by
      rw [← Fintype.sum_prod_type']
    _ = calabiEnergyTensorContract g h T := by
      exact Fintype.sum_equiv (calabiEnergyPairTripleEquiv ι) _ _ (by
        rintro ⟨⟨i, j, k⟩, ⟨a, b, c⟩⟩
        simp [calabiEnergyPairTripleEquiv])

private def calabiEnergyPullbackMetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A G : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A.transpose * G * A.map (starRingEnd ℂ)

private def calabiEnergyPullbackInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  B.map (starRingEnd ℂ) * H * B.transpose

private theorem calabiEnergy_pullbackMetric_inverse {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B G : Matrix ι ι ℂ) (hAB : A * B = 1)
    (hBA : B * A = 1) (hG : IsUnit G.det) :
    (calabiEnergyPullbackMetric A G)⁻¹ = calabiEnergyPullbackInverse B G⁻¹ := by
  classical
  let G₀ := calabiEnergyPullbackMetric A G
  let H₀ := calabiEnergyPullbackInverse B G⁻¹
  have hstar : A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul (f := starRingEnd ℂ), hAB]
    simp
  have hright : G₀ * H₀ = 1 := by
    dsimp [G₀, H₀]
    calc
      _ = A.transpose * G *
          (A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ)) * G⁻¹ * B.transpose := by
        simp only [calabiEnergyPullbackMetric, calabiEnergyPullbackInverse,
          Matrix.mul_assoc]
      _ = A.transpose * G * G⁻¹ * B.transpose := by rw [hstar]; simp
      _ = A.transpose * B.transpose := by
        rw [Matrix.mul_assoc A.transpose G G⁻¹, Matrix.mul_nonsing_inv G hG]
        simp
      _ = (B * A).transpose := by rw [← Matrix.transpose_mul]
      _ = 1 := by rw [hBA]; simp
  have hG₀ : IsUnit G₀.det := by
    apply (Matrix.isUnit_iff_isUnit_det G₀).mp
    exact IsUnit.of_mul_eq_one (b := H₀) hright
  have hcancel := Matrix.nonsing_inv_mul_cancel_left G₀ H₀ hG₀
  rw [hright, Matrix.mul_one] at hcancel
  simpa [G₀, H₀] using hcancel

/-- Pulling back a Hermitian matrix and its inverse gives the output and reversed-covariant
pair-contraction laws used by the tensor norm. -/
private theorem calabiEnergy_pullback_pairContractions {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B G H : Matrix ι ι ℂ) (hAB : A * B = 1) :
    (∀ p s, ∑ x : CalabiEnergyPair ι,
      calabiEnergyPullbackMetric A G x.1 x.2 * B x.1 p * star (B x.2 s) = G p s) ∧
    (∀ q t, ∑ x : CalabiEnergyPair ι,
      calabiEnergyPullbackInverse B H x.1 x.2 * A q x.2 * star (A t x.1) = H t q) := by
  classical
  constructor
  · intro p s
    have hmat : B.transpose * (calabiEnergyPullbackMetric A G *
        B.map (starRingEnd ℂ)) = G := by
      dsimp [calabiEnergyPullbackMetric]
      calc
        _ = (B.transpose * A.transpose) * G *
            (A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ)) := by
          simp only [Matrix.mul_assoc]
        _ = (A * B).transpose * G * (A * B).map (starRingEnd ℂ) := by
          rw [← Matrix.transpose_mul, ← Matrix.map_mul (f := starRingEnd ℂ)]
        _ = G := by rw [hAB]; simp
    have heq := congrArg (fun M : Matrix ι ι ℂ => M p s) hmat
    calc
      _ = (B.transpose * (calabiEnergyPullbackMetric A G *
          B.map (starRingEnd ℂ))) p s := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
          Fintype.sum_prod_type, Finset.mul_sum]
        simp [mul_assoc, mul_comm]
      _ = G p s := heq
  · intro q t
    have hmat : A.map (starRingEnd ℂ) *
        (calabiEnergyPullbackInverse B H * A.transpose) = H := by
      dsimp [calabiEnergyPullbackInverse]
      calc
        _ = (A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ)) * H *
            (B.transpose * A.transpose) := by
          simp only [Matrix.mul_assoc]
        _ = (A * B).map (starRingEnd ℂ) * H * (A * B).transpose := by
          rw [← Matrix.map_mul (f := starRingEnd ℂ), ← Matrix.transpose_mul]
        _ = H := by rw [hAB]; simp
    have heq := congrArg (fun M : Matrix ι ι ℂ => M t q) hmat
    calc
      _ = (A.map (starRingEnd ℂ) *
          (calabiEnergyPullbackInverse B H * A.transpose)) t q := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
          Fintype.sum_prod_type, Finset.mul_sum]
        simp [mul_assoc, mul_comm]
      _ = H t q := heq

omit [T2Space M] [CompactSpace M] in
private theorem calabiEnergy_perturbedChart_pairContractions
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
    (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source) :
    let g₀ : Matrix (Fin n) (Fin n) ℂ :=
      (ω₀.perturb φ hφ).metricInChart x₀
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y)
    let g₁ : Matrix (Fin n) (Fin n) ℂ :=
      (ω₀.perturb φ hφ).metricInChart x₁
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y)
    let A := EuclideanSpace.clmMatrix
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)
    let B := EuclideanSpace.clmMatrix
      (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₁ x₀ y)
    (∀ p s, ∑ x : CalabiEnergyPair (Fin n),
      g₀ x.1 x.2 * B x.1 p * star (B x.2 s) = g₁ p s) ∧
    (∀ q t, ∑ x : CalabiEnergyPair (Fin n),
      g₀⁻¹ x.1 x.2 * A q x.2 * star (A t x.1) = g₁⁻¹ t q) := by
  classical
  let c₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let c₁ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁
  have hy₀' : y ∈ c₀.source := by
    rw [extChartAt_source]
    exact hy₀
  have hy₁' : y ∈ c₁.source := by
    rw [extChartAt_source]
    exact hy₁
  have hz₀ : c₀ y ∈ c₀.target := c₀.map_source hy₀'
  have hz₁ : c₁ y ∈ c₁.target := c₁.map_source hy₁'
  let g₀ : Matrix (Fin n) (Fin n) ℂ :=
    (ω₀.perturb φ hφ).metricInChart x₀ (c₀ y)
  let g₁ : Matrix (Fin n) (Fin n) ℂ :=
    (ω₀.perturb φ hφ).metricInChart x₁ (c₁ y)
  let A := EuclideanSpace.clmMatrix
    (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)
  let B := EuclideanSpace.clmMatrix
    (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₁ x₀ y)
  obtain ⟨hAB, hBA⟩ := calabiEnergy_chartJacobian_matrix_inverse
    (x₀ := x₀) (x₁ := x₁) (y := y) hy₀ hy₁
  have hmetric : g₀ = calabiEnergyPullbackMetric A g₁ := by
    dsimp [g₀, g₁, A, calabiEnergyPullbackMetric]
    rw [KahlerForm.metricInChart_perturb hφ x₀ hz₀,
      KahlerForm.metricInChart_perturb hφ x₁ hz₁]
    have htrans := calabiEnergy_perturbed_metric_transition ω₀ hφ x₀ x₁ hy₀ hy₁
    rw [KahlerForm.metricInChart_perturb hφ x₀ hz₀] at htrans
    exact htrans
  have hg₁ : g₁.PosDef :=
    KahlerForm.posDef_metricInChart (ω₀.perturb φ hφ) x₁ hz₁
  have hdet : IsUnit g₁.det := (Matrix.isUnit_iff_isUnit_det g₁).mp hg₁.isUnit
  have hinv : g₀⁻¹ = calabiEnergyPullbackInverse B g₁⁻¹ := by
    rw [hmetric]
    exact calabiEnergy_pullbackMetric_inverse A B g₁ hAB hBA hdet
  have hpairs := calabiEnergy_pullback_pairContractions A B g₁ g₁⁻¹ hAB
  change (∀ p s, ∑ x : CalabiEnergyPair (Fin n),
    g₀ x.1 x.2 * B x.1 p * star (B x.2 s) = g₁ p s) ∧
    (∀ q t, ∑ x : CalabiEnergyPair (Fin n),
      g₀⁻¹ x.1 x.2 * A q x.2 * star (A t x.1) = g₁⁻¹ t q)
  constructor
  · intro p s
    rw [hmetric]
    exact hpairs.1 p s
  · intro q t
    rw [hinv]
    exact hpairs.2 q t

/-- The metric-weighted tensor contraction is invariant under the tensor and dual-metric
transformation laws. In the covariant slots the dual contraction is reversed: `h₁ t q`. -/
private theorem calabiEnergy_tensorContract_tensorChange {ι : Type*} [Fintype ι]
    (g₀ h₀ g₁ h₁ A B : ι → ι → ℂ) (T : ι → ι → ι → ℂ)
    (hOut : ∀ p s, ∑ x : CalabiEnergyPair ι,
      g₀ x.1 x.2 * B x.1 p * star (B x.2 s) = g₁ p s)
    (hIn : ∀ q t, ∑ x : CalabiEnergyPair ι,
      h₀ x.1 x.2 * A q x.2 * star (A t x.1) = h₁ t q) :
    calabiEnergyTensorContract g₀ h₀ (calabiEnergyTensorChange A B T) =
      calabiEnergyTensorContract g₁ h₁ T := by
  unfold calabiEnergyTensorContract calabiEnergyTensorChange
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro y; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  let f₀ : CalabiEnergyTriple ι → CalabiEnergyTriple ι → CalabiEnergyPair ι → ℂ :=
    fun y x z ↦ g₀ z.1 z.2 * B z.1 y.1 * star (B z.2 x.1)
  let f₁ : CalabiEnergyTriple ι → CalabiEnergyTriple ι → CalabiEnergyPair ι → ℂ :=
    fun y x z ↦ h₀ z.1 z.2 * A y.2.1 z.2 * star (A x.2.1 z.1)
  let f₂ : CalabiEnergyTriple ι → CalabiEnergyTriple ι → CalabiEnergyPair ι → ℂ :=
    fun y x z ↦ h₀ z.1 z.2 * A y.2.2 z.2 * star (A x.2.2 z.1)
  have hfac (y x : CalabiEnergyTriple ι) :
      (∑ z : CalabiEnergyPairTriple ι,
        g₀ z.1.1 z.1.2 * h₀ z.2.1.1 z.2.1.2 * h₀ z.2.2.1 z.2.2.2 *
          (B z.1.1 y.1 * A y.2.1 z.2.1.2 * A y.2.2 z.2.2.2 *
            T y.1 y.2.1 y.2.2) *
          (star (T x.1 x.2.1 x.2.2) *
            (star (A x.2.2 z.2.2.1) *
              (star (A x.2.1 z.2.1.1) * star (B z.1.2 x.1))))) =
        (∑ z, f₀ y x z) * (∑ z, f₁ y x z) * (∑ z, f₂ y x z) *
          (T y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2)) := by
    calc
      _ = ∑ z : CalabiEnergyPairTriple ι,
          f₀ y x z.1 * f₁ y x z.2.1 * f₂ y x z.2.2 *
            (T y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2)) := by
        apply Finset.sum_congr rfl
        intro z hz
        simp only [f₀, f₁, f₂]
        ring
      _ = _ := calabiEnergy_sumPairTripleFactor (f₀ y x) (f₁ y x) (f₂ y x)
        (T y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2))
  simp_rw [hfac, f₀, f₁, f₂, hOut, hIn]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (calabiEnergyPairTripleEquiv ι) _ _ (by
    rintro ⟨⟨i, j, k⟩, ⟨a, b, c⟩⟩
    simp [calabiEnergyPairTripleEquiv]
    ring)

omit [T2Space M] [CompactSpace M] in
private theorem calabiEnergy_inChart_tensorContract
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x₀ : M) (z : EuclideanSpace ℂ (Fin n)) :
    calabiEnergyInChart ω₀ φ x₀ z =
      RCLike.re (calabiEnergyTensorContract
        (fun i a => (ω₀.metricInChart x₀ z +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) z) i a)
        (fun b j => ((ω₀.metricInChart x₀ z +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) z)⁻¹) b j)
        (fun i j k => connectionDifferenceInChart ω₀ φ x₀ z i j k)) := by
  unfold calabiEnergyInChart
  dsimp only
  apply congrArg RCLike.re
  exact calabiEnergy_tensorContract_reindex
    (fun i a => (ω₀.metricInChart x₀ z +
      complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) z) i a)
    (fun b j => ((ω₀.metricInChart x₀ z +
      complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm) z)⁻¹) b j)
    (fun i j k => connectionDifferenceInChart ω₀ φ x₀ z i j k)

omit [T2Space M] [CompactSpace M] in
private theorem calabiEnergy_connectionDifference_transition
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
    (x₀ x₁ : M) {y : M}
    (hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source)
    (hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source)
    (i j k : Fin n) :
    connectionDifferenceInChart ω₀ φ x₀
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀ y) i j k =
      ∑ p : CalabiEnergyTriple (Fin n),
        (EuclideanSpace.clmMatrix
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₁ x₀ y)) i p.1 *
        (EuclideanSpace.clmMatrix
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)) p.2.1 j *
        (EuclideanSpace.clmMatrix
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)) p.2.2 k *
        connectionDifferenceInChart ω₀ φ x₁
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ y) p.1 p.2.1 p.2.2 := by
  classical
  let IC := 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
  let IR := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let c₀ := extChartAt IC x₀
  let c₁ := extChartAt IC x₁
  let F := c₁ ∘ c₀.symm
  let U := c₀.target ∩ c₀.symm ⁻¹' c₁.source
  let V := (extChartAt IR x₁).target
  have hU : IsOpen U := by
    have hsymm : ContinuousOn c₀.symm c₀.target :=
      (contMDiffOn_extChartAt_symm (I := IC) (n := ω) x₀).continuousOn
    have hsrc : IsOpen c₁.source := by
      rw [extChartAt_source]
      exact (chartAt (EuclideanSpace ℂ (Fin n)) x₁).open_source
    exact hsymm.isOpen_inter_preimage (isOpen_extChartAt_target x₀) hsrc
  have hUsrc : U = (c₀.symm ≫ c₁).source := by
    ext w
    simp [U, c₀, c₁, PartialEquiv.trans_source]
  have hF : ContDiffOn ℂ 2 F U := by
    have hFsrc : ContDiffOn ℂ 2 (c₁ ∘ c₀.symm) (c₀.symm ≫ c₁).source := by
      simpa [c₀, c₁] using (contDiffOn_ext_coord_change (I := IC) x₁ x₀)
    have hsubset : U ⊆ (c₀.symm ≫ c₁).source := hUsrc.subset
    change ContDiffOn ℂ 2 (c₁ ∘ c₀.symm) U
    exact hFsrc.mono hsubset
  have hV : IsOpen V := by
    change IsOpen (extChartAt IR x₁).target
    exact isOpen_extChartAt_target x₁
  have hFV : Set.MapsTo F U V := by
    intro w hw
    change w ∈ c₀.target ∧ c₀.symm w ∈ c₁.source at hw
    have htarget : c₁ (c₀.symm w) ∈ c₁.target := c₁.map_source hw.2
    simpa [F, V, c₁, IR, IC, extChartAt_real_eq] using htarget
  have hderiv (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ U) :
      fderiv ℂ F w = tangentCoordChange IC x₀ x₁ (c₀.symm w) := by
    have hc₀ : c₀ (c₀.symm w) = w := c₀.right_inv hw.1
    rw [tangentCoordChange_def]
    change fderiv ℂ (c₁ ∘ c₀.symm) w =
      fderivWithin ℂ (c₁ ∘ c₀.symm) (Set.range IC) (c₀ (c₀.symm w))
    conv_lhs => rw [← hc₀]
    simp [IC, fderivWithin_univ]
  let g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ (ω₀.perturb φ hφ).metricInChart x₁ w
  let g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ (ω₀.perturb φ hφ).metricInChart x₀ w
  let h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x₁ w
  let h' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x₀ w
  have hg : ∀ a b, ContDiffOn ℝ 1 (fun w ↦ g w a b) V := by
    intro a b
    have hreg := (ω₀.perturb φ hφ).contDiffOn_metricInChart x₁ a b
    have hreg' : ContDiffOn ℝ 1
        (fun w ↦ (ω₀.perturb φ hφ).metricInChart x₁ w a b)
        (extChartAt IR x₁).target :=
      hreg.of_le (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))
    simpa [g, V] using hreg'
  have hh : ∀ a b, ContDiffOn ℝ 1 (fun w ↦ h w a b) V := by
    intro a b
    have hreg := ω₀.contDiffOn_metricInChart x₁ a b
    have hreg' : ContDiffOn ℝ 1 (fun w ↦ ω₀.metricInChart x₁ w a b)
        (extChartAt IR x₁).target :=
      hreg.of_le (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top))
    simpa [h, V] using hreg'
  have hchart (a : M) : extChartAt IR a = extChartAt IC a := by simp [IR, IC]
  have hgmetric : ∀ w ∈ U, g' w =
      (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * g (F w) *
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star := by
    intro w hw
    let y := c₀.symm w
    have hy0C : y ∈ c₀.source := c₀.map_target hw.1
    have hy1C : y ∈ c₁.source := hw.2
    have hy0C' : y ∈ (extChartAt IC x₀).source := by simpa [c₀, IC] using hy0C
    have hy1C' : y ∈ (extChartAt IC x₁).source := by simpa [c₁, IC] using hy1C
    have hy0R : y ∈ (extChartAt IR x₀).source := by
      rw [hchart x₀]
      exact hy0C'
    have hy1R : y ∈ (extChartAt IR x₁).source := by
      rw [hchart x₁]
      exact hy1C'
    have hy0 : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
      rw [← extChartAt_source (I := IR)]
      exact hy0R
    have hy1 : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source := by
      rw [← extChartAt_source (I := IR)]
      exact hy1R
    have hcoord0C : c₀ y = w := c₀.right_inv hw.1
    have hcoord0R : extChartAt IR x₀ y = w := by
      rw [hchart x₀]
      exact hcoord0C
    have hcoord1C : F w = c₁ y := rfl
    have hcoord1R : extChartAt IR x₁ y = F w := by
      rw [hchart x₁]
      exact hcoord1C.symm
    have htrans := calabiEnergy_perturbed_metric_transition ω₀ hφ x₀ x₁ hy0 hy1
    rw [hcoord0R, hcoord1R] at htrans
    have hz1R : F w ∈ (extChartAt IR x₁).target := hFV hw
    have hmetric1 := KahlerForm.metricInChart_perturb hφ x₁ hz1R
    rw [← hmetric1] at htrans
    rw [← hderiv w hw] at htrans
    simpa [g, g', F] using htrans
  have hhmetric : ∀ w ∈ U, h' w =
      (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * h (F w) *
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star := by
    intro w hw
    let y := c₀.symm w
    have hy0C : y ∈ c₀.source := c₀.map_target hw.1
    have hy1C : y ∈ c₁.source := hw.2
    have hy0C' : y ∈ (extChartAt IC x₀).source := by simpa [c₀, IC] using hy0C
    have hy1C' : y ∈ (extChartAt IC x₁).source := by simpa [c₁, IC] using hy1C
    have hy0R : y ∈ (extChartAt IR x₀).source := by
      rw [hchart x₀]
      exact hy0C'
    have hy1R : y ∈ (extChartAt IR x₁).source := by
      rw [hchart x₁]
      exact hy1C'
    have hy0 : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
      rw [← extChartAt_source (I := IR)]
      exact hy0R
    have hy1 : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₁).source := by
      rw [← extChartAt_source (I := IR)]
      exact hy1R
    have hcoord0C : c₀ y = w := c₀.right_inv hw.1
    have hcoord0R : extChartAt IR x₀ y = w := by
      rw [hchart x₀]
      exact hcoord0C
    have hcoord1C : F w = c₁ y := rfl
    have hcoord1R : extChartAt IR x₁ y = F w := by
      rw [hchart x₁]
      exact hcoord1C.symm
    have htrans := calabiEnergy_metric_transition ω₀ x₀ x₁ hy0 hy1
    rw [hcoord0R, hcoord1R] at htrans
    rw [← hderiv w hw] at htrans
    simpa [h, h', F] using htrans
  let z₀ := c₀ y
  let z₁ := c₁ y
  have hy₀R : y ∈ (extChartAt IR x₀).source := by
    rw [extChartAt_source]
    exact hy₀
  have hy₁R : y ∈ (extChartAt IR x₁).source := by
    rw [extChartAt_source]
    exact hy₁
  have hy₀C : y ∈ c₀.source := by
    change y ∈ (extChartAt IC x₀).source
    rw [← hchart x₀]
    exact hy₀R
  have hy₁C : y ∈ c₁.source := by
    change y ∈ (extChartAt IC x₁).source
    rw [← hchart x₁]
    exact hy₁R
  have hz₀C : z₀ ∈ c₀.target := c₀.map_source hy₀C
  have hz₁C : z₁ ∈ c₁.target := c₁.map_source hy₁C
  have hz₀R : z₀ ∈ (extChartAt IR x₀).target := by
    rw [hchart x₀]
    exact hz₀C
  have hz₁R : z₁ ∈ (extChartAt IR x₁).target := by
    rw [hchart x₁]
    exact hz₁C
  have hz₀U : z₀ ∈ U := by
    change z₀ ∈ c₀.target ∧ c₀.symm z₀ ∈ c₁.source
    constructor
    · exact c₀.map_source hy₀C
    · rw [c₀.left_inv hy₀C]
      exact hy₁C
  have hc₀symm : c₀.symm z₀ = y := c₀.left_inv hy₀C
  have hFderiv₀ : fderiv ℂ F z₀ = tangentCoordChange IC x₀ x₁ y := by
    simpa [z₀, hc₀symm] using hderiv z₀ hz₀U
  let B := EuclideanSpace.clmMatrix (tangentCoordChange IC x₁ x₀ y)
  obtain ⟨hAB₀, hBA₀⟩ :=
    calabiEnergy_chartJacobian_matrix_inverse (x₀ := x₀) (x₁ := x₁) (y := y) hy₀ hy₁
  have hAB : EuclideanSpace.clmMatrix (fderiv ℂ F z₀) * B = 1 := by
    rw [hFderiv₀]
    exact hAB₀
  have hBA : B * EuclideanSpace.clmMatrix (fderiv ℂ F z₀) = 1 := by
    rw [hFderiv₀]
    exact hBA₀
  have hposg : (g z₁).PosDef := by
    simpa [g, z₁] using
      KahlerForm.posDef_metricInChart (ω₀.perturb φ hφ) x₁ hz₁R
  have hposh : (h z₁).PosDef := by
    simpa [h, z₁] using KahlerForm.posDef_metricInChart ω₀ x₁ hz₁R
  have hFz : F z₀ = z₁ := by
    dsimp [F, z₀, z₁]
    rw [c₀.left_inv hy₀C]
  have hdetg : IsUnit (g (F z₀)).det := by
    simpa [hFz] using (Matrix.isUnit_iff_isUnit_det (g z₁)).mp hposg.isUnit
  have hdeth : IsUnit (h (F z₀)).det := by
    simpa [hFz] using (Matrix.isUnit_iff_isUnit_det (h z₁)).mp hposh.isUnit
  let A := EuclideanSpace.clmMatrix (fderiv ℂ F z₀)
  have hA : A = EuclideanSpace.clmMatrix (tangentCoordChange IC x₀ x₁ y) :=
    congrArg EuclideanSpace.clmMatrix hFderiv₀
  have hcoord₀ : extChartAt IR x₀ y = z₀ := by
    rw [hchart x₀]
  have hcoord₁ : extChartAt IR x₁ y = z₁ := by
    rw [hchart x₁]
  have hpert₀ := calabiEnergy_c3Christoffel_perturb ω₀ hφ x₀ z₀ hz₀R i j k
  have hpert₁ (a b c : Fin n) :
      christoffelInChart
          (fun w ↦ ω₀.metricInChart x₁ w +
            complexHessian (φ ∘ (extChartAt IR x₁).symm) w) z₁ a b c =
        christoffelInChart g z₁ a b c := by
    exact calabiEnergy_c3Christoffel_perturb ω₀ hφ x₁ z₁ hz₁R a b c
  have hleft : connectionDifferenceInChart ω₀ φ x₀
      (extChartAt IR x₀ y) i j k =
      (∑ l, (g' z₀)⁻¹ l i * wirtingerDerivInChart (fun w ↦ g' w k l) z₀ j) -
        ∑ l, (h' z₀)⁻¹ l i * wirtingerDerivInChart (fun w ↦ h' w k l) z₀ j := by
    rw [hcoord₀]
    change christoffelInChart
        (fun w ↦ ω₀.metricInChart x₀ w +
          complexHessian (φ ∘ (extChartAt IR x₀).symm) w) z₀ i j k -
      christoffelInChart (fun w ↦ ω₀.metricInChart x₀ w) z₀ i j k = _
    rw [hpert₀]
    rfl
  have hgen := calabiEnergy_connectionDifference_transition_generic F g h g' h'
    U V hU hV hF hg hh hFV hgmetric hhmetric z₀ hz₀U B hAB hBA hdetg hdeth i j k
  have hconn₁ (a b c : Fin n) :
      connectionDifferenceInChart ω₀ φ x₁
          (extChartAt IR x₁ y) a b c =
        christoffelInChart g z₁ a b c - christoffelInChart h z₁ a b c := by
    rw [hcoord₁]
    change christoffelInChart
        (fun w ↦ ω₀.metricInChart x₁ w +
          complexHessian (φ ∘ (extChartAt IR x₁).symm) w) z₁ a b c -
      christoffelInChart (fun w ↦ ω₀.metricInChart x₁ w) z₁ a b c = _
    rw [hpert₁ a b c]
  have hright :
      (∑ p : CalabiEnergyTriple (Fin n),
        B i p.1 * A p.2.1 j * A p.2.2 k *
          connectionDifferenceInChart ω₀ φ x₁
            (extChartAt IR x₁ y) p.1 p.2.1 p.2.2) =
        ∑ p, ∑ q, ∑ r, B i p * A q j * A r k *
          ((∑ s, (g (F z₀))⁻¹ s p * wirtingerDerivInChart (fun w ↦ g w r s) (F z₀) q) -
            ∑ s, (h (F z₀))⁻¹ s p * wirtingerDerivInChart (fun w ↦ h w r s) (F z₀) q) := by
    simp_rw [hconn₁, hFz]
    simp only [christoffelInChart]
    simp only [Fintype.sum_prod_type]
  have hAconv :
      (∑ p : CalabiEnergyTriple (Fin n),
        B i p.1 *
          (EuclideanSpace.clmMatrix
            (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)) p.2.1 j *
          (EuclideanSpace.clmMatrix
            (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₁ y)) p.2.2 k *
          connectionDifferenceInChart ω₀ φ x₁
            (extChartAt IR x₁ y) p.1 p.2.1 p.2.2) =
      ∑ p : CalabiEnergyTriple (Fin n),
        B i p.1 * A p.2.1 j * A p.2.2 k *
          connectionDifferenceInChart ω₀ φ x₁
            (extChartAt IR x₁ y) p.1 p.2.1 p.2.2 := by
    rw [← hA]
  calc
    _ = (∑ l, (g' z₀)⁻¹ l i * wirtingerDerivInChart (fun w ↦ g' w k l) z₀ j) -
        ∑ l, (h' z₀)⁻¹ l i * wirtingerDerivInChart (fun w ↦ h' w k l) z₀ j := hleft
    _ = ∑ p, ∑ q, ∑ r, B i p * A q j * A r k *
        ((∑ s, (g (F z₀))⁻¹ s p * wirtingerDerivInChart (fun w ↦ g w r s) (F z₀) q) -
          ∑ s, (h (F z₀))⁻¹ s p * wirtingerDerivInChart (fun w ↦ h w r s) (F z₀) q) := hgen
    _ = ∑ p : CalabiEnergyTriple (Fin n),
        B i p.1 * A p.2.1 j * A p.2.2 k *
          connectionDifferenceInChart ω₀ φ x₁
            (extChartAt IR x₁ y) p.1 p.2.1 p.2.2 := hright.symm
    _ = _ := hAconv.symm

omit [T2Space M] [CompactSpace M] in
/-- The chartwise Calabi energy agrees with its global value at every point of the chart. -/
theorem calabiEnergy_chartFormula (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsPotential φ) :
    ∀ x₀ z, z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target →
      calabiEnergy ω₀ φ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm z) =
        calabiEnergyInChart ω₀ φ x₀ z := by
  intro x₀ z hz
  let c₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀
  let y := c₀.symm z
  have hy₀R : y ∈ c₀.source := c₀.map_target hz
  have hy₀ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x₀).source := by
    simpa [c₀, extChartAt_source] using hy₀R
  have hcenter : c₀ y = z := c₀.right_inv hz
  have hy₁ : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) y).source := by
    have hy₁R : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
      mem_extChartAt_source y
    rw [extChartAt_source] at hy₁R
    exact hy₁R
  let c₁ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  have hy₁R : y ∈ c₁.source := mem_extChartAt_source y
  have hz₀ : c₀ y ∈ c₀.target := c₀.map_source hy₀R
  have hz₁ : c₁ y ∈ c₁.target := c₁.map_source hy₁R
  let g₀ : Matrix (Fin n) (Fin n) ℂ :=
    (ω₀.perturb φ hφ).metricInChart x₀ (c₀ y)
  let g₁ : Matrix (Fin n) (Fin n) ℂ :=
    (ω₀.perturb φ hφ).metricInChart y (c₁ y)
  let A := EuclideanSpace.clmMatrix
    (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ y y)
  let B := EuclideanSpace.clmMatrix
    (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x₀ y)
  let g₀Fun : Fin n → Fin n → ℂ := fun i a => g₀ i a
  let g₁Fun : Fin n → Fin n → ℂ := fun i a => g₁ i a
  let h₀Fun : Fin n → Fin n → ℂ := fun b j => (g₀⁻¹) b j
  let h₁Fun : Fin n → Fin n → ℂ := fun b j => (g₁⁻¹) b j
  obtain ⟨hOut, hIn⟩ :=
    calabiEnergy_perturbedChart_pairContractions ω₀ hφ x₀ y hy₀ hy₁
  let T₀ : Fin n → Fin n → Fin n → ℂ := fun i j k =>
    connectionDifferenceInChart ω₀ φ x₀ (c₀ y) i j k
  let T₁ : Fin n → Fin n → Fin n → ℂ := fun i j k =>
    connectionDifferenceInChart ω₀ φ y (c₁ y) i j k
  have hOutFun : ∀ p s, ∑ x : CalabiEnergyPair (Fin n),
      g₀Fun x.1 x.2 * B x.1 p * star (B x.2 s) = g₁Fun p s := by
    intro p s
    simpa [g₀Fun, g₁Fun, g₀, g₁, A, B, c₀, c₁, extChartAt_real_eq] using hOut p s
  have hInFun : ∀ q t, ∑ x : CalabiEnergyPair (Fin n),
      h₀Fun x.1 x.2 * A q x.2 * star (A t x.1) = h₁Fun t q := by
    intro q t
    simpa [h₀Fun, h₁Fun, g₀, g₁, A, B, c₀, c₁, extChartAt_real_eq] using hIn q t
  have hT : T₀ = calabiEnergyTensorChange A B T₁ := by
    funext i j k
    exact calabiEnergy_connectionDifference_transition ω₀ hφ x₀ y hy₀ hy₁ i j k
  have hcontract :
      calabiEnergyTensorContract g₀Fun h₀Fun T₀ =
        calabiEnergyTensorContract g₁Fun h₁Fun T₁ := by
    rw [hT]
    exact calabiEnergy_tensorContract_tensorChange
      g₀Fun h₀Fun g₁Fun h₁Fun A B T₁ hOutFun hInFun
  have hBase₀ : g₀ = ω₀.metricInChart x₀ (c₀ y) +
      complexHessian (φ ∘ c₀.symm) (c₀ y) :=
    KahlerForm.metricInChart_perturb hφ x₀ hz₀
  have hBase₁ : g₁ = ω₀.metricInChart y (c₁ y) +
      complexHessian (φ ∘ c₁.symm) (c₁ y) :=
    KahlerForm.metricInChart_perturb hφ y hz₁
  change calabiEnergyInChart ω₀ φ y (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y) =
    calabiEnergyInChart ω₀ φ x₀ z
  rw [← hcenter]
  rw [calabiEnergy_inChart_tensorContract ω₀ φ y (c₁ y),
    calabiEnergy_inChart_tensorContract ω₀ φ x₀ (c₀ y)]
  apply congrArg RCLike.re
  rw [← hBase₁, ← hBase₀]
  exact hcontract.symm

end KahlerForm
