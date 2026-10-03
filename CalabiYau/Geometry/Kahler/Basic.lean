module

public import CalabiYau.Geometry.Complex.Forms.ComplexHessian
public import CalabiYau.Geometry.Manifold.Bundle.TangentSpace

/-!
# Kähler forms and Kähler potentials

A **Kähler form** on a complex manifold `M` of complex dimension `n` is a smooth real `2`-form
field which is of type `(1,1)`, positive and closed. Its coefficient matrix in the chart at `x`,
`KahlerForm.metricInChart ω x z = (g_{jk̄}(z))`, is the local Hermitian metric,
`ω = i ∑ g_{jk̄} dzⱼ ∧ dz̄ₖ`. The associated Riemannian metric is `g(u, v) = ω(u, Jv)`.

A smooth function `φ` is a **Kähler potential** for `ω` (`KahlerForm.IsPotential`) if
`ω + i∂∂̄φ` is again positive; `ω.perturb φ hφ` is the Kähler form `ω_φ = ω + i∂∂̄φ`. On a compact
manifold, the Kähler forms `ω_φ` are exactly the Kähler forms in the class `[ω]` (by the
`∂∂̄`-lemma, `CalabiYau.Geometry.Complex.DDBar.Basic`).

## Definitions and properties

* `KahlerForm n M`, with coercion to `M → (ℂⁿ [⋀^Fin 2]→L[ℝ] ℝ)`;
* `KahlerForm.metricInChart`: the local metric `g_{jk̄}`;
* `KahlerForm.innerAt` and `KahlerForm.innerProductCoreAt`: the pointwise real inner product
  associated to a Kähler form;
* `KahlerForm.IsPotential`, `KahlerForm.perturb`.
-/

@[expose] public section

open scoped Manifold ContDiff
open Set ContinuousAlternatingMap

/-- A Kähler form on a complex manifold of complex dimension `n`: a smooth, closed, positive real
`(1,1)`-form field. -/
structure KahlerForm (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] where
  /-- The underlying real `2`-form field. -/
  toFormField : FormField (EuclideanSpace ℂ (Fin n)) M 2
  isSmooth' : toFormField.IsSmooth
  isPositive' : toFormField.IsPositive
  isClosed' : toFormField.IsClosed

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

instance : CoeFun (KahlerForm n M) fun _ ↦ M → EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ :=
  ⟨fun ω₀ ↦ ω₀.toFormField⟩

variable (ω₀ : KahlerForm n M)

@[simp]
theorem coe_toFormField : (ω₀.toFormField : M → _) = ω₀ := rfl

@[ext]
theorem ext {ω₀ ω₁ : KahlerForm n M} (h : ∀ x, ω₀ x = ω₁ x) : ω₀ = ω₁ := by
  cases ω₀ with
  | mk f hf hp hc =>
    cases ω₁ with
    | mk g hg hq hcl =>
      have hfg : f = g := by
        funext x
        exact h x
      subst g
      congr

theorem isSmooth : ω₀.toFormField.IsSmooth := ω₀.isSmooth'

theorem isPositive (x : M) : (ω₀ x).IsPositive := ω₀.isPositive' x

theorem isOneOne (x : M) : (ω₀ x).IsOneOne := (ω₀.isPositive x).1

theorem isClosed : ω₀.toFormField.IsClosed := ω₀.isClosed'

/-- The pointwise real inner product induced by a Kähler form, with convention
`g(v,w) = ω(v,Jw)`. The tangent vectors are carried to the chart model with the canonical
tangent-space equivalence. -/
noncomputable def innerAt (x : M)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) : ℝ :=
  ω₀ x ![
    CalabiYau.tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x v,
    EuclideanSpace.complexStructure n
      (CalabiYau.tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x w)]

private theorem isOneOne_apply_J_swap (x : M) (u v : EuclideanSpace ℂ (Fin n)) :
    ω₀ x ![u, EuclideanSpace.complexStructure n v] =
      ω₀ x ![v, EuclideanSpace.complexStructure n u] := by
  let α := ω₀ x
  let Iu := Complex.I • u
  let Iv := Complex.I • v
  have hswap (a b : EuclideanSpace ℂ (Fin n)) : α ![a, b] = -α ![b, a] := by
    have h : α ![b, a] = -α ![a, b] := by
      simpa using α.map_swap ![a, b] Fin.zero_ne_one
    linarith
  have hmix : α ![u, Iv] = α ![v, Iu] := by
    calc
      α ![u, Iv] = -α ![Iu, v] := by
        have h := (ω₀.isOneOne x) u Iv
        have hI : Complex.I • (Complex.I • v) = -v := by simp [smul_smul]
        rw [hI] at h
        have hneg : α ![Iu, -v] = -α ![Iu, v] := by
          change α.toContinuousMultilinearMap ![Iu, -v] =
            -α.toContinuousMultilinearMap ![Iu, v]
          have hvec : ![Iu, -v] = Function.update ![Iu, v] 1 (-v) := by
            funext i
            fin_cases i <;> simp [Function.update]
          rw [hvec]
          have hvec' : Function.update ![Iu, v] 1 v = ![Iu, v] := by
            funext i
            fin_cases i <;> simp [Function.update]
          have hlin := α.toContinuousMultilinearMap.map_update_smul ![Iu, v]
            (1 : Fin 2) (-1 : ℝ) v
          rw [hvec'] at hlin
          simpa only [neg_one_smul] using hlin
        rw [hneg] at h
        linarith
      _ = α ![v, Iu] := by
        have h := hswap Iu v
        linarith
  simpa [Iu, Iv, EuclideanSpace.complexStructure] using hmix

/-- The metric induced by a Kähler form is symmetric. -/
theorem innerAt_symm (x : M)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) :
    ω₀.innerAt x v w = ω₀.innerAt x w v := by
  unfold innerAt
  exact isOneOne_apply_J_swap ω₀ x _ _

/-- The induced metric is positive on nonzero tangent vectors. -/
theorem innerAt_pos (x : M) {v : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x}
    (hv : v ≠ 0) : 0 < ω₀.innerAt x v v := by
  unfold innerAt
  have hmodel : CalabiYau.tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x v ≠ 0 := by
    intro hzero
    exact hv ((CalabiYau.tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).injective hzero)
  exact (ω₀.isPositive x).2 _ hmodel

private theorem innerAt_zero (x : M) : ω₀.innerAt x 0 0 = 0 := by
  have hzero : (ω₀ x).toAlternatingMap ![(0 : EuclideanSpace ℂ (Fin n)), 0] = 0 := by
    have hswap := (ω₀ x).map_swap ![(0 : EuclideanSpace ℂ (Fin n)), 0] Fin.zero_ne_one
    have hvec : (![(0 : EuclideanSpace ℂ (Fin n)), 0] : Fin 2 → EuclideanSpace ℂ (Fin n)) ∘
        Equiv.swap 0 1 = ![0, 0] := by
      funext i
      fin_cases i <;> simp
    rw [hvec] at hswap
    nlinarith [hswap]
  simpa [innerAt] using hzero

/-- The fiberwise real inner product induced by a Kähler form, bundled as an inner-product core. -/
@[instance_reducible]
noncomputable def innerProductCoreAt (x : M) :
    InnerProductSpace.Core ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) where
  inner := ω₀.innerAt x
  conj_inner_symm v w := by
    simpa using (ω₀.innerAt_symm x w v)
  re_inner_nonneg v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp [innerAt_zero]
    · exact (ω₀.innerAt_pos x hv).le
  add_left v w z := by
    let e := CalabiYau.tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x
    let base : Fin 2 → EuclideanSpace ℂ (Fin n) :=
      ![0, EuclideanSpace.complexStructure n (e z)]
    have h := (ω₀ x).toContinuousMultilinearMap.map_update_add
      base (0 : Fin 2) (e v) (e w)
    have hleft : Function.update base (0 : Fin 2) (e v + e w) =
        ![e (v + w), EuclideanSpace.complexStructure n (e z)] := by
      funext i
      fin_cases i
      · simp [base, e.map_add]
      · simp [base]
    have hfirst : Function.update base (0 : Fin 2) (e v) =
        ![e v, EuclideanSpace.complexStructure n (e z)] := by
      funext i
      fin_cases i <;> simp [base]
    have hsecond : Function.update base (0 : Fin 2) (e w) =
        ![e w, EuclideanSpace.complexStructure n (e z)] := by
      funext i
      fin_cases i <;> simp [base]
    simpa [innerAt, base, hleft, hfirst, hsecond] using h
  smul_left v w c := by
    let e := CalabiYau.tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x
    let base : Fin 2 → EuclideanSpace ℂ (Fin n) :=
      ![0, EuclideanSpace.complexStructure n (e w)]
    have h := (ω₀ x).toContinuousMultilinearMap.map_update_smul
      base (0 : Fin 2) c (e v)
    have hleft : Function.update base (0 : Fin 2) (c • e v) =
        ![e (c • v), EuclideanSpace.complexStructure n (e w)] := by
      funext i
      fin_cases i
      · simp [base, e.map_smul]
      · simp [base]
    have hright : Function.update base (0 : Fin 2) (e v) =
        ![e v, EuclideanSpace.complexStructure n (e w)] := by
      funext i
      fin_cases i <;> simp [base]
    simpa [innerAt, base, hleft, hright] using h
  definite v hzero := by
    by_contra hv
    exact (ω₀.innerAt_pos x hv).ne' hzero

/-- The bundled inner product has the expected pointwise value. -/
@[simp]
theorem innerProductCoreAt_inner (x : M)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) :
    (ω₀.innerProductCoreAt x).inner v w = ω₀.innerAt x v w := rfl

/-- The local metric `g_{jk̄}(z)` of `ω₀` in the chart at `x`. -/
noncomputable def metricInChart (x : M) (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  (ω₀.toFormField.chartRep x z).coeffMatrix

theorem metricInChart_self (x : M) :
    ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) = (ω₀ x).coeffMatrix := by
  change (ω₀.toFormField.chartRep x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)).coeffMatrix = _
  rw [FormField.chartRep_self]

open scoped ComplexOrder in
theorem posDef_metricInChart (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (ω₀.metricInChart x z).PosDef := by
  let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z
  have hyx : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source :=
    (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_target hz
  have hyyℝ : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyx
  have hyyℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyℝ
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v)
          ⟨⟨hyxℂ, hyyℂ⟩, hyxℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxℂ
  have hAB : ∀ v, A (B v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v)
          ⟨⟨hyyℂ, hyxℂ⟩, hyyℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyℂ
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toLinearEquiv :=
        { toFun := A
          invFun := B
          left_inv := hBA
          right_inv := hAB
          map_add' := A.map_add
          map_smul' := A.map_smul }
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
    tangentCoordChange_real_eq ⟨hyx, hyyℝ⟩
  have hchart : ω₀.toFormField.chartRep x z =
      (ω₀.toFormField y).compContinuousLinearMap (A.restrictScalars ℝ) := by
    change (ω₀.toFormField y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hAreal]
  have hpos : (ω₀.toFormField.chartRep x z).IsPositive := by
    rw [hchart]
    exact (ω₀.isPositive y).compContinuousLinearMap AEquiv
  change ((ω₀.toFormField.chartRep x z).coeffMatrix).PosDef
  exact (ContinuousAlternatingMap.isPositive_iff.mp hpos).2

private noncomputable def alternatingEvalCLM (v : Fin 2 → EuclideanSpace ℂ (Fin n)) :
    (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] ℝ := by
  let f : (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun α ↦ α v
      map_add' := by intro α β; simp
      map_smul' := by intro c α; simp }
  exact f.mkContinuous (∏ i, ‖v i‖) (by
    intro α
    calc
      ‖f α‖ = ‖α v‖ := rfl
      _ ≤ ‖α‖ * ∏ i, ‖v i‖ := ContinuousAlternatingMap.le_opNorm α v
      _ = (∏ i, ‖v i‖) * ‖α‖ := by ring)

private noncomputable def coeffEntryCLM (j k : Fin n) :
    (EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] ℂ :=
  (1 / 2 : ℝ) •
    (Complex.ofRealCLM.comp (alternatingEvalCLM ![EuclideanSpace.single j 1,
      Complex.I • EuclideanSpace.single k 1]) -
      Complex.I • Complex.ofRealCLM.comp (alternatingEvalCLM ![EuclideanSpace.single j 1,
        EuclideanSpace.single k 1]))

private theorem coeffMatrix_entry_eq (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (j k : Fin n) : α.coeffMatrix j k = coeffEntryCLM j k α := by
  simp [coeffEntryCLM, alternatingEvalCLM, ContinuousAlternatingMap.coeffMatrix]
  ring

theorem contDiffOn_metricInChart (x : M) (j k : Fin n) :
    ContDiffOn ℝ ∞ (fun z ↦ ω₀.metricInChart x z j k)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  have hcoeff : ContDiff ℝ ∞ (coeffEntryCLM j k) := (coeffEntryCLM j k).contDiff
  have hcomp : ContDiffOn ℝ ∞
      (fun z ↦ coeffEntryCLM j k (ω₀.toFormField.chartRep x z))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    hcoeff.comp_contDiffOn (ω₀.isSmooth x)
  simpa [metricInChart, coeffMatrix_entry_eq] using hcomp

/-! ### Kähler potentials -/

/-- `φ` is a Kähler potential for `ω₀`: `φ` is smooth and `ω₀ + i∂∂̄φ > 0`. -/
def IsPotential (φ : M → ℝ) : Prop :=
  ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ ∧
    (ω₀.toFormField + mddbar n φ).IsPositive

/-- The Kähler form `ω_φ = ω₀ + i∂∂̄φ` of a Kähler potential. -/
noncomputable def perturb (φ : M → ℝ) (hφ : ω₀.IsPotential φ) : KahlerForm n M where
  toFormField := ω₀.toFormField + mddbar n φ
  isSmooth' := ω₀.isSmooth.add (isSmooth_mddbar hφ.1)
  isPositive' := hφ.2
  isClosed' := FormField.IsClosed.add ω₀.isSmooth (isSmooth_mddbar hφ.1) ω₀.isClosed
    (isClosed_mddbar hφ.1)

variable {ω₀} {φ ψ : M → ℝ}

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem contMDiff_add_functions
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (φ + ψ) := by
  have hadd : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 + p.2) := contDiff_fst.add contDiff_snd
  convert hadd.comp_contMDiff (hφ.prodMk_space hψ) using 1
  ext x
  rfl

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem contMDiff_smul_function (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
    𝓘(ℝ) ∞ φ) (c : ℝ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (c • φ) := by
  have hmul : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_fst.mul contDiff_snd
  change ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun x ↦ c * φ x)
  simpa [Function.comp_def, smul_eq_mul] using hmul.comp_contMDiff (contMDiff_const.prodMk_space hφ)

@[simp]
theorem perturb_apply (hφ : ω₀.IsPotential φ) (x : M) :
    ω₀.perturb φ hφ x = ω₀ x + mddbar n φ x := rfl

theorem IsPotential.contMDiff (hφ : ω₀.IsPotential φ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ := hφ.1

theorem isPotential_zero : ω₀.IsPotential 0 := by
  constructor
  · exact contMDiff_const
  · intro x
    have hzero : mddbar n (0 : M → ℝ) = 0 := by
      exact mddbar_const (n := n) (M := M) (0 : ℝ)
    rw [hzero]
    simpa using ω₀.isPositive x

@[simp]
theorem perturb_zero : ω₀.perturb 0 isPotential_zero = ω₀ := by
  apply ext
  intro x
  have hzero : mddbar n (0 : M → ℝ) = 0 := by
    exact mddbar_const (n := n) (M := M) (0 : ℝ)
  simp [perturb, hzero]

theorem IsPotential.add_const (hφ : ω₀.IsPotential φ) (c : ℝ) :
    ω₀.IsPotential fun x ↦ φ x + c := by
  rcases hφ with ⟨hφ, hpos⟩
  constructor
  · have hc : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun _ : M ↦ c) := contMDiff_const
    exact contMDiff_add_functions hφ hc
  · simpa [mddbar_add_const] using hpos

theorem perturb_add_const (hφ : ω₀.IsPotential φ) (c : ℝ) :
    ω₀.perturb (fun x ↦ φ x + c) (hφ.add_const c) = ω₀.perturb φ hφ := by
  apply ext
  intro x
  simp [perturb, mddbar_add_const]

/-- Potentials for `ω_φ` are the differences of potentials for `ω₀`. -/
theorem isPotential_perturb_iff (hφ : ω₀.IsPotential φ) :
    (ω₀.perturb φ hφ).IsPotential ψ ↔ ω₀.IsPotential (φ + ψ) := by
  constructor
  · intro hψ
    rcases hψ with ⟨hψsmooth, hψpos⟩
    constructor
    · exact contMDiff_add_functions hφ.1 hψsmooth
    · simpa [IsPotential, perturb, mddbar_add hφ.1 hψsmooth, add_assoc] using hψpos
  · intro hsum
    have hψsmooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ψ := by
      have hφneg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ((-1 : ℝ) • φ) :=
        contMDiff_smul_function hφ.1 (-1)
      have hdiff := contMDiff_add_functions hsum.1 hφneg
      convert hdiff using 1
      ext x
      simp
    constructor
    · exact hψsmooth
    · simpa [IsPotential, perturb, mddbar_add hφ.1 hψsmooth, add_assoc] using hsum.2

theorem perturb_perturb (hφ : ω₀.IsPotential φ) (hψ : (ω₀.perturb φ hφ).IsPotential ψ) :
    (ω₀.perturb φ hφ).perturb ψ hψ = ω₀.perturb (φ + ψ) ((isPotential_perturb_iff hφ).1 hψ) := by
  apply ext
  intro x
  simp [perturb, mddbar_add hφ.1 hψ.1, add_assoc]

/-- The set of Kähler potentials is convex. -/
theorem IsPotential.convex_comb (hφ : ω₀.IsPotential φ) (hψ : ω₀.IsPotential ψ) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) : ω₀.IsPotential ((1 - s) • φ + s • ψ) := by
  by_cases hs0 : s = 0
  · subst s
    simpa using hφ
  by_cases hs1 : s = 1
  · subst s
    simpa using hψ
  have hslt : s < 1 := lt_of_le_of_ne hs₁ hs1
  have hleft : 0 < 1 - s := sub_pos.mpr hslt
  have hright : 0 < s := lt_of_le_of_ne hs₀ (Ne.symm hs0)
  constructor
  · have hleft' : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ((1 - s : ℝ) • φ) :=
      contMDiff_smul_function hφ.1 (1 - s)
    have hright' : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (s • ψ) :=
      contMDiff_smul_function hψ.1 s
    exact contMDiff_add_functions hleft' hright'
  · have hdecomp : ω₀.toFormField + mddbar n ((1 - s) • φ + s • ψ) =
        (1 - s) • (ω₀.toFormField + mddbar n φ) + s • (ω₀.toFormField + mddbar n ψ) := by
      rw [mddbar_add (contMDiff_smul_function hφ.1 (1 - s)) (contMDiff_smul_function hψ.1 s),
        mddbar_smul hφ.1, mddbar_smul hψ.1]
      funext x
      ext u
      simp [smul_eq_mul]; ring
    change ∀ x, ((ω₀.toFormField + mddbar n ((1 - s) • φ + s • ψ)) x).IsPositive
    intro x
    rw [hdecomp]
    exact ((hφ.2 x).smul hleft).add ((hψ.2 x).smul hright)

/-- In particular `s • φ` is a potential for `s ∈ [0, 1]`. -/
theorem IsPotential.smul (hφ : ω₀.IsPotential φ) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    ω₀.IsPotential (s • φ) := by
  simpa using (isPotential_zero (ω₀ := ω₀)).convex_comb hφ hs₀ hs₁

/-- The local metric of `ω_φ` is `g_{jk̄} + φ_{jk̄}`. -/
theorem metricInChart_perturb (hφ : ω₀.IsPotential φ) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (ω₀.perturb φ hφ).metricInChart x z =
      ω₀.metricInChart x z +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
  simp [metricInChart, perturb, FormField.chartRep_add, chartRep_mddbar hφ.1 x hz,
    ContinuousAlternatingMap.coeffMatrix_add, complexHessian]

/-- On a compact connected manifold, two potentials define the same Kähler form iff they differ
by a constant. -/
theorem perturb_eq_perturb_iff [CompactSpace M] [ConnectedSpace M] (hφ : ω₀.IsPotential φ)
    (hψ : ω₀.IsPotential ψ) : ω₀.perturb φ hφ = ω₀.perturb ψ hψ ↔ ∃ c : ℝ, ∀ x, ψ x = φ x + c := by
  constructor
  · intro h
    have hforms : (ω₀.perturb φ hφ).toFormField = (ω₀.perturb ψ hψ).toFormField :=
      congrArg (fun θ : KahlerForm n M => θ.toFormField) h
    have hdd : mddbar n (ψ - φ) = 0 := by
      rw [mddbar_sub hψ.1 hφ.1]
      funext x
      have hx := congrArg (fun α : FormField (EuclideanSpace ℂ (Fin n)) M 2 => α x) hforms
      simp only [perturb] at hx
      change mddbar n ψ x - mddbar n φ x = 0
      exact sub_eq_zero.mpr (add_left_cancel hx).symm
    have hφneg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ ((-1 : ℝ) • φ) :=
      contMDiff_smul_function hφ.1 (-1)
    have hdiff : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (ψ - φ) := by
      have hh := contMDiff_add_functions hψ.1 hφneg
      convert hh using 1
      ext x
      simp; ring
    obtain ⟨c, hc⟩ := eq_const_of_mddbar_eq_zero hdiff hdd
    refine ⟨c, ?_⟩
    intro x
    have := hc x
    change ψ x - φ x = c at this
    linarith
  · rintro ⟨c, hc⟩
    have hfun : ψ = fun x ↦ φ x + c := funext hc
    subst ψ
    exact (perturb_add_const hφ c).symm

end KahlerForm
