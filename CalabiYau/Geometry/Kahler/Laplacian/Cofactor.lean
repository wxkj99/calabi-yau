module

public import CalabiYau.Geometry.Kahler.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

open scoped Manifold ContDiff ComplexOrder
open Set MeasureTheory ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M]
  {ω₀ : KahlerForm n M}

noncomputable def chartPartialZ (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  ((fderiv ℝ u z (EuclideanSpace.single j 1) : ℂ) -
    Complex.I * fderiv ℝ u z (Complex.I • EuclideanSpace.single j 1)) / 2

noncomputable def chartPartialBar (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  ((fderiv ℝ u z (EuclideanSpace.single j 1) : ℂ) +
    Complex.I * fderiv ℝ u z (Complex.I • EuclideanSpace.single j 1)) / 2

noncomputable def chartPartialZComplex (u : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ u z (EuclideanSpace.single j 1) -
    Complex.I * fderiv ℝ u z (Complex.I • EuclideanSpace.single j 1)) / 2

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
/-- The outer holomorphic derivative in coordinate `j` of the inner antiholomorphic derivative
in coordinate `k` is the `j,k` entry of the complex Hessian. In real coordinates the two
Wirtinger factors combine to the `1/4` normalization of `complexHessian_apply`. -/
theorem chartPartialZComplex_chartPartialBar
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (j k : Fin n) :
    chartPartialZComplex (fun w ↦ chartPartialBar f w k) z j =
      complexHessian f z j k := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ f w e) z d = fderiv ℝ (fderiv ℝ f) z d e := by
    rw [fderiv_clm_apply hfd (differentiableAt_const e)]
    simp
  have hsecondComplex (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (fderiv ℝ f w e : ℂ)) z d =
        (fderiv ℝ (fderiv ℝ f) z d e : ℂ) := by
    have hreal := hfd.clm_apply (differentiableAt_const e)
    have h := (Complex.ofRealCLM.hasFDerivAt.comp z hreal.hasFDerivAt).fderiv
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
    change fderiv ℝ (Complex.ofRealCLM ∘ (fun w ↦ fderiv ℝ f w e)) z d = _
    simpa [hsecond] using h'
  have hbarDeriv (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ chartPartialBar f w k) z d =
        ((fderiv ℝ (fderiv ℝ f) z d (EuclideanSpace.single k 1) : ℂ) +
          Complex.I * fderiv ℝ (fderiv ℝ f) z d
            (Complex.I • EuclideanSpace.single k 1)) / 2 := by
    let A := fun w ↦ (fderiv ℝ f w (EuclideanSpace.single k 1) : ℂ)
    let B := fun w ↦ (fderiv ℝ f w (Complex.I • EuclideanSpace.single k 1) : ℂ)
    have hA : DifferentiableAt ℝ A z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        (hfd.clm_apply (differentiableAt_const _)))
    have hB : DifferentiableAt ℝ B z := by
      exact (Complex.ofRealCLM.differentiableAt.comp z
        (hfd.clm_apply (differentiableAt_const _)))
    have hnum : DifferentiableAt ℝ (fun w ↦ A w + Complex.I * B w) z :=
      hA.add (hB.const_mul Complex.I)
    have hfun : (fun w ↦ chartPartialBar f w k) =
        fun w ↦ (2 : ℂ)⁻¹ * (A w + Complex.I * B w) := by
      funext w
      simp [chartPartialBar, A, B, div_eq_mul_inv]
      ring
    rw [hfun, fderiv_const_mul hnum (2 : ℂ)⁻¹, fderiv_fun_add hA (hB.const_mul Complex.I),
      fderiv_const_mul hB Complex.I]
    dsimp [A, B]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hsecondComplex d (EuclideanSpace.single k 1),
      hsecondComplex d (Complex.I • EuclideanSpace.single k 1)]
    ring
  change ((fderiv ℝ (fun w ↦ chartPartialBar f w k) z (EuclideanSpace.single j 1) -
    Complex.I * fderiv ℝ (fun w ↦ chartPartialBar f w k) z
      (Complex.I • EuclideanSpace.single j 1)) / 2) = _
  rw [hbarDeriv (EuclideanSpace.single j 1),
    hbarDeriv (Complex.I • EuclideanSpace.single j 1),
    complexHessian_apply hf j k]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem chartPartialZComplex_mul
    {u v : EuclideanSpace ℂ (Fin n) → ℂ}
    {z : EuclideanSpace ℂ (Fin n)} (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) (j : Fin n) :
    chartPartialZComplex (fun w ↦ u w * v w) z j =
      (chartPartialZComplex u z j) * (v z) + (u z) * (chartPartialZComplex v z j) := by
  unfold chartPartialZComplex
  rw [fderiv_fun_mul hu hv]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

theorem fderiv_coeffMatrix_entry
    {α : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    {z : EuclideanSpace ℂ (Fin n)} (hα : ContDiffAt ℝ 1 α z) (j k : Fin n) :
    fderiv ℝ (fun y ↦ (α y).coeffMatrix j k) z =
      (1 / 2 : ℝ) •
        (Complex.ofRealCLM.comp
            (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
              Complex.I • EuclideanSpace.single k 1]) z) -
          Complex.I • Complex.ofRealCLM.comp
            (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
              EuclideanSpace.single k 1]) z)) := by
  have hdiff : DifferentiableAt ℝ α z := hα.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ
      (fun y ↦ α y ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]) z :=
    hdiff.continuousAlternatingMap_apply_const _
  have hB : DifferentiableAt ℝ
      (fun y ↦ α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]) z :=
    hdiff.continuousAlternatingMap_apply_const _
  have hAcast : (fun y ↦ ((α y ![EuclideanSpace.single j 1,
      Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun y ↦ α y ![EuclideanSpace.single j 1,
        Complex.I • EuclideanSpace.single k 1]) := rfl
  have hBcast : (fun y ↦ ((α y ![EuclideanSpace.single j 1,
      EuclideanSpace.single k 1] : ℝ) : ℂ)) =
      Complex.ofRealCLM ∘ (fun y ↦ α y ![EuclideanSpace.single j 1,
        EuclideanSpace.single k 1]) := rfl
  change fderiv ℝ (fun y ↦
    (((α y ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
      Complex.I * (α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2) z = _
  have hAcomplex : DifferentiableAt ℝ
      (fun y ↦ ((α y ![EuclideanSpace.single j 1,
        Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ)) z := by
    rw [hAcast]
    exact Complex.ofRealCLM.differentiableAt.comp z hA
  have hBcomplex : DifferentiableAt ℝ
      (fun y ↦ ((α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ) : ℂ)) z := by
    rw [hBcast]
    exact Complex.ofRealCLM.differentiableAt.comp z hB
  have hAderiv : fderiv ℝ
      (fun y ↦ ((α y ![EuclideanSpace.single j 1,
        Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ)) z =
      Complex.ofRealCLM.comp
      (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
          Complex.I • EuclideanSpace.single k 1]) z) := by
    rw [hAcast]
    exact (Complex.ofRealCLM.hasFDerivAt.comp z hA.hasFDerivAt).fderiv
  have hBderiv : fderiv ℝ
      (fun y ↦ ((α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ) : ℂ)) z =
      Complex.ofRealCLM.comp
      (fderiv ℝ (fun y ↦ α y ![EuclideanSpace.single j 1,
          EuclideanSpace.single k 1]) z) := by
    rw [hBcast]
    exact (Complex.ofRealCLM.hasFDerivAt.comp z hB.hasFDerivAt).fderiv
  have hnum : DifferentiableAt ℝ
      (fun y ↦ ((α y ![EuclideanSpace.single j 1,
        Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
          Complex.I * (α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) z :=
    hAcomplex.sub (hBcomplex.const_mul Complex.I)
  rw [show (fun y ↦
      (((α y ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
        Complex.I * (α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ)) / 2) =
      (fun y ↦ (2 : ℂ)⁻¹ *
        (((α y ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] : ℝ) : ℂ) -
          Complex.I * (α y ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ))) by
    funext y
    simp only [div_eq_mul_inv]
    ring]
  rw [fderiv_const_mul hnum (2 : ℂ)⁻¹]
  rw [fderiv_fun_sub hAcomplex (hBcomplex.const_mul Complex.I)]
  rw [fderiv_const_mul hBcomplex Complex.I, hAderiv, hBderiv]
  have hhalf : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  rw [hhalf]
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]

noncomputable def chartGradientPair
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n)) : ℝ :=
  RCLike.re ((G z)⁻¹ * Matrix.vecMulVec (chartPartialZ u z) (chartPartialBar v z)).trace

/-- The chart pairing is linear in its first function argument over a finite sum. -/
theorem chartGradientPair_sum_first {ι : Type*} (G : EuclideanSpace ℂ (Fin n) →
    Matrix (Fin n) (Fin n) ℂ) (s : Finset ι) (U : ι → EuclideanSpace ℂ (Fin n) → ℝ)
    (V : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hU : ∀ i ∈ s, DifferentiableAt ℝ (U i) z) :
    chartGradientPair G (fun w ↦ ∑ i ∈ s, U i w) V z =
      ∑ i ∈ s, chartGradientPair G (U i) V z := by
  have hfdSum : fderiv ℝ (fun w ↦ ∑ i ∈ s, U i w) z =
      ∑ i ∈ s, fderiv ℝ (U i) z :=
    fderiv_fun_sum (u := s) (fun i hi ↦ hU i hi)
  have hfdSumVal (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ ∑ i ∈ s, U i w) z v =
        ∑ i ∈ s, fderiv ℝ (U i) z v := by
    simpa using congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L v) hfdSum
  have hpartialZ : chartPartialZ (fun w ↦ ∑ i ∈ s, U i w) z =
      ∑ i ∈ s, chartPartialZ (U i) z := by
    funext j
    simp only [Finset.sum_apply, chartPartialZ]
    rw [hfdSumVal, hfdSumVal]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  have hvec : Matrix.vecMulVec (∑ i ∈ s, chartPartialZ (U i) z)
      (chartPartialBar V z) =
      ∑ i ∈ s, Matrix.vecMulVec (chartPartialZ (U i) z) (chartPartialBar V z) := by
    have h := congrArg
      (fun L : (Fin n → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ ↦ L (chartPartialBar V z))
      (_root_.map_sum (vecMulVecBilin ℂ ℂ) (fun i ↦ chartPartialZ (U i) z) s)
    have hBilin (X Y : Fin n → ℂ) :
        (vecMulVecBilin ℂ ℂ X) Y = Matrix.vecMulVec X Y := rfl
    rw [LinearMap.sum_apply, hBilin] at h
    exact h
  unfold chartGradientPair
  rw [hpartialZ, hvec]
  simp [Matrix.mul_sum, Matrix.trace_sum]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
/-- The Hermitian chart pairing is symmetric for a positive Kähler metric. -/
theorem chartGradientPair_symm (ω₀ : KahlerForm n M) (i : M)
    (u v : EuclideanSpace ℂ (Fin n) → ℝ) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target) :
    chartGradientPair (ω₀.metricInChart i) u v z =
      chartGradientPair (ω₀.metricInChart i) v u z := by
  let C := (ω₀.metricInChart i z)⁻¹
  have hC : C.IsHermitian := (ω₀.posDef_metricInChart i hz).isHermitian.inv
  have hbar (w : EuclideanSpace ℂ (Fin n) → ℝ) (j : Fin n) :
      chartPartialBar w z j = star (chartPartialZ w z j) := by
    simp [chartPartialBar, chartPartialZ, div_eq_mul_inv]
  have hstar :
      star (∑ a, ∑ b, C a b * chartPartialZ v z b * chartPartialBar u z a) =
        ∑ a, ∑ b, chartPartialZ u z a *
          (chartPartialBar v z b * C b a) := by
    simp only [star_sum, star_mul, star_star, hbar]
    simp_rw [hC.apply]
  have hsum :
      (∑ a, ∑ b, C a b * chartPartialZ u z b * chartPartialBar v z a) =
        star (∑ a, ∑ b, C a b * chartPartialZ v z b * chartPartialBar u z a) := by
    rw [hstar, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  change RCLike.re (C * Matrix.vecMulVec (chartPartialZ u z) (chartPartialBar v z)).trace =
    RCLike.re (C * Matrix.vecMulVec (chartPartialZ v z) (chartPartialBar u z)).trace
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  change RCLike.re (∑ a, ∑ b,
      C a b * (chartPartialZ u z b * chartPartialBar v z a)) =
    RCLike.re (∑ a, ∑ b,
      C a b * (chartPartialZ v z b * chartPartialBar u z a))
  calc
    _ = RCLike.re (star (∑ a, ∑ b,
        C a b * chartPartialZ v z b * chartPartialBar u z a)) :=
      (by simpa only [← mul_assoc] using congrArg RCLike.re hsum)
    _ = _ := by
      change (star (∑ a, ∑ b,
        C a b * chartPartialZ v z b * chartPartialBar u z a)).re =
        (∑ a, ∑ b, C a b *
          (chartPartialZ v z b * chartPartialBar u z a)).re
      simp only [Complex.star_def, Complex.conj_re, ← mul_assoc]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
/-- The chart pairing of a function with itself is its intrinsic trace pairing,
expressed using the chart representatives of the two forms. -/
theorem chartGradientPair_eq_relTrace_mdWedgeDBar (ω₀ : KahlerForm n M) (i : M)
    (g : M → ℝ) (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target) :
    chartGradientPair (ω₀.metricInChart i)
        (fun w ↦ g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm w))
        (fun w ↦ g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm w)) z =
      relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z))
        (mdWedgeDBar n g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
  let y := c.symm z
  have hyx : y ∈ c.source := c.map_target hz
  have hzpoint : c.symm z = y := rfl
  have hychart : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := by
    simp [y]
  have hyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) i).source := by
    simpa [c, extChartAt_real_eq, ← extChartAt_source] using hyx
  have hyCy : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hOverlap : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).source ∩
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := ⟨hyx, hychart⟩
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    toLinearEquiv := {
      toFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) i y y
      invFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y i y
      left_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) i).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
              (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) i).source :=
          ⟨⟨hyC, hyCy⟩, hyC⟩
        rw [tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := i) (x := y) (y := i) (z := y) (v := v) htriple]
        exact tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (x := i) (z := y) hyC
      right_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) i).source ∩
              (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source :=
          ⟨⟨hyCy, hyC⟩, hyCy⟩
        rw [tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := i) (y := y) (z := y) (v := v) htriple]
        exact tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (x := y) (z := y) (by simp)
      map_add' := by intro u v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) i y y).map_add u v
      map_smul' := by intro a v; exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) i y y).map_smul a v
    }
    continuous_toFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) i y y).continuous
    continuous_invFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y i y).continuous
  }
  have hA : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘ c.symm) z =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    have hdef : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i y y =
        fderiv ℝ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘ c.symm) (c y) := by
      rw [tangentCoordChange_def]
      simp [c]
    calc
      _ = fderiv ℝ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘ c.symm) (c y) := by
        rw [← c.right_inv hz]
      _ = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i y y := hdef.symm
      _ = (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) i y y).restrictScalars ℝ :=
        tangentCoordChange_real_eq hOverlap
      _ = _ := rfl
  have hrep (β : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
      β.chartRep i z = (β y).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    rw [FormField.chartRep_eq_chartRep_comp (x := i) (x' := y) (z := z) hz]
    · rw [hzpoint, FormField.chartRep_self, hA]
    · rw [hzpoint]
      exact hychart
  have hα : (mdWedgeDBar n g y).IsOneOne :=
    (isNonneg_dWedgeDBar _).1
  have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap
    (ω₀.isOneOne y) hα A
  have hcoord := chartRep_mdWedgeDBar hg i hz
  let Gg : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ g (c.symm w)
  have hcoeff : ((mdWedgeDBar n g).chartRep i z).coeffMatrix =
      Matrix.vecMulVec (chartPartialZ Gg z) (chartPartialBar Gg z) := by
    rw [hcoord, coeffMatrix_dWedgeDBar]
    rfl
  change RCLike.re ((ω₀.metricInChart i z)⁻¹ *
      Matrix.vecMulVec (chartPartialZ Gg z) (chartPartialBar Gg z)).trace = _
  calc
    _ = RCLike.re ((ω₀.metricInChart i z)⁻¹ *
          ((mdWedgeDBar n g).chartRep i z).coeffMatrix).trace := by rw [hcoeff]
    _ = relTrace (ω₀.toFormField.chartRep i z) ((mdWedgeDBar n g).chartRep i z) := by
      simp [relTrace, metricInChart]
    _ = relTrace
          ((ω₀ y).compContinuousLinearMap
            ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
          ((mdWedgeDBar n g y).compContinuousLinearMap
            ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) := by
      rw [hrep (ω₀.toFormField), hrep (mdWedgeDBar n g)]
    _ = relTrace (ω₀ y) (mdWedgeDBar n g y) := htrace

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] in
/-- In holomorphic coordinates the Kähler identity says that the cofactor matrix of the metric has
zero holomorphic divergence. -/
def ChartCofactorDivergenceFree
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ) (U : Set (EuclideanSpace ℂ (Fin n))) :
  Prop :=
  ∀ z ∈ U, ∀ k : Fin n,
    ∑ j, chartPartialZComplex (fun w ↦ (G w).det * (G w)⁻¹ k j) z j = 0

theorem cofactor_divergence_algebra {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℂ) (T : ι → ι → ι → ℂ)
    (hT : ∀ i j k, T i j k = T j i k) (k : ι) :
    ∑ j, ∑ a, ∑ b, B a b * T j b a * B k j =
      ∑ j, ∑ a, ∑ b, B k a * T j a b * B b j := by
  classical
  let F := fun j a b ↦ B a b * T b j a * B k j
  have hT' : ∑ j, ∑ a, ∑ b, B a b * T j b a * B k j =
      ∑ j, ∑ a, ∑ b, F j a b := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hT j b a]
  calc
    _ = ∑ j, ∑ a, ∑ b, F j a b := hT'
    _ = ∑ j, ∑ b, ∑ a, F j a b := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ j, ∑ a, F j a b := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro a ha
      dsimp [F]
      ring

open scoped Matrix.Norms.Elementwise in
theorem chartDet_partial_formula
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)}
    (hG : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z)
    (hunit : IsUnit (G z)) (j : Fin n) :
    DifferentiableAt ℝ (fun w ↦ (G w).det) z ∧
      chartPartialZComplex (fun w ↦ (G w).det) z j =
        (G z).det * Matrix.trace
          ((G z)⁻¹ * Matrix.of (fun a b : Fin n ↦ chartPartialZComplex (fun w ↦ G w a b) z j)) := by
  constructor
  · simp_rw [Matrix.det_apply]
    fun_prop
  · have hentry (a b : Fin n) : DifferentiableAt ℝ (fun w ↦ G w a b) z :=
      (hG a b).differentiableAt (by norm_num)
    have hGdiff : DifferentiableAt ℝ G z := by
      change DifferentiableAt ℝ (fun w a b ↦ G w a b) z
      exact differentiableAt_pi.2 (fun a ↦ differentiableAt_pi.2 (fun b ↦ hentry a b))
    have hdetDiff : DifferentiableAt ℝ (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.det) (G z) := by
      simp_rw [Matrix.det_apply]
      fun_prop
    have hjac (H : Matrix (Fin n) (Fin n) ℂ) :
        fderiv ℝ (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.det) (G z) H =
          (G z).det * Matrix.trace ((G z)⁻¹ * H) := by
      let M : Matrix (Fin n) (Fin n) ℂ := (G z)⁻¹ * H
      have hcore : HasDerivAt (fun t : ℂ ↦ (1 + t • M).det) (Matrix.trace M) 0 := by
        let p : Polynomial ℂ := Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)
        have hp := p.hasDerivAt (0 : ℂ)
        have hp' : HasDerivAt (fun t : ℂ ↦ p.eval t) (Matrix.trace M) 0 := by
          simpa [p] using hp.congr_deriv (Matrix.derivative_det_one_add_X_smul M)
        have heq : (fun t : ℂ ↦ (1 + t • M).det) = fun t ↦ p.eval t := by
          funext t
          simp [p, eval_det, matPolyEquiv_map_smul]
          congr 1
          ext a b
          simp [Matrix.mul_apply, Matrix.diagonal]
          ring_nf
        rw [heq]
        exact hp'
      have hunitA : IsUnit (G z).det :=
        (Matrix.isUnit_iff_isUnit_det (A := G z)).mp hunit
      have hmul : G z * M = H := by
        change G z * ((G z)⁻¹ * H) = H
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv (G z) hunitA, Matrix.one_mul]
      have hfactor (t : ℝ) : G z + t • H = G z * (1 + (t : ℂ) • M) := by
        calc
          G z + t • H = G z + (t : ℂ) • H := by simp
          _ = G z * 1 + (t : ℂ) • (G z * M) := by rw [hmul]; simp
          _ = G z * 1 + G z * ((t : ℂ) • M) := by rw [← Matrix.mul_smul]
          _ = G z * (1 + (t : ℂ) • M) := by simp [Matrix.mul_add]
      have hdetline : HasDerivAt (fun t : ℝ ↦ (G z + t • H).det)
          ((G z).det * Matrix.trace M) 0 := by
        have hcoreF : HasDerivAt (fun t : ℝ ↦ (1 + (t : ℂ) • M).det)
            (Matrix.trace M) 0 := by
          have hcast : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 0 := by
            simpa using (RCLike.ofRealCLM : ℝ →L[ℝ] ℂ).hasDerivAt
          have hcoreF := hcore.hasFDerivAt.restrictScalars ℝ
          simpa [Function.comp_def] using hcoreF.comp_hasDerivAt_of_eq 0 hcast (by simp)
        have heq : (fun t : ℝ ↦ (G z + t • H).det) =
            fun t : ℝ ↦ (G z).det * (1 + (t : ℂ) • M).det := by
          funext t
          rw [hfactor t, Matrix.det_mul]
        rw [heq]
        exact hcoreF.const_mul (G z).det
      have hline : HasDerivAt (fun t : ℝ ↦ G z + t • H) H 0 := by
        exact (((hasDerivAt_id (0 : ℝ)).smul_const H).const_add (G z)).congr_deriv
          (one_smul ℝ H)
      have hchain := hdetDiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
      have hchain' : HasDerivAt (fun t : ℝ ↦ (G z + t • H).det)
          (fderiv ℝ (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.det) (G z) H) 0 := by
        convert hchain using 1 <;> rfl
      have hraw := hdetline.unique hchain'
      simpa [M] using hraw.symm
    have hderiv (v : EuclideanSpace ℂ (Fin n)) :
        fderiv ℝ (fun w ↦ (G w).det) z v =
          (G z).det * Matrix.trace ((G z)⁻¹ * Matrix.of
            (fun a b : Fin n ↦ fderiv ℝ (fun w ↦ G w a b) z v)) := by
      change fderiv ℝ ((fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.det) ∘ G) z v = _
      rw [fderiv_comp z hdetDiff hGdiff]
      change (fderiv ℝ (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.det) (G z))
          (fderiv ℝ G z v) = _
      rw [hjac]
      have hD : fderiv ℝ G z v = Matrix.of
          (fun a b : Fin n ↦ fderiv ℝ (fun w ↦ G w a b) z v) := by
        ext a b
        change (fderiv ℝ (fun w a b ↦ G w a b) z v) a b =
          fderiv ℝ (fun w ↦ G w a b) z v
        have hrow (a : Fin n) : DifferentiableAt ℝ (fun w b ↦ G w a b) z :=
          differentiableAt_pi.2 (fun b ↦ hentry a b)
        rw [fderiv_pi (fun a ↦ hrow a)]
        simp only [ContinuousLinearMap.pi_apply]
        rw [fderiv_pi (fun b ↦ hentry a b)]
        rfl
      rw [hD]
    let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
    let D₁ : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ G w a b) z e)
    let D₂ : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ G w a b) z (Complex.I • e))
    have hmatrix : Matrix.of (fun a b : Fin n ↦
        chartPartialZComplex (fun w ↦ G w a b) z j) =
        (2 : ℂ)⁻¹ • (D₁ - Complex.I • D₂) := by
      ext a b
      simp [chartPartialZComplex, D₁, D₂, div_eq_mul_inv]
      ring
    have htrace : Matrix.trace ((G z)⁻¹ *
        ((2 : ℂ)⁻¹ • (D₁ - Complex.I • D₂))) =
        (2 : ℂ)⁻¹ * (Matrix.trace ((G z)⁻¹ * D₁) -
          Complex.I * Matrix.trace ((G z)⁻¹ * D₂)) := by
      rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub,
        Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      ring
    change (fderiv ℝ (fun w ↦ (G w).det) z e -
      Complex.I * fderiv ℝ (fun w ↦ (G w).det) z (Complex.I • e)) / 2 = _
    rw [hderiv e, hderiv (Complex.I • e)]
    change ( (G z).det * Matrix.trace ((G z)⁻¹ * D₁) -
      Complex.I * ((G z).det * Matrix.trace ((G z)⁻¹ * D₂))) / 2 = _
    rw [hmatrix, htrace]
    ring

theorem chartInv_differentiableAt
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)}
    (hG : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z)
    (hunit : IsUnit (G z)) (k j : Fin n) :
    DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ k j) z := by
  have hentry (a b : Fin n) : DifferentiableAt ℝ (fun w ↦ G w a b) z :=
    (hG a b).differentiableAt (by norm_num)
  have hdet : DifferentiableAt ℝ (fun w ↦ (G w).det) z := by
    simp_rw [Matrix.det_apply]
    fun_prop
  have hadj : DifferentiableAt ℝ (fun w ↦ (G w).adjugate k j) z := by
    simp_rw [Matrix.adjugate_apply]
    have hupd (a b : Fin n) :
        DifferentiableAt ℝ
          (fun w ↦ (G w).updateRow j (Pi.single k (1 : ℂ)) a b) z := by
      by_cases hab : a = j
      · simp [Matrix.updateRow_apply, hab]
      · simpa [Matrix.updateRow_apply, hab] using hentry a b
    simp_rw [Matrix.det_apply]
    fun_prop
  have hdetUnit : IsUnit ((G z).det) :=
    (Matrix.isUnit_iff_isUnit_det (A := G z)).mp hunit
  have hinvdet : DifferentiableAt ℝ (fun w ↦ Ring.inverse ((G w).det)) z :=
    by simpa only [Function.comp_def] using
      (differentiableAt_inverse hdetUnit).comp z hdet
  have hinvEntry : DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ k j) z := by
    have hform : (fun w ↦ (G w)⁻¹ k j) =
        fun w ↦ Ring.inverse ((G w).det) * (G w).adjugate k j := by
      funext w
      simp [Matrix.inv_def, smul_eq_mul]
    rw [hform]
    exact hinvdet.mul hadj
  exact hinvEntry

theorem chartInv_partial_formula
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)}
    (hG : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z)
    (hunit : IsUnit (G z)) (k j : Fin n) :
    DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ k j) z ∧
      chartPartialZComplex (fun w ↦ (G w)⁻¹ k j) z j =
        -(((G z)⁻¹ * ((Matrix.of (fun a b : Fin n ↦
          chartPartialZComplex (fun w ↦ G w a b) z j)) * (G z)⁻¹)) k j) := by
  refine ⟨chartInv_differentiableAt hG hunit k j, ?_⟩
  have hInvFderiv (i j : Fin n) (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ (G w)⁻¹ i j) z v =
        -(((G z)⁻¹ * (Matrix.of (fun a b : Fin n ↦
          fderiv ℝ (fun w ↦ G w a b) z v)) * (G z)⁻¹) i j) := by
    classical
    have hentry (a b : Fin n) : DifferentiableAt ℝ (fun w ↦ G w a b) z :=
      (hG a b).differentiableAt (by norm_num)
    have hinvEntry (a b : Fin n) :
        DifferentiableAt ℝ (fun w ↦ (G w)⁻¹ a b) z :=
      chartInv_differentiableAt hG hunit a b
    have hdet : DifferentiableAt ℝ (fun w ↦ (G w).det) z := by
      simp_rw [Matrix.det_apply]
      fun_prop
    have hdetUnit : IsUnit ((G z).det) :=
      (Matrix.isUnit_iff_isUnit_det (A := G z)).mp hunit
    have hdetEvent : ∀ᶠ w in nhds z, (G w).det ≠ 0 :=
      hdet.continuousAt.eventually_ne hdetUnit.ne_zero
    have hunitEvent : ∀ᶠ w in nhds z, IsUnit (G w) := by
      filter_upwards [hdetEvent] with w hw
      exact (Matrix.isUnit_iff_isUnit_det (A := G w)).mpr (isUnit_iff_ne_zero.mpr hw)
    have hprodEvent (a b : Fin n) :
        (fun w ↦ (G w * (G w)⁻¹) a b) =ᶠ[nhds z]
          fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
      filter_upwards [hunitEvent] with w hw
      have hwdet : IsUnit ((G w).det) :=
        (Matrix.isUnit_iff_isUnit_det (A := G w)).mp hw
      rw [Matrix.mul_nonsing_inv (G w) hwdet]
    have hprodSum (a b : Fin n) :
        (fun w ↦ (G w * (G w)⁻¹) a b) =
          fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b := by
      funext w
      simp [Matrix.mul_apply]
    have htermDiff (a b l : Fin n) :
        DifferentiableAt ℝ (fun w ↦ G w a l * (G w)⁻¹ l b) z :=
      (hentry a l).mul (hinvEntry l b)
    have hderivSum (a b : Fin n) :
        fderiv ℝ (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) z v = 0 := by
      have hsumEvent :
          (fun w ↦ ∑ l : Fin n, G w a l * (G w)⁻¹ l b) =ᶠ[nhds z]
            fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ) a b :=
        (Filter.EventuallyEq.of_eq (hprodSum a b).symm).trans (hprodEvent a b)
      have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v)
        hsumEvent.fderiv_eq
      simpa using h
    have hentryEq (a b : Fin n) :
        ∑ l : Fin n,
          fderiv ℝ (fun w ↦ G w a l * (G w)⁻¹ l b) z v = 0 := by
      have h := hderivSum a b
      rw [fderiv_fun_sum (u := Finset.univ) (by intro l hl; exact htermDiff a b l)] at h
      simpa only [_root_.sum_apply] using h
    have hentryRel (a b : Fin n) :
        ∑ l : Fin n,
          (G z a l * fderiv ℝ (fun w ↦ (G w)⁻¹ l b) z v +
            fderiv ℝ (fun w ↦ G w a l) z v * (G z)⁻¹ l b) = 0 := by
      have h := hentryEq a b
      simp_rw [fderiv_fun_mul (hentry a _) (hinvEntry _ b)] at h
      simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] at h
      simp_rw [mul_comm ((G z)⁻¹ _ _) (fderiv ℝ (fun w ↦ G w a _) z v)] at h
      linear_combination h
    let D : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ (G w)⁻¹ a b) z v)
    let H : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ G w a b) z v)
    have hmul : G z * D = -(H * (G z)⁻¹) := by
      ext a b
      simp only [D, H, Matrix.mul_apply, Matrix.of_apply]
      have hsum :
          (∑ l : Fin n, G z a l * fderiv ℝ (fun w ↦ (G w)⁻¹ l b) z v) +
            (∑ l : Fin n, fderiv ℝ (fun w ↦ G w a l) z v * (G z)⁻¹ l b) = 0 := by
        calc
          _ = ∑ l : Fin n,
              (G z a l * fderiv ℝ (fun w ↦ (G w)⁻¹ l b) z v +
                fderiv ℝ (fun w ↦ G w a l) z v * (G z)⁻¹ l b) := by
                  rw [← Finset.sum_add_distrib]
          _ = 0 := hentryRel a b
      exact (eq_neg_iff_add_eq_zero).2 hsum
    have hleft : (G z)⁻¹ * G z = 1 :=
      Matrix.nonsing_inv_mul (A := G z) ((Matrix.isUnit_iff_isUnit_det (A := G z)).mp hunit)
    have hD : D = -((G z)⁻¹ * H * (G z)⁻¹) := by
      calc
        D = 1 * D := by simp
        _ = ((G z)⁻¹ * G z) * D := by rw [hleft]
        _ = (G z)⁻¹ * (G z * D) := by rw [Matrix.mul_assoc]
        _ = (G z)⁻¹ * (-(H * (G z)⁻¹)) := by rw [hmul]
        _ = -((G z)⁻¹ * H * (G z)⁻¹) := by simp [Matrix.mul_assoc]
    simpa [D, H] using congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A i j) hD
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let D₁ : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ G w a b) z e)
  let D₂ : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun a b ↦ fderiv ℝ (fun w ↦ G w a b) z (Complex.I • e))
  let H : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun a b ↦ chartPartialZComplex (fun w ↦ G w a b) z j)
  have hH : H = (2 : ℂ)⁻¹ • (D₁ - Complex.I • D₂) := by
    ext a b
    change ((fderiv ℝ (fun w ↦ G w a b) z e -
      Complex.I * fderiv ℝ (fun w ↦ G w a b) z (Complex.I • e)) / 2) =
        (2 : ℂ)⁻¹ * (fderiv ℝ (fun w ↦ G w a b) z e -
          Complex.I * fderiv ℝ (fun w ↦ G w a b) z (Complex.I • e))
    ring
  have h₁ := hInvFderiv k j e
  have h₂ := hInvFderiv k j (Complex.I • e)
  have hD₁ : Matrix.of (fun a b : Fin n ↦ fderiv ℝ (fun w ↦ G w a b) z e) = D₁ := rfl
  have hD₂ : Matrix.of (fun a b : Fin n ↦
      fderiv ℝ (fun w ↦ G w a b) z (Complex.I • e)) = D₂ := rfl
  rw [hD₁] at h₁
  rw [hD₂] at h₂
  change chartPartialZComplex (fun w ↦ (G w)⁻¹ k j) z j =
    -((G z)⁻¹ * (H * (G z)⁻¹)) k j
  have hmatrix : (G z)⁻¹ * ((2 : ℂ)⁻¹ • (D₁ - Complex.I • D₂) * (G z)⁻¹) =
      (2 : ℂ)⁻¹ • ((G z)⁻¹ * D₁ * (G z)⁻¹ -
        Complex.I • ((G z)⁻¹ * D₂ * (G z)⁻¹)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul]
    simp [Matrix.mul_assoc]
  change ((fderiv ℝ (fun w ↦ (G w)⁻¹ k j) z e -
    Complex.I * fderiv ℝ (fun w ↦ (G w)⁻¹ k j) z (Complex.I • e)) / 2) =
      -((G z)⁻¹ * (H * (G z)⁻¹)) k j
  rw [h₁, h₂, hH]
  rw [hmatrix]
  have hcomp :
      ((G z)⁻¹ * D₁ * (G z)⁻¹ - Complex.I • ((G z)⁻¹ * D₂ * (G z)⁻¹)) k j =
        ((G z)⁻¹ * D₁ * (G z)⁻¹) k j -
          Complex.I * ((G z)⁻¹ * D₂ * (G z)⁻¹) k j := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.smul_apply, smul_eq_mul, hcomp]
  simp only [Matrix.mul_assoc]
  ring_nf

theorem chartCofactor_partial_formula
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {z : EuclideanSpace ℂ (Fin n)}
    (hG : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z)
    (hunit : IsUnit (G z)) (k j : Fin n) :
    chartPartialZComplex (fun w ↦ (G w).det * (G w)⁻¹ k j) z j =
      (G z).det *
        (Matrix.trace ((G z)⁻¹ * Matrix.of (fun a b : Fin n ↦
          chartPartialZComplex (fun w ↦ G w a b) z j)) * (G z)⁻¹ k j -
          (((G z)⁻¹ * ((Matrix.of (fun a b : Fin n ↦
            chartPartialZComplex (fun w ↦ G w a b) z j)) * (G z)⁻¹)) k j)) := by
  have hdet := chartDet_partial_formula hG hunit j
  have hinv := chartInv_partial_formula hG hunit k j
  rw [chartPartialZComplex_mul hdet.1 hinv.1, hdet.2, hinv.2]
  ring

theorem extDeriv_zero_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : E → E [⋀^Fin 2]→L[ℝ] ℝ}
    {z : E} (hα : ContDiffAt ℝ 1 α z) (hclosed : extDeriv α z = 0)
    (u v w : E) :
    fderiv ℝ (fun y ↦ α y ![v, w]) z u -
      fderiv ℝ (fun y ↦ α y ![u, w]) z v +
      fderiv ℝ (fun y ↦ α y ![u, v]) z w = 0 := by
  have hdiff := hα.differentiableAt (by norm_num)
  have heval := congrArg (fun β : E [⋀^Fin 3]→L[ℝ] ℝ => β ![u, v, w]) hclosed
  rw [extDeriv_apply hdiff ![u, v, w]] at heval
  simp [Fin.sum_univ_succ] at heval
  have hr₁ : Fin.removeNth (1 : Fin 3) ![u, v, w] = ![u, w] := by
    ext i
    fin_cases i <;> rfl
  have hr₂ : Fin.removeNth (2 : Fin 3) ![u, v, w] = ![u, v] := by
    ext i
    fin_cases i <;> rfl
  rw [hr₁, hr₂] at heval
  linarith

theorem closed_oneOne_partial_identity
    {α : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    {z : EuclideanSpace ℂ (Fin n)} (hα : ContDiffAt ℝ 1 α z)
    (hclosed : extDeriv α z = 0)
    (hone : ∀ᶠ y in nhds z, (α y).IsOneOne)
    (u v w : EuclideanSpace ℂ (Fin n)) :
    let D := fun (d a b : EuclideanSpace ℂ (Fin n)) ↦
      fderiv ℝ (fun y ↦ α y ![a, b]) z d
    ((D u v (Complex.I • w) - D v u (Complex.I • w) : ℝ) -
      Complex.I * (D u v w - D v u w : ℝ) -
      Complex.I * (D (Complex.I • u) v (Complex.I • w) -
        D (Complex.I • v) u (Complex.I • w) : ℝ) -
      (D (Complex.I • u) v w - D (Complex.I • v) u w : ℝ)) = 0 := by
  dsimp only
  let D := fun (d a b : EuclideanSpace ℂ (Fin n)) ↦
    fderiv ℝ (fun y ↦ α y ![a, b]) z d
  have hA := extDeriv_zero_apply hα hclosed u v (Complex.I • w)
  have hB := extDeriv_zero_apply hα hclosed u v w
  have hC := extDeriv_zero_apply hα hclosed (Complex.I • u) (Complex.I • v) w
  have hE := extDeriv_zero_apply hα hclosed (Complex.I • u) (Complex.I • v)
    (Complex.I • w)
  have hJ (d a b : EuclideanSpace ℂ (Fin n)) : D d (Complex.I • a) (Complex.I • b) = D d a b := by
    have heq : (fun y ↦ α y ![Complex.I • a, Complex.I • b]) =ᶠ[nhds z]
        fun y ↦ α y ![a, b] := by
      filter_upwards [hone] with y hy
      exact hy a b
    exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L d) heq.fderiv_eq
  have hSwap (d a b : EuclideanSpace ℂ (Fin n)) :
      D d (Complex.I • a) b = -D d a (Complex.I • b) := by
    have heq : (fun y ↦ α y ![Complex.I • a, b]) =ᶠ[nhds z]
        fun y ↦ -(α y ![a, Complex.I • b]) := by
      filter_upwards [hone] with y hy
      have h := hy (Complex.I • a) b
      have hI : Complex.I • (Complex.I • a) = -a := by simp [smul_smul]
      rw [hI] at h
      have hNeg : α y ![-a, Complex.I • b] = -α y ![a, Complex.I • b] := by
        have hm := (α y).map_smul_univ ![(-1 : ℝ), 1] ![a, Complex.I • b]
        have ht : (fun i : Fin 2 ↦ ![(-1 : ℝ), 1] i • ![a, Complex.I • b] i) =
            ![-a, Complex.I • b] := by
          ext i
          fin_cases i <;> simp
        rw [ht] at hm
        simpa using hm
      rw [hNeg] at h
      linarith
    have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L d) heq.fderiv_eq
    simpa [D, fderiv_neg] using h
  have hA' : D u v (Complex.I • w) - D v u (Complex.I • w) =
      -D (Complex.I • w) u v := by linarith [hA]
  have hB' : D u v w - D v u w = -D w u v := by linarith [hB]
  have hC' : D (Complex.I • u) v (Complex.I • w) -
      D (Complex.I • v) u (Complex.I • w) = D w u v := by
    have h := hC
    change D (Complex.I • u) (Complex.I • v) w - D (Complex.I • v) (Complex.I • u) w +
      D w (Complex.I • u) (Complex.I • v) = 0 at h
    rw [hSwap (Complex.I • u) v w, hSwap (Complex.I • v) u w, hJ w u v] at h
    linarith
  have hE' : D (Complex.I • u) v w - D (Complex.I • v) u w =
      -D (Complex.I • w) u v := by
    have h := hE
    change D (Complex.I • u) (Complex.I • v) (Complex.I • w) -
      D (Complex.I • v) (Complex.I • u) (Complex.I • w) +
      D (Complex.I • w) (Complex.I • u) (Complex.I • v) = 0 at h
    rw [hJ (Complex.I • u) v w, hJ (Complex.I • v) u w,
      hJ (Complex.I • w) u v] at h
    linarith
  rw [hA', hB', hC', hE']
  push_cast
  ring

theorem chartPartialZComplex_coeffMatrix_symm
    {α : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ}
    {z : EuclideanSpace ℂ (Fin n)} (hα : ContDiffAt ℝ 1 α z)
    (hclosed : extDeriv α z = 0) (hone : ∀ᶠ y in nhds z, (α y).IsOneOne)
    (i j k : Fin n) :
    chartPartialZComplex (fun y ↦ (α y).coeffMatrix j k) z i =
      chartPartialZComplex (fun y ↦ (α y).coeffMatrix i k) z j := by
  let D := fun (d a b : EuclideanSpace ℂ (Fin n)) ↦
    fderiv ℝ (fun y ↦ α y ![a, b]) z d
  have h := closed_oneOne_partial_identity hα hclosed hone
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
  unfold chartPartialZComplex
  rw [fderiv_coeffMatrix_entry hα j k, fderiv_coeffMatrix_entry hα i k]
  simp only [_root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  push_cast at h ⊢
  simp only [Complex.ofRealCLM_apply, div_eq_mul_inv] at h ⊢
  norm_num [one_div] at h ⊢
  ring_nf at h ⊢
  simp [Complex.I_sq] at h ⊢
  linear_combination h / 2

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem chartRep_isOneOne (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (ω₀.toFormField.chartRep x z).IsOneOne := by
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
  rw [hchart]
  exact (ω₀.isOneOne y).compContinuousLinearMap AEquiv

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem kahler_chart_metric_symmetry (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (i j k : Fin n) :
    chartPartialZComplex (fun w ↦ ω₀.metricInChart x w j k) z i =
      chartPartialZComplex (fun w ↦ ω₀.metricInChart x w i k) z j := by
  let α := ω₀.toFormField.chartRep x
  have hαtop : ContDiffAt ℝ ∞ α z :=
    (ω₀.isSmooth x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)
  have hle : (1 : ℕ∞ω) ≤ ∞ := by
    change ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hα := hαtop.of_le hle
  have hclosed : extDeriv α z = 0 := by
    have hclosed0 : ω₀.toFormField.extDeriv = 0 := ω₀.isClosed
    have hzero := congrArg (fun β ↦ β.chartRep x z) hclosed0
    rw [FormField.chartRep_extDeriv ω₀.isSmooth x hz, FormField.chartRep_zero] at hzero
    exact hzero
  have hone : ∀ᶠ y in nhds z, (α y).IsOneOne := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hz] with y hy
    exact chartRep_isOneOne x hy
  simpa [α, metricInChart] using
    chartPartialZComplex_coeffMatrix_symm hα hclosed hone i j k

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem kahler_chart_cofactor_divergence (x : M) :
    ChartCofactorDivergenceFree (ω₀.metricInChart x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  intro z hz k
  let G := ω₀.metricInChart x
  let B := (G z)⁻¹
  let T := fun j a b ↦ chartPartialZComplex (fun w ↦ G w a b) z j
  have hBdef : (G z)⁻¹ = B := rfl
  have hle : (1 : ℕ∞ω) ≤ ∞ := by
    change ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hGentry : ∀ a b, ContDiffAt ℝ 1 (fun w ↦ G w a b) z := by
    intro a b
    exact (ω₀.contDiffOn_metricInChart x a b).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz) |>.of_le hle
  have hunit : IsUnit (G z) := (ω₀.posDef_metricInChart x hz).isUnit
  have hsymm : ∀ i a b, T i a b = T a i b := by
    intro i a b
    exact kahler_chart_metric_symmetry x hz i a b
  let H : Fin n → Matrix (Fin n) (Fin n) ℂ := fun j ↦
    Matrix.of (fun a b : Fin n ↦ T j a b)
  have htrace (j : Fin n) :
      Matrix.trace (B * H j) = ∑ a, ∑ b, B a b * T j b a := by
    simp [H, Matrix.trace, Matrix.mul_apply, T]
  have hprod (j : Fin n) :
      (B * (H j * B)) k j = ∑ a, ∑ b, B k a * T j a b * B b j := by
    simp only [Matrix.mul_apply, H, Matrix.of_apply, T]
    apply Finset.sum_congr rfl
    intro a ha
    simpa [mul_assoc] using (Fintype.sum_mul_sum (ι := Unit) (κ := Fin n)
      (fun _ : Unit ↦ B k a)
      (fun b : Fin n ↦ T j a b * B b j))
  let A := fun j : Fin n ↦ (∑ a, ∑ b, B a b * T j b a) * B k j
  let C := fun j : Fin n ↦ ∑ a, ∑ b, B k a * T j a b * B b j
  have hformula (j : Fin n) :
    chartPartialZComplex (fun w ↦ (G w).det * (G w)⁻¹ k j) z j =
        (G z).det * (A j - C j) := by
    have hf := chartCofactor_partial_formula hGentry hunit k j
    have hmat : Matrix.of (fun a b : Fin n ↦ T j a b) = H j := rfl
    rw [hBdef, hmat, htrace j, hprod j] at hf
    simpa [A, C, mul_assoc] using hf
  have hAsum : (∑ j, A j) = ∑ j, ∑ a, ∑ b, B a b * T j b a * B k j := by
    simp [A, Finset.sum_mul]
  calc
    _ = ∑ j, (G z).det * (A j - C j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hformula j
    _ = (G z).det * ((∑ j, A j) - ∑ j, C j) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    _ = 0 := by
      rw [hAsum]
      simp only [C]
      rw [cofactor_divergence_algebra B T hsymm k]
      simp

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
/-- Polarize the chart-diagonal trace identity to obtain the mixed Hermitian chart pairing. -/
theorem chartGradientPair_polarization_relTrace (ω₀ : KahlerForm n M) (i : M)
    (u v : M → ℝ)
    (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u)
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v)
    {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target) :
    chartGradientPair (ω₀.metricInChart i)
        (fun w ↦ u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm w))
        (fun w ↦ v ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm w)) z =
      (relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z))
          (mdWedgeDBar n (u + v) ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) -
        relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z))
          (mdWedgeDBar n u ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) -
        relTrace (ω₀ ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z))
          (mdWedgeDBar n v ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z))) / 2 := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
  let U : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ u (c.symm w)
  let V : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ v (c.symm w)
  have hUmd : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ U c.target := by
    have huMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u Set.univ :=
      contMDiffOn_univ.mpr hu
    exact huMD.comp (contMDiffOn_extChartAt_symm i) (by intro w hw; simp)
  have hVmd : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ V c.target := by
    have hvMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ v Set.univ :=
      contMDiffOn_univ.mpr hv
    exact hvMD.comp (contMDiffOn_extChartAt_symm i) (by intro w hw; simp)
  have hU₂ : ContDiffAt ℝ 2 U z := by
    have h := hUmd.contDiffOn.contDiffAt ((isOpen_extChartAt_target i).mem_nhds hz)
    exact h.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hV₂ : ContDiffAt ℝ 2 V z := by
    have h := hVmd.contDiffOn.contDiffAt ((isOpen_extChartAt_target i).mem_nhds hz)
    exact h.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hUdiff : DifferentiableAt ℝ U z := hU₂.differentiableAt (by norm_num)
  have hVdiff : DifferentiableAt ℝ V z := hV₂.differentiableAt (by norm_num)
  have hfd_add : fderiv ℝ (U + V) z = fderiv ℝ (fun w ↦ U w + V w) z := rfl
  have hpartialZ : chartPartialZ (U + V) z =
      chartPartialZ U z + chartPartialZ V z := by
    funext j
    simp only [chartPartialZ]
    rw [hfd_add, fderiv_fun_add hUdiff hVdiff]
    simp [chartPartialZ]
    ring
  have hpartialBar : chartPartialBar (U + V) z =
      chartPartialBar U z + chartPartialBar V z := by
    funext j
    simp only [chartPartialBar]
    rw [hfd_add, fderiv_fun_add hUdiff hVdiff]
    simp [chartPartialBar]
    ring
  have hvec : Matrix.vecMulVec (chartPartialZ U z + chartPartialZ V z)
      (chartPartialBar U z + chartPartialBar V z) =
      Matrix.vecMulVec (chartPartialZ U z) (chartPartialBar U z) +
        Matrix.vecMulVec (chartPartialZ U z) (chartPartialBar V z) +
        Matrix.vecMulVec (chartPartialZ V z) (chartPartialBar U z) +
        Matrix.vecMulVec (chartPartialZ V z) (chartPartialBar V z) := by
    ext a b
    simp [Matrix.vecMulVec]
    ring
  have hpairAdd : chartGradientPair (ω₀.metricInChart i) (U + V) (U + V) z =
      chartGradientPair (ω₀.metricInChart i) U U z +
        chartGradientPair (ω₀.metricInChart i) U V z +
        chartGradientPair (ω₀.metricInChart i) V U z +
        chartGradientPair (ω₀.metricInChart i) V V z := by
    simp only [chartGradientPair, hpartialZ, hpartialBar, hvec]
    simp [Matrix.mul_add, Matrix.trace_add, map_add]
  have hglobalUV :
      relTrace (ω₀ (c.symm z)) (mdWedgeDBar n (u + v) (c.symm z)) =
        chartGradientPair (ω₀.metricInChart i) (U + V) (U + V) z := by
    have h := (ω₀.chartGradientPair_eq_relTrace_mdWedgeDBar i (u + v) (hu.add hv) hz).symm
    have hfun : (fun w ↦ (u + v) (c.symm w)) = U + V := by
      funext w
      rfl
    rw [hfun] at h
    simpa [c] using h
  have hglobalU :
      relTrace (ω₀ (c.symm z)) (mdWedgeDBar n u (c.symm z)) =
        chartGradientPair (ω₀.metricInChart i) U U z := by
    simpa [c, U] using
      (ω₀.chartGradientPair_eq_relTrace_mdWedgeDBar i u hu hz).symm
  have hglobalV :
      relTrace (ω₀ (c.symm z)) (mdWedgeDBar n v (c.symm z)) =
        chartGradientPair (ω₀.metricInChart i) V V z := by
    simpa [c, V] using
      (ω₀.chartGradientPair_eq_relTrace_mdWedgeDBar i v hv hz).symm
  have hsymm := ω₀.chartGradientPair_symm i U V hz
  rw [hglobalUV, hglobalU, hglobalV, hpairAdd, hsymm]
  dsimp [U, V]
  ring

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
/-- A finite smooth partition has zero total mixed chart-gradient pairing against a fixed
function. The polarization is stated intrinsically using relTrace and mdWedgeDBar. -/
theorem chartGradientPair_partition_sum_zero (ω₀ : KahlerForm n M)
    (S : Finset M) (ρ : M → M → ℝ)
    (hρsum : ∀ y, ∑ i ∈ S, ρ i y = 1)
    (hρsmooth : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (ρ i))
    (g : M → ℝ) (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g)
    (y : M) :
    ∑ i ∈ S,
      (relTrace (ω₀ y) (mdWedgeDBar n (ρ i + g) y) -
        relTrace (ω₀ y) (mdWedgeDBar n (ρ i) y) -
        relTrace (ω₀ y) (mdWedgeDBar n g y)) / 2 = 0 := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let z := c y
  have hz : z ∈ c.target := mem_extChartAt_target y
  let U : M → EuclideanSpace ℂ (Fin n) → ℝ := fun i w ↦ ρ i (c.symm w)
  let V : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ g (c.symm w)
  have hUon (i : M) : ContDiffOn ℝ ∞ (U i) c.target := by
    have hρMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
        (ρ i) Set.univ := contMDiffOn_univ.mpr (hρsmooth i)
    exact (hρMD.comp (contMDiffOn_extChartAt_symm y) (by intro w hw; simp)).contDiffOn
  have hUdiff (i : M) (hi : i ∈ S) : DifferentiableAt ℝ (U i) z := by
    have hU₂ : ContDiffAt ℝ 2 (U i) z :=
      ((hUon i).contDiffAt ((isOpen_extChartAt_target y).mem_nhds hz)).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact hU₂.differentiableAt (by norm_num)
  let sumU : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ ∑ i ∈ S, U i w
  have hsumUloc : sumU =ᶠ[nhds z] fun _ ↦ (1 : ℝ) := by
    filter_upwards [(isOpen_extChartAt_target y).mem_nhds hz] with w hw
    simpa [sumU, U] using hρsum (c.symm w)
  have hfdSum : fderiv ℝ sumU z = ∑ i ∈ S, fderiv ℝ (U i) z := by
    simpa [sumU] using fderiv_fun_sum (u := S) (fun i hi ↦ hUdiff i hi)
  have hfdConst : fderiv ℝ sumU z = 0 := by
    calc
      _ = fderiv ℝ (fun _ : EuclideanSpace ℂ (Fin n) ↦ (1 : ℝ)) z :=
        hsumUloc.fderiv_eq
      _ = 0 := by simp
  have hpairSum := chartGradientPair_sum_first (ω₀.metricInChart y) S U V z
    (fun i hi ↦ hUdiff i hi)
  have hpairZero : chartGradientPair (ω₀.metricInChart y) sumU V z = 0 := by
    have hpartialZzero : chartPartialZ sumU z = 0 := by
      funext j
      simp [chartPartialZ, hfdConst]
    unfold chartGradientPair
    rw [hpartialZzero]
    have hvecZero : Matrix.vecMulVec (0 : Fin n → ℂ) (chartPartialBar V z) = 0 := by
      ext a b
      simp [Matrix.vecMulVec]
    rw [hvecZero]
    simp
  have hpolar (i : M) (hi : i ∈ S) :
      (relTrace (ω₀ y) (mdWedgeDBar n (ρ i + g) y) -
        relTrace (ω₀ y) (mdWedgeDBar n (ρ i) y) -
        relTrace (ω₀ y) (mdWedgeDBar n g y)) / 2 =
        chartGradientPair (ω₀.metricInChart y) (U i) V z := by
    have hp := ω₀.chartGradientPair_polarization_relTrace y (ρ i) g
      (hρsmooth i) hg hz
    have hleft : c.symm z = y := c.left_inv (mem_extChartAt_source y)
    rw [hleft] at hp
    simpa only [U, V] using hp.symm
  calc
    ∑ i ∈ S,
        (relTrace (ω₀ y) (mdWedgeDBar n (ρ i + g) y) -
          relTrace (ω₀ y) (mdWedgeDBar n (ρ i) y) -
          relTrace (ω₀ y) (mdWedgeDBar n g y)) / 2 =
      ∑ i ∈ S, chartGradientPair (ω₀.metricInChart y) (U i) V z := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpolar i hi
    _ = chartGradientPair (ω₀.metricInChart y) sumU V z := hpairSum.symm
    _ = 0 := hpairZero

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] in
theorem chartPolarization_zero_of_not_source (ω₀ : KahlerForm n M)
    (r g : M → ℝ)
    (hr : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ r)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g)
    {y : M} (hy : y ∉ tsupport r) :
    (relTrace (ω₀ y) (mdWedgeDBar n (r + g) y) -
      relTrace (ω₀ y) (mdWedgeDBar n r y) -
      relTrace (ω₀ y) (mdWedgeDBar n g y)) / 2 = 0 := by
  let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let z := c y
  let U : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ r (c.symm w)
  let V : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ g (c.symm w)
  have hz : z ∈ c.target := mem_extChartAt_target y
  have hleft : c.symm z = y := c.left_inv (mem_extChartAt_source y)
  have hopen : (tsupport r)ᶜ ∈ nhds y :=
    (isClosed_tsupport r).isOpen_compl.mem_nhds hy
  have hzero {x : M} (hx : x ∉ tsupport r) : r x = 0 := by
    by_contra hne
    exact hx (subset_tsupport _ hne)
  have hpre : c.symm ⁻¹' (tsupport r)ᶜ ∈ nhds z := by
    have hopen' : (tsupport r)ᶜ ∈ nhds (c.symm z) := by simpa [hleft] using hopen
    exact (continuousAt_extChartAt_symm y).preimage_mem_nhds hopen'
  have hUzero : U =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hpre] with w hw
    exact hzero hw
  have hfdU : fderiv ℝ U z = 0 := by
    rw [hUzero.fderiv_eq]
    simp
  have hpartialZero : chartPartialZ U z = 0 := by
    funext j
    simp [chartPartialZ, hfdU]
  have hvecZero : Matrix.vecMulVec (0 : Fin n → ℂ) (chartPartialBar V z) = 0 := by
    ext a b
    simp [Matrix.vecMulVec]
  have hpairZero : chartGradientPair (ω₀.metricInChart y) U V z = 0 := by
    unfold chartGradientPair
    rw [hpartialZero, hvecZero]
    simp
  have hp := ω₀.chartGradientPair_polarization_relTrace y r g hr hg hz
  rw [hleft] at hp
  have hq :
      chartGradientPair (ω₀.metricInChart y) U V z =
        (relTrace (ω₀ y) (mdWedgeDBar n (r + g) y) -
          relTrace (ω₀ y) (mdWedgeDBar n r y) -
          relTrace (ω₀ y) (mdWedgeDBar n g y)) / 2 := by
    simpa only [U, V] using hp
  exact hq.symm.trans hpairZero
omit [MeasurableSpace M] [BorelSpace M] [T2Space M] in
/-- Construct a compactly supported chart cutoff and global smooth extensions of two functions.
The cutoff agrees with the given function on the chart target, and the extensions agree with the
chart pullbacks on a neighborhood of its support. -/
theorem exists_chart_cutoff_extensions
    (i : M) (r f g : M → ℝ)
    (hr : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ r)
    (hsource : tsupport r ⊆ (chartAt (EuclideanSpace ℂ (Fin n)) i).source)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ g) :
    ∃ (χ β : EuclideanSpace ℂ (Fin n) → ℝ)
      (O : Set (EuclideanSpace ℂ (Fin n)))
      (U V : EuclideanSpace ℂ (Fin n) → ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
        tsupport χ ⊆
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i) '' tsupport r ∧
      (∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
        χ z = r ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) ∧
      ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
        tsupport β ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
      IsOpen O ∧
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i '' tsupport r) ⊆ O ∧
        O ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
        (∀ z ∈ O, β z = 1) ∧
      ContDiff ℝ ∞ U ∧
        EqOn U (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) O ∧
      ContDiff ℝ ∞ V ∧
        EqOn V (fun z ↦ g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) O := by
  classical
  have hcutoff :
      ∃ χ : EuclideanSpace ℂ (Fin n) → ℝ,
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
          tsupport χ ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
          tsupport χ ⊆
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i) '' tsupport r ∧
          (∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
            χ z = r ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) ∧
        ∃ β : EuclideanSpace ℂ (Fin n) → ℝ,
          ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
            tsupport β ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
          ∃ O : Set (EuclideanSpace ℂ (Fin n)), IsOpen O ∧
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i '' tsupport (r)) ⊆ O ∧
            O ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
            ∀ z ∈ O, β z = 1 := by
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
    let χ : EuclideanSpace ℂ (Fin n) → ℝ :=
      fun z ↦ if z ∈ c.target then r (c.symm z) else 0
    have hρsource : tsupport (r) ⊆ c.source := by
      simpa [c, ← extChartAt_source] using hsource
    have hρcompact : IsCompact (tsupport (r)) :=
      (isClosed_tsupport (r)).isCompact
    let K : Set (EuclideanSpace ℂ (Fin n)) := c '' tsupport (r)
    have hK : IsCompact K :=
      hρcompact.image_of_continuousOn ((continuousOn_extChartAt i).mono hρsource)
    have hKtarget : K ⊆ c.target := by
      rintro z ⟨y, hy, rfl⟩
      exact c.map_source (hρsource hy)
    have hχsupport : Function.support χ ⊆ K := by
      intro z hz
      change χ z ≠ 0 at hz
      have hzt : z ∈ c.target := by
        by_contra hnot
        exact hz (by simp [χ, hnot])
      have hy : c.symm z ∈ tsupport (r) := by
        apply subset_tsupport
        have hρnz : r (c.symm z) ≠ 0 := by simpa [χ, hzt] using hz
        exact hρnz
      exact ⟨c.symm z, hy, c.right_inv hzt⟩
    have hχtsupport : tsupport χ ⊆ K := by
      rw [tsupport]
      exact (closure_mono hχsupport).trans hK.isClosed.closure_subset
    have hχcompact : HasCompactSupport χ := HasCompactSupport.intro hK (by
      intro z hz
      by_contra hne
      exact hz (hχsupport (Function.mem_support.mpr hne)))
    have hχtarget : tsupport χ ⊆ c.target := hχtsupport.trans hKtarget
    have hχon : ContDiffOn ℝ ∞ (fun z ↦ r (c.symm z)) c.target := by
      have hρMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (r) Set.univ :=
        contMDiffOn_univ.mpr hr
      exact (hρMD.comp (contMDiffOn_extChartAt_symm i) (by intro z hz; simp)).contDiffOn
    have hχcont : ContDiff ℝ ∞ χ := by
      apply contDiff_iff_contDiffAt.mpr
      intro z
      by_cases hz : z ∈ c.target
      · have heq : χ =ᶠ[nhds z] fun w ↦ r (c.symm w) := by
          filter_upwards [(isOpen_extChartAt_target i).mem_nhds hz] with w hw
          have hw' : w ∈ c.target := by simpa [c] using hw
          simp [χ, hw']
        exact (hχon.contDiffAt ((isOpen_extChartAt_target i).mem_nhds hz)).congr_of_eventuallyEq heq
      · have hzK : z ∉ K := fun hzK ↦ hz (hKtarget hzK)
        have heq : χ =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
          filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
          have hwzero : χ w = 0 := by
            by_contra hne
            exact hw (hχsupport (Function.mem_support.mpr hne))
          exact hwzero
        exact contDiff_const.contDiffAt.congr_of_eventuallyEq heq
    have hplateau : ∃ β : EuclideanSpace ℂ (Fin n) → ℝ,
        ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ c.target ∧
          ∃ O : Set (EuclideanSpace ℂ (Fin n)), IsOpen O ∧ K ⊆ O ∧ O ⊆ c.target ∧
            ∀ z ∈ O, β z = 1 := by
      by_cases hKne : K.Nonempty
      · let Ix := {z // z ∈ K}
        have hbump (x : Ix) : ∃ b : EuclideanSpace ℂ (Fin n) → ℝ,
            tsupport b ⊆ c.target ∧ HasCompactSupport b ∧ ContDiff ℝ ∞ b ∧
              Set.range b ⊆ Set.Icc 0 1 ∧ b x = 1 :=
          exists_contDiff_tsupport_subset ((isOpen_extChartAt_target i).mem_nhds (hKtarget x.2))
        choose b hbsupp hbcomp hbcont hbrange hbvalue using hbump
        let V : Ix → Set (EuclideanSpace ℂ (Fin n)) := fun x ↦ {z | 0 < b x z}
        have hVopen (x : Ix) : IsOpen (V x) := isOpen_lt continuous_const (hbcont x).continuous
        have hcover : K ⊆ ⋃ x : Ix, V x := by
          intro z hz
          let x : Ix := ⟨z, hz⟩
          refine Set.mem_iUnion.2 ⟨x, ?_⟩
          change 0 < b x z
          rw [hbvalue x]
          norm_num
        obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVopen hcover
        let s : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ ∑ x ∈ t, b x z
        have hscont : ContDiff ℝ ∞ s := by
          dsimp [s]
          exact ContDiff.sum fun x hx ↦ hbcont x
        have hbn (x : Ix) (z : EuclideanSpace ℂ (Fin n)) : 0 ≤ b x z :=
          (hbrange x ⟨z, rfl⟩).1
        have hsnonneg (z : EuclideanSpace ℂ (Fin n)) : 0 ≤ s z := by
          simp only [s]
          exact Finset.sum_nonneg fun x hx ↦ hbn x z
        have hspos {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) : 0 < s z := by
          rcases Set.mem_iUnion₂.1 (ht hz) with ⟨x, hxt, hxV⟩
          have hbx : 0 < b x z := by simpa [V] using hxV
          change 0 < ∑ x ∈ t, b x z
          exact (Finset.sum_pos_iff_of_nonneg (fun y hy ↦ hbn y z)).2 ⟨x, hxt, hbx⟩
        let K' : Set (EuclideanSpace ℂ (Fin n)) := ⋃ x ∈ t, tsupport (b x)
        have hK' : IsCompact K' := t.isCompact_biUnion fun x hx ↦ hbcomp x
        have hK'target : K' ⊆ c.target := by
          intro z hz
          rcases Set.mem_iUnion₂.1 hz with ⟨x, hxt, hzx⟩
          exact hbsupp x hzx
        have hsuppS : Function.support s ⊆ K' := by
          intro z hz
          change s z ≠ 0 at hz
          by_contra hzK'
          have hzero (x : Ix) (hx : x ∈ t) : b x z = 0 := by
            have hnot : z ∉ tsupport (b x) := by
              intro hz'
              exact hzK' (Set.mem_iUnion₂.2 ⟨x, hx, hz'⟩)
            have hnot' : z ∉ Function.support (b x) := fun hz' ↦ hnot (subset_tsupport _ hz')
            exact not_not.mp hnot'
          have hsumzero : s z = 0 := by
            dsimp [s]
            exact Finset.sum_eq_zero fun x hx ↦ hzero x hx
          exact hz hsumzero
        have hsZero {z : EuclideanSpace ℂ (Fin n)} (hz : z ∉ K') : s z = 0 := by
          by_contra hne
          exact hz (hsuppS (Function.mem_support.mpr hne))
        obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hscont.continuous.continuousOn
        let δ : ℝ := s z₀ / 2
        have hδ : 0 < δ := by dsimp [δ]; linarith [hspos hz₀]
        let β : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ Real.smoothTransition (s z / δ)
        have hβcont : ContDiff ℝ ∞ β := by
          dsimp [β]
          exact Real.smoothTransition.contDiff.comp (hscont.mul contDiff_const)
        have hβone {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) : β z = 1 := by
          dsimp [β, δ]
          rw [Real.smoothTransition.one_of_one_le]
          apply (one_le_div hδ).2
          calc
            δ ≤ s z₀ := by dsimp [δ]; linarith [hspos hz₀]
            _ ≤ s z := hmin hz
        have hβloc {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) :
            β =ᶠ[nhds z] fun _ ↦ (1 : ℝ) := by
          have hzδ : δ < s z := by calc
            δ < s z₀ := by dsimp [δ]; linarith [hspos hz₀]
            _ ≤ s z := hmin hz
          have hneigh : {w | δ < s w} ∈ nhds z :=
            (isOpen_lt continuous_const hscont.continuous).mem_nhds hzδ
          filter_upwards [hneigh] with w hw
          dsimp [β]
          exact Real.smoothTransition.one_of_one_le ((one_le_div hδ).2 hw.le)
        have hβsupport : Function.support β ⊆ K' := by
          intro z hz
          change β z ≠ 0 at hz
          by_contra hzK'
          have hzzero := hsZero hzK'
          exact hz (by simp [β, hzzero, Real.smoothTransition.zero])
        have hβtsupport : tsupport β ⊆ K' := by
          rw [tsupport]
          exact (closure_mono hβsupport).trans hK'.isClosed.closure_subset
        have hβcompact : HasCompactSupport β := HasCompactSupport.intro hK' (by
          intro z hz
          by_contra hne
          exact hz (hβsupport (Function.mem_support.mpr hne)))
        let O : Set (EuclideanSpace ℂ (Fin n)) := {z | δ < s z}
        have hOopen : IsOpen O := by dsimp [O]; exact isOpen_lt continuous_const hscont.continuous
        have hOK : K ⊆ O := by
          intro z hz
          dsimp [O]
          calc
            δ < s z₀ := by dsimp [δ]; linarith [hspos hz₀]
            _ ≤ s z := hmin hz
        have hOtarget : O ⊆ c.target := by
          intro z hz
          have hspos' : s z ≠ 0 := ne_of_gt (lt_trans hδ hz)
          have hzK' : z ∈ K' := hsuppS (Function.mem_support.mpr hspos')
          exact hK'target hzK'
        have hβoneO : ∀ z ∈ O, β z = 1 := by
          intro z hz
          dsimp [O] at hz
          dsimp [β]
          exact Real.smoothTransition.one_of_one_le ((one_le_div hδ).2 hz.le)
        exact ⟨β, hβcont, hβcompact, hβtsupport.trans hK'target,
          O, hOopen, hOK, hOtarget, hβoneO⟩
      · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
        refine ⟨0, contDiff_const, ?_, by simp, ∅, isOpen_empty, ?_, empty_subset _, ?_⟩
        · exact HasCompactSupport.intro isCompact_empty (by intro z _; simp)
        · simp [hKempty]
        · simp
    obtain ⟨β, hβcont, hβcompact, hβsupport, O, hOopen, hOK, hOtarget, hβoneO⟩ := hplateau
    have hχeq : ∀ z ∈ c.target, χ z = r (c.symm z) := by
      intro z hz
      simp [χ, hz]
    exact ⟨χ, hχcont, hχcompact, hχtarget, hχtsupport, hχeq, β, hβcont, hβcompact, hβsupport,
      O, hOopen, hOK, hOtarget, hβoneO⟩
  have hchartExtensions :
      ∃ (χ β : EuclideanSpace ℂ (Fin n) → ℝ)
        (O : Set (EuclideanSpace ℂ (Fin n)))
        (U V : EuclideanSpace ℂ (Fin n) → ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
      tsupport χ ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i) '' tsupport r ∧
      (∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target,
          χ z = r ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) ∧
        ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
          tsupport β ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
        IsOpen O ∧
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i '' tsupport (r)) ⊆ O ∧
          O ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).target ∧
          (∀ z ∈ O, β z = 1) ∧
          ContDiff ℝ ∞ U ∧
            EqOn U (fun z ↦ f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) O ∧
          ContDiff ℝ ∞ V ∧
            EqOn V (fun z ↦ g ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i).symm z)) O := by
    obtain ⟨χ, hχ, hχcompact, hχsupport, hχK, hχeq, β, hβ, hβcompact, hβsupport,
      O, hOopen, hOK, hOtarget, hβone⟩ := hcutoff
    let c := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) i
    have hmake (u : M → ℝ) (hu : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u) :
        ∃ U : EuclideanSpace ℂ (Fin n) → ℝ, ContDiff ℝ ∞ U ∧
          EqOn U (fun z ↦ u (c.symm z)) O := by
      let F : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ u (c.symm z)
      let U : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ u i + β z * (F z - u i)
      have hFOn : ContDiffOn ℝ ∞ F c.target := by
        have huMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ u Set.univ :=
          contMDiffOn_univ.mpr hu
        exact (huMD.comp (contMDiffOn_extChartAt_symm i) (by intro z hz; simp)).contDiffOn
      have hUOn : ContDiffOn ℝ ∞ U c.target := by
        change ContDiffOn ℝ ∞ (fun z ↦ (fun _ ↦ u i) z + β z * (F z - (fun _ ↦ u i) z)) _
        exact contDiffOn_const.add (hβ.contDiffOn.mul (hFOn.sub contDiffOn_const))
      have hUcont : ContDiff ℝ ∞ U := by
        apply contDiff_iff_contDiffAt.mpr
        intro z
        by_cases hz : z ∈ c.target
        · exact hUOn.contDiffAt ((isOpen_extChartAt_target i).mem_nhds hz)
        · have hβzero : β =ᶠ[nhds z] fun _ ↦ (0 : ℝ) := by
            filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds
              (fun hzβ ↦ hz (hβsupport hzβ))] with w hw
            have hwzero : β w = 0 := by
              by_contra hne
              exact hw (subset_tsupport β (Function.mem_support.mpr hne))
            exact hwzero
          have hUeq : U =ᶠ[nhds z] fun _ ↦ u i := by
            filter_upwards [hβzero] with w hw
            simp [U, hw]
          exact (contDiff_const.contDiffAt).congr_of_eventuallyEq hUeq
      have hUEq : EqOn U F O := by
        intro z hz
        simp [U, F, hβone z hz]
      exact ⟨U, hUcont, fun z hz ↦ by simpa [F] using hUEq hz⟩
    obtain ⟨U, hU, hUEq⟩ := hmake f hf
    obtain ⟨V, hV, hVEq⟩ := hmake g hg
    exact ⟨χ, β, O, U, V, hχ, hχcompact, hχsupport, hχK, hχeq, hβ, hβcompact, hβsupport,
      hOopen, hOK, hOtarget, hβone, hU, hUEq, hV, hVEq⟩
  exact hchartExtensions

end KahlerForm
