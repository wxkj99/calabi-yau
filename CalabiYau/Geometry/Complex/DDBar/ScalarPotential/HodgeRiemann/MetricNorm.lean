module

public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.Geometry.Complex.DDBar.HermitianAdjoint
public import CalabiYau.Geometry.Kahler.Riemannian.Metric

/-!
# Squared norm of real `(1,1)`-forms

The coefficient matrix convention is `a' = Cᵀ a conjugate(C)` under a complex-linear
change of coordinates. The square trace `Re tr((g⁻¹a)²)` is invariant under
simultaneous pullback of the positive form and the real `(1,1)`-form. In a common
normal frame it is `∑ λᵢ²`, equal to the *induced real Riemannian metric* squared
norm of the corresponding two-form, normalized by `2!`.
-/

open Matrix
open scoped Manifold ContDiff

@[expose] public section

namespace ContinuousAlternatingMap

/-- The squared norm trace in Hermitian-matrix coefficients. This is not the
fixed-background Euclidean norm of the coefficient matrix. -/
noncomputable def hodgeNormSq {n : ℕ}
    (ω₀ γ : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) : ℝ :=
  RCLike.re (((ω₀.coeffMatrix)⁻¹ * γ.coeffMatrix) ^ 2).trace

/-- An arbitrary invertible matrix simultaneously changing two Hermitian coefficient
matrices preserves the trace-square of their relative endomorphism. No positivity
or unitary-frame premise is needed for this purely algebraic identity. -/
private theorem traceSquare_pullback_invariant {n : ℕ}
    (G H C : Matrix (Fin n) (Fin n) ℂ) (hC : IsUnit C) :
    RCLike.re (((Cᵀ * G * C.map star)⁻¹ * (Cᵀ * H * C.map star)) ^ 2).trace =
      RCLike.re ((G⁻¹ * H) ^ 2).trace := by
  let D : Matrix (Fin n) (Fin n) ℂ := Cᵀ
  let B : Matrix (Fin n) (Fin n) ℂ := C.map star
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC
  have hDunit : IsUnit D := by
    apply (Matrix.isUnit_iff_isUnit_det D).mpr
    rw [Matrix.det_transpose]
    exact hCdet
  have hBunit : IsUnit B := by
    apply (Matrix.isUnit_iff_isUnit_det B).mpr
    change IsUnit (C.map star).det
    rw [show (C.map star).det = star C.det by
      simpa using ((starRingEnd ℂ).map_det C).symm]
    exact hCdet.map (starRingEnd ℂ)
  have hDdetUnit : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDunit
  have hBdetUnit : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  have hDinv : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hDdetUnit
  have hBBinv : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBdetUnit
  have hconj :
      (D * G * B)⁻¹ * (D * H * B) = B⁻¹ * (G⁻¹ * H) * B := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    conv_lhs =>
      arg 2
      arg 2
      rw [← Matrix.mul_assoc]
    rw [hDinv]
    simp
  have hsq : (B⁻¹ * (G⁻¹ * H) * B) ^ 2 =
      B⁻¹ * ((G⁻¹ * H) ^ 2) * B := by
    rw [pow_two]
    calc
      (B⁻¹ * (G⁻¹ * H) * B) * (B⁻¹ * (G⁻¹ * H) * B) =
          B⁻¹ * (G⁻¹ * H) * (B * B⁻¹) * (G⁻¹ * H) * B := by
        simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (G⁻¹ * H) * (G⁻¹ * H) * B := by rw [hBBinv, Matrix.mul_one]
      _ = B⁻¹ * ((G⁻¹ * H) ^ 2) * B := by
        rw [pow_two, ← Matrix.mul_assoc B⁻¹ (G⁻¹ * H) (G⁻¹ * H)]
  rw [show Cᵀ * G * C.map star = D * G * B by rfl,
    show Cᵀ * H * C.map star = D * H * B by rfl, hconj, hsq]
  exact congrArg RCLike.re (Matrix.trace_conj' hBunit ((G⁻¹ * H) ^ 2))

/-- Simultaneous complex-linear changes of frame preserve the matrix trace square. -/
theorem hodgeNormSq_compContinuousLinearMap {n : ℕ}
    (ω₀ γ : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hω₀ : ω₀.IsPositive) (hγ : γ.IsOneOne)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n)) :
    hodgeNormSq
      (ω₀.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ))
      (γ.compContinuousLinearMap (A.toContinuousLinearMap.restrictScalars ℝ)) =
    hodgeNormSq ω₀ γ := by
  let C : Matrix (Fin n) (Fin n) ℂ :=
    EuclideanSpace.clmMatrix A.toContinuousLinearMap
  let b : Module.Basis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let Ae : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := A.toLinearEquiv
  have hC : C = LinearMap.toMatrix b b
      (Ae : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
    ext i j
    change A (EuclideanSpace.single j 1) i = _
    rw [LinearMap.toMatrix_apply]
    simp [b, Ae, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have hCdet : C.det ≠ 0 := by
    rw [hC, LinearMap.det_toMatrix]
    simpa only [LinearEquiv.coe_det] using (LinearEquiv.det Ae).ne_zero
  have hCunit : IsUnit C :=
    (Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hCdet)
  have hω₀c := hω₀.1.coeffMatrix_compContinuousLinearMap A.toContinuousLinearMap
  have hγc := hγ.coeffMatrix_compContinuousLinearMap A.toContinuousLinearMap
  change RCLike.re ((((ω₀.compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix)⁻¹ *
      (γ.compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix) ^ 2).trace =
    RCLike.re ((ω₀.coeffMatrix⁻¹ * γ.coeffMatrix) ^ 2).trace
  rw [hω₀c, hγc]
  change RCLike.re (((Cᵀ * ω₀.coeffMatrix * C.map star)⁻¹ *
      (Cᵀ * γ.coeffMatrix * C.map star)) ^ 2).trace = _
  exact traceSquare_pullback_invariant ω₀.coeffMatrix γ.coeffMatrix C hCunit

/-- In a simultaneous normal frame the algebraic trace is the sum of squares. -/
theorem hodgeNormSq_eq_eigenvalues {n : ℕ}
    (ω₀ γ : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hω₀ : ω₀.IsPositive) (hγ : γ.IsOneOne)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (lam : Fin n → ℝ)
    (hAω₀ : (ω₀.compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix = 1)
    (hAγ : (γ.compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix =
        Matrix.diagonal (fun i => (lam i : ℂ))) :
    hodgeNormSq ω₀ γ = ∑ i, (lam i) ^ 2 := by
  rw [← hodgeNormSq_compContinuousLinearMap ω₀ γ hω₀ hγ A]
  simp [hodgeNormSq, hAω₀, hAγ, pow_two,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

end ContinuousAlternatingMap

end

namespace ContinuousAlternatingMap

section FrameContraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Module.Finite ℝ E] in
private theorem full_frame_reconstruction
    (g : CalabiYau.SmoothRiemannianMetric I M) (x : M) (b : ι → E)
    (hb : Submodule.span ℝ (Set.range b) = ⊤)
    (hgram : ∀ p q, CalabiYau.L2.modelInnerAt (I := I) g x (b p) (b q) =
      if p = q then 2 else 0) (v : E) :
    ∑ p, ((CalabiYau.L2.modelInnerAt (I := I) g x v (b p)) / 2) • b p = v := by
  have hv : v ∈ Submodule.span ℝ (Set.range b) := by rw [hb]; trivial
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨q, rfl⟩ := hw
      simp [hgram, ite_div, ite_smul, eq_comm]
  | zero => simp
  | add u v hu hv ihu ihv =>
      simp only [map_add, _root_.add_apply, add_div, add_smul,
        Finset.sum_add_distrib, ihu, ihv]
  | smul c u hu ihu =>
      simp only [map_smul, _root_.smul_apply, smul_eq_mul]
      calc
        _ = c • ∑ p, (CalabiYau.L2.modelInnerAt (I := I) g x u (b p) / 2) • b p := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro p _
          rw [smul_smul]
          congr 1
          ring
        _ = c • u := by rw [ihu]

omit [Module.Finite ℝ E] in
private theorem tensor_two_basis_expansion
    {κ : Type*} [Fintype κ] (e : Module.Basis κ ℝ E)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) (u v : E) :
    S ![u, v] = ∑ i, ∑ k, e.repr u i * S ![e i, e k] * e.repr v k := by
  classical
  conv_lhs => rw [← e.sum_repr u, ← e.sum_repr v]
  change ((S.curryLeft (∑ i, e.repr u i • e i)).curryLeft
    (∑ k, e.repr v k • e k)) ![] = _
  simp only [_root_.map_sum, _root_.map_smul, _root_.sum_apply, _root_.smul_apply,
    ContinuousMultilinearMap.curryLeft_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  have hcons : Fin.cons (e i) (Fin.cons (e k) ![]) = ![e i, e k] := by
    ext a
    fin_cases a <;> rfl
  rw [hcons]
  ring

private theorem full_frame_inverse_coordinates
    (g : CalabiYau.SmoothRiemannianMetric I M) (x : M) (b : ι → E)
    (hb : Submodule.span ℝ (Set.range b) = ⊤)
    (hgram : ∀ p q, CalabiYau.L2.modelInnerAt (I := I) g x (b p) (b q) =
      if p = q then 2 else 0) :
    let e := CalabiYau.Tensor.Coordinates.chartModelBasis E
    let C : Matrix (Fin (Module.finrank ℝ E)) ι ℝ := fun i p => e.repr (b p) i
    (CalabiYau.L2.gramMatrixAt (I := I) g x)⁻¹ = (1 / 2 : ℝ) • (C * Cᵀ) := by
  classical
  let e := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let C : Matrix (Fin (Module.finrank ℝ E)) ι ℝ := fun i p => e.repr (b p) i
  let G := CalabiYau.L2.gramMatrixAt (I := I) g x
  change G⁻¹ = (1 / 2 : ℝ) • (C * Cᵀ)
  have hmetric (p : ι) (j : Fin (Module.finrank ℝ E)) :
      CalabiYau.L2.modelInnerAt (I := I) g x (b p) (e j) =
      ∑ k, C k p * G k j := by
    conv_lhs => rw [← e.sum_repr (b p)]
    simp only [_root_.map_sum, _root_.sum_apply, _root_.map_smul, _root_.smul_apply, smul_eq_mul]
    rfl
  have hrec (i j : Fin (Module.finrank ℝ E)) :
      ∑ p, (CalabiYau.L2.modelInnerAt (I := I) g x (b p) (e j) / 2) * C i p =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i j := by
    have h := congrArg (fun v : E => e.repr v i)
      (full_frame_reconstruction g x b hb hgram (e j))
    simp only [_root_.map_sum, _root_.map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul, Module.Basis.repr_self, Finsupp.single_apply] at h
    have hswap (p : ι) : CalabiYau.L2.modelInnerAt (I := I) g x (e j) (b p) =
        CalabiYau.L2.modelInnerAt (I := I) g x (b p) (e j) :=
      CalabiYau.L2.modelInnerAt_symm g x _ _
    simp_rw [hswap] at h
    simpa only [Matrix.one_apply, C, eq_comm] using h
  apply Matrix.inv_eq_left_inv
  ext i j
  rw [← hrec i j]
  simp_rw [hmetric]
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem contraction_coordinate_sums
    {κ ν : Type*} [Fintype κ] [Fintype ν]
    (C : Matrix κ ν ℝ) (S T : Matrix κ κ ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      (∑ p, C i p * C j p) * (∑ q, C k q * C l q) * S i k * T j l) =
    ∑ p, ∑ q,
      (∑ i, ∑ k, C i p * S i k * C k q) *
      (∑ j, ∑ l, C j p * T j l * C l q) := by
  classical
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, i, 2, j, 2, k, 2, l]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j, 2, k]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, p, 2, i, 2, j, 2, k]; rw [Finset.sum_comm]
  conv_lhs => enter [2, p, 2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, p, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, p]; rw [Finset.sum_comm]
  conv_lhs => enter [2, p, 2, q]; rw [Finset.sum_comm]
  conv_lhs => enter [2, p, 2, q, 2, j, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, p, 2, q, 2, j]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem covariantTensorInnerPointwise_two_of_spanning_gram_two
    (g : CalabiYau.SmoothRiemannianMetric I M) (x : M) (b : ι → E)
    (hb : Submodule.span ℝ (Set.range b) = ⊤)
    (hgram : ∀ p q, CalabiYau.L2.modelInnerAt (I := I) g x (b p) (b q) =
      if p = q then 2 else 0)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) :
    CalabiYau.L2.covariantTensorInnerPointwise (I := I) 2 g x S T =
      (1 / 4 : ℝ) * ∑ p : ι, ∑ q : ι, S ![b p, b q] * T ![b p, b q] := by
  classical
  let e := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let C : Matrix (Fin (Module.finrank ℝ E)) ι ℝ := fun i p => e.repr (b p) i
  let G := CalabiYau.L2.gramMatrixAt (I := I) g x
  let Sm : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i k => S ![e i, e k]
  let Tm : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun j l => T ![e j, e l]
  have hcons (u v : E) : Fin.cons u
      (Fin.cons v (fun i : Fin 0 => Fin.elim0 i)) = ![u, v] := by
    ext i
    fin_cases i <;> rfl
  have hcons1 (u : E) : Fin.cons u (fun i : Fin 0 => Fin.elim0 i) = ![u] := by
    ext i
    fin_cases i; rfl
  have hinner (U V : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) :
      CalabiYau.L2.covariantTensorInnerPointwise (I := I) 1 g x U V =
        ∑ k, ∑ l, (CalabiYau.L2.gramMatrixAt (I := I) g x)⁻¹ k l * U ![e k] * V ![e l] := by
    change CalabiYau.L2.covariantTensorInnerPointwise (I := I) (0 + 1) g x U V = _
    rw [CalabiYau.L2.tensorInnerPointwise_0s_succ]
    simp only [CalabiYau.L2.tensorInnerPointwise_0s_zero_arity,
      ContinuousMultilinearMap.curryLeft_apply, hcons1]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hraw : CalabiYau.L2.covariantTensorInnerPointwise (I := I) 2 g x S T =
      ∑ i, ∑ j, ∑ k, ∑ l, G⁻¹ i j * G⁻¹ k l * Sm i k * Tm j l := by
    change CalabiYau.L2.covariantTensorInnerPointwise (I := I) (1 + 1) g x S T = _
    rw [CalabiYau.L2.tensorInnerPointwise_0s_succ]
    simp_rw [hinner]
    simp_rw [ContinuousMultilinearMap.curryLeft_apply]
    simp_rw [← hcons1, hcons]
    dsimp [Sm, Tm]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    dsimp [G]
    ring
  have hi (i j : Fin (Module.finrank ℝ E)) :
      G⁻¹ i j = (1 / 2 : ℝ) * ∑ p, C i p * C j p := by
    have hh := full_frame_inverse_coordinates g x b hb hgram
    change G⁻¹ = (1 / 2 : ℝ) • (C * Cᵀ) at hh
    rw [hh]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
  have hs (p q : ι) :
      S ![b p, b q] = ∑ i, ∑ k, C i p * Sm i k * C k q :=
    tensor_two_basis_expansion e S (b p) (b q)
  have ht (p q : ι) :
      T ![b p, b q] = ∑ j, ∑ l, C j p * Tm j l * C l q :=
    tensor_two_basis_expansion e T (b p) (b q)
  rw [hraw]
  simp_rw [hi, hs, ht]
  calc
    _ = (1 / 4 : ℝ) * ∑ i, ∑ j, ∑ k, ∑ l,
        (∑ p, C i p * C j p) * (∑ q, C k q * C l q) * Sm i k * Tm j l := by
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by rw [contraction_coordinate_sums]

end FrameContraction

private theorem hodgeMetricRealFrame_exists {n : ℕ} :
    ∃ f : Fin n × Bool → EuclideanSpace ℂ (Fin n),
      ∀ p, f p = if p.2 then Complex.I • EuclideanSpace.single p.1 1 else
        EuclideanSpace.single p.1 1 := by
  exact ⟨fun p => if p.2 then Complex.I • EuclideanSpace.single p.1 1 else
    EuclideanSpace.single p.1 1, fun _ => rfl⟩

local syntax "hodgeMetricRealFrame" term:max : term
local macro_rules
  | `(hodgeMetricRealFrame $p) => `(Classical.choose hodgeMetricRealFrame_exists $p)

private theorem hodgeMetricRealFrame_spec {n : ℕ} (p : Fin n × Bool) :
    (Classical.choose hodgeMetricRealFrame_exists) p =
      if p.2 then Complex.I • EuclideanSpace.single p.1 1 else
        EuclideanSpace.single p.1 1 :=
  Classical.choose_spec hodgeMetricRealFrame_exists p

private theorem hodgeMetric_modelInnerAt_apply {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M) (u v : EuclideanSpace ℂ (Fin n)) :
    CalabiYau.L2.modelInnerAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      ω₀.toRiemannianMetric x u v =
      ω₀ x ![u, EuclideanSpace.complexStructure n v] := by
  rw [CalabiYau.L2.modelInnerAt_apply, ω₀.toRiemannianMetric_inner_apply]
  simp [KahlerForm.innerAt]

private theorem hodgeMetric_pullback_eval {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (u v : EuclideanSpace ℂ (Fin n)) :
    CalabiYau.L2.modelInnerAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      ω₀.toRiemannianMetric x (A u) (A v) =
      ((ω₀ x).compContinuousLinearMap (A.restrictScalars ℝ))
        ![u, EuclideanSpace.complexStructure n v] := by
  rw [hodgeMetric_modelInnerAt_apply]
  simp only [EuclideanSpace.complexStructure,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i
  · rfl
  · simp

private theorem hodgeMetric_pullback_coeff {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (u v : EuclideanSpace ℂ (Fin n))
    (hAω : ((ω₀ x).compContinuousLinearMap (A.restrictScalars ℝ)).coeffMatrix = 1) :
    CalabiYau.L2.modelInnerAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      ω₀.toRiemannianMetric x (A u) (A v) =
      2 * (∑ j : Fin n, u j * star (v j)).re := by
  let β := (ω₀ x).compContinuousLinearMap (A.restrictScalars ℝ)
  have hβ : β.IsOneOne := (ω₀.isOneOne x).compContinuousLinearMap A
  rw [hodgeMetric_pullback_eval]
  change β ![u, EuclideanSpace.complexStructure n v] = _
  rw [hβ.apply_eq]
  rw [show β.coeffMatrix = 1 from hAω]
  simp only [Matrix.one_apply]
  simp only [EuclideanSpace.complexStructure]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  simp [Complex.I_re]

private theorem hodgeMetric_realFrame_pairing {n : ℕ} (p q : Fin n × Bool) :
    (∑ j : Fin n, (hodgeMetricRealFrame p) j *
      star ((hodgeMetricRealFrame q) j)).re =
      if p = q then 1 else 0 := by
  classical
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, c⟩
  by_cases hij : i = j
  · subst j
    cases b <;> cases c <;>
      simp only [hodgeMetricRealFrame_spec] <;>
      simp [PiLp.single_apply, Complex.I_re]
  · have hpq : (i, b) ≠ (j, c) := by
      intro he
      apply hij
      exact congrArg Prod.fst he
    cases b <;> cases c <;>
      simp only [hodgeMetricRealFrame_spec] <;>
      simp [PiLp.single_apply, hij, eq_comm, hpq]

private theorem hodgeMetric_transported_realFrame_metric {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (x : M)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hAω : ((ω₀ x).compContinuousLinearMap (A.restrictScalars ℝ)).coeffMatrix = 1)
    (p q : Fin n × Bool) :
    CalabiYau.L2.modelInnerAt (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
      ω₀.toRiemannianMetric x (A (hodgeMetricRealFrame p))
      (A (hodgeMetricRealFrame q)) = if p = q then 2 else 0 := by
  rw [hodgeMetric_pullback_coeff ω₀ x A _ _ hAω,
    hodgeMetric_realFrame_pairing]
  split_ifs <;> norm_num

private theorem hodgeMetric_realFrame_decomp {n : ℕ}
    (u : EuclideanSpace ℂ (Fin n)) :
    u = ∑ p : Fin n × Bool,
      (if p.2 then (u p.1).im else (u p.1).re) • hodgeMetricRealFrame p := by
  classical
  ext i
  simp only [hodgeMetricRealFrame_spec]
  simp [Fintype.sum_prod_type, Pi.single_apply,
    Finset.sum_ite_eq, Finset.sum_add_distrib]
  conv_lhs => rw [← RCLike.re_add_im (u.ofLp i)]
  change (RCLike.re (u.ofLp i) : ℂ) + RCLike.im (u.ofLp i) * Complex.I =
    (RCLike.im (u.ofLp i) : ℂ) * Complex.I + RCLike.re (u.ofLp i)
  ring

private theorem hodgeMetric_transported_realFrame_spans {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : Function.Bijective A) :
    Submodule.span ℝ (Set.range (fun p : Fin n × Bool => A (hodgeMetricRealFrame p))) = ⊤ := by
  classical
  apply top_unique
  intro v _
  obtain ⟨u, rfl⟩ := hA.2 v
  rw [hodgeMetric_realFrame_decomp u, _root_.map_sum]
  apply Submodule.sum_mem
  intro p _
  change (A.restrictScalars ℝ) ((_ : ℝ) • hodgeMetricRealFrame p) ∈ _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

private theorem hodgeMetric_normalFrame_sq {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (γ : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (x : M) (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : Function.Bijective A)
    (hAω : ((ω₀ x).compContinuousLinearMap (A.restrictScalars ℝ)).coeffMatrix = 1) :
    FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ =
      (∑ p : Fin n × Bool, ∑ q : Fin n × Bool,
        ((γ x) ![A (hodgeMetricRealFrame p), A (hodgeMetricRealFrame q)]) ^ 2) / 8 := by
  rw [FormField.pointwiseRealInner_degree_two,
    covariantTensorInnerPointwise_two_of_spanning_gram_two ω₀.toRiemannianMetric x
      (fun p => A (hodgeMetricRealFrame p))
      (hodgeMetric_transported_realFrame_spans A hA)
      (hodgeMetric_transported_realFrame_metric ω₀ x A hAω)]
  change ((1 / 4 : ℝ) * ∑ p : Fin n × Bool, ∑ q : Fin n × Bool,
    (γ x) ![A (hodgeMetricRealFrame p), A (hodgeMetricRealFrame q)] *
      (γ x) ![A (hodgeMetricRealFrame p), A (hodgeMetricRealFrame q)]) / 2 = _
  simp only [← pow_two]
  ring

private theorem hodgeMetric_diagonal_frame_values {n : ℕ}
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hα : α.IsOneOne) (lam : Fin n → ℝ)
    (hmat : α.coeffMatrix = Matrix.diagonal (fun i => (lam i : ℂ)))
    (i j : Fin n) (b c : Bool) :
    α ![hodgeMetricRealFrame (i, b), hodgeMetricRealFrame (j, c)] =
      if i = j then (if b = c then 0 else if b then -2 * lam i else 2 * lam i)
        else 0 := by
  classical
  rw [hα.apply_eq, hmat]
  by_cases hij : i = j
  · subst j
    cases b <;> cases c <;>
      simp only [hodgeMetricRealFrame_spec] <;>
      simp [Matrix.diagonal_apply, PiLp.single_apply,
        Complex.I_re]
  · cases b <;> cases c <;>
      simp only [hodgeMetricRealFrame_spec] <;>
      simp [Matrix.diagonal_apply, PiLp.single_apply, hij, eq_comm]

@[expose] public section

/-- Pointwise metric two-form squared norm in a common Hermitian-normal frame.
The inverse *ω-induced* metric contracts both slots, followed by division by `2!`. -/
theorem hodgeMetricNorm_diagonalFrame {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (γ : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (x : M) (lam : Fin n → ℝ)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : Function.Bijective A)
    (hAω₀ : ((ω₀ x).compContinuousLinearMap (A.restrictScalars ℝ)).coeffMatrix = 1)
    (hγ : (γ x).IsOneOne)
    (hAγ : ((γ x).compContinuousLinearMap (A.restrictScalars ℝ)).coeffMatrix =
      Matrix.diagonal (fun i => (lam i : ℂ))) :
    FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ =
      ∑ i, (lam i) ^ 2 := by
  classical
  rw [hodgeMetric_normalFrame_sq ω₀ γ x A hA hAω₀]
  let β := (γ x).compContinuousLinearMap (A.restrictScalars ℝ)
  have hβ : β.IsOneOne := hγ.compContinuousLinearMap A
  have hval (p q : Fin n × Bool) :
      (γ x) ![A (hodgeMetricRealFrame p), A (hodgeMetricRealFrame q)] =
        β ![hodgeMetricRealFrame p, hodgeMetricRealFrame q] := by
    change _ = (γ x) ((A.restrictScalars ℝ) ∘
      ![hodgeMetricRealFrame p, hodgeMetricRealFrame q])
    congr 1
    funext i
    fin_cases i <;> rfl
  simp_rw [hval]
  simp only [Fintype.sum_prod_type]
  simp_rw [hodgeMetric_diagonal_frame_values β hβ lam hAγ]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  ring

/-- The actual field norm agrees with the matrix square trace in a common normal
frame. Both sides are intrinsic although the supplied frame need not be Euclidean-unitary. -/
theorem hodgeNormSq_eq_pointwiseRealInner_of_normalFrame {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) (γ : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (x : M) (lam : Fin n → ℝ)
    (A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n))
    (hAω₀ : ((ω₀ x).compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix = 1)
    (hγ : (γ x).IsOneOne)
    (hAγ : ((γ x).compContinuousLinearMap
      (A.toContinuousLinearMap.restrictScalars ℝ)).coeffMatrix =
      Matrix.diagonal (fun i => (lam i : ℂ))) :
    hodgeNormSq (ω₀ x) (γ x) =
      FormField.pointwiseRealInner ω₀.toRiemannianMetric 2 x γ γ := by
  exact (hodgeNormSq_eq_eigenvalues (ω₀ x) (γ x)
    (ω₀.isPositive x) hγ A lam hAω₀ hAγ).trans
    (hodgeMetricNorm_diagonalFrame ω₀ γ x lam
      A.toContinuousLinearMap A.bijective hAω₀ hγ hAγ).symm

end

end ContinuousAlternatingMap
