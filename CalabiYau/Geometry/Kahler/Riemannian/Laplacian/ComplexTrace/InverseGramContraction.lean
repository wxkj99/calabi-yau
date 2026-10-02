module

public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.Geometry.Manifold.Tensor.Coordinates.ModelBasis

/-!
# Inverse Kähler Gram contraction in a real chart-model basis

The real Gram matrix of a positive `(1,1)`-form need not be written in the
standard `(e_j, ie_j)` frame: `chartModelBasis` may have a nontrivial real
Jacobian. Its inverse contracts a real covector to the complex vector whose
`j`-th coefficient is `∑ k, (G⁻¹) k j ∂̄_k u`. The order `k j` follows from
the Hermitian coefficient convention `α = i ∑ G j k dz_j ∧ dż_k`.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §§1.1,
1.3; Ballmann, *Lectures on Kähler Manifolds*, §5, Exercise 5.51(1), p. 75.
-/

@[expose] public section

namespace ContinuousAlternatingMap

variable {n : ℕ}

/-- Real Gram matrix of a `(1,1)`-form in the actual real chart-model basis. -/
noncomputable def complexChartModelGram
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) :
    Matrix (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))
      (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) ℝ :=
  Matrix.of fun i j => α ![
    CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) i,
    EuclideanSpace.complexStructure n
      (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) j)]

/-- The pointwise inverse real Gram/complex gradient identity. The named
predicate allows its exact local hypothesis to be passed to the differential
transport theorem without imposing the positivity of the form globally. -/
def ComplexChartInverseGramContraction
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) : Prop :=
    (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
      (∑ j : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
        (complexChartModelGram α)⁻¹ i j *
          ℓ (CalabiYau.Tensor.Coordinates.chartModelBasis
            (EuclideanSpace ℂ (Fin n)) j)) •
        CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) i) =
      ∑ j : Fin n,
        (∑ k : Fin n, (α.coeffMatrix)⁻¹ k j *
          (((ℓ (EuclideanSpace.single k 1) : ℂ) +
            Complex.I * (ℓ (Complex.I • EuclideanSpace.single k 1) : ℂ)) / 2)) •
          EuclideanSpace.single j (1 : ℂ)

/-- Inverse real Gram contraction is the complex antiholomorphic gradient,
independently of the real chart-model basis and its Jacobian. -/
private theorem inverseGram_metric_symmetric
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ} (hα : α.IsPositive)
    (u v : EuclideanSpace ℂ (Fin n)) :
    α ![u, EuclideanSpace.complexStructure n v] =
      α ![v, EuclideanSpace.complexStructure n u] := by
  have hswap (x y : EuclideanSpace ℂ (Fin n)) : α ![x, y] = -α ![y, x] := by
    have h : α ![y, x] = -α ![x, y] := by
      simpa using α.map_swap ![x, y] Fin.zero_ne_one
    linarith
  have hI : α ![EuclideanSpace.complexStructure n v, -u] =
      α ![v, EuclideanSpace.complexStructure n u] := by
    simpa [EuclideanSpace.complexStructure, smul_smul, Complex.I_mul_I] using
      hα.1 v (EuclideanSpace.complexStructure n u)
  have hneg : α ![EuclideanSpace.complexStructure n v, -u] =
      -α ![EuclideanSpace.complexStructure n v, u] := by
    change α.toContinuousMultilinearMap ![EuclideanSpace.complexStructure n v, -u] =
      -α.toContinuousMultilinearMap ![EuclideanSpace.complexStructure n v, u]
    have hvect : ![EuclideanSpace.complexStructure n v, -u] =
        Function.update ![EuclideanSpace.complexStructure n v, u] 1 (-u) := by
      funext i
      fin_cases i <;> simp [Function.update]
    rw [hvect]
    have hvec' : Function.update ![EuclideanSpace.complexStructure n v, u] 1 u =
        ![EuclideanSpace.complexStructure n v, u] := by
      funext i
      fin_cases i <;> simp [Function.update]
    have h := α.toContinuousMultilinearMap.map_update_smul
      ![EuclideanSpace.complexStructure n v, u] 1 (-1 : ℝ) u
    rw [hvec'] at h
    simpa only [neg_one_smul, smul_eq_mul, neg_one_mul] using h
  rw [hneg] at hI
  calc
    α ![u, EuclideanSpace.complexStructure n v] =
        -α ![EuclideanSpace.complexStructure n v, u] := hswap _ _
    _ = α ![v, EuclideanSpace.complexStructure n u] := hI

private theorem inverseGram_eval_sum_first
    {m : ℕ} (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (b : Fin m → EuclideanSpace ℂ (Fin n)) (c : Fin m → ℝ)
    (v : EuclideanSpace ℂ (Fin n)) :
    α ![∑ i, c i • b i, v] = ∑ i, c i * α ![b i, v] := by
  have hvect : ![∑ i, c i • b i, v] =
      Function.update ![0, v] 0 (∑ i, c i • b i) := by
    funext i
    fin_cases i <;> simp [Function.update]
  rw [hvect]
  change α.toMultilinearMap
      (Function.update ![0, v] 0 (∑ i, c i • b i)) = _
  rw [α.toMultilinearMap.map_update_sum Finset.univ 0
    (fun i : Fin m ↦ c i • b i) ![0, v]]
  simp only [MultilinearMap.map_update_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hvec : Function.update ![0, v] 0 (b i) = ![b i, v] := by
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hvec]
  rfl

private theorem inverseGram_eval_sum_second
    {m : ℕ} (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (u : EuclideanSpace ℂ (Fin n)) (b : Fin m → EuclideanSpace ℂ (Fin n))
    (c : Fin m → ℝ) :
    α ![u, ∑ i, c i • b i] = ∑ i, c i * α ![u, b i] := by
  have hvect : ![u, ∑ i, c i • b i] =
      Function.update ![u, 0] 1 (∑ i, c i • b i) := by
    funext i
    fin_cases i <;> simp [Function.update]
  rw [hvect]
  change α.toMultilinearMap
      (Function.update ![u, 0] 1 (∑ i, c i • b i)) = _
  rw [α.toMultilinearMap.map_update_sum Finset.univ 1
    (fun i : Fin m ↦ c i • b i) ![u, 0]]
  simp only [MultilinearMap.map_update_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hvec : Function.update ![u, 0] 1 (b i) = ![u, b i] := by
    funext j
    fin_cases j <;> simp [Function.update]
  rw [hvec]
  rfl

private theorem inverseGram_chartGram_posDef
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ} (hα : α.IsPositive) :
    (complexChartModelGram α).PosDef := by
  let E := EuclideanSpace ℂ (Fin n)
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let G := complexChartModelGram α
  have hsymm : G.IsSymm := by
    refine Matrix.IsSymm.ext ?_
    intro i j
    exact (inverseGram_metric_symmetric hα (b i) (b j)).symm
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hsymm ?_
  intro c hc
  let w : E := ∑ i, c i • b i
  have hJw : EuclideanSpace.complexStructure n w =
      ∑ i, c i • EuclideanSpace.complexStructure n (b i) := by
    simp [w, map_smul]
  have hquad : dotProduct c (G.mulVec c) =
      α ![w, EuclideanSpace.complexStructure n w] := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [hJw]
    rw [inverseGram_eval_sum_first]
    simp_rw [inverseGram_eval_sum_second]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    change G i j * c j = c j * α ![b i,
      EuclideanSpace.complexStructure n (b j)]
    rw [show G i j = α ![b i, EuclideanSpace.complexStructure n (b j)] from rfl]
    ring
  have hwnz : w ≠ 0 := by
    intro hw
    have hli := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    have hc0 : c = 0 := funext (hli c hw)
    exact hc hc0
  change 0 < dotProduct c (G.mulVec c)
  rw [hquad]
  exact hα.2 w hwnz

open scoped ComplexOrder in
private theorem inverseGram_complex_candidate_pair
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ} (hα : α.IsPositive)
    (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) (w : EuclideanSpace ℂ (Fin n)) :
    α ![(∑ j : Fin n,
      (∑ k : Fin n, (α.coeffMatrix)⁻¹ k j *
        (((ℓ (EuclideanSpace.single k 1) : ℂ) +
          Complex.I * (ℓ (Complex.I • EuclideanSpace.single k 1) : ℂ)) / 2)) •
        EuclideanSpace.single j (1 : ℂ)), EuclideanSpace.complexStructure n w] = ℓ w := by
  let A := α.coeffMatrix
  let q (k : Fin n) : ℂ :=
    (((ℓ (EuclideanSpace.single k 1) : ℂ) +
      Complex.I * (ℓ (Complex.I • EuclideanSpace.single k 1) : ℂ)) / 2)
  let z : EuclideanSpace ℂ (Fin n) :=
    ∑ j : Fin n, (∑ k : Fin n, A⁻¹ k j * q k) • EuclideanSpace.single j 1
  have hA : A.PosDef := (ContinuousAlternatingMap.isPositive_iff (α := α)).mp hα |>.2
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hz (j : Fin n) : z j = ∑ k : Fin n, A⁻¹ k j * q k := by
    simp [z, Pi.single_apply, Finset.sum_apply]
  have hprod : A.transpose * A⁻¹.transpose = 1 := by
    calc
      _ = (A⁻¹ * A).transpose := by rw [← Matrix.transpose_mul]
      _ = 1 := by rw [Matrix.nonsing_inv_mul A hdetA, Matrix.transpose_one]
  have hcoeff (k m : Fin n) :
      (∑ j : Fin n, A j k * A⁻¹ m j) = if k = m then 1 else 0 := by
    have hh := congrFun₂ hprod k m
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hh
  have hcontract (k : Fin n) : (∑ j : Fin n, A j k * z j) = q k := by
    calc
      _ = ∑ j : Fin n, A j k * (∑ m : Fin n, A⁻¹ m j * q m) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hz]
      _ = ∑ m : Fin n, q m * (∑ j : Fin n, A j k * A⁻¹ m j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = q k := by simp [hcoeff]
  have hbar (k : Fin n) :
      star ((EuclideanSpace.complexStructure n w) k) = -Complex.I * star (w k) := by
    simp [EuclideanSpace.complexStructure, star_mul]
    ; ring
  have hform : α ![z, EuclideanSpace.complexStructure n w] =
      2 * (∑ j : Fin n, ∑ k : Fin n, A j k * z j * star (w k)).re := by
    rw [hα.1.apply_eq]
    simp_rw [hbar]
    simp [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.mul_re]
    ; ring
  have hsum : (∑ j : Fin n, ∑ k : Fin n, A j k * z j * star (w k)) =
      ∑ k : Fin n, q k * star (w k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = (∑ j : Fin n, A j k * z j) * star (w k) := by
        rw [Finset.sum_mul]
      _ = q k * star (w k) := by rw [hcontract]
  let E (p : Fin n × Bool) : EuclideanSpace ℂ (Fin n) :=
    if p.2 then Complex.I • EuclideanSpace.single p.1 1 else EuclideanSpace.single p.1 1
  let c (x : EuclideanSpace ℂ (Fin n)) (p : Fin n × Bool) : ℝ :=
    if p.2 then (x p.1).im else (x p.1).re
  have hdecomp (x : EuclideanSpace ℂ (Fin n)) :
      x = ∑ p : Fin n × Bool, c x p • E p := by
    ext i
    simp [c, E, Fintype.sum_prod_type, Pi.single_apply,
      Finset.sum_ite_eq, Finset.sum_add_distrib]
    conv_lhs => rw [← RCLike.re_add_im (x.ofLp i)]
    change (RCLike.re (x.ofLp i) : ℂ) + RCLike.im (x.ofLp i) * Complex.I =
      (RCLike.im (x.ofLp i) : ℂ) * Complex.I + RCLike.re (x.ofLp i)
    ring_nf
  have hℓ : ℓ w = ∑ p : Fin n × Bool, c w p * ℓ (E p) := by
    calc
      _ = ℓ (∑ p : Fin n × Bool, c w p • E p) := by rw [← hdecomp w]
      _ = _ := by
        change ℓ.toLinearMap (∑ p ∈ Finset.univ, c w p • E p) =
          ∑ p ∈ Finset.univ, c w p * ℓ (E p)
        rw [_root_.map_sum]
        simp only [map_smul, smul_eq_mul]
        rfl
  have hq (k : Fin n) :
      2 * (q k * star (w k)).re =
        (w k).re * ℓ (EuclideanSpace.single k 1) +
          (w k).im * ℓ (Complex.I • EuclideanSpace.single k 1) := by
    simp [q, Complex.mul_re, Complex.I_re, Complex.I_im]
    ; ring
  have hqsum : 2 * (∑ k : Fin n, q k * star (w k)).re =
      ∑ k : Fin n,
        ((w k).re * ℓ (EuclideanSpace.single k 1) +
          (w k).im * ℓ (Complex.I • EuclideanSpace.single k 1)) := by
    simp only [Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hq k
  have hreal_sum :
      (∑ p : Fin n × Bool, c w p * ℓ (E p)) =
        ∑ k : Fin n,
          ((w k).re * ℓ (EuclideanSpace.single k 1) +
            (w k).im * ℓ (Complex.I • EuclideanSpace.single k 1)) := by
    simp [c, E, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    α ![z, EuclideanSpace.complexStructure n w] =
        2 * (∑ j : Fin n, ∑ k : Fin n, A j k * z j * star (w k)).re := hform
    _ = 2 * (∑ k : Fin n, q k * star (w k)).re := by rw [hsum]
    _ = ∑ k : Fin n,
        ((w k).re * ℓ (EuclideanSpace.single k 1) +
          (w k).im * ℓ (Complex.I • EuclideanSpace.single k 1)) := hqsum
    _ = ℓ w := by rw [← hreal_sum, ← hℓ]

private theorem inverseGram_chart_real_pair
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ} (hα : α.IsPositive)
    (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) (w : EuclideanSpace ℂ (Fin n)) :
    α ![(∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
      (∑ j : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))),
        (complexChartModelGram α)⁻¹ i j * ℓ
          (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) j)) •
        CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)) i),
      EuclideanSpace.complexStructure n w] = ℓ w := by
  let E := EuclideanSpace ℂ (Fin n)
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let G := complexChartModelGram α
  let c (i : Fin (Module.finrank ℝ E)) : ℝ :=
    ∑ j, (G⁻¹) i j * ℓ (b j)
  let x : E := ∑ i, c i • b i
  have hsymm : G.IsSymm := by
    refine Matrix.IsSymm.ext ?_
    intro i j
    exact (inverseGram_metric_symmetric hα (b i) (b j)).symm
  have hsymentry (i j : Fin (Module.finrank ℝ E)) : G i j = G j i := by
    have hh := congrFun₂ hsymm.eq i j
    simpa [Matrix.transpose_apply] using hh.symm
  have hGpos : G.PosDef := by
    simpa [G] using inverseGram_chartGram_posDef hα
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hGpos.isUnit
  have hmul : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  have hentry (i j : Fin (Module.finrank ℝ E)) :
      (∑ k, G i k * (G⁻¹) k j) = if i = j then 1 else 0 := by
    have hh := congrFun₂ hmul i j
    simpa [Matrix.mul_apply, Matrix.one_apply] using hh
  have hcoef (m : Fin (Module.finrank ℝ E)) :
      (∑ i, c i * G i m) = ℓ (b m) := by
    calc
      _ = ∑ i, (∑ j, (G⁻¹) i j * ℓ (b j)) * G i m := by
        apply Finset.sum_congr rfl
        intro i hi
        rfl
      _ = ∑ j, ∑ i, ℓ (b j) * (G m i * (G⁻¹) i j) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        rw [hsymentry]
        ring
      _ = ∑ j, ℓ (b j) * (∑ i, G m i * (G⁻¹) i j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
      _ = ℓ (b m) := by
        simp_rw [hentry m]
        simp
  have hpair (m : Fin (Module.finrank ℝ E)) :
      α ![x, EuclideanSpace.complexStructure n (b m)] = ℓ (b m) := by
    calc
      α ![x, EuclideanSpace.complexStructure n (b m)] =
          ∑ i, c i * α ![b i, EuclideanSpace.complexStructure n (b m)] := by
            simpa [x] using inverseGram_eval_sum_first α b c
              (EuclideanSpace.complexStructure n (b m))
      _ = ∑ i, c i * G i m := by rfl
      _ = ℓ (b m) := hcoef m
  have hw : w = ∑ i, (b.repr w i) • b i := (b.sum_repr w).symm
  have hJsum : EuclideanSpace.complexStructure n
      (∑ i, (b.repr w i) • b i) =
      ∑ i, (b.repr w i) • EuclideanSpace.complexStructure n (b i) := by
    calc
      _ = EuclideanSpace.complexStructure n w := congrArg
        (EuclideanSpace.complexStructure n) (b.sum_repr w)
      _ = _ := by
        conv_lhs => rw [← b.sum_repr w]
        change Complex.I • (∑ i, (b.repr w i) • b i) = _
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact smul_comm Complex.I (b.repr w i) (b i)
  have hℓsum : ℓ w = ∑ i, (b.repr w i) * ℓ (b i) := by
    calc
      ℓ w = ℓ (∑ i, (b.repr w i) • b i) := by rw [← hw]
      _ = ∑ i, (b.repr w i) * ℓ (b i) := by
        change ℓ.toLinearMap (∑ i ∈ Finset.univ, (b.repr w i) • b i) =
          ∑ i ∈ Finset.univ, (b.repr w i) * ℓ (b i)
        rw [_root_.map_sum]
        simp only [map_smul, smul_eq_mul]
        rfl
  calc
    α ![x, EuclideanSpace.complexStructure n w] =
        α ![x, EuclideanSpace.complexStructure n
          (∑ i, (b.repr w i) • b i)] := by rw [← hw]
    _ = ∑ i, (b.repr w i) * ℓ (b i) := by
      rw [hJsum]
      rw [inverseGram_eval_sum_second α x
        (fun i => EuclideanSpace.complexStructure n (b i)) (b.repr w)]
      simp_rw [hpair]
    _ = ℓ w := hℓsum.symm

private theorem inverseGram_contraction_proof
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ} (hα : α.IsPositive)
    (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) :
    ComplexChartInverseGramContraction α ℓ := by
  let E := EuclideanSpace ℂ (Fin n)
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let G := complexChartModelGram α
  let c (i : Fin (Module.finrank ℝ E)) : ℝ :=
    ∑ j, (G⁻¹) i j * ℓ (b j)
  let x : E := ∑ i, c i • b i
  let z : E := ∑ j : Fin n,
    (∑ k : Fin n, (α.coeffMatrix)⁻¹ k j *
      (((ℓ (EuclideanSpace.single k 1) : ℂ) +
        Complex.I * (ℓ (Complex.I • EuclideanSpace.single k 1) : ℂ)) / 2)) •
      EuclideanSpace.single j (1 : ℂ)
  have hx := inverseGram_chart_real_pair hα ℓ
  have hz := inverseGram_complex_candidate_pair hα ℓ
  have heq : x = z := by
    by_contra hne
    let d : E := x - z
    have hd : d ≠ 0 := by
      dsimp [d]
      exact sub_ne_zero.mpr hne
    have hpair : α ![x, EuclideanSpace.complexStructure n d] =
        α ![z, EuclideanSpace.complexStructure n d] := by
      rw [hx d, hz d]
    have hadd (u v t : E) : α ![u + v, t] = α ![u, t] + α ![v, t] := by
      change α.toContinuousMultilinearMap ![u + v, t] =
        α.toContinuousMultilinearMap ![u, t] + α.toContinuousMultilinearMap ![v, t]
      have hm := α.toContinuousMultilinearMap.map_update_add ![0, t] (0 : Fin 2) u v
      have hleft : Function.update ![0, t] (0 : Fin 2) (u + v) = ![u + v, t] := by
        funext i
        fin_cases i <;> simp [Function.update]
      have hfirst : Function.update ![0, t] (0 : Fin 2) u = ![u, t] := by
        funext i
        fin_cases i <;> simp [Function.update]
      have hsecond : Function.update ![0, t] (0 : Fin 2) v = ![v, t] := by
        funext i
        fin_cases i <;> simp [Function.update]
      simpa only [hleft, hfirst, hsecond] using hm
    have hzero : α ![d, EuclideanSpace.complexStructure n d] = 0 := by
      have hsum : α ![d, EuclideanSpace.complexStructure n d] +
          α ![z, EuclideanSpace.complexStructure n d] =
          α ![z, EuclideanSpace.complexStructure n d] := by
        calc
          _ = α ![d + z, EuclideanSpace.complexStructure n d] := (hadd d z _).symm
          _ = α ![x, EuclideanSpace.complexStructure n d] := by
            congr 1
            simp [d]
          _ = α ![z, EuclideanSpace.complexStructure n d] := hpair
      linarith
    have hpos := hα.2 d hd
    have hzero' : α ![d, Complex.I • d] = 0 := by
      simpa [EuclideanSpace.complexStructure] using hzero
    rw [hzero'] at hpos
    linarith
  change x = z
  exact heq

theorem IsPositive.inverse_complexChartModelGram_contract
    {α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ} (hα : α.IsPositive)
    (ℓ : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) :
    ComplexChartInverseGramContraction α ℓ := by
  exact inverseGram_contraction_proof hα ℓ

end ContinuousAlternatingMap
