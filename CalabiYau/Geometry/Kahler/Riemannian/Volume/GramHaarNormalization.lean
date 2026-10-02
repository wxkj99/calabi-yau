module

public import CalabiYau.Geometry.Complex.Forms.OneOne
public import CalabiYau.Geometry.Riemannian.Volume.Chart.Density
public import CalabiYau.Mathlib.LinearAlgebra.Matrix.Realification
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar normalization and the real Gram determinant of a positive (1,1)-form

Let `b` be the real `chartModelBasis` of `ℂⁿ`. Its fundamental parallelepiped has
complex Euclidean volume `J`; no orthonormality of `b` is assumed. Mathlib's
`b.addHaar` gives that parallelepiped mass `1`, whereas `MeasureTheory.volume`
gives it mass `J`. The real Gram determinant of the metric `α(u,Jv)` is
`J² · 2^(2n) · |det α.coeffMatrix|²`. In particular `J` is the *inverse* of the
scalar taking complex volume to `b.addHaar`, not that scalar itself.

For `n = 0`, all determinants and `J` equal `1`. For the flat `n = 1` form
`i dz ∧ dż`, the standard real basis has `J = 1` and Gram determinant `4`,
while the basis `(2,i)` has `J = 2` and Gram determinant `16`. Reversing basis
orientation leaves both positive factors unchanged. In dimension two, the
Hermitian matrix `[[2,i],[-i,2]]` has determinant `3`; the standard real Gram
has determinant `16 · 9 = 144`. Its off-diagonal real entries check the
transpose in the coefficient convention: `g(e₁,i e₂) = 2` and
`g(i e₁,e₂) = -2`.

Sources: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §§1.1,
1.3 (the metric associated to `ω` and its volume form); Mathlib
`Basis.addHaar_self`, `Measure.addHaarMeasure_unique`,
`OrthonormalBasis.volume_parallelepiped`; `Matrix.det_realify`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix NNReal ENNReal

noncomputable section

namespace CalabiYau.RiemannianVolume

/-- Complex Euclidean volume of the real chart-model basis parallelepiped.
Unlike `modelHaar`, this definition uses only the canonical complex volume instance. -/
noncomputable def complexChartBasisVolume (n : ℕ) : ℝ≥0∞ :=
  MeasureTheory.volume
    (↑(CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))).parallelepiped :
      Set (EuclideanSpace ℂ (Fin n)))

theorem complexChartBasisVolume_pos (n : ℕ) : 0 < complexChartBasisVolume n := by
  rw [complexChartBasisVolume]
  let K := (CalabiYau.Tensor.Coordinates.chartModelBasis
    (EuclideanSpace ℂ (Fin n))).parallelepiped
  have hpos : 0 < MeasureTheory.volume (interior (K : Set (EuclideanSpace ℂ (Fin n)))) :=
    isOpen_interior.measure_pos _ K.interior_nonempty
  change 0 < MeasureTheory.volume (K : Set (EuclideanSpace ℂ (Fin n)))
  exact lt_of_lt_of_le hpos (measure_mono interior_subset)

theorem complexChartBasisVolume_lt_top (n : ℕ) : complexChartBasisVolume n < ⊤ := by
  rw [complexChartBasisVolume]
  exact (CalabiYau.Tensor.Coordinates.chartModelBasis
    (EuclideanSpace ℂ (Fin n))).parallelepiped.isCompact.measure_lt_top

private theorem complexVolume_eq_chartBasisVolume_smul_addHaar (n : ℕ) :
    (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      complexChartBasisVolume n •
        (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))).addHaar := by
  classical
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))
  change MeasureTheory.volume = complexChartBasisVolume n • b.addHaar
  rw [MeasureTheory.Measure.addHaarMeasure_unique (MeasureTheory.volume) b.parallelepiped]
  rw [Module.Basis.addHaar, complexChartBasisVolume]

/-- Complex volume, transported by the chart-model coordinates, is `J` times real
Euclidean volume. This avoids identifying a privately instantiated `modelHaar`
with the canonical complex `volume`. -/
theorem map_toEuclidean_complexVolume_eq_chartBasisVolume_smul_volume (n : ℕ) :
    Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
      (MeasureTheory.volume : Measure (EuclideanSpace ℂ (Fin n))) =
      complexChartBasisVolume n •
        (MeasureTheory.volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))))) := by
  classical
  rw [complexVolume_eq_chartBasisVolume_smul_addHaar, Measure.map_smul]
  congr 1
  have hmap :
      Measure.map (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
          (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))).addHaar =
        ((CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))).map
          (toEuclidean (E := EuclideanSpace ℂ (Fin n))).toLinearEquiv).addHaar :=
    Module.Basis.map_addHaar
      (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n)))
      (toEuclidean (E := EuclideanSpace ℂ (Fin n)))
  rw [hmap]
  have hcancel :
      (CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))).map
          (toEuclidean (E := EuclideanSpace ℂ (Fin n))).toLinearEquiv =
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ
          (EuclideanSpace ℂ (Fin n)))) ℝ).toBasis := by
    refine Module.Basis.eq_of_apply_eq ?_
    intro i
    have hb_i :
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ
          (EuclideanSpace ℂ (Fin n)))) ℝ).toBasis i = EuclideanSpace.single i (1 : ℝ) := by
      simp [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply (𝕜 := ℝ)
        (ι := Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n))))]
    rw [Module.Basis.map_apply, CalabiYau.Tensor.Coordinates.chartModelBasis_apply, hb_i]
    simp
  rw [hcancel]
  exact (EuclideanSpace.basisFun (Fin (Module.finrank ℝ
    (EuclideanSpace ℂ (Fin n)))) ℝ).addHaar_eq_volume

/-- The real Jacobian of the (not necessarily orthonormal) chart-model basis is
exactly its complex Euclidean parallelepiped volume. -/
theorem complexChartBasisVolume_toReal_eq_sqrt_gram (n : ℕ) :
    (complexChartBasisVolume n).toReal =
      Real.sqrt (Matrix.det (Matrix.of fun (i j :
        Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) =>
        Inner.inner ℝ
          ((CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))) i)
          ((CalabiYau.Tensor.Coordinates.chartModelBasis (EuclideanSpace ℂ (Fin n))) j))) := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let c : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ := c.toBasis.toMatrix b
  have hrepr (j : Fin (Module.finrank ℝ E)) : b j = ∑ k, A k j • c k := by
    change b j = ∑ k, (c.toBasis.repr (b j) k) • c k
    exact (c.toBasis.sum_repr (b j)).symm
  have hgram : (fun i j : Fin (Module.finrank ℝ E) => Inner.inner ℝ (b i) (b j)) = A.transpose * A := by
    ext i j
    calc
      Inner.inner ℝ (b i) (b j) = Inner.inner ℝ
          (∑ k, A k i • c k) (∑ k, A k j • c k) := by rw [hrepr i, hrepr j]
      _ = ∑ k, A k i * A k j := by
        simpa using c.orthonormal.inner_sum (fun k => A k i) (fun k => A k j) Finset.univ
      _ = (A.transpose * A) i j := by simp [Matrix.mul_apply]
  have hmat : (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
      Inner.inner ℝ (b i) (b j)) = A.transpose * A := by
    ext i j
    exact congrFun₂ hgram i j
  have hdetGram : (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
      Inner.inner ℝ (b i) (b j)).det = (c.toBasis.det b) ^ 2 := by
    rw [hmat, Matrix.det_mul, Matrix.det_transpose]
    simp [A, Module.Basis.det_apply]
    ring
  have hvol : complexChartBasisVolume n = ENNReal.ofReal |c.toBasis.det b| := by
    rw [complexChartBasisVolume]
    change (MeasureTheory.volume : Measure E) (↑b.parallelepiped : Set E) = _
    rw [← c.addHaar_eq_volume]
    simpa using (MeasureTheory.Measure.addHaar_parallelepiped c.toBasis b)
  change (complexChartBasisVolume n).toReal =
    Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
      Inner.inner ℝ (b i) (b j)))
  rw [hvol, ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [hdetGram, Real.sqrt_sq_eq_abs]

/-- The positive real metric `α(u,Jv)` in the chart-model basis has determinant
`J² · 2^(2n) · |det α.coeffMatrix|²`. The positivity hypothesis matches the
Kähler metric used by the parent and is satisfiable also when `n = 0`. -/
theorem gramDet_chartModelBasis (n : ℕ)
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (hα : α.IsPositive) :
    (Matrix.of fun (i j : Fin (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)))) =>
      α ![(CalabiYau.Tensor.Coordinates.chartModelBasis
          (EuclideanSpace ℂ (Fin n))) i,
        EuclideanSpace.complexStructure n
          ((CalabiYau.Tensor.Coordinates.chartModelBasis
            (EuclideanSpace ℂ (Fin n))) j)]).det =
      (complexChartBasisVolume n).toReal ^ 2 * (2 : ℝ) ^ (2 * n) *
        Complex.normSq α.coeffMatrix.det := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let b := CalabiYau.Tensor.Coordinates.chartModelBasis E
  let cProd : Module.Basis (Fin n × Fin 2) ℝ E :=
    Complex.basisOneI.smulTower' ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)
  have hcard : Fintype.card (Fin n × Fin 2) = Module.finrank ℝ E :=
    (Module.finrank_eq_card_basis cProd).symm
  let e : Fin n × Fin 2 ≃ Fin (Module.finrank ℝ E) := Fintype.equivFinOfCardEq hcard
  let c : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := cProd.reindex e
  let C : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ := c.toMatrix b
  have hcanonicalMatrix : Matrix.of (fun p q : Fin n × Fin 2 =>
      α ![(Complex.basisOneI.smulTower'
          ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) p,
        EuclideanSpace.complexStructure n
          ((Complex.basisOneI.smulTower'
            ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) q)]) =
      (2 : ℝ) • α.coeffMatrix.transpose.realify := by
    have hHerm := hα.1.isHermitian_coeffMatrix
    have hstar (i j : Fin n) : star (α.coeffMatrix j i) = α.coeffMatrix i j := by
      have h := congrFun₂ hHerm.eq i j
      simpa using h
    have hRe (i j : Fin n) : (α.coeffMatrix i j).re = (α.coeffMatrix j i).re := by
      have h := congrArg Complex.re (hstar i j)
      simpa using h.symm
    have hIm (i j : Fin n) : (α.coeffMatrix i j).im = -(α.coeffMatrix j i).im := by
      have h := congrArg Complex.im (hstar i j)
      simpa using h.symm
    have hReIIf (p : Prop) [Decidable p] : (if p then (Complex.I : ℂ) else 0).re = 0 := by
      by_cases hp : p <;> simp [hp, Complex.I_re]
    have hImIIf (p : Prop) [Decidable p] :
        (if p then (Complex.I : ℂ) else 0).im = if p then 1 else 0 := by
      by_cases hp : p <;> simp [hp, Complex.I_im]
    have hReNegIf (p : Prop) [Decidable p] :
        (if p then (-1 : ℂ) else 0).re = if p then -1 else 0 := by
      by_cases hp : p <;> simp [hp]
    have hImNegIf (p : Prop) [Decidable p] :
        (if p then (-1 : ℂ) else 0).im = 0 := by
      by_cases hp : p <;> simp [hp]
    ext ⟨i,a⟩ ⟨j,b⟩
    fin_cases a <;> fin_cases b <;>
      simp [Module.Basis.smulTower'_apply, EuclideanSpace.basisFun_apply,
        EuclideanSpace.complexStructure, ContinuousAlternatingMap.IsOneOne.apply_eq hα.1,
        Matrix.realify_apply, hReIIf, hImIIf, hReNegIf, hImNegIf,
        Finset.sum_ite_eq'] <;> simp only [hRe i j, hIm i j] <;> ring
  have hcanonicalDet : (Matrix.of (fun p q : Fin n × Fin 2 =>
      α ![(Complex.basisOneI.smulTower'
          ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) p,
        EuclideanSpace.complexStructure n
          ((Complex.basisOneI.smulTower'
            ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) q)])).det =
      (2 : ℝ) ^ (2 * n) * Complex.normSq α.coeffMatrix.det := by
    rw [hcanonicalMatrix, Matrix.det_smul, Matrix.det_realify, Matrix.det_transpose]
    simp [Fintype.card_prod, Fintype.card_fin]; omega
  have hcanonicalInner : Matrix.of (fun p q : Fin n × Fin 2 =>
      Inner.inner ℝ
        ((Complex.basisOneI.smulTower'
          ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) p)
        ((Complex.basisOneI.smulTower'
          ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) q)) = 1 := by
    ext ⟨i,a⟩ ⟨j,b⟩
    simp only [Matrix.of_apply]
    change Inner.inner ℝ
        ((Complex.basisOneI.smulTower' ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) (i,a))
        ((Complex.basisOneI.smulTower' ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) (j,b)) = _
    simp only [Module.Basis.smulTower'_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_apply]
    have hreIf (p : Prop) [Decidable p] (z : ℂ) :
        (if p then z else 0).re = if p then z.re else 0 := by
      by_cases hp : p <;> simp [hp]
    have himIIf (p : Prop) [Decidable p] :
        (if p then (Complex.I : ℂ) else 0).im = if p then 1 else 0 := by
      by_cases hp : p <;> simp [hp, Complex.I_im]
    fin_cases a <;> fin_cases b <;>
      simp [PiLp.inner_apply, PiLp.single_apply, Matrix.one_apply,
        Complex.I_re, Complex.I_im, hreIf, himIIf, Finset.sum_ite_eq']; simp [eq_comm]
  have hGc : Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      α ![c i, EuclideanSpace.complexStructure n (c j)]) =
      Matrix.reindex e e ((2 : ℝ) • α.coeffMatrix.transpose.realify) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [c, Module.Basis.reindex_apply]
    exact congrFun₂ hcanonicalMatrix (e.symm i) (e.symm j)
  have hdetGc : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      α ![c i, EuclideanSpace.complexStructure n (c j)])).det =
      (2 : ℝ) ^ (2 * n) * Complex.normSq α.coeffMatrix.det := by
    calc
      _ = (Matrix.reindex e e ((2 : ℝ) • α.coeffMatrix.transpose.realify)).det :=
        congrArg Matrix.det hGc
      _ = (Matrix.of (fun p q : Fin n × Fin 2 =>
          α ![(Complex.basisOneI.smulTower' ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) p,
            EuclideanSpace.complexStructure n
              ((Complex.basisOneI.smulTower' ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis)) q)])).det := by
        rw [Matrix.det_reindex]
        have he : e.trans e.symm = Equiv.refl _ :=
          Equiv.ext (fun x => e.symm_apply_apply x)
        rw [he]
        norm_num
        simpa [Nat.mul_comm] using hcanonicalDet.symm
      _ = (2 : ℝ) ^ (2 * n) * Complex.normSq α.coeffMatrix.det := hcanonicalDet
  have hHc : Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      Inner.inner ℝ (c i) (c j)) = 1 := by
    ext i j
    simp only [Matrix.of_apply]
    have h := congrFun₂ hcanonicalInner (e.symm i) (e.symm j)
    simpa [Matrix.one_apply, c] using h
  have hmetric : Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      α ![b i, EuclideanSpace.complexStructure n (b j)]) =
      C.transpose * Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        α ![c i, EuclideanSpace.complexStructure n (c j)]) * C := by
    have hrepr (j : Fin (Module.finrank ℝ E)) : b j = ∑ k, C k j • c k := by
      change b j = ∑ k, (c.repr (b j) k) • c k
      exact (c.sum_repr (b j)).symm
    have hJ (j : Fin (Module.finrank ℝ E)) :
        EuclideanSpace.complexStructure n (b j) =
          ∑ k, C k j • EuclideanSpace.complexStructure n (c k) := by
      rw [hrepr j]
      simp [map_sum, map_smul]
    have hfirst (i : Fin (Module.finrank ℝ E)) (x : EuclideanSpace ℂ (Fin n)) :
        α ![b i, x] = ∑ k, C k i * α ![c k, x] := by
      have hvect : ![b i, x] = Function.update ![0, x] 0 (∑ k, C k i • c k) := by
        funext q
        fin_cases q <;> simp [Function.update, hrepr i]
      rw [hvect]
      change α.toMultilinearMap (Function.update ![0, x] 0 (∑ k, C k i • c k)) = _
      rw [α.toMultilinearMap.map_update_sum Finset.univ 0 (fun k => C k i • c k) ![0, x]]
      simp only [MultilinearMap.map_update_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hvec : Function.update ![0, x] 0 (c k) = ![c k, x] := by
        funext q
        fin_cases q <;> simp [Function.update]
      rw [hvec]
      rfl
    have hsecond (k j : Fin (Module.finrank ℝ E)) :
        α ![c k, EuclideanSpace.complexStructure n (b j)] =
          ∑ l, C l j * α ![c k, EuclideanSpace.complexStructure n (c l)] := by
      have hvect : ![c k, EuclideanSpace.complexStructure n (b j)] =
          Function.update ![c k, 0] 1 (∑ l, C l j • EuclideanSpace.complexStructure n (c l)) := by
        funext q
        fin_cases q <;> simp [Function.update, hJ j]
      rw [hvect]
      change α.toMultilinearMap
        (Function.update ![c k, 0] 1 (∑ l, C l j • EuclideanSpace.complexStructure n (c l))) = _
      rw [α.toMultilinearMap.map_update_sum Finset.univ 1
        (fun l => C l j • EuclideanSpace.complexStructure n (c l)) ![c k, 0]]
      simp only [MultilinearMap.map_update_smul, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro l hl
      have hvec : Function.update ![c k, 0] 1 (EuclideanSpace.complexStructure n (c l)) =
          ![c k, EuclideanSpace.complexStructure n (c l)] := by
        funext q
        fin_cases q <;> simp [Function.update]
      rw [hvec]
      rfl
    ext i j
    change α ![b i, EuclideanSpace.complexStructure n (b j)] = _
    rw [hfirst i]
    simp_rw [hsecond]
    simp only [C, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Matrix.of_apply]
    ring
  have hinner : Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      Inner.inner ℝ (b i) (b j)) =
      C.transpose * Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        Inner.inner ℝ (c i) (c j)) * C := by
    have hrepr (j : Fin (Module.finrank ℝ E)) : b j = ∑ k, C k j • c k := by
      change b j = ∑ k, (c.repr (b j) k) • c k
      exact (c.sum_repr (b j)).symm
    ext i j
    simp only [Matrix.of_apply]
    rw [hrepr i, hrepr j]
    rw [sum_inner]
    simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
    simp only [Matrix.of_apply, C, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hdetGramB : (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
      Inner.inner ℝ (b i) (b j)).det = C.det ^ 2 := by
    rw [hinner, hHc, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    simp [C]
    ring
  have hJ : (complexChartBasisVolume n).toReal ^ 2 = C.det ^ 2 := by
    rw [complexChartBasisVolume_toReal_eq_sqrt_gram n]
    rw [hdetGramB, Real.sqrt_sq_eq_abs]
    exact sq_abs _
  calc
    (Matrix.of fun (i j : Fin (Module.finrank ℝ E)) =>
        α ![b i, EuclideanSpace.complexStructure n (b j)]).det =
        (C.transpose * Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
          α ![c i, EuclideanSpace.complexStructure n (c j)]) * C).det :=
      congrArg Matrix.det hmetric
    _ = C.det ^ 2 * (2 : ℝ) ^ (2 * n) * Complex.normSq α.coeffMatrix.det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetGc]
      ring
    _ = (complexChartBasisVolume n).toReal ^ 2 * (2 : ℝ) ^ (2 * n) *
        Complex.normSq α.coeffMatrix.det := by rw [← hJ]

end CalabiYau.RiemannianVolume

end
