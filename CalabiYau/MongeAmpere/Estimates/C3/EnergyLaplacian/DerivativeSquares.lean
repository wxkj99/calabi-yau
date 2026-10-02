module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
import CalabiYau.Geometry.Complex.Forms.Positive

/-!
# Positivity of the two Calabi derivative-square contractions

The existing proved Kronecker-positivity calculation is moved below the
Bochner identity so its children need not import their parent. The two
derivative slots have opposite inverse-index orders. Székelyhidi, §3.3,
proof of Lemma 3.9, printed p. 45, the two squares in (3.14).
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder

namespace KahlerForm

private abbrev V (n : ℕ) := EuclideanSpace ℂ (Fin n)
private abbrev Metric (n : ℕ) := V n → Matrix (Fin n) (Fin n) ℂ

private noncomputable def c3FourWeight {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (((Fin n × Fin n) × Fin n) × Fin n)
      (((Fin n × Fin n) × Fin n) × Fin n) ℂ :=
  Matrix.kroneckerMap (· * ·)
    (Matrix.kroneckerMap (· * ·)
      (Matrix.kroneckerMap (· * ·) A.transpose B) C) D

private noncomputable def c3FourVector {n : ℕ} (X : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (((Fin n × Fin n) × Fin n) × Fin n) → ℂ :=
  fun t => X t.1.1.1 t.1.1.2 t.1.2 t.2

private noncomputable def c3FourQuadratic {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℂ)
    (X : Fin n → Fin n → Fin n → Fin n → ℂ) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l,
    star (X a b c d) * A i a * B b j * C c k * D d l * X i j k l

private theorem c3FourWeight_pos {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef) :
    (c3FourWeight A B C D).PosDef := by
  simpa [c3FourWeight] using ((hA.transpose.kronecker hB).kronecker hC).kronecker hD

private theorem c3FourQuadratic_eq_dotProduct {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℂ)
    (X : Fin n → Fin n → Fin n → Fin n → ℂ) :
    c3FourQuadratic A B C D X =
      star (c3FourVector X) ⬝ᵥ ((c3FourWeight A B C D).mulVec (c3FourVector X)) := by
  classical
  simp [c3FourQuadratic, c3FourVector, c3FourWeight, dotProduct, Matrix.mulVec,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    Finset.mul_sum]
  ring_nf

private theorem c3FourQuadratic_re_nonneg {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (X : Fin n → Fin n → Fin n → Fin n → ℂ) :
    0 ≤ (c3FourQuadratic A B C D X).re := by
  rw [c3FourQuadratic_eq_dotProduct]
  let v := c3FourVector X
  change 0 ≤ (star v ⬝ᵥ (c3FourWeight A B C D).mulVec v).re
  by_cases hv : v = 0
  · simp [v, hv]
  · have hpos := (c3FourWeight_pos A B C D hA hB hC hD).dotProduct_mulVec_pos hv
    exact le_of_lt (Complex.pos_iff.mp hpos).1

private theorem c3HolomorphicDerivativeQuadraticNonneg {n : ℕ}
    (G I : Matrix (Fin n) (Fin n) ℂ) (D : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hG : G.PosDef) (hI : I.PosDef) :
    0 ≤ (c3FourQuadratic I.transpose G.transpose I I D).re := by
  exact c3FourQuadratic_re_nonneg I.transpose G.transpose I I
    hI.transpose hG.transpose hI hI D

private theorem c3AntiholomorphicDerivativeQuadraticNonneg {n : ℕ}
    (G I : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hG : G.PosDef) (hI : I.PosDef) :
    0 ≤ (c3FourQuadratic I G.transpose I I B).re := by
  exact c3FourQuadratic_re_nonneg I G.transpose I I hI hG.transpose hI hI B

private abbrev C3Tuple8 (n : ℕ) := Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × (Fin n × Fin n))))))

private def c3NativeToQuad {n : ℕ} : C3Tuple8 n ≃ C3Tuple8 n where
  toFun x := (x.2.1, (x.2.2.2.2.2.1, (x.2.2.2.2.2.2.1,
    (x.2.2.2.2.2.2.2, (x.1, (x.2.2.1, (x.2.2.2.1, x.2.2.2.2.1)))))))
  invFun x := (x.2.2.2.2.1, (x.1, (x.2.2.2.2.2.1, (x.2.2.2.2.2.2.1,
    (x.2.2.2.2.2.2.2, (x.2.1, (x.2.2.1, x.2.2.2.1)))))))
  left_inv x := by rcases x with ⟨p, q, i, j, k, a, b, c⟩; rfl
  right_inv x := by rcases x with ⟨q, a, b, c, p, i, j, k⟩; rfl

private abbrev C3Tuple3 (n : ℕ) := Fin n × (Fin n × Fin n)
private abbrev C3Tuple4 (n : ℕ) := Fin n × C3Tuple3 n
private abbrev C3Tuple5 (n : ℕ) := Fin n × C3Tuple4 n
private abbrev C3Tuple6 (n : ℕ) := Fin n × C3Tuple5 n
private abbrev C3Tuple7 (n : ℕ) := Fin n × C3Tuple6 n

private theorem c3Sum2Reindex {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℂ) : (∑ i, ∑ j, f i j) = ∑ x : α × β, f x.1 x.2 := by
  exact (Fintype.sum_prod_type (fun x : α × β => f x.1 x.2)).symm

private theorem c3Sum3Reindex {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, f i j k) = ∑ x : Fin n × (Fin n × Fin n), f x.1 x.2.1 x.2.2 := by
  calc
    _ = ∑ i, ∑ y : Fin n × Fin n, f i y.1 y.2 := by
      apply Finset.sum_congr rfl; intro i hi; exact c3Sum2Reindex (fun j k => f i j k)
    _ = _ := c3Sum2Reindex (fun (i : Fin n) (y : Fin n × Fin n) => f i y.1 y.2)

private theorem c3Sum4Reindex {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) =
      ∑ x : C3Tuple4 n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  calc
    _ = ∑ i, ∑ y : C3Tuple3 n, f i y.1 y.2.1 y.2.2 := by
      apply Finset.sum_congr rfl; intro i hi; exact c3Sum3Reindex (fun j k l => f i j k l)
    _ = _ := c3Sum2Reindex (fun (i : Fin n) (y : C3Tuple3 n) => f i y.1 y.2.1 y.2.2)

private theorem c3Sum5Reindex {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, f i j k l m) =
      ∑ x : C3Tuple5 n, f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  calc
    _ = ∑ i, ∑ y : C3Tuple4 n, f i y.1 y.2.1 y.2.2.1 y.2.2.2 := by
      apply Finset.sum_congr rfl; intro i hi; exact c3Sum4Reindex (fun j k l m => f i j k l m)
    _ = _ := c3Sum2Reindex (fun (i : Fin n) (y : C3Tuple4 n) => f i y.1 y.2.1 y.2.2.1 y.2.2.2)

private theorem c3Sum6Reindex {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ o, f i j k l m o) =
      ∑ x : C3Tuple6 n, f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 := by
  calc
    _ = ∑ i, ∑ y : C3Tuple5 n, f i y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 := by
      apply Finset.sum_congr rfl; intro i hi; exact c3Sum5Reindex (fun j k l m o => f i j k l m o)
    _ = _ := c3Sum2Reindex (fun (i : Fin n) (y : C3Tuple5 n) =>
      f i y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2)

private theorem c3Sum7Reindex {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, ∑ m, ∑ o, ∑ r, f i j k l m o r) =
      ∑ x : C3Tuple7 n, f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2 := by
  calc
    _ = ∑ i, ∑ y : C3Tuple6 n, f i y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2 := by
      apply Finset.sum_congr rfl; intro i hi
      exact c3Sum6Reindex (fun j k l m o r => f i j k l m o r)
    _ = _ := c3Sum2Reindex (fun (i : Fin n) (y : C3Tuple6 n) =>
      f i y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2)

private theorem c3Sum8Reindex {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p, ∑ q, ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, f p q i j k a b c) =
      ∑ x : C3Tuple8 n, f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2 := by
  calc
    _ = ∑ p, ∑ y : C3Tuple7 n,
        f p y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2.1 y.2.2.2.2.2.2 := by
      apply Finset.sum_congr rfl; intro p hp
      exact c3Sum7Reindex (fun q i j k a b c => f p q i j k a b c)
    _ = _ := c3Sum2Reindex (fun (p : Fin n) (y : C3Tuple7 n) =>
      f p y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2.1 y.2.2.2.2.2.2)

private theorem c3Sum8ReindexQuadratic {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ i, ∑ j, ∑ k, ∑ l, f a b c d i j k l) =
      ∑ x : C3Tuple8 n, f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2 := by
  calc
    _ = ∑ a, ∑ y : C3Tuple7 n,
        f a y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2.1 y.2.2.2.2.2.2 := by
      apply Finset.sum_congr rfl; intro a ha
      exact c3Sum7Reindex (fun b c d i j k l => f a b c d i j k l)
    _ = _ := c3Sum2Reindex (fun (a : Fin n) (y : C3Tuple7 n) =>
      f a y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2.1 y.2.2.2.2.2.1 y.2.2.2.2.2.2)

private theorem c3Sum8Permute {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p, ∑ q, ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, f p q i j k a b c) =
      ∑ q, ∑ a, ∑ b, ∑ c, ∑ p, ∑ i, ∑ j, ∑ k, f p q i j k a b c := by
  rw [c3Sum8Reindex, c3Sum8ReindexQuadratic]
  exact Fintype.sum_equiv c3NativeToQuad
    (fun x : C3Tuple8 n => f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
      x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2)
    (fun x : C3Tuple8 n => f x.2.2.2.2.1 x.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
      x.2.2.2.2.2.2.2 x.2.1 x.2.2.1 x.2.2.2.1)
    (by intro x; rcases x with ⟨p, q, i, j, k, a, b, c⟩; rfl)

private theorem c3HolomorphicNativeEqQuadratic {n : ℕ}
    (G I : Matrix (Fin n) (Fin n) ℂ) (D : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p, ∑ q, ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      I q p * (G i a * I b j * I c k * D p i j k * star (D q a b c))) =
      c3FourQuadratic I.transpose G.transpose I I D := by
  rw [c3Sum8Permute (f := fun p q i j k a b c =>
    I q p * (G i a * I b j * I c k * D p i j k * star (D q a b c)))]
  simp only [c3FourQuadratic]
  apply Finset.sum_congr rfl; intro q hq
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  simp [Matrix.transpose_apply]; ring

private theorem c3AntiholomorphicNativeEqQuadratic {n : ℕ}
    (G I : Matrix (Fin n) (Fin n) ℂ) (B : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ p, ∑ q, ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      I p q * (G i a * I b j * I c k * B p i j k * star (B q a b c))) =
      c3FourQuadratic I G.transpose I I B := by
  rw [c3Sum8Permute (f := fun p q i j k a b c =>
    I p q * (G i a * I b j * I c k * B p i j k * star (B q a b c)))]
  simp only [c3FourQuadratic]
  apply Finset.sum_congr rfl; intro q hq
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  apply Finset.sum_congr rfl; intro c hc
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  simp [Matrix.transpose_apply]; ring

theorem c3DerivativeSquares_nonneg {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (D B : Fin n → Fin n → Fin n → Fin n → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hg : (g z).PosDef) : 0 ≤ c3DerivativeSquares g D B z := by
  unfold c3DerivativeSquares c3Pair
  simp only [Finset.mul_sum]
  rw [c3HolomorphicNativeEqQuadratic, c3AntiholomorphicNativeEqQuadratic]
  change 0 ≤ (c3FourQuadratic (g z)⁻¹.transpose (g z).transpose
    (g z)⁻¹ (g z)⁻¹ D).re +
    (c3FourQuadratic (g z)⁻¹ (g z).transpose (g z)⁻¹ (g z)⁻¹ B).re
  exact add_nonneg
    (c3HolomorphicDerivativeQuadraticNonneg (g z) (g z)⁻¹ D hg hg.inv)
    (c3AntiholomorphicDerivativeQuadraticNonneg (g z) (g z)⁻¹ B hg hg.inv)
theorem c3ConnectionDifference_derivativeSquares_nonneg
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) {φ : M → ℝ} (hφ : ω₀.IsPotential φ)
    (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    let ψ := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
    let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun w ↦ ω₀.metricInChart x w + complexHessian (φ ∘ ψ) w
    let T : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ :=
      fun w i j k ↦ c3ConnectionDifferenceInChart ω₀ φ x w i j k
    let N : Fin n → Fin n → Fin n → Fin n → ℂ := fun p i j k ↦
      c3PartialZ (fun w ↦ T w i j k) z p
      + ∑ r, c3ChristoffelInChart gφ z i p r * T z r j k
      - ∑ r, c3ChristoffelInChart gφ z r p j * T z i r k
      - ∑ r, c3ChristoffelInChart gφ z r p k * T z i j r
    let Nbar : Fin n → Fin n → Fin n → Fin n → ℂ := fun q i j k ↦
      c3PartialBar (fun w ↦ T w i j k) z q
    0 ≤ c3DerivativeSquares gφ N Nbar z := by
  classical
  let ψ := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm
  let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w + complexHessian (φ ∘ ψ) w
  let T : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ :=
    fun w i j k ↦ c3ConnectionDifferenceInChart ω₀ φ x w i j k
  let N : Fin n → Fin n → Fin n → Fin n → ℂ := fun p i j k ↦
    c3PartialZ (fun w ↦ T w i j k) z p
    + ∑ r, c3ChristoffelInChart gφ z i p r * T z r j k
    - ∑ r, c3ChristoffelInChart gφ z r p j * T z i r k
    - ∑ r, c3ChristoffelInChart gφ z r p k * T z i j r
  let Nbar : Fin n → Fin n → Fin n → Fin n → ℂ := fun q i j k ↦
    c3PartialBar (fun w ↦ T w i j k) z q
  have hmetric := ω₀.metricInChart_perturb hφ x hz
  have hmetric' : gφ z = (ω₀.perturb φ hφ).metricInChart x z := by
    dsimp [gφ, ψ]
    simpa [extChartAt] using hmetric.symm
  have hpos : (gφ z).PosDef := by
    rw [hmetric']
    exact (ω₀.perturb φ hφ).posDef_metricInChart x hz
  exact c3DerivativeSquares_nonneg gφ N Nbar z hpos

end KahlerForm
