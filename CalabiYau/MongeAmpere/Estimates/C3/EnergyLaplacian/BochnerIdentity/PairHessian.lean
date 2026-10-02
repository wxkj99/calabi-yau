module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.OrderedJets
import CalabiYau.Geometry.Kahler.MatrixInverse

/-!
# The second mixed Hessian of the actual tensor norm

Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45, (3.14).
The inverse entry is [q,p]; curvature begins with -partialZ_p(partialBar_q g).
The pairing is linear on the left and conjugate-linear on the right.
This computation uses only the stated
No off-target smoothness is assumed.
-/

@[expose] public section

open scoped Manifold ContDiff BigOperators ComplexOrder
open Filter Topology

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

private noncomputable def c3PairMixedJetLaplacian
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (T : Fin n → Fin n → Fin n → ℂ)
    (D B : Fin n → Fin n → Fin n → Fin n → ℂ)
    (H : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) : ℝ :=
  ((∑ p, ∑ q, (g z)⁻¹ q p *
      c3Pair g z (fun i j k ↦ H p q i j k) T) +
    (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (D p) (D q)) +
    (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (B q) (B p)) +
    (∑ p, ∑ q, (g z)⁻¹ q p *
      c3Pair g z T (fun i j k ↦ H q p i j k))).re

private theorem c3Pair_fixed_metric_mixed_jet
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (T : Fin n → Fin n → Fin n → ℂ)
    (D B : Fin n → Fin n → Fin n → Fin n → ℂ)
    (H : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    c3PairMixedJetLaplacian g z T D B H =
      c3DerivativeSquares g D B z +
        (∑ p, ∑ q, (g z)⁻¹ q p *
          c3Pair g z (fun i j k ↦ H p q i j k) T).re +
        (∑ p, ∑ q, (g z)⁻¹ q p *
          c3Pair g z T (fun i j k ↦ H q p i j k)).re := by
  have hB :
      (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (B q) (B p)) =
        ∑ p, ∑ q, (g z)⁻¹ p q * c3Pair g z (B p) (B q) := by
    calc
      _ = ∑ q, ∑ p, (g z)⁻¹ q p * c3Pair g z (B q) (B p) := Finset.sum_comm
      _ = _ := rfl
  unfold c3PairMixedJetLaplacian c3DerivativeSquares
  rw [hB]
  simp only [Complex.add_re]
  ring

omit [T2Space M] [CompactSpace M] in
private theorem c3ChartPairHessianLaplacian_eq_realWirtinger_sum
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (hE : ContDiffAt ℝ 2
      (fun w ↦ (c3Pair (c3PerturbedMetricInChart ω₀ φ x) w
        (c3ConnectionDifferenceInChart ω₀ φ x w)
        (c3ConnectionDifferenceInChart ω₀ φ x w)).re)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)) :
    c3ChartPairHessianLaplacian ω₀ φ x =
      (∑ p, ∑ q,
        (c3PerturbedMetricInChart ω₀ φ x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))⁻¹ q p *
          chartPartialZComplex
            (fun w ↦ chartPartialBar
              (fun v ↦ (c3Pair (c3PerturbedMetricInChart ω₀ φ x) v
                (c3ConnectionDifferenceInChart ω₀ φ x v)
                (c3ConnectionDifferenceInChart ω₀ φ x v)).re) w q)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) p).re := by
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  change (((g z)⁻¹ * complexHessian (fun w ↦ (c3Pair g w (T w) (T w)).re) z).trace).re = _
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  simp_rw [← chartPartialZComplex_chartPartialBar
    (fun v ↦ (c3Pair g v (T v) (T v)).re) z hE]
  change (∑ p, ∑ q, (g z)⁻¹ p q *
    chartPartialZComplex
      (fun w ↦ chartPartialBar (fun v ↦ (c3Pair g v (T v) (T v)).re) w p) z q).re = _
  calc
    _ = (∑ p, ∑ q, (g z)⁻¹ q p *
        chartPartialZComplex
          (fun w ↦ chartPartialBar (fun v ↦ (c3Pair g v (T v) (T v)).re) w q) z p).re := by
      congr 1
      calc
        _ = ∑ q, ∑ p, (g z)⁻¹ p q *
            chartPartialZComplex
              (fun w ↦ chartPartialBar (fun v ↦ (c3Pair g v (T v) (T v)).re) w p) z q :=
          Finset.sum_comm
        _ = _ := rfl
    _ = _ := rfl

private theorem c3ConnectionDifference_contDiffOn_target
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ) (x : M) :
    ∀ i j k, ContDiffOn ℝ ∞
      (fun z ↦ c3ConnectionDifferenceInChart ω₀ φ x z i j k)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  intro i j k z hz
  exact (c3ConnectionDifference_contDiffAt ω₀ φ hφ x z hz i j k).contDiffWithinAt

private abbrev PairTuple3 (n : ℕ) := Fin n × (Fin n × Fin n)
private abbrev PairTuple4 (n : ℕ) := Fin n × PairTuple3 n
private abbrev PairTuple5 (n : ℕ) := Fin n × PairTuple4 n
private abbrev PairTuple6 (n : ℕ) := Fin n × PairTuple5 n

private theorem pairSum2 {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℂ) : (∑ i, ∑ j, f i j) = ∑ x : α × β, f x.1 x.2 := by
  exact (Fintype.sum_prod_type (fun x : α × β => f x.1 x.2)).symm

private theorem pairSum3 {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, f i j k) =
      ∑ x : PairTuple3 n, f x.1 x.2.1 x.2.2 := by
  calc
    _ = ∑ i, ∑ y : Fin n × Fin n, f i y.1 y.2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pairSum2 (fun j k => f i j k)
    _ = _ := pairSum2 (fun (i : Fin n) (y : Fin n × Fin n) => f i y.1 y.2)

private theorem pairSum4 {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ a, f i j k a) =
      ∑ x : PairTuple4 n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  calc
    _ = ∑ i, ∑ y : PairTuple3 n, f i y.1 y.2.1 y.2.2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pairSum3 (fun j k a => f i j k a)
    _ = _ := pairSum2 (fun (i : Fin n) (y : PairTuple3 n) => f i y.1 y.2.1 y.2.2)

private theorem pairSum5 {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, f i j k a b) =
      ∑ x : PairTuple5 n, f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  calc
    _ = ∑ i, ∑ y : PairTuple4 n, f i y.1 y.2.1 y.2.2.1 y.2.2.2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pairSum4 (fun j k a b => f i j k a b)
    _ = _ := pairSum2 (fun (i : Fin n) (y : PairTuple4 n) =>
      f i y.1 y.2.1 y.2.2.1 y.2.2.2)

private theorem pairSum6 {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c, f i j k a b c) =
      ∑ x : PairTuple6 n,
        f x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 := by
  calc
    _ = ∑ i, ∑ y : PairTuple5 n, f i y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact pairSum5 (fun j k a b c => f i j k a b c)
    _ = _ := pairSum2 (fun (i : Fin n) (y : PairTuple5 n) =>
      f i y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2)

private def pairSwap6 {n : ℕ} : PairTuple6 n ≃ PairTuple6 n where
  toFun x :=
    (x.2.2.2.1, (x.2.2.2.2.1, (x.2.2.2.2.2, (x.1, (x.2.1, x.2.2.1)))))
  invFun x :=
    (x.2.2.2.1, (x.2.2.2.2.1, (x.2.2.2.2.2, (x.1, (x.2.1, x.2.2.1)))))
  left_inv x := by rcases x with ⟨i, j, k, a, b, c⟩; rfl
  right_inv x := by rcases x with ⟨a, b, c, i, j, k⟩; rfl

private theorem c3Pair_star_of_isHermitian {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (A B : Fin n → Fin n → Fin n → ℂ)
    (hG : (g z).IsHermitian) : c3Pair g z A B = star (c3Pair g z B A) := by
  have hI : ((g z)⁻¹).IsHermitian := hG.inv
  unfold c3Pair
  simp only [star_sum, star_mul, star_star]
  simp_rw [hG.apply, hI.apply]
  calc
    _ = ∑ x : PairTuple6 n,
        g z x.1 x.2.2.2.1 * (g z)⁻¹ x.2.2.2.2.1 x.2.1 *
          (g z)⁻¹ x.2.2.2.2.2 x.2.2.1 *
          A x.1 x.2.1 x.2.2.1 * star (B x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by
      exact pairSum6 (fun i j k a b c =>
        g z i a * (g z)⁻¹ b j * (g z)⁻¹ c k * A i j k * star (B a b c))
    _ = ∑ x : PairTuple6 n,
        A x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 *
          (star (B x.1 x.2.1 x.2.2.1) *
            ((g z)⁻¹ x.2.2.1 x.2.2.2.2.2 *
              ((g z)⁻¹ x.2.1 x.2.2.2.2.1 * g z x.2.2.2.1 x.1))) := by
      exact Fintype.sum_equiv pairSwap6 _ _ (by
        intro x
        rcases x with ⟨i, j, k, a, b, c⟩
        simp [pairSwap6]
        ring_nf)
    _ = _ := by
      symm
      exact pairSum6 (fun i j k a b c =>
        A a b c * (star (B i j k) *
          ((g z)⁻¹ k c * ((g z)⁻¹ j b * g z a i))))

private theorem c3PartialBar_eq_star_partialZ_star {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (q : Fin n) (hf : DifferentiableAt ℝ f z) :
    c3PartialBar f z q = star (c3PartialZ (fun w ↦ star (f w)) z q) := by
  have h := c3Pair_partialZ_star f z q hf
  simpa only [star_star] using (congrArg star h).symm

private theorem c3Pair_bar_firstjet_of_hermitian
    {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hLeibniz : c3MetricPairLeibnizOn g U)
    (hG : ∀ w ∈ U, (g w).IsHermitian)
    (A B : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ)
    (hA : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ A w i j k) U)
    (hB : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ B w i j k) U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (hf : DifferentiableAt ℝ (fun w ↦ c3Pair g w (A w) (B w)) z)
    (q : Fin n) :
    c3PartialBar (fun w ↦ c3Pair g w (A w) (B w)) z q =
      c3Pair g z (fun i j k ↦ c3PartialBar (fun w ↦ A w i j k) z q) (B z) +
        c3Pair g z (A z) (c3TensorCovariantZ g B z q) := by
  have hEq : (fun w ↦ star (c3Pair g w (A w) (B w))) =ᶠ[𝓝 z]
      (fun w ↦ c3Pair g w (B w) (A w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simpa using congrArg star (c3Pair_star_of_isHermitian g w (A w) (B w) (hG w hw))
  have hder := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq
  have hpart :
      c3PartialZ (fun w ↦ star (c3Pair g w (A w) (B w))) z q =
        c3PartialZ (fun w ↦ c3Pair g w (B w) (A w)) z q := by
    unfold c3PartialZ
    rw [hder]
  rw [c3PartialBar_eq_star_partialZ_star _ _ q hf, hpart,
    hLeibniz B A hB hA z hz q]
  simp only [star_add]
  rw [← c3Pair_star_of_isHermitian g z (A z)
    (c3TensorCovariantZ g B z q) (hG z hz)]
  rw [← c3Pair_star_of_isHermitian g z
    (fun i j k ↦ c3PartialBar (fun w ↦ A w i j k) z q) (B z) (hG z hz)]
  exact add_comm _ _

private theorem c3Pair_first_derivative_of_leibniz
    (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsPotential φ) (x : M)
    (hLeibniz : c3MetricPairLeibnizOn (c3PerturbedMetricInChart ω₀ φ x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (p : Fin n) :
    c3PartialZ
        (fun w ↦ c3Pair (c3PerturbedMetricInChart ω₀ φ x) w
          (c3ConnectionDifferenceInChart ω₀ φ x w)
          (c3ConnectionDifferenceInChart ω₀ φ x w)) z p =
      c3Pair (c3PerturbedMetricInChart ω₀ φ x) z
        (c3TensorCovariantZ (c3PerturbedMetricInChart ω₀ φ x)
          (c3ConnectionDifferenceInChart ω₀ φ x) z p)
        (c3ConnectionDifferenceInChart ω₀ φ x z) +
      c3Pair (c3PerturbedMetricInChart ω₀ φ x) z
        (c3ConnectionDifferenceInChart ω₀ φ x z)
        (fun i j k ↦ c3PartialBar
          (fun w ↦ c3ConnectionDifferenceInChart ω₀ φ x w i j k) z p) := by
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x
  have hT : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ T w i j k)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    simpa [T] using c3ConnectionDifference_contDiffOn_target ω₀ φ hφ x
  simpa [g, T] using hLeibniz T T hT hT z hz p

private theorem c3ConnectionDifference_mixed_derivative_commute
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ) (x : M)
    (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (i j k p q : Fin n) :
    c3PartialBar
        (fun w ↦ c3PartialZ
          (fun v ↦ c3ConnectionDifferenceInChart ω₀ φ x v i j k) w p) z q =
      c3PartialZ
        (fun w ↦ c3PartialBar
          (fun v ↦ c3ConnectionDifferenceInChart ω₀ φ x v i j k) w q) z p := by
  have hT : ContDiffAt ℝ ∞
      (fun v ↦ c3ConnectionDifferenceInChart ω₀ φ x v i j k) z :=
    c3ConnectionDifference_contDiffAt ω₀ φ hφ x z hz i j k
  simpa [c3PartialBar, c3PartialZ, chartPartialBarComplex, chartPartialZComplex] using
    (c3PartialBar_partialZ_comm
      (fun v ↦ c3ConnectionDifferenceInChart ω₀ φ x v i j k) z hT p q)

private theorem c3Pair_secondjet_of_leibniz
    {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hLeibniz : c3MetricPairLeibnizOn g U)
    (hG : ∀ w ∈ U, (g w).IsHermitian)
    (A B : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ)
    (hA : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ A w i j k) U)
    (hB : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ B w i j k) U)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (p q : Fin n)
    (hDA : ∀ i j k, ContDiffOn ℝ ∞
      (fun w ↦ c3TensorCovariantZ g A w p i j k) U)
    (hBbar : ∀ i j k, ContDiffOn ℝ ∞
      (fun w ↦ c3PartialBar (fun v ↦ B v i j k) w p) U)
    (hDPair : DifferentiableAt ℝ
      (fun w ↦ c3Pair g w (c3TensorCovariantZ g A w p) (B w)) z)
    (hBbarPair : DifferentiableAt ℝ
      (fun w ↦ c3Pair g w (A w)
        (fun i j k ↦ c3PartialBar (fun v ↦ B v i j k) w p)) z) :
    c3PartialBar (fun w ↦ c3PartialZ (fun v ↦ c3Pair g v (A v) (B v)) w p) z q =
      c3Pair g z (fun i j k ↦
        c3PartialBar (fun w ↦ c3TensorCovariantZ g A w p i j k) z q) (B z) +
      c3Pair g z (c3TensorCovariantZ g A z p)
        (c3TensorCovariantZ g B z q) +
      c3Pair g z (fun i j k ↦ c3PartialBar (fun w ↦ A w i j k) z q)
        (fun i j k ↦ c3PartialBar (fun w ↦ B w i j k) z p) +
      c3Pair g z (A z) (c3TensorCovariantZ g
        (fun w i j k ↦ c3PartialBar (fun v ↦ B v i j k) w p) z q) := by
  let D : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ :=
    fun w i j k ↦ c3TensorCovariantZ g A w p i j k
  let C : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ :=
    fun w i j k ↦ c3PartialBar (fun v ↦ B v i j k) w p
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ c3Pair g w (D w) (B w)
  let G : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ c3Pair g w (A w) (C w)
  have hEq : (fun w ↦ c3PartialZ (fun v ↦ c3Pair g v (A v) (B v)) w p) =ᶠ[𝓝 z]
      (F + G) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simpa [F, G, D, C] using hLeibniz A B hA hB w hw p
  have hbarEq : c3PartialBar
      (fun w ↦ c3PartialZ (fun v ↦ c3Pair g v (A v) (B v)) w p) z q =
      c3PartialBar (F + G) z q := by
    unfold c3PartialBar
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hEq]
  have hfd : fderiv ℝ (F + G) z = fderiv ℝ F z + fderiv ℝ G z :=
    fderiv_add hDPair hBbarPair
  have hadd : c3PartialBar (F + G) z q =
      c3PartialBar F z q + c3PartialBar G z q := by
    unfold c3PartialBar
    rw [hfd]
    simp only [add_apply]
    ring
  have hfirst := c3Pair_bar_firstjet_of_hermitian g U hU hLeibniz hG
    D B hDA hB z hz hDPair q
  have hsecond := c3Pair_bar_firstjet_of_hermitian g U hU hLeibniz hG
    A C hA hBbar z hz hBbarPair q
  rw [hbarEq, hadd, hfirst, hsecond]
  simp only [D, C]
  abel

private theorem c3SecondDirectionalFDeriv {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (x : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f x) (u v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u =
      fderiv ℝ (fderiv ℝ f) x u v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hc := fderiv_clm_apply hD (differentiableAt_const v)
  rw [hc]
  simp [ContinuousLinearMap.flip_apply]

private theorem c3PartialZDerivApply {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (u : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    fderiv ℝ (fun y ↦ c3PartialZ f y j) z u =
      (fderiv ℝ (fderiv ℝ f) z u (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ (fderiv ℝ f) z u (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  have he : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hie : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hs : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    he.sub (hie.const_mul Complex.I)
  unfold c3PartialZ
  rw [show (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) / 2) =
      (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) -
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) * (2 : ℂ)⁻¹) by
        funext y; rw [div_eq_mul_inv]]
  rw [fderiv_mul_const hs (2 : ℂ)⁻¹]
  rw [fderiv_fun_sub he (hie.const_mul Complex.I)]
  rw [fderiv_const_mul hie Complex.I]
  simp only [_root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  rw [c3SecondDirectionalFDeriv f z hf u (EuclideanSpace.single j 1),
    c3SecondDirectionalFDeriv f z hf u (Complex.I • EuclideanSpace.single j 1)]
  ring

private theorem c3PartialBarDerivApply {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (u : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    fderiv ℝ (fun y ↦ c3PartialBar f y j) z u =
      (fderiv ℝ (fderiv ℝ f) z u (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ (fderiv ℝ f) z u (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  have he : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hie : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    (ContDiffAt.clm_apply ((hf).fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hs : DifferentiableAt ℝ
      (fun y ↦ fderiv ℝ f y (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) z :=
    he.add (hie.const_mul Complex.I)
  unfold c3PartialBar
  rw [show (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) / 2) =
      (fun y ↦ (fderiv ℝ f y (EuclideanSpace.single j 1) +
        Complex.I * fderiv ℝ f y (Complex.I • EuclideanSpace.single j 1)) * (2 : ℂ)⁻¹) by
        funext y; rw [div_eq_mul_inv]]
  rw [fderiv_mul_const hs (2 : ℂ)⁻¹]
  rw [fderiv_fun_add he (hie.const_mul Complex.I)]
  rw [fderiv_const_mul hie Complex.I]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [c3SecondDirectionalFDeriv f z hf u (EuclideanSpace.single j 1),
    c3SecondDirectionalFDeriv f z hf u (Complex.I • EuclideanSpace.single j 1)]
  ring

private theorem c3OfRealFDeriv {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun w ↦ (f w : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ f z) := by
  exact (Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt).fderiv

private theorem c3RealSecondDirectionalFDeriv {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (x : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f x) (u v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u =
      fderiv ℝ (fderiv ℝ f) x u v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hc := fderiv_clm_apply hD (differentiableAt_const v)
  rw [hc]
  simp [ContinuousLinearMap.flip_apply]

private theorem c3RealCastSecondDirectional {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (u v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun w ↦ (f w : ℂ))) z u v =
      (fderiv ℝ (fderiv ℝ f) z u v : ℂ) := by
  let fc : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ (f w : ℂ)
  have hCLM : ContDiffAt ℝ 2 (fun r : ℝ ↦ (r : ℂ)) (f z) :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hfc : ContDiffAt ℝ 2 fc z := hCLM.comp z hf
  have hpoint : (fun w ↦ fderiv ℝ fc w v) =ᶠ[𝓝 z]
      (fun w ↦ (fderiv ℝ f w v : ℂ)) := by
    filter_upwards [hf.eventually (by norm_num : (2 : ℕ∞ω) ≠ ∞)] with w hw
    have h := c3OfRealFDeriv f w (hw.differentiableAt (by norm_num))
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ => L v) h
    simpa [fc, ContinuousLinearMap.comp_apply] using h'
  have hfd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hpoint
  have hg : DifferentiableAt ℝ (fun w ↦ fderiv ℝ f w v) z :=
    (ContDiffAt.clm_apply (hf.fderiv_right (m := 1) (by norm_num))
      contDiffAt_const).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hder := c3OfRealFDeriv (fun w ↦ fderiv ℝ f w v) z hg
  have hEval := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ => L u) hder
  rw [← c3SecondDirectionalFDeriv fc z hfc u v]
  rw [hfd]
  have hsecond := c3RealSecondDirectionalFDeriv f z hf u v
  simp only [ContinuousLinearMap.comp_apply] at hEval
  rw [hsecond] at hEval
  exact hEval

private theorem c3ComplexHessian_eq_mixedWirtinger {n : ℕ}
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n))
    (hf : ContDiffAt ℝ 2 f z) (p q : Fin n) :
    complexHessian f z p q =
      c3PartialBar (fun w ↦ c3PartialZ (fun v ↦ (f v : ℂ)) w p) z q := by
  let fc : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ (f w : ℂ)
  have hCLM : ContDiffAt ℝ 2 (fun r : ℝ ↦ (r : ℂ)) (f z) :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have hfc : ContDiffAt ℝ 2 fc z := hCLM.comp z hf
  rw [complexHessian_apply hf p q]
  unfold c3PartialBar
  rw [c3PartialZDerivApply fc z hfc (EuclideanSpace.single q 1) p,
    c3PartialZDerivApply fc z hfc (Complex.I • EuclideanSpace.single q 1) p]
  rw [c3RealCastSecondDirectional f z hf (EuclideanSpace.single q 1)
      (EuclideanSpace.single p 1),
    c3RealCastSecondDirectional f z hf (EuclideanSpace.single q 1)
      (Complex.I • EuclideanSpace.single p 1),
    c3RealCastSecondDirectional f z hf (Complex.I • EuclideanSpace.single q 1)
      (EuclideanSpace.single p 1),
    c3RealCastSecondDirectional f z hf (Complex.I • EuclideanSpace.single q 1)
      (Complex.I • EuclideanSpace.single p 1)]
  have hsymm (u v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ f) z u v = fderiv ℝ (fderiv ℝ f) z v u :=
    ContDiffAt.isSymmSndFDerivAt hf (by norm_num) u v
  rw [hsymm (EuclideanSpace.single q 1) (EuclideanSpace.single p 1),
    hsymm (Complex.I • EuclideanSpace.single q 1) (Complex.I • EuclideanSpace.single p 1),
    hsymm (EuclideanSpace.single q 1) (Complex.I • EuclideanSpace.single p 1),
    hsymm (Complex.I • EuclideanSpace.single q 1) (EuclideanSpace.single p 1)]
  ring_nf
  simp only [Complex.I_sq]
  ring_nf

private theorem c3ContDiffOnPair
    {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (A B : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ g w i j) U)
    (hGinv : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ (g w)⁻¹ i j) U)
    (hA : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ A w i j k) U)
    (hB : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ B w i j k) U) :
    ContDiffOn ℝ ∞ (fun w ↦ c3Pair g w (A w) (B w)) U := by
  have hterm (i j k a b c : Fin n) : ContDiffOn ℝ ∞
      (fun w ↦ g w i a * (g w)⁻¹ b j * (g w)⁻¹ c k *
        A w i j k * star (B w a b c)) U := by
    have hstar : ContDiffOn ℝ ∞ (fun w ↦ star (B w a b c)) U := by
      change ContDiffOn ℝ ∞ (Complex.conjCLE ∘ fun w ↦ B w a b c) U
      exact Complex.conjCLE.contDiff.comp_contDiffOn (hB a b c)
    exact ((((hG i a).mul (hGinv b j)).mul (hGinv c k)).mul
      (hA i j k)).mul hstar
  unfold c3Pair
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  apply ContDiffOn.sum
  intro k hk
  apply ContDiffOn.sum
  intro a ha
  apply ContDiffOn.sum
  intro b hb
  apply ContDiffOn.sum
  intro c hc
  exact hterm i j k a b c

private theorem c3ContDiffOnPartialZScalar
    {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (j : Fin n) :
    ContDiffOn ℝ ∞ (fun z ↦ c3PartialZ f z j) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by rw [ENat.coe_top_add_one])
  have hD₁ : ContDiffOn ℝ ∞
      (fun z ↦ fderiv ℝ f z (EuclideanSpace.single j 1)) U :=
    hD.clm_apply contDiffOn_const
  have hD₂ : ContDiffOn ℝ ∞
      (fun z ↦ fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) U :=
    hD.clm_apply contDiffOn_const
  change ContDiffOn ℝ ∞
    (fun z ↦ (fderiv ℝ f z (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2) U
  exact (hD₁.sub (contDiffOn_const.mul hD₂)).div_const (2 : ℂ)

private theorem c3ContDiffOnPartialBarScalar
    {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hf : ContDiffOn ℝ ∞ f U)
    (j : Fin n) :
    ContDiffOn ℝ ∞ (fun z ↦ c3PartialBar f z j) U := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by rw [ENat.coe_top_add_one])
  have hD₁ : ContDiffOn ℝ ∞
      (fun z ↦ fderiv ℝ f z (EuclideanSpace.single j 1)) U :=
    hD.clm_apply contDiffOn_const
  have hD₂ : ContDiffOn ℝ ∞
      (fun z ↦ fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) U :=
    hD.clm_apply contDiffOn_const
  change ContDiffOn ℝ ∞
    (fun z ↦ (fderiv ℝ f z (EuclideanSpace.single j 1) +
      Complex.I * fderiv ℝ f z (Complex.I • EuclideanSpace.single j 1)) / 2) U
  exact (hD₁.add (contDiffOn_const.mul hD₂)).div_const (2 : ℂ)

private theorem c3TensorCovariantZ_contDiffOn
    {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (A : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ)
    (hA : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ A w i j k) U)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ g w i j) U)
    (hGinv : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ (g w)⁻¹ i j) U)
    (p i j k : Fin n) :
    ContDiffOn ℝ ∞ (fun w ↦ c3TensorCovariantZ g A w p i j k) U := by
  have hPart := c3ContDiffOnPartialZScalar hU (hA i j k) p
  have hUpper : ContDiffOn ℝ ∞
      (fun w ↦ ∑ r, c3ChristoffelInChart g w i p r * A w r j k) U := by
    apply ContDiffOn.sum
    intro r hr
    exact (c3Christoffel_contDiffOn hU hG hGinv i p r).mul (hA r j k)
  have hLower₁ : ContDiffOn ℝ ∞
      (fun w ↦ ∑ r, c3ChristoffelInChart g w r p j * A w i r k) U := by
    apply ContDiffOn.sum
    intro r hr
    exact (c3Christoffel_contDiffOn hU hG hGinv r p j).mul (hA i r k)
  have hLower₂ : ContDiffOn ℝ ∞
      (fun w ↦ ∑ r, c3ChristoffelInChart g w r p k * A w i j r) U := by
    apply ContDiffOn.sum
    intro r hr
    exact (c3Christoffel_contDiffOn hU hG hGinv r p k).mul (hA i j r)
  change ContDiffOn ℝ ∞
    (fun w ↦ c3PartialZ (fun v ↦ A v i j k) w p +
      (∑ r, c3ChristoffelInChart g w i p r * A w r j k) -
      (∑ r, c3ChristoffelInChart g w r p j * A w i r k) -
      (∑ r, c3ChristoffelInChart g w r p k * A w i j r)) U
  exact ((hPart.add hUpper).sub hLower₁).sub hLower₂

private theorem fourthScalarHermitianSwap {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hG : (g z).IsHermitian)
    (a : ℂ) (T V : Fin n → Fin n → Fin n → ℂ) :
    (a * c3Pair g z T V).re = (star a * c3Pair g z V T).re := by
  rw [c3Pair_star_of_isHermitian g z T V hG]
  calc
    (a * star (c3Pair g z V T)).re =
        (star (a * star (c3Pair g z V T))).re := by
          rw [Complex.star_def, Complex.conj_re]
    _ = (star (star (c3Pair g z V T)) * star a).re := by rw [star_mul]
    _ = (c3Pair g z V T * star a).re := by rw [star_star]
    _ = (star a * c3Pair g z V T).re := by rw [mul_comm]

private theorem fourthScalarInverseSwap {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hG : (g z).IsHermitian)
    (p q : Fin n) (T V : Fin n → Fin n → Fin n → ℂ) :
    ((g z)⁻¹ q p * c3Pair g z T V).re =
      ((g z)⁻¹ p q * c3Pair g z V T).re := by
  rw [fourthScalarHermitianSwap g z hG ((g z)⁻¹ q p) T V]
  have hInv : ((g z)⁻¹).IsHermitian := hG.inv
  have hEntry : star ((g z)⁻¹ q p) = (g z)⁻¹ p q := by
    have h := hInv.apply q p
    simpa only [star_star] using (congrArg star h).symm
  rw [hEntry]

private theorem fourthScalarDoubleSumSwap {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hG : (g z).IsHermitian)
    (T : Fin n → Fin n → Fin n → ℂ)
    (V : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ q, ∑ p, ((g z)⁻¹ q p * c3Pair g z T (V q p)).re) =
      ∑ q, ∑ p, ((g z)⁻¹ q p * c3Pair g z (V p q) T).re := by
  calc
    _ = ∑ q, ∑ p,
        ((g z)⁻¹ p q * c3Pair g z (V q p) T).re := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      exact fourthScalarInverseSwap g z hG p q T (V q p)
    _ = ∑ p, ∑ q,
        ((g z)⁻¹ p q * c3Pair g z (V q p) T).re := by
      rw [Finset.sum_comm]
    _ = ∑ q, ∑ p,
        ((g z)⁻¹ q p * c3Pair g z (V p q) T).re := by
      rw [Finset.sum_comm]

private theorem c3Pair_double_sum_left {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (A : Fin n → Fin n → ℂ)
    (V : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (T : Fin n → Fin n → Fin n → ℂ) :
    c3Pair g z (fun i j k ↦ ∑ p, ∑ q, A q p * V p q i j k) T =
      ∑ p, ∑ q, A q p * c3Pair g z (V p q) T := by
  simp_rw [c3Pair, pairSum6, Finset.mul_sum, Finset.sum_mul]
  simp_rw [pairSum2]
  let e : PairTuple6 n × (Fin n × Fin n) ≃ Fin n × (Fin n × PairTuple6 n) :=
    ⟨fun x ↦ (x.2.1, (x.2.2, x.1)),
      fun x ↦ (x.2.2, (x.1, x.2.1)),
      by intro x; rcases x with ⟨I, p, q⟩; rfl,
      by intro x; rcases x with ⟨p, q, I⟩; rfl⟩
  apply Fintype.sum_equiv e
  intro x
  rcases x with ⟨I, ⟨p, q⟩⟩
  rcases I with ⟨i, j, k, a, b, c⟩
  simp only [e, Equiv.coe_fn_mk, PairTuple6, PairTuple5, PairTuple4, PairTuple3]
  ring

set_option maxHeartbeats 1000000 in
theorem c3ChartPairHessianLaplacian_eq_ordered_pair_of_leibniz
    (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ω₀.IsPotential φ) (x : M)
    (hLeibniz : c3MetricPairLeibnizOn (c3PerturbedMetricInChart ω₀ φ x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    c3ChartPairHessianLaplacian ω₀ φ x =
      c3BochnerDerivativeSquares ω₀ φ x +
        (c3Pair (c3PerturbedMetricInChart ω₀ φ x)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x)
          (c3OppositeConnectionTensorLaplacian ω₀ φ x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
          (c3ConnectionDifferenceInChart ω₀ φ x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))).re +
        c3BochnerConnectionTerm ω₀ φ x := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let U := e.target
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := c3ConnectionDifferenceInChart ω₀ φ x
  let z := e x
  have hcenterExt : z = (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) x := by rfl
  have hgcenterExt : g z = c3PerturbedMetricInChart ω₀ φ x
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) x) := by rfl
  have hTcenterExt : T z = c3ConnectionDifferenceInChart ω₀ φ x
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) x) := by rfl
  have hcenterChart : z = (chartAt (EuclideanSpace ℂ (Fin n)) x) x := by rfl
  have hgcenterChart : g z = c3PerturbedMetricInChart ω₀ φ x
      ((chartAt (EuclideanSpace ℂ (Fin n)) x) x) := by rfl
  have hTcenterChart : T z = c3ConnectionDifferenceInChart ω₀ φ x
      ((chartAt (EuclideanSpace ℂ (Fin n)) x) x) := by rfl
  have hEndpointCenter : c3ChartPairHessianLaplacian ω₀ φ x =
      (((g z)⁻¹ * complexHessian (fun w ↦ (c3Pair g w (T w) (T w)).re) z).trace).re := by rfl
  have hOppCenterChart (i j k : Fin n) :
      c3OppositeConnectionTensorLaplacian ω₀ φ x
          ((chartAt (EuclideanSpace ℂ (Fin n)) x) x) i j k =
        ∑ p, ∑ q, (g z)⁻¹ q p *
          c3PartialBar (fun w ↦ c3TensorCovariantZ g T w p i j k) z q := by rfl
  have hDerivativeSquaresCenter :
      c3BochnerDerivativeSquares ω₀ φ x =
        c3DerivativeSquares g (c3TensorCovariantZ g T z)
          (fun q i j k ↦ c3PartialBar (fun w ↦ T w i j k) z q) z := by rfl
  have hU : IsOpen U := isOpen_extChartAt_target x
  have hz : z ∈ U := by
    simpa [z, U, e] using mem_extChartAt_target x
  have hTOn : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ T w i j k) U := by
    intro i j k
    apply hU.contDiffOn_iff.mpr
    intro w hw
    exact c3ConnectionDifference_contDiffAt ω₀ φ hφ x w hw i j k
  have hG : ∀ a b, ContDiffOn ℝ ∞ (fun w ↦ g w a b) U := by
    intro a b
    have hreg := (ω₀.perturb φ hφ).contDiffOn_metricInChart x a b
    apply hreg.congr
    intro w hw
    have heq : g w = (ω₀.perturb φ hφ).metricInChart x w := by
      exact (ω₀.metricInChart_perturb hφ x hw).symm
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A a b) heq
  have hGUnit : ∀ w ∈ U, IsUnit (g w) := by
    intro w hw
    have hunit := (ω₀.perturb φ hφ).posDef_metricInChart x hw |>.isUnit
    have heq : g w = (ω₀.perturb φ hφ).metricInChart x w := by
      exact (ω₀.metricInChart_perturb hφ x hw).symm
    rw [heq]
    exact hunit
  have hGinv := Matrix.contDiffOn_inverse_entries hG hGUnit
  have hΓ : ∀ i j k, ContDiffOn ℝ ∞
      (fun w ↦ c3ChristoffelInChart g w i j k) U := by
    intro i j k
    exact c3Christoffel_contDiffOn hU hG hGinv i j k
  let D (p : Fin n) : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ :=
    fun w i j k ↦ c3TensorCovariantZ g T w p i j k
  let C (p : Fin n) : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ :=
    fun w i j k ↦ c3PartialBar (fun v ↦ T v i j k) w p
  have hDOn (p : Fin n) : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ D p w i j k) U := by
    intro i j k
    have hpart := c3ContDiffOnPartialZScalar hU (hTOn i j k) p
    have hupper : ContDiffOn ℝ ∞
        (fun w ↦ ∑ r, c3ChristoffelInChart g w i p r * T w r j k) U := by
      apply ContDiffOn.sum
      intro r hr
      exact (hΓ i p r).mul (hTOn r j k)
    have hlower₁ : ContDiffOn ℝ ∞
        (fun w ↦ ∑ r, c3ChristoffelInChart g w r p j * T w i r k) U := by
      apply ContDiffOn.sum
      intro r hr
      exact (hΓ r p j).mul (hTOn i r k)
    have hlower₂ : ContDiffOn ℝ ∞
        (fun w ↦ ∑ r, c3ChristoffelInChart g w r p k * T w i j r) U := by
      apply ContDiffOn.sum
      intro r hr
      exact (hΓ r p k).mul (hTOn i j r)
    change ContDiffOn ℝ ∞
      (fun w ↦ c3PartialZ (fun v ↦ T v i j k) w p +
        (∑ r, c3ChristoffelInChart g w i p r * T w r j k) -
        (∑ r, c3ChristoffelInChart g w r p j * T w i r k) -
        (∑ r, c3ChristoffelInChart g w r p k * T w i j r)) U
    exact ((hpart.add hupper).sub hlower₁).sub hlower₂
  have hCOn (p : Fin n) : ∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ C p w i j k) U := by
    intro i j k
    exact c3ContDiffOnPartialBarScalar hU (hTOn i j k) p
  have hDPairOn (p : Fin n) : ContDiffOn ℝ ∞
      (fun w ↦ c3Pair g w (D p w) (T w)) U :=
    c3ContDiffOnPair g (D p) T hG hGinv (hDOn p) hTOn
  have hCpairOn (p : Fin n) : ContDiffOn ℝ ∞
      (fun w ↦ c3Pair g w (T w) (C p w)) U :=
    c3ContDiffOnPair g T (C p) hG hGinv hTOn (hCOn p)
  have hDPair (p : Fin n) : DifferentiableAt ℝ
      (fun w ↦ c3Pair g w (D p w) (T w)) z :=
    (hDPairOn p).contDiffAt (hU.mem_nhds hz) |>.differentiableAt (by norm_num)
  have hCpair (p : Fin n) : DifferentiableAt ℝ
      (fun w ↦ c3Pair g w (T w) (C p w)) z :=
    (hCpairOn p).contDiffAt (hU.mem_nhds hz) |>.differentiableAt (by norm_num)
  have hHerm : ∀ w ∈ U, (g w).IsHermitian := by
    intro w hw
    let : PartialOrder ℂ := Complex.partialOrder
    have hmetric := ω₀.metricInChart_perturb hφ x hw
    change (ω₀.metricInChart x w +
      complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w).IsHermitian
    rw [← hmetric]
    exact (ω₀.perturb φ hφ).posDef_metricInChart x hw |>.isHermitian
  have hSecond (p q : Fin n) :=
    c3Pair_secondjet_of_leibniz g U hU hLeibniz hHerm T T hTOn hTOn z hz p q
      (hDOn p) (hCOn p) (hDPair p) (hCpair p)
  have hPairTTOn : ContDiffOn ℝ ∞ (fun w ↦ c3Pair g w (T w) (T w)) U :=
    c3ContDiffOnPair g T T hG hGinv hTOn hTOn
  have hRealOn : ContDiffOn ℝ ∞
      (fun w ↦ (c3Pair g w (T w) (T w)).re) U := by
    change ContDiffOn ℝ ∞
      (Complex.reCLM ∘ fun w ↦ c3Pair g w (T w) (T w)) U
    exact Complex.reCLM.contDiff.comp_contDiffOn hPairTTOn
  have hRealAt : ContDiffAt ℝ 2 (fun w ↦ (c3Pair g w (T w) (T w)).re) z := by
    exact (hRealOn.contDiffAt (hU.mem_nhds hz)).of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.2 le_top)
  have hHessian (p q : Fin n) :=
    c3ComplexHessian_eq_mixedWirtinger
      (fun w ↦ (c3Pair g w (T w) (T w)).re) z hRealAt p q
  change (((g z)⁻¹ * complexHessian (fun w ↦ (c3Pair g w (T w) (T w)).re) z).trace).re = _
  have hPairReal (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ U) :
      c3Pair g w (T w) (T w) = ((c3Pair g w (T w) (T w)).re : ℂ) := by
    have hs := c3Pair_star_of_isHermitian g w (T w) (T w) (hHerm w hw)
    have him : (c3Pair g w (T w) (T w)).im = 0 := by
      have hc := congrArg Complex.im hs
      change (c3Pair g w (T w) (T w)).im =
        -(c3Pair g w (T w) (T w)).im at hc
      linarith
    apply Complex.ext
    · rfl
    · simp [him]
  have hFirstEq (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ U) (p : Fin n) :
      c3PartialZ (fun v ↦ c3Pair g v (T v) (T v)) w p =
        c3PartialZ (fun v ↦ ((c3Pair g v (T v) (T v)).re : ℂ)) w p := by
    unfold c3PartialZ
    have heq : (fun v ↦ c3Pair g v (T v) (T v)) =ᶠ[𝓝 w]
        (fun v ↦ ((c3Pair g v (T v) (T v)).re : ℂ)) := by
      filter_upwards [hU.mem_nhds hw] with v hv
      exact hPairReal v hv
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq]
  have hOuterEq (p : Fin n) :
      (fun w ↦ c3PartialZ (fun v ↦ c3Pair g v (T v) (T v)) w p) =ᶠ[𝓝 z]
        (fun w ↦ c3PartialZ (fun v ↦ ((c3Pair g v (T v) (T v)).re : ℂ)) w p) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hFirstEq w hw p
  have hHessEq (p q : Fin n) :
      complexHessian (fun w ↦ (c3Pair g w (T w) (T w)).re) z p q =
        c3PartialBar (fun w ↦ c3PartialZ (fun v ↦ c3Pair g v (T v) (T v)) w p) z q := by
    rw [hHessian p q]
    unfold c3PartialBar
    rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (hOuterEq p)]
  have hHessianSecondJet (p q : Fin n) :
      complexHessian (fun w ↦ (c3Pair g w (T w) (T w)).re) z p q =
        c3Pair g z (fun i j k ↦
          c3PartialBar (fun w ↦ c3TensorCovariantZ g T w p i j k) z q) (T z) +
        c3Pair g z (c3TensorCovariantZ g T z p) (c3TensorCovariantZ g T z q) +
        c3Pair g z (fun i j k ↦ c3PartialBar (fun w ↦ T w i j k) z q)
          (fun i j k ↦ c3PartialBar (fun w ↦ T w i j k) z p) +
        c3Pair g z (T z) (c3TensorCovariantZ g
          (fun w i j k ↦ c3PartialBar (fun v ↦ T v i j k) w p) z q) := by
    calc
      _ = c3PartialBar
          (fun w ↦ c3PartialZ (fun v ↦ c3Pair g v (T v) (T v)) w p) z q := hHessEq p q
      _ = _ := hSecond p q
  have hTerm2Alias :
      (∑ i, ∑ j, (g z)⁻¹ i j *
        c3Pair g z (c3TensorCovariantZ g T z j) (c3TensorCovariantZ g T z i)) =
      ∑ p, ∑ q, (g z)⁻¹ q p *
        c3Pair g z (c3TensorCovariantZ g T z p) (c3TensorCovariantZ g T z q) := by
    calc
      _ = ∑ j, ∑ i, (g z)⁻¹ i j *
          c3Pair g z (c3TensorCovariantZ g T z j) (c3TensorCovariantZ g T z i) := Finset.sum_comm
      _ = _ := rfl
  let Dbar (p q : Fin n) : Fin n → Fin n → Fin n → ℂ :=
    c3TensorCovariantZ g
      (fun w i j k ↦ c3PartialBar (fun v ↦ T v i j k) w p) z q
  have hInvHerm : ((g z)⁻¹).IsHermitian := (hHerm z hz).inv
  have hConnStar :
      star (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (Dbar q p) (T z)) =
        ∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (T z) (Dbar p q) := by
    simp only [star_sum, star_mul, hInvHerm.apply]
    simp_rw [show ∀ p q, star (c3Pair g z (Dbar q p) (T z)) =
      c3Pair g z (T z) (Dbar q p) from fun p q =>
        (c3Pair_star_of_isHermitian g z (T z) (Dbar q p) (hHerm z hz)).symm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have hConnRe :
      (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (T z) (Dbar p q)).re =
        (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (Dbar q p) (T z)).re := by
    have hc := congrArg Complex.re hConnStar
    simpa only [Complex.star_def, Complex.conj_re] using hc.symm
  have hConnReSwap :
      (∑ q, ∑ p, (g z)⁻¹ q p * c3Pair g z (T z) (Dbar p q)).re =
        (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (Dbar q p) (T z)).re := by
    rw [Finset.sum_comm]
    exact hConnRe
  have hPairAdd (A A' B : Fin n → Fin n → Fin n → ℂ) :
      c3Pair g z (fun i j k ↦ A i j k + A' i j k) B =
        c3Pair g z A B + c3Pair g z A' B := by
    simp [c3Pair, Finset.sum_add_distrib, mul_add, add_mul]
  have hPairSum {α : Type} [Fintype α]
      (F : α → Fin n → Fin n → Fin n → ℂ)
      (B : Fin n → Fin n → Fin n → ℂ) :
      c3Pair g z (fun i j k ↦ ∑ a, F a i j k) B =
        ∑ a, c3Pair g z (F a) B := by
    classical
    have haux (s : Finset α) :
        c3Pair g z (fun i j k ↦ ∑ a ∈ s, F a i j k) B =
          ∑ a ∈ s, c3Pair g z (F a) B := by
      induction s using Finset.induction_on with
      | empty => simp [c3Pair]
      | @insert a s ha ih =>
          simp only [Finset.sum_insert ha]
          rw [hPairAdd, ih]
    exact haux Finset.univ
  have hPairSmul (a : ℂ) (A B : Fin n → Fin n → Fin n → ℂ) :
      c3Pair g z (fun i j k ↦ a * A i j k) B = a * c3Pair g z A B := by
    unfold c3Pair
    simp_rw [show ∀ i j k a' b c, g z i a' * (g z)⁻¹ b j * (g z)⁻¹ c k *
      (a * A i j k) * star (B a' b c) = a *
        (g z i a' * (g z)⁻¹ b j * (g z)⁻¹ c k * A i j k * star (B a' b c)) from
      fun _ _ _ _ _ _ => by ring]
    simp_rw [← Finset.mul_sum]
  have hPairWeighted (F : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
      (B : Fin n → Fin n → Fin n → ℂ) :
      c3Pair g z (fun i j k ↦ ∑ p, ∑ q, (g z)⁻¹ q p * F p q i j k) B =
        ∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (F p q) B := by
    calc
      _ = ∑ p, c3Pair g z (fun i j k ↦
          ∑ q, (g z)⁻¹ q p * F p q i j k) B := hPairSum _ _
      _ = ∑ p, ∑ q, c3Pair g z (fun i j k ↦
          (g z)⁻¹ q p * F p q i j k) B := by
        congr 1
        funext p
        exact hPairSum _ _
      _ = _ := by simp_rw [hPairSmul]
  have hOppPair :
      (c3Pair (ω₀.c3PerturbedMetricInChart φ x)
        (chartAt (EuclideanSpace ℂ (Fin n)) x x)
        (ω₀.c3OppositeConnectionTensorLaplacian φ x
          (chartAt (EuclideanSpace ℂ (Fin n)) x x))
        (ω₀.c3ConnectionDifferenceInChart φ x (chartAt (EuclideanSpace ℂ (Fin n)) x x))).re =
      (∑ p, ∑ q, (g z)⁻¹ q p *
        c3Pair g z (fun i j k ↦
          c3PartialBar (fun w ↦ c3TensorCovariantZ g T w p i j k) z q) (T z)).re := by
    change (c3Pair g (chartAt (EuclideanSpace ℂ (Fin n)) x x)
      (ω₀.c3OppositeConnectionTensorLaplacian φ x
        (chartAt (EuclideanSpace ℂ (Fin n)) x x))
      (T (chartAt (EuclideanSpace ℂ (Fin n)) x x))).re = _
    have hTensor : ω₀.c3OppositeConnectionTensorLaplacian φ x
        (chartAt (EuclideanSpace ℂ (Fin n)) x x) = fun i j k ↦
          ∑ p, ∑ q, (g z)⁻¹ q p *
            c3PartialBar (fun w ↦ c3TensorCovariantZ g T w p i j k) z q := by
      funext i j k
      exact hOppCenterChart i j k
    rw [hTensor, ← hcenterChart]
    exact congrArg Complex.re (hPairWeighted
      (fun p q i j k ↦ c3PartialBar (fun w ↦ c3TensorCovariantZ g T w p i j k) z q)
      (T z))
  have hConnPair :
      (c3Pair (ω₀.c3PerturbedMetricInChart φ x)
        (chartAt (EuclideanSpace ℂ (Fin n)) x x)
        (ω₀.c3ConnectionTensorLaplacian φ x
          (chartAt (EuclideanSpace ℂ (Fin n)) x x))
        (ω₀.c3ConnectionDifferenceInChart φ x (chartAt (EuclideanSpace ℂ (Fin n)) x x))).re =
      (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z (Dbar q p) (T z)).re := by
    change (c3Pair g (chartAt (EuclideanSpace ℂ (Fin n)) x x)
      (ω₀.c3ConnectionTensorLaplacian φ x
        (chartAt (EuclideanSpace ℂ (Fin n)) x x))
      (T (chartAt (EuclideanSpace ℂ (Fin n)) x x))).re = _
    have hTensor : ω₀.c3ConnectionTensorLaplacian φ x
        (chartAt (EuclideanSpace ℂ (Fin n)) x x) = fun i j k ↦
          ∑ p, ∑ q, (g z)⁻¹ q p * Dbar q p i j k := by
      funext i j k
      dsimp [c3ConnectionTensorLaplacian, Dbar]
      rfl
    rw [hTensor, ← hcenterChart]
    exact congrArg Complex.re (hPairWeighted
      (fun p q ↦ Dbar q p) (T z))
  have hOppReSwap :
      (∑ q, ∑ p, (g z)⁻¹ q p * c3Pair g z
        (fun i j k ↦ c3PartialBar (fun w ↦ c3TensorCovariantZ g T w p i j k) z q)
        (T z)).re =
      (∑ p, ∑ q, (g z)⁻¹ q p * c3Pair g z
        (fun i j k ↦ c3PartialBar (fun w ↦ c3TensorCovariantZ g T w p i j k) z q)
        (T z)).re := by
    rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [hHessianSecondJet]
  rw [hDerivativeSquaresCenter]
  conv_rhs =>
    dsimp [c3DerivativeSquares,
      c3BochnerConnectionTerm, c3ConnectionTensorLaplacian,
      c3OppositeConnectionTensorLaplacian]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hTerm2Alias]
  simp only [Complex.add_re]
  rw [hConnReSwap]
  rw [hOppReSwap, hOppPair, hConnPair]
  ring_nf

end KahlerForm
