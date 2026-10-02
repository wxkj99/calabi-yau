module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Local Hölder control of lower matrix jets

On a sufficiently small Euclidean ball, the uniform bound on the next derivative
makes each lower derivative Lipschitz. A ball of diameter at most one converts
that Lipschitz estimate to the prescribed Hölder exponent in `(0, 1)`.
-/

@[expose] public section

open scoped ContDiff NNReal Topology

/-- A finite `C^{r,α}` bound controls all lower matrix jets in a common local ball.
The radius depends on the open domain and the center, but not on the matrix entry
or derivative order. -/
theorem locally_holder_lower_matrix_jets
    {n r : ℕ} {α K : ℝ≥0} {W : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (hα₁ : α < 1)
    (B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiffOn ℝ r (fun w ↦ B w i j) W)
    (hBH : ∀ i j, HolderBoundOn r α K W (fun w ↦ B w i j))
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ W) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 4 ∧ Metric.closedBall z ρ ⊆ W ∧
      ∀ i j m, m < r → HolderOnWith K α
        (fun w ↦ iteratedFDeriv ℝ m (fun v ↦ B v i j) w) (Metric.ball z ρ) := by
  obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hz)
  let ρ : ℝ := min (R / 2) (1 / 4)
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hρle : ρ ≤ 1 / 4 := by dsimp [ρ]; exact min_le_right _ _
  have hρlt : ρ < R := by
    dsimp [ρ]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hClosed : Metric.closedBall z ρ ⊆ W := by
    intro x hx
    apply hRball
    exact Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) hρlt)
  have hUsubW : Metric.ball z ρ ⊆ W :=
    Metric.ball_subset_closedBall.trans hClosed
  refine ⟨ρ, hρpos, hρle, hClosed, ?_⟩
  intro i j m hmr
  let J := iteratedFDeriv ℝ m (fun v ↦ B v i j)
  have hmWithTop : (m : WithTop ℕ∞) < (r : WithTop ℕ∞) := by
    exact_mod_cast hmr
  have hdiff (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball z ρ) :
      DifferentiableAt ℝ J x := by
    exact ((hB i j).contDiffAt (hW.mem_nhds (hUsubW hx))).differentiableAt_iteratedFDeriv hmWithTop
  have hderiv (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball z ρ) :
      ‖fderiv ℝ J x‖ ≤ (K : ℝ) := by
    change ‖fderiv ℝ (iteratedFDeriv ℝ m (fun v ↦ B v i j)) x‖ ≤ (K : ℝ)
    rw [norm_fderiv_iteratedFDeriv]
    exact (hBH i j).1 (m + 1) (Nat.succ_le_of_lt hmr) x (hUsubW hx)
  have hLip : LipschitzOnWith K J (Metric.ball z ρ) :=
    (convex_ball z ρ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) hdiff hderiv
  have hdiam (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ Metric.ball z ρ)
      (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ Metric.ball z ρ) :
      edist x y ≤ (1 : ENNReal) := by
    have hx' : dist x z < ρ := Metric.mem_ball.mp hx
    have hy' : dist y z < ρ := Metric.mem_ball.mp hy
    have htri : dist x y ≤ dist x z + dist y z := by
      calc
        dist x y ≤ dist x z + dist z y := dist_triangle x z y
        _ = dist x z + dist y z := by rw [dist_comm z y]
    have hdist : dist x y ≤ 1 := by linarith
    rw [edist_dist]
    calc
      ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hdist
      _ = 1 := ENNReal.ofReal_one
  simpa [J] using hLip.holderOnWith.of_le hdiam (le_of_lt hα₁)
