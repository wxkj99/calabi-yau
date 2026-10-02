module

public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.TransitionFrame

/-!
# Four-slot covariance of the reference curvature between centered holomorphic charts

The Jacobian is evaluated at the center of the moving `y`-chart, but the metric relation and
curvature transformation must hold on an *open overlap*, not only at one point. The coordinate
transition need not be affine. The ordered complex slots are holomorphic, antiholomorphic,
holomorphic, antiholomorphic.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem sum_move_first_to_last8 {ι : Type*} [Fintype ι]
    (F : ι → ι → ι → ι → ι → ι → ι → ι → ℂ) :
    (∑ x, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g,
      F x a b c d e f g) =
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, ∑ x,
      F x a b c d e f g := by
  calc
    _ = ∑ a, ∑ x, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g,
        F x a b c d e f g := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g,
        F x a b c d e f g := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ x, ∑ d, ∑ e, ∑ f, ∑ g,
        F x a b c d e f g := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ x, ∑ e, ∑ f, ∑ g,
        F x a b c d e f g := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ x, ∑ f, ∑ g,
        F x a b c d e f g := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ x, ∑ g,
        F x a b c d e f g := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑ g, ∑ x,
        F x a b c d e f g := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro f hf
      exact Finset.sum_comm

private theorem sum_reverse4 {ι : Type*} [Fintype ι]
    (F : ι → ι → ι → ι → ℂ) :
    (∑ u, ∑ v, ∑ w, ∑ t, F u v w t) =
      ∑ t, ∑ w, ∑ v, ∑ u, F u v w t := by
  calc
    _ = ∑ v, ∑ u, ∑ w, ∑ t, F u v w t := Finset.sum_comm
    _ = ∑ v, ∑ w, ∑ u, ∑ t, F u v w t := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Finset.sum_comm
    _ = ∑ v, ∑ w, ∑ t, ∑ u, F u v w t := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      exact Finset.sum_comm
    _ = ∑ w, ∑ v, ∑ t, ∑ u, F u v w t := Finset.sum_comm
    _ = ∑ w, ∑ t, ∑ v, ∑ u, F u v w t := by
      apply Finset.sum_congr rfl
      intro w hw
      exact Finset.sum_comm
    _ = ∑ t, ∑ w, ∑ v, ∑ u, F u v w t := Finset.sum_comm

private theorem sum_prod_four {ι : Type*} [Fintype ι]
    (f g h k : ι → ℂ) :
    (∑ u, ∑ v, ∑ w, ∑ t, f u * g v * h w * k t) =
      (∑ u, f u) * (∑ v, g v) * (∑ w, h w) * (∑ t, k t) := by
  calc
    _ = ∑ t, ∑ w, ∑ v, ∑ u, f u * g v * h w * k t := by
      exact sum_reverse4 _
    _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum]

private theorem referenceCurvatureContractMatrix
    (A P : Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → Fin n → ℂ) (p q j k : Fin n) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      P a p * star (P b q) * P c j * star (P d k) *
        (∑ e, ∑ f, ∑ g, ∑ h,
          A e a * star (A f b) * A g c * star (A h d) * T e f g h)) =
      ∑ e, ∑ f, ∑ g, ∑ h,
        (A * P) e p * star ((A * P) f q) * (A * P) g j *
          star ((A * P) h k) * T e f g h := by
  classical
  simp only [Matrix.mul_apply]
  conv_lhs => simp only [Finset.mul_sum]
  conv_lhs =>
    rw [sum_move_first_to_last8]
    rw [sum_move_first_to_last8]
    rw [sum_move_first_to_last8]
    rw [sum_move_first_to_last8]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro h hh
  have hfactor (u v w t : Fin n) :
      P u p * star (P v q) * P w j * star (P t k) *
        (A e u * star (A f v) * A g w * star (A h t) * T e f g h) =
      (P u p * A e u) * (star (P v q) * star (A f v)) *
        (P w j * A g w) * (star (P t k) * star (A h t) * T e f g h) := by ring
  simp_rw [hfactor]
  rw [sum_prod_four]
  rw [← Finset.sum_mul]
  simp only [star_sum, star_mul]
  have hpA : (∑ u, P u p * A e u) = ∑ u, A e u * P u p := by
    apply Finset.sum_congr rfl
    intro u hu
    ring
  have hqc : (∑ u, P u j * A g u) = ∑ u, A g u * P u j := by
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hpA, hqc]
  ring

/-- At a point in the overlap, the curvature contracted against a frame in the moving chart
is the contraction in the fixed chart against the transported frame. -/
theorem referenceCurvatureComponent_transition (ω₀ : KahlerForm n M) (x y : M)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : ω₀.IsReferenceChartOverlap x y U)
    (P : Matrix (Fin n) (Fin n) ℂ) (p q j k : Fin n) :
    let Q := referenceTransitionMatrix x y * P
    referenceCurvatureComponent ω₀ y P p q j k =
      ∑ a, ∑ b, ∑ c, ∑ d,
        Q a p * star (Q b q) * Q c j * star (Q d k) *
          chartCurvature (fun z ↦ ω₀.metricInChart x z)
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) a b c d := by
  classical
  rcases hU with ⟨hUopen, hz₀, himage, hf, hhol, hjac, hmetric⟩
  let f := referenceChartTransition (n := n) x y
  let z₀ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y
  let A := referenceTransitionMatrix (n := n) x y
  let C := fun a b c d =>
    chartCurvature (ω₀.metricInChart x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) a b c d
  have hcurv := chartCurvature_pullback (U := U) hUopen f hf hhol
    (ω₀.metricInChart y) (ω₀.metricInChart x)
    (fun a b => (ω₀.contDiffOn_metricInChart x a b).mono himage)
    (by
      intro w hw
      exact hmetric w hw)
    z₀ hz₀
    (by
      exact hjac)
    (by
      exact (Matrix.isUnit_iff_isUnit_det _).1
        (ω₀.posDef_metricInChart x (himage ⟨z₀, hz₀, rfl⟩)).isUnit)
  have hcenter : f z₀ = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y := by
    change (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x)
      ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).symm
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y y)) = _
    rw [(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).left_inv
      (mem_extChartAt_source y)]
  have hA : EuclideanSpace.clmMatrix (fderiv ℂ f z₀) = A := by rfl
  have hcurv' (a b c d : Fin n) :
      chartCurvature (ω₀.metricInChart y) z₀ a b c d =
        ∑ e, ∑ f, ∑ g, ∑ h,
          A e a * star (A f b) * A g c * star (A h d) * C e f g h := by
    have hc := hcurv a b c d
    rw [hcenter] at hc
    simpa only [A, C, f, z₀, hA] using hc
  have hframe :
      (∑ a, ∑ b, ∑ c, ∑ d,
        P a p * star (P b q) * P c j * star (P d k) *
          chartCurvature (fun z ↦ ω₀.metricInChart y z) z₀ a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d,
        P a p * star (P b q) * P c j * star (P d k) *
          (∑ e, ∑ f, ∑ g, ∑ h,
            A e a * star (A f b) * A g c * star (A h d) * C e f g h) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    rw [hcurv' a b c d]
  dsimp only [referenceCurvatureComponent]
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ d,
        P a p * star (P b q) * P c j * star (P d k) *
          (∑ e, ∑ f, ∑ g, ∑ h,
            A e a * star (A f b) * A g c * star (A h d) * C e f g h) := hframe
    _ = ∑ e, ∑ f, ∑ g, ∑ h,
        (A * P) e p * star ((A * P) f q) * (A * P) g j *
          star ((A * P) h k) * C e f g h :=
      referenceCurvatureContractMatrix A P C p q j k
    _ = _ := by
      simp [A, C, Matrix.mul_apply, star_sum, star_mul]

end KahlerForm
