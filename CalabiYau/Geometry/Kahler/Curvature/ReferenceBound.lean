module

public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.FixedChartBound
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound.CurvatureTransition

/-!
# Uniform absolute curvature components in orthonormal frames

For a fixed compact Kähler metric, curvature is a continuous tensor.  Its components in a
coordinate basis need not be uniformly bounded under arbitrary coordinate rescalings; the
coordinate frame must first be normalized by the metric.  This module records the compactness
bound in the invariant form used by the Chern–Lu argument: every component of the curvature tensor
in every metric-orthonormal complex frame has a uniform absolute bound.

The frame matrix `P` is column-oriented and satisfies
`P.transpose * G * P.map star = 1`, matching the coefficient pullback convention in `Chart`.  The
tensor component is the fourfold contraction of `chartCurvature` with `P`, its conjugate in the
antiholomorphic slots, and the remaining two holomorphic frame vectors.  Its complex norm bounds
the absolute value of each real bisectional component; the Chern–Lu lower bound follows from the
diagonal case after pulling a Yau normal frame back to the reference chart.

Compactness of the unitary frame bundle over compact `M` gives a finite bound.  The bound
quantifies over all orthonormal frames, not just one local frame, and makes no curvature-sign
assumption.  In `n = 0` the component-index conditions are empty; for a flat metric all curvature
components vanish; for `n = 1` the diagonal component is the holomorphic sectional curvature.  A
linear coordinate test `P = i` in dimension one preserves the unit metric because
`i * 1 * star(i) = 1`.
-/

@[expose] public section

open scoped Manifold ContDiff ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

variable [CompactSpace M]

/-- Absolute values of all holomorphic curvature components in all reference-metric orthonormal
frames are uniformly bounded on a compact Kähler manifold. -/
theorem exists_uniform_reference_curvature_component_bound (ω₀ : KahlerForm n M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (x : M) (P : Matrix (Fin n) (Fin n) ℂ),
      referenceOrthonormalFrameMatrix ω₀ x P → ∀ p q j k,
      ‖referenceCurvatureComponent ω₀ x P p q j k‖ ≤ B := by
  have hCompactUpperBound (K : Set (Matrix (Fin n) (Fin n) ℂ))
      (hK : IsCompact K) (f : Matrix (Fin n) (Fin n) ℂ → ℝ)
      (hf : ContinuousOn f K) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, f x ≤ C := by
    have hbdd : BddAbove (f '' K) := hK.bddAbove_image hf
    obtain ⟨C, hC⟩ := hbdd
    refine ⟨max 0 C, le_max_left _ _, ?_⟩
    intro x hx
    exact (hC (Set.mem_image_of_mem f hx)).trans (le_max_right _ _)
  have hComponentContinuous (x : M) (p q j k : Fin n) :
      Continuous (fun P : Matrix (Fin n) (Fin n) ℂ =>
        referenceCurvatureComponent ω₀ x P p q j k) := by
    fun_prop [referenceCurvatureComponent]
  have hComponentNorm (x : M) (P : Matrix (Fin n) (Fin n) ℂ) (p q j k : Fin n) :
      ‖referenceCurvatureComponent ω₀ x P p q j k‖ ≤
        ∑ a, ∑ b, ∑ c, ∑ d,
          ‖P a p‖ * ‖P b q‖ * ‖P c j‖ * ‖P d k‖ *
            ‖chartCurvature (fun z ↦ ω₀.metricInChart x z)
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d‖ := by
    unfold referenceCurvatureComponent
    calc
      ‖∑ a, ∑ b, ∑ c, ∑ d,
          P a p * star (P b q) * P c j * star (P d k) *
            chartCurvature (fun z ↦ ω₀.metricInChart x z)
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d‖
          ≤ ∑ a, ∑ b, ∑ c, ∑ d,
            ‖P a p * star (P b q) * P c j * star (P d k) *
              chartCurvature (fun z ↦ ω₀.metricInChart x z)
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d‖ := by
              calc
                ‖∑ a, ∑ b, ∑ c, ∑ d, _‖ ≤
                    ∑ a, ‖∑ b, ∑ c, ∑ d, _‖ :=
                  norm_sum_le Finset.univ (fun a : Fin n ↦ ∑ b, ∑ c, ∑ d, _)
                _ ≤ ∑ a, ∑ b, ‖∑ c, ∑ d, _‖ := by
                  apply Finset.sum_le_sum
                  intro a ha
                  exact norm_sum_le Finset.univ (fun b : Fin n ↦ ∑ c, ∑ d, _)
                _ ≤ ∑ a, ∑ b, ∑ c, ‖∑ d, _‖ := by
                  apply Finset.sum_le_sum
                  intro a ha
                  apply Finset.sum_le_sum
                  intro b hb
                  exact norm_sum_le Finset.univ (fun c : Fin n ↦ ∑ d, _)
                _ ≤ ∑ a, ∑ b, ∑ c, ∑ d, ‖_‖ := by
                  apply Finset.sum_le_sum
                  intro a ha
                  apply Finset.sum_le_sum
                  intro b hb
                  apply Finset.sum_le_sum
                  intro c hc
                  exact norm_sum_le Finset.univ (fun d : Fin n ↦ _)
      _ = ∑ a, ∑ b, ∑ c, ∑ d,
            ‖P a p‖ * ‖P b q‖ * ‖P c j‖ * ‖P d k‖ *
              ‖chartCurvature (fun z ↦ ω₀.metricInChart x z)
                (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d‖ := by
          simp_rw [norm_mul, norm_star]
  have hInverse (A P : Matrix (Fin n) (Fin n) ℂ)
      (h : Matrix.transpose P * A * P.map star = 1) :
      A⁻¹ = P.map star * Matrix.transpose P := by
    have h' : (P.transpose * A) * P.map star = 1 := by
      simpa [Matrix.mul_assoc] using h
    have hleft : P.map star * (P.transpose * A) = 1 := mul_eq_one_comm.1 h'
    have hleft' : (P.map star * P.transpose) * A = 1 := by
      simpa [Matrix.mul_assoc] using hleft
    exact Matrix.inv_eq_left_inv hleft'
  have hEntry (A P : Matrix (Fin n) (Fin n) ℂ)
      (h : Matrix.transpose P * A * P.map star = 1) (i j : Fin n) :
      ‖P i j‖ ≤ ‖A⁻¹ i i‖ + 1 := by
    have hInv := hInverse A P h
    have hdiag : ∑ a, Complex.normSq (P i a) = (A⁻¹ i i).re := by
      have hmat := congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X i i) hInv
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply] at hmat
      have hre := congrArg Complex.re hmat
      rw [Complex.re_sum] at hre
      have hterm (z : ℂ) : (star z * z).re = Complex.normSq z := by
        have hh := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := z))
        simpa using hh.symm
      simp_rw [hterm] at hre
      exact hre.symm
    have hsum : Complex.normSq (P i j) ≤ ∑ a, Complex.normSq (P i a) :=
      Finset.single_le_sum (fun a ha => Complex.normSq_nonneg _) (Finset.mem_univ j)
    have hdiagBound : (A⁻¹ i i).re ≤ ‖A⁻¹ i i‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    have hsq : ‖P i j‖ ^ 2 ≤ ‖A⁻¹ i i‖ := by
      rw [← Complex.normSq_eq_norm_sq]
      exact (hsum.trans_eq hdiag).trans hdiagBound
    have hnonneg : 0 ≤ ‖P i j‖ := norm_nonneg _
    nlinarith
  have hFrameCompact (A : Matrix (Fin n) (Fin n) ℂ) :
      IsCompact {P : Matrix (Fin n) (Fin n) ℂ | P.transpose * A * P.map star = 1} := by
    let S : Set (Matrix (Fin n) (Fin n) ℂ) := {P | P.transpose * A * P.map star = 1}
    let K : Set (Matrix (Fin n) (Fin n) ℂ) :=
      {P | ∀ i j, P i j ∈ Metric.closedBall (0 : ℂ) (‖A⁻¹ i i‖ + 1)}
    have hK : IsCompact K := by
      change IsCompact {P : Fin n → Fin n → ℂ | ∀ i, P i ∈
        {row : Fin n → ℂ | ∀ j, row j ∈ Metric.closedBall (0 : ℂ) (‖A⁻¹ i i‖ + 1)}}
      apply isCompact_pi_infinite
      intro i
      apply isCompact_pi_infinite
      intro j
      exact isCompact_closedBall _ _
    have hsubset : S ⊆ K := by
      intro P hP
      change ∀ i j, P i j ∈ Metric.closedBall (0 : ℂ) (‖A⁻¹ i i‖ + 1)
      intro i j
      simpa [Metric.mem_closedBall, dist_eq_norm] using hEntry A P hP i j
    have hcont : Continuous (fun P : Matrix (Fin n) (Fin n) ℂ => P.transpose * A * P.map star) := by
      fun_prop
    have hclosed : IsClosed S := by
      change IsClosed ((fun P : Matrix (Fin n) (Fin n) ℂ => P.transpose * A * P.map star) ⁻¹' {1})
      exact isClosed_singleton.preimage hcont
    exact hK.of_isClosed_subset hclosed hsubset
  have hFiberCompact (x : M) :
      IsCompact {P : Matrix (Fin n) (Fin n) ℂ | referenceOrthonormalFrameMatrix ω₀ x P} := by
    simpa [referenceOrthonormalFrameMatrix] using
      hFrameCompact (ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
  have hFiberBound (x : M) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (P : Matrix (Fin n) (Fin n) ℂ),
        referenceOrthonormalFrameMatrix ω₀ x P → ∀ p q j k,
          ‖referenceCurvatureComponent ω₀ x P p q j k‖ ≤ B := by
    classical
    let S : Set (Matrix (Fin n) (Fin n) ℂ) :=
      {P | referenceOrthonormalFrameMatrix ω₀ x P}
    have hcompact : IsCompact S := hFiberCompact x
    have hcomponentBound (p q j k : Fin n) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ P, P ∈ S →
          ‖referenceCurvatureComponent ω₀ x P p q j k‖ ≤ C := by
      let f : Matrix (Fin n) (Fin n) ℂ → ℝ := fun P ↦
        ‖referenceCurvatureComponent ω₀ x P p q j k‖
      have hf : ContinuousOn f S := by
        exact (continuous_norm.comp (hComponentContinuous x p q j k)).continuousOn
      obtain ⟨C, hCnonneg, hC⟩ := hCompactUpperBound S hcompact f hf
      exact ⟨C, hCnonneg, hC⟩
    let ι := Fin n × (Fin n × (Fin n × Fin n))
    let C : ι → ℝ := fun t => Classical.choose
      (hcomponentBound t.1 t.2.1 t.2.2.1 t.2.2.2)
    have hCnonneg (t : ι) : 0 ≤ C t :=
      (Classical.choose_spec (hcomponentBound t.1 t.2.1 t.2.2.1 t.2.2.2)).1
    have hCbound (t : ι) (P : Matrix (Fin n) (Fin n) ℂ) (hP : P ∈ S) :
        ‖referenceCurvatureComponent ω₀ x P t.1 t.2.1 t.2.2.1 t.2.2.2‖ ≤ C t :=
      (Classical.choose_spec (hcomponentBound t.1 t.2.1 t.2.2.1 t.2.2.2)).2 P hP
    let B : ℝ := ∑ t, C t
    refine ⟨B, ?_, ?_⟩
    · exact Finset.sum_nonneg (fun t ht => hCnonneg t)
    · intro P hP p q j k
      let t : ι := ⟨p, ⟨q, ⟨j, k⟩⟩⟩
      have hsingle : C t ≤ ∑ t, C t :=
        Finset.single_le_sum (fun t ht => hCnonneg t) (Finset.mem_univ t)
      exact (hCbound t P hP).trans (by simpa [B] using hsingle)
  have hLocalToGlobal (f : M → ℝ)
      (hlocal : ∀ x, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, f y ≤ C) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x, f x ≤ B := by
    classical
    choose U hUopen hx hbound using hlocal
    choose C hCnonneg hCbound using hbound
    have hcover : (Set.univ : Set M) ⊆ ⋃ x : M, U x := by
      intro x hxuniv
      exact Set.mem_iUnion.mpr ⟨x, hx x⟩
    obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
      U hUopen hcover
    let B : ℝ := ∑ x ∈ t, C x
    refine ⟨B, ?_, ?_⟩
    · exact Finset.sum_nonneg fun x hx ↦ hCnonneg x
    · intro x
      rcases Set.mem_iUnion₂.mp (ht (Set.mem_univ x)) with ⟨y, hyt, hxy⟩
      have hsingle : C y ≤ ∑ z ∈ t, C z :=
        Finset.single_le_sum (fun z hz ↦ hCnonneg z) hyt
      exact (hCbound y x hxy).trans (by simpa [B] using hsingle)
  have hLocalBound : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ (P : Matrix (Fin n) (Fin n) ℂ),
        referenceOrthonormalFrameMatrix ω₀ y P → ∀ p q j k,
          ‖referenceCurvatureComponent ω₀ y P p q j k‖ ≤ C := by
    intro x
    obtain ⟨U, hUopen, hx, hUsource, C, hCnonneg, hC⟩ :=
      ω₀.exists_local_fixed_chart_frame_curvature_bound x
    refine ⟨U, hUopen, hx, C, hCnonneg, ?_⟩
    intro y hy P hP p q j k
    have hyx := hUsource hy
    obtain ⟨V, hV⟩ := ω₀.exists_reference_chart_overlap x y hyx
    have hQ := ω₀.referenceFrame_transition x y V hV P hP
    rw [ω₀.referenceCurvatureComponent_transition x y V hV P p q j k]
    exact hC y hy (referenceTransitionMatrix x y * P) hQ p q j k
  classical
  choose U hUopen hx hbound using hLocalBound
  choose C hCnonneg hCbound using hbound
  have hcover : (Set.univ : Set M) ⊆ ⋃ x : M, U x := by
    intro x hxuniv
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
    U hUopen hcover
  let B : ℝ := ∑ x ∈ t, C x
  refine ⟨B, ?_, ?_⟩
  · exact Finset.sum_nonneg fun x hx ↦ hCnonneg x
  · intro x P hP p q j k
    rcases Set.mem_iUnion₂.mp (ht (Set.mem_univ x)) with ⟨y, hyt, hxy⟩
    have hsingle : C y ≤ ∑ z ∈ t, C z :=
      Finset.single_le_sum (fun z hz ↦ hCnonneg z) hyt
    exact (hCbound y x hxy P hP p q j k).trans (by simpa [B] using hsingle)

end KahlerForm
