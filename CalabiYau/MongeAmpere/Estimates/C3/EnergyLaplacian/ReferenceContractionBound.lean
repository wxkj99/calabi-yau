module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
public import CalabiYau.Geometry.Kahler.Curvature.ReferenceBound
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Frame
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.Energy
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.PairingBound
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.LinearCovariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.ActionCovariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.DriftCovariance
public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ReferenceContractionBound.MixedPairing

/-!
# Reference-curvature contraction in Calabi's Bochner formula

Székelyhidi, §3.3, proof of Lemma 3.9, printed p. 45, the two reference
terms following (3.15). The fixed derivative and connection-action pieces
are of degrees one and two in `T`, respectively. Both reference tensor
bounds follow from the corresponding curvature estimates.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

open scoped ComplexOrder MatrixOrder

omit [T2Space M] [CompactSpace M] in
private theorem referenceContraction_calabiEnergy_frame_weighted_sum
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hPQ : P * Q = 1)
    (hdiag : P.transpose *
      c3PerturbedMetricInChart ω₀ φ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star =
          Matrix.diagonal (fun i ↦ (d i : ℂ)))
    (hd : ∀ i, 0 < d i) :
    calabiEnergyInChart ω₀ φ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k)) *
          ‖referenceContractionTensorFrameTransform Q P
            (fun i j k ↦ connectionDifferenceInChart ω₀ φ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) i j k)
            i j k‖ ^ 2 := by
  classical
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let T : Fin n → Fin n → Fin n → ℂ :=
    fun i j k ↦ connectionDifferenceInChart ω₀ φ x z i j k
  change (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦
    c3PerturbedMetricInChart ω₀ φ x z) z T T).re = _
  exact c3_pair_diagonalized_frame_energy
    (c3PerturbedMetricInChart ω₀ φ x z) z P Q d hd hPQ
    (by simpa [z, c3PullbackMetric] using hdiag) T

omit [T2Space M] [CompactSpace M] in
/-- The exact already-proved reference frame bounds suffice to control the
reference contraction for every comparable positive potential. No forcing equation is needed. -/
theorem exists_uniform_c3BochnerReference_bound (ω₀ : KahlerForm n M)
    (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ω₀.IsPotential p.2)
    (hMetric : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ S, ∀ x,
      relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ B ∧
      relTrace (ω₀ x + mddbar n p.2 x) (ω₀ x) ≤ B)
    (K : ℝ) (hK : 0 ≤ K)
    (hCurv : ∀ (x : M) (P : Matrix (Fin n) (Fin n) ℂ),
      IsReferenceOrthonormalFrame ω₀ x P → ∀ p q j k,
      ‖referenceCurvatureComponent ω₀ x P p q j k‖ ≤ K)
    (A : ℝ) (hA : 0 ≤ A)
    (hDeriv : ∀ (x : M) (P : Matrix (Fin n) (Fin n) ℂ),
      Matrix.transpose P *
          ω₀.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) *
          P.map star = 1 → ∀ s p q j k : Fin n,
        ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ d : Fin n, ∑ e : Fin n,
          P a s * P b p * star (P c q) * P d j * star (P e k) *
            c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c d e‖ ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ x,
      |c3BochnerReferenceTerm ω₀ p.2 x| ≤
        C * (calabiEnergy ω₀ p.2 x + Real.sqrt (calabiEnergy ω₀ p.2 x)) := by
  classical
  obtain ⟨B₀, hB₀, htr⟩ := hMetric
  let B := max B₀ 1
  have hB : 1 ≤ B := le_max_right _ _
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let C := (n : ℝ) ^ 4 * B ^ 6 * A + 3 * (n : ℝ) ^ 5 * B ^ 8 * K
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro p hp x
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let G₀ := ω₀.metricInChart x z
  let G := c3PerturbedMetricInChart ω₀ p.2 x z
  let T := connectionDifferenceInChart ω₀ p.2 x z
  let X := c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x z
  let R := chartCurvature (ω₀.metricInChart x) z
  let E := calabiEnergy ω₀ p.2 x
  obtain ⟨P, d, hf, hdiag, hd, hupper, hlower⟩ :=
    exists_trace_controlled_reference_frame ω₀ p.2 (hS p hp) x B
      ((htr p hp x).1.trans (le_max_left _ _))
      ((htr p hp x).2.trans (le_max_left _ _))
  have hdb := referenceContraction_eigenvalue_bounds d B hBpos hd hupper hlower
  have hunit : IsUnit P.det := by
    have hdet := congrArg Matrix.det hf
    have hdet' : P.det * G₀.det * (P.map star).det = 1 := by
      simpa [IsReferenceOrthonormalFrame, G₀, z, Matrix.det_mul,
        Matrix.det_transpose] using hdet
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    simp [hzero] at hdet'
  let Q := P⁻¹
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv P hunit
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul P hunit
  have hf' : linearPullbackMetric P G₀ = 1 := hf
  have hd' : linearPullbackMetric P G = Matrix.diagonal (fun i ↦ (d i : ℂ)) := by
    simpa [linearPullbackMetric, G, c3PerturbedMetricInChart, z, Function.comp_def] using hdiag
  have henergy : ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (d i / (d j * d k)) * ‖referenceContractionTensorFrameTransform Q P T i j k‖ ^ 2 = E := by
    have hh := referenceContraction_calabiEnergy_frame_weighted_sum
      ω₀ p.2 x P Q d hPQ hd' hd
    exact hh.symm
  have hE : 0 ≤ E := by
    rw [← henergy]
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (div_nonneg (le_of_lt (hd i))
      (mul_nonneg (le_of_lt (hd j)) (le_of_lt (hd k)))) (sq_nonneg _)
  have hX : ∀ s a b c e,
      ‖referenceContractionFiveSlotTransform P X s a b c e‖ ≤ A := by
    intro s a b c e
    exact hDeriv x P hf s a b c e
  have hR : ∀ a b c e, ‖referenceContractionFourSlotTransform P R a b c e‖ ≤ K := by
    intro a b c e
    exact hCurv x P hf a b c e
  have hsplit : c3ReferenceTensorDrift ω₀ p.2 x z =
      (fun i j k => linearReferenceDrift G₀ G X i j k +
        referenceAction_contract G⁻¹ T (fun a b c e => ∑ l, G₀⁻¹ l a * R b e c l) i j k) := by
    funext i j k
    simp only [c3ReferenceTensorDrift, linearReferenceDrift, referenceAction_contract,
      c3RaisedReferenceCurvature, G₀, G, T, X, R]
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp only [Finset.sum_add_distrib]
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  have hdrift := referenceContraction_drift_frame P Q G₀ G X R T d hd hPQ hQP hf' hd'
  rw [← hsplit] at hdrift
  have hpair := referenceContraction_mixed_weighted_pair G z P Q d hd hPQ hd'
    (c3ReferenceTensorDrift ω₀ p.2 x z) T
  have hpair' : c3BochnerReferenceTerm ω₀ p.2 x =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ((d i / (d j * d k) : ℝ) : ℂ) *
          referenceContractionDiagonalDrift d
            (referenceContractionFiveSlotTransform P X)
            (referenceContractionFourSlotTransform P R)
            (referenceContractionTensorFrameTransform Q P T) i j k *
          star (referenceContractionTensorFrameTransform Q P T i j k)).re := by
    change (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ G) z
      (c3ReferenceTensorDrift ω₀ p.2 x z) T).re = _
    rw [hpair, hdrift]
  rw [hpair']
  have hbound := referenceContraction_diagonal_pairing_weighted_bound d
    (referenceContractionFiveSlotTransform P X)
    (referenceContractionFourSlotTransform P R)
    (referenceContractionTensorFrameTransform Q P T) B A K E hB hE hA hK hd hdb
    (le_of_eq henergy) (fun a b c e => hX a b a c e) hR
  exact hbound.trans (referenceContraction_le_const_mul_add_sqrt
    (n := n) B A K E hB hA hK hE).2

end KahlerForm
