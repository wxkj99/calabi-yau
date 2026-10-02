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

private theorem referenceContraction_tensorFrameTransform_diagonal_rescale {n : ℕ}
    (P B : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (T : Fin n → Fin n → Fin n → ℂ) (i j k : Fin n) :
    referenceContraction_tensorFrameTransform
        (Matrix.diagonal (fun r => (Real.sqrt (d r) : ℂ)) * B)
        (P * Matrix.diagonal (fun r => ((Real.sqrt (d r))⁻¹ : ℂ))) T i j k =
      (Real.sqrt (d i) : ℂ) * (Real.sqrt (d j))⁻¹ * (Real.sqrt (d k))⁻¹ *
        referenceContraction_tensorFrameTransform B P T i j k := by
  classical
  have hdiagB (r a : Fin n) :
      (Matrix.diagonal (fun q => (Real.sqrt (d q) : ℂ)) * B) r a =
        (Real.sqrt (d r) : ℂ) * B r a := by
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  have hdiagP (b l : Fin n) :
      (P * Matrix.diagonal (fun q => ((Real.sqrt (d q))⁻¹ : ℂ))) b l =
        P b l * (Real.sqrt (d l))⁻¹ := by
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  unfold referenceContraction_tensorFrameTransform
  simp_rw [hdiagB, hdiagP]
  calc
    (∑ a, ∑ b, ∑ c,
      ((Real.sqrt (d i) : ℂ) * B i a) *
        (P b j * (Real.sqrt (d j))⁻¹) *
        (P c k * (Real.sqrt (d k))⁻¹) * T a b c) =
      (Real.sqrt (d i) : ℂ) * (Real.sqrt (d j))⁻¹ * (Real.sqrt (d k))⁻¹ *
        (∑ a, ∑ b, ∑ c, B i a * P b j * P c k * T a b c) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      ring

private theorem referenceContraction_fourSlot_diagonal_rescale {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) (p q j k : Fin n) :
    referenceContraction_fourSlotTransform (P * Matrix.diagonal a) R p q j k =
      a p * star (a q) * a j * star (a k) *
        referenceContraction_fourSlotTransform P R p q j k := by
  classical
  have hentry (i l : Fin n) :
      (P * Matrix.diagonal a) i l = P i l * a l := by
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  unfold referenceContraction_fourSlotTransform
  simp_rw [hentry, star_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  ring

private theorem referenceContraction_fiveSlot_diagonal_rescale {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ)
    (X : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ)
    (s p q j k : Fin n) :
    referenceContraction_fiveSlotTransform (P * Matrix.diagonal a) X s p q j k =
      a s * a p * star (a q) * a j * star (a k) *
        referenceContraction_fiveSlotTransform P X s p q j k := by
  classical
  have hentry (i l : Fin n) :
      (P * Matrix.diagonal a) i l = P i l * a l := by
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  unfold referenceContraction_fiveSlotTransform
  simp_rw [hentry, star_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  ring

private noncomputable def referenceContraction_rescaleFactor {n : ℕ}
    (d : Fin n → ℝ) : Fin n → ℂ := fun i => ((Real.sqrt (d i))⁻¹ : ℝ)

private theorem referenceContraction_rescaleFactor_norm_bound {n : ℕ}
    (d : Fin n → ℝ) (B : ℝ) (hB : 0 < B) (hd : ∀ i, 0 < d i)
    (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B) (i : Fin n) :
    ‖referenceContraction_rescaleFactor d i‖ ≤ Real.sqrt B := by
  have hinv : (d i)⁻¹ ≤ B := by
    have hmul : 1 ≤ B * d i := by
      calc
        1 = B * B⁻¹ := by field_simp [hB.ne']
        _ ≤ B * d i := mul_le_mul_of_nonneg_left (hdb i).1 (le_of_lt hB)
    simpa [one_div] using (div_le_iff₀ (hd i)).2 hmul
  have hroot := Real.sqrt_le_sqrt hinv
  rw [Real.sqrt_inv] at hroot
  have hnorm : ‖referenceContraction_rescaleFactor d i‖ = (Real.sqrt (d i))⁻¹ := by
    simp [referenceContraction_rescaleFactor]
  rw [hnorm]
  exact hroot

private theorem referenceContraction_fourFactor_norm_bound {n : ℕ}
    (d : Fin n → ℝ) (B : ℝ) (i j k l : Fin n) (hB : 0 < B)
    (hd : ∀ i, 0 < d i) (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B) :
    ‖referenceContraction_rescaleFactor d i *
        star (referenceContraction_rescaleFactor d j) *
        referenceContraction_rescaleFactor d k *
        star (referenceContraction_rescaleFactor d l)‖ ≤ B ^ 2 := by
  have hi := referenceContraction_rescaleFactor_norm_bound d B hB hd hdb i
  have hj := referenceContraction_rescaleFactor_norm_bound d B hB hd hdb j
  have hk := referenceContraction_rescaleFactor_norm_bound d B hB hd hdb k
  have hl := referenceContraction_rescaleFactor_norm_bound d B hB hd hdb l
  have hnorm : ‖referenceContraction_rescaleFactor d i *
      star (referenceContraction_rescaleFactor d j) *
      referenceContraction_rescaleFactor d k *
      star (referenceContraction_rescaleFactor d l)‖ =
      ‖referenceContraction_rescaleFactor d i‖ *
        ‖referenceContraction_rescaleFactor d j‖ *
        ‖referenceContraction_rescaleFactor d k‖ *
        ‖referenceContraction_rescaleFactor d l‖ := by simp [mul_assoc]
  rw [hnorm]
  calc
    ‖referenceContraction_rescaleFactor d i‖ *
        ‖referenceContraction_rescaleFactor d j‖ *
        ‖referenceContraction_rescaleFactor d k‖ *
        ‖referenceContraction_rescaleFactor d l‖ ≤
      Real.sqrt B * Real.sqrt B * Real.sqrt B * Real.sqrt B := by gcongr
    _ = B ^ 2 := by
      have hroot : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
      rw [← Real.sq_sqrt (le_of_lt hB)]
      simp [Real.sqrt_sq hroot]
      ring

private theorem referenceContraction_fiveFactor_norm_bound {n : ℕ}
    (d : Fin n → ℝ) (B : ℝ) (s p q j k : Fin n) (hB : 0 < B)
    (hd : ∀ i, 0 < d i) (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B) :
    ‖referenceContraction_rescaleFactor d s *
        referenceContraction_rescaleFactor d p *
        star (referenceContraction_rescaleFactor d q) *
        referenceContraction_rescaleFactor d j *
        star (referenceContraction_rescaleFactor d k)‖ ≤ B ^ 2 * Real.sqrt B := by
  have hfour := referenceContraction_fourFactor_norm_bound d B s q p j hB hd hdb
  have hfour' : ‖referenceContraction_rescaleFactor d s *
      referenceContraction_rescaleFactor d p *
      star (referenceContraction_rescaleFactor d q) *
      referenceContraction_rescaleFactor d j‖ ≤ B ^ 2 := by
    simpa [referenceContraction_rescaleFactor, mul_comm, mul_left_comm, mul_assoc] using hfour
  have hk := referenceContraction_rescaleFactor_norm_bound d B hB hd hdb k
  have hnorm : ‖referenceContraction_rescaleFactor d s *
      referenceContraction_rescaleFactor d p *
      star (referenceContraction_rescaleFactor d q) *
      referenceContraction_rescaleFactor d j *
      star (referenceContraction_rescaleFactor d k)‖ =
      ‖referenceContraction_rescaleFactor d s *
        referenceContraction_rescaleFactor d p *
        star (referenceContraction_rescaleFactor d q) *
        referenceContraction_rescaleFactor d j‖ *
        ‖referenceContraction_rescaleFactor d k‖ := by simp [mul_assoc]
  rw [hnorm]
  exact mul_le_mul hfour' hk (norm_nonneg _) (by positivity)

private theorem referenceContraction_fourSlot_component_bound {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ) (B K : ℝ)
    (hB : 1 ≤ B) (hd : ∀ i, 0 < d i)
    (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (hR : ∀ p q j k, ‖referenceContraction_fourSlotTransform P R p q j k‖ ≤ K)
    (p q j k : Fin n) :
    ‖referenceContraction_fourSlotTransform
      (P * Matrix.diagonal (referenceContraction_rescaleFactor d)) R p q j k‖ ≤ B ^ 2 * K := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  rw [referenceContraction_fourSlot_diagonal_rescale]
  have hscale := referenceContraction_fourFactor_norm_bound d B p q j k hBpos hd hdb
  have hbase := hR p q j k
  rw [norm_mul]
  exact mul_le_mul hscale hbase (norm_nonneg _) (by positivity)

private theorem referenceContraction_fiveSlot_component_bound {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (X : Fin n → Fin n → Fin n → Fin n → Fin n → ℂ) (B A : ℝ)
    (hB : 1 ≤ B) (hd : ∀ i, 0 < d i)
    (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (hX : ∀ s p q j k,
      ‖referenceContraction_fiveSlotTransform P X s p q j k‖ ≤ A)
    (s p q j k : Fin n) :
    ‖referenceContraction_fiveSlotTransform
      (P * Matrix.diagonal (referenceContraction_rescaleFactor d)) X s p q j k‖ ≤
      B ^ 2 * Real.sqrt B * A := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  rw [referenceContraction_fiveSlot_diagonal_rescale]
  have hscale := referenceContraction_fiveFactor_norm_bound d B s p q j k hBpos hd hdb
  have hbase := hX s p q j k
  rw [norm_mul]
  exact mul_le_mul hscale hbase (norm_nonneg _) (by positivity)

omit [T2Space M] [CompactSpace M] in
private theorem referenceContraction_referenceCurvature_rescaled_bound
    (ω₀ : KahlerForm n M) (x : M) (P : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℝ) (B K : ℝ) (hB : 1 ≤ B)
    (hd : ∀ i, 0 < d i) (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (hCurv : referenceOrthonormalFrameMatrix ω₀ x P →
      ∀ p q j k, ‖referenceCurvatureComponent ω₀ x P p q j k‖ ≤ K)
    (hframe : referenceOrthonormalFrameMatrix ω₀ x P) :
    ∀ p q j k,
      ‖referenceCurvatureComponent ω₀ x
        (P * Matrix.diagonal (referenceContraction_rescaleFactor d)) p q j k‖ ≤ B ^ 2 * K := by
  intro p q j k
  apply referenceContraction_fourSlot_component_bound P d
    (fun a b c e => chartCurvature (ω₀.metricInChart x)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c e)
    B K hB hd hdb (fun a b c e => ?_) p q j k
  change ‖referenceCurvatureComponent ω₀ x P a b c e‖ ≤ K
  exact hCurv hframe a b c e

omit [T2Space M] [CompactSpace M] in
private theorem referenceContraction_referenceDerivative_rescaled_bound
    (ω₀ : KahlerForm n M) (x : M) (P : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℝ) (B A : ℝ) (hB : 1 ≤ B)
    (hd : ∀ i, 0 < d i) (hdb : ∀ i, B⁻¹ ≤ d i ∧ d i ≤ B)
    (hframe : referenceOrthonormalFrameMatrix ω₀ x P)
    (hDeriv : referenceOrthonormalFrameMatrix ω₀ x P → ∀ s p q j k,
      ‖∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, ∑ e : Fin n, ∑ f : Fin n,
        P a s * P b p * star (P c q) * P e j * star (P f k) *
          c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c e f‖ ≤ A) :
    ∀ s p q j k,
      ‖referenceContraction_fiveSlotTransform
        (P * Matrix.diagonal (referenceContraction_rescaleFactor d))
        (fun a b c e f => c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c e f)
        s p q j k‖ ≤ B ^ 2 * Real.sqrt B * A := by
  intro s p q j k
  apply referenceContraction_fiveSlot_component_bound P d
    (fun a b c e f => c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) a b c e f)
    B A hB hd hdb (fun s p q j k => ?_) s p q j k
  exact hDeriv hframe s p q j k

omit [T2Space M] [CompactSpace M] in
private theorem referenceContraction_drift_split (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M) (z : EuclideanSpace ℂ (Fin n)) (i j k : Fin n) :
    c3ReferenceTensorDrift ω₀ φ x z i j k =
      (∑ p, ∑ q, (ω₀.metricInChart x z + complexHessian
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ q p *
          ∑ l, (ω₀.metricInChart x z)⁻¹ l i *
            c3ReferenceCurvatureCovariantDerivativeInChart ω₀ x z p j q k l) +
      (∑ p, ∑ q, (ω₀.metricInChart x z + complexHessian
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ q p *
          ((∑ r, c3ConnectionDifferenceInChart ω₀ φ x z i p r *
              c3RaisedReferenceCurvature ω₀ x z r j k q) -
            (∑ r, c3ConnectionDifferenceInChart ω₀ φ x z r p j *
              c3RaisedReferenceCurvature ω₀ x z i r k q) -
            (∑ r, c3ConnectionDifferenceInChart ω₀ φ x z r p k *
              c3RaisedReferenceCurvature ω₀ x z i j r q))) := by
  classical
  simp only [c3ReferenceTensorDrift, c3PerturbedMetricInChart,
    c3RaisedReferenceCurvature]
  rw [← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_add_distrib]
  ring_nf

omit [T2Space M] [CompactSpace M] in
private theorem referenceContraction_calabiEnergy_frame_weighted_sum
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (P Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hdiag : P.transpose *
      c3PerturbedMetricInChart ω₀ φ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) * P.map star =
          Matrix.diagonal (fun i ↦ (d i : ℂ)))
    (hd : ∀ i, 0 < d i) :
    calabiEnergyInChart ω₀ φ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (d i / (d j * d k)) *
          ‖referenceContraction_tensorFrameTransform Q P
            (fun i j k ↦ c3ConnectionDifferenceInChart ω₀ φ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) i j k)
            i j k‖ ^ 2 := by
  classical
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  let T : Fin n → Fin n → Fin n → ℂ :=
    fun i j k ↦ c3ConnectionDifferenceInChart ω₀ φ x z i j k
  change (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦
    c3PerturbedMetricInChart ω₀ φ x z) z T T).re = _
  exact c3_pair_diagonalized_frame_energy
    (c3PerturbedMetricInChart ω₀ φ x z) z P Q d hd hPQ hQP
    (by simpa [z, c3PullbackMetric] using hdiag) T

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
      referenceOrthonormalFrameMatrix ω₀ x P → ∀ p q j k,
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
  let T := c3ConnectionDifferenceInChart ω₀ p.2 x z
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
      simpa [referenceOrthonormalFrameMatrix, G₀, z, Matrix.det_mul,
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
      (d i / (d j * d k)) * ‖referenceContraction_tensorFrameTransform Q P T i j k‖ ^ 2 = E := by
    have hh := referenceContraction_calabiEnergy_frame_weighted_sum
      ω₀ p.2 x P Q d hPQ hQP hd' hd
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
      ‖referenceContraction_fiveSlotTransform P X s a b c e‖ ≤ A := by
    intro s a b c e
    exact hDeriv x P hf s a b c e
  have hR : ∀ a b c e, ‖referenceContraction_fourSlotTransform P R a b c e‖ ≤ K := by
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
  have hpair := referenceContraction_mixed_weighted_pair G z P Q d hd hPQ hQP hd'
    (c3ReferenceTensorDrift ω₀ p.2 x z) T
  have hpair' : c3BochnerReferenceTerm ω₀ p.2 x =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ((d i / (d j * d k) : ℝ) : ℂ) *
          referenceContraction_diagonal_drift d
            (referenceContraction_fiveSlotTransform P X)
            (referenceContraction_fourSlotTransform P R)
            (referenceContraction_tensorFrameTransform Q P T) i j k *
          star (referenceContraction_tensorFrameTransform Q P T i j k)).re := by
    change (c3Pair (fun _ : EuclideanSpace ℂ (Fin n) ↦ G) z
      (c3ReferenceTensorDrift ω₀ p.2 x z) T).re = _
    rw [hpair, hdrift]
  rw [hpair']
  have hbound := referenceContraction_diagonal_pairing_weighted_bound d
    (referenceContraction_fiveSlotTransform P X)
    (referenceContraction_fourSlotTransform P R)
    (referenceContraction_tensorFrameTransform Q P T) B A K E hB hE hA hK hd hdb
    (le_of_eq henergy) (fun a b c e => hX a b a c e) hR
  exact hbound.trans (referenceContraction_final_constant_bound
    (n := n) B A K E hB hA hK hE).2

end KahlerForm
