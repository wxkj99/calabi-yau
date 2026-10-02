module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.NormalCoordinateFrame
import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.ChartInvariance.Transition

/-!
# Connection-difference energy under a holomorphic coordinate change

The difference of two Kähler connections is a three-index tensor: the
non-tensorial second derivatives of a holomorphic chart change cancel on
subtracting the two Christoffel symbols. Its squared norm is invariant and
reduces to the diagonal three-inverse-eigenvalue sum in a reference-normal
frame. Curvature transport is treated separately.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §3.3,
equation (3.13), p. 45; Yau (1978), §3.
-/

@[expose] public section

open scoped BigOperators Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private abbrev NFPair (ι : Type*) := ι × ι
private abbrev NFTriple (ι : Type*) := ι × ι × ι
private abbrev NFPairTriple (ι : Type*) := NFPair ι × NFPair ι × NFPair ι

private def nfTensorContract {ι : Type*} [Fintype ι]
    (g h : ι → ι → ℂ) (T : ι → ι → ι → ℂ) : ℂ :=
  ∑ x : NFPairTriple ι,
    g x.1.1 x.1.2 * h x.2.1.1 x.2.1.2 * h x.2.2.1 x.2.2.2 *
      T x.1.1 x.2.1.2 x.2.2.2 * star (T x.1.2 x.2.1.1 x.2.2.1)

private def nfTensorChange {ι : Type*} [Fintype ι]
    (A B : ι → ι → ℂ) (T : ι → ι → ι → ℂ) (i j k : ι) : ℂ :=
  ∑ p : NFTriple ι, B i p.1 * A p.2.1 j * A p.2.2 k * T p.1 p.2.1 p.2.2

private abbrev nfPullbackMetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A G : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A.transpose * G * A.map (starRingEnd ℂ)

private abbrev nfPullbackInverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  B.map (starRingEnd ℂ) * H * B.transpose

private theorem nfPullbackPairContractions {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B G H : Matrix ι ι ℂ) (hAB : A * B = 1) :
    (∀ p s, ∑ x : NFPair ι,
      nfPullbackMetric A G x.1 x.2 * B x.1 p * star (B x.2 s) = G p s) ∧
    (∀ q t, ∑ x : NFPair ι,
      nfPullbackInverse B H x.1 x.2 * A q x.2 * star (A t x.1) = H t q) := by
  classical
  constructor
  · intro p s
    have hmat : B.transpose * (nfPullbackMetric A G * B.map (starRingEnd ℂ)) = G := by
      dsimp [nfPullbackMetric]
      calc
        _ = (B.transpose * A.transpose) * G *
            (A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ)) := by
          simp only [Matrix.mul_assoc]
        _ = (A * B).transpose * G * (A * B).map (starRingEnd ℂ) := by
          rw [← Matrix.transpose_mul, ← Matrix.map_mul (f := starRingEnd ℂ)]
        _ = G := by rw [hAB]; simp
    have heq := congrArg (fun M : Matrix ι ι ℂ => M p s) hmat
    calc
      _ = (B.transpose * (nfPullbackMetric A G * B.map (starRingEnd ℂ))) p s := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
          Fintype.sum_prod_type, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro x₁ hx₁
        simp only [starRingEnd_apply]
        ring
      _ = G p s := heq
  · intro q t
    have hmat : A.map (starRingEnd ℂ) *
        (nfPullbackInverse B H * A.transpose) = H := by
      dsimp [nfPullbackInverse]
      calc
        _ = (A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ)) * H *
            (B.transpose * A.transpose) := by
          simp only [Matrix.mul_assoc]
        _ = (A * B).map (starRingEnd ℂ) * H * (A * B).transpose := by
          rw [← Matrix.map_mul (f := starRingEnd ℂ), ← Matrix.transpose_mul]
        _ = H := by rw [hAB]; simp
    have heq := congrArg (fun M : Matrix ι ι ℂ => M t q) hmat
    calc
      _ = (A.map (starRingEnd ℂ) *
          (nfPullbackInverse B H * A.transpose)) t q := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
          Fintype.sum_prod_type, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro x₁ hx₁
        simp only [starRingEnd_apply]
        ring
      _ = H t q := heq

private theorem nfPullbackMetricInverse {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B G : Matrix ι ι ℂ) (hAB : A * B = 1)
    (hBA : B * A = 1) (hG : IsUnit G.det) :
    (nfPullbackMetric A G)⁻¹ = nfPullbackInverse B G⁻¹ := by
  classical
  let G₀ := nfPullbackMetric A G
  let H₀ := nfPullbackInverse B G⁻¹
  have hstar : A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul (f := starRingEnd ℂ), hAB]
    simp
  have hright : G₀ * H₀ = 1 := by
    dsimp [G₀, H₀]
    calc
      _ = A.transpose * G *
          (A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ)) * G⁻¹ * B.transpose := by
        simp only [nfPullbackMetric, nfPullbackInverse, Matrix.mul_assoc]
      _ = A.transpose * G * G⁻¹ * B.transpose := by rw [hstar]; simp
      _ = A.transpose * B.transpose := by
        rw [Matrix.mul_assoc A.transpose G G⁻¹, Matrix.mul_nonsing_inv G hG]
        simp
      _ = (B * A).transpose := by rw [← Matrix.transpose_mul]
      _ = 1 := by rw [hBA]; simp
  have hG₀ : IsUnit G₀.det := by
    apply (Matrix.isUnit_iff_isUnit_det G₀).mp
    exact IsUnit.of_mul_eq_one (b := H₀) hright
  have hcancel := Matrix.nonsing_inv_mul_cancel_left G₀ H₀ hG₀
  rw [hright, Matrix.mul_one] at hcancel
  simpa [G₀, H₀] using hcancel

private theorem nfSumThreeFactor
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → ℂ) (g : β → ℂ) (h : γ → ℂ) :
    (∑ a, ∑ b, ∑ c, f a * g b * h c) =
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) := by
  have hp :
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) =
        ∑ a, ∑ b, ∑ c, f a * g b * h c := by
    calc
      _ = (∑ p : α × β, f p.1 * g p.2) * (∑ c, h c) := by
        rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
      _ = ∑ p : α × β, ∑ c, (f p.1 * g p.2) * h c := by
        rw [Fintype.sum_mul_sum]
      _ = _ := by simp only [Fintype.sum_prod_type]
  exact hp.symm

private theorem nfSumPairTripleFactor {ι : Type*} [Fintype ι]
    (f g h : NFPair ι → ℂ) (d : ℂ) :
    (∑ x : NFPairTriple ι, f x.1 * g x.2.1 * h x.2.2 * d) =
      (∑ x, f x) * (∑ x, g x) * (∑ x, h x) * d := by
  rw [← Finset.sum_mul]
  have hh :
      (∑ x : NFPairTriple ι, f x.1 * g x.2.1 * h x.2.2) =
        (∑ x, f x) * (∑ x, g x) * (∑ x, h x) := by
    simpa only [Fintype.sum_prod_type] using nfSumThreeFactor f g h
  exact congrArg (fun z : ℂ => z * d) hh

private abbrev nfPairTripleEquiv (ι : Type*) :
    NFTriple ι × NFTriple ι ≃ NFPairTriple ι where
  toFun v := ((v.1.1, v.2.1), (v.2.2.1, v.1.2.1), (v.2.2.2, v.1.2.2))
  invFun z := ((z.1.1, (z.2.1.2, z.2.2.2)), (z.1.2, (z.2.1.1, z.2.2.1)))
  left_inv := by rintro ⟨⟨i,j,k⟩,⟨a,b,c⟩⟩; rfl
  right_inv := by rintro ⟨⟨i,a⟩,⟨b,j⟩,⟨c,k⟩⟩; rfl

private theorem nfTensorContractReindex {ι : Type*} [Fintype ι]
    (g h : ι → ι → ℂ) (T : ι → ι → ι → ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
      g i a * h b j * h c k * T i j k * star (T a b c)) =
      nfTensorContract g h T := by
  unfold nfTensorContract
  calc
    _ = ∑ p : NFTriple ι, ∑ q : NFTriple ι,
        g p.1 q.1 * h q.2.1 p.2.1 * h q.2.2 p.2.2 *
          T p.1 p.2.1 p.2.2 * star (T q.1 q.2.1 q.2.2) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ v : NFTriple ι × NFTriple ι,
        g v.1.1 v.2.1 * h v.2.2.1 v.1.2.1 * h v.2.2.2 v.1.2.2 *
          T v.1.1 v.1.2.1 v.1.2.2 * star (T v.2.1 v.2.2.1 v.2.2.2) := by
      rw [← Fintype.sum_prod_type']
    _ = nfTensorContract g h T := by
      exact Fintype.sum_equiv (nfPairTripleEquiv ι) _ _ (by
        rintro ⟨⟨i,j,k⟩,⟨a,b,c⟩⟩
        simp [nfPairTripleEquiv])

private theorem nfTensorContractTensorChange {ι : Type*} [Fintype ι]
    (g₀ h₀ g₁ h₁ A B : ι → ι → ℂ) (T : ι → ι → ι → ℂ)
    (hOut : ∀ p s, ∑ x : NFPair ι,
      g₀ x.1 x.2 * B x.1 p * star (B x.2 s) = g₁ p s)
    (hIn : ∀ q t, ∑ x : NFPair ι,
      h₀ x.1 x.2 * A q x.2 * star (A t x.1) = h₁ t q) :
    nfTensorContract g₀ h₀ (nfTensorChange A B T) = nfTensorContract g₁ h₁ T := by
  unfold nfTensorContract nfTensorChange
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2]; intro y; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  let f₀ : NFTriple ι → NFTriple ι → NFPair ι → ℂ :=
    fun y x z ↦ g₀ z.1 z.2 * B z.1 y.1 * star (B z.2 x.1)
  let f₁ : NFTriple ι → NFTriple ι → NFPair ι → ℂ :=
    fun y x z ↦ h₀ z.1 z.2 * A y.2.1 z.2 * star (A x.2.1 z.1)
  let f₂ : NFTriple ι → NFTriple ι → NFPair ι → ℂ :=
    fun y x z ↦ h₀ z.1 z.2 * A y.2.2 z.2 * star (A x.2.2 z.1)
  have hfac (y x : NFTriple ι) :
      (∑ z : NFPairTriple ι,
        g₀ z.1.1 z.1.2 * h₀ z.2.1.1 z.2.1.2 * h₀ z.2.2.1 z.2.2.2 *
          (B z.1.1 y.1 * A y.2.1 z.2.1.2 * A y.2.2 z.2.2.2 *
            T y.1 y.2.1 y.2.2) *
          (star (T x.1 x.2.1 x.2.2) *
            (star (A x.2.2 z.2.2.1) *
              (star (A x.2.1 z.2.1.1) * star (B z.1.2 x.1))))) =
        (∑ z, f₀ y x z) * (∑ z, f₁ y x z) * (∑ z, f₂ y x z) *
          (T y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2)) := by
    calc
      _ = ∑ z : NFPairTriple ι,
          f₀ y x z.1 * f₁ y x z.2.1 * f₂ y x z.2.2 *
            (T y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2)) := by
        apply Finset.sum_congr rfl
        intro z hz
        simp only [f₀, f₁, f₂]
        ring_nf
      _ = _ := nfSumPairTripleFactor (f₀ y x) (f₁ y x) (f₂ y x)
        (T y.1 y.2.1 y.2.2 * star (T x.1 x.2.1 x.2.2))
  simp_rw [hfac, f₀, f₁, f₂, hOut, hIn]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (nfPairTripleEquiv ι) _ _ (by
    rintro ⟨⟨i,j,k⟩,⟨a,b,c⟩⟩
    simp [nfPairTripleEquiv]
    ring)

/-- Transport the squared connection-difference norm from the point-selected
chart to the *same* holomorphic normal frame used for the trace computation.
The three inverse eigenvalue factors correspond to its differentiation and
two metric indices; none of the factors is missing in dimension one. -/
theorem c3RefinedTrace_normalFrame_connectionEnergy
    (ω₀ : KahlerForm n M) (G φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M)
    (frame : C3RefinedTraceNormalCoordinateFrame ω₀ φ x) :
    let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
    calabiEnergy ω₀ φ x =
      ∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ‖wirtingerDerivInChart (fun w ↦ h w j k) frame.center p‖ ^ (2 : ℕ) /
          (frame.eigenvalue p * frame.eigenvalue j * frame.eigenvalue k) := by
  let g := c3RefinedTracePulledReferenceMetric ω₀ x frame.coord
  let h := c3RefinedTracePulledPerturbedMetric ω₀ φ x frame.coord
  have hInvDiagonal :
      (Matrix.diagonal (fun j ↦ (frame.eigenvalue j : ℂ)))⁻¹ =
        Matrix.diagonal (fun j ↦ ((frame.eigenvalue j)⁻¹ : ℂ)) := by
    have hunit : IsUnit (fun k ↦ (frame.eigenvalue k : ℂ)) := by
      rw [Pi.isUnit_iff]
      intro k
      exact isUnit_iff_ne_zero.mpr
        (by exact_mod_cast ne_of_gt (frame.eigenvalue_pos k))
    have hinv : Ring.inverse (fun k ↦ (frame.eigenvalue k : ℂ)) =
        (fun k ↦ ((frame.eigenvalue k)⁻¹ : ℂ)) := by
      funext j
      rw [Ring.inverse_of_isUnit hunit]
      simp [IsUnit.val_inv_apply hunit j]
    rw [Matrix.inv_diagonal]
    ext i j
    simp [Matrix.diagonal_apply, hinv]
  have hCoefficient : ∀ i j k : Fin n,
      christoffelInChart h frame.center i j k -
          christoffelInChart g frame.center i j k =
        wirtingerDerivInChart (fun w ↦ h w k i) frame.center j / frame.eigenvalue i := by
    intro i j k
    dsimp [christoffelInChart, h, g]
    rw [frame.perturbed_diagonal, hInvDiagonal, frame.reference_normal]
    simp [Matrix.diagonal_apply, Matrix.one_apply, frame.reference_first]
    rw [div_eq_mul_inv]
    ring
  have hEnergyTransport :
      (∀ i j k : Fin n,
        christoffelInChart h frame.center i j k -
            christoffelInChart g frame.center i j k =
          wirtingerDerivInChart (fun w ↦ h w k i) frame.center j / frame.eigenvalue i) →
      calabiEnergy ω₀ φ x =
        ∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          ‖wirtingerDerivInChart (fun w ↦ h w j k) frame.center p‖ ^ (2 : ℕ) /
            (frame.eigenvalue p * frame.eigenvalue j * frame.eigenvalue k) := by
    intro hCoeff
    classical
    let hφ : ω₀.IsPotential φ := hsol.1
    let F := frame.coord
    let U := frame.domain
    let V := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
    let G₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun w ↦ ω₀.metricInChart x w
    let H₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun w ↦ (ω₀.perturb φ hφ).metricInChart x w
    let A := EuclideanSpace.clmMatrix (fderiv ℂ F frame.center)
    let B := A⁻¹
    have hFcenter : F frame.center ∈ V :=
      frame.in_chart ⟨frame.center, frame.center_mem, rfl⟩
    have hFV : Set.MapsTo F U V := fun w hw ↦ frame.in_chart ⟨w, hw, rfl⟩
    have hAunit : IsUnit A.det := by
      dsimp [A, F]
      exact frame.jacobian_unit frame.center frame.center_mem
    have hAB : A * B = 1 := by
      dsimp [B]
      exact Matrix.mul_nonsing_inv A hAunit
    have hBA : B * A = 1 := by
      dsimp [B]
      have hc := Matrix.nonsing_inv_mul_cancel_left A
        (1 : Matrix (Fin n) (Fin n) ℂ) hAunit
      simpa using hc
    have hG₀smooth : ∀ a b, ContDiffOn ℝ 1 (fun w ↦ G₀ w a b) V := by
      intro a b
      exact (ω₀.contDiffOn_metricInChart x a b).of_le (by norm_num)
    have hH₀smooth : ∀ a b, ContDiffOn ℝ 1 (fun w ↦ H₀ w a b) V := by
      intro a b
      exact ((ω₀.perturb φ hφ).contDiffOn_metricInChart x a b).of_le (by norm_num)
    have hGmetric : ∀ w ∈ U, g w =
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * G₀ (F w) *
          (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star := by
      intro w hw
      rfl
    have hHmetric : ∀ w ∈ U, h w =
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * H₀ (F w) *
          (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star := by
      intro w hw
      change (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose *
          (ω₀.metricInChart x (F w) +
            complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) (F w)) *
          (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star =
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * H₀ (F w) *
          (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star
      rw [← KahlerForm.metricInChart_perturb hφ x (hFV hw)]
    let : PartialOrder ℂ := Complex.partialOrder
    have hPosG : (G₀ (F frame.center)).PosDef :=
      ω₀.posDef_metricInChart x hFcenter
    have hPosH : (H₀ (F frame.center)).PosDef :=
      (ω₀.perturb φ hφ).posDef_metricInChart x hFcenter
    have hGdet : IsUnit (G₀ (F frame.center)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hPosG.isUnit
    have hHdet : IsUnit (H₀ (F frame.center)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hPosH.isUnit
    let Hc : Matrix (Fin n) (Fin n) ℂ := H₀ (F frame.center)
    let Hci : Matrix (Fin n) (Fin n) ℂ := Hc⁻¹
    let T : Fin n → Fin n → Fin n → ℂ := fun i j k ↦
      christoffelInChart H₀ (F frame.center) i j k -
        christoffelInChart G₀ (F frame.center) i j k
    let T' : Fin n → Fin n → Fin n → ℂ := fun i j k ↦
      christoffelInChart h frame.center i j k - christoffelInChart g frame.center i j k
    have hT : T' = nfTensorChange A B T := by
      funext i j k
      simpa [T, T', nfTensorChange, christoffelInChart, A, B, F, U, V,
        G₀, H₀, g, h, Fintype.sum_prod_type] using
        (KahlerForm.ChartInvariance.calabiEnergy_connectionDifference_transition_generic
          F H₀ G₀ h g U V frame.open_domain (isOpen_extChartAt_target x)
          (frame.holomorphic.of_le (by decide)) hH₀smooth hG₀smooth hFV hHmetric hGmetric
          frame.center frame.center_mem B hAB hBA hHdet hGdet i j k)
    obtain ⟨hOut, hIn⟩ := nfPullbackPairContractions A B Hc Hci hAB
    have hhMetric : h frame.center = nfPullbackMetric A Hc := by
      simpa [nfPullbackMetric, c3RefinedTracePulledPerturbedMetric, A, F, H₀, Hc] using
        (hHmetric frame.center frame.center_mem)
    have hOut' : ∀ p s, ∑ z : NFPair (Fin n),
        h frame.center z.1 z.2 * B z.1 p * star (B z.2 s) = Hc p s := by
      intro p s
      rw [hhMetric]
      simpa [nfPullbackMetric, A, Hc] using hOut p s
    have hIn' : ∀ q t, ∑ z : NFPair (Fin n),
        (h frame.center)⁻¹ z.1 z.2 * A q z.2 * star (A t z.1) = Hci t q := by
      intro q t
      have hinv : (h frame.center)⁻¹ = nfPullbackInverse B Hci := by
        rw [hhMetric]
        exact nfPullbackMetricInverse A B Hc hAB hBA hHdet
      simpa [hinv, nfPullbackInverse, A, B, F, H₀, Hc, Hci] using hIn q t
    have hContract : nfTensorContract (fun i j ↦ h frame.center i j)
        (fun i j ↦ (h frame.center)⁻¹ i j) T' =
        nfTensorContract (fun i j ↦ Hc i j) (fun i j ↦ Hci i j) T := by
      rw [hT]
      exact nfTensorContractTensorChange _ _ _ _ A B T hOut' hIn'
    have hOrig : calabiEnergy ω₀ φ x =
        RCLike.re (nfTensorContract (fun i j ↦ Hc i j) (fun i j ↦ Hci i j) T) := by
      have hbase :
          ω₀.metricInChart x (F frame.center) +
              complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
                (F frame.center) = Hc := by
        calc
          _ = (ω₀.perturb φ hφ).metricInChart x (F frame.center) :=
            (KahlerForm.metricInChart_perturb hφ x hFcenter).symm
          _ = Hc := by simp [Hc, H₀, F]
      have hconn (i j k : Fin n) :
          connectionDifferenceInChart ω₀ φ x (F frame.center) i j k = T i j k := by
        change christoffelInChart
            (fun w ↦ ω₀.metricInChart x w +
              complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w)
            (F frame.center) i j k -
          christoffelInChart (fun w ↦ ω₀.metricInChart x w) (F frame.center) i j k =
          christoffelInChart H₀ (F frame.center) i j k -
            christoffelInChart G₀ (F frame.center) i j k
        rw [KahlerForm.ChartInvariance.calabiEnergy_c3Christoffel_perturb
          ω₀ hφ x (F frame.center) hFcenter i j k]
      simp only [calabiEnergy]
      rw [← frame.center_eq]
      simp only [calabiEnergyInChart, Hc, Hci, T]
      rw [hbase]
      have hTvalue : ∀ i j k, connectionDifferenceInChart ω₀ φ x
          (frame.coord frame.center) i j k = T i j k := by
        simpa [F] using hconn
      simp_rw [hTvalue]
      rw [← nfTensorContractReindex (fun i j ↦ Hc i j) (fun i j ↦ Hci i j) T]
    let cycle : NFTriple (Fin n) ≃ NFTriple (Fin n) :=
      { toFun := fun v ↦ (v.2.1, v.2.2, v.1)
        invFun := fun v ↦ (v.2.2, v.1, v.2.1)
        left_inv := by rintro ⟨i,j,k⟩; rfl
        right_inv := by rintro ⟨i,j,k⟩; rfl }
    have hhdiag : h frame.center =
        Matrix.diagonal (fun j ↦ (frame.eigenvalue j : ℂ)) := frame.perturbed_diagonal
    have hCoeff' (i j k : Fin n) : T' i j k =
        wirtingerDerivInChart (fun w ↦ h w k i) frame.center j / (frame.eigenvalue i : ℂ) := by
      simpa [T', h, g, F] using hCoeff i j k
    let D : Fin n → Fin n → Fin n → ℂ :=
      fun i j k ↦ wirtingerDerivInChart (fun w ↦ h w k i) frame.center j
    have hRightReindex :
        (∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          ‖wirtingerDerivInChart (fun w ↦ h w j k) frame.center p‖ ^ (2 : ℕ) /
            (frame.eigenvalue p * frame.eigenvalue j * frame.eigenvalue k)) =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          ‖D i j k‖ ^ (2 : ℕ) /
            (frame.eigenvalue j * frame.eigenvalue k * frame.eigenvalue i) := by
      calc
        _ = ∑ v : NFTriple (Fin n),
            ‖D v.2.2 v.1 v.2.1‖ ^ (2 : ℕ) /
              (frame.eigenvalue v.1 * frame.eigenvalue v.2.1 * frame.eigenvalue v.2.2) := by
          simp only [Fintype.sum_prod_type, D]
        _ = ∑ v : NFTriple (Fin n),
            ‖D v.1 v.2.1 v.2.2‖ ^ (2 : ℕ) /
              (frame.eigenvalue v.2.1 * frame.eigenvalue v.2.2 * frame.eigenvalue v.1) := by
          exact Fintype.sum_equiv cycle.symm _ _ (by
            rintro ⟨i,j,k⟩
            simp [D, cycle])
        _ = _ := by simp only [Fintype.sum_prod_type]
    have hDiag : RCLike.re (nfTensorContract (fun i j ↦ h frame.center i j)
        (fun i j ↦ (h frame.center)⁻¹ i j) T') =
        ∑ p : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          ‖wirtingerDerivInChart (fun w ↦ h w j k) frame.center p‖ ^ (2 : ℕ) /
            (frame.eigenvalue p * frame.eigenvalue j * frame.eigenvalue k) := by
      rw [← nfTensorContractReindex (fun i j ↦ h frame.center i j)
        (fun i j ↦ (h frame.center)⁻¹ i j) T']
      rw [hhdiag, hInvDiagonal]
      simp_rw [hCoeff']
      rw [hRightReindex]
      simp [Matrix.diagonal_apply]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hnorm : ‖D i j k‖ ^ (2 : ℕ) =
          (D i j k).re * (D i j k).re + (D i j k).im * (D i j k).im := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      rw [hnorm]
      field_simp [ne_of_gt (frame.eigenvalue_pos i),
        ne_of_gt (frame.eigenvalue_pos j), ne_of_gt (frame.eigenvalue_pos k)]
      ring
    calc
      calabiEnergy ω₀ φ x = RCLike.re (nfTensorContract
          (fun i j ↦ Hc i j) (fun i j ↦ Hci i j) T) := hOrig
      _ = RCLike.re (nfTensorContract (fun i j ↦ h frame.center i j)
          (fun i j ↦ (h frame.center)⁻¹ i j) T') := by rw [hContract]
      _ = _ := hDiag
  exact hEnergyTransport hCoefficient

end KahlerForm
