module

public import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.Basic
import CalabiYau.MongeAmpere.Estimates.C3.CalabiEnergy.ChartInvariance.Wirtinger

@[expose] public section

open scoped BigOperators Manifold ContDiff ComplexOrder

namespace KahlerForm.ChartInvariance

theorem pullback_entry_derivative {n : ℕ}
    (J : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (p j k : Fin n)
    (hJ : ∀ r s, DifferentiableAt ℂ (fun w ↦ J w r s) z)
    (hG : ∀ r s, DifferentiableAt ℝ (fun w ↦ G w r s) (ψ z))
    (hψ : DifferentiableAt ℂ ψ z) :
    wirtingerDerivInChart
        (fun w ↦ ((J w).transpose * G (ψ w) * (J w).map star) j k) z p =
      ∑ r, ∑ s,
        (wirtingerDerivInChart (fun w ↦ J w r j) z p * G (ψ z) r s * star (J z s k) +
          J z r j * (∑ a, (EuclideanSpace.clmMatrix (fderiv ℂ ψ z)) a p *
            wirtingerDerivInChart (fun w ↦ G w r s) (ψ z) a) * star (J z s k)) := by
  let T (rs : Fin n × Fin n) (w : EuclideanSpace ℂ (Fin n)) : ℂ :=
    (J w rs.1 j * star (J w rs.2 k)) * G (ψ w) rs.1 rs.2
  have hentry (w : EuclideanSpace ℂ (Fin n)) :
      ((J w).transpose * G (ψ w) * (J w).map star) j k =
        ∑ r, ∑ s, (J w r j * star (J w s k)) * G (ψ w) r s := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hTdiff (rs : Fin n × Fin n) : DifferentiableAt ℝ (T rs) z := by
    have hJ1 : DifferentiableAt ℝ (fun w ↦ J w rs.1 j) z :=
      (hJ rs.1 j).hasFDerivAt.restrictScalars ℝ |>.differentiableAt
    have hJ2 : DifferentiableAt ℝ (fun w ↦ star (J w rs.2 k)) z := by
      have h := (hJ rs.2 k).hasFDerivAt.restrictScalars ℝ
      have hc := Complex.conjCLE.hasFDerivAt (x := J z rs.2 k)
      simpa [Function.comp_def, Complex.star_def, Complex.conjCLE_apply] using
        (hc.comp z h).differentiableAt
    have hGcomp : DifferentiableAt ℝ (fun w ↦ G (ψ w) rs.1 rs.2) z := by
      have hψR := hψ.hasFDerivAt.restrictScalars ℝ
      exact (hG rs.1 rs.2).comp z hψR.differentiableAt
    exact (hJ1.mul hJ2).mul hGcomp
  have hfun :
      (fun w ↦ ((J w).transpose * G (ψ w) * (J w).map star) j k) =
        fun w ↦ ∑ rs : Fin n × Fin n, T rs w := by
    funext w
    rw [hentry w]
    simp only [T, Fintype.sum_prod_type]
  rw [hfun]
  rw [wirtingerDerivInChart_sum T z p hTdiff]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  simp only [T]
  have hT_eq : (fun w ↦ (J w r j * star (J w s k)) * G (ψ w) r s) =
      fun w ↦ J w r j * G (ψ w) r s * star (J w s k) := by
    funext w
    ring
  rw [hT_eq]
  exact pullback_summand (fun w ↦ J w r j) (fun w ↦ J w s k)
    (fun w ↦ G w r s) ψ z p (hJ r j) (hJ s k) (hG r s) hψ

/-- The actual first jet of a holomorphic metric pullback, with local equality
of the metric functions on the open overlap. Nothing is assumed about their
values or regularity outside `U` and `V`. The derivative `∂z` includes `1/2`. -/
theorem calabiEnergy_c3PartialZ_metric_pullback {n : ℕ}
    (F : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (g g' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U V : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℂ 2 F U)
    (hg : ∀ a b, ContDiffOn ℝ 1 (fun w => g w a b) V)
    (hFV : Set.MapsTo F U V)
    (hmetric : ∀ w ∈ U, g' w =
      (EuclideanSpace.clmMatrix (fderiv ℂ F w)).transpose * g (F w) *
        (EuclideanSpace.clmMatrix (fderiv ℂ F w)).map star)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) (j k l : Fin n) :
    let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w)
    wirtingerDerivInChart (fun w => g' w k l) z j =
      (∑ r, ∑ s,
        wirtingerDerivInChart (fun w => A w r k) z j * g (F z) r s * star (A z s l)) +
      ∑ p, ∑ r, ∑ s, A z p j * A z r k *
        wirtingerDerivInChart (fun w => g w r s) (F z) p * star (A z s l) := by
  dsimp only
  let A := fun w => EuclideanSpace.clmMatrix (fderiv ℂ F w)
  have hzV : F z ∈ V := hFV hz
  have hA (r s : Fin n) : DifferentiableAt ℂ (fun w ↦ A w r s) z := by
    have hFz : ContDiffAt ℂ 2 F z := hF.contDiffAt (hU.mem_nhds hz)
    have hfd : ContDiffAt ℂ 1 (fderiv ℂ F) z :=
      hFz.fderiv_right (m := 1) (by norm_num)
    have happly : ContDiffAt ℂ 1
        (fun w ↦ fderiv ℂ F w (EuclideanSpace.single s (1 : ℂ))) z :=
      hfd.clm_apply contDiffAt_const
    have hpi : DifferentiableAt ℂ
        (fun w ↦ EuclideanSpace.equiv (Fin n) ℂ
          (fderiv ℂ F w (EuclideanSpace.single s (1 : ℂ)))) z := by
      fun_prop
    have hentry' : DifferentiableAt ℂ
        (fun w ↦ (fderiv ℂ F w (EuclideanSpace.single s (1 : ℂ))) r) z := by
      have hcoord := differentiableAt_pi.1 hpi r
      simpa [EuclideanSpace.equiv] using hcoord
    have hentry'' : DifferentiableAt ℂ (fun w ↦ A w r s) z := by
      simpa [A, EuclideanSpace.clmMatrix] using hentry'
    exact hentry''
  have hgF (r s : Fin n) : DifferentiableAt ℝ (fun w ↦ g w r s) (F z) :=
    (hg r s).contDiffAt (hV.mem_nhds (hFV hz)) |>.differentiableAt (by norm_num)
  have hFdiff : DifferentiableAt ℂ F z :=
    (hF.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hevent : (fun w ↦ g' w k l) =ᶠ[nhds z]
      fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [hmetric w hw]
  have hderivEq : fderiv ℝ (fun w ↦ g' w k l) z =
      fderiv ℝ (fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l) z :=
    hevent.fderiv_eq
  change (fderiv ℝ (fun w ↦ g' w k l) z (EuclideanSpace.single j 1) -
      Complex.I * fderiv ℝ (fun w ↦ g' w k l) z
        (Complex.I • EuclideanSpace.single j 1)) / 2 = _
  rw [hderivEq]
  change wirtingerDerivInChart
      (fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l) z j = _
  let P : Fin n → Fin n → ℂ := fun r s =>
    wirtingerDerivInChart (fun w ↦ A w r k) z j * g (F z) r s * star (A z s l)
  let Q : Fin n → Fin n → ℂ := fun r s =>
    A z r k * (∑ p, A z p j * wirtingerDerivInChart (fun w ↦ g w r s) (F z) p) *
      star (A z s l)
  let R : Fin n → Fin n → Fin n → ℂ := fun p r s =>
    A z p j * A z r k * wirtingerDerivInChart (fun w ↦ g w r s) (F z) p *
      star (A z s l)
  have hformula : wirtingerDerivInChart
      (fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l) z j =
      ∑ r, ∑ s, (P r s + Q r s) := by
    simpa [P, Q, A, mul_assoc] using
      pullback_entry_derivative A g F z j k l hA hgF hFdiff
  have hq : (∑ r, ∑ s, Q r s) = ∑ p, ∑ r, ∑ s, R p r s := by
    calc
      ∑ r, ∑ s, Q r s = ∑ r, ∑ s, ∑ p, R p r s := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro s hs
        dsimp [Q, R]
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = ∑ p, ∑ r, ∑ s, R p r s := by
        calc
          ∑ r, ∑ s, ∑ p, R p r s = ∑ r, ∑ p, ∑ s, R p r s := by
            apply Finset.sum_congr rfl
            intro r hr
            exact Finset.sum_comm
          _ = ∑ p, ∑ r, ∑ s, R p r s := Finset.sum_comm
  calc
    wirtingerDerivInChart
        (fun w ↦ ((A w).transpose * g (F w) * (A w).map star) k l) z j =
        ∑ r, ∑ s, (P r s + Q r s) := hformula
    _ = (∑ r, ∑ s, P r s) + ∑ p, ∑ r, ∑ s, R p r s := by
      calc
        ∑ r, ∑ s, (P r s + Q r s) = ∑ r, (∑ s, P r s + ∑ s, Q r s) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact Finset.sum_add_distrib
        _ = (∑ r, ∑ s, P r s) + ∑ r, ∑ s, Q r s := Finset.sum_add_distrib
        _ = _ := by rw [hq]
    _ = _ := by simp [P, R, A, mul_assoc]

end KahlerForm.ChartInvariance
