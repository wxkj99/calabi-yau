module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.FiniteJets
import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.ConnectionLaplacian.MetricDerivatives
import CalabiYau.Geometry.Kahler.Curvature.Chart.MixedDerivatives

/-!
# Kähler permutations of metric jets

Székelyhidi, §3.3, proof of Lemma 3.9, Bianchi calculation following (3.15),
printed p. 45. The Kähler condition gives the stated symmetries of the metric jets.

The first-jet Kähler symmetry holds on the open neighborhood `U`, not only at `z`.
The jets are Z-bar, ZZ and ZZ-bar, with the existing Wirtinger normalization.
No positivity, invertibility, Hermitian-entry symmetry or compactness is assumed.

-/

public section

open scoped Manifold ContDiff BigOperators ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ}

private noncomputable def auxiliaryWirtinger
    (t : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ F w (EuclideanSpace.single j 1) +
    t * fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem auxiliaryWirtinger_fderiv (t : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (j : Fin n)
    (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => auxiliaryWirtinger t F w j) z v =
      (fderiv ℝ (fderiv ℝ F) z v (EuclideanSpace.single j 1) +
        t * fderiv ℝ (fderiv ℝ F) z v
          (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
  have he : DifferentiableAt ℝ (fun w => fderiv ℝ F w e) z :=
    hfd.clm_apply (differentiableAt_const _)
  have hie : DifferentiableAt ℝ (fun w => fderiv ℝ F w (Complex.I • e)) z :=
    hfd.clm_apply (differentiableAt_const _)
  have h_e (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w => fderiv ℝ F w e) z u = fderiv ℝ (fderiv ℝ F) z u e := by
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  have h_ie (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w => fderiv ℝ F w (Complex.I • e)) z u =
        fderiv ℝ (fderiv ℝ F) z u (Complex.I • e) := by
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  have hsum : DifferentiableAt ℝ
      (fun w => fderiv ℝ F w e + t * fderiv ℝ F w (Complex.I • e)) z :=
    he.add (hie.const_mul t)
  have hfun : (fun w => auxiliaryWirtinger t F w j) =
      fun w => (2 : ℂ)⁻¹ *
        (fderiv ℝ F w e + t * fderiv ℝ F w (Complex.I • e)) := by
    funext w
    simp only [auxiliaryWirtinger, e, div_eq_mul_inv]
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul t),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem auxiliaryWirtinger_comm_at (s t : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    auxiliaryWirtinger s (fun w => auxiliaryWirtinger t F w q) z p =
      auxiliaryWirtinger t (fun w => auxiliaryWirtinger s F w p) z q := by
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  let eq : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single q 1
  have hs : IsSymmSndFDerivAt ℝ F z :=
    hF.isSymmSndFDerivAt
      (by simpa [minSmoothness_of_isRCLikeNormedField] using
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change (fderiv ℝ (fun w => auxiliaryWirtinger t F w q) z ep +
    s * fderiv ℝ (fun w => auxiliaryWirtinger t F w q) z
      (Complex.I • ep)) / 2 =
    (fderiv ℝ (fun w => auxiliaryWirtinger s F w p) z eq +
    t * fderiv ℝ (fun w => auxiliaryWirtinger s F w p) z
      (Complex.I • eq)) / 2
  rw [auxiliaryWirtinger_fderiv t F z hF q ep,
    auxiliaryWirtinger_fderiv t F z hF q (Complex.I • ep),
    auxiliaryWirtinger_fderiv s F z hF p eq,
    auxiliaryWirtinger_fderiv s F z hF p (Complex.I • eq)]
  dsimp only [ep, eq] at *
  rw [hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)]
  ring

private theorem chartPartialZComplex_chartPartialZComplex_comm_at
    (F : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    chartPartialZComplex (fun w => chartPartialZComplex F w p) z q =
      chartPartialZComplex (fun w => chartPartialZComplex F w q) z p := by
  have hrepr (G : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      auxiliaryWirtinger (-Complex.I) G w j = chartPartialZComplex G w j := by
    simp [auxiliaryWirtinger, chartPartialZComplex, div_eq_mul_inv]
    ring
  have hfun (j : Fin n) :
      (fun w => auxiliaryWirtinger (-Complex.I) F w j) =
        (fun w => chartPartialZComplex F w j) := funext (fun w => hrepr F w j)
  calc
    chartPartialZComplex (fun w => chartPartialZComplex F w p) z q =
        auxiliaryWirtinger (-Complex.I)
          (fun w => auxiliaryWirtinger (-Complex.I) F w p) z q := by
      rw [hfun p]
      exact (hrepr (fun w => chartPartialZComplex F w p) z q).symm
    _ = auxiliaryWirtinger (-Complex.I)
          (fun w => auxiliaryWirtinger (-Complex.I) F w q) z p :=
      auxiliaryWirtinger_comm_at (-Complex.I) (-Complex.I) F z hF q p
    _ = chartPartialZComplex (fun w => chartPartialZComplex F w q) z p := by
      rw [hfun q]
      exact hrepr (fun w => chartPartialZComplex F w q) z p

private theorem chartPartialZComplex_congr_eventuallyEq
    (F G : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hFG : F =ᶠ[nhds z] G) (p : Fin n) :
    chartPartialZComplex F z p = chartPartialZComplex G z p := by
  have hfd := hFG.fderiv_eq (𝕜 := ℝ)
  simpa [chartPartialZComplex] using congrArg
    (fun D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ =>
      (D (EuclideanSpace.single p 1) -
        Complex.I * D (Complex.I • EuclideanSpace.single p 1)) / 2) hfd

private theorem chartPartialBarComplex_congr_eventuallyEq
    (F G : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n))
    (hFG : F =ᶠ[nhds z] G) (q : Fin n) :
    chartPartialBarComplex F z q = chartPartialBarComplex G z q := by
  have hfd := hFG.fderiv_eq (𝕜 := ℝ)
  simpa [chartPartialBarComplex] using congrArg
    (fun D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ =>
      (D (EuclideanSpace.single q 1) +
        Complex.I * D (Complex.I • EuclideanSpace.single q 1)) / 2) hfd

theorem c3MetricJetZBar_permute_of_kahler
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun w => g w a b) U)
    (hK : ∀ w ∈ U, ∀ i j k,
      chartPartialZComplex (fun v => g v j k) w i =
        chartPartialZComplex (fun v => g v i k) w j)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (p q k l : Fin n) :
    c3MetricJetZBar g z p q k l = c3MetricJetZBar g z k q p l := by
  let F := fun w => chartPartialZComplex (fun v => g v k l) w p
  let G := fun w => chartPartialZComplex (fun v => g v p l) w k
  have hEq : F =ᶠ[nhds z] G := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hK w hw p k l
  have hfd := hEq.fderiv_eq (𝕜 := ℝ)
  have hbar : chartPartialBarComplex F z q = chartPartialBarComplex G z q := by
    simpa [chartPartialBarComplex, F, G] using congrArg
      (fun D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ =>
        (D (EuclideanSpace.single q 1) +
          Complex.I * D (Complex.I • EuclideanSpace.single q 1)) / 2) hfd
  have hgkl : ContDiffAt ℝ ∞ (fun v => g v k l) z :=
    (hg k l z hz).contDiffAt (hU.mem_nhds hz)
  have hgpl : ContDiffAt ℝ ∞ (fun v => g v p l) z :=
    (hg p l z hz).contDiffAt (hU.mem_nhds hz)
  calc
    c3MetricJetZBar g z p q k l = chartPartialBarComplex F z q := by
      change chartPartialZComplex (fun w => chartPartialBarComplex
        (fun v => g v k l) w q) z p = _
      rw [← chartPartialBarComplex_chartPartialZComplex_comm_at
        (fun v => g v k l) z hgkl p q]
    _ = chartPartialBarComplex G z q := hbar
    _ = c3MetricJetZBar g z k q p l := by
      change chartPartialBarComplex G z q = chartPartialZComplex
        (fun w => chartPartialBarComplex (fun v => g v p l) w q) z k
      rw [chartPartialBarComplex_chartPartialZComplex_comm_at
        (fun v => g v p l) z hgpl k q]

theorem c3MetricJetZZ_permute_of_kahler
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun w => g w a b) U)
    (hK : ∀ w ∈ U, ∀ i j k,
      chartPartialZComplex (fun v => g v j k) w i =
        chartPartialZComplex (fun v => g v i k) w j)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (s p k b : Fin n) :
    c3MetricJetZZ g z s p k b = c3MetricJetZZ g z k s p b := by
  let F := fun w => chartPartialZComplex (fun v => g v k b) w p
  let G := fun w => chartPartialZComplex (fun v => g v p b) w k
  have hEq : F =ᶠ[nhds z] G := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hK w hw p k b
  have hgp : ContDiffAt ℝ ∞ (fun v => g v p b) z :=
    (hg p b z hz).contDiffAt (hU.mem_nhds hz)
  calc
    c3MetricJetZZ g z s p k b = chartPartialZComplex F z s := rfl
    _ = chartPartialZComplex G z s :=
      chartPartialZComplex_congr_eventuallyEq F G z hEq s
    _ = c3MetricJetZZ g z k s p b := by
      change chartPartialZComplex
          (fun w => chartPartialZComplex (fun v => g v p b) w k) z s =
        chartPartialZComplex
          (fun w => chartPartialZComplex (fun v => g v p b) w s) z k
      exact chartPartialZComplex_chartPartialZComplex_comm_at
        (fun v => g v p b) z hgp k s

theorem c3MetricJetZZBar_permute_of_kahler
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hg : ∀ a b, ContDiffOn ℝ ∞ (fun w => g w a b) U)
    (hK : ∀ w ∈ U, ∀ i j k,
      chartPartialZComplex (fun v => g v j k) w i =
        chartPartialZComplex (fun v => g v i k) w j)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
    (s p q k l : Fin n) :
    c3MetricJetZZBar g z s p q k l = c3MetricJetZZBar g z k s q p l := by
  let A := fun w => chartPartialZComplex (fun v => g v k l) w p
  let B := fun w => chartPartialZComplex (fun v => g v p l) w k
  let F := fun w => chartPartialZComplex
    (fun v => chartPartialBarComplex (fun u => g u k l) v q) w p
  let G := fun w => chartPartialZComplex
    (fun v => chartPartialBarComplex (fun u => g u p l) v q) w k
  have hFG : F =ᶠ[nhds z] G := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hAB : A =ᶠ[nhds w] B := by
      filter_upwards [hU.mem_nhds hw] with v hv
      exact hK v hv p k l
    have hbar := chartPartialBarComplex_congr_eventuallyEq A B w hAB q
    have hgkl : ContDiffAt ℝ ∞ (fun u => g u k l) w :=
      (hg k l w hw).contDiffAt (hU.mem_nhds hw)
    have hgpl : ContDiffAt ℝ ∞ (fun u => g u p l) w :=
      (hg p l w hw).contDiffAt (hU.mem_nhds hw)
    change F w = G w
    dsimp [F, G, A, B]
    calc
      chartPartialZComplex
          (fun v => chartPartialBarComplex (fun u => g u k l) v q) w p =
          chartPartialBarComplex A w q := by
        rw [← chartPartialBarComplex_chartPartialZComplex_comm_at
          (fun u => g u k l) w hgkl p q]
      _ = chartPartialBarComplex B w q := hbar
      _ = chartPartialZComplex
          (fun v => chartPartialBarComplex (fun u => g u p l) v q) w k := by
        rw [chartPartialBarComplex_chartPartialZComplex_comm_at
          (fun u => g u p l) w hgpl k q]
  have hgpl : ContDiffAt ℝ ∞ (fun u => g u p l) z :=
    (hg p l z hz).contDiffAt (hU.mem_nhds hz)
  have hbarSmooth := c3ChartPartialBar_contDiffAt
    (fun u => g u p l) z hgpl q
  calc
    c3MetricJetZZBar g z s p q k l = chartPartialZComplex F z s := rfl
    _ = chartPartialZComplex G z s :=
      chartPartialZComplex_congr_eventuallyEq F G z hFG s
    _ = c3MetricJetZZBar g z k s q p l := by
      change chartPartialZComplex
          (fun w => chartPartialZComplex
            (fun v => chartPartialBarComplex (fun u => g u p l) v q) w k) z s =
        chartPartialZComplex
          (fun w => chartPartialZComplex
            (fun v => chartPartialBarComplex (fun u => g u p l) v q) w s) z k
      exact chartPartialZComplex_chartPartialZComplex_comm_at
        (fun v => chartPartialBarComplex (fun u => g u p l) v q) z hbarSmooth k s

end KahlerForm
