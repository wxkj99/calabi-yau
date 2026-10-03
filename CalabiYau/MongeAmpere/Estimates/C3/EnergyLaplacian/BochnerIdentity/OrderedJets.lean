module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerTensors
import CalabiYau.Mathlib.Analysis.Matrix.EntrywiseSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Ordered tensor jets, weighted pairing calculus and local regularity

Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45, (3.14).
The inverse entry is [q,p]; curvature begins with -partialZ_p(partialBar_q g).
The pairing is linear on the left and conjugate-linear on the right.
This computation uses only the stated
No off-target smoothness is assumed.
-/

@[expose] public section

open scoped Manifold ContDiff BigOperators ComplexOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

noncomputable def c3OppositeConnectionTensorLaplacian (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M) (z : EuclideanSpace ℂ (Fin n))
    (i j k : Fin n) : ℂ :=
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := connectionDifferenceInChart ω₀ φ x
  ∑ p, ∑ q, (g z)⁻¹ q p *
    c3PartialBar (fun w ↦ c3TensorCovariantZ g T w p i j k) z q

theorem c3Pair_add_left
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (A B U : Fin n → Fin n → Fin n → ℂ) :
    c3Pair g z (fun i j k ↦ A i j k + B i j k) U =
      c3Pair g z A U + c3Pair g z B U := by
  simp [c3Pair, Finset.sum_add_distrib, mul_add, add_mul]

def MetricPairLeibnizOn {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∀ (A B : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ),
    (∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ A w i j k) U) →
    (∀ i j k, ContDiffOn ℝ ∞ (fun w ↦ B w i j k) U) →
    ∀ z ∈ U, ∀ p,
      wirtingerDerivInChart (fun w ↦ c3Pair g w (A w) (B w)) z p =
        c3Pair g z (c3TensorCovariantZ g A z p) (B z) +
          c3Pair g z (A z) (fun i j k ↦
            c3PartialBar (fun w ↦ B w i j k) z p)

noncomputable def c3ChartPairHessianLaplacian (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M) : ℝ :=
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := connectionDifferenceInChart ω₀ φ x
  let z := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x
  (((g z)⁻¹ * complexHessian (fun w ↦ (c3Pair g w (T w) (T w)).re) z).trace).re

private theorem wirtingerDerivInChart_contDiffOn_entry
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ k l, ContDiffOn ℝ ∞ (fun z ↦ G z k l) U)
    (j k l : Fin n) :
    ContDiffOn ℝ ∞ (fun z ↦ wirtingerDerivInChart (fun w ↦ G w k l) z j) U := by
  let f : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ G w k l
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) U :=
    (hG k l).fderiv_of_isOpen hU (by rw [ENat.coe_top_add_one])
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

theorem c3Christoffel_contDiffOn
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U)
    (hGinv : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ (G z)⁻¹ i j) U)
    (i j k : Fin n) :
    ContDiffOn ℝ ∞ (fun z ↦ christoffelInChart G z i j k) U := by
  have hterm (l : Fin n) : ContDiffOn ℝ ∞
      (fun z ↦ (G z)⁻¹ l i * wirtingerDerivInChart (fun w ↦ G w k l) z j) U :=
    (hGinv l i).mul (wirtingerDerivInChart_contDiffOn_entry hU hG j k l)
  have hsum : ContDiffOn ℝ ∞
      (fun z ↦ ∑ l ∈ Finset.univ, (G z)⁻¹ l i *
        wirtingerDerivInChart (fun w ↦ G w k l) z j) U := by
    apply ContDiffOn.sum
    intro l hl
    exact hterm l
  change ContDiffOn ℝ ∞
    (fun z ↦ ∑ l ∈ Finset.univ, (G z)⁻¹ l i *
      wirtingerDerivInChart (fun w ↦ G w k l) z j) U
  exact hsum

omit [T2Space M] [CompactSpace M] in theorem c3ConnectionDifference_contDiffAt
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ) (x : M)
    (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (i j k : Fin n) :
    ContDiffAt ℝ ∞
      (fun w ↦ connectionDifferenceInChart ω₀ φ x w i j k) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let U := e.target
  let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ ω₀.metricInChart x w
  let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w ↦ g₀ w + complexHessian (φ ∘ e.symm) w
  have hU : IsOpen U := isOpen_extChartAt_target x
  have hG₀ : ∀ a b, ContDiffOn ℝ ∞ (fun w ↦ g₀ w a b) U := by
    intro a b
    exact ω₀.contDiffOn_metricInChart x a b
  have hGφ : ∀ a b, ContDiffOn ℝ ∞ (fun w ↦ gφ w a b) U := by
    intro a b
    have hreg := (ω₀.perturb φ hφ).contDiffOn_metricInChart x a b
    apply hreg.congr
    intro w hw
    have heq : gφ w = (ω₀.perturb φ hφ).metricInChart x w := by
      simpa [gφ, g₀, e] using (ω₀.metricInChart_perturb hφ x hw).symm
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A a b) heq
  have hUnit₀ : ∀ w ∈ U, IsUnit (g₀ w) := by
    intro w hw
    exact (ω₀.posDef_metricInChart x hw).isUnit
  have hUnitφ : ∀ w ∈ U, IsUnit (gφ w) := by
    intro w hw
    have hunit := (ω₀.perturb φ hφ).posDef_metricInChart x hw |>.isUnit
    have heq : gφ w = (ω₀.perturb φ hφ).metricInChart x w := by
      simpa [gφ, g₀, e] using (ω₀.metricInChart_perturb hφ x hw).symm
    rw [heq]
    exact hunit
  have hG₀inv := Matrix.contDiffOn_inverse_entries hG₀ hUnit₀
  have hGφinv := Matrix.contDiffOn_inverse_entries hGφ hUnitφ
  have hΓ₀ : ContDiffOn ℝ ∞
      (fun w ↦ christoffelInChart g₀ w i j k) U :=
    c3Christoffel_contDiffOn hU hG₀ hG₀inv i j k
  have hΓφ : ContDiffOn ℝ ∞
      (fun w ↦ christoffelInChart gφ w i j k) U :=
    c3Christoffel_contDiffOn hU hGφ hGφinv i j k
  have hT : ContDiffOn ℝ ∞
      (fun w ↦ connectionDifferenceInChart ω₀ φ x w i j k) U := by
    change ContDiffOn ℝ ∞
      (fun w ↦ christoffelInChart gφ w i j k -
        christoffelInChart g₀ w i j k) U
    exact hΓφ.sub hΓ₀
  exact hT.contDiffAt (hU.mem_nhds hz)

theorem c3Pair_partialZ_mul
    (f h : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    wirtingerDerivInChart (fun w ↦ f w * h w) z p =
      wirtingerDerivInChart f z p * h z + f z * wirtingerDerivInChart h z p := by
  have hprod (v : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ f w * h w) z v =
        f z * fderiv ℝ h z v + fderiv ℝ f z v * h z := by
    calc
      fderiv ℝ (fun w ↦ f w * h w) z v =
          f z * fderiv ℝ h z v + h z * fderiv ℝ f z v := by
        have h := (hf.hasFDerivAt.mul hh.hasFDerivAt).fderiv
        convert congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ => L v) h using 1
      _ = f z * fderiv ℝ h z v + fderiv ℝ f z v * h z := by ring
  unfold wirtingerDerivInChart
  rw [hprod (EuclideanSpace.single p 1),
    hprod (Complex.I • EuclideanSpace.single p 1)]
  ring

theorem c3Pair_partialZ_finset_sum {α : Type*} (s : Finset α)
    (f : α → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) z) :
    wirtingerDerivInChart (fun w ↦ ∑ a ∈ s, f a w) z p =
      ∑ a ∈ s, wirtingerDerivInChart (f a) z p := by
  unfold wirtingerDerivInChart
  rw [fderiv_fun_sum hf]
  simp only [sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_div]

theorem c3Pair_partialZ_star
    (f : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (_hf : DifferentiableAt ℝ f z) :
    wirtingerDerivInChart (fun w ↦ star (f w)) z p =
      star (c3PartialBar f z p) := by
  unfold wirtingerDerivInChart c3PartialBar
  rw [fderiv_star]
  simp [starL']
  ring

private noncomputable def c3PairWirtinger
    {n : ℕ} (s : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ F w (EuclideanSpace.single j 1) +
    s * fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem c3PairWirtinger_fderiv
    {n : ℕ} (s : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ ∞ F z) (j : Fin n)
    (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => c3PairWirtinger s F w j) z v =
      (fderiv ℝ (fderiv ℝ F) z v (EuclideanSpace.single j 1) +
        s * fderiv ℝ (fderiv ℝ F) z v
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
      (fun w => fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) z :=
    he.add (hie.const_mul s)
  have hfun : (fun w => c3PairWirtinger s F w j) =
      fun w => (2 : ℂ)⁻¹ * (fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) := by
    funext w
    simp only [c3PairWirtinger, e, div_eq_mul_inv]
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul s),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem c3PairWirtinger_comm
    {n : ℕ} (s t : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    c3PairWirtinger s (fun w => c3PairWirtinger t F w q) z p =
      c3PairWirtinger t (fun w => c3PairWirtinger s F w p) z q := by
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  let eq : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single q 1
  have hs : IsSymmSndFDerivAt ℝ F z :=
    hF.isSymmSndFDerivAt
      (by simp [minSmoothness_of_isRCLikeNormedField])
  change (fderiv ℝ (fun w => c3PairWirtinger t F w q) z ep +
    s * fderiv ℝ (fun w => c3PairWirtinger t F w q) z (Complex.I • ep)) / 2 =
    (fderiv ℝ (fun w => c3PairWirtinger s F w p) z eq +
    t * fderiv ℝ (fun w => c3PairWirtinger s F w p) z (Complex.I • eq)) / 2
  rw [c3PairWirtinger_fderiv t F z hF q ep,
    c3PairWirtinger_fderiv t F z hF q (Complex.I • ep),
    c3PairWirtinger_fderiv s F z hF p eq,
    c3PairWirtinger_fderiv s F z hF p (Complex.I • eq)]
  dsimp only [ep, eq] at *
  rw [hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1),
    hs (Complex.I • EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)]
  ring

theorem c3PartialBar_partialZ_comm
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ ∞ F z) (p q : Fin n) :
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
      chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
  have hz (A : EuclideanSpace ℂ (Fin n) → ℂ) (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      c3PairWirtinger (-Complex.I) A w j = chartPartialZComplex A w j := by
    simp [c3PairWirtinger, chartPartialZComplex, div_eq_mul_inv]
    ring
  have hb (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      c3PairWirtinger Complex.I F w j = chartPartialBarComplex F w j := rfl
  have hzf (j : Fin n) :
      (fun w => c3PairWirtinger (-Complex.I) F w j) =
        (fun w => chartPartialZComplex F w j) := funext (fun w => hz F w j)
  have hbf (j : Fin n) :
      (fun w => c3PairWirtinger Complex.I F w j) =
        (fun w => chartPartialBarComplex F w j) := funext (fun w => hb w j)
  calc
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
        c3PairWirtinger Complex.I (fun w => c3PairWirtinger (-Complex.I) F w p) z q := by
      rw [hzf]
      rfl
    _ = c3PairWirtinger (-Complex.I) (fun w => c3PairWirtinger Complex.I F w q) z p :=
      (c3PairWirtinger_comm (-Complex.I) Complex.I F z hF p q).symm
    _ = chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
      rw [hbf]
      exact hz (fun w => chartPartialBarComplex F w q) z p

end KahlerForm
