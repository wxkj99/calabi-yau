module

public import CalabiYau.MongeAmpere.Estimates.C3.EnergyLaplacian.BochnerIdentity.OrderedJets
import CalabiYau.Geometry.Kahler.Curvature.ConnectionDerivative

/-!
# The ordered connection commutator and its Ricci contraction

Székelyhidi, §3.3, proof of Lemma 3.9, printed pp. 44–45, (3.14).
The inverse entry is [q,p]; curvature begins with -partialZ_p(partialBar_q g).
The pairing is linear on the left and conjugate-linear on the right.
This computation uses only the stated
No off-target smoothness is assumed.
-/

@[expose] public section

open scoped Manifold ContDiff BigOperators ComplexOrder Matrix.Norms.Elementwise

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

private theorem c3Pair_bar_add
    {n : ℕ}
    (F G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    chartPartialBarComplex (fun w => F w + G w) z q =
      chartPartialBarComplex F z q + chartPartialBarComplex G z q := by
  unfold chartPartialBarComplex
  rw [fderiv_fun_add hF hG]
  simp only [add_apply, add_div]
  ring

private theorem c3Pair_bar_sum
    {n : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : ∀ i, DifferentiableAt ℝ (F i) z) :
    chartPartialBarComplex (fun w => ∑ i, F i w) z q =
      ∑ i, chartPartialBarComplex (F i) z q := by
  unfold chartPartialBarComplex
  have hfd : fderiv ℝ (fun w => ∑ i, F i w) z = ∑ i, fderiv ℝ (F i) z := by
    simpa using fderiv_fun_sum (u := Finset.univ) (fun i hi => hF i)
  rw [hfd]
  simp only [sum_apply]
  have hsum :
      (∑ i, fderiv ℝ (F i) z (EuclideanSpace.single q 1)) +
        Complex.I * ∑ i, fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single q 1) =
      ∑ i, (fderiv ℝ (F i) z (EuclideanSpace.single q 1) +
        Complex.I * fderiv ℝ (F i) z (Complex.I • EuclideanSpace.single q 1)) := by
    rw [Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

private theorem c3Pair_bar_const_mul
    {n : ℕ}
    (c : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : DifferentiableAt ℝ F z) :
    chartPartialBarComplex (fun w => c * F w) z q =
      c * chartPartialBarComplex F z q := by
  unfold chartPartialBarComplex
  rw [fderiv_const_mul hF c]
  simp only [smul_apply, div_eq_mul_inv]
  ring

private theorem c3Pair_bar_neg
    {n : ℕ} (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : DifferentiableAt ℝ F z) :
    chartPartialBarComplex (fun w => -F w) z q =
      -chartPartialBarComplex F z q := by
  have hfun : (fun w => -F w) = (fun w => (-1 : ℂ) * F w) := by
    funext w
    ring
  rw [hfun, c3Pair_bar_const_mul (-1) F z q hF]
  ring

private theorem c3Pair_bar_mul
    {n : ℕ}
    (F G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    chartPartialBarComplex (fun w => F w * G w) z q =
      chartPartialBarComplex F z q * G z + F z * chartPartialBarComplex G z q := by
  unfold chartPartialBarComplex
  rw [fderiv_fun_mul hF hG]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem c3Pair_scalar_connection_commutator
    {n : ℕ} {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (V Γ : ι → EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p q : Fin n)
    (hF : ContDiffAt ℝ ∞ F z)
    (hV : ∀ r, ContDiffAt ℝ ∞ (V r) z)
    (hΓ : ∀ r, ContDiffAt ℝ ∞ (Γ r) z) :
    chartPartialBarComplex
      (fun w => chartPartialZComplex F w p + ∑ r, Γ r w * V r w) z q =
      chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p +
        ∑ r, Γ r z * chartPartialBarComplex (V r) z q +
        ∑ r, chartPartialBarComplex (Γ r) z q * V r z := by
  have hFfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := ∞)
      (le_of_eq (show (∞ : ℕ∞ω) = ∞ + 1 from rfl).symm)).differentiableAt (by norm_num)
  have hFz : DifferentiableAt ℝ (fun w => chartPartialZComplex F w p) z := by
    unfold chartPartialZComplex
    fun_prop (disch := assumption)
  have hprod (r : ι) : DifferentiableAt ℝ (fun w => Γ r w * V r w) z :=
    ((hΓ r).differentiableAt (by norm_num)).mul
      ((hV r).differentiableAt (by norm_num))
  have hsum : DifferentiableAt ℝ (fun w => ∑ r, Γ r w * V r w) z := by
    classical
    exact DifferentiableAt.fun_sum (fun r hr => hprod r)
  have hmul (r : ι) :
      chartPartialBarComplex (fun w => Γ r w * V r w) z q =
        chartPartialBarComplex (Γ r) z q * V r z +
          Γ r z * chartPartialBarComplex (V r) z q :=
    c3Pair_bar_mul (Γ r) (V r) z q
      ((hΓ r).differentiableAt (by norm_num))
      ((hV r).differentiableAt (by norm_num))
  rw [c3Pair_bar_add _ _ z q hFz hsum]
  rw [c3Pair_bar_sum (fun r w => Γ r w * V r w) z q hprod]
  simp_rw [hmul]
  rw [c3PartialBar_partialZ_comm F z hF p q]
  rw [Finset.sum_add_distrib]
  ring

private theorem c3TensorCovariantZ_bar_commutator
    {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (T : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → Fin n → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (p q i j k : Fin n)
    (hT : ∀ a b c, ContDiffAt ℝ ∞ (fun w => T w a b c) z)
    (hΓ : ∀ a b c, ContDiffAt ℝ ∞ (fun w => christoffelInChart g w a b c) z) :
    chartPartialBarComplex
        (fun w => c3TensorCovariantZ g T w p i j k) z q =
      c3TensorCovariantZ g
          (fun w a b c => chartPartialBarComplex (fun v => T v a b c) w q)
          z p i j k +
        (∑ r, chartPartialBarComplex
          (fun w => christoffelInChart g w i p r) z q * T z r j k) -
        (∑ r, chartPartialBarComplex
          (fun w => christoffelInChart g w r p j) z q * T z i r k) -
        ∑ r, chartPartialBarComplex
          (fun w => christoffelInChart g w r p k) z q * T z i j r := by
  let ι := Fin n ⊕ Fin n ⊕ Fin n
  let F : EuclideanSpace ℂ (Fin n) → ℂ := fun w => T w i j k
  let V : ι → EuclideanSpace ℂ (Fin n) → ℂ := fun s w =>
    match s with
    | Sum.inl r => T w r j k
    | Sum.inr (Sum.inl r) => T w i r k
    | Sum.inr (Sum.inr r) => T w i j r
  let G : ι → EuclideanSpace ℂ (Fin n) → ℂ := fun s w =>
    match s with
    | Sum.inl r => christoffelInChart g w i p r
    | Sum.inr (Sum.inl r) => -christoffelInChart g w r p j
    | Sum.inr (Sum.inr r) => -christoffelInChart g w r p k
  have hdecomp (w : EuclideanSpace ℂ (Fin n)) :
      c3TensorCovariantZ g T w p i j k =
        chartPartialZComplex F w p + ∑ s, G s w * V s w := by
    change wirtingerDerivInChart (fun v => T v i j k) w p +
        (∑ r, christoffelInChart g w i p r * T w r j k) -
        (∑ r, christoffelInChart g w r p j * T w i r k) -
        ∑ r, christoffelInChart g w r p k * T w i j r =
      wirtingerDerivInChart (fun v => T v i j k) w p + ∑ s, G s w * V s w
    simp [G, V, ι, Fintype.sum_sum_type, Finset.sum_neg_distrib]
    ring
  have hV (s : ι) : ContDiffAt ℝ ∞ (V s) z := by
    rcases s with r | r | r
    · exact hT _ _ _
    · exact hT _ _ _
    · exact hT _ _ _
  have hG (s : ι) : ContDiffAt ℝ ∞ (G s) z := by
    rcases s with r | r | r
    · exact hΓ _ _ _
    · exact (hΓ _ _ _).neg
    · exact (hΓ _ _ _).neg
  have hcomm := c3Pair_scalar_connection_commutator F V G z p q (hT i j k) hV hG
  have hbarcov :
      c3TensorCovariantZ g
          (fun w a b c => chartPartialBarComplex (fun v => T v a b c) w q)
          z p i j k =
        chartPartialZComplex (fun w => chartPartialBarComplex (fun v => T v i j k) w q) z p +
          ∑ s, G s z * chartPartialBarComplex (V s) z q := by
    change wirtingerDerivInChart (fun w => chartPartialBarComplex (fun v => T v i j k) w q) z p +
        (∑ r, christoffelInChart g z i p r * chartPartialBarComplex (fun v => T v r j k) z q) -
        (∑ r, christoffelInChart g z r p j * chartPartialBarComplex (fun v => T v i r k) z q) -
        ∑ r, christoffelInChart g z r p k * chartPartialBarComplex (fun v => T v i j r) z q =
      wirtingerDerivInChart (fun w => chartPartialBarComplex (fun v => T v i j k) w q) z p +
        ∑ s, G s z * chartPartialBarComplex (V s) z q
    simp [G, V, ι, Fintype.sum_sum_type, Finset.sum_neg_distrib]
    ring
  have hdecompFun :
      (fun w => c3TensorCovariantZ g T w p i j k) =
        (fun w => chartPartialZComplex F w p + ∑ s, G s w * V s w) := by
    funext w
    exact hdecomp w
  rw [hdecompFun, hcomm, ← hbarcov]
  have hnegj (r : Fin n) :
      chartPartialBarComplex
          (fun w => -christoffelInChart g w r p j) z q =
        -chartPartialBarComplex
          (fun w => christoffelInChart g w r p j) z q :=
    c3Pair_bar_neg (fun w => christoffelInChart g w r p j) z q
      ((hΓ r p j).differentiableAt (by simp))
  have hnegk (r : Fin n) :
      chartPartialBarComplex
          (fun w => -christoffelInChart g w r p k) z q =
        -chartPartialBarComplex
          (fun w => christoffelInChart g w r p k) z q :=
    c3Pair_bar_neg (fun w => christoffelInChart g w r p k) z q
      ((hΓ r p k).differentiableAt (by simp))
  simp [G, V, ι, Fintype.sum_sum_type, Finset.sum_neg_distrib,
    hnegj, hnegk]
  ring_nf

private theorem c3PerturbedMetric_barChristoffel
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [T2Space M] [CompactSpace M]
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (hφ : ω₀.IsPotential φ)
    (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (i p r q : Fin n) :
    chartPartialBarComplex
        (fun w => christoffelInChart (c3PerturbedMetricInChart ω₀ φ x) w i p r) z q =
      -(∑ l, (c3PerturbedMetricInChart ω₀ φ x z)⁻¹ l i *
        chartCurvature (c3PerturbedMetricInChart ω₀ φ x) z p q r l) := by
  let U := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  let g₀ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => ω₀.metricInChart x w
  let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun w => g₀ w + complexHessian
      (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w
  let ωφ := ω₀.perturb φ hφ
  have hU : IsOpen U := isOpen_extChartAt_target x
  have heq : Set.EqOn gφ (fun w => ωφ.metricInChart x w) U := by
    intro w hw
    simpa [gφ, g₀, ωφ] using (ω₀.metricInChart_perturb hφ x hw).symm
  have hg : ∀ a b, ContDiffOn ℝ ∞ (fun w => gφ w a b) U := by
    intro a b
    exact (ωφ.contDiffOn_metricInChart x a b).congr
      (fun w hw => congrArg (fun G : Matrix (Fin n) (Fin n) ℂ => G a b) (heq hw))
  have hdet : IsUnit (gφ z).det := by
    rw [heq hz]
    exact (Matrix.isUnit_iff_isUnit_det (A := ωφ.metricInChart x z)).mp
      (ωφ.posDef_metricInChart x hz).isUnit
  have hresult := chartChristoffel_bar_eq_curvature_local
    gφ U hU hg z hz hdet i p r q
  change chartPartialBarComplex
      (fun w => ∑ l, (gφ w)⁻¹ l i *
        chartPartialZComplex (fun v => gφ v r l) w p) z q =
    -(∑ l, (gφ z)⁻¹ l i * chartCurvature gφ z p q r l)
  exact hresult

private theorem c3Pair_sum4_reorder_fin {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  classical
  calc
    _ = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, ∑ d, f a b c d := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ d, ∑ a, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm

private theorem c3Pair_fintype_mul_sum {α : Type*} [Fintype α]
    (a : ℂ) (f : α → ℂ) :
    a * (∑ x, f x) = ∑ x, a * f x := by
  classical
  exact Finset.mul_sum Finset.univ f a

private theorem c3Pair_fintype_sum_mul {α : Type*} [Fintype α]
    (f : α → ℂ) (a : ℂ) :
    (∑ x, f x) * a = ∑ x, f x * a := by
  classical
  exact Finset.sum_mul Finset.univ f a

private theorem c3Pair_sum_neg_scalar_left_right {n : ℕ}
    (a t : ℂ) (f : Fin n → ℂ) :
    a * ((-(∑ l, f l)) * t) = ∑ l, -((a * f l) * t) := by
  rw [← mul_assoc, mul_neg, neg_mul, c3Pair_fintype_mul_sum,
    c3Pair_fintype_sum_mul, ← Finset.sum_neg_distrib]

private theorem c3Pair_sum4_congr {n : ℕ}
    (f g : Fin n → Fin n → Fin n → Fin n → ℂ)
    (h : ∀ a b c d, f a b c d = g a b c d) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ a, ∑ b, ∑ c, ∑ d, g a b c d := by
  classical
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  exact h a b c d

private theorem c3RicciTensorAction_eq_barChristoffel_contraction
    {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (T : Fin n → Fin n → Fin n → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (i j k : Fin n)
    (hbar : ∀ a b c q,
      chartPartialBarComplex
          (fun w => christoffelInChart g w a b c) z q =
        -(∑ l, (g z)⁻¹ l a * chartCurvature g z b q c l)) :
    (∑ p, ∑ q, (g z)⁻¹ q p *
      ((∑ r, chartPartialBarComplex
        (fun w => christoffelInChart g w i p r) z q * T r j k) -
       (∑ r, chartPartialBarComplex
        (fun w => christoffelInChart g w r p j) z q * T i r k) -
       ∑ r, chartPartialBarComplex
        (fun w => christoffelInChart g w r p k) z q * T i j r)) =
      c3RicciTensorAction g T z i j k := by
  classical
  simp_rw [hbar]
  unfold c3RicciTensorAction c3RicciEndomorphism c3RicciInChart
  simp only [mul_sub, c3Pair_fintype_mul_sum, c3Pair_fintype_sum_mul,
    Finset.sum_sub_distrib]
  simp_rw [c3Pair_sum_neg_scalar_left_right]
  simp only [Finset.sum_neg_distrib]
  rw [c3Pair_sum4_reorder_fin
      (fun p q r l => (g z)⁻¹ q p *
        ((g z)⁻¹ l i * chartCurvature g z p q r l) * T r j k),
    c3Pair_sum4_reorder_fin
      (fun p q r l => (g z)⁻¹ q p *
        ((g z)⁻¹ l r * chartCurvature g z p q j l) * T i r k),
    c3Pair_sum4_reorder_fin
      (fun p q r l => (g z)⁻¹ q p *
        ((g z)⁻¹ l r * chartCurvature g z p q k l) * T i j r)]
  have hUpper :
      (∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        (g z)⁻¹ b a * ((g z)⁻¹ d i * chartCurvature g z a b c d) * T c j k) =
      ∑ x : Fin n, ∑ x1 : Fin n, ∑ x2 : Fin n, ∑ x3 : Fin n,
        (g z)⁻¹ x1 i * ((g z)⁻¹ x3 x2 * chartCurvature g z x2 x3 x x1) * T x j k := by
    apply c3Pair_sum4_congr
    intro c d a b
    ring
  have hLowerJ :
      (∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        (g z)⁻¹ b a * ((g z)⁻¹ d c * chartCurvature g z a b j d) * T i c k) =
      ∑ x : Fin n, ∑ x1 : Fin n, ∑ x2 : Fin n, ∑ x3 : Fin n,
        (g z)⁻¹ x1 x * ((g z)⁻¹ x3 x2 * chartCurvature g z x2 x3 j x1) * T i x k := by
    apply c3Pair_sum4_congr
    intro c d a b
    ring
  have hLowerK :
      (∑ c : Fin n, ∑ d : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        (g z)⁻¹ b a * ((g z)⁻¹ d c * chartCurvature g z a b k d) * T i j c) =
      ∑ x : Fin n, ∑ x1 : Fin n, ∑ x2 : Fin n, ∑ x3 : Fin n,
        (g z)⁻¹ x1 x * ((g z)⁻¹ x3 x2 * chartCurvature g z x2 x3 k x1) * T i j x := by
    apply c3Pair_sum4_congr
    intro c d a b
    ring
  rw [← hUpper, ← hLowerJ, ← hLowerK]
  ring

private theorem c3Ricci_det_contDiffAt
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hA : ContDiffAt ℝ ∞ A z) :
    ContDiffAt ℝ ∞ (fun w => (A w).det) z := by
  have hentry (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => A w a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hA a) b
  have hpoly : ContDiffAt ℝ ∞
      (fun w => ∑ σ : Equiv.Perm (Fin n),
        Equiv.Perm.sign σ • ∏ i, A w (σ i) i) z := by
    fun_prop (disch := assumption)
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [Filter.univ_mem] with w hw
  exact Matrix.det_apply (A w)

private theorem c3Ricci_adjugate_entry_contDiffAt
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hA : ContDiffAt ℝ ∞ A z) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w => (A w).adjugate i j) z := by
  have hentry (a b : Fin n) : ContDiffAt ℝ ∞ (fun w => A w a b) z :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hA a) b
  have hpoly : ContDiffAt ℝ ∞
      (fun w => ((A w).updateRow j (Pi.single i 1)).det) z := by
    have hupdate (a b : Fin n) : ContDiffAt ℝ ∞
        (fun w => (A w).updateRow j (Pi.single i 1) a b) z := by
      by_cases ha : a = j
      · subst a
        simp only [Matrix.updateRow_apply]
        exact contDiffAt_const
      · simp only [Matrix.updateRow_apply, if_neg ha]
        exact hentry a b
    have hmatrix : ContDiffAt ℝ ∞
        (fun w => (A w).updateRow j (Pi.single i 1)) z := by
      apply contDiffAt_pi.mpr
      intro a
      apply contDiffAt_pi.mpr
      intro b
      exact hupdate a b
    exact c3Ricci_det_contDiffAt _ z hmatrix
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [Filter.univ_mem] with w hw
  exact Matrix.adjugate_apply (A w) i j

private theorem c3Ricci_inverse_entry_contDiffAt
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hA : ContDiffAt ℝ ∞ A z) (hunit : IsUnit (A z).det) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w => (A w)⁻¹ i j) z := by
  have hdet := c3Ricci_det_contDiffAt A z hA
  have hinvdet : ContDiffAt ℝ ∞ (fun w => ((A w).det)⁻¹) z := by
    have hnz : (A z).det ≠ 0 := hunit.ne_zero
    exact (contDiffAt_inv ℝ hnz).comp z hdet
  have hadj := c3Ricci_adjugate_entry_contDiffAt A z hA i j
  have hentry : ContDiffAt ℝ ∞
      (fun w => ((A w).det)⁻¹ * (A w).adjugate i j) z := hinvdet.mul hadj
  apply hentry.congr_of_eventuallyEq
  filter_upwards [Filter.univ_mem] with w
  rw [Matrix.inv_def]
  simp [Matrix.smul_apply]

theorem c3ConnectionTensorLaplacian_commutator (ω₀ : KahlerForm n M)
    {φ : M → ℝ} (hφ : ω₀.IsPotential φ) (x : M) :
    c3OppositeConnectionTensorLaplacian ω₀ φ x
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) =
      fun i j k ↦
        c3ConnectionTensorLaplacian ω₀ φ x
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) i j k +
          c3RicciTensorAction (c3PerturbedMetricInChart ω₀ φ x)
            (connectionDifferenceInChart ω₀ φ x
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x))
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x) i j k := by
  classical
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let U := e.target
  let z := e x
  let g := c3PerturbedMetricInChart ω₀ φ x
  let T := connectionDifferenceInChart ω₀ φ x
  funext i j k
  have hz : z ∈ U := by
    dsimp [z, U, e]
    exact mem_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x
  have hGamma (a b c : Fin n) :
      ContDiffAt ℝ ∞ (fun w => christoffelInChart g w a b c) z := by
    let ωφ := ω₀.perturb φ hφ
    let gφ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
      fun w => ω₀.metricInChart x w + complexHessian (φ ∘ e.symm) w
    have hU : IsOpen U := isOpen_extChartAt_target x
    have heq : Set.EqOn gφ (fun w => ωφ.metricInChart x w) U := by
      intro w hw
      simpa [gφ, e, ωφ] using (ω₀.metricInChart_perturb hφ x hw).symm
    have hG : ∀ a b, ContDiffOn ℝ ∞ (fun w => gφ w a b) U := by
      intro a b
      exact (ωφ.contDiffOn_metricInChart x a b).congr
        (fun w hw => congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A a b) (heq hw))
    have hUnit : ∀ w ∈ U, IsUnit (gφ w) := by
      intro w hw
      have hu := (ωφ.posDef_metricInChart x hw).isUnit
      have heq' : gφ w = ωφ.metricInChart x w := heq hw
      rw [heq']
      exact hu
    have hGAt : ContDiffAt ℝ ∞ gφ z := by
      apply contDiffAt_pi.mpr
      intro a'
      apply contDiffAt_pi.mpr
      intro b'
      exact (hG a' b').contDiffAt (hU.mem_nhds hz)
    have hdet : IsUnit (gφ z).det := by
      rw [heq hz]
      exact (Matrix.isUnit_iff_isUnit_det (A := ωφ.metricInChart x z)).mp
        (ωφ.posDef_metricInChart x hz).isUnit
    have hGammaAt : ContDiffAt ℝ ∞
        (fun w => christoffelInChart gφ w a b c) z := by
      have hinv (l : Fin n) : ContDiffAt ℝ ∞
          (fun w => (gφ w)⁻¹ l a) z :=
        c3Ricci_inverse_entry_contDiffAt gφ z hGAt hdet l a
      have hpart (l : Fin n) : ContDiffAt ℝ ∞
          (fun w => chartPartialZComplex (fun v => gφ v c l) w b) z := by
        have hmetric := (hG c l).contDiffAt (hU.mem_nhds hz)
        have hfd : ContDiffAt ℝ ∞
            (fderiv ℝ (fun v => gφ v c l)) z := hmetric.fderiv_right (by simp)
        unfold chartPartialZComplex
        fun_prop (disch := assumption)
      unfold christoffelInChart
      apply ContDiffAt.sum
      intro l hl
      have hpartial : ContDiffAt ℝ ∞
          (fun w => wirtingerDerivInChart (fun v => gφ v c l) w b) z := by
        change ContDiffAt ℝ ∞
          (fun w => chartPartialZComplex (fun v => gφ v c l) w b) z
        exact hpart l
      exact (hinv l).mul hpartial
    change ContDiffAt ℝ ∞ (fun w => christoffelInChart g w a b c) z
    exact hGammaAt
  have hT (a b c : Fin n) :
      ContDiffAt ℝ ∞ (fun w => T w a b c) z :=
    c3ConnectionDifference_contDiffAt ω₀ φ hφ x z hz a b c
  have hbar : ∀ a b c q,
      chartPartialBarComplex
          (fun w => christoffelInChart g w a b c) z q =
        -(∑ l, (g z)⁻¹ l a * chartCurvature g z b q c l) := by
    intro a b c q
    exact c3PerturbedMetric_barChristoffel ω₀ φ hφ x z hz a b c q
  have haction := c3RicciTensorAction_eq_barChristoffel_contraction
    g (T z) z i j k hbar
  have hcomm (p q : Fin n) :=
    c3TensorCovariantZ_bar_commutator g T z p q i j k hT hGamma
  let C : Fin n → Fin n → ℂ := fun p q =>
    (∑ r, chartPartialBarComplex
      (fun w => christoffelInChart g w i p r) z q * T z r j k) -
    (∑ r, chartPartialBarComplex
      (fun w => christoffelInChart g w r p j) z q * T z i r k) -
    ∑ r, chartPartialBarComplex
      (fun w => christoffelInChart g w r p k) z q * T z i j r
  have hcomm' (p q : Fin n) :
      chartPartialBarComplex (fun w => c3TensorCovariantZ g T w p i j k) z q =
        c3TensorCovariantZ g
          (fun w a b c => c3PartialBar (fun v => T v a b c) w q)
          z p i j k + C p q := by
    calc
      _ = c3TensorCovariantZ g
            (fun w a b c => c3PartialBar (fun v => T v a b c) w q)
            z p i j k +
          (∑ r, chartPartialBarComplex
            (fun w => christoffelInChart g w i p r) z q * T z r j k) -
          (∑ r, chartPartialBarComplex
            (fun w => christoffelInChart g w r p j) z q * T z i r k) -
          ∑ r, chartPartialBarComplex
            (fun w => christoffelInChart g w r p k) z q * T z i j r := hcomm p q
      _ = _ := by simp [C]; ring
  have hcontract : (∑ p, ∑ q, (g z)⁻¹ q p * C p q) =
      c3RicciTensorAction g (T z) z i j k := by
    exact haction
  change (∑ p, ∑ q, (g z)⁻¹ q p *
      chartPartialBarComplex (fun w => c3TensorCovariantZ g T w p i j k) z q) =
    c3ConnectionTensorLaplacian ω₀ φ x z i j k +
      c3RicciTensorAction g (T z) z i j k
  calc
    _ = (∑ p, ∑ q, (g z)⁻¹ q p *
          c3TensorCovariantZ g
            (fun w a b c => c3PartialBar (fun v => T v a b c) w q)
            z p i j k) + c3RicciTensorAction g (T z) z i j k := by
      calc
        _ = ∑ p, ∑ q, (g z)⁻¹ q p *
            (c3TensorCovariantZ g
              (fun w a b c => c3PartialBar (fun v => T v a b c) w q)
              z p i j k + C p q) := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          rw [hcomm' p q]
        _ = (∑ p, ∑ q, (g z)⁻¹ q p *
              c3TensorCovariantZ g
                (fun w a b c => c3PartialBar (fun v => T v a b c) w q)
                z p i j k) + (∑ p, ∑ q, (g z)⁻¹ q p * C p q) := by
          simp_rw [mul_add]
          simp only [Finset.sum_add_distrib]
        _ = _ := by rw [hcontract]
    _ = _ := rfl

end KahlerForm
