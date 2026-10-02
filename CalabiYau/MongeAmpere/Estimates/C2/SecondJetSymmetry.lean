module

public import CalabiYau.Geometry.Kahler.Curvature.Chart
import all CalabiYau.Geometry.Kahler.Curvature.Chart
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Star

public section

open scoped ContDiff Topology
open Filter

namespace KahlerForm

variable {n : ℕ}

private noncomputable def chartSecondJetWirtinger
    (s : ℂ) (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) : ℂ :=
  (fderiv ℝ F w (EuclideanSpace.single j 1) +
    s * fderiv ℝ F w (Complex.I • EuclideanSpace.single j 1)) / 2

private theorem chartSecondJetWirtinger_fderiv (s : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ 2 F z) (j : Fin n)
    (v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun w => chartSecondJetWirtinger s F w j) z v =
      (fderiv ℝ (fderiv ℝ F) z v (EuclideanSpace.single j 1) +
        s * fderiv ℝ (fderiv ℝ F) z v
          (Complex.I • EuclideanSpace.single j 1)) / 2 := by
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
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
  have hfun : (fun w => chartSecondJetWirtinger s F w j) =
      fun w => (2 : ℂ)⁻¹ * (fderiv ℝ F w e + s * fderiv ℝ F w (Complex.I • e)) := by
    funext w
    simp only [chartSecondJetWirtinger, e, div_eq_mul_inv]
    ring
  rw [hfun, fderiv_const_mul hsum, fderiv_fun_add he (hie.const_mul s),
    fderiv_const_mul hie]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [h_e v, h_ie v]
  simp only [div_eq_mul_inv]
  ring

private theorem chartSecondJetWirtinger_comm (s t : ℂ)
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ 2 F z) (p q : Fin n) :
    chartSecondJetWirtinger s (fun w => chartSecondJetWirtinger t F w q) z p =
      chartSecondJetWirtinger t (fun w => chartSecondJetWirtinger s F w p) z q := by
  have hs : IsSymmSndFDerivAt ℝ F z :=
    hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  change (fderiv ℝ (fun w => chartSecondJetWirtinger t F w q) z
      (EuclideanSpace.single p 1) +
    s * fderiv ℝ (fun w => chartSecondJetWirtinger t F w q) z
      (Complex.I • EuclideanSpace.single p 1)) / 2 =
    (fderiv ℝ (fun w => chartSecondJetWirtinger s F w p) z (EuclideanSpace.single q 1) +
      t * fderiv ℝ (fun w => chartSecondJetWirtinger s F w p) z
        (Complex.I • EuclideanSpace.single q 1)) / 2
  rw [chartSecondJetWirtinger_fderiv t F z hF q (EuclideanSpace.single p 1),
    chartSecondJetWirtinger_fderiv t F z hF q (Complex.I • EuclideanSpace.single p 1),
    chartSecondJetWirtinger_fderiv s F z hF p (EuclideanSpace.single q 1),
    chartSecondJetWirtinger_fderiv s F z hF p (Complex.I • EuclideanSpace.single q 1)]
  have h₁ := hs (EuclideanSpace.single p 1) (EuclideanSpace.single q 1)
  have h₂ := hs (EuclideanSpace.single p 1) (Complex.I • EuclideanSpace.single q 1)
  have h₃ := hs (Complex.I • EuclideanSpace.single p 1) (EuclideanSpace.single q 1)
  have h₄ := hs (Complex.I • EuclideanSpace.single p 1)
    (Complex.I • EuclideanSpace.single q 1)
  rw [h₁, h₂, h₃, h₄]
  ring

private theorem chartPartialBarComplex_eventuallyEq
    (F G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (h : F =ᶠ[nhds z] G) :
    (fun w => chartPartialBarComplex F w q) =ᶠ[nhds z]
      (fun w => chartPartialBarComplex G w q) := by
  have hfd : (fun w => fderiv ℝ F w) =ᶠ[nhds z] (fun w => fderiv ℝ G w) :=
    h.fderiv (𝕜 := ℝ)
  filter_upwards [hfd] with w hw
  unfold chartPartialBarComplex
  rw [hw]

private theorem chartPartialZComplex_eventuallyEq
    (F G : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n)
    (h : F =ᶠ[nhds z] G) :
    (fun w => chartPartialZComplex F w q) =ᶠ[nhds z]
      (fun w => chartPartialZComplex G w q) := by
  have hfd : (fun w => fderiv ℝ F w) =ᶠ[nhds z] (fun w => fderiv ℝ G w) :=
    h.fderiv (𝕜 := ℝ)
  filter_upwards [hfd] with w hw
  unfold chartPartialZComplex
  rw [hw]

private theorem chartPartialBarComplex_star
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (q : Fin n) :
    chartPartialBarComplex (fun w => star (F w)) z q =
      star (chartPartialZComplex F z q) := by
  unfold chartPartialBarComplex chartPartialZComplex
  rw [fderiv_star]
  simp only [ContinuousLinearMap.comp_apply]
  change (star ((fderiv ℝ F z) (EuclideanSpace.single q 1)) +
    Complex.I * star ((fderiv ℝ F z) (Complex.I • EuclideanSpace.single q 1))) / 2 = _
  simp [Complex.conj_I]

private theorem chartPartialBarComplex_commute_Z
    (F : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (hF : ContDiffAt ℝ 2 F z)
    (p q : Fin n) :
    chartPartialBarComplex (fun w => chartPartialZComplex F w p) z q =
      chartPartialZComplex (fun w => chartPartialBarComplex F w q) z p := by
  have hcomm := chartSecondJetWirtinger_comm (-Complex.I) Complex.I F z hF p q
  have hz (A : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      chartSecondJetWirtinger (-Complex.I) A w j = chartPartialZComplex A w j := by
    simp [chartSecondJetWirtinger, chartPartialZComplex, div_eq_mul_inv]
    ring
  have hb (A : EuclideanSpace ℂ (Fin n) → ℂ)
      (w : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
      chartSecondJetWirtinger Complex.I A w j = chartPartialBarComplex A w j := by
    rfl
  simpa only [hz, hb] using hcomm.symm

/-- For a Hermitian coefficient matrix satisfying the Kähler first-partial identity on a
neighborhood, the diagonal mixed complex-coordinate second derivatives agree in real part. -/
theorem diagonal_mixed_second_real_symmetric_of_partialZ_symmetry
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b : Fin n, ContDiffAt ℝ 2 (fun w ↦ g w a b) z)
    (hHermitian : ∀ᶠ w in 𝓝 z, (g w).IsHermitian)
    (hKahler : ∀ᶠ w in 𝓝 z, ∀ i j k : Fin n,
      chartPartialZComplex (fun v ↦ g v j k) w i =
        chartPartialZComplex (fun v ↦ g v i k) w j)
    (p j : Fin n) :
    (chartPartialZComplex
      (fun w ↦ chartPartialBarComplex (fun v ↦ g v j j) w p) z p).re =
    (chartPartialZComplex
      (fun w ↦ chartPartialBarComplex (fun v ↦ g v p p) w j) z j).re := by
  have hK₁ : (fun w ↦ chartPartialZComplex (fun v ↦ g v j j) w p) =ᶠ[𝓝 z]
      (fun w ↦ chartPartialZComplex (fun v ↦ g v p j) w j) := by
    filter_upwards [hKahler] with w hw
    exact hw p j j
  have hK₂ : (fun w ↦ chartPartialZComplex (fun v ↦ g v j p) w p) =ᶠ[𝓝 z]
      (fun w ↦ chartPartialZComplex (fun v ↦ g v p p) w j) := by
    filter_upwards [hKahler] with w hw
    exact hw p j p
  have hHerm₁ : (fun w ↦ star (g w j p)) =ᶠ[𝓝 z] (fun w ↦ g w p j) := by
    filter_upwards [hHermitian] with w hw
    exact hw.apply p j
  have hHerm₂ : (fun w ↦ star (g w p p)) =ᶠ[𝓝 z] (fun w ↦ g w p p) := by
    filter_upwards [hHermitian] with w hw
    exact hw.apply p p
  have hbarConj :
      (fun w ↦ chartPartialBarComplex (fun v ↦ star (g v j p)) w p) =ᶠ[𝓝 z]
      (fun w ↦ chartPartialBarComplex (fun v ↦ star (g v p p)) w j) := by
    filter_upwards [hK₂] with w hw
    calc
      chartPartialBarComplex (fun v ↦ star (g v j p)) w p =
          star (chartPartialZComplex (fun v ↦ g v j p) w p) :=
        chartPartialBarComplex_star (fun v ↦ g v j p) w p
      _ = star (chartPartialZComplex (fun v ↦ g v p p) w j) := congrArg star hw
      _ = chartPartialBarComplex (fun v ↦ star (g v p p)) w j :=
        (chartPartialBarComplex_star (fun v ↦ g v p p) w j).symm
  have hbar : (fun w ↦ chartPartialBarComplex (fun v ↦ g v p j) w p) =ᶠ[𝓝 z]
      (fun w ↦ chartPartialBarComplex (fun v ↦ g v p p) w j) := by
    have hleft := chartPartialBarComplex_eventuallyEq
      (fun w ↦ star (g w j p)) (fun w ↦ g w p j) z p hHerm₁
    have hright := chartPartialBarComplex_eventuallyEq
      (fun w ↦ star (g w p p)) (fun w ↦ g w p p) z j hHerm₂
    exact hleft.symm.trans (hbarConj.trans hright)
  have hfirst := chartPartialBarComplex_eventuallyEq
    (fun w ↦ chartPartialZComplex (fun v ↦ g v j j) w p)
    (fun w ↦ chartPartialZComplex (fun v ↦ g v p j) w j) z p hK₁
  have hlast := chartPartialZComplex_eventuallyEq
    (fun w ↦ chartPartialBarComplex (fun v ↦ g v p j) w p)
    (fun w ↦ chartPartialBarComplex (fun v ↦ g v p p) w j) z j hbar
  have hcomm₁ := chartPartialBarComplex_commute_Z
    (fun w ↦ g w j j) z (hg j j) p p
  have hcomm₂ := chartPartialBarComplex_commute_Z
    (fun w ↦ g w p j) z (hg p j) j p
  have hcomplex :
      chartPartialZComplex (fun w ↦ chartPartialBarComplex (fun v ↦ g v j j) w p) z p =
      chartPartialZComplex (fun w ↦ chartPartialBarComplex (fun v ↦ g v p p) w j) z j := by
    calc
      _ = chartPartialBarComplex
          (fun w ↦ chartPartialZComplex (fun v ↦ g v j j) w p) z p := hcomm₁.symm
      _ = chartPartialBarComplex
          (fun w ↦ chartPartialZComplex (fun v ↦ g v p j) w j) z p := hfirst.self_of_nhds
      _ = chartPartialZComplex (fun w ↦ chartPartialBarComplex (fun v ↦ g v p j) w p) z j :=
        hcomm₂
      _ = chartPartialZComplex (fun w ↦ chartPartialBarComplex (fun v ↦ g v p p) w j) z j :=
        hlast.self_of_nhds
  exact congrArg Complex.re hcomplex

end KahlerForm
