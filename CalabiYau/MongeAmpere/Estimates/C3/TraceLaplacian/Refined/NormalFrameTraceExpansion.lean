module

public import CalabiYau.MongeAmpere.Estimates.C3.TraceLaplacian.Refined.ReferenceCurvatureError
import CalabiYau.MongeAmpere.Estimates.C2.RelativeTraceSecondJet
import CalabiYau.MongeAmpere.Estimates.C2.HermitianFirstJet

/-!
# Trace Hessian in a reference-normal frame

The matrix inverse differentiation identity of `TraceHessian`, specialized to
`g(z)=1` with `∂g(z)=0`, expands the perturbed trace Laplacian into mixed
entries of `h` and a signed reference-curvature contraction. Hermitian symmetry
near the center also kills `∂bar g(z)`; it is not inferred from `∂g(z)=0`
without this hypothesis. Source: Székelyhidi, *An Introduction to Extremal
Kähler Metrics*, §3.3, Lemma 3.10, pp. 45–46.
-/

@[expose] public section

open scoped BigOperators Manifold ContDiff NNReal ComplexOrder MatrixOrder Matrix.Norms.Elementwise
open ContinuousAlternatingMap
open Filter Topology

namespace KahlerForm

variable {n : ℕ}

private theorem c3RefinedTracePartialBar_star_partialZ_star
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (z : EuclideanSpace ℂ (Fin n)) (p : Fin n)
    (hf : DifferentiableAt ℝ f z) :
    c3RefinedTracePartialBar f z p =
      star (wirtingerDerivInChart (fun w ↦ star (f w)) z p) := by
  unfold c3RefinedTracePartialBar wirtingerDerivInChart
  let e := EuclideanSpace.single p (1 : ℂ)
  have hreal := hf.hasFDerivAt
  have hc := (Complex.conjCLE.hasFDerivAt (x := f z)).comp z hreal
  have hstar : fderiv ℝ (fun w ↦ star (f w)) z =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ f z) := by
    simpa [Function.comp_def, Complex.conjCLE_apply, Complex.star_def] using hc.fderiv
  rw [hstar]
  simp only [ContinuousLinearMap.comp_apply]
  simp [Complex.conj_I]

private theorem c3RefinedTrace_normalFrame_referenceBar_zero
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hFirst : ∀ i j p, wirtingerDerivInChart (fun w ↦ g w i j) z p = 0)
    (hHermitian : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, g w = (g w).conjTranspose) :
    ∀ i j p, c3RefinedTracePartialBar (fun w ↦ g w i j) z p = 0 := by
  obtain ⟨U, hU, hz, hHerm⟩ := hHermitian
  intro i j p
  have hlocal : (fun w ↦ star (g w i j)) =ᶠ[𝓝 z] (fun w ↦ g w j i) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hij : g w i j = star (g w j i) := by
      have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A i j) (hHerm w hw)
      simpa using h
    simpa using congrArg star hij
  have hderiv := hlocal.fderiv_eq (𝕜 := ℝ) (x := z)
  have hpartial : wirtingerDerivInChart (fun w ↦ star (g w i j)) z p =
      wirtingerDerivInChart (fun w ↦ g w j i) z p := by
    unfold wirtingerDerivInChart
    rw [hderiv]
  have hbar := c3RefinedTracePartialBar_star_partialZ_star
    (fun w ↦ g w i j) z p ((hg i j).differentiableAt (by norm_num))
  rw [hpartial, hFirst j i p] at hbar
  simpa using hbar

private theorem c3RefinedTrace_adjugate_entry_contDiff {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w ↦ g w a b) z)
    (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w ↦ (g w).adjugate i j) z := by
  have hentry (σ : Equiv.Perm (Fin n)) (k : Fin n) :
      ContDiffAt ℝ ∞
        (fun w ↦ (g w).updateRow j (Pi.single i (1 : ℂ)) (σ k) k) z := by
    by_cases h : σ k = j
    · simp [Matrix.updateRow_apply, h, Pi.single_apply]
      by_cases hk : k = i <;> simp [hk] <;> exact contDiffAt_const
    · simp [Matrix.updateRow_apply, h]
      exact hg (σ k) k
  rw [show (fun w ↦ (g w).adjugate i j) =
    (fun w ↦ ((g w).updateRow j (Pi.single i (1 : ℂ))).det) by
      funext w
      exact Matrix.adjugate_apply (g w) i j]
  simp_rw [Matrix.det_apply]
  fun_prop (disch := assumption)

private theorem c3RefinedTrace_inverse_entry_contDiff {n : ℕ}
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ a b, ContDiffAt ℝ ∞ (fun w ↦ g w a b) z)
    (hdet : (g z).det ≠ 0) (i j : Fin n) :
    ContDiffAt ℝ ∞ (fun w ↦ ((g w)⁻¹) i j) z := by
  have hdetfun : ContDiffAt ℝ ∞ (fun w ↦ (g w).det) z := by
    simp_rw [Matrix.det_apply]
    fun_prop (disch := assumption)
  have hdetinv : ContDiffAt ℝ ∞ (fun w ↦ ((g w).det)⁻¹) z :=
    (contDiffAt_inv ℝ hdet).comp z hdetfun
  have hadj := c3RefinedTrace_adjugate_entry_contDiff g z hg i j
  rw [show (fun w ↦ ((g w)⁻¹) i j) =
      (fun w ↦ ((g w).det)⁻¹ * (g w).adjugate i j) by
        funext w
        rw [Matrix.inv_def]
        simp]
  exact hdetinv.mul hadj

private theorem c3RefinedTrace_normalFrame_curvature_eq_neg_mixed
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hNormal : g z = 1)
    (hFirst : ∀ i j p, wirtingerDerivInChart (fun w ↦ g w i j) z p = 0)
    (hHermitian : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, g w = (g w).conjTranspose)
    (p j : Fin n) :
    c3RefinedTraceReferenceCurvatureInChart g z p p j j =
      -c3RefinedTraceMatrixMixedPartial g z p p j j := by
  have hbar := c3RefinedTrace_normalFrame_referenceBar_zero g z hg hFirst hHermitian
  have hdet : IsUnit (g z).det := by rw [hNormal]; simp
  have hbarGamma (a : Fin n) : c3RefinedTracePartialBar
      (fun w ↦ christoffelInChart g w a p j) z p =
      -(∑ l, (g z)⁻¹ l a * chartCurvature g z p p j l) := by
    have hcurv := chartChristoffel_bar_eq_curvature_at g z hg hdet a p j p
    simpa [c3RefinedTracePartialBar, christoffelInChart, wirtingerDerivInChart,
      chartPartialBarComplex, chartPartialZComplex] using hcurv
  unfold c3RefinedTraceReferenceCurvatureInChart
  rw [Finset.sum_congr rfl (fun a ha => by rw [hbarGamma a])]
  have hInv : (g z)⁻¹ = 1 := by rw [hNormal]; simp
  rw [hInv, hNormal]
  simp [Matrix.one_apply]
  unfold chartCurvature c3RefinedTraceMatrixMixedPartial
    c3RefinedTraceMatrixPartialZ c3RefinedTraceMatrixPartialBar
  rw [show chartPartialZComplex = wirtingerDerivInChart from rfl,
    show chartPartialBarComplex = c3RefinedTracePartialBar from rfl]
  simp [hFirst, hbar]

private theorem c3RefinedTrace_positiveDiagonal_inverse {lam : Fin n → ℝ}
    (hlam : ∀ j, 0 < lam j) :
    (Matrix.diagonal (fun j ↦ (lam j : ℂ)))⁻¹ =
      Matrix.diagonal (fun j ↦ ((lam j)⁻¹ : ℂ)) := by
  have hunit : IsUnit (fun k ↦ (lam k : ℂ)) := by
    rw [Pi.isUnit_iff]
    intro k
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt (hlam k))
  have hinv : Ring.inverse (fun k ↦ (lam k : ℂ)) =
      (fun k ↦ ((lam k)⁻¹ : ℂ)) := by
    funext j
    rw [Ring.inverse_of_isUnit hunit]
    simp [IsUnit.val_inv_apply hunit j]
  rw [Matrix.inv_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, hinv]

private theorem c3RefinedTrace_positiveDiagonal_inverse_trace
    (lam : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hlam : ∀ j, 0 < lam j) :
    RCLike.re ((Matrix.diagonal (fun j ↦ (lam j : ℂ)))⁻¹ * A).trace =
      ∑ j, RCLike.re (A j j) / lam j := by
  rw [c3RefinedTrace_positiveDiagonal_inverse hlam]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_eq_mul_inv]
  ring

private theorem c3RefinedTrace_realpart_complexWirtinger_eq_hessian
    (a : EuclideanSpace ℂ (Fin n) → ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (ha : ContDiffAt ℝ 2 a z) (p : Fin n) :
    (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar a w p) z p).re =
      (complexHessian (fun w ↦ (a w).re) z p p).re := by
  let ep : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single p 1
  have ha1 : ContDiffAt ℝ 1 (fderiv ℝ a) z := ha.fderiv_right (m := 1) (by norm_num)
  have hfdDiff : DifferentiableAt ℝ (fderiv ℝ a) z := ha1.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (fun w ↦ fderiv ℝ a w ep) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hB : DifferentiableAt ℝ (fun w ↦ fderiv ℝ a w (Complex.I • ep)) z :=
    hfdDiff.clm_apply (differentiableAt_const _)
  have hD (d q : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ a w q) z d = fderiv ℝ (fderiv ℝ a) z d q := by
    have h := fderiv_clm_apply (u := fun _ : EuclideanSpace ℂ (Fin n) ↦ q)
      hfdDiff (differentiableAt_const _)
    have h' := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) h
    simpa using h'
  have hAc (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ a w ep) z d = fderiv ℝ (fderiv ℝ a) z d ep :=
    hD d ep
  have hBc (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ fderiv ℝ a w (Complex.I • ep)) z d =
        fderiv ℝ (fderiv ℝ a) z d (Complex.I • ep) := hD d (Complex.I • ep)
  have hnum : DifferentiableAt ℝ
      (fun w ↦ fderiv ℝ a w ep + Complex.I * fderiv ℝ a w (Complex.I • ep)) z :=
    hA.add (hB.const_mul Complex.I)
  have hbar : (fun w ↦ c3RefinedTracePartialBar a w p) =
      fun w ↦ (2 : ℂ)⁻¹ *
        (fderiv ℝ a w ep + Complex.I * fderiv ℝ a w (Complex.I • ep)) := by
    funext w
    simp [c3RefinedTracePartialBar, ep, div_eq_mul_inv]
    ring
  have hpartial (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ c3RefinedTracePartialBar a w p) z d =
        (2 : ℂ)⁻¹ *
          (fderiv ℝ (fderiv ℝ a) z d ep +
            Complex.I * fderiv ℝ (fderiv ℝ a) z d (Complex.I • ep)) := by
    rw [hbar, fderiv_const_mul hnum (2 : ℂ)⁻¹,
      fderiv_fun_add hA (hB.const_mul Complex.I),
      fderiv_const_mul hB Complex.I]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hAc, hBc]
  have hq : ContDiffAt ℝ 2 (fun w ↦ (a w).re) z := by
    change ContDiffAt ℝ 2 (RCLike.re ∘ a) z
    exact (RCLike.reCLM.contDiff.contDiffAt.comp z ha)
  change RCLike.re (chartPartialZComplex
      (fun w ↦ chartPartialBarComplex a w p) z p) = _
  unfold chartPartialZComplex
  rw [show chartPartialBarComplex = c3RefinedTracePartialBar from rfl]
  rw [hpartial ep, hpartial (Complex.I • ep), complexHessian_apply hq p p]
  simp only [div_eq_mul_inv]
  have hsymm := ha.isSymmSndFDerivAt (by norm_num [minSmoothness])
  have hsymm₁ : fderiv ℝ (fderiv ℝ a) z ep (Complex.I • ep) =
      fderiv ℝ (fderiv ℝ a) z (Complex.I • ep) ep := hsymm _ _
  have hRe (d e : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fderiv ℝ (fun w ↦ (a w).re)) z d e =
        (fderiv ℝ (fderiv ℝ a) z d e).re := by
    let L : ℂ →L[ℝ] ℝ := RCLike.reCLM
    have hiter := L.iteratedFDeriv_comp_left (f := a) ha (i := 2) (by norm_num)
    have hEval := congrArg (fun T ↦ T ![d, e]) hiter
    have hL : iteratedFDeriv ℝ 2 (fun w ↦ (a w).re) z ![d, e] =
        fderiv ℝ (fderiv ℝ (fun w ↦ (a w).re)) z d e := by
      rw [iteratedFDeriv_two_apply]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hR : iteratedFDeriv ℝ 2 a z ![d, e] =
        fderiv ℝ (fderiv ℝ a) z d e := by
      rw [iteratedFDeriv_two_apply]
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hcomp : iteratedFDeriv ℝ 2 (fun w ↦ (a w).re) z ![d, e] =
        (iteratedFDeriv ℝ 2 a z ![d, e]).re := by
      have h := hEval
      simp [L, Function.comp_def] at h
      exact h
    rw [← hL, hcomp, hR]
  rw [hRe ep ep, hRe (Complex.I • ep) (Complex.I • ep),
    hRe ep (Complex.I • ep), hRe (Complex.I • ep) ep, hsymm₁]
  simp [Complex.I_re, Complex.mul_re]
  ring

private theorem c3RefinedTrace_contDiffAt_relativeTraceMatrix
    (G₀ G₁ : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hG₀ : ∀ j k, ContDiffAt ℝ ∞ (fun w ↦ G₀ w j k) z)
    (hG₁ : ∀ j k, ContDiffAt ℝ ∞ (fun w ↦ G₁ w j k) z)
    (hId : G₀ z = 1) :
    ContDiffAt ℝ 2 (fun w ↦ (((G₀ w)⁻¹ * G₁ w).trace)) z := by
  let H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun w ↦ (G₀ w)⁻¹
  let term : Fin n → Fin n → EuclideanSpace ℂ (Fin n) → ℂ :=
    fun j k w ↦ H w j k * G₁ w k j
  have hdet : (G₀ z).det ≠ 0 := by simp [hId]
  have hle : (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.2 (by norm_num : (2 : ℕ∞) ≤ ⊤)
  have hHentry (j k : Fin n) : ContDiffAt ℝ 2 (fun w ↦ H w j k) z := by
    exact (c3RefinedTrace_inverse_entry_contDiff G₀ z hG₀ hdet j k).of_le hle
  have hG₁entry (j k : Fin n) : ContDiffAt ℝ 2 (fun w ↦ G₁ w j k) z :=
    (hG₁ j k).of_le (WithTop.coe_le_coe.mpr
      (le_top : (2 : ℕ∞) ≤ ⊤))
  have hterm (j k : Fin n) : ContDiffAt ℝ 2 (term j k) z :=
    (hHentry j k).mul (hG₁entry k j)
  have hInner (j : Fin n) :
      ContDiffAt ℝ 2 (fun w ↦ ∑ k ∈ Finset.univ, term j k w) z :=
    ContDiffAt.sum (fun k hk ↦ hterm j k)
  have hSum : ContDiffAt ℝ 2
      (fun w ↦ ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, term j k w) z :=
    ContDiffAt.sum (fun j hj ↦ hInner j)
  have htrace : (fun w ↦ (((G₀ w)⁻¹ * G₁ w).trace)) =
      fun w ↦ ∑ j ∈ Finset.univ, ∑ k ∈ Finset.univ, term j k w := by
    funext w
    simp [term, H, Matrix.trace, Matrix.mul_apply]
  rw [htrace]
  exact hSum

private theorem c3RefinedTrace_traceExpansion_jet
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ h w i j) z)
    (hNormal : g z = 1)
    (hFirst : ∀ i j p, wirtingerDerivInChart (fun w ↦ g w i j) z p = 0)
    (hDiagonal : h z = Matrix.diagonal (fun i ↦ (lam i : ℂ)))
    (hHermitian : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, g w = (g w).conjTranspose)
    (p : Fin n) :
    RCLike.re (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w p) z p) =
      (∑ j : Fin n,
        RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j)) -
      ∑ j : Fin n, lam j *
        RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j) := by
  have hG2 : ∀ i j, ContDiffAt ℝ 2 (fun w ↦ g w i j) z := by
    intro i j
    exact (hg i j).of_le (WithTop.coe_le_coe.mpr
      (le_top : (2 : ℕ∞) ≤ ⊤))
  have hH2 : ∀ i j, ContDiffAt ℝ 2 (fun w ↦ h w i j) z := by
    intro i j
    exact (hh i j).of_le (WithTop.coe_le_coe.mpr
      (le_top : (2 : ℕ∞) ≤ ⊤))
  have hGdiffAll : ContDiffAt ℝ 2 g z := by
    change ContDiffAt ℝ 2 (fun w i j ↦ g w i j) z
    rw [contDiffAt_pi]
    intro i
    rw [contDiffAt_pi]
    exact hG2 i
  have hHermNear : ∀ᶠ w in 𝓝 z, (g w).IsHermitian := by
    obtain ⟨U, hU, hz, hHerm⟩ := hHermitian
    filter_upwards [hU.mem_nhds hz] with w hw
    simpa [Matrix.IsHermitian] using (hHerm w hw).symm
  have hFirst' : ∀ p i j, chartPartialZComplex (fun w ↦ g w i j) z p = 0 := by
    intro p i j
    change wirtingerDerivInChart (fun w ↦ g w i j) z p = 0
    exact hFirst i j p
  have hFirstReal : fderiv ℝ g z = 0 :=
    Matrix.fderiv_eq_zero_of_eventually_isHermitian_of_partialZ_eq_zero
      g z (hGdiffAll.differentiableAt (by norm_num)) hHermNear hFirst'
  have hJet := complexHessian_relativeTraceMatrix_diag_of_normal
    g h z lam hG2 hH2 hNormal hDiagonal hFirstReal p
  have hTreg : ContDiffAt ℝ 2
      (fun w ↦ c3RefinedTraceRelativeMatrixTrace g h w) z := by
    exact c3RefinedTrace_contDiffAt_relativeTraceMatrix g h z hg hh hNormal
  have hWirtinger := c3RefinedTrace_realpart_complexWirtinger_eq_hessian
    (fun w ↦ c3RefinedTraceRelativeMatrixTrace g h w) z hTreg p
  have hJet' :
      RCLike.re (wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
        (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w p) z p) =
      (∑ j : Fin n,
        RCLike.re (chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ h v j j) w p) z p)) -
      ∑ j : Fin n, lam j *
        RCLike.re (chartPartialZComplex
          (fun w ↦ chartPartialBarComplex (fun v ↦ g v j j) w p) z p) := by
    calc
      _ = (complexHessian
          (fun w ↦ (c3RefinedTraceRelativeMatrixTrace g h w).re) z p p).re := by
        simpa [c3RefinedTraceRelativeMatrixTrace] using hWirtinger
      _ = _ := hJet
  simpa only [c3RefinedTraceMatrixMixedPartial, c3RefinedTraceMatrixPartialZ,
    c3RefinedTraceMatrixPartialBar,
    show chartPartialZComplex = wirtingerDerivInChart from rfl,
    show chartPartialBarComplex = c3RefinedTracePartialBar from rfl] using hJet'

/-- The normal-center specialization of the ordered inverse-matrix trace
Hessian, before using either Kähler symmetry or the determinant equation.
The first inverse eigenvalue belongs to the differentiation index `p`, while
the curvature multiplier carries the metric index `j`. -/
theorem c3RefinedTrace_normalFrame_traceExpansion
    (g h : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) (lam : Fin n → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ g w i j) z)
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun w ↦ h w i j) z)
    (hNormal : g z = 1)
    (hFirst : ∀ i j p, wirtingerDerivInChart (fun w ↦ g w i j) z p = 0)
    (hDiagonal : h z = Matrix.diagonal (fun i ↦ (lam i : ℂ)))
    (hPositive : ∀ i, 0 < lam i)
    (hHermitian : ∃ U : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen U ∧ z ∈ U ∧ ∀ w ∈ U, g w = (g w).conjTranspose) :
    RCLike.re (((h z)⁻¹ * Matrix.of (fun p q ↦
        wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
          (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w q) z p)).trace) =
      (∑ p : Fin n, ∑ j : Fin n,
        RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j) / lam p) +
      (∑ p : Fin n, ∑ j : Fin n,
        lam j / lam p *
          RCLike.re (c3RefinedTraceReferenceCurvatureInChart g z p p j j)) := by
  let traceJet : Fin n → ℂ := fun p ↦
    wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w p) z p
  let traceMatrix : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun p q ↦
    wirtingerDerivInChart (fun w ↦ c3RefinedTracePartialBar
      (fun v ↦ c3RefinedTraceRelativeMatrixTrace g h v) w q) z p)
  have htrace :
      RCLike.re (((h z)⁻¹ * traceMatrix).trace) =
        ∑ p, RCLike.re (traceMatrix p p) / lam p := by
    rw [hDiagonal]
    simpa [traceMatrix] using
      c3RefinedTrace_positiveDiagonal_inverse_trace lam traceMatrix hPositive
  have htrace' :
      RCLike.re (((h z)⁻¹ * traceMatrix).trace) =
        ∑ p, RCLike.re (traceJet p) / lam p := by
    calc
      _ = ∑ p, RCLike.re (traceMatrix p p) / lam p := htrace
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [traceMatrix, traceJet]
  have hjet (p : Fin n) : RCLike.re (traceJet p) =
      (∑ j : Fin n,
        RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j)) -
      ∑ j : Fin n, lam j *
        RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j) := by
    exact c3RefinedTrace_traceExpansion_jet g h z lam hg hh hNormal
      hFirst hDiagonal hHermitian p
  have hcurv (p j : Fin n) :
      RCLike.re (c3RefinedTraceReferenceCurvatureInChart g z p p j j) =
        -RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j) := by
    rw [c3RefinedTrace_normalFrame_curvature_eq_neg_mixed
      g z hg hNormal hFirst hHermitian p j]
    simp
  have hgcurv (p j : Fin n) :
      RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j) =
        -RCLike.re (c3RefinedTraceReferenceCurvatureInChart g z p p j j) := by
    linarith [hcurv p j]
  have hAlg (p : Fin n) :
      ((∑ j : Fin n,
        RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j)) -
       ∑ j : Fin n, lam j *
        RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j)) / lam p =
      (∑ j : Fin n,
        RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j) / lam p) +
      ∑ j : Fin n, lam j / lam p *
        RCLike.re (c3RefinedTraceReferenceCurvatureInChart g z p p j j) := by
    calc
      _ = (∑ j : Fin n,
          RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j) / lam p) +
        ∑ j : Fin n,
          -(lam j * RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j) / lam p) := by
        rw [sub_div, Finset.sum_div, Finset.sum_div, sub_eq_add_neg,
          ← Finset.sum_neg_distrib]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [hgcurv p j]
        ring
  calc
    _ = ∑ p : Fin n, RCLike.re (traceJet p) / lam p := htrace'
    _ = ∑ p : Fin n,
        ((∑ j : Fin n,
          RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j)) -
         ∑ j : Fin n, lam j *
          RCLike.re (c3RefinedTraceMatrixMixedPartial g z p p j j)) / lam p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hjet p]
    _ = ∑ p : Fin n,
        ((∑ j : Fin n,
          RCLike.re (c3RefinedTraceMatrixMixedPartial h z p p j j) / lam p) +
         ∑ j : Fin n, lam j / lam p *
          RCLike.re (c3RefinedTraceReferenceCurvatureInChart g z p p j j)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hAlg p
    _ = _ := by rw [Finset.sum_add_distrib]

end KahlerForm
