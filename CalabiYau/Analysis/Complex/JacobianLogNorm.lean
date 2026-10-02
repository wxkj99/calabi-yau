module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Basic

public section

open Filter
open scoped Topology

namespace Complex

/-- The Jacobian determinant is twice continuously differentiable over the reals when the map is
three times continuously differentiable and complex differentiable on a neighborhood. -/
private lemma jacobianDet_contDiffAt_real_two
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z : EuclideanSpace ℂ (Fin n)}
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w) :
    ContDiffAt ℝ 2
      (fun w => LinearMap.det (fderiv ℂ ψ w).toLinearMap) z := by
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let A : EuclideanSpace ℂ (Fin n) → Fin n → Fin n → ℂ :=
    fun w i j => (fderiv ℝ ψ w (b j)) i
  have hder : ContDiffAt ℝ 2 (fderiv ℝ ψ) z := by
    exact hψ.fderiv_right (by norm_num)
  have hA : ∀ i j, ContDiffAt ℝ 2 (fun w => A w i j) z := by
    intro i j
    have hcol : ContDiffAt ℝ 2 (fun w => fderiv ℝ ψ w (b j)) z := by
      exact hder.clm_apply contDiffAt_const
    simpa [A] using (contDiffAt_piLp 2).mp hcol i
  let D : EuclideanSpace ℂ (Fin n) → ℂ :=
    fun w => ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A w (σ i) i
  have hD : ContDiffAt ℝ 2 D z := by
    dsimp [D]
    fun_prop (disch := aesop)
  have hdet : (fun w => LinearMap.det (fderiv ℂ ψ w).toLinearMap) =ᶠ[𝓝 z] D := by
    filter_upwards [hψhol] with w hw
    rw [← LinearMap.det_toMatrix b, Matrix.det_apply]
    simp [D, A, b, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr,
      hw.fderiv_restrictScalars (𝕜 := ℝ)]
  exact hD.congr_of_eventuallyEq hdet

/-- On a complex affine line, the complex Jacobian determinant remains complex differentiable.
This is the bridge from a holomorphic map to its complex derivative. -/
private lemma fderiv_fderiv_complex_smul_left
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {w a b : EuclideanSpace ℂ (Fin n)}
    (hψ : ContDiffAt ℝ 3 ψ w)
    (hψhol : ∀ᶠ y in 𝓝 w, DifferentiableAt ℂ ψ y) :
    fderiv ℝ (fderiv ℝ ψ) w (Complex.I • a) b =
      Complex.I • fderiv ℝ (fderiv ℝ ψ) w a b := by
  have hD : DifferentiableAt ℝ (fderiv ℝ ψ) w :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun y : EuclideanSpace ℂ (Fin n) => fderiv ℝ ψ y (Complex.I • a)) =ᶠ[𝓝 w]
      (fun y => Complex.I • fderiv ℝ ψ y a) := by
    filter_upwards [hψhol] with y hy
    rw [hy.fderiv_restrictScalars (𝕜 := ℝ)]
    simp
  have hLeft : fderiv ℝ (fun y : EuclideanSpace ℂ (Fin n) =>
      fderiv ℝ ψ y (Complex.I • a)) w = (fderiv ℝ (fderiv ℝ ψ) w).flip (Complex.I • a) := by
    rw [fderiv_clm_apply hD (by fun_prop)]
    simp
  have hVa : fderiv ℝ (fun y : EuclideanSpace ℂ (Fin n) => fderiv ℝ ψ y a) w =
      (fderiv ℝ (fderiv ℝ ψ) w).flip a := by
    rw [fderiv_clm_apply hD (by fun_prop)]
    simp
  have hRight : fderiv ℝ (fun y : EuclideanSpace ℂ (Fin n) =>
      Complex.I • fderiv ℝ ψ y a) w = Complex.I • (fderiv ℝ (fderiv ℝ ψ) w).flip a := by
    rw [fderiv_fun_const_smul (by fun_prop) Complex.I, hVa]
  have hderiv := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) heq
  rw [hLeft, hRight] at hderiv
  have hval : fderiv ℝ (fderiv ℝ ψ) w b (Complex.I • a) =
      Complex.I • fderiv ℝ (fderiv ℝ ψ) w b a := by
    have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) => L b) hderiv
    simpa using h
  have hs := hψ.isSymmSndFDerivAt (by norm_num)
  calc
    fderiv ℝ (fderiv ℝ ψ) w (Complex.I • a) b =
        fderiv ℝ (fderiv ℝ ψ) w b (Complex.I • a) := hs.eq _ _
    _ = Complex.I • fderiv ℝ (fderiv ℝ ψ) w b a := hval
    _ = Complex.I • fderiv ℝ (fderiv ℝ ψ) w a b := by rw [hs.eq a b]

private lemma realLinearMap_map_smul_of_cr {ℓ : ℂ →ₗ[ℝ] ℂ}
    (h : ℓ Complex.I = Complex.I • ℓ 1) (a b : ℂ) :
    ℓ (a • b) = a • ℓ b := by
  rw [← Complex.re_add_im a, ← Complex.re_add_im b,
    ← smul_eq_mul _ Complex.I, ← smul_eq_mul _ Complex.I]
  have t₀ : ((a.im : ℂ) • Complex.I) • (b.re : ℂ) =
      (↑(a.im * b.re) : ℂ) • Complex.I := by
    simp only [smul_eq_mul, ofReal_mul, ← mul_assoc, mul_comm _ Complex.I]
  have t₁ : ((a.im : ℂ) • Complex.I) • (b.im : ℂ) • Complex.I =
      (↑(-a.im * b.im) : ℂ) • (1 : ℂ) := by
    simp [mul_mul_mul_comm _ Complex.I]
  simp only [add_smul, smul_add, ℓ.map_add, t₀, t₁]
  repeat rw [Complex.coe_smul, ℓ.map_smul]
  have t₂ {r : ℝ} : ℓ (r : ℂ) = r • ℓ (1 : ℂ) := by simp [← ℓ.map_smul]
  simp only [t₂, h]
  match_scalars
  simp [mul_mul_mul_comm _ Complex.I]
  ring

private lemma differentiableAt_complex_of_real_fderiv_cr
    {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z)
    (hcr : fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1) :
    DifferentiableAt ℂ f z := by
  let L : ℂ →ₗ[ℂ] ℂ := {
    toFun := fderiv ℝ f z
    map_add' := (fderiv ℝ f z).map_add
    map_smul' := realLinearMap_map_smul_of_cr hcr
  }
  let Lc : ℂ →L[ℂ] ℂ := {
    toLinearMap := L
    cont := (fderiv ℝ f z).continuous
  }
  have hL : Lc.restrictScalars ℝ = fderiv ℝ f z := by
    ext c
    rfl
  exact (hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt hL).differentiableAt

private lemma jacobianEntry_real_coordinate_cr_at
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {w u : EuclideanSpace ℂ (Fin n)}
    (hψ : ContDiffAt ℝ 3 ψ w)
    (hψhol : ∀ᶠ y in 𝓝 w, DifferentiableAt ℂ ψ y)
    (i j : Fin n) :
    fderiv ℝ (fun y : EuclideanSpace ℂ (Fin n) =>
      (fderiv ℝ ψ y ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j)) i) w
        (Complex.I • u) = Complex.I * fderiv ℝ (fun y : EuclideanSpace ℂ (Fin n) =>
      (fderiv ℝ ψ y ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j)) i) w u := by
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis j
  let V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
    fun y => fderiv ℝ ψ y b
  let π : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
  let Q : EuclideanSpace ℂ (Fin n) → ℂ := fun y => π (V y)
  have hD : ContDiffAt ℝ 2 (fderiv ℝ ψ) w :=
    hψ.fderiv_right (m := 2) (by norm_num)
  have hDdiff : DifferentiableAt ℝ (fderiv ℝ ψ) w :=
    hD.differentiableAt (by norm_num)
  have hV : DifferentiableAt ℝ V w := by
    exact (hD.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hVderiv : fderiv ℝ V w = (fderiv ℝ (fderiv ℝ ψ) w).flip b := by
    change fderiv ℝ (fun y => fderiv ℝ ψ y b) w = _
    rw [fderiv_clm_apply hDdiff (by fun_prop)]
    simp
  have hQderiv : fderiv ℝ Q w = π.comp (fderiv ℝ V w) := by
    change fderiv ℝ (π ∘ V) w = _
    rw [fderiv_comp w π.differentiableAt hV, ContinuousLinearMap.fderiv]
  change fderiv ℝ Q w (Complex.I • u) = Complex.I * fderiv ℝ Q w u
  rw [hQderiv, hVderiv]
  change π ((fderiv ℝ (fderiv ℝ ψ) w (Complex.I • u)) b) =
    Complex.I * π ((fderiv ℝ (fderiv ℝ ψ) w u) b)
  rw [fderiv_fderiv_complex_smul_left (a := u) (b := b) hψ hψhol]
  simp [π]

private lemma jacobianEntry_realLine_cr
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z u : EuclideanSpace ℂ (Fin n)}
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w)
    (i j : Fin n) :
    ∀ᶠ t in 𝓝 (0 : ℂ),
      fderiv ℝ (fun s : ℂ =>
        (fderiv ℝ ψ (z + s • u) ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j)) i)
          t Complex.I = Complex.I * fderiv ℝ (fun s : ℂ =>
        (fderiv ℝ ψ (z + s • u) ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j)) i)
          t 1 := by
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis j
  let L : ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (ContinuousLinearMap.id ℝ ℂ).smulRight u
  let P : ℂ → EuclideanSpace ℂ (Fin n) := fun t => z + L t
  let π : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
  let V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
    fun w => fderiv ℝ ψ w b
  let Q : EuclideanSpace ℂ (Fin n) → ℂ := fun w => π (V w)
  let q : ℂ → ℂ := fun s => (fderiv ℝ ψ (z + s • u) b) i
  have hPcontinuous : Continuous P := by fun_prop
  have hT : Tendsto P (𝓝 (0 : ℂ)) (𝓝 z) := by
    have hP0 : P 0 = z := by simp [P, L, ContinuousLinearMap.smulRight_apply]
    simpa [hP0] using (hPcontinuous.continuousAt (x := 0)).tendsto
  have hUmem : {w : EuclideanSpace ℂ (Fin n) | DifferentiableAt ℂ ψ w} ∈ 𝓝 z := hψhol
  obtain ⟨U, hzU, hUopen, hUsub⟩ := mem_nhds_iff.mp hUmem
  have hUline : ∀ᶠ t in 𝓝 (0 : ℂ), P t ∈ U := hT (hUopen.mem_nhds hUsub)
  have hψline : ∀ᶠ t in 𝓝 (0 : ℂ), ContDiffAt ℝ 3 ψ (P t) :=
    hT (hψ.eventually (by simp))
  filter_upwards [hUline, hψline] with t htU htψ
  have hholAt : ∀ᶠ y in 𝓝 (P t), DifferentiableAt ℂ ψ y := by
    filter_upwards [hUopen.mem_nhds htU] with y hy
    exact hzU hy
  have hD : ContDiffAt ℝ 2 (fderiv ℝ ψ) (P t) :=
    htψ.fderiv_right (m := 2) (by norm_num)
  have hV : ContDiffAt ℝ 2 V (P t) := by
    exact hD.clm_apply contDiffAt_const
  have hQ : ContDiffAt ℝ 2 Q (P t) := by
    change ContDiffAt ℝ 2 (fun w => π (V w)) (P t)
    exact (contDiffAt_const : ContDiffAt ℝ 2
      (fun _ : EuclideanSpace ℂ (Fin n) => π) (P t)).clm_apply hV
  have hQdiff : DifferentiableAt ℝ Q (P t) := hQ.differentiableAt (by norm_num)
  have hPdiff : DifferentiableAt ℝ P t := by fun_prop
  have hPderiv : fderiv ℝ P t = L := by
    simp [P, fderiv_const_add, ContinuousLinearMap.fderiv]
  have hCR := jacobianEntry_real_coordinate_cr_at (u := u) htψ hholAt i j
  have hq : q = Q ∘ P := by
    funext s
    simp [q, Q, V, π, P, L, b, ContinuousLinearMap.smulRight_apply]
  change fderiv ℝ q t Complex.I = Complex.I * fderiv ℝ q t 1
  rw [hq, fderiv_comp t hQdiff hPdiff, hPderiv]
  simpa [Q, V, π, b, L, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.coe_proj] using hCR

private lemma jacobianEntry_complexLine_differentiableAt
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z u : EuclideanSpace ℂ (Fin n)}
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w)
    (i j : Fin n) :
    ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableAt ℂ
      (fun s : ℂ => (fderiv ℂ ψ (z + s • u) ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis j)) i) t := by
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis j
  let L : ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (ContinuousLinearMap.id ℝ ℂ).smulRight u
  let P : ℂ → EuclideanSpace ℂ (Fin n) := fun t => z + L t
  let π : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
  let V : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) :=
    fun w => fderiv ℝ ψ w b
  let Q : EuclideanSpace ℂ (Fin n) → ℂ := fun w => π (V w)
  let qR : ℂ → ℂ := fun t => (fderiv ℝ ψ (P t) b) i
  let qC : ℂ → ℂ := fun t => (fderiv ℂ ψ (P t) b) i
  have hPcontinuous : Continuous P := by fun_prop
  have hT : Tendsto P (𝓝 (0 : ℂ)) (𝓝 z) := by
    have hP0 : P 0 = z := by simp [P, L, ContinuousLinearMap.smulRight_apply]
    simpa [hP0] using (hPcontinuous.continuousAt (x := 0)).tendsto
  have hUmem : {w : EuclideanSpace ℂ (Fin n) | DifferentiableAt ℂ ψ w} ∈ 𝓝 z := hψhol
  obtain ⟨U, hzU, hUopen, hUsub⟩ := mem_nhds_iff.mp hUmem
  have hUline : ∀ᶠ t in 𝓝 (0 : ℂ), P t ∈ U := hT (hUopen.mem_nhds hUsub)
  have hψline : ∀ᶠ t in 𝓝 (0 : ℂ), ContDiffAt ℝ 3 ψ (P t) :=
    hT (hψ.eventually (by simp))
  have hCRline := jacobianEntry_realLine_cr (u := u) hψ hψhol i j
  filter_upwards [hUline, hψline, hCRline] with t htU htψ hcr
  have hD : ContDiffAt ℝ 2 (fderiv ℝ ψ) (P t) :=
    htψ.fderiv_right (m := 2) (by norm_num)
  have hV : ContDiffAt ℝ 2 V (P t) := hD.clm_apply contDiffAt_const
  have hQ : ContDiffAt ℝ 2 Q (P t) := by
    change ContDiffAt ℝ 2 (fun w => π (V w)) (P t)
    exact (contDiffAt_const : ContDiffAt ℝ 2
      (fun _ : EuclideanSpace ℂ (Fin n) => π) (P t)).clm_apply hV
  have hQdiff : DifferentiableAt ℝ Q (P t) := hQ.differentiableAt (by norm_num)
  have hPdiff : DifferentiableAt ℝ P t := by fun_prop
  have hqR : DifferentiableAt ℝ qR t := by
    have hq : qR = Q ∘ P := by
      funext s
      simp [qR, Q, V, π, P, L, b, ContinuousLinearMap.smulRight_apply]
    rw [hq]
    exact hQdiff.comp t hPdiff
  have hqHol : DifferentiableAt ℂ qR t :=
    differentiableAt_complex_of_real_fderiv_cr hqR hcr
  have hPpre : P ⁻¹' U ∈ 𝓝 t :=
    hPcontinuous.continuousAt.preimage_mem_nhds (hUopen.mem_nhds htU)
  have hEq : qC =ᶠ[𝓝 t] qR := by
    filter_upwards [hPpre] with s hs
    have hsψ := hzU hs
    simp only [qC, qR]
    rw [hsψ.fderiv_restrictScalars (𝕜 := ℝ)]
    simp
  simpa [qC, b, EuclideanSpace.basisFun_apply, P, L,
    ContinuousLinearMap.smulRight_apply] using hqHol.congr_of_eventuallyEq hEq

private lemma jacobianDet_complexLine_differentiableAt
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z u : EuclideanSpace ℂ (Fin n)}
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w) :
    ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableAt ℂ
      (fun s : ℂ => LinearMap.det (fderiv ℂ ψ (z + s • u)).toLinearMap) t := by
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let A : ℂ → Fin n → Fin n → ℂ :=
    fun s i j => (fderiv ℂ ψ (z + s • u) (b j)) i
  let D : ℂ → ℂ :=
    fun s => ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A s (σ i) i
  have hentries : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i j, DifferentiableAt ℂ (fun s => A s i j) t := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    simpa [A, b] using jacobianEntry_complexLine_differentiableAt hψ hψhol i j
  have hD : ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableAt ℂ D t := by
    filter_upwards [hentries] with t ht
    dsimp [D]
    fun_prop (disch := aesop)
  have hEq : (fun s : ℂ => LinearMap.det (fderiv ℂ ψ (z + s • u)).toLinearMap) = D := by
    funext s
    rw [← LinearMap.det_toMatrix b, Matrix.det_apply]
    simp [D, A, b, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr]
  rw [hEq]
  exact hD

/-- The scalar log norm squared of a nonvanishing complex-differentiable function is harmonic at
the base point of a complex line. -/
private lemma log_normSq_complexLine_laplacian
    {g : ℂ → ℂ} {z : ℂ}
    (hgHol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ g w)
    (hgz : g z ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun w => Real.log (Complex.normSq (g w)))) z Complex.I Complex.I +
      fderiv ℝ (fderiv ℝ (fun w => Real.log (Complex.normSq (g w)))) z 1 1 = 0 := by
  have hgAnalytic : AnalyticAt ℂ g z :=
    (analyticAt_iff_eventually_differentiableAt).2 hgHol
  have hharm := hgAnalytic.harmonicAt_log_norm hgz
  have hEq : (fun w => Real.log (Complex.normSq (g w))) =
      (2 : ℝ) • (fun w => Real.log ‖g w‖) := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_eq_norm_sq]
    rw [Real.log_pow]
    norm_num
  have hq : InnerProductSpace.HarmonicAt
      (fun w => Real.log (Complex.normSq (g w))) z := by
    rw [hEq]
    exact hharm.const_smul
  have hzero := hq.2.eq_of_nhds
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at hzero
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply, add_comm] at hzero
  exact hzero

/-- A symmetric real bilinear form whose diagonal is invariant under the complex structure has the
`J`-invariant mixed Hessian identity. -/
private lemma j_invariant_of_hessian_diagonal
    {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x)
    (hdiag : ∀ x, B (Complex.I • x) (Complex.I • x) + B x x = 0)
    (u v : E) :
    B (Complex.I • u) v = B u (Complex.I • v) := by
  have hcross (x y : E) : B (Complex.I • x) (Complex.I • y) + B x y = 0 := by
    have h := hdiag (x + y)
    rw [smul_add] at h
    simp only [map_add, LinearMap.add_apply] at h
    rw [hB (Complex.I • x) (Complex.I • y), hB x y] at h
    have hx := hdiag x
    have hy := hdiag y
    rw [hB (Complex.I • x) (Complex.I • y), hB x y]
    linarith
  have h := hcross u (Complex.I • v)
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at h
  linarith

private lemma jacobianLogNorm_contDiffAt_real_two
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z : EuclideanSpace ℂ (Fin n)}
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w)
    (hdet : LinearMap.det (fderiv ℂ ψ z).toLinearMap ≠ 0) :
    ContDiffAt ℝ 2
      (fun w : EuclideanSpace ℂ (Fin n) =>
        Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap))) z := by
  let J := fun w : EuclideanSpace ℂ (Fin n) => LinearMap.det (fderiv ℂ ψ w).toLinearMap
  have hJ : ContDiffAt ℝ 2 J z := jacobianDet_contDiffAt_real_two hψ hψhol
  have hRe : ContDiffAt ℝ 2 (fun w => (J w).re) z := by
    change ContDiffAt ℝ 2 (fun w => Complex.reCLM (J w)) z
    exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : EuclideanSpace ℂ (Fin n) =>
      Complex.reCLM) z).clm_apply hJ
  have hIm : ContDiffAt ℝ 2 (fun w => (J w).im) z := by
    change ContDiffAt ℝ 2 (fun w => Complex.imCLM (J w)) z
    exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : EuclideanSpace ℂ (Fin n) =>
      Complex.imCLM) z).clm_apply hJ
  have hnorm : ContDiffAt ℝ 2 (fun w => Complex.normSq (J w)) z := by
    have hnorm' : ContDiffAt ℝ 2
        (fun w => (J w).re * (J w).re + (J w).im * (J w).im) z := by
      fun_prop (disch := assumption)
    simpa only [Complex.normSq_apply] using hnorm'
  have hnormz : Complex.normSq (J z) ≠ 0 := by
    intro hzero
    apply hdet
    simpa [J, Complex.normSq_eq_zero] using hzero
  simpa [J] using hnorm.log hnormz

private lemma fderiv_fderiv_affineLine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z)
    (L : ℂ →L[ℝ] E) (e d : ℂ) :
    fderiv ℝ (fderiv ℝ (fun t : ℂ => f (z + L t))) 0 e d =
      fderiv ℝ (fderiv ℝ f) z (L e) (L d) := by
  let P : ℂ → E := fun t => z + L t
  let q : ℂ → ℝ := fun t => f (P t)
  let post : (E →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ ℂ E ℝ).flip L
  let A : ℂ → E →L[ℝ] ℝ := fun t => fderiv ℝ f (P t)
  let K : ℂ → ℂ →L[ℝ] ℝ := fun t => post (A t)
  have hPdiff (t : ℂ) : DifferentiableAt ℝ P t := by
    fun_prop
  have hPderiv (t : ℂ) : fderiv ℝ P t = L := by
    simp [P, fderiv_const_add, ContinuousLinearMap.fderiv]
  have hFnear : ∀ᶠ t in 𝓝 (0 : ℂ), ContDiffAt ℝ 2 f (P t) := by
    have hPcontinuous : Continuous P := by fun_prop
    have hP0 : P 0 = z := by simp [P]
    have hT : Tendsto P (𝓝 (0 : ℂ)) (𝓝 z) := by
      have hPAt : ContinuousAt P 0 := hPcontinuous.continuousAt
      simpa [hP0] using hPAt.tendsto
    exact hT (hf.eventually (by simp))
  have hEq : fderiv ℝ q =ᶠ[𝓝 (0 : ℂ)] K := by
    filter_upwards [hFnear] with t ht
    have hfd : DifferentiableAt ℝ f (P t) := ht.differentiableAt (by norm_num)
    have hpd := hPdiff t
    change fderiv ℝ (f ∘ P) t = K t
    rw [fderiv_comp t hfd hpd, hPderiv t]
    rfl
  have hA_diff : DifferentiableAt ℝ A 0 := by
    have hfderiv : DifferentiableAt ℝ (fderiv ℝ f) z :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hfderivP : DifferentiableAt ℝ (fderiv ℝ f) (P 0) := by
      simpa [P] using hfderiv
    exact hfderivP.comp 0 (hPdiff 0)
  have hAderiv : fderiv ℝ A 0 = (fderiv ℝ (fderiv ℝ f) z).comp L := by
    change fderiv ℝ ((fderiv ℝ f) ∘ P) 0 = _
    rw [fderiv_comp 0 (by
      simpa [P] using (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      (hPdiff 0), hPderiv 0]
    simp [P]
  have hKderiv : fderiv ℝ K 0 = post.comp (fderiv ℝ A 0) := by
    change fderiv ℝ (post ∘ A) 0 = _
    rw [fderiv_comp 0 post.differentiableAt hA_diff, ContinuousLinearMap.fderiv]
  have hSecond := congrArg (fun D : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) => D e d) hEq.fderiv_eq
  rw [hKderiv, hAderiv] at hSecond
  simpa [K, post, A, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply] using hSecond

/-- A holomorphic Jacobian determinant that is nonzero at the base point has pluriharmonic
logarithmic squared norm there. In real coordinates, this is the `J`-invariance identity for its
mixed Hessian. This is the local analytic input used in the Ricci form coordinate-change formula. -/
theorem jacobianLogNorm_mixed_hessian
    {n : ℕ} {ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n)}
    {z : EuclideanSpace ℂ (Fin n)}
    (hψ : ContDiffAt ℝ 3 ψ z)
    (hψhol : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ ψ w)
    (hdet : LinearMap.det (fderiv ℂ ψ z).toLinearMap ≠ 0)
    (u v : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun w : EuclideanSpace ℂ (Fin n) =>
      Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap)))) z
      (Complex.I • u) v =
    fderiv ℝ (fderiv ℝ (fun w : EuclideanSpace ℂ (Fin n) =>
      Real.log (Complex.normSq (LinearMap.det (fderiv ℂ ψ w).toLinearMap)))) z
      u (Complex.I • v) := by
  let J : EuclideanSpace ℂ (Fin n) → ℂ :=
    fun w => LinearMap.det (fderiv ℂ ψ w).toLinearMap
  let F : EuclideanSpace ℂ (Fin n) → ℝ := fun w => Real.log (Complex.normSq (J w))
  have hF : ContDiffAt ℝ 2 F z := by
    exact jacobianLogNorm_contDiffAt_real_two hψ hψhol hdet
  let B : EuclideanSpace ℂ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℂ (Fin n) →ₗ[ℝ] ℝ :=
    { toFun := fun a => (fderiv ℝ (fderiv ℝ F) z a).toLinearMap
      map_add' := by intro a b; ext c; simp
      map_smul' := by intro r a; ext c; simp }
  have hSymm : ∀ a b, fderiv ℝ (fderiv ℝ F) z a b =
      fderiv ℝ (fderiv ℝ F) z b a := by
    intro a b
    exact hF.isSymmSndFDerivAt (by simp) a b
  have hB : ∀ a b, B a b = B b a := by
    intro a b
    exact hSymm a b
  have hdiag : ∀ x, B (Complex.I • x) (Complex.I • x) + B x x = 0 := by
    intro x
    let L : ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) :=
      (ContinuousLinearMap.id ℝ ℂ).smulRight x
    let g : ℂ → ℂ := fun t => J (z + L t)
    have hgHol : ∀ᶠ t in 𝓝 (0 : ℂ), DifferentiableAt ℂ g t := by
      simpa [g, L, ContinuousLinearMap.smulRight_apply] using
        jacobianDet_complexLine_differentiableAt (u := x) hψ hψhol
    have hg0 : g 0 ≠ 0 := by
      simpa [g, L, J, ContinuousLinearMap.smulRight_apply] using hdet
    have hLap := log_normSq_complexLine_laplacian hgHol hg0
    have hI := fderiv_fderiv_affineLine hF L Complex.I Complex.I
    have h1 := fderiv_fderiv_affineLine hF L 1 1
    have hI' : fderiv ℝ (fderiv ℝ (fun t => Real.log (Complex.normSq (g t))))
        0 Complex.I Complex.I = B (Complex.I • x) (Complex.I • x) := by
      simpa [g, F, J, L, B, ContinuousLinearMap.smulRight_apply] using hI
    have h1' : fderiv ℝ (fderiv ℝ (fun t => Real.log (Complex.normSq (g t))))
        0 1 1 = B x x := by
      simpa [g, F, J, L, B, ContinuousLinearMap.smulRight_apply] using h1
    rw [← hI', ← h1']
    exact hLap
  have hmain := j_invariant_of_hessian_diagonal B hB hdiag u v
  simpa [B, F, J] using hmain

end Complex
