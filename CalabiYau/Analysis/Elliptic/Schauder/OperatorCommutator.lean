module

public import CalabiYau.Analysis.Elliptic.Schauder

/-!
# Differentiating the complex elliptic operator

For a real direction `e`, differentiating `L_A u = re tr (A * H(u))` separates the
coefficient derivative from the differentiated Hessian. The product order in the trace is
intentional: expanding the trace gives the contraction `A_ij H_ji`. The imported
`complexHessian_apply` formula carries the factor `1/4` in real coordinates.
-/

@[expose] public section

open Matrix Filter
open scoped Topology

private theorem complexHessian_entry_contDiffAt_one {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (j k : Fin n) :
    ContDiffAt ℝ 1 (fun x ↦ complexHessian u x j k) z := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z :=
    hu.fderiv_right (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) z :=
    hD1.fderiv_right (by norm_num)
  have hQ (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x v w) z := by
    have hv : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) z := contDiffAt_const
    have hw : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ w) z := contDiffAt_const
    exact (hD2.clm_apply hv).clm_apply hw
  let q : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦
    ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) : ℂ) +
      fderiv ℝ (fderiv ℝ u) x (Complex.I • EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1) +
      Complex.I * (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1) -
      fderiv ℝ (fderiv ℝ u) x (Complex.I • EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1))) / 4
  have hq : ContDiffAt ℝ 1 q z := by
    dsimp [q]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x :=
    hu.eventually (by norm_num)
  have hEq : (fun x ↦ complexHessian u x j k) =ᶠ[𝓝 z] q := by
    filter_upwards [hnear] with x hx
    exact complexHessian_apply (hx.of_le (by norm_num)) j k
  exact hq.congr_of_eventuallyEq hEq

private theorem complexHessian_differentiableAt {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) : DifferentiableAt ℝ (complexHessian u) z := by
  change DifferentiableAt ℝ (fun x i j ↦ complexHessian u x i j) z
  rw [differentiableAt_pi]
  intro j
  rw [differentiableAt_pi]
  intro k
  exact (complexHessian_entry_contDiffAt_one hu j k).differentiableAt (by norm_num)

private theorem fderiv_ofRealCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun x ↦ (f x : ℂ)) z = (Complex.ofRealCLM).comp (fderiv ℝ f z) := by
  change fderiv ℝ (fun x ↦ Complex.ofRealCLM (f x)) z = _
  rw [fderiv_clm_apply (differentiableAt_const Complex.ofRealCLM) hf]
  simp

private theorem fderiv_gradient_eval {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (b c : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun x ↦ fderiv ℝ u x c) z b =
      fderiv ℝ (fderiv ℝ u) z b c := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) z := hD1.differentiableAt (by norm_num)
  rw [fderiv_clm_apply hdiff (differentiableAt_const c)]
  simp

private theorem secondDerivative_directional_eq {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z e : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (b c : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun x ↦ fderiv ℝ u x e)) z b c =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x c e) z b := by
  let du : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦ fderiv ℝ u x e
  have hDu : ContDiffAt ℝ 2 du z := by
    dsimp [du]
    exact (hu.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hDdu : ContDiffAt ℝ 1 (fderiv ℝ du) z := hDu.fderiv_right (by norm_num)
  have hDiffDdu : DifferentiableAt ℝ (fderiv ℝ du) z := hDdu.differentiableAt (by norm_num)
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEq : (fun x ↦ fderiv ℝ du x c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ (fderiv ℝ u) x c e := by
    filter_upwards [hnear] with x hx
    exact fderiv_gradient_eval hx c e
  have hEval : fderiv ℝ (fun x ↦ fderiv ℝ du x c) z b =
      fderiv ℝ (fderiv ℝ du) z b c := by
    rw [fderiv_clm_apply hDiffDdu (differentiableAt_const c)]
    simp
  calc
    fderiv ℝ (fderiv ℝ du) z b c = fderiv ℝ (fun x ↦ fderiv ℝ du x c) z b := hEval.symm
    _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x c e) z b := by
      exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L b)
        (hEq.fderiv_eq (𝕜 := ℝ))

private theorem thirdDerivative_swap_hessian_slots {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (a b c : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z a =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x c b) z a := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) z :=
    hD1.fderiv_right (by norm_num)
  have hbc : ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z := by
    have hb : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ b) z := contDiffAt_const
    have hc : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ c) z := contDiffAt_const
    exact (hD2.clm_apply hb).clm_apply hc
  have hcb : ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x c b) z := by
    have hb : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ b) z := contDiffAt_const
    have hc : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ c) z := contDiffAt_const
    exact (hD2.clm_apply hc).clm_apply hb
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEq : (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ (fderiv ℝ u) x c b := by
    filter_upwards [hnear] with x hx
    have hx2 : ContDiffAt ℝ 2 u x := hx.of_le (by norm_num)
    exact (hx2.isSymmSndFDerivAt (by norm_num)) b c
  have hderiv := hEq.fderiv_eq (𝕜 := ℝ)
  exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L a) hderiv

private theorem thirdDerivative_swap_outer_hessian_slot {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (a b c : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z a =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x a c) z b := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  let g : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦ fderiv ℝ u x c
  have hgc : ContDiffAt ℝ 2 g z := by
    dsimp [g]
    exact hD1.clm_apply contDiffAt_const
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEqB : (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ g x b := by
    filter_upwards [hnear] with x hx
    exact (fderiv_gradient_eval hx b c).symm
  have hEqA : (fun x ↦ fderiv ℝ (fderiv ℝ u) x a c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ g x a := by
    filter_upwards [hnear] with x hx
    exact (fderiv_gradient_eval hx a c).symm
  have hDg : ContDiffAt ℝ 1 (fderiv ℝ g) z := hgc.fderiv_right (by norm_num)
  have hDgDiff : DifferentiableAt ℝ (fderiv ℝ g) z := hDg.differentiableAt (by norm_num)
  have hEvalB : fderiv ℝ (fun x ↦ fderiv ℝ g x b) z a =
      fderiv ℝ (fderiv ℝ g) z a b := by
    rw [fderiv_clm_apply hDgDiff (differentiableAt_const b)]
    simp
  have hEvalA : fderiv ℝ (fun x ↦ fderiv ℝ g x a) z b =
      fderiv ℝ (fderiv ℝ g) z b a := by
    rw [fderiv_clm_apply hDgDiff (differentiableAt_const a)]
    simp
  have hsymm := hgc.isSymmSndFDerivAt (by norm_num)
  calc
    fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z a =
        fderiv ℝ (fun x ↦ fderiv ℝ g x b) z a := by
      exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L a)
        (hEqB.fderiv_eq (𝕜 := ℝ))
    _ = fderiv ℝ (fderiv ℝ g) z a b := hEvalB
    _ = fderiv ℝ (fderiv ℝ g) z b a := hsymm a b
    _ = fderiv ℝ (fun x ↦ fderiv ℝ g x a) z b := hEvalA.symm
    _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x a c) z b := by
      exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L b)
        (hEqA.fderiv_eq (𝕜 := ℝ)).symm

private theorem complexHessian_entry_fderiv_directional {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z e : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (j k : Fin n) :
    (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k =
      complexHessian (fun w ↦ fderiv ℝ u w e) z j k := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) z :=
    hD1.fderiv_right (by norm_num)
  have hQ (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x v w) z := by
    have hv : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) z := contDiffAt_const
    have hw : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ w) z := contDiffAt_const
    exact (hD2.clm_apply hv).clm_apply hw
  let vj : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let vk : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k 1
  let ivj : EuclideanSpace ℂ (Fin n) := Complex.I • EuclideanSpace.single j 1
  let ivk : EuclideanSpace ℂ (Fin n) := Complex.I • EuclideanSpace.single k 1
  let q₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦
    fderiv ℝ (fderiv ℝ u) x vj vk
  let q₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦
    fderiv ℝ (fderiv ℝ u) x ivj ivk
  let q₃ : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦
    fderiv ℝ (fderiv ℝ u) x vj ivk
  let q₄ : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦
    fderiv ℝ (fderiv ℝ u) x ivj vk
  let s : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦
    (q₁ x : ℂ) + (q₂ x : ℂ) + Complex.I * ((q₃ x : ℂ) - (q₄ x : ℂ))
  let q : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ (1 / 4 : ℝ) • s x
  have hq₁ : ContDiffAt ℝ 1 q₁ z := by
    dsimp [q₁, vj, vk]
    exact hQ _ _
  have hq₂ : ContDiffAt ℝ 1 q₂ z := by
    dsimp [q₂, ivj, ivk]
    exact hQ _ _
  have hq₃ : ContDiffAt ℝ 1 q₃ z := by
    dsimp [q₃, vj, ivk]
    exact hQ _ _
  have hq₄ : ContDiffAt ℝ 1 q₄ z := by
    dsimp [q₄, ivj, vk]
    exact hQ _ _
  have hs : ContDiffAt ℝ 1 s z := by
    dsimp [s]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hq : ContDiffAt ℝ 1 q z := by
    dsimp [q]
    fun_prop
  have hEq : (fun x ↦ complexHessian u x j k) =ᶠ[𝓝 z] q := by
    have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
    filter_upwards [hnear] with x hx
    rw [complexHessian_apply (hx.of_le (by norm_num)) j k]
    dsimp [q, s, q₁, q₂, q₃, q₄, vj, vk, ivj, ivk]
    simp only [Complex.ofReal_div]
    norm_num
    ring_nf
  have hq₁C : ContDiffAt ℝ 1 (fun x ↦ (q₁ x : ℂ)) z := by
    dsimp [q₁]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hq₂C : ContDiffAt ℝ 1 (fun x ↦ (q₂ x : ℂ)) z := by
    dsimp [q₂]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hq₃C : ContDiffAt ℝ 1 (fun x ↦ (q₃ x : ℂ)) z := by
    dsimp [q₃]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hq₄C : ContDiffAt ℝ 1 (fun x ↦ (q₄ x : ℂ)) z := by
    dsimp [q₄]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hcast₁ : fderiv ℝ (fun x ↦ (q₁ x : ℂ)) z e = (fderiv ℝ q₁ z e : ℂ) := by
    have h := fderiv_ofRealCLM (hq₁.differentiableAt (by norm_num))
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) h
    simpa using he
  have hcast₂ : fderiv ℝ (fun x ↦ (q₂ x : ℂ)) z e = (fderiv ℝ q₂ z e : ℂ) := by
    have h := fderiv_ofRealCLM (hq₂.differentiableAt (by norm_num))
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) h
    simpa using he
  have hcast₃ : fderiv ℝ (fun x ↦ (q₃ x : ℂ)) z e = (fderiv ℝ q₃ z e : ℂ) := by
    have h := fderiv_ofRealCLM (hq₃.differentiableAt (by norm_num))
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) h
    simpa using he
  have hcast₄ : fderiv ℝ (fun x ↦ (q₄ x : ℂ)) z e = (fderiv ℝ q₄ z e : ℂ) := by
    have h := fderiv_ofRealCLM (hq₄.differentiableAt (by norm_num))
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) h
    simpa using he
  have hsumDiff : DifferentiableAt ℝ (fun x ↦ (q₁ x : ℂ) + (q₂ x : ℂ)) z :=
    (hq₁C.differentiableAt (by norm_num)).add (hq₂C.differentiableAt (by norm_num))
  have hdiffCD : DifferentiableAt ℝ (fun x ↦ (q₃ x : ℂ) - (q₄ x : ℂ)) z :=
    (hq₃C.differentiableAt (by norm_num)).sub (hq₄C.differentiableAt (by norm_num))
  have hprodDiff : DifferentiableAt ℝ
      (fun x ↦ Complex.I * ((q₃ x : ℂ) - (q₄ x : ℂ))) z := hdiffCD.const_mul _
  have hsderiv : fderiv ℝ s z e =
      (fderiv ℝ q₁ z e : ℂ) + (fderiv ℝ q₂ z e : ℂ) +
        Complex.I * ((fderiv ℝ q₃ z e : ℂ) - (fderiv ℝ q₄ z e : ℂ)) := by
    change (fderiv ℝ
      ((fun x ↦ (q₁ x : ℂ) + (q₂ x : ℂ)) +
        fun x ↦ Complex.I * ((q₃ x : ℂ) - (q₄ x : ℂ))) z) e = _
    rw [fderiv_add hsumDiff hprodDiff]
    change (fderiv ℝ
        ((fun x ↦ (q₁ x : ℂ)) + (fun x ↦ (q₂ x : ℂ))) z +
      fderiv ℝ (fun x ↦ Complex.I * ((q₃ x : ℂ) - (q₄ x : ℂ))) z) e = _
    rw [fderiv_add (hq₁C.differentiableAt (by norm_num))
      (hq₂C.differentiableAt (by norm_num))]
    change (fderiv ℝ (fun x ↦ (q₁ x : ℂ)) z +
      fderiv ℝ (fun x ↦ (q₂ x : ℂ)) z +
      fderiv ℝ (fun x ↦ Complex.I *
        ((fun x ↦ (q₃ x : ℂ)) x - (fun x ↦ (q₄ x : ℂ)) x)) z) e = _
    rw [fderiv_const_mul hdiffCD Complex.I]
    change (fderiv ℝ (fun x ↦ (q₁ x : ℂ)) z +
      fderiv ℝ (fun x ↦ (q₂ x : ℂ)) z +
      Complex.I • fderiv ℝ ((fun x ↦ (q₃ x : ℂ)) - (fun x ↦ (q₄ x : ℂ))) z) e = _
    rw [fderiv_sub (hq₃C.differentiableAt (by norm_num))
      (hq₄C.differentiableAt (by norm_num))]
    have hsub_eval : (fderiv ℝ (fun x ↦ (q₃ x : ℂ)) z -
        fderiv ℝ (fun x ↦ (q₄ x : ℂ)) z) e =
        fderiv ℝ (fun x ↦ (q₃ x : ℂ)) z e -
          fderiv ℝ (fun x ↦ (q₄ x : ℂ)) z e := rfl
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hsub_eval]
    rw [hcast₁, hcast₂, hcast₃, hcast₄]
  have hqderiv : fderiv ℝ q z e = (1 / 4 : ℝ) • fderiv ℝ s z e := by
    change (fderiv ℝ (fun y ↦ (1 / 4 : ℝ) • s y) z) e = _
    rw [fderiv_fun_const_smul (hs.differentiableAt (by norm_num))]
    rfl
  let du : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦ fderiv ℝ u x e
  have hDu : ContDiffAt ℝ 2 du z := by
    dsimp [du]
    exact hD1.clm_apply contDiffAt_const
  have hq₁third : fderiv ℝ q₁ z e = fderiv ℝ (fderiv ℝ du) z vj vk := by
    calc
      fderiv ℝ q₁ z e = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x vj vk) z e := rfl
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x e vk) z vj :=
        thirdDerivative_swap_outer_hessian_slot hu e vj vk
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x vk e) z vj :=
        thirdDerivative_swap_hessian_slots hu vj e vk
      _ = fderiv ℝ (fderiv ℝ du) z vj vk :=
        (secondDerivative_directional_eq hu vj vk).symm
  have hq₂third : fderiv ℝ q₂ z e = fderiv ℝ (fderiv ℝ du) z ivj ivk := by
    calc
      fderiv ℝ q₂ z e = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x ivj ivk) z e := rfl
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x e ivk) z ivj :=
        thirdDerivative_swap_outer_hessian_slot hu e ivj ivk
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x ivk e) z ivj :=
        thirdDerivative_swap_hessian_slots hu ivj e ivk
      _ = fderiv ℝ (fderiv ℝ du) z ivj ivk :=
        (secondDerivative_directional_eq hu ivj ivk).symm
  have hq₃third : fderiv ℝ q₃ z e = fderiv ℝ (fderiv ℝ du) z vj ivk := by
    calc
      fderiv ℝ q₃ z e = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x vj ivk) z e := rfl
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x e ivk) z vj :=
        thirdDerivative_swap_outer_hessian_slot hu e vj ivk
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x ivk e) z vj :=
        thirdDerivative_swap_hessian_slots hu vj e ivk
      _ = fderiv ℝ (fderiv ℝ du) z vj ivk :=
        (secondDerivative_directional_eq hu vj ivk).symm
  have hq₄third : fderiv ℝ q₄ z e = fderiv ℝ (fderiv ℝ du) z ivj vk := by
    calc
      fderiv ℝ q₄ z e = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x ivj vk) z e := rfl
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x e vk) z ivj :=
        thirdDerivative_swap_outer_hessian_slot hu e ivj vk
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x vk e) z ivj :=
        thirdDerivative_swap_hessian_slots hu ivj e vk
      _ = fderiv ℝ (fderiv ℝ du) z ivj vk :=
        (secondDerivative_directional_eq hu ivj vk).symm
  have hright := complexHessian_apply hDu j k
  have hleft : (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k = fderiv ℝ q z e := by
    have hMatDiff : DifferentiableAt ℝ (fun w ↦ complexHessian u w) z :=
      complexHessian_differentiableAt hu
    have hRowDiff (i : Fin n) :
        DifferentiableAt ℝ (fun w l ↦ complexHessian u w i l) z := by
      rw [differentiableAt_pi]
      intro l
      exact (complexHessian_entry_contDiffAt_one hu i l).differentiableAt (by norm_num)
    have hOuter := fderiv_apply hMatDiff j
    have hInner := fderiv_apply (hRowDiff j) k
    have hCoordinate : (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k =
        fderiv ℝ (fun w ↦ complexHessian u w j k) z e := by
      change (fderiv ℝ (complexHessian u) z e) j k = _
      calc
        (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k =
            (fderiv ℝ (fun w ↦ complexHessian u w j) z e) k := by
          have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ]
              (Fin n → ℂ) ↦ L e) hOuter.symm
          have h' := congrArg (fun row : Fin n → ℂ ↦ row k) h
          change ((fderiv ℝ (fun w ↦ complexHessian u w) z e) j) k = _ at h'
          exact h'
        _ = fderiv ℝ (fun w ↦ complexHessian u w j k) z e := by
          have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) hInner.symm
          change (fderiv ℝ (fun w l ↦ complexHessian u w j l) z e) k = _ at h
          exact h
    have hderivEq := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e)
      (hEq.fderiv_eq (𝕜 := ℝ))
    exact hCoordinate.trans hderivEq
  have hstep : fderiv ℝ q z e = complexHessian du z j k := by
    rw [hqderiv, hsderiv, hq₁third, hq₂third, hq₃third, hq₄third, hright]
    simp [vj, vk, ivj, ivk, Complex.real_smul]
    norm_num
    ring_nf
  exact hleft.trans hstep

private theorem complexHessian_scalar_entry_fderiv {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z e : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (j k : Fin n) :
    fderiv ℝ (fun w ↦ complexHessian u w j k) z e =
      (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k := by
  have hMatDiff : DifferentiableAt ℝ (fun w ↦ complexHessian u w) z :=
    complexHessian_differentiableAt hu
  have hRowDiff (i : Fin n) :
      DifferentiableAt ℝ (fun w l ↦ complexHessian u w i l) z := by
    rw [differentiableAt_pi]
    intro l
    exact (complexHessian_entry_contDiffAt_one hu i l).differentiableAt (by norm_num)
  have hOuter := fderiv_apply hMatDiff j
  have hInner := fderiv_apply (hRowDiff j) k
  calc
    fderiv ℝ (fun w ↦ complexHessian u w j k) z e =
        (fderiv ℝ (fun w ↦ complexHessian u w j) z e) k := by
      have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) hInner.symm
      change (fderiv ℝ (fun w l ↦ complexHessian u w j l) z e) k = _ at h
      exact h.symm
    _ = (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k := by
      have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ]
          (Fin n → ℂ) ↦ L e) hOuter.symm
      have h' := congrArg (fun row : Fin n → ℂ ↦ row k) h
      change ((fderiv ℝ (fun w ↦ complexHessian u w) z e) j) k = _ at h'
      exact h'.symm

private theorem fderiv_matrix_entry {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    {z e : EuclideanSpace ℂ (Fin n)}
    (hA : ∀ j l, ContDiffAt ℝ 1 (fun w ↦ A w j l) z) (j l : Fin n) :
    (fderiv ℝ A z e) j l = fderiv ℝ (fun w ↦ A w j l) z e := by
  have hRowDiff (i : Fin n) :
      DifferentiableAt ℝ (fun w k ↦ A w i k) z := by
    rw [differentiableAt_pi]
    intro k
    exact (hA i k).differentiableAt (by norm_num)
  have hMatDiff : DifferentiableAt ℝ (fun w ↦ A w) z := by
    change DifferentiableAt ℝ (fun w i k ↦ A w i k) z
    rw [differentiableAt_pi]
    intro i
    exact hRowDiff i
  have hOuter := fderiv_apply hMatDiff j
  have hInner := fderiv_apply (hRowDiff j) l
  calc
    (fderiv ℝ (fun w ↦ A w) z e) j l =
        (fderiv ℝ (fun w ↦ A w j) z e) l := by
      have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ]
          (Fin n → ℂ) ↦ L e) hOuter.symm
      have h' := congrArg (fun row : Fin n → ℂ ↦ row l) h
      change ((fderiv ℝ (fun w ↦ A w) z e) j) l = _ at h'
      exact h'
    _ = fderiv ℝ (fun w ↦ A w j l) z e := by
      have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) hInner.symm
      change (fderiv ℝ (fun w k ↦ A w j k) z e) l = _ at h
      exact h

private theorem complexEllipticOp_eq_entry_sum {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    complexEllipticOp A v z =
      ∑ j, ∑ l, Complex.reCLM (A z j l * complexHessian v z l j) := by
  simp [complexEllipticOp, Matrix.trace, Matrix.mul_apply, Complex.reCLM_apply]

private theorem real_trace_mul_eq_entry_sum {n : ℕ}
    (B C : Matrix (Fin n) (Fin n) ℂ) :
    RCLike.re ((B * C).trace) =
      ∑ j, ∑ l, Complex.reCLM (B j l * C l j) := by
  simp [Matrix.trace, Matrix.mul_apply, Complex.reCLM_apply]

private theorem fderiv_reCLM_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {z e : E} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun x ↦ Complex.reCLM (f x)) z e =
      Complex.reCLM (fderiv ℝ f z e) := by
  have h := fderiv_clm_apply (differentiableAt_const Complex.reCLM) hf
  have he := congrArg (fun L : E →L[ℝ] ℝ ↦ L e) h
  simpa using he

private theorem fderiv_re_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℂ} {z e : E}
    (ha : DifferentiableAt ℝ a z) (hb : DifferentiableAt ℝ b z) :
    fderiv ℝ (fun x ↦ Complex.reCLM (a x * b x)) z e =
      Complex.reCLM (a z * fderiv ℝ b z e + b z * fderiv ℝ a z e) := by
  calc
    fderiv ℝ (fun x ↦ Complex.reCLM (a x * b x)) z e =
        Complex.reCLM (fderiv ℝ (fun x ↦ a x * b x) z e) :=
      fderiv_reCLM_comp (ha.mul hb)
    _ = Complex.reCLM (a z * fderiv ℝ b z e + b z * fderiv ℝ a z e) := by
      have h := congrArg (fun L : E →L[ℝ] ℂ ↦ L e) (fderiv_fun_mul ha hb)
      simpa only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] using congrArg Complex.reCLM h

/-- Real-direction derivative of `L_A u`: the coefficient derivative is contracted with
`H(u)`, while the Hessian derivative is `H(Dₑu)`. -/
theorem fderiv_complexEllipticOp {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ)
    {z e : EuclideanSpace ℂ (Fin n)}
    (hA : ∀ j l, ContDiffAt ℝ 1 (fun w ↦ A w j l) z)
    (hu : ContDiffAt ℝ 3 u z) :
    fderiv ℝ (complexEllipticOp A u) z e =
      complexEllipticOp A (fun w ↦ fderiv ℝ u w e) z +
        RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace) := by
  let du : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ u w e
  let S : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦
    ∑ j, ∑ l, Complex.reCLM (A x j l * complexHessian u x l j)
  have hDu : ContDiffAt ℝ 2 du z := by
    dsimp [du]
    exact (hu.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hS (v : EuclideanSpace ℂ (Fin n) → ℝ) :
      complexEllipticOp A v = fun x ↦ ∑ j, ∑ l,
        Complex.reCLM (A x j l * complexHessian v x l j) := by
    funext x
    exact complexEllipticOp_eq_entry_sum A v x
  have hTermC1 (j l : Fin n) :
      ContDiffAt ℝ 1 (fun x ↦ Complex.reCLM
        (A x j l * complexHessian u x l j)) z := by
    have hA' := hA j l
    have hH' := complexHessian_entry_contDiffAt_one hu l j
    fun_prop
  have hTermDiff (j l : Fin n) :
      DifferentiableAt ℝ (fun x ↦ Complex.reCLM
        (A x j l * complexHessian u x l j)) z :=
    (hTermC1 j l).differentiableAt (by norm_num)
  have hRowDiff (j : Fin n) : DifferentiableAt ℝ
      (fun x ↦ ∑ l, Complex.reCLM (A x j l * complexHessian u x l j)) z := by
    apply DifferentiableAt.fun_sum
    intro l hl
    exact hTermDiff j l
  have hSumDiff : DifferentiableAt ℝ S z := by
    dsimp [S]
    apply DifferentiableAt.fun_sum
    intro j hj
    exact hRowDiff j
  have hSumDeriv : fderiv ℝ S z =
      ∑ j, ∑ l, fderiv ℝ (fun x ↦ Complex.reCLM
        (A x j l * complexHessian u x l j)) z := by
    change fderiv ℝ (fun x ↦ ∑ j, ∑ l, Complex.reCLM
      (A x j l * complexHessian u x l j)) z = _
    rw [fderiv_fun_sum (fun j hj ↦ hRowDiff j)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [fderiv_fun_sum (fun l hl ↦ hTermDiff j l)]
  have hTermDerivative (j l : Fin n) :
      fderiv ℝ (fun x ↦ Complex.reCLM (A x j l * complexHessian u x l j)) z e =
        Complex.reCLM ((fderiv ℝ A z e j l) * complexHessian u z l j +
          A z j l * complexHessian du z l j) := by
    have hAjl : DifferentiableAt ℝ (fun x ↦ A x j l) z :=
      (hA j l).differentiableAt (by norm_num)
    have hHlj : DifferentiableAt ℝ (fun x ↦ complexHessian u x l j) z :=
      (complexHessian_entry_contDiffAt_one hu l j).differentiableAt (by norm_num)
    rw [fderiv_re_mul hAjl hHlj]
    rw [complexHessian_scalar_entry_fderiv hu l j,
      ← fderiv_matrix_entry A hA j l,
      complexHessian_entry_fderiv_directional hu l j]
    congr 1
    ring
  have hSumDir := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L e) hSumDeriv
  simp only [_root_.sum_apply] at hSumDir
  have hSumTerms :
      (∑ j, ∑ l, fderiv ℝ (fun x ↦ Complex.reCLM
        (A x j l * complexHessian u x l j)) z e) =
      ∑ j, ∑ l, Complex.reCLM
        ((fderiv ℝ A z e j l) * complexHessian u z l j +
          A z j l * complexHessian du z l j) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    exact hTermDerivative j l
  calc
    fderiv ℝ (complexEllipticOp A u) z e = (fderiv ℝ S z) e := by
      rw [hS u]
    _ = ∑ j, ∑ l, Complex.reCLM
        ((fderiv ℝ A z e j l) * complexHessian u z l j +
          A z j l * complexHessian du z l j) := hSumDir.trans hSumTerms
    _ = complexEllipticOp A du z +
        RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace) := by
      rw [hS du, real_trace_mul_eq_entry_sum]
      simp only [map_add, Finset.sum_add_distrib]
      ac_rfl

