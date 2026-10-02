-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Bundle/PartialMfderiv/ModelMixed.lean
-- Locally modified.
module
public import CalabiYau.Geometry.Manifold.Bundle.PartialMfderiv.Basic

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

open scoped Topology Manifold ContDiff

namespace CalabiYau

section ModelMixed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem model_spatial_fderiv_eq
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (s : ℝ) (x V : E) :
    (fderiv ℝ (F s) x) V =
      (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (s, x)) (0, V) := by
  let G : ℝ × E -> ℝ := fun p => F p.1 p.2
  let L : E -> ℝ × E := fun y => (s, y)
  have hG : DifferentiableAt ℝ G (s, x) :=
    hF.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (s, x)
  have hL : DifferentiableAt ℝ L x := by
    fun_prop
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := x) (f := L) (g := G) hG hL
  have hLderiv : (fderiv ℝ L x) V = (0, V) := by
    rw [DifferentiableAt.fderiv_prodMk]
    · simp
    · fun_prop
    · fun_prop
  change (fderiv ℝ (G ∘ L) x) V = (fderiv ℝ G (s, x)) (0, V)
  rw [hcomp]
  change (fderiv ℝ G (s, x)) ((fderiv ℝ L x) V) =
    (fderiv ℝ G (s, x)) (0, V)
  rw [hLderiv]

private theorem model_spatial_fderiv_eq_of_contDiffAt
    (F : ℝ -> E -> ℝ)
    {s : ℝ} {x V : E}
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × E => F p.1 p.2) (s, x)) :
    (fderiv ℝ (F s) x) V =
      (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (s, x)) (0, V) := by
  let G : ℝ × E -> ℝ := fun p => F p.1 p.2
  let L : E -> ℝ × E := fun y => (s, y)
  have hG : DifferentiableAt ℝ G (s, x) :=
    hF.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hL : DifferentiableAt ℝ L x := by
    fun_prop
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := x) (f := L) (g := G) hG hL
  have hLderiv : (fderiv ℝ L x) V = (0, V) := by
    rw [DifferentiableAt.fderiv_prodMk]
    · simp
    · fun_prop
    · fun_prop
  change (fderiv ℝ (G ∘ L) x) V = (fderiv ℝ G (s, x)) (0, V)
  rw [hcomp]
  change (fderiv ℝ G (s, x)) ((fderiv ℝ L x) V) =
    (fderiv ℝ G (s, x)) (0, V)
  rw [hLderiv]

private theorem model_hasDerivAt_fixed_snd
    (A : ℝ × E -> ℝ) (t : ℝ) (x : E)
    (hA : DifferentiableAt ℝ A (t, x)) :
    HasDerivAt (fun s : ℝ => A (s, x))
      ((fderiv ℝ A (t, x)) (1, 0)) t := by
  let L : ℝ -> ℝ × E := fun s => (s, x)
  have hL : DifferentiableAt ℝ L t := by
    fun_prop
  have hcomp := (hA.hasFDerivAt.comp t hL.hasFDerivAt).hasDerivAt
  have hLderiv : (fderiv ℝ L t) 1 = (1, 0) := by
    rw [DifferentiableAt.fderiv_prodMk]
    · simp
    · fun_prop
    · fun_prop
  change HasDerivAt (A ∘ L)
    ((fderiv ℝ A (t, x)) ((fderiv ℝ L t) 1)) t at hcomp
  rw [hLderiv] at hcomp
  exact hcomp

theorem modelLine_fst_hasDerivAt
    {A : ℝ × ℝ -> ℝ} {s t : ℝ}
    (hA : DifferentiableAt ℝ A (s, t)) :
    HasDerivAt (fun σ : ℝ => A (σ, t))
      ((fderiv ℝ A (s, t)) ((1 : ℝ), 0)) s := by
  let L : ℝ -> ℝ × ℝ := fun σ => (σ, t)
  have hL : DifferentiableAt ℝ L s := by
    fun_prop
  have hcomp := (hA.hasFDerivAt.comp s hL.hasFDerivAt).hasDerivAt
  have hLderiv : (fderiv ℝ L s) 1 = ((1 : ℝ), 0) := by
    rw [DifferentiableAt.fderiv_prodMk]
    · simp
    · fun_prop
    · fun_prop
  change HasDerivAt (A ∘ L)
    ((fderiv ℝ A (s, t)) ((fderiv ℝ L s) 1)) s at hcomp
  rw [hLderiv] at hcomp
  exact hcomp

theorem modelLine_snd_hasDerivAt
    {A : ℝ × ℝ -> ℝ} {s t : ℝ}
    (hA : DifferentiableAt ℝ A (s, t)) :
    HasDerivAt (fun τ : ℝ => A (s, τ))
      ((fderiv ℝ A (s, t)) (0, (1 : ℝ))) t := by
  let L : ℝ -> ℝ × ℝ := fun τ => (s, τ)
  have hL : DifferentiableAt ℝ L t := by
    fun_prop
  have hcomp := (hA.hasFDerivAt.comp t hL.hasFDerivAt).hasDerivAt
  have hLderiv : (fderiv ℝ L t) 1 = (0, (1 : ℝ)) := by
    rw [DifferentiableAt.fderiv_prodMk]
    · simp
    · fun_prop
    · fun_prop
  change HasDerivAt (A ∘ L)
    ((fderiv ℝ A (s, t)) ((fderiv ℝ L t) 1)) t at hcomp
  rw [hLderiv] at hcomp
  exact hcomp

theorem fixedBaseFDerivTimeDerivativeAt_of_contDiff
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (t : ℝ) (x V : E) :
    HasDerivAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      t := by
  let G : ℝ × E -> ℝ := fun p => F p.1 p.2
  let A : ℝ × E -> ℝ := fun p => (fderiv ℝ G p) (0, V)
  let B : ℝ × E -> ℝ := fun p => (fderiv ℝ G p) (1, 0)
  have hAcont : ContDiff ℝ 1 A := by
    have hDA := hF.contDiff_fderiv_apply (m := (1 : WithTop ℕ∞)) (by norm_num)
    exact hDA.comp (contDiff_id.prodMk contDiff_const)
  have hA : DifferentiableAt ℝ A (t, x) :=
    (ContDiff.differentiable hAcont (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) (t, x)
  have h0 := model_hasDerivAt_fixed_snd (E := E) A t x hA
  have hswap :
      (fderiv ℝ A (t, x)) (1, 0) =
        (fderiv ℝ (fun y : E => B (t, y)) x) V := by
    have hlie := VectorField.fderiv_apply_lieBracket
      (𝕜 := ℝ) (E := ℝ × E) (F := ℝ)
      (f := G)
      (V := fun _ : ℝ × E => (1, 0))
      (W := fun _ : ℝ × E => (0, V))
      (x := (t, x))
      hF.contDiffAt
      (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
      (by fun_prop)
      (by fun_prop)
    have hlie' :
        (fderiv ℝ A (t, x)) (1, 0) =
          (fderiv ℝ B (t, x)) (0, V) := by
      unfold A B
      simp [VectorField.lieBracket] at hlie
      linarith
    rw [hlie']
    symm
    have hBcont : ContDiff ℝ 1 B := by
      have hDB := hF.contDiff_fderiv_apply (m := (1 : WithTop ℕ∞)) (by norm_num)
      exact hDB.comp (contDiff_id.prodMk contDiff_const)
    have hBdiff : DifferentiableAt ℝ B (t, x) :=
      (ContDiff.differentiable hBcont (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) (t, x)
    let L : E -> ℝ × E := fun y => (t, y)
    have hL : DifferentiableAt ℝ L x := by
      fun_prop
    have hcomp := fderiv_comp (𝕜 := ℝ) (x := x) (f := L) (g := B) hBdiff hL
    have hLderiv : (fderiv ℝ L x) V = (0, V) := by
      rw [DifferentiableAt.fderiv_prodMk]
      · simp
      · fun_prop
      · fun_prop
    change (fderiv ℝ (B ∘ L) x) V = (fderiv ℝ B (t, x)) (0, V)
    rw [hcomp]
    change (fderiv ℝ B (t, x)) ((fderiv ℝ L x) V) =
      (fderiv ℝ B (t, x)) (0, V)
    rw [hLderiv]
  refine (h0.congr_deriv hswap).congr_of_eventuallyEq ?_
  filter_upwards with s
  exact model_spatial_fderiv_eq (E := E) F hF s x V

theorem fixedBaseFDerivTimeDerivativeAt_of_contDiffAt
    (F : ℝ -> E -> ℝ)
    {t : ℝ} {x V : E}
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × E => F p.1 p.2) (t, x)) :
    HasDerivAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      t := by
  let G : ℝ × E -> ℝ := fun p => F p.1 p.2
  let A : ℝ × E -> ℝ := fun p => (fderiv ℝ G p) (0, V)
  let B : ℝ × E -> ℝ := fun p => (fderiv ℝ G p) (1, 0)
  have hAcont : ContDiffAt ℝ 1 A (t, x) := by
    have hDA : ContDiffAt ℝ 1 (fderiv ℝ G) (t, x) :=
      hF.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)
    exact hDA.clm_apply contDiffAt_const
  have hA : DifferentiableAt ℝ A (t, x) :=
    hAcont.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have h0 := model_hasDerivAt_fixed_snd (E := E) A t x hA
  have hswap :
      (fderiv ℝ A (t, x)) (1, 0) =
        (fderiv ℝ (fun y : E => B (t, y)) x) V := by
    have hlie := VectorField.fderiv_apply_lieBracket
      (𝕜 := ℝ) (E := ℝ × E) (F := ℝ)
      (f := G)
      (V := fun _ : ℝ × E => (1, 0))
      (W := fun _ : ℝ × E => (0, V))
      (x := (t, x))
      hF
      (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
      (by fun_prop)
      (by fun_prop)
    have hlie' :
        (fderiv ℝ A (t, x)) (1, 0) =
          (fderiv ℝ B (t, x)) (0, V) := by
      unfold A B
      simp [VectorField.lieBracket] at hlie
      linarith
    rw [hlie']
    symm
    have hBcont : ContDiffAt ℝ 1 B (t, x) := by
      have hDB : ContDiffAt ℝ 1 (fderiv ℝ G) (t, x) :=
        hF.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)
      exact hDB.clm_apply contDiffAt_const
    have hBdiff : DifferentiableAt ℝ B (t, x) :=
      hBcont.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    let L : E -> ℝ × E := fun y => (t, y)
    have hL : DifferentiableAt ℝ L x := by
      fun_prop
    have hcomp := fderiv_comp (𝕜 := ℝ) (x := x) (f := L) (g := B) hBdiff hL
    have hLderiv : (fderiv ℝ L x) V = (0, V) := by
      rw [DifferentiableAt.fderiv_prodMk]
      · simp
      · fun_prop
      · fun_prop
    change (fderiv ℝ (B ∘ L) x) V = (fderiv ℝ B (t, x)) (0, V)
    rw [hcomp]
    change (fderiv ℝ B (t, x)) ((fderiv ℝ L x) V) =
      (fderiv ℝ B (t, x)) (0, V)
    rw [hLderiv]
  refine (h0.congr_deriv hswap).congr_of_eventuallyEq ?_
  have h_event :
      ∀ᶠ s in 𝓝 t,
        ContDiffAt ℝ 2 (fun p : ℝ × E => F p.1 p.2) (s, x) :=
    by
      have hmap : ContinuousAt (fun s : ℝ => (s, x)) t := by
        fun_prop
      exact hmap.eventually
        (hF.eventually (by norm_num : (2 : WithTop ℕ∞) ≠ ∞))
  filter_upwards [h_event] with s hs
  exact model_spatial_fderiv_eq_of_contDiffAt (E := E) F hs

theorem fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    {timeSet : Set ℝ} {t : ℝ}
    (x V : E) :
    HasDerivWithinAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      timeSet
      t :=
  (fixedBaseFDerivTimeDerivativeAt_of_contDiff (E := E) F hF t x V).hasDerivWithinAt

theorem modelMix2
    {φ : ℝ × ℝ -> ℝ} {s t : ℝ}
    (hφ : ContDiffAt ℝ 2 φ (s, t)) :
    (fderiv ℝ (fun p : ℝ × ℝ => (fderiv ℝ φ p) (0, (1 : ℝ))) (s, t))
        ((1 : ℝ), 0) =
      (fderiv ℝ (fun p : ℝ × ℝ => (fderiv ℝ φ p) ((1 : ℝ), 0)) (s, t))
        (0, (1 : ℝ)) := by
  have hlie := VectorField.fderiv_apply_lieBracket
    (𝕜 := ℝ) (E := ℝ × ℝ) (F := ℝ)
    (f := φ)
    (V := fun _ : ℝ × ℝ => ((1 : ℝ), 0))
    (W := fun _ : ℝ × ℝ => (0, (1 : ℝ)))
    (x := (s, t))
    hφ
    (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞))
    (by fun_prop)
    (by fun_prop)
  simp [VectorField.lieBracket] at hlie
  linarith

theorem modelMix3
    {φ : ℝ × ℝ -> ℝ} {s t : ℝ}
    (hφ : ContDiffAt ℝ 3 φ (s, t)) :
    (fderiv ℝ
        (fun p : ℝ × ℝ =>
          (fderiv ℝ (fun q : ℝ × ℝ => (fderiv ℝ φ q) (0, (1 : ℝ))) p)
            (0, (1 : ℝ))) (s, t))
        ((1 : ℝ), 0) =
      (fderiv ℝ
        (fun p : ℝ × ℝ =>
          (fderiv ℝ (fun q : ℝ × ℝ => (fderiv ℝ φ q) (0, (1 : ℝ))) p)
            ((1 : ℝ), 0)) (s, t))
        (0, (1 : ℝ)) := by
  have hD : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => (fderiv ℝ φ q) (0, (1 : ℝ)))
      (s, t) := by
    have hfd : ContDiffAt ℝ 2 (fderiv ℝ φ) (s, t) :=
      hφ.fderiv_right (m := (2 : WithTop ℕ∞)) (by norm_num)
    exact hfd.clm_apply contDiffAt_const
  exact modelMix2 (φ := fun q : ℝ × ℝ => (fderiv ℝ φ q) (0, (1 : ℝ)))
    (s := s) (t := t) hD

end ModelMixed

end CalabiYau
