module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Harmonicity along complex lines

This module records the local calculation that identifies the Laplacian of a restriction to a
complex line with the complex trace of the real Hessian. It is a criterion used in the proof of the strong
maximum principle for pluriharmonic functions.
-/

@[expose] public section

open Complex InnerProductSpace Set

variable {n : ℕ}

/-- If the complex trace of the real Hessian vanishes along an affine complex line, then the
restriction of the function to that line is harmonic. -/
theorem harmonicOnNhd_comp_complexLine
    {f : EuclideanSpace ℂ (Fin n) → ℝ} {z v : EuclideanSpace ℂ (Fin n)}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U)
    (hline : MapsTo (fun t : ℂ ↦ z + t • v) (Metric.ball (0 : ℂ) 2) U)
    (hf : ContDiffOn ℝ 2 f U)
    (htrace : ∀ w ∈ U,
      fderiv ℝ (fderiv ℝ f) w v v +
        fderiv ℝ (fderiv ℝ f) w (I • v) (I • v) = 0) :
    InnerProductSpace.HarmonicOnNhd (fun t : ℂ ↦ f (z + t • v)) (Metric.ball (0 : ℂ) 2) := by
  intro t ht
  have htU : z + t • v ∈ U := hline ht
  refine ⟨?_, ?_⟩
  · have hfc : ContDiffAt ℝ 2 f (z + t • v) := hf.contDiffAt (hU.mem_nhds htU)
    have hlineC : ContDiff ℝ 2 (fun t : ℂ ↦ z + t • v) := by fun_prop
    exact hfc.comp t hlineC.contDiffAt
  · filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
    have hsU : z + s • v ∈ U := hline hs
    have hlap : Laplacian.laplacian (fun s : ℂ ↦ f (z + s • v)) s =
        fderiv ℝ (fderiv ℝ f) (z + s • v) v v +
          fderiv ℝ (fderiv ℝ f) (z + s • v) (I • v) (I • v) := by
      let L : ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) :=
        ((1 : ℂ →L[ℂ] ℂ).smulRight v).restrictScalars ℝ
      have hL (r : ℂ) : L r = r • v := by simp [L]
      let S : Set (EuclideanSpace ℂ (Fin n)) := (fun x ↦ z + x) ⁻¹' U
      let g : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦ f (z + x)
      have hSopen : IsOpen S := by
        apply hU.preimage
        fun_prop
      have hsS : s • v ∈ S := by simpa [S] using hsU
      have htrans : ContDiff ℝ 2 (fun x : EuclideanSpace ℂ (Fin n) ↦ z + x) := by
        fun_prop
      have hg : ContDiffOn ℝ 2 g S := by
        change ContDiffOn ℝ 2 (f ∘ (fun x : EuclideanSpace ℂ (Fin n) ↦ z + x)) S
        apply hf.comp htrans.contDiffOn
        intro x hx
        exact hx
      have hPopen : IsOpen (L ⁻¹' S) := hSopen.preimage L.continuous
      have hsP : s ∈ L ⁻¹' S := by simpa [hL] using hsS
      have hcomp : (fun r : ℂ ↦ f (z + r • v)) = g ∘ L := by
        funext r
        simp [g, hL]
      have hgAt : ContDiffAt ℝ 2 g (L s) := hg.contDiffAt (hSopen.mem_nhds hsS)
      have hLcd : ContDiff ℝ 2 (fun r : ℂ ↦ L r) := by fun_prop
      have hcompAt : ContDiffAt ℝ 2 (g ∘ L) s := hgAt.comp s hLcd.contDiffAt
      have hchain : iteratedFDerivWithin ℝ 2 (g ∘ L) (L ⁻¹' S) s =
          (iteratedFDerivWithin ℝ 2 g S (L s)).compContinuousLinearMap (fun _ ↦ L) :=
        L.iteratedFDerivWithin_comp_right hg hSopen.uniqueDiffOn hPopen.uniqueDiffOn hsS le_rfl
      rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
      change iteratedFDeriv ℝ 2 (fun r : ℂ ↦ f (z + r • v)) s ![1, 1] +
          iteratedFDeriv ℝ 2 (fun r : ℂ ↦ f (z + r • v)) s ![I, I] = _
      rw [hcomp]
      rw [← iteratedFDerivWithin_eq_iteratedFDeriv hPopen.uniqueDiffOn hcompAt hsP,
        hchain,
        iteratedFDerivWithin_eq_iteratedFDeriv hSopen.uniqueDiffOn hgAt hsS]
      simp [iteratedFDeriv_two_apply, hL, g, iteratedFDeriv_comp_add_left]
    simpa only [hlap, Pi.zero_apply] using htrace (z + s • v) hsU
