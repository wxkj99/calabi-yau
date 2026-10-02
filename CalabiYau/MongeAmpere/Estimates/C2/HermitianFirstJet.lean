module

public import CalabiYau.Geometry.Kahler.Laplacian.Cofactor
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Star

@[expose] public section

open scoped Matrix.Norms.Elementwise
open Filter Topology

namespace Matrix

/-- A Hermitian matrix-valued germ with vanishing holomorphic first jets has vanishing full real
Fréchet derivative. The Hermitian germ identifies the conjugate of each transposed entry's
Wirtinger equation with the complementary antiholomorphic equation. -/
theorem fderiv_eq_zero_of_eventually_isHermitian_of_partialZ_eq_zero
    {n : ℕ}
    (G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n))
    (hG : DifferentiableAt ℝ G z)
    (hHermitian : ∀ᶠ w in 𝓝 z, (G w).IsHermitian)
    (hFirst : ∀ p j k : Fin n,
      KahlerForm.chartPartialZComplex (fun w ↦ G w j k) z p = 0) :
    fderiv ℝ G z = 0 := by
  classical
  have hRowDiff (j : Fin n) : DifferentiableAt ℝ (fun w ↦ G w j) z :=
    (differentiableAt_pi.1 hG) j
  have hEntryDiff (j k : Fin n) : DifferentiableAt ℝ (fun w ↦ G w j k) z :=
    (differentiableAt_pi.1 (hRowDiff j)) k
  have hD (j k : Fin n) (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ G w j k) z d = (fderiv ℝ G z d) j k := by
    rw [fderiv_apply (hRowDiff j) k, fderiv_apply hG j]
    rfl
  have hHermEntry (j k : Fin n) :
      (fun w ↦ G w j k) =ᶠ[𝓝 z] (fun w ↦ star (G w k j)) := by
    filter_upwards [hHermitian] with w hw
    exact (hw.apply j k).symm
  have hHermDeriv (j k : Fin n) (d : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun w ↦ G w j k) z d = star (fderiv ℝ (fun w ↦ G w k j) z d) := by
    have heq := (hHermEntry j k).fderiv_eq (𝕜 := ℝ) (x := z)
    have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L d) heq
    rw [fderiv_star, ContinuousLinearMap.comp_apply] at h
    have hstar (x : ℂ) : ((starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap) x = star x := by rfl
    simpa only [hstar] using h
  have hA (p j k : Fin n) :
      fderiv ℝ (fun w ↦ G w j k) z (EuclideanSpace.single p 1) = 0 := by
    have hp := hFirst p j k
    have hq := hFirst p k j
    dsimp [KahlerForm.chartPartialZComplex] at hp hq
    have hrel1 := hHermDeriv j k (EuclideanSpace.single p 1)
    have hrel2 := hHermDeriv j k (Complex.I • EuclideanSpace.single p 1)
    change fderiv ℝ (fun w ↦ G w j k) z (EuclideanSpace.single p 1) =
      (starRingEnd ℂ) (fderiv ℝ (fun w ↦ G w k j) z (EuclideanSpace.single p 1)) at hrel1
    change fderiv ℝ (fun w ↦ G w j k) z (Complex.I • EuclideanSpace.single p 1) =
      (starRingEnd ℂ) (fderiv ℝ (fun w ↦ G w k j) z (Complex.I • EuclideanSpace.single p 1)) at hrel2
    have hp' :
        (fderiv ℝ (fun w ↦ G w j k) z (EuclideanSpace.single p 1) -
          Complex.I * fderiv ℝ (fun w ↦ G w j k) z (Complex.I • EuclideanSpace.single p 1)) / 2 = 0 := by
      simpa only [hD] using hp
    let A : ℂ := fderiv ℝ (fun w ↦ G w j k) z (EuclideanSpace.single p 1)
    let B : ℂ := fderiv ℝ (fun w ↦ G w j k) z (Complex.I • EuclideanSpace.single p 1)
    have hs : A - Complex.I * B = 0 := by
      have h := congrArg (fun x : ℂ ↦ 2 * x) hp'
      field_simp at h
      simpa [A, B] using h
    have ht : A + Complex.I * B = 0 := by
      have h := congrArg star hq
      simp at h
      rw [← hrel1, ← hrel2] at h
      field_simp at h
      simpa [A, B] using h
    have hsum : 2 * A = 0 := by linear_combination hs + ht
    exact (mul_eq_zero.mp hsum).resolve_left (by norm_num)
  have hB (p j k : Fin n) :
      fderiv ℝ (fun w ↦ G w j k) z (Complex.I • EuclideanSpace.single p 1) = 0 := by
    have hp := hFirst p j k
    have hq := hFirst p k j
    dsimp [KahlerForm.chartPartialZComplex] at hp hq
    have hrel1 := hHermDeriv j k (EuclideanSpace.single p 1)
    have hrel2 := hHermDeriv j k (Complex.I • EuclideanSpace.single p 1)
    change fderiv ℝ (fun w ↦ G w j k) z (EuclideanSpace.single p 1) =
      (starRingEnd ℂ) (fderiv ℝ (fun w ↦ G w k j) z (EuclideanSpace.single p 1)) at hrel1
    change fderiv ℝ (fun w ↦ G w j k) z (Complex.I • EuclideanSpace.single p 1) =
      (starRingEnd ℂ) (fderiv ℝ (fun w ↦ G w k j) z (Complex.I • EuclideanSpace.single p 1)) at hrel2
    have hp' :
        (fderiv ℝ (fun w ↦ G w j k) z (EuclideanSpace.single p 1) -
          Complex.I * fderiv ℝ (fun w ↦ G w j k) z (Complex.I • EuclideanSpace.single p 1)) / 2 = 0 := by
      simpa only [hD] using hp
    let A : ℂ := fderiv ℝ (fun w ↦ G w j k) z (EuclideanSpace.single p 1)
    let B : ℂ := fderiv ℝ (fun w ↦ G w j k) z (Complex.I • EuclideanSpace.single p 1)
    have hs : A - Complex.I * B = 0 := by
      have h := congrArg (fun x : ℂ ↦ 2 * x) hp'
      field_simp at h
      simpa [A, B] using h
    have ht : A + Complex.I * B = 0 := by
      have h := congrArg star hq
      simp at h
      rw [← hrel1, ← hrel2] at h
      field_simp at h
      simpa [A, B] using h
    have hdiff : 2 * Complex.I * B = 0 := by
      calc
        2 * Complex.I * B = (A + Complex.I * B) - (A - Complex.I * B) := by ring
        _ = 0 := by rw [ht, hs]; ring
    exact (mul_eq_zero.mp hdiff).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  apply ContinuousLinearMap.ext
  intro d
  apply Matrix.ext
  intro j k
  change (fderiv ℝ G z d) j k = 0
  rw [← hD]
  have hd : d = ∑ p : Fin n,
      ((d p).re • PiLp.single 2 p 1 + (d p).im • (Complex.I • PiLp.single 2 p 1)) := by
    ext p
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply]
    change d.ofLp p = ∑ c : Fin n,
      ((d.ofLp c).re • (PiLp.single 2 c (1 : ℂ) : EuclideanSpace ℂ (Fin n)) p +
        (d.ofLp c).im • Complex.I • (PiLp.single 2 c (1 : ℂ) : EuclideanSpace ℂ (Fin n)) p)
    simp only [PiLp.single_apply]
    rw [Finset.sum_add_distrib]
    simp [smul_ite, mul_one, mul_zero]
  rw [hd]
  simp only [map_sum, map_add, map_smul]
  simp [hA, hB]

end Matrix
