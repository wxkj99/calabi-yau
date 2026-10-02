module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetMatrixRemainder

/-!
# Pointwise comparison of pairwise log-determinant remainders

Implementation-only matrix estimates for the chartwise Hölder transfer.
The parent imports this module privately; these declarations do not extend its public API.
All norms in the estimates are Frobenius norms.
-/

@[expose] public section

open scoped ComplexOrder ContDiff NNReal Matrix.Norms.Frobenius

namespace KahlerForm

theorem logDetTaylorRemainder_sub_shift_base
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A H K : Matrix ι ι ℂ) :
    Matrix.logDetTaylorRemainder A H - Matrix.logDetTaylorRemainder A K =
      Matrix.logDetTaylorRemainder (A + K) (H - K) +
        RCLike.re (((A + K)⁻¹ - A⁻¹) * (H - K)).trace := by
  unfold Matrix.logDetTaylorRemainder
  have hmat : A + K + (H - K) = A + H := by abel
  rw [hmat]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, map_sub]
  ring

set_option maxHeartbeats 200000 in
theorem matrixDifferenceRemainder_pointwise
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M Q Δ a k d Cb Cf : ℝ)
    (Ax Ay Hx Kx Hy Ky : Matrix ι ι ℂ)
    (hQ : 0 ≤ Q) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hAx : Ax.PosDef) (hAy : Ay.PosDef)
    (hUx : (Ax + Kx).PosDef) (hUy : (Ay + Ky).PosDef)
    (hAxInv : ‖Ax⁻¹‖ ≤ M) (hAyInv : ‖Ay⁻¹‖ ≤ M)
    (hUxInv : ‖(Ax + Kx)⁻¹‖ ≤ M) (hUyInv : ‖(Ay + Ky)⁻¹‖ ≤ M)
    (hKx : ‖Kx‖ ≤ Q) (hKy : ‖Ky‖ ≤ Q)
    (hDx : ‖Hx - Kx‖ ≤ Δ)
    (hAxAy : ‖Ax - Ay‖ ≤ a) (hKxKy : ‖Kx - Ky‖ ≤ k)
    (hDxDy : ‖(Hx - Kx) - (Hy - Ky)‖ ≤ d)
    (hbase : |Matrix.logDetTaylorRemainder (Ax + Kx) (Hx - Kx) -
        Matrix.logDetTaylorRemainder (Ay + Kx) (Hx - Kx)| ≤ Cb * a * Δ ^ 2)
    (hbaseDy : |Matrix.logDetTaylorRemainder (Ay + Kx) (Hy - Ky) -
        Matrix.logDetTaylorRemainder (Ay + Ky) (Hy - Ky)| ≤ Cb * a * Δ ^ 2)
    (hfixed : |Matrix.logDetTaylorRemainder (Ay + Kx) (Hx - Kx) -
        Matrix.logDetTaylorRemainder (Ay + Kx) (Hy - Ky)| ≤ Cf * Δ * d)
    (htrace : ∀ U V : Matrix ι ι ℂ,
      |RCLike.re (U * V).trace| ≤ ‖U‖ * ‖V‖) :
    |(Matrix.logDetTaylorRemainder Ax Hx - Matrix.logDetTaylorRemainder Ax Kx) -
      (Matrix.logDetTaylorRemainder Ay Hy - Matrix.logDetTaylorRemainder Ay Ky)| ≤
      (Cb * a * Δ ^ 2 + Cf * Δ * d + Cb * a * Δ ^ 2) +
        (max 1 M) ^ 3 * (Q * (2 * a + k) + k) * Δ +
        (max 1 M) ^ 2 * Q * d := by
  let Dx := Hx - Kx
  let Dy := Hy - Ky
  let Ux := Ax + Kx
  let Uy := Ay + Ky
  let N := max 1 M
  have hN1 : 1 ≤ N := le_max_left _ _
  have hMN : M ≤ N := le_max_right _ _
  have hNnonneg : 0 ≤ N := le_trans (by norm_num) hN1
  have hAxInvN : ‖Ax⁻¹‖ ≤ N := hAxInv.trans hMN
  have hAyInvN : ‖Ay⁻¹‖ ≤ N := hAyInv.trans hMN
  have hUxInvN : ‖Ux⁻¹‖ ≤ N := by simpa [Ux] using hUxInv.trans hMN
  have hUyInvN : ‖Uy⁻¹‖ ≤ N := by simpa [Uy] using hUyInv.trans hMN
  have hUxUy : ‖Ux - Uy‖ ≤ a + k := by
    dsimp [Ux, Uy]
    calc
      ‖Ax + Kx - (Ay + Ky)‖ = ‖(Ax - Ay) + (Kx - Ky)‖ := by
        have hmat : Ax + Kx - (Ay + Ky) = (Ax - Ay) + (Kx - Ky) := by abel
        rw [hmat]
      _ ≤ ‖Ax - Ay‖ + ‖Kx - Ky‖ := norm_add_le _ _
      _ ≤ a + k := add_le_add hAxAy hKxKy
  have hUxPD : Ux.PosDef := hUx
  have hUxVx : IsUnit Ux.det := (ne_of_gt hUxPD.det_pos).isUnit
  have hAxU : IsUnit Ax.det := (ne_of_gt hAx.det_pos).isUnit
  have hUyPD : Uy.PosDef := hUy
  have hUyV : IsUnit Uy.det := (ne_of_gt hUyPD.det_pos).isUnit
  have hAyU : IsUnit Ay.det := (ne_of_gt hAy.det_pos).isUnit
  have hE0 : Ux⁻¹ - Ax⁻¹ = -(Ax⁻¹ * Kx * Ux⁻¹) := by
    have hInv : Ax⁻¹ - Ux⁻¹ = Ax⁻¹ * (Ux - Ax) * Ux⁻¹ := by
      calc
        Ax⁻¹ - Ux⁻¹ = Ax⁻¹ * (Ux * Ux⁻¹) - (Ax⁻¹ * Ax) * Ux⁻¹ := by
          rw [Matrix.mul_nonsing_inv Ux hUxVx, Matrix.nonsing_inv_mul Ax hAxU]
          simp
        _ = Ax⁻¹ * (Ux - Ax) * Ux⁻¹ := by noncomm_ring
    have hdiff : Ux - Ax = Kx := by dsimp [Ux]; abel
    rw [hdiff] at hInv
    calc
      Ux⁻¹ - Ax⁻¹ = -(Ax⁻¹ - Ux⁻¹) := by abel
      _ = -(Ax⁻¹ * Kx * Ux⁻¹) := by rw [hInv]
  have hE1 : Uy⁻¹ - Ay⁻¹ = -(Ay⁻¹ * Ky * Uy⁻¹) := by
    have hInv : Ay⁻¹ - Uy⁻¹ = Ay⁻¹ * (Uy - Ay) * Uy⁻¹ := by
      calc
        Ay⁻¹ - Uy⁻¹ = Ay⁻¹ * (Uy * Uy⁻¹) - (Ay⁻¹ * Ay) * Uy⁻¹ := by
          rw [Matrix.mul_nonsing_inv Uy hUyV, Matrix.nonsing_inv_mul Ay hAyU]
          simp
        _ = Ay⁻¹ * (Uy - Ay) * Uy⁻¹ := by noncomm_ring
    have hdiff : Uy - Ay = Ky := by dsimp [Uy]; abel
    rw [hdiff] at hInv
    calc
      Uy⁻¹ - Ay⁻¹ = -(Ay⁻¹ - Uy⁻¹) := by abel
      _ = -(Ay⁻¹ * Ky * Uy⁻¹) := by rw [hInv]
  have hAiAy : Ax⁻¹ - Ay⁻¹ = Ax⁻¹ * (Ay - Ax) * Ay⁻¹ := by
    have h := Matrix.nonsing_inv_mul Ax hAxU
    have h' := Matrix.mul_nonsing_inv Ay hAyU
    calc
      Ax⁻¹ - Ay⁻¹ = Ax⁻¹ * (Ay * Ay⁻¹) - (Ax⁻¹ * Ax) * Ay⁻¹ := by rw [h', h]; simp
      _ = Ax⁻¹ * (Ay - Ax) * Ay⁻¹ := by noncomm_ring
  have hUiUy : Ux⁻¹ - Uy⁻¹ = Ux⁻¹ * (Uy - Ux) * Uy⁻¹ := by
    have h := Matrix.nonsing_inv_mul Ux hUxVx
    have h' := Matrix.mul_nonsing_inv Uy hUyV
    calc
      Ux⁻¹ - Uy⁻¹ = Ux⁻¹ * (Uy * Uy⁻¹) - (Ux⁻¹ * Ux) * Uy⁻¹ := by rw [h', h]; simp
      _ = Ux⁻¹ * (Uy - Ux) * Uy⁻¹ := by noncomm_ring
  have hnormInvA : ‖Ax⁻¹ - Ay⁻¹‖ ≤ N ^ 2 * a := by
    rw [hAiAy]
    calc
      ‖Ax⁻¹ * (Ay - Ax) * Ay⁻¹‖ ≤ ‖Ax⁻¹‖ * ‖Ay - Ax‖ * ‖Ay⁻¹‖ := by
        calc
          _ ≤ ‖Ax⁻¹ * (Ay - Ax)‖ * ‖Ay⁻¹‖ := Matrix.frobenius_norm_mul _ _
          _ ≤ (‖Ax⁻¹‖ * ‖Ay - Ax‖) * ‖Ay⁻¹‖ := by
            gcongr
            exact Matrix.frobenius_norm_mul _ _
      _ ≤ N * a * N := by
        have hnormrev : ‖Ay - Ax‖ = ‖Ax - Ay‖ := norm_sub_rev _ _
        rw [hnormrev]
        exact mul_le_mul
          (mul_le_mul hAxInvN hAxAy (norm_nonneg _) hNnonneg) hAyInvN
          (by positivity) (mul_nonneg hNnonneg ha)
      _ = N ^ 2 * a := by ring
  have hnormInvU : ‖Ux⁻¹ - Uy⁻¹‖ ≤ N ^ 2 * (a + k) := by
    rw [hUiUy]
    calc
      ‖Ux⁻¹ * (Uy - Ux) * Uy⁻¹‖ ≤ ‖Ux⁻¹‖ * ‖Uy - Ux‖ * ‖Uy⁻¹‖ := by
        calc
          _ ≤ ‖Ux⁻¹ * (Uy - Ux)‖ * ‖Uy⁻¹‖ := Matrix.frobenius_norm_mul _ _
          _ ≤ (‖Ux⁻¹‖ * ‖Uy - Ux‖) * ‖Uy⁻¹‖ := by
            gcongr
            exact Matrix.frobenius_norm_mul _ _
      _ ≤ N * (a + k) * N := by
        have hnormrev : ‖Uy - Ux‖ = ‖Ux - Uy‖ := norm_sub_rev _ _
        rw [hnormrev]
        exact mul_le_mul
          (mul_le_mul hUxInvN hUxUy (norm_nonneg _) hNnonneg) hUyInvN
          (by positivity) (mul_nonneg hNnonneg (add_nonneg ha hk))
      _ = N ^ 2 * (a + k) := by ring
  have hEdiff : ‖(Ux⁻¹ - Ax⁻¹) - (Uy⁻¹ - Ay⁻¹)‖ ≤
      N ^ 3 * (Q * (2 * a + k) + k) := by
    have hEdiffEq : (Ux⁻¹ - Ax⁻¹) - (Uy⁻¹ - Ay⁻¹) =
        -(Ax⁻¹ * Kx * Ux⁻¹ - Ay⁻¹ * Ky * Uy⁻¹) := by
      rw [hE0, hE1]
      noncomm_ring
    rw [hEdiffEq, norm_neg]
    calc
      ‖Ax⁻¹ * Kx * Ux⁻¹ - Ay⁻¹ * Ky * Uy⁻¹‖ ≤
          ‖(Ax⁻¹ - Ay⁻¹) * Kx * Ux⁻¹‖ +
            ‖Ay⁻¹ * (Kx - Ky) * Ux⁻¹‖ +
            ‖Ay⁻¹ * Ky * (Ux⁻¹ - Uy⁻¹)‖ := by
        have hfactor : Ax⁻¹ * Kx * Ux⁻¹ - Ay⁻¹ * Ky * Uy⁻¹ =
            (Ax⁻¹ - Ay⁻¹) * Kx * Ux⁻¹ + Ay⁻¹ * (Kx - Ky) * Ux⁻¹ +
              Ay⁻¹ * Ky * (Ux⁻¹ - Uy⁻¹) := by noncomm_ring
        rw [hfactor]
        calc
          _ ≤ ‖(Ax⁻¹ - Ay⁻¹) * Kx * Ux⁻¹ + Ay⁻¹ * (Kx - Ky) * Ux⁻¹‖ +
              ‖Ay⁻¹ * Ky * (Ux⁻¹ - Uy⁻¹)‖ := norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ (N ^ 2 * a * Q * N) + (N * k * N) + (N * Q * (N ^ 2 * (a + k))) := by
        apply add_le_add
        · apply add_le_add
          · calc
              ‖(Ax⁻¹ - Ay⁻¹) * Kx * Ux⁻¹‖ ≤
                  ‖Ax⁻¹ - Ay⁻¹‖ * ‖Kx‖ * ‖Ux⁻¹‖ := by
                calc
                  _ ≤ ‖(Ax⁻¹ - Ay⁻¹) * Kx‖ * ‖Ux⁻¹‖ := Matrix.frobenius_norm_mul _ _
                  _ ≤ (‖Ax⁻¹ - Ay⁻¹‖ * ‖Kx‖) * ‖Ux⁻¹‖ := by
                    gcongr
                    exact Matrix.frobenius_norm_mul _ _
              _ ≤ N ^ 2 * a * Q * N := by gcongr
          · calc
              ‖Ay⁻¹ * (Kx - Ky) * Ux⁻¹‖ ≤
                  ‖Ay⁻¹‖ * ‖Kx - Ky‖ * ‖Ux⁻¹‖ := by
                calc
                  _ ≤ ‖Ay⁻¹ * (Kx - Ky)‖ * ‖Ux⁻¹‖ := Matrix.frobenius_norm_mul _ _
                  _ ≤ (‖Ay⁻¹‖ * ‖Kx - Ky‖) * ‖Ux⁻¹‖ := by
                    gcongr
                    exact Matrix.frobenius_norm_mul _ _
              _ ≤ N * k * N := by gcongr
        · calc
            ‖Ay⁻¹ * Ky * (Ux⁻¹ - Uy⁻¹)‖ ≤
                ‖Ay⁻¹‖ * ‖Ky‖ * ‖Ux⁻¹ - Uy⁻¹‖ := by
              calc
                _ ≤ ‖Ay⁻¹ * Ky‖ * ‖Ux⁻¹ - Uy⁻¹‖ := Matrix.frobenius_norm_mul _ _
                _ ≤ (‖Ay⁻¹‖ * ‖Ky‖) * ‖Ux⁻¹ - Uy⁻¹‖ := by
                  gcongr
                  exact Matrix.frobenius_norm_mul _ _
            _ ≤ N * Q * (N ^ 2 * (a + k)) := by gcongr
      _ ≤ N ^ 3 * (Q * (2 * a + k) + k) := by
        have hkN : N ^ 2 * k ≤ N ^ 3 * k := by
          have hpow : N ^ 2 ≤ N ^ 3 := by nlinarith [sq_nonneg (N - 1)]
          exact mul_le_mul_of_nonneg_right hpow hk
        nlinarith [hkN]
  have hE1norm : ‖Uy⁻¹ - Ay⁻¹‖ ≤ N ^ 2 * Q := by
    rw [hE1]
    calc
      ‖-(Ay⁻¹ * Ky * Uy⁻¹)‖ ≤ ‖Ay⁻¹‖ * ‖Ky‖ * ‖Uy⁻¹‖ := by
        rw [norm_neg]
        calc
          ‖Ay⁻¹ * Ky * Uy⁻¹‖ ≤ ‖Ay⁻¹ * Ky‖ * ‖Uy⁻¹‖ := Matrix.frobenius_norm_mul _ _
          _ ≤ (‖Ay⁻¹‖ * ‖Ky‖) * ‖Uy⁻¹‖ := by
            gcongr
            exact Matrix.frobenius_norm_mul _ _
      _ ≤ N * Q * N := by gcongr
      _ = N ^ 2 * Q := by ring
  have htraceDiff :
      |RCLike.re ((Ux⁻¹ - Ax⁻¹) * Dx).trace -
        RCLike.re ((Uy⁻¹ - Ay⁻¹) * Dy).trace| ≤
        N ^ 3 * (Q * (2 * a + k) + k) * Δ + N ^ 2 * Q * d := by
    have hdecomp :
        RCLike.re ((Ux⁻¹ - Ax⁻¹) * Dx).trace -
          RCLike.re ((Uy⁻¹ - Ay⁻¹) * Dy).trace =
          RCLike.re (((Ux⁻¹ - Ax⁻¹) - (Uy⁻¹ - Ay⁻¹)) * Dx).trace +
            RCLike.re ((Uy⁻¹ - Ay⁻¹) * (Dx - Dy)).trace := by
      simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, map_sub]
    rw [hdecomp]
    calc
      |RCLike.re (((Ux⁻¹ - Ax⁻¹) - (Uy⁻¹ - Ay⁻¹)) * Dx).trace +
          RCLike.re ((Uy⁻¹ - Ay⁻¹) * (Dx - Dy)).trace| ≤
          |RCLike.re (((Ux⁻¹ - Ax⁻¹) - (Uy⁻¹ - Ay⁻¹)) * Dx).trace| +
            |RCLike.re ((Uy⁻¹ - Ay⁻¹) * (Dx - Dy)).trace| := abs_add_le _ _
      _ ≤ ‖(Ux⁻¹ - Ax⁻¹) - (Uy⁻¹ - Ay⁻¹)‖ * ‖Dx‖ +
          ‖Uy⁻¹ - Ay⁻¹‖ * ‖Dx - Dy‖ := by
        exact add_le_add (htrace _ _) (htrace _ _)
      _ ≤ N ^ 3 * (Q * (2 * a + k) + k) * Δ + N ^ 2 * Q * d := by
        exact add_le_add
          (mul_le_mul hEdiff hDx (norm_nonneg _) (by positivity))
          (mul_le_mul hE1norm hDxDy (norm_nonneg _) (by positivity))
  have hrem :
      |(Matrix.logDetTaylorRemainder Ux Dx - Matrix.logDetTaylorRemainder Uy Dy)| ≤
        Cb * a * Δ ^ 2 + Cf * Δ * d + Cb * a * Δ ^ 2 := by
    have hEq : Matrix.logDetTaylorRemainder Ux Dx - Matrix.logDetTaylorRemainder Uy Dy =
        (Matrix.logDetTaylorRemainder Ux Dx - Matrix.logDetTaylorRemainder (Ay + Kx) Dx) +
        (Matrix.logDetTaylorRemainder (Ay + Kx) Dx - Matrix.logDetTaylorRemainder (Ay + Kx) Dy) +
        (Matrix.logDetTaylorRemainder (Ay + Kx) Dy - Matrix.logDetTaylorRemainder Uy Dy) := by ring
    rw [hEq]
    have hlast : |Matrix.logDetTaylorRemainder (Ay + Kx) Dy -
        Matrix.logDetTaylorRemainder Uy Dy| ≤ Cb * a * Δ ^ 2 := by
      simpa [Uy, Dy] using hbaseDy
    have hfirst : |Matrix.logDetTaylorRemainder Ux Dx -
        Matrix.logDetTaylorRemainder (Ay + Kx) Dx| ≤ Cb * a * Δ ^ 2 := by
      simpa [Ux, Dx] using hbase
    have hmiddle : |Matrix.logDetTaylorRemainder (Ay + Kx) Dx -
        Matrix.logDetTaylorRemainder (Ay + Kx) Dy| ≤ Cf * Δ * d := by
      simpa [Dx, Dy] using hfixed
    calc
      |(Matrix.logDetTaylorRemainder Ux Dx - Matrix.logDetTaylorRemainder (Ay + Kx) Dx) +
          (Matrix.logDetTaylorRemainder (Ay + Kx) Dx - Matrix.logDetTaylorRemainder (Ay + Kx) Dy) +
          (Matrix.logDetTaylorRemainder (Ay + Kx) Dy - Matrix.logDetTaylorRemainder Uy Dy)| ≤
          |Matrix.logDetTaylorRemainder Ux Dx - Matrix.logDetTaylorRemainder (Ay + Kx) Dx| +
          |Matrix.logDetTaylorRemainder (Ay + Kx) Dx - Matrix.logDetTaylorRemainder (Ay + Kx) Dy| +
          |Matrix.logDetTaylorRemainder (Ay + Kx) Dy - Matrix.logDetTaylorRemainder Uy Dy| := by
        calc
          _ ≤ |Matrix.logDetTaylorRemainder Ux Dx - Matrix.logDetTaylorRemainder (Ay + Kx) Dx +
              (Matrix.logDetTaylorRemainder (Ay + Kx) Dx - Matrix.logDetTaylorRemainder (Ay + Kx) Dy)| +
              |Matrix.logDetTaylorRemainder (Ay + Kx) Dy - Matrix.logDetTaylorRemainder Uy Dy| :=
                abs_add_le _ _
          _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ Cb * a * Δ ^ 2 + Cf * Δ * d + Cb * a * Δ ^ 2 :=
        add_le_add (add_le_add hfirst hmiddle) hlast
  have hfinalId :
      (Matrix.logDetTaylorRemainder Ax Hx - Matrix.logDetTaylorRemainder Ax Kx) -
        (Matrix.logDetTaylorRemainder Ay Hy - Matrix.logDetTaylorRemainder Ay Ky) =
        (Matrix.logDetTaylorRemainder Ux Dx - Matrix.logDetTaylorRemainder Uy Dy) +
          (RCLike.re ((Ux⁻¹ - Ax⁻¹) * Dx).trace -
            RCLike.re ((Uy⁻¹ - Ay⁻¹) * Dy).trace) := by
    rw [logDetTaylorRemainder_sub_shift_base Ax Hx Kx,
      logDetTaylorRemainder_sub_shift_base Ay Hy Ky]
    simp [Dx, Dy, Ux, Uy]
    ring
  rw [hfinalId]
  calc
    |(Matrix.logDetTaylorRemainder Ux Dx - Matrix.logDetTaylorRemainder Uy Dy) +
        (RCLike.re ((Ux⁻¹ - Ax⁻¹) * Dx).trace -
          RCLike.re ((Uy⁻¹ - Ay⁻¹) * Dy).trace)| ≤
        |Matrix.logDetTaylorRemainder Ux Dx - Matrix.logDetTaylorRemainder Uy Dy| +
          |RCLike.re ((Ux⁻¹ - Ax⁻¹) * Dx).trace -
            RCLike.re ((Uy⁻¹ - Ay⁻¹) * Dy).trace| := abs_add_le _ _
    _ ≤ (Cb * a * Δ ^ 2 + Cf * Δ * d + Cb * a * Δ ^ 2) +
        ((max 1 M) ^ 3 * (Q * (2 * a + k) + k) * Δ +
          (max 1 M) ^ 2 * Q * d) := add_le_add hrem htraceDiff
    _ = (Cb * a * Δ ^ 2 + Cf * Δ * d + Cb * a * Δ ^ 2) +
        (max 1 M) ^ 3 * (Q * (2 * a + k) + k) * Δ +
        (max 1 M) ^ 2 * Q * d := by ring

end KahlerForm
