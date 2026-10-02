module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import CalabiYau.Geometry.Kahler.MatrixInverse
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.InverseHolder

/-!
# Uniform Hölder bounds of inverse matrix coefficient jets

Assume a common norm bound for the inverse jets. The bounded bilinear product estimate,
together with Mathlib's inverse derivative and finite Leibniz convolution, gives the required
Hölder bounds. The two-term telescope is
`B(f x, g x) - B(f y, g y) = B(f x, g x - g y) + B(f x - f y, g y)`.
Use translated germs and `iteratedFDeriv_comp_add_left` to apply the same telescope to jets.

Starting with the resolvent bound `T₀ = n² * N² * C`, induction through the scalar-times-CLM
inverse derivative gives the next bound `n² * 4^m * C * (N² + 2 * N * Tₘ)`.
Taking a maximum retains all lower Hölder bounds. In particular this argument compares points
of arbitrary `K` directly, rather than integrating along a segment that might leave `W`.
-/

open scoped ContDiff NNReal

namespace KahlerForm

private theorem holder_norm_probe {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C α : ℝ≥0} {f : X → Y} {K : Set X} {x y : X}
    (h : HolderOnWith C α f K) (hx : x ∈ K) (hy : y ∈ K) :
    ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
  have hh := h x hx y hy
  rw [edist_dist, dist_eq_norm] at hh
  have hpow : (ENNReal.ofReal (dist x y)) ^ (α : ℝ) =
      ENNReal.ofReal (dist x y ^ (α : ℝ)) :=
    ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) (NNReal.coe_nonneg α)
  rw [edist_dist, hpow, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

private theorem matrix_inverse_resolvent
    {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsUnit X) (hY : IsUnit Y) :
    X⁻¹ - Y⁻¹ = X⁻¹ * (Y - X) * Y⁻¹ := by
  have hXd : IsUnit X.det := X.isUnit_iff_isUnit_det.mp hX
  have hYd : IsUnit Y.det := Y.isUnit_iff_isUnit_det.mp hY
  have hXi : X⁻¹ * X = 1 := X.nonsing_inv_mul hXd
  have hYi : Y * Y⁻¹ = 1 := Y.mul_nonsing_inv hYd
  calc
    X⁻¹ - Y⁻¹ = X⁻¹ * (Y * Y⁻¹) - (X⁻¹ * X) * Y⁻¹ := by
      rw [hYi, hXi, mul_one, one_mul]
    _ = X⁻¹ * (Y - X) * Y⁻¹ := by noncomm_ring

private theorem matrix_inverse_resolvent_entry
    {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ)
    (hX : IsUnit X) (hY : IsUnit Y) (i j : Fin n) :
    (X⁻¹) i j - (Y⁻¹) i j =
      ∑ a : Fin n, ∑ b : Fin n, (X⁻¹) i a * (Y - X) a b * (Y⁻¹) b j := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j)
    (matrix_inverse_resolvent X Y hX hY)
  change (X⁻¹ - Y⁻¹) i j = _ at h
  rw [Matrix.sub_apply] at h
  simp only [Matrix.mul_apply] at h
  simp only [Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  simpa [mul_assoc] using h

private theorem product_iterated_jet_bound_real
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {C D : ℝ} {W K : Set E}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hW : IsOpen W) (hKW : K ⊆ W)
    (f g : E → ℂ)
    (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
    (hfBound : ∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m f z‖ ≤ C)
    (hgBound : ∀ m ≤ k, ∀ z ∈ K, ‖iteratedFDeriv ℝ m g z‖ ≤ D) :
    ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ f z * g z) z‖ ≤ (2 : ℝ) ^ k * C * D := by
  intro m hm z hz
  have hWz : z ∈ W := hKW hz
  have hNatLeInf (r : ℕ) : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (le_top : (r : ℕ∞) ≤ (⊤ : ℕ∞))
  have hAtF : ContDiffAt ℝ ∞ f z :=
    (hf.contDiffWithinAt hWz).contDiffAt (hW.mem_nhds hWz)
  have hAtG : ContDiffAt ℝ ∞ g z :=
    (hg.contDiffWithinAt hWz).contDiffAt (hW.mem_nhds hWz)
  have hmul := norm_iteratedFDerivWithin_mul_le hf hg hW.uniqueDiffOn hWz
    (hNatLeInf m)
  have hleft (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDerivWithin ℝ i f W z‖ ≤ C := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn
      (hAtF.of_le (hNatLeInf i)) hWz]
    exact hfBound i (le_trans hi hm) z hz
  have hright (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDerivWithin ℝ i g W z‖ ≤ D := by
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn
      (hAtG.of_le (hNatLeInf i)) hWz]
    exact hgBound i (le_trans hi hm) z hz
  have hsum :
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f W z‖ *
        ‖iteratedFDerivWithin ℝ (m - i) g W z‖ ≤
      (2 : ℝ) ^ m * C * D := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * C * D := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hmi : m - i ≤ m := Nat.sub_le _ _
        calc
          (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f W z‖ *
              ‖iteratedFDerivWithin ℝ (m - i) g W z‖ ≤
              (m.choose i : ℝ) * C *
                ‖iteratedFDerivWithin ℝ (m - i) g W z‖ := by
            gcongr
            exact hleft i hi'
          _ ≤ (m.choose i : ℝ) * C * D := by
            exact mul_le_mul_of_nonneg_left (hright (m - i) hmi) (by positivity)
      _ = (2 : ℝ) ^ m * C * D := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hchoose :
            (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ)) = (2 : ℝ) ^ m := by
          norm_cast
          exact Nat.sum_range_choose m
        rw [hchoose]
  have hbound : ‖iteratedFDerivWithin ℝ m (fun z ↦ f z * g z) W z‖ ≤
      (2 : ℝ) ^ k * C * D := by
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f W z‖ *
          ‖iteratedFDerivWithin ℝ (m - i) g W z‖ := hmul
      _ ≤ (2 : ℝ) ^ m * C * D := hsum
      _ ≤ (2 : ℝ) ^ k * C * D := by
        gcongr
        norm_num
  have hAtProd : ContDiffAt ℝ ∞ (fun z ↦ f z * g z) z :=
    ((hf.mul hg).contDiffWithinAt hWz).contDiffAt (hW.mem_nhds hWz)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn
    (hAtProd.of_le (hNatLeInf m)) hWz] at hbound
  exact hbound

/-- Common bounds on input jets and their Hölder seminorms, together with a common norm bound
on inverse jets, give ONE finite Hölder constant for every inverse jet through order `k`.
All lower input Hölder bounds are explicit, not inferred from convexity of the comparison set. -/
@[deprecated "unused hypotheses `hα₀`, `hα₁`, and `hAJet`; will be removed" (since := "2026-10-02")]
public theorem exists_holderConstantOn_matrix_inverse_entry_jets
    {P E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k : ℕ} {α C N : ℝ≥0} {W K : Set E}
    (S : Set P) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hW : IsOpen W) (hKW : K ⊆ W)
    (A : P → E → Matrix (Fin n) (Fin n) ℂ)
    (hASmooth : ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ A p z i j) W)
    (hAJet : ∀ p ∈ S, ∀ i j, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ A p z i j) z‖ ≤ C)
    (hAHolder : ∀ p ∈ S, ∀ i j, ∀ m ≤ k,
      HolderOnWith C α (iteratedFDeriv ℝ m (fun z ↦ A p z i j)) K)
    (hUnit : ∀ p ∈ S, ∀ z ∈ W, IsUnit (A p z))
    (hInvJet : ∀ p ∈ S, ∀ i j, ∀ m ≤ k, ∀ z ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j) z‖ ≤ N) :
    ∃ H : ℝ≥0, ∀ p ∈ S, ∀ i j, ∀ m ≤ k,
      HolderOnWith H α (iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j)) K := by
  let H : ℝ≥0 := (n : ℝ≥0) ^ 2 * ((2 : ℝ≥0) ^ k) ^ 2 * N ^ 2 * C
  refine ⟨H, ?_⟩
  intro p hp i j m hm x hx y hy
  have hxW : x ∈ W := hKW hx
  have hyW : y ∈ W := hKW hy
  let U : Set E := (fun z : E ↦ x + z) ⁻¹' W ∩ (fun z : E ↦ y + z) ⁻¹' W
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact hW.preimage (continuous_const.add continuous_id)
    · exact hW.preimage (continuous_const.add continuous_id)
  have hU0 : (0 : E) ∈ U := by
    simp [U, hxW, hyW]
  have hU0sub : ({0} : Set E) ⊆ U := by
    intro z hz
    simpa [Set.mem_singleton_iff.mp hz] using hU0
  have htrX : ContDiffOn ℝ ∞ (fun z : E ↦ x + z) U := by
    simpa using (contDiffOn_const.add (contDiffOn_id : ContDiffOn ℝ ∞ (id : E → E) U))
  have htrY : ContDiffOn ℝ ∞ (fun z : E ↦ y + z) U := by
    simpa using (contDiffOn_const.add (contDiffOn_id : ContDiffOn ℝ ∞ (id : E → E) U))
  have hInvSmooth : ∀ a b : Fin n, ContDiffOn ℝ ∞
      (fun z : E ↦ (A p z)⁻¹ a b) W := by
    intro a b
    exact Matrix.contDiffOn_inverse_entries (hASmooth p hp)
      (fun z hz ↦ hUnit p hp z hz) a b
  let f (a : Fin n) : E → ℂ := fun z ↦ (A p (x + z))⁻¹ i a
  let g (a b : Fin n) : E → ℂ := fun z ↦ A p (y + z) a b - A p (x + z) a b
  let q (b : Fin n) : E → ℂ := fun z ↦ (A p (y + z))⁻¹ b j
  let term (ab : Fin n × Fin n) : E → ℂ :=
    fun z ↦ f ab.1 z * g ab.1 ab.2 z * q ab.2 z
  let rhs : E → ℂ := fun z ↦ ∑ ab : Fin n × Fin n, term ab z
  have hf : ∀ a, ContDiffOn ℝ ∞ (f a) U := by
    intro a
    exact (hInvSmooth i a).comp htrX (fun z hz ↦ hz.1)
  have hq : ∀ b, ContDiffOn ℝ ∞ (q b) U := by
    intro b
    exact (hInvSmooth b j).comp htrY (fun z hz ↦ hz.2)
  have hAshiftX : ∀ a b, ContDiffOn ℝ ∞ (fun z : E ↦ A p (x + z) a b) U := by
    intro a b
    exact (hASmooth p hp a b).comp htrX (fun z hz ↦ hz.1)
  have hAshiftY : ∀ a b, ContDiffOn ℝ ∞ (fun z : E ↦ A p (y + z) a b) U := by
    intro a b
    exact (hASmooth p hp a b).comp htrY (fun z hz ↦ hz.2)
  have hg : ∀ a b, ContDiffOn ℝ ∞ (g a b) U := by
    intro a b
    exact (hAshiftY a b).sub (hAshiftX a b)
  have hTermOn : ∀ ab, ContDiffOn ℝ ∞ (term ab) U := by
    intro ab
    dsimp [term]
    exact ((hf ab.1).mul (hg ab.1 ab.2)).mul (hq ab.2)
  have hRhsOn : ContDiffOn ℝ ∞ rhs U := by
    dsimp [rhs]
    apply ContDiffOn.sum
    intro ab hab
    exact hTermOn ab
  have hXAt (a : Fin n) : ContDiffAt ℝ ∞ (f a) 0 :=
    (hf a).contDiffWithinAt hU0 |>.contDiffAt (hU.mem_nhds hU0)
  have hYAt (b : Fin n) : ContDiffAt ℝ ∞ (q b) 0 :=
    (hq b).contDiffWithinAt hU0 |>.contDiffAt (hU.mem_nhds hU0)
  have hGAt (a b : Fin n) : ContDiffAt ℝ ∞ (g a b) 0 :=
    (hg a b).contDiffWithinAt hU0 |>.contDiffAt (hU.mem_nhds hU0)
  have hRhsAt : ContDiffAt ℝ ∞ rhs 0 :=
    (hRhsOn.contDiffWithinAt hU0).contDiffAt (hU.mem_nhds hU0)
  have hLhsAt : ContDiffAt ℝ ∞ (fun z : E ↦ (A p (x + z))⁻¹ i j -
      (A p (y + z))⁻¹ i j) 0 := by
    exact (hXAt j).sub (hYAt i)
  have hEqOn : ∀ z ∈ U,
      (fun z : E ↦ (A p (x + z))⁻¹ i j - (A p (y + z))⁻¹ i j) z = rhs z := by
    intro z hz
    have hres := matrix_inverse_resolvent_entry (A p (x + z)) (A p (y + z))
      (hUnit p hp (x + z) hz.1) (hUnit p hp (y + z) hz.2) i j
    simp only [rhs, term, f, g, q]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    exact hres
  have hJetWithin := iteratedFDerivWithin_congr (𝕜 := ℝ)
    (f₁ := fun z : E ↦ (A p (x + z))⁻¹ i j - (A p (y + z))⁻¹ i j)
    (f := rhs) hEqOn hU0 m
  have hNatLeInf (r : ℕ) : (r : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (le_top : (r : ℕ∞) ≤ (⊤ : ℕ∞))
  have hWithinL := iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    (hLhsAt.of_le (hNatLeInf m)) hU0
  have hWithinR := iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    (hRhsAt.of_le (hNatLeInf m)) hU0
  rw [hWithinL, hWithinR] at hJetWithin
  have hJetSum : iteratedFDeriv ℝ m rhs 0 =
      ∑ ab : Fin n × Fin n, iteratedFDeriv ℝ m (term ab) 0 := by
    dsimp [rhs]
    rw [iteratedFDeriv_fun_sum_apply]
    intro ab hab
    exact (hTermOn ab).contDiffWithinAt hU0 |>.contDiffAt (hU.mem_nhds hU0) |>.of_le
      (hNatLeInf m)
  have hLeftAt : ContDiffAt ℝ ∞ (fun z : E ↦ (A p (x + z))⁻¹ i j) 0 := by
    simpa [f] using hXAt j
  have hRightAt : ContDiffAt ℝ ∞ (fun z : E ↦ (A p (y + z))⁻¹ i j) 0 := by
    simpa [q] using hYAt i
  have hLeftAtm : ContDiffAt ℝ m
      (fun z : E ↦ (A p (x + z))⁻¹ i j) 0 := hLeftAt.of_le (hNatLeInf m)
  have hRightAtm : ContDiffAt ℝ m
      (fun z : E ↦ (A p (y + z))⁻¹ i j) 0 := hRightAt.of_le (hNatLeInf m)
  change iteratedFDeriv ℝ m
      ((fun z : E ↦ (A p (x + z))⁻¹ i j) -
        (fun z : E ↦ (A p (y + z))⁻¹ i j)) 0 = _ at hJetWithin
  rw [iteratedFDeriv_sub_apply hLeftAtm hRightAtm, hJetSum] at hJetWithin
  have hFBound (a : Fin n) (r : ℕ) (hr : r ≤ k) :
      ‖iteratedFDeriv ℝ r (f a) 0‖ ≤ (N : ℝ) := by
    have h := hInvJet p hp i a r hr x hx
    have h' : ‖iteratedFDeriv ℝ r (fun z ↦ (A p z)⁻¹ i a) x‖ ≤ (N : ℝ) := by
      exact_mod_cast h
    change ‖iteratedFDeriv ℝ r (fun z : E ↦ (A p (x + z))⁻¹ i a) 0‖ ≤ (N : ℝ)
    have htrans : iteratedFDeriv ℝ r (fun z : E ↦ (A p (x + z))⁻¹ i a) 0 =
        iteratedFDeriv ℝ r (fun z : E ↦ (A p z)⁻¹ i a) x := by
      simpa only [add_zero] using iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun z : E ↦ (A p z)⁻¹ i a) r x 0
    rw [htrans]
    exact h'
  have hQBound (b : Fin n) (r : ℕ) (hr : r ≤ k) :
      ‖iteratedFDeriv ℝ r (q b) 0‖ ≤ (N : ℝ) := by
    have h := hInvJet p hp b j r hr y hy
    have h' : ‖iteratedFDeriv ℝ r (fun z ↦ (A p z)⁻¹ b j) y‖ ≤ (N : ℝ) := by
      exact_mod_cast h
    change ‖iteratedFDeriv ℝ r (fun z : E ↦ (A p (y + z))⁻¹ b j) 0‖ ≤ (N : ℝ)
    have htrans : iteratedFDeriv ℝ r (fun z : E ↦ (A p (y + z))⁻¹ b j) 0 =
        iteratedFDeriv ℝ r (fun z : E ↦ (A p z)⁻¹ b j) y := by
      simpa only [add_zero] using iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun z : E ↦ (A p z)⁻¹ b j) r y 0
    rw [htrans]
    exact h'
  have hGBound (a b : Fin n) (r : ℕ) (hr : r ≤ k) :
      ‖iteratedFDeriv ℝ r (g a b) 0‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    have hh := holder_norm_probe (hAHolder p hp a b r hr) hx hy
    have hYAtA : ContDiffAt ℝ r (fun z : E ↦ A p (y + z) a b) 0 :=
      ((hAshiftY a b).contDiffWithinAt hU0).contDiffAt (hU.mem_nhds hU0) |>.of_le
        (hNatLeInf r)
    have hXAtA : ContDiffAt ℝ r (fun z : E ↦ A p (x + z) a b) 0 :=
      ((hAshiftX a b).contDiffWithinAt hU0).contDiffAt (hU.mem_nhds hU0) |>.of_le
        (hNatLeInf r)
    change ‖iteratedFDeriv ℝ r
      (fun z : E ↦ A p (y + z) a b - A p (x + z) a b) 0‖ ≤
        (C : ℝ) * dist x y ^ (α : ℝ)
    change ‖iteratedFDeriv ℝ r
      ((fun z : E ↦ A p (y + z) a b) - (fun z : E ↦ A p (x + z) a b)) 0‖ ≤ _
    rw [iteratedFDeriv_sub_apply hYAtA hXAtA]
    have htransY : iteratedFDeriv ℝ r (fun z : E ↦ A p (y + z) a b) 0 =
        iteratedFDeriv ℝ r (fun z : E ↦ A p z a b) y := by
      simpa only [add_zero] using iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun z : E ↦ A p z a b) r y 0
    have htransX : iteratedFDeriv ℝ r (fun z : E ↦ A p (x + z) a b) 0 =
        iteratedFDeriv ℝ r (fun z : E ↦ A p z a b) x := by
      simpa only [add_zero] using iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun z : E ↦ A p z a b) r x 0
    rw [htransY, htransX]
    simpa [norm_sub_rev] using hh
  have hZero : (0 : E) ∈ ({0} : Set E) := by simp
  have hFJet (a : Fin n) : ∀ r ≤ k, ∀ z ∈ ({0} : Set E),
      ‖iteratedFDeriv ℝ r (f a) z‖ ≤ (N : ℝ) := by
    intro r hr z hz
    have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
    subst z
    exact hFBound a r hr
  have hQJet (b : Fin n) : ∀ r ≤ k, ∀ z ∈ ({0} : Set E),
      ‖iteratedFDeriv ℝ r (q b) z‖ ≤ (N : ℝ) := by
    intro r hr z hz
    have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
    subst z
    exact hQBound b r hr
  have hGJet (a b : Fin n) : ∀ r ≤ k, ∀ z ∈ ({0} : Set E),
      ‖iteratedFDeriv ℝ r (g a b) z‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    intro r hr z hz
    have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
    subst z
    exact hGBound a b r hr
  have hFGJet (a b : Fin n) : ∀ r ≤ k, ∀ z ∈ ({0} : Set E),
      ‖iteratedFDeriv ℝ r (fun z ↦ f a z * g a b z) z‖ ≤
        (2 : ℝ) ^ k * (N : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)) := by
    have h := product_iterated_jet_bound_real
      (NNReal.coe_nonneg N) (by positivity) hU (by intro z hz; subst z; exact hU0)
      (f a) (g a b) (hf a) (hg a b) (hFJet a) (hGJet a b)
    exact h
  have hFGOn (a b : Fin n) : ContDiffOn ℝ ∞ (fun z ↦ f a z * g a b z) U :=
    (hf a).mul (hg a b)
  have hTermJet (ab : Fin n × Fin n) :
      ‖iteratedFDeriv ℝ m (term ab) 0‖ ≤
        (2 : ℝ) ^ k * ((2 : ℝ) ^ k * (N : ℝ) *
          ((C : ℝ) * dist x y ^ (α : ℝ))) * (N : ℝ) := by
    have h := product_iterated_jet_bound_real
      (by positivity : 0 ≤ (2 : ℝ) ^ k * (N : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)))
      (NNReal.coe_nonneg N) hU (by intro z hz; subst z; exact hU0)
      (fun z ↦ f ab.1 z * g ab.1 ab.2 z) (q ab.2)
      (hFGOn ab.1 ab.2) (hq ab.2) (hFGJet ab.1 ab.2) (hQJet ab.2)
    exact h m hm 0 hZero
  have hJetDiff :
      iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j) x -
        iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j) y =
          ∑ ab : Fin n × Fin n, iteratedFDeriv ℝ m (term ab) 0 := by
    have htransX : iteratedFDeriv ℝ m (fun z : E ↦ (A p (x + z))⁻¹ i j) 0 =
        iteratedFDeriv ℝ m (fun z : E ↦ (A p z)⁻¹ i j) x := by
      simpa only [add_zero] using iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun z : E ↦ (A p z)⁻¹ i j) m x 0
    have htransY : iteratedFDeriv ℝ m (fun z : E ↦ (A p (y + z))⁻¹ i j) 0 =
        iteratedFDeriv ℝ m (fun z : E ↦ (A p z)⁻¹ i j) y := by
      simpa only [add_zero] using iteratedFDeriv_comp_add_left (𝕜 := ℝ)
        (f := fun z : E ↦ (A p z)⁻¹ i j) m y 0
    rw [← htransX, ← htransY]
    exact hJetWithin
  have hJetNorm :
      ‖iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j) x -
        iteratedFDeriv ℝ m (fun z ↦ (A p z)⁻¹ i j) y‖ ≤
        (H : ℝ) * dist x y ^ (α : ℝ) := by
    rw [hJetDiff]
    calc
      _ ≤ ∑ ab : Fin n × Fin n, ‖iteratedFDeriv ℝ m (term ab) 0‖ := norm_sum_le _ _
      _ ≤ ∑ _ab : Fin n × Fin n,
          (2 : ℝ) ^ k * ((2 : ℝ) ^ k * (N : ℝ) *
            ((C : ℝ) * dist x y ^ (α : ℝ))) * (N : ℝ) := by
        apply Finset.sum_le_sum
        intro ab hab
        exact hTermJet ab
      _ = (n : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 2 * (N : ℝ) ^ 2 * C * dist x y ^ (α : ℝ) := by
        simp [Finset.sum_const, Fintype.card_prod, nsmul_eq_mul]
        ring
      _ = (H : ℝ) * dist x y ^ (α : ℝ) := by
        simp [H]
  have hpow : ENNReal.ofReal (dist x y ^ (α : ℝ)) =
      ENNReal.ofReal (dist x y) ^ (α : ℝ) :=
    (ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) (NNReal.coe_nonneg α)).symm
  have hmul : ENNReal.ofReal ((H : ℝ) * dist x y ^ (α : ℝ)) =
      (H : ENNReal) * ENNReal.ofReal (dist x y) ^ (α : ℝ) := by
    rw [ENNReal.ofReal_mul (NNReal.coe_nonneg H), ENNReal.ofReal_coe_nnreal, hpow]
  rw [edist_dist, dist_eq_norm, edist_dist]
  rw [← hmul]
  exact ENNReal.ofReal_le_ofReal hJetNorm

end KahlerForm
