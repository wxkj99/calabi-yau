module

public import CalabiYau.Geometry.Complex.Holder

/-!
# Uniform finite compact-patch Hölder assembly

Székelyhidi, §2.3, pp. 31–32: assemble estimates on finitely many smaller chart domains.
For close pairs a Lebesgue number puts both points in one patch; for distant pairs the
zeroth bound on the top jet controls its difference. Only compactness of the output set
and coverage by patch interiors are used, not convexity or boundary regularity.
-/

@[expose] public section

open scoped ContDiff NNReal Topology

namespace KahlerForm

/-- Quantitative assembly at order two. The factor is chosen before `f` and its common bound
`B`, unlike a merely existential compact-patch Hölder estimate. With a Lebesgue radius `δ > 0`
a valid factor is `max 1 (2 / δ ^ (α : ℝ))`. Empty sets and zero common bounds are allowed. -/
theorem exists_compactPatch_holder_factor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (K : Set E) (hK : IsCompact K)
    (patch : ι → Set E) (hcover : K ⊆ ⋃ i, interior (patch i)) (α : ℝ≥0) :
    ∃ A : ℝ≥0, ∀ f : E → ℝ, ∀ B : ℝ≥0,
      (∀ i, HolderBoundOn 2 α B (patch i) f) →
      HolderBoundOn 2 α (A * B) K f := by
  classical
  obtain ⟨δ, hδ, hLeb⟩ :=
    lebesgue_number_lemma_of_metric (s := K) hK (fun i => isOpen_interior) hcover
  let δ₀ : ℝ≥0 := Real.toNNReal δ
  have hδ₀ : (δ₀ : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  have hδ₀pos : 0 < δ₀ := Real.toNNReal_pos.mpr hδ
  let A : ℝ≥0 := max 1 (2 / δ₀ ^ (α : ℝ))
  refine ⟨A, ?_⟩
  intro f B hpatch
  let g : E → E [×2]→L[ℝ] ℝ := iteratedFDeriv ℝ 2 f
  have htop (z : E) (hz : z ∈ K) : ‖g z‖ ≤ B := by
    rcases Set.mem_iUnion.mp (hcover hz) with ⟨i, hi⟩
    exact hpatch i |>.1 2 le_rfl z (interior_subset hi)
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    rcases Set.mem_iUnion.mp (hcover hz) with ⟨i, hi⟩
    exact (hpatch i).1 j hj z (interior_subset hi) |>.trans (by
      calc
        B = 1 * B := by simp
        _ ≤ A * B := by
          apply mul_le_mul_of_nonneg_right
          · exact le_max_left 1 (2 / δ₀ ^ (α : ℝ))
          · positivity)
  · intro x hx y hy
    by_cases hnear : dist x y < δ
    · obtain ⟨i, hball⟩ := hLeb x hx
      have hxball : x ∈ Metric.ball x δ := Metric.mem_ball_self hδ
      have hyball : y ∈ Metric.ball x δ := by
        rw [Metric.mem_ball]
        simpa [dist_comm] using hnear
      have hAB : B ≤ A * B := by
        calc
          B = 1 * B := by simp
          _ ≤ A * B := mul_le_mul_of_nonneg_right
            (le_max_left 1 (2 / δ₀ ^ (α : ℝ))) (by positivity)
      exact ((hpatch i).2.mono_const hAB) x (interior_subset (hball hxball)) y
        (interior_subset (hball hyball))
    · have hfar : δ ≤ dist x y := le_of_not_gt hnear
      have hδdist : (δ₀ : ENNReal) ≤ edist x y := by
        rw [edist_dist]
        calc
          (δ₀ : ENNReal) = ENNReal.ofReal (δ₀ : ℝ) := by simp
          _ ≤ ENNReal.ofReal (dist x y) := ENNReal.ofReal_le_ofReal <| by
            simpa [hδ₀] using hfar
      have hpower : (δ₀ : ENNReal) ^ (α : ℝ) ≤ edist x y ^ (α : ℝ) :=
        ENNReal.rpow_le_rpow hδdist α.coe_nonneg
      have hden : 0 < δ₀ ^ (α : ℝ) := NNReal.rpow_pos (NNReal.coe_pos.1 hδ₀pos)
      have hscale : 2 ≤ A * δ₀ ^ (α : ℝ) := by
        calc
          2 = (2 / δ₀ ^ (α : ℝ)) * δ₀ ^ (α : ℝ) := by
            field_simp [ne_of_gt hden]
          _ ≤ A * δ₀ ^ (α : ℝ) := by
            exact mul_le_mul_of_nonneg_right (le_max_right 1 (2 / δ₀ ^ (α : ℝ))) (by positivity)
      have hscale' : (2 : ENNReal) ≤ (A : ENNReal) * (δ₀ : ENNReal) ^ (α : ℝ) := by
        calc
          (2 : ENNReal) ≤ (↑(A * δ₀ ^ (α : ℝ)) : ENNReal) := by exact_mod_cast hscale
          _ = (A : ENNReal) * (δ₀ : ENNReal) ^ (α : ℝ) := by
            simp [ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg]
      have htopdist : edist (g x) (g y) ≤ (2 * B : ENNReal) := by
        calc
          edist (g x) (g y) = ENNReal.ofReal (dist (g x) (g y)) := edist_dist _ _
          _ ≤ ENNReal.ofReal (‖g x‖ + ‖g y‖) := ENNReal.ofReal_le_ofReal (dist_le_norm_add_norm _ _)
          _ ≤ ENNReal.ofReal ((B : ℝ) + B) := ENNReal.ofReal_le_ofReal (add_le_add (htop x hx) (htop y hy))
          _ = (2 * B : ENNReal) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity)]
            simp [two_mul]
      calc
        edist (g x) (g y) ≤ (2 * B : ENNReal) := htopdist
        _ = (2 : ENNReal) * (B : ENNReal) := by simp
        _ ≤ ((A : ENNReal) * (B : ENNReal)) * edist x y ^ (α : ℝ) := by
          calc
            (2 : ENNReal) * (B : ENNReal) ≤
                ((A : ENNReal) * (δ₀ : ENNReal) ^ (α : ℝ)) * (B : ENNReal) :=
              mul_le_mul_of_nonneg_right hscale' (by positivity)
            _ ≤ ((A : ENNReal) * (B : ENNReal)) * edist x y ^ (α : ℝ) := by
              calc
                ((A : ENNReal) * (δ₀ : ENNReal) ^ (α : ℝ)) * (B : ENNReal) =
                    ((A : ENNReal) * (B : ENNReal)) * (δ₀ : ENNReal) ^ (α : ℝ) := by ac_rfl
                _ ≤ ((A : ENNReal) * (B : ENNReal)) * edist x y ^ (α : ℝ) :=
                  mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = (↑(A * B) : ENNReal) * edist x y ^ (α : ℝ) := by simp [ENNReal.coe_mul, mul_left_comm, mul_comm]

end KahlerForm
