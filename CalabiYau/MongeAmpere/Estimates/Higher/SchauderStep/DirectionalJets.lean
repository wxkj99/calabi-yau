module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder

/-!
# Directional derivatives of Hölder jets

An ambient derivative evaluated in a fixed direction loses one Hölder order on an open set.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal

/-- A smooth function with a `C^{k+1,α}` bound has bounded `C^{k,α}` directional derivatives.
The openness hypothesis ensures that the derivatives on the set are the ambient derivatives;
without it, `ContDiffOn` only controls the relative derivative and this claim can fail. -/
theorem exists_holderBoundOn_fderiv_directional_of_succ
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    {k : ℕ} {α C : ℝ≥0} (f : E → F) (v : E)
    (hf : ContDiffOn ℝ ∞ f U) (hbound : HolderBoundOn (k + 1) α C K f) :
    ∃ C' : ℝ≥0, HolderBoundOn k α C' K (fun z ↦ fderiv ℝ f z v) := by
  let T : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F v
  let C' : ℝ≥0 := ‖T‖₊ * C
  have hiterAt (j : ℕ) (hj : j ≤ k) (z : E) (hz : z ∈ K) :
      iteratedFDeriv ℝ j (fun z ↦ fderiv ℝ f z v) z =
        T.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ f) z) := by
    have hfz : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hU.mem_nhds (hKU hz))
    have hfd : ContDiffAt ℝ k (fderiv ℝ f) z :=
      hfz.fderiv_right (by simp)
    change iteratedFDeriv ℝ j (T ∘ fderiv ℝ f) z = _
    simpa [T, Function.comp_apply, ContinuousLinearMap.apply_apply] using
      T.iteratedFDeriv_comp_left hfd (i := j) (by exact_mod_cast hj)
  refine ⟨C', ?_⟩
  constructor
  · intro j hj z hz
    rw [hiterAt j hj z hz]
    calc
      ‖T.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ f) z)‖ ≤
          ‖T‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ f) z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ ‖T‖ * C := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa [norm_iteratedFDeriv_fderiv] using hbound.1 (j + 1) (by omega) z hz
      _ = C' := by simp [C', T]
  · intro x hx y hy
    have hiterx := hiterAt k le_rfl x hx
    have hitery := hiterAt k le_rfl y hy
    have hq (z : E) :
        (continuousMultilinearCurryRightEquiv' ℝ k E F)
          (iteratedFDeriv ℝ (k + 1) f z) = iteratedFDeriv ℝ k (fderiv ℝ f) z := by
      have hsucc := iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := f) (n := k) (x := z)
      have hq0 := congrArg (continuousMultilinearCurryRightEquiv' ℝ k E F) hsucc
      simpa [Function.comp_apply] using hq0
    have hdistQ : edist (iteratedFDeriv ℝ k (fderiv ℝ f) x)
        (iteratedFDeriv ℝ k (fderiv ℝ f) y) =
        edist (iteratedFDeriv ℝ (k + 1) f x) (iteratedFDeriv ℝ (k + 1) f y) := by
      rw [edist_dist, edist_dist, ← hq x, ← hq y, dist_eq_norm, dist_eq_norm]
      have hnorm : ‖(continuousMultilinearCurryRightEquiv' ℝ k E F)
          (iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) f y)‖ =
          ‖iteratedFDeriv ℝ (k + 1) f x - iteratedFDeriv ℝ (k + 1) f y‖ :=
        (continuousMultilinearCurryRightEquiv' ℝ k E F).norm_map _
      rw [← map_sub, hnorm]
    rw [hiterx, hitery]
    change edist (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ f) x))
        (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ f) y)) ≤ _
    rw [edist_dist, edist_dist]
    have hnorm : dist
          (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ f) x))
          (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ f) y)) ≤
        ‖T‖ * dist (iteratedFDeriv ℝ k (fderiv ℝ f) x)
          (iteratedFDeriv ℝ k (fderiv ℝ f) y) := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : T.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ f) x) -
          T.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ f) y) =
          T.compContinuousMultilinearMap
            (iteratedFDeriv ℝ k (fderiv ℝ f) x - iteratedFDeriv ℝ k (fderiv ℝ f) y) := by
        change (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => E)
          (E →L[ℝ] F) F T) _ - _ = _
        exact map_sub
          (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => E)
            (E →L[ℝ] F) F T) _ _
      rw [hsub]
      exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    calc
      ENNReal.ofReal (dist
          (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ f) x))
          (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fderiv ℝ f) y))) ≤
          ENNReal.ofReal (‖T‖ * dist (iteratedFDeriv ℝ k (fderiv ℝ f) x)
            (iteratedFDeriv ℝ k (fderiv ℝ f) y)) := ENNReal.ofReal_le_ofReal hnorm
      _ = (‖T‖₊ : ENNReal) *
          edist (iteratedFDeriv ℝ k (fderiv ℝ f) x) (iteratedFDeriv ℝ k (fderiv ℝ f) y) := by
        rw [ENNReal.ofReal_mul (norm_nonneg T), edist_dist]
        congr 1
        exact ENNReal.ofReal_eq_coe_nnreal (norm_nonneg T)
      _ = (‖T‖₊ : ENNReal) *
          edist (iteratedFDeriv ℝ (k + 1) f x) (iteratedFDeriv ℝ (k + 1) f y) := by rw [hdistQ]
      _ ≤ (‖T‖₊ : ENNReal) * (C : ENNReal) * edist x y ^ (α : ℝ) := by
        calc
          (‖T‖₊ : ENNReal) *
              edist (iteratedFDeriv ℝ (k + 1) f x) (iteratedFDeriv ℝ (k + 1) f y) ≤
              (‖T‖₊ : ENNReal) *
                ((C : ENNReal) * edist x y ^ (α : ℝ)) :=
            mul_le_mul_of_nonneg_left (hbound.2.edist_le hx hy) (by positivity)
          _ = (‖T‖₊ : ENNReal) * (C : ENNReal) * edist x y ^ (α : ℝ) := by rw [mul_assoc]
      _ = (C' : ENNReal) * edist x y ^ (α : ℝ) := by simp [C', mul_assoc]
      _ = (C' : ENNReal) * ENNReal.ofReal (dist x y) ^ (α : ℝ) := by rw [edist_dist]
end
