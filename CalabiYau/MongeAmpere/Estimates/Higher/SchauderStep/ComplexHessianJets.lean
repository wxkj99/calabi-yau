module

public import CalabiYau.Mathlib.Geometry.Manifold.Holder
public import CalabiYau.Geometry.Complex.Forms.ComplexHessian
public import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.DirectionalJets

/-!
# Hölder bounds for complex Hessian coefficients

These statements pass local Hölder bounds on a potential to its complex Hessian coefficients.
The family result keeps the constant uniform in the family parameter and in the finite matrix
indices.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal
open ContinuousAlternatingMap

namespace KahlerForm

/-- A family with a common `C^{r,α}` bound has a common `C^{r-2,α}` bound on all complex
Hessian entries. -/
theorem exists_uniform_holderBoundOn_complexHessian_family_of_succ_succ
    {P : Type*} {n r : ℕ} {W K : Set (EuclideanSpace ℂ (Fin n))} {α C : ℝ≥0}
    (S : Set P) (f : P → EuclideanSpace ℂ (Fin n) → ℝ)
    (hW : IsOpen W) (hKW : K ⊆ W) (hr : 2 ≤ r)
    (hf : ∀ p ∈ S, ContDiffOn ℝ ∞ (f p) W)
    (hbound : ∀ p ∈ S, HolderBoundOn r α C K (f p)) :
    ∃ C' : ℝ≥0, ∀ p ∈ S, ∀ i j,
      HolderBoundOn (r - 2) α C' K (fun z ↦ complexHessian (f p) z i j) := by
  have holderBoundOn_fderiv_directional_of_succ_exact
      {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      {U K : Set E} {k : ℕ} {α C : ℝ≥0}
      (hU : IsOpen U) (hKU : K ⊆ U) (f : E → F) (v : E)
      (hf : ContDiffOn ℝ ∞ f U) (hbound : HolderBoundOn (k + 1) α C K f) :
      HolderBoundOn k α (‖(ContinuousLinearMap.apply ℝ F v)‖₊ * C) K
        (fun z ↦ fderiv ℝ f z v) := by
    let T : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F v
    have hiterAt (j : ℕ) (hj : j ≤ k) (z : E) (hz : z ∈ K) :
        iteratedFDeriv ℝ j (fun z ↦ fderiv ℝ f z v) z =
          T.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ f) z) := by
      have hfz : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hU.mem_nhds (hKU hz))
      have hfd : ContDiffAt ℝ k (fderiv ℝ f) z :=
        hfz.fderiv_right (by simp)
      change iteratedFDeriv ℝ j (T ∘ fderiv ℝ f) z = _
      simpa [T, Function.comp_apply, ContinuousLinearMap.apply_apply] using
        T.iteratedFDeriv_comp_left hfd (i := j) (by exact_mod_cast hj)
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      rw [hiterAt j hj z hz]
      calc
        ‖T.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ f) z)‖ ≤
            ‖T‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ f) z‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ ‖T‖ * C := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simpa [norm_iteratedFDeriv_fderiv] using hbound.1 (j + 1) (by omega) z hz
        _ = (‖T‖₊ * C : ℝ≥0) := by simp [NNReal.coe_mul]
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
            edist (iteratedFDeriv ℝ k (fderiv ℝ f) x)
              (iteratedFDeriv ℝ k (fderiv ℝ f) y) := by
          rw [ENNReal.ofReal_mul (norm_nonneg T), edist_dist]
          congr 1
          exact ENNReal.ofReal_eq_coe_nnreal (norm_nonneg T)
        _ = (‖T‖₊ : ENNReal) *
            edist (iteratedFDeriv ℝ (k + 1) f x)
              (iteratedFDeriv ℝ (k + 1) f y) := by rw [hdistQ]
        _ ≤ (‖T‖₊ : ENNReal) * (C : ENNReal) * edist x y ^ (α : ℝ) := by
          calc
            (‖T‖₊ : ENNReal) *
                edist (iteratedFDeriv ℝ (k + 1) f x) (iteratedFDeriv ℝ (k + 1) f y) ≤
                (‖T‖₊ : ENNReal) *
                  ((C : ENNReal) * edist x y ^ (α : ℝ)) :=
              mul_le_mul_of_nonneg_left (hbound.2.edist_le hx hy) (by positivity)
            _ = (‖T‖₊ : ENNReal) * (C : ENNReal) * edist x y ^ (α : ℝ) := by rw [mul_assoc]
        _ = ((‖(ContinuousLinearMap.apply ℝ F v)‖₊ * C : ℝ≥0) : ENNReal) *
            ENNReal.ofReal (dist x y) ^ (α : ℝ) := by
          rw [edist_dist]
          simp [T, mul_assoc]

  have exists_holderBoundOn_second_directional_derivative_exact
      {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {W K : Set E} {r : ℕ} {α C : ℝ≥0}
      (hW : IsOpen W) (hKW : K ⊆ W) (hr : 2 ≤ r)
      (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f W) (hbound : HolderBoundOn r α C K f)
      (u v : E) :
      HolderBoundOn (r - 2) α
        (‖(ContinuousLinearMap.apply ℝ ℝ v)‖₊ * (‖(ContinuousLinearMap.apply ℝ ℝ u)‖₊ * C)) K
        (fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ f w u) z v) := by
    have hr0 : 1 ≤ r := by omega
    have hr1 : 1 ≤ r - 1 := by omega
    have hrFirst : (r - 1) + 1 = r := by omega
    have hrSecond : (r - 2) + 1 = r - 1 := by omega
    have hboundFirst : HolderBoundOn ((r - 1) + 1) α C K f := by
      simpa [hrFirst] using hbound
    let g : E → ℝ := fun z ↦ fderiv ℝ f z u
    have hg : ContDiffOn ℝ ∞ g W := by
      have hderiv := hf.fderiv_of_isOpen hW (m := ∞) (by simp)
      exact hderiv.clm_apply contDiffOn_const
    have hbound1 := holderBoundOn_fderiv_directional_of_succ_exact
      hW hKW (k := r - 1) f u hf hboundFirst
    have hboundFirst2 : HolderBoundOn ((r - 2) + 1) α
        (‖(ContinuousLinearMap.apply ℝ ℝ u)‖₊ * C) K g := by
      simpa [g, hrSecond] using hbound1
    have hbound2 := holderBoundOn_fderiv_directional_of_succ_exact
      hW hKW (k := r - 2) g v hg hboundFirst2
    simpa [g, hrSecond, mul_assoc] using hbound2

  have holderBoundOn_add_smooth
      {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      {W K : Set E} {k : ℕ} {α C₁ C₂ : ℝ≥0}
      (hW : IsOpen W) (hKW : K ⊆ W) (f g : E → F)
      (hf : ContDiffOn ℝ ∞ f W) (hg : ContDiffOn ℝ ∞ g W)
      (hboundf : HolderBoundOn k α C₁ K f) (hboundg : HolderBoundOn k α C₂ K g) :
      HolderBoundOn k α (C₁ + C₂) K (f + g) := by
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hzW : z ∈ W := hKW hz
      have hjTop : (↑j : ℕ∞ω) ≤ ∞ := by
        exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
      have hfz : ContDiffAt ℝ j f z := (hf.contDiffAt (hW.mem_nhds hzW)).of_le hjTop
      have hgz : ContDiffAt ℝ j g z := (hg.contDiffAt (hW.mem_nhds hzW)).of_le hjTop
      have hsum := iteratedFDeriv_add_apply hfz hgz
      have hb₁ := hboundf.1 j hj z hz
      have hb₂ := hboundg.1 j hj z hz
      change ‖iteratedFDeriv ℝ j (f + g) z‖ ≤ _
      rw [hsum]
      calc
        ‖iteratedFDeriv ℝ j f z + iteratedFDeriv ℝ j g z‖ ≤
            ‖iteratedFDeriv ℝ j f z‖ + ‖iteratedFDeriv ℝ j g z‖ := norm_add_le _ _
        _ ≤ C₁ + C₂ := add_le_add hb₁ hb₂
    · have h₁ : HolderWith C₁ α (K.domRestrict fun z ↦ iteratedFDeriv ℝ k f z) :=
        hboundf.2.holderWith
      have h₂ : HolderWith C₂ α (K.domRestrict fun z ↦ iteratedFDeriv ℝ k g z) :=
        hboundg.2.holderWith
      have hadd := h₁.add h₂
      intro x hx y hy
      have hxW : x ∈ W := hKW hx
      have hyW : y ∈ W := hKW hy
      have hxTop : (↑k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)
      have hfx : ContDiffAt ℝ k f x := (hf.contDiffAt (hW.mem_nhds hxW)).of_le hxTop
      have hgx : ContDiffAt ℝ k g x := (hg.contDiffAt (hW.mem_nhds hxW)).of_le hxTop
      have hfy : ContDiffAt ℝ k f y := (hf.contDiffAt (hW.mem_nhds hyW)).of_le hxTop
      have hgy : ContDiffAt ℝ k g y := (hg.contDiffAt (hW.mem_nhds hyW)).of_le hxTop
      have hsumx := iteratedFDeriv_add_apply hfx hgx
      have hsumy := iteratedFDeriv_add_apply hfy hgy
      rw [hsumx, hsumy]
      simpa using hadd ⟨x, hx⟩ ⟨y, hy⟩

  have holderBoundOn_clm_comp_smooth
      {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G]
      {W K : Set E} {k : ℕ} {α C : ℝ≥0}
      (hW : IsOpen W) (hKW : K ⊆ W) (T : F →L[ℝ] G) (f : E → F)
      (hf : ContDiffOn ℝ ∞ f W) (hbound : HolderBoundOn k α C K f) :
      HolderBoundOn k α (‖T‖₊ * C) K (fun z ↦ T (f z)) := by
    have hiterAt (j : ℕ) (hj : j ≤ k) (z : E) (hz : z ∈ K) :
        iteratedFDeriv ℝ j (fun z ↦ T (f z)) z =
          T.compContinuousMultilinearMap (iteratedFDeriv ℝ j f z) := by
      have hfz : ContDiffAt ℝ ∞ f z := hf.contDiffAt (hW.mem_nhds (hKW hz))
      have hjTop : (↑j : ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)
      have hfzj : ContDiffAt ℝ j f z := hfz.of_le hjTop
      change iteratedFDeriv ℝ j (T ∘ f) z = _
      simpa [Function.comp_apply] using T.iteratedFDeriv_comp_left hfzj (i := j) le_rfl
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      rw [hiterAt j hj z hz]
      calc
        ‖T.compContinuousMultilinearMap (iteratedFDeriv ℝ j f z)‖ ≤
            ‖T‖ * ‖iteratedFDeriv ℝ j f z‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
        _ ≤ ‖T‖ * C := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact hbound.1 j hj z hz
        _ = (‖T‖₊ * C : ℝ≥0) := by simp [NNReal.coe_mul]
    · intro x hx y hy
      rw [hiterAt k le_rfl x hx, hiterAt k le_rfl y hy]
      change edist (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x))
          (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k f y)) ≤ _
      rw [edist_dist, edist_dist]
      have hnorm : dist (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x))
          (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k f y)) ≤
          ‖T‖ * dist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) := by
        rw [dist_eq_norm, dist_eq_norm]
        have hsub : T.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x) -
            T.compContinuousMultilinearMap (iteratedFDeriv ℝ k f y) =
            T.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y) := by
          change (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => E)
            F G T) _ - _ = _
          exact (map_sub (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => E)
            F G T) _ _).symm
        rw [hsub]
        exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      calc
        ENNReal.ofReal (dist (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k f x))
            (T.compContinuousMultilinearMap (iteratedFDeriv ℝ k f y))) ≤
            ENNReal.ofReal (‖T‖ * dist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y)) :=
          ENNReal.ofReal_le_ofReal hnorm
        _ = (‖T‖₊ : ENNReal) * edist (iteratedFDeriv ℝ k f x)
            (iteratedFDeriv ℝ k f y) := by
          rw [ENNReal.ofReal_mul (norm_nonneg T), edist_dist]
          congr 1
          exact ENNReal.ofReal_eq_coe_nnreal (norm_nonneg T)
        _ ≤ (‖T‖₊ : ENNReal) * (C : ENNReal) * edist x y ^ (α : ℝ) := by
          calc
            (‖T‖₊ : ENNReal) * edist (iteratedFDeriv ℝ k f x)
                (iteratedFDeriv ℝ k f y) ≤
                (‖T‖₊ : ENNReal) * ((C : ENNReal) * edist x y ^ (α : ℝ)) :=
              mul_le_mul_of_nonneg_left (hbound.2.edist_le hx hy) (by positivity)
            _ = (‖T‖₊ : ENNReal) * (C : ENNReal) * edist x y ^ (α : ℝ) := by rw [mul_assoc]
        _ = (‖T‖₊ * C : ℝ≥0) * ENNReal.ofReal (dist x y) ^ (α : ℝ) := by
          rw [edist_dist, ENNReal.coe_mul]

  have eval_single_norm_le_one {n : ℕ} (i : Fin n) :
      ‖(ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℂ)))‖₊ ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    apply ContinuousLinearMap.opNorm_le_bound
    · norm_num
    · intro L
      calc
        ‖L (EuclideanSpace.single i (1 : ℂ))‖ ≤
            ‖L‖ * ‖EuclideanSpace.single i (1 : ℂ)‖ := L.le_opNorm _
        _ = ‖L‖ * 1 := by simp [PiLp.norm_single]
        _ = 1 * ‖L‖ := by ring

  have eval_I_single_norm_le_one {n : ℕ} (i : Fin n) :
      ‖(ContinuousLinearMap.apply ℝ ℝ (Complex.I • EuclideanSpace.single i (1 : ℂ)))‖₊ ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    apply ContinuousLinearMap.opNorm_le_bound
    · norm_num
    · intro L
      calc
        ‖L (Complex.I • EuclideanSpace.single i (1 : ℂ))‖ ≤
            ‖L‖ * ‖Complex.I • EuclideanSpace.single i (1 : ℂ)‖ := L.le_opNorm _
        _ = 1 * ‖L‖ := by
          rw [norm_smul, Complex.norm_I, PiLp.norm_single]
          norm_num

  have exists_holderBoundOn_second_directional_derivative_unit
      {n r : ℕ} {α C : ℝ≥0} {W K : Set (EuclideanSpace ℂ (Fin n))}
      (hW : IsOpen W) (hKW : K ⊆ W) (hr : 2 ≤ r)
      (f : EuclideanSpace ℂ (Fin n) → ℝ)
      (hf : ContDiffOn ℝ ∞ f W) (hbound : HolderBoundOn r α C K f)
      (u v : EuclideanSpace ℂ (Fin n))
      (hu : ‖(ContinuousLinearMap.apply ℝ ℝ u)‖₊ ≤ 1)
      (hv : ‖(ContinuousLinearMap.apply ℝ ℝ v)‖₊ ≤ 1) :
      HolderBoundOn (r - 2) α C K
        (fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ f w u) z v) := by
    have h := exists_holderBoundOn_second_directional_derivative_exact hW hKW hr f hf hbound u v
    apply h.mono_const
    calc
      ‖(ContinuousLinearMap.apply ℝ ℝ v)‖₊ *
          (‖(ContinuousLinearMap.apply ℝ ℝ u)‖₊ * C) ≤ 1 * (1 * C) := by
        exact mul_le_mul hv (mul_le_mul hu le_rfl (by positivity) (by positivity))
          (by positivity) (by positivity)
      _ = C := by simp

  have exists_second_directional_derivative_contDiffOn
      {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {W : Set E} (hW : IsOpen W) (f : E → ℝ) (hf : ContDiffOn ℝ ∞ f W)
      (u v : E) : ContDiffOn ℝ ∞
        (fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ f w u) z v) W := by
    have hfirst := hf.fderiv_of_isOpen hW (m := ∞) (by simp)
    have hfirstDir : ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ f z u) W :=
      hfirst.clm_apply contDiffOn_const
    have hsecond := hfirstDir.fderiv_of_isOpen hW (m := ∞) (by simp)
    exact hsecond.clm_apply contDiffOn_const

  have holderBoundOn_contDiffOn_complexHessian_entry
      {n r : ℕ} {α C : ℝ≥0} {W K : Set (EuclideanSpace ℂ (Fin n))}
      (hW : IsOpen W) (hKW : K ⊆ W) (hr : 2 ≤ r)
      (f : EuclideanSpace ℂ (Fin n) → ℝ)
      (hf : ContDiffOn ℝ ∞ f W) (hbound : HolderBoundOn r α C K f)
      (i j : Fin n) :
      HolderBoundOn (r - 2) α C K (fun z ↦ complexHessian f z i j) := by
    let eI : Fin n → EuclideanSpace ℂ (Fin n) := fun a ↦ EuclideanSpace.single a (1 : ℂ)
    let d (u v : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) → ℝ :=
      fun z ↦ fderiv ℝ (fun w ↦ fderiv ℝ f w u) z v
    have hd_smooth (u v : EuclideanSpace ℂ (Fin n)) : ContDiffOn ℝ ∞ (d u v) W := by
      exact exists_second_directional_derivative_contDiffOn hW f hf u v
    have hd_bound (u v : EuclideanSpace ℂ (Fin n))
        (hu : ‖(ContinuousLinearMap.apply ℝ ℝ u)‖₊ ≤ 1)
        (hv : ‖(ContinuousLinearMap.apply ℝ ℝ v)‖₊ ≤ 1) :
        HolderBoundOn (r - 2) α C K (d u v) := by
      simpa [d] using exists_holderBoundOn_second_directional_derivative_unit
        hW hKW hr f hf hbound u v hu hv
    let u1 := eI i
    let v1 := eI j
    let u2 := Complex.I • eI i
    let v2 := Complex.I • eI j
    have hnorm1 : ‖(ContinuousLinearMap.apply ℝ ℝ u1)‖₊ ≤ 1 := by
      simpa [u1, eI] using eval_single_norm_le_one i
    have hnorm2 : ‖(ContinuousLinearMap.apply ℝ ℝ v1)‖₊ ≤ 1 := by
      simpa [v1, eI] using eval_single_norm_le_one j
    have hnorm3 : ‖(ContinuousLinearMap.apply ℝ ℝ u2)‖₊ ≤ 1 := by
      simpa [u2, eI] using eval_I_single_norm_le_one i
    have hnorm4 : ‖(ContinuousLinearMap.apply ℝ ℝ v2)‖₊ ≤ 1 := by
      simpa [v2, eI] using eval_I_single_norm_le_one j
    let a := d u1 v1
    let b := d u2 v2
    let c := d u1 v2
    let q := d u2 v1
    have haC := holderBoundOn_clm_comp_smooth hW hKW Complex.ofRealCLM a (hd_smooth u1 v1)
      (hd_bound u1 v1 hnorm1 hnorm2)
    have hbC := holderBoundOn_clm_comp_smooth hW hKW Complex.ofRealCLM b (hd_smooth u2 v2)
      (hd_bound u2 v2 hnorm3 hnorm4)
    have hcC := holderBoundOn_clm_comp_smooth hW hKW Complex.ofRealCLM c (hd_smooth u1 v2)
      (hd_bound u1 v2 hnorm1 hnorm4)
    have hqC := holderBoundOn_clm_comp_smooth hW hKW Complex.ofRealCLM q (hd_smooth u2 v1)
      (hd_bound u2 v1 hnorm3 hnorm2)
    have hnormReal : ‖Complex.ofRealCLM‖₊ ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      apply ContinuousLinearMap.opNorm_le_bound
      · norm_num
      · intro x
        rw [Complex.ofRealCLM_apply]
        simp
    have ha : HolderBoundOn (r - 2) α C K (fun z ↦ (a z : ℂ)) := by
      convert haC.mono_const (by
        calc
          ‖Complex.ofRealCLM‖₊ * C ≤ 1 * C := mul_le_mul_of_nonneg_right hnormReal (by positivity)
          _ = C := by simp) using 1; simp
    have hb : HolderBoundOn (r - 2) α C K (fun z ↦ (b z : ℂ)) := by
      convert hbC.mono_const (by
        calc
          ‖Complex.ofRealCLM‖₊ * C ≤ 1 * C := mul_le_mul_of_nonneg_right hnormReal (by positivity)
          _ = C := by simp) using 1; simp
    have hc : HolderBoundOn (r - 2) α C K (fun z ↦ (c z : ℂ)) := by
      convert hcC.mono_const (by
        calc
          ‖Complex.ofRealCLM‖₊ * C ≤ 1 * C := mul_le_mul_of_nonneg_right hnormReal (by positivity)
          _ = C := by simp) using 1; simp
    have hq : HolderBoundOn (r - 2) α C K (fun z ↦ (q z : ℂ)) := by
      convert hqC.mono_const (by
        calc
          ‖Complex.ofRealCLM‖₊ * C ≤ 1 * C := mul_le_mul_of_nonneg_right hnormReal (by positivity)
          _ = C := by simp) using 1; simp
    have haSmooth : ContDiffOn ℝ ∞ (fun z ↦ (a z : ℂ)) W := by
      exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hd_smooth u1 v1)
    have hbSmooth : ContDiffOn ℝ ∞ (fun z ↦ (b z : ℂ)) W := by
      exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hd_smooth u2 v2)
    have hcSmooth : ContDiffOn ℝ ∞ (fun z ↦ (c z : ℂ)) W := by
      exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hd_smooth u1 v2)
    have hqSmooth : ContDiffOn ℝ ∞ (fun z ↦ (q z : ℂ)) W := by
      exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hd_smooth u2 v1)
    let negCLM : ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℂ (-1)
    let mulICLM : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ Complex.I
    let divFourCLM : ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℂ (1 / 4 : ℝ)
    have hneg := holderBoundOn_clm_comp_smooth hW hKW negCLM (fun z ↦ (q z : ℂ)) hqSmooth hq
    have hnegNorm : ‖negCLM‖₊ ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      apply ContinuousLinearMap.opNorm_le_bound
      · norm_num
      · intro z
        simp [negCLM]
    have hneg' : HolderBoundOn (r - 2) α C K (fun z ↦ -(q z : ℂ)) := by
      have hmono := hneg.mono_const (by
        calc
          ‖negCLM‖₊ * C ≤ 1 * C := mul_le_mul_of_nonneg_right hnegNorm (by positivity)
          _ = C := by simp)
      simpa [negCLM] using hmono
    have hsub := holderBoundOn_add_smooth hW hKW (fun z ↦ (c z : ℂ))
      (fun z ↦ -(q z : ℂ)) hcSmooth hqSmooth.neg hc hneg'
    have hmulI := holderBoundOn_clm_comp_smooth hW hKW mulICLM
      (fun z ↦ ((c z : ℂ) - (q z : ℂ))) (hcSmooth.sub hqSmooth)
      hsub
    have hmulINorm : ‖mulICLM‖₊ ≤ 1 := by
      apply NNReal.coe_le_coe.mp
      apply ContinuousLinearMap.opNorm_le_bound
      · norm_num
      · intro z
        simp [mulICLM]
    have hmulI' : HolderBoundOn (r - 2) α (2 * C) K
        (fun z ↦ Complex.I * ((c z : ℂ) - (q z : ℂ))) := by
      have hmono := hmulI.mono_const (by
        calc
          ‖mulICLM‖₊ * (C + C) ≤ 1 * (C + C) := mul_le_mul_of_nonneg_right hmulINorm (by positivity)
          _ = 2 * C := by ring)
      simpa [mulICLM] using hmono
    have hab := holderBoundOn_add_smooth hW hKW (fun z ↦ (a z : ℂ))
      (fun z ↦ (b z : ℂ)) haSmooth hbSmooth ha hb
    have hsum := holderBoundOn_add_smooth hW hKW (fun z ↦ (a z : ℂ) + (b z : ℂ))
      (fun z ↦ Complex.I * ((c z : ℂ) - (q z : ℂ))) (haSmooth.add hbSmooth)
      (hcSmooth.sub hqSmooth |> fun h => mulICLM.contDiff.comp_contDiffOn h)
      hab hmulI'
    have hsumSmooth : ContDiffOn ℝ ∞
        (fun z ↦ ((a z : ℂ) + (b z : ℂ)) + Complex.I * ((c z : ℂ) - (q z : ℂ))) W := by
      exact (haSmooth.add hbSmooth).add (mulICLM.contDiff.comp_contDiffOn (hcSmooth.sub hqSmooth))
    have hfinal := holderBoundOn_clm_comp_smooth hW hKW divFourCLM
      (fun z ↦ ((a z : ℂ) + (b z : ℂ)) + Complex.I * ((c z : ℂ) - (q z : ℂ)))
      hsumSmooth hsum
    have hdivNorm : ‖divFourCLM‖₊ ≤ 1 / 4 := by
      apply NNReal.coe_le_coe.mp
      apply ContinuousLinearMap.opNorm_le_bound
      · positivity
      · intro z
        simp [divFourCLM]
    have hfinal' : HolderBoundOn (r - 2) α C K
        (fun z ↦ (1 / 4 : ℝ) • (((a z : ℂ) + (b z : ℂ)) +
          Complex.I * ((c z : ℂ) - (q z : ℂ)))) := by
      have hmono := hfinal.mono_const (by
        calc
          ‖divFourCLM‖₊ * (C + C + 2 * C) ≤ (1 / 4 : ℝ≥0) * (C + C + 2 * C) :=
            mul_le_mul_of_nonneg_right hdivNorm (by positivity)
          _ = C := by ring)
      convert hmono using 1
      ext z
      simp [divFourCLM]
      ring
    have hEq (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ W) :
        complexHessian f z i j =
          (1 / 4 : ℝ) • (((a z : ℂ) + (b z : ℂ)) +
            Complex.I * ((c z : ℂ) - (q z : ℂ))) := by
      have hfz : ContDiffAt ℝ 2 f z :=
        (hf.contDiffAt (hW.mem_nhds hz)).of_le
          (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
      have hfd : ContDiffAt ℝ 1 (fderiv ℝ f) z := hfz.fderiv_right (by norm_num)
      have hfd' : DifferentiableAt ℝ (fderiv ℝ f) z := hfd.differentiableAt (by norm_num)
      have hEval (u v : EuclideanSpace ℂ (Fin n)) :
          d u v z = fderiv ℝ (fderiv ℝ f) z u v := by
        have hEval' : d u v z = fderiv ℝ (fderiv ℝ f) z v u := by
          dsimp [d]
          rw [fderiv_clm_apply hfd' (differentiableAt_const u)]
          simp
        rw [hEval']
        exact hfz.isSymmSndFDerivAt (by norm_num) v u
      rw [complexHessian_apply hfz]
      simp only [a, b, c, q, d, u1, u2, v1, v2, eI, hEval]
      simp [div_eq_mul_inv]
      ring
    let G : EuclideanSpace ℂ (Fin n) → ℂ := fun z ↦
      (1 / 4 : ℝ) • (((a z : ℂ) + (b z : ℂ)) +
        Complex.I * ((c z : ℂ) - (q z : ℂ)))
    have hresult : HolderBoundOn (r - 2) α C K G := by
      simpa [G] using hfinal'
    have hGsmooth : ContDiffOn ℝ ∞ G W := by
      have heq : G = fun z ↦ divFourCLM
          (((a z : ℂ) + (b z : ℂ)) + Complex.I * ((c z : ℂ) - (q z : ℂ))) := by
        funext z
        simp [G, divFourCLM, smul_eq_mul]
        ring
      rw [heq]
      exact divFourCLM.contDiff.comp_contDiffOn hsumSmooth
    have hEqOn : Set.EqOn (fun z ↦ complexHessian f z i j) G W := by
      intro z hz
      exact hEq z hz
    have hHsmooth : ContDiffOn ℝ ∞ (fun z ↦ complexHessian f z i j) W :=
      hGsmooth.congr (fun z hz ↦ hEqOn hz)
    have hIter (k : ℕ) (hk : k ≤ r - 2) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
        iteratedFDeriv ℝ k (fun w ↦ complexHessian f w i j) z = iteratedFDeriv ℝ k G z := by
      have hkTop : (↑k : ℕ∞ω) ≤ ∞ := by
        exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)
      have hHAt : ContDiffAt ℝ k (fun w ↦ complexHessian f w i j) z :=
        (hHsmooth.contDiffAt (hW.mem_nhds (hKW hz))).of_le hkTop
      have hGAt : ContDiffAt ℝ k G z :=
        (hGsmooth.contDiffAt (hW.mem_nhds (hKW hz))).of_le hkTop
      calc
        iteratedFDeriv ℝ k (fun w ↦ complexHessian f w i j) z =
            iteratedFDerivWithin ℝ k (fun w ↦ complexHessian f w i j) W z :=
          (iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn hHAt (hKW hz)).symm
        _ = iteratedFDerivWithin ℝ k G W z :=
          iteratedFDerivWithin_congr hEqOn (hKW hz) k
        _ = iteratedFDeriv ℝ k G z :=
          iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn hGAt (hKW hz)
    refine ⟨?_, ?_⟩
    · intro k hk z hz
      rw [hIter k hk z hz]
      exact hresult.1 k hk z hz
    · intro x hx y hy
      rw [hIter (r - 2) le_rfl x hx, hIter (r - 2) le_rfl y hy]
      exact hresult.2 x hx y hy

  refine ⟨C, ?_⟩
  intro p hp i j
  exact holderBoundOn_contDiffOn_complexHessian_entry hW hKW hr (f p) (hf p hp)
    (hbound p hp) i j
/-- Smooth chart potentials have smooth complex-Hessian coefficient fields. -/
theorem contDiffOn_complexHessian_entries_of_contDiffOn
    {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → ℝ) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ complexHessian f z i j) U := by
  have hddbar : ContDiffOn ℝ ∞ (ddbar f) U := ContDiffOn.ddbar hU hf
  intro i j
  let f₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
    ddbar f z ![EuclideanSpace.single i 1, Complex.I • EuclideanSpace.single j 1]
  let f₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
    ddbar f z ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
  have hf₁ : ContDiffOn ℝ ∞ f₁ U := by
    dsimp [f₁]
    exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
      ![EuclideanSpace.single i 1, Complex.I • EuclideanSpace.single j 1]).contDiff).comp_contDiffOn
        hddbar
  have hf₂ : ContDiffOn ℝ ∞ f₂ U := by
    dsimp [f₂]
    exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]).contDiff).comp_contDiffOn hddbar
  have hf₁c : ContDiffOn ℝ ∞ (fun z ↦ (f₁ z : ℂ)) U := by
    convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₁ using 1
    ext z
    simp [Complex.ofRealCLM_apply]
  have hf₂c : ContDiffOn ℝ ∞ (fun z ↦ (f₂ z : ℂ)) U := by
    convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₂ using 1
    ext z
    simp [Complex.ofRealCLM_apply]
  have hIprod : ContDiffOn ℝ ∞ (fun z ↦ Complex.I * (f₂ z : ℂ)) U :=
    contDiffOn_const.mul hf₂c
  have hformula : ContDiffOn ℝ ∞
      (fun z ↦ ((f₁ z : ℂ) - Complex.I * (f₂ z : ℂ)) / 2) U :=
    (hf₁c.sub hIprod).div_const (2 : ℂ)
  apply hformula.congr
  intro z hz
  change (ddbar f z).coeffMatrix i j = _
  simp [ContinuousAlternatingMap.coeffMatrix, f₁, f₂]

end KahlerForm

end
