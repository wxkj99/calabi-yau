module

public import CalabiYau.Geometry.Complex.Schauder

/-!
# Reconstructing Hölder metric jets from directional derivatives

The first Schauder pass controls the first derivatives on open inner domains.
Use finitely many real coordinate directions, lower their derivative order by one,
and use the real expansion of the complex Hessian (with its factor `1/4`).
The original genuine `C^k` regularity remains a separate hypothesis.
-/

@[expose] public section

open scoped ContDiff NNReal Topology

private theorem fderivHolderBoundOn {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α C : ℝ≥0} {K : Set E} {f : E → F}
    (hbound : HolderBoundOn (k + 1) α C K f) :
    HolderBoundOn k α C K (fderiv ℝ f) := by
  have hJet (x : E) : iteratedFDeriv ℝ k (fderiv ℝ f) x =
      (continuousMultilinearCurryRightEquiv' ℝ k E F) (iteratedFDeriv ℝ (k + 1) f x) := by
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    rw [norm_iteratedFDeriv_fderiv]
    exact hbound.1 (j + 1) (Nat.succ_le_succ hj) x hx
  · intro x hx y hy
    rw [hJet x, hJet y]
    simpa only [edist_dist, (continuousMultilinearCurryRightEquiv' ℝ k E F).dist_map] using
      hbound.2 x hx y hy

private theorem holderBoundOn_comp_linear
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U K : Set E} {k : ℕ} {α C : ℝ≥0} {f : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ k f U)
    (hbound : HolderBoundOn k α C K f) (L : F →L[ℝ] G) :
    HolderBoundOn k α (‖L‖₊ * C) K (fun x ↦ L (f x)) := by
  let post : (E [×k]→L[ℝ] F) →L[ℝ] (E [×k]→L[ℝ] G) :=
    ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => E) F G L
  have hpost : ‖post‖ ≤ ‖L‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    (fun T ↦ L.norm_compContinuousMultilinearMap_le T)
  have hLip : LipschitzWith ‖post‖₊ post := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa [dist_eq_norm, ← map_sub] using post.le_opNorm (a - b)
  have hTop : HolderOnWith (‖post‖₊ * C) α
      (fun x ↦ post (iteratedFDeriv ℝ k f x)) K := by
    simpa [Function.comp_def, NNReal.rpow_one] using
      ((holderWith_one.mpr hLip).holderOnWith Set.univ).comp hbound.2
        (fun x hx ↦ Set.mem_univ _)
  have hconst : ‖post‖₊ * C ≤ ‖L‖₊ * C :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hpost) (show 0 ≤ C from bot_le)
  have hJet (j : ℕ) (hj : j ≤ k) (x : E) (hx : x ∈ K) :
      iteratedFDeriv ℝ j (fun y ↦ L (f y)) x =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ j f x) :=
    L.iteratedFDeriv_comp_left (hf.contDiffAt (hU.mem_nhds (hKU hx)))
      (by exact_mod_cast hj)
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    rw [hJet j hj x hx]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (by simpa using mul_le_mul_of_nonneg_left (hbound.1 j hj x hx) (norm_nonneg L))
  · intro x hx y hy
    rw [hJet k le_rfl x hx, hJet k le_rfl y hy]
    exact (hTop.mono_const hconst) x hx y hy

private theorem coordinate_complexHessian
    {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z : EuclideanSpace ℂ (Fin n)}
    (hf : ContDiffAt ℝ 2 f z) (i j : Fin n) :
    complexHessian f z i j =
      ((fderiv ℝ (fun x ↦ fderiv ℝ f x (EuclideanSpace.single j 1)) z
          (EuclideanSpace.single i 1) : ℂ) +
        fderiv ℝ (fun x ↦ fderiv ℝ f x (Complex.I • EuclideanSpace.single j 1)) z
          (Complex.I • EuclideanSpace.single i 1) +
        Complex.I * (fderiv ℝ (fun x ↦ fderiv ℝ f x (Complex.I • EuclideanSpace.single j 1)) z
          (EuclideanSpace.single i 1) -
        fderiv ℝ (fun x ↦ fderiv ℝ f x (EuclideanSpace.single j 1)) z
          (Complex.I • EuclideanSpace.single i 1))) / 4 := by
  rw [complexHessian_apply hf i j]
  have hD : ContDiffAt ℝ 1 (fderiv ℝ f) z := hf.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) z := hD.differentiableAt (by norm_num)
  have hEval (a b : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ (fun x ↦ fderiv ℝ f x b) z a = fderiv ℝ (fderiv ℝ f) z a b := by
    rw [fderiv_clm_apply hdiff (differentiableAt_const b)]
    simp
  rw [hEval, hEval, hEval, hEval]

private theorem holderBoundOn_add
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} {k : ℕ} {α C D : ℝ≥0} {f g : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ k f U) (hg : ContDiffOn ℝ k g U)
    (hfb : HolderBoundOn k α C K f) (hgb : HolderBoundOn k α D K g) :
    HolderBoundOn k α (C + D) K (fun x ↦ f x + g x) := by
  have hJet (j : ℕ) (hj : j ≤ k) (x : E) (hx : x ∈ K) :
      iteratedFDeriv ℝ j (fun y ↦ f y + g y) x =
        iteratedFDeriv ℝ j f x + iteratedFDeriv ℝ j g x :=
    iteratedFDeriv_add_apply
      ((hf.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by exact_mod_cast hj))
      ((hg.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by exact_mod_cast hj))
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    rw [hJet j hj x hx]
    exact (norm_add_le _ _).trans (by
      simpa using add_le_add (hfb.1 j hj x hx) (hgb.1 j hj x hx))
  · intro x hx y hy
    rw [hJet k le_rfl x hx, hJet k le_rfl y hy]
    calc
      edist (iteratedFDeriv ℝ k f x + iteratedFDeriv ℝ k g x)
          (iteratedFDeriv ℝ k f y + iteratedFDeriv ℝ k g y) ≤
        edist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) +
          edist (iteratedFDeriv ℝ k g x) (iteratedFDeriv ℝ k g y) := edist_add_add_le _ _ _ _
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
          (D : ENNReal) * edist x y ^ (α : ℝ) :=
        add_le_add (hfb.2 x hx y hy) (hgb.2 x hx y hy)
      _ = ((C + D : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_add, add_mul]

private theorem holderBoundOn_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} {k : ℕ} {α C : ℝ≥0} {f : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U) (hf : ContDiffOn ℝ k f U)
    (hbound : HolderBoundOn k α C K f) (a : ℝ) :
    HolderBoundOn k α (‖a • (1 : F →L[ℝ] F)‖₊ * C) K (fun x ↦ a • f x) := by
  have h := holderBoundOn_comp_linear hU hKU hf hbound
    (a • (1 : F →L[ℝ] F))
  have hfun : (fun x ↦ (a • (1 : F →L[ℝ] F)) (f x)) = fun x ↦ a • f x := by
    funext x
    simp
  rw [← hfun]
  exact h

private theorem holderBoundOn_sub
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} {k : ℕ} {α C D : ℝ≥0} {f g : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ k f U) (hg : ContDiffOn ℝ k g U)
    (hfb : HolderBoundOn k α C K f) (hgb : HolderBoundOn k α D K g) :
    HolderBoundOn k α (C + ‖(-1 : ℝ) • (1 : F →L[ℝ] F)‖₊ * D) K
      (fun x ↦ f x - g x) := by
  have hneg := holderBoundOn_smul hU hKU hg hgb (-1)
  have hnegSmooth : ContDiffOn ℝ k (fun x ↦ -g x) U := by fun_prop
  have hsum := holderBoundOn_add hU hKU hf hnegSmooth hfb (by simpa using hneg)
  simpa [sub_eq_add_neg] using hsum

private theorem common_directional_bounds
    {n k : ℕ} {α : ℝ≥0}
    {W : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (hfirst : ∀ z ∈ W, ∀ v : EuclideanSpace ℂ (Fin n),
      ∃ V : Set (EuclideanSpace ℂ (Fin n)), ∃ C : ℝ≥0,
        IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        HolderBoundOn (k - 1) α C V (fun w ↦ fderiv ℝ f w v))
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ W) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), ∃ C : ℝ≥0,
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      ∀ p : Fin n × Bool,
        HolderBoundOn (k - 1) α C V
          (fun w ↦ fderiv ℝ f w
            (if p.2 then Complex.I • EuclideanSpace.single p.1 1
              else EuclideanSpace.single p.1 1)) := by
  classical
  let direction (p : Fin n × Bool) : EuclideanSpace ℂ (Fin n) :=
    if p.2 then Complex.I • EuclideanSpace.single p.1 1
    else EuclideanSpace.single p.1 1
  have hex : ∀ p : Fin n × Bool, ∃ V : Set (EuclideanSpace ℂ (Fin n)),
      ∃ C : ℝ≥0, IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        HolderBoundOn (k - 1) α C V (fun w ↦ fderiv ℝ f w (direction p)) := by
    intro p
    exact hfirst z hz (direction p)
  choose Vp Cp hVpOpen hzVp hVpW hpbound using hex
  let U := W ∩ ⋂ p : Fin n × Bool, Vp p
  have hUOpen : IsOpen U := hW.inter (isOpen_iInter_of_finite fun p ↦ hVpOpen p)
  have hzU : z ∈ U := by
    refine ⟨hz, ?_⟩
    exact Set.mem_iInter.mpr (fun p ↦ hzVp p)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hUOpen z hzU
  let V := Metric.ball z (r / 2)
  have hVOpen : IsOpen V := Metric.isOpen_ball
  have hzV : z ∈ V := Metric.mem_ball_self (by positivity)
  have hVsubU : V ⊆ U := by
    exact (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)).trans hball
  have hVU : V ⊆ W := fun w hw ↦ (hVsubU hw).1
  refine ⟨V, ∑ p : Fin n × Bool, Cp p, hVOpen, hzV, hVU, ?_⟩
  intro p
  have hVp : V ⊆ Vp p := by
    intro w hw
    exact (Set.mem_iInter.mp (hVsubU hw).2) p
  have hC : Cp p ≤ ∑ q : Fin n × Bool, Cp q :=
    Finset.single_le_sum (fun q hq ↦ bot_le) (Finset.mem_univ p)
  exact (hpbound p).mono_set hVp |>.mono_const hC

private theorem compact_derivative_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ m f U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ≥0, ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have htop (j : ℕ) (hj : j ≤ m) : (j : ℕ∞ω) ≤ (m : ℕ∞ω) := by
    exact_mod_cast hj
  have hcont (j : ℕ) (hj : j ≤ m) :
      ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ j f x‖) K := by
    have hwithin := hf.continuousOn_iteratedFDerivWithin (htop j hj) hU.uniqueDiffOn
    have heq : Set.EqOn (iteratedFDerivWithin ℝ j f U) (iteratedFDeriv ℝ j f) U := by
      intro x hx
      exact iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        ((hf.contDiffAt (hU.mem_nhds hx)).of_le (htop j hj)) hx
    exact (hwithin.congr heq.symm).mono hKU |>.norm
  let q : E → ℝ := fun x ↦ ∑ j ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ j f x‖
  have hq : ContinuousOn q K := by
    dsimp [q]
    exact continuousOn_finsetSum (Finset.range (m + 1)) fun j hj =>
      hcont j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  obtain ⟨B, hB0, hB⟩ := (hK.bddAbove_image hq).exists_ge 0
  let C : ℝ≥0 := ⟨B, hB0⟩
  refine ⟨C, ?_⟩
  intro j hj x hx
  have hqbound : q x ≤ B := hB (q x) (Set.mem_image_of_mem q hx)
  have hterm : ‖iteratedFDeriv ℝ j f x‖ ≤ q x := by
    dsimp [q]
    apply Finset.single_le_sum (f := fun i ↦ ‖iteratedFDeriv ℝ i f x‖)
    · intro i hi
      exact norm_nonneg _
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  change ‖iteratedFDeriv ℝ j f x‖ ≤ B
  exact hterm.trans hqbound

private theorem holderBoundOn_of_contDiffOn_succ_derivative_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {k : ℕ} {alpha C : ℝ≥0} {f : E → F}
    (hsOpen : IsOpen s) (hsConvex : Convex ℝ s)
    (hsDiam : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ 1)
    (hAlpha : alpha ≤ 1) (hf : ContDiffOn ℝ (k + 1) f s)
    (hbound : ∀ j ≤ k + 1, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    HolderBoundOn k alpha C s f := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    exact hbound j (le_trans hj (Nat.le_succ k)) x hx
  · let g : E → _ := iteratedFDeriv ℝ k f
    have hklt : (↑k : ℕ∞ω) < (↑(k + 1) : ℕ∞ω) := by
      exact_mod_cast Nat.lt_succ_self k
    have hgDiff (x : E) (hx : x ∈ s) : DifferentiableAt ℝ g x :=
      (hf.contDiffAt (hsOpen.mem_nhds hx)).differentiableAt_iteratedFDeriv hklt
    have hgDeriv (x : E) (hx : x ∈ s) : ‖fderiv ℝ g x‖ ≤ (C : ℝ) := by
      rw [norm_fderiv_iteratedFDeriv]
      exact hbound (k + 1) le_rfl x hx
    have hLip : LipschitzOnWith C g s :=
      hsConvex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) hgDiff hgDeriv
    have hdiam (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) :
        edist x y ≤ (1 : ENNReal) := by
      rw [edist_dist]
      exact_mod_cast hsDiam x hx y hy
    simpa [g] using hLip.holderOnWith.of_le hdiam hAlpha

private theorem complexHessian_entry_contDiffOn
    {n k : ℕ} (hk : 3 ≤ k) {W : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ k f W) (i j : Fin n) :
    ContDiffOn ℝ (k - 2 : ℕ) (fun z ↦ complexHessian f z i j) W := by
  have hfd : ContDiffOn ℝ (k - 1 : ℕ) (fderiv ℝ f) W :=
    hf.fderiv_of_isOpen hW (by exact_mod_cast (show k - 1 + 1 ≤ k by omega))
  have hfdd : ContDiffOn ℝ (k - 2 : ℕ) (fderiv ℝ (fderiv ℝ f)) W :=
    hfd.fderiv_of_isOpen hW (by
      exact_mod_cast (show k - 2 + 1 ≤ k - 1 by omega))
  have hformula : ContDiffOn ℝ (k - 2 : ℕ) (fun z ↦
      ((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) : ℂ) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single i 1)
          (Complex.I • EuclideanSpace.single j 1) +
        Complex.I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single i 1)
          (Complex.I • EuclideanSpace.single j 1) -
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1))) / 4) W := by
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  apply hformula.congr
  intro z hz
  rw [complexHessian_apply
    ((hf.contDiffAt (hW.mem_nhds hz)).of_le (by exact_mod_cast (show 2 ≤ k by omega))) i j]

private theorem holderBoundOn_congr_of_isOpen
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ} {α C : ℝ≥0} {U : Set E} {f g : E → F}
    (hU : IsOpen U) (hEq : Set.EqOn f g U)
    (hg : HolderBoundOn m α C U g) : HolderBoundOn m α C U f := by
  have hjet (j : ℕ) (x : E) (hx : x ∈ U) :
      iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j g x := by
    have he : f =ᶠ[𝓝 x] g := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hEq hy
    exact (he.iteratedFDeriv ℝ j).self_of_nhds
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    rw [hjet j x hx]
    exact hg.1 j hj x hx
  · intro x hx y hy
    rw [hjet m x hx, hjet m y hy]
    exact hg.2 x hx y hy

private theorem local_hessian_entry_holder
    {n k : ℕ} (hk : 3 ≤ k) {α : ℝ≥0}
    {W V : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (hV : IsOpen V) (hVW : V ⊆ W)
    (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ k f W) (C : ℝ≥0)
    (hdirs : ∀ p : Fin n × Bool,
      HolderBoundOn (k - 1) α C V
        (fun w ↦ fderiv ℝ f w
          (if p.2 then Complex.I • EuclideanSpace.single p.1 1
            else EuclideanSpace.single p.1 1))) (i j : Fin n) :
    ∃ D : ℝ≥0, HolderBoundOn (k - 2 : ℕ) α D V
      (fun w ↦ complexHessian f w i j) := by
  classical
  let direction (p : Fin n × Bool) : EuclideanSpace ℂ (Fin n) :=
    if p.2 then Complex.I • EuclideanSpace.single p.1 1
    else EuclideanSpace.single p.1 1
  have hm : (k - 2 : ℕ) + 1 = k - 1 := by omega
  have hfD : ContDiffOn ℝ (k - 1 : ℕ) (fderiv ℝ f) W :=
    hf.fderiv_of_isOpen hW (by exact_mod_cast (show k - 1 + 1 ≤ k by omega))
  let u (p : Fin n × Bool) : EuclideanSpace ℂ (Fin n) → ℝ :=
    fun w ↦ fderiv ℝ f w (direction p)
  have huSmooth (p : Fin n × Bool) : ContDiffOn ℝ (k - 1 : ℕ) (u p) V := by
    exact (hfD.clm_apply contDiffOn_const).mono hVW
  have huD (p : Fin n × Bool) : ContDiffOn ℝ (k - 2 : ℕ) (fderiv ℝ (u p)) V :=
    (huSmooth p).fderiv_of_isOpen hV (by
      exact_mod_cast (show k - 2 + 1 ≤ k - 1 by omega))
  have hrealSmooth (p : Fin n × Bool) (a : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ fderiv ℝ (u p) w a) V :=
    (huD p).clm_apply contDiffOn_const
  have hrealHolder (p : Fin n × Bool) (a : EuclideanSpace ℂ (Fin n)) :
      HolderBoundOn (k - 2 : ℕ) α
        (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C) V
        (fun w ↦ fderiv ℝ (u p) w a) := by
    have hb : HolderBoundOn ((k - 2 : ℕ) + 1) α C V (u p) := by
      simpa [hm] using hdirs p
    have hjet := fderivHolderBoundOn (k := k - 2) hb
    simpa using
      (holderBoundOn_comp_linear hV (Set.Subset.refl V) (huD p)
        hjet (ContinuousLinearMap.apply ℝ ℝ a))
  have hcomplexSmooth (p : Fin n × Bool) (a : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ (fderiv ℝ (u p) w a : ℂ)) V := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.contDiffOn.comp (hrealSmooth p a)
        (Set.mapsTo_univ _ _)
  have hcomplexHolder (p : Fin n × Bool) (a : EuclideanSpace ℂ (Fin n)) :
      HolderBoundOn (k - 2 : ℕ) α
        (‖Complex.ofRealCLM‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C)) V
        (fun w ↦ (fderiv ℝ (u p) w a : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (holderBoundOn_comp_linear hV (Set.Subset.refl V) (hrealSmooth p a)
        (hrealHolder p a) Complex.ofRealCLM)
  let a : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let b : EuclideanSpace ℂ (Fin n) := Complex.I • EuclideanSpace.single i 1
  let p₀ : Fin n × Bool := (j, false)
  let p₁ : Fin n × Bool := (j, true)
  let q₁ : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ (fderiv ℝ (u p₀) w a : ℂ)
  let q₂ : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ (fderiv ℝ (u p₁) w b : ℂ)
  let q₃ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (u p₁) w a
  let q₄ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (u p₀) w b
  let q₁₂ : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ q₁ w + q₂ w
  let q₃₄ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ q₃ w - q₄ w
  let Li : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ Complex.I
  let Liof : ℝ →L[ℝ] ℂ := Li.comp Complex.ofRealCLM
  let Lquarter : ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℂ (1 / 4 : ℝ)
  let qi : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ Liof (q₃₄ w)
  let qnum : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ q₁₂ w + qi w
  let qout : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦ Lquarter (qnum w)
  have hq₁ : HolderBoundOn (k - 2 : ℕ) α
      (‖Complex.ofRealCLM‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C)) V q₁ := by
    simpa [q₁, u, p₀, a] using hcomplexHolder p₀ a
  have hq₂ : HolderBoundOn (k - 2 : ℕ) α
      (‖Complex.ofRealCLM‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ b‖₊ * C)) V q₂ := by
    simpa [q₂, u, p₁, b] using hcomplexHolder p₁ b
  have hq₁₂ : HolderBoundOn (k - 2 : ℕ) α
      (‖Complex.ofRealCLM‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C) +
        ‖Complex.ofRealCLM‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ b‖₊ * C)) V q₁₂ := by
    simpa [q₁₂] using
      (holderBoundOn_add hV (Set.Subset.refl V)
        (hcomplexSmooth p₀ a) (hcomplexSmooth p₁ b) hq₁ hq₂)
  have hq₃₄ : HolderBoundOn (k - 2 : ℕ) α
      (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C +
        ‖(-1 : ℝ) • (1 : ℝ →L[ℝ] ℝ)‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ b‖₊ * C)) V q₃₄ := by
    simpa [q₃₄, q₃, q₄, u, p₁, p₀, a, b] using
      (holderBoundOn_sub hV (Set.Subset.refl V)
        (hrealSmooth p₁ a) (hrealSmooth p₀ b)
        (hrealHolder p₁ a) (hrealHolder p₀ b))
  have hq₃₄Smooth : ContDiffOn ℝ (k - 2 : ℕ) q₃₄ V := by
    exact (hrealSmooth p₁ a).sub (hrealSmooth p₀ b)
  have hqi : HolderBoundOn (k - 2 : ℕ) α
      (‖Liof‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C +
        ‖(-1 : ℝ) • (1 : ℝ →L[ℝ] ℝ)‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ b‖₊ * C))) V qi := by
    simpa [qi, Liof, q₃₄] using
      (holderBoundOn_comp_linear hV (Set.Subset.refl V) hq₃₄Smooth hq₃₄ Liof)
  have hqiSmooth : ContDiffOn ℝ (k - 2 : ℕ) qi V := by
    exact (Liof.contDiff.contDiffOn.comp hq₃₄Smooth (Set.mapsTo_univ _ _))
  have hqnum : HolderBoundOn (k - 2 : ℕ) α
      ((‖Complex.ofRealCLM‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C) +
        ‖Complex.ofRealCLM‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ b‖₊ * C)) +
        ‖Liof‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C +
          ‖(-1 : ℝ) • (1 : ℝ →L[ℝ] ℝ)‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ b‖₊ * C))) V qnum := by
    simpa [qnum, q₁₂] using
      (holderBoundOn_add hV (Set.Subset.refl V)
        (by fun_prop : ContDiffOn ℝ (k - 2 : ℕ) q₁₂ V) hqiSmooth hq₁₂ hqi)
  have hqnumSmooth : ContDiffOn ℝ (k - 2 : ℕ) qnum V := by
    exact (by fun_prop : ContDiffOn ℝ (k - 2 : ℕ) q₁₂ V).add hqiSmooth
  have hqout : HolderBoundOn (k - 2 : ℕ) α
      (‖Lquarter‖₊ * ((‖Complex.ofRealCLM‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C) +
        ‖Complex.ofRealCLM‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ b‖₊ * C)) +
        ‖Liof‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ a‖₊ * C +
          ‖(-1 : ℝ) • (1 : ℝ →L[ℝ] ℝ)‖₊ * (‖ContinuousLinearMap.apply ℝ ℝ b‖₊ * C)))) V qout := by
    simpa [qout, Lquarter] using
      (holderBoundOn_comp_linear hV (Set.Subset.refl V) hqnumSmooth hqnum Lquarter)
  have hqoutSmooth : ContDiffOn ℝ (k - 2 : ℕ) qout V := by
    exact (Lquarter.contDiff.contDiffOn.comp hqnumSmooth (Set.mapsTo_univ _ _))
  have hEq : Set.EqOn (fun w ↦ complexHessian f w i j) qout V := by
    intro w hw
    have hfw : ContDiffAt ℝ 2 f w :=
      (hf.contDiffAt (hW.mem_nhds (hVW hw))).of_le
        (by exact_mod_cast (show 2 ≤ k by omega))
    change complexHessian f w i j = qout w
    rw [coordinate_complexHessian hfw i j]
    simp [qout, qnum, q₁₂, qi, q₃₄, q₁, q₂, q₃, q₄, Lquarter, Liof, Li,
      u, p₀, p₁, a, b, direction, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.lsmul_apply, div_eq_mul_inv]
    ring
  exact ⟨_, holderBoundOn_congr_of_isOpen hV hEq hqout⟩

/-- Local directional Hölder gains imply local order-`k-2` perturbed metric bounds. -/
theorem locally_holder_metric_of_directional_derivatives
    {n k : ℕ} (hk : 3 ≤ k) {α : ℝ≥0}
    {W : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hf : ContDiffOn ℝ k f W)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ g w i j) W)
    (hfirst : ∀ z ∈ W, ∀ v : EuclideanSpace ℂ (Fin n),
      ∃ V : Set (EuclideanSpace ℂ (Fin n)), ∃ C : ℝ≥0,
        IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        HolderBoundOn (k - 1) α C V (fun w ↦ fderiv ℝ f w v))
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ W) :
    ∃ V : Set (EuclideanSpace ℂ (Fin n)), ∃ C : ℝ≥0,
      IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      ∀ i j, HolderBoundOn (k - 2) α C V
        (fun w ↦ (g w + complexHessian f w) i j) := by
  classical
  let direction (p : Fin n × Bool) : EuclideanSpace ℂ (Fin n) :=
    if p.2 then Complex.I • EuclideanSpace.single p.1 1
    else EuclideanSpace.single p.1 1
  have _hα₀ := hα₀
  obtain ⟨U, C, hU, hzU, hUW, hdirsU⟩ :=
    common_directional_bounds hW f hfirst z hz
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU z hzU
  let r := min (R / 2) (1 / 2)
  let V := Metric.ball z r
  have hV : IsOpen V := Metric.isOpen_ball
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrle : r ≤ 1 / 2 := min_le_right _ _
  have hzV : z ∈ V := Metric.mem_ball_self hrpos
  have hVsubU : V ⊆ U :=
    (Metric.ball_subset_ball (by dsimp [r]; linarith [min_le_left (R / 2) (1 / 2)])).trans hball
  have hVW : V ⊆ W := hVsubU.trans hUW
  have hrR : r < R := by dsimp [r]; linarith [min_le_left (R / 2) (1 / 2)]
  have hclosureU : closure V ⊆ U :=
    Metric.closure_ball_subset_closedBall.trans
      ((Metric.closedBall_subset_ball hrR).trans hball)
  have hclosureW : closure V ⊆ W := hclosureU.trans hUW
  have hVcompact : IsCompact (closure V) :=
    (isCompact_closedBall z r).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  have hVdiam : ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ 1 := by
    intro x hx y hy
    have hx' : dist x z < r := by simpa [V, Metric.mem_ball, dist_comm] using hx
    have hy' : dist y z < r := by simpa [V, Metric.mem_ball, dist_comm] using hy
    apply le_of_lt
    calc
      dist x y ≤ dist x z + dist z y := dist_triangle x z y
      _ = dist x z + dist y z := by rw [dist_comm z y]
      _ < r + r := add_lt_add hx' hy'
      _ ≤ 1 := by nlinarith [hrle]
  have hdirsV (p : Fin n × Bool) :
      HolderBoundOn (k - 1) α C V
        (fun w ↦ fderiv ℝ f w (direction p)) :=
    (hdirsU p).mono_set hVsubU
  have hpair : ∀ ij : Fin n × Fin n, ∃ D : ℝ≥0,
      HolderBoundOn (k - 2 : ℕ) α D V
        (fun w ↦ (g w + complexHessian f w) ij.1 ij.2) := by
    intro ij
    obtain ⟨Dh, hh⟩ := local_hessian_entry_holder hk hW hV hVW f hf C
      hdirsV ij.1 ij.2
    have hgsmooth : ContDiffOn ℝ k (fun w ↦ g w ij.1 ij.2) W :=
      (hg ij.1 ij.2).of_le (by exact_mod_cast (ENat.natCast_lt_top k).le)
    obtain ⟨Dg, hgbound⟩ := compact_derivative_bound hW hgsmooth
      hVcompact hclosureW
    have hgSucc : ContDiffOn ℝ ((k - 2 : ℕ) + 1)
        (fun w ↦ g w ij.1 ij.2) V := by
      exact hgsmooth.mono hVW |>.of_le (by
        exact_mod_cast (show (k - 2 : ℕ) + 1 ≤ k by omega))
    have hgbV : HolderBoundOn (k - 2 : ℕ) α Dg V
        (fun w ↦ g w ij.1 ij.2) := by
      apply holderBoundOn_of_contDiffOn_succ_derivative_bound hV
        (convex_ball z r) hVdiam (le_of_lt hα₁) hgSucc
      intro l hl w hw
      exact hgbound l (le_trans hl (by omega)) w (subset_closure hw)
    have hgSmooth : ContDiffOn ℝ (k - 2 : ℕ)
        (fun w ↦ g w ij.1 ij.2) V :=
      hgsmooth.mono hVW |>.of_le (by
        exact_mod_cast (show (k - 2 : ℕ) ≤ k by omega))
    have hHessSmooth := complexHessian_entry_contDiffOn hk hW f hf ij.1 ij.2
    have hHessSmoothV := hHessSmooth.mono hVW
    have hsum := holderBoundOn_add hV (Set.Subset.refl V)
      hgSmooth hHessSmoothV hgbV hh
    refine ⟨Dg + Dh, ?_⟩
    simpa [Matrix.add_apply] using hsum
  choose Dpair hpairBound using hpair
  refine ⟨V, ∑ ij : Fin n × Fin n, Dpair ij, hV, hzV, hVW, ?_⟩
  intro i j
  have hD : Dpair (i, j) ≤ ∑ ij : Fin n × Fin n, Dpair ij :=
    Finset.single_le_sum (fun ij hij ↦ bot_le) (Finset.mem_univ (i, j))
  exact (hpairBound (i, j)).mono_const hD
