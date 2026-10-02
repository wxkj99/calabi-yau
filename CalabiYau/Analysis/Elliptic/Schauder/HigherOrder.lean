module

public import CalabiYau.Analysis.Elliptic.Schauder.InteriorProvider.Order
import CalabiYau.Analysis.Elliptic.Schauder.OperatorCommutator.HolderBound

open scoped ContDiff NNReal Matrix.Norms.Elementwise

/-!
# The higher-order induction step for interior Schauder estimates

`InteriorSchauderOrder n k` is the exact order-`k` slice of the frozen interior provider.
For `k ≥ 1`, differentiating `L_A u` in a real direction gives

  `L_A (D_v u) = D_v (L_A u) - (D_v A) : D²u`.

The previous slice supplies `u ∈ C^(k+2)` and hence `D_v u ∈ C²`; the differentiated
coefficient and commutator require the order-`k+1` coefficient bound and the corresponding
Holder product estimates. Applying the previous slice to the differentiated equation yields
order `k+1`, with constants depending only on the fixed Schauder data. The induction starts at
`k = 1`, includes dimension `n = 0`, and does not claim the full all-orders provider.
The output slice retains the original quantifiers, including the single constant depending only on
`n`, `k`, `α`, `λ`, `K`, `U`, and `V`.
-/

@[expose] public section

namespace CalabiYau.Schauder

private theorem directional_derivative_contDiffOn_two
    {n k : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} (hU : IsOpen U) (hk : 1 ≤ k)
    (hu : ContDiffOn ℝ (k + 2) u U) (v : EuclideanSpace ℂ (Fin n)) :
    ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ u z v) U := by
  have hD : ContDiffOn ℝ (k + 1) (fderiv ℝ u) U := by
    apply hu.fderiv_of_isOpen hU
    apply WithTop.coe_le_coe.mpr
    norm_num [Nat.cast_add, add_assoc]
  have hv : ContDiffOn ℝ (k + 1)
      (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) U := contDiffOn_const
  have hEval := hD.clm_apply hv
  have hk' : (1 : WithTop ℕ) ≤ (k : WithTop ℕ) := by exact_mod_cast hk
  have htwo : (2 : WithTop ℕ) ≤ (k : WithTop ℕ) + 1 := by
    calc
      (2 : WithTop ℕ) = 1 + 1 := by norm_num
      _ ≤ (k : WithTop ℕ) + 1 := add_le_add_left hk' 1
  exact hEval.of_le (WithTop.coe_le_coe.mpr htwo)

private theorem directional_commutator_contDiffOn {n k : ℕ}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {e : EuclideanSpace ℂ (Fin n)}
    (hU : IsOpen U)
    (hA : ∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U)
    (hu : ContDiffOn ℝ (k + 2) u U) :
    ContDiffOn ℝ k
      (fun z ↦ RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) U := by
  have hAm : ContDiffOn ℝ (k + 1) A U := by
    apply contDiffOn_pi.2
    intro i
    apply contDiffOn_pi.2
    intro j
    exact hA i j
  have hDAij (i j : Fin n) : ContDiffOn ℝ k
      (fun z ↦ fderiv ℝ (fun z ↦ A z i j) z e) U := by
    have hD : ContDiffOn ℝ k (fderiv ℝ (fun z ↦ A z i j)) U := by
      apply (hA i j).fderiv_of_isOpen hU
      exact WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc])
    exact hD.clm_apply contDiffOn_const
  have hADiff (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
      DifferentiableAt ℝ A z := by
    apply differentiableAt_pi.2
    intro i
    apply differentiableAt_pi.2
    intro j
    exact ((hA i j).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num)
  have hDerivativeEntry (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U)
      (i j : Fin n) :
      fderiv ℝ A z e i j = fderiv ℝ (fun z ↦ A z i j) z e := by
    have hrow : ∀ i, DifferentiableAt ℝ (fun z ↦ A z i) z :=
      differentiableAt_pi.1 (hADiff z hz)
    have hscalar : ∀ j, DifferentiableAt ℝ (fun z ↦ A z i j) z :=
      differentiableAt_pi.1 (hrow i)
    change (fderiv ℝ (fun z i j ↦ A z i j) z e) i j = _
    rw [fderiv_pi (𝕜 := ℝ) (φ := fun i z ↦ fun j ↦ A z i j) hrow]
    rw [ContinuousLinearMap.pi_apply]
    change (fderiv ℝ (fun z ↦ A z i) z e) j = _
    rw [fderiv_pi (𝕜 := ℝ) (φ := fun j z ↦ A z i j) hscalar]
    rw [ContinuousLinearMap.pi_apply]
  have hDu : ContDiffOn ℝ (k + 1) (fderiv ℝ u) U := by
    apply hu.fderiv_of_isOpen hU
    exact WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc])
  have hD₂u : ContDiffOn ℝ k (fderiv ℝ (fderiv ℝ u)) U := by
    apply hDu.fderiv_of_isOpen hU
    exact WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc])
  have hD₂eval (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ k (fun z ↦ fderiv ℝ (fderiv ℝ u) z v w) U := by
    have hv : ContDiffOn ℝ k (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) U := contDiffOn_const
    have hw : ContDiffOn ℝ k (fun _ : EuclideanSpace ℂ (Fin n) ↦ w) U := contDiffOn_const
    exact (hD₂u.clm_apply hv).clm_apply hw
  have hEntry (j l : Fin n) :
      ContDiffOn ℝ k (fun z ↦ complexHessian u z j l) U := by
    have hFormula : ContDiffOn ℝ k (fun z ↦
        ((fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) : ℂ) +
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
            (Complex.I • EuclideanSpace.single l 1) +
          Complex.I * (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1)
            (Complex.I • EuclideanSpace.single l 1) -
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
            (EuclideanSpace.single l 1))) / 4) U := by
      simp only [← Complex.ofRealCLM_apply]
      fun_prop
    apply hFormula.congr
    intro z hz
    rw [complexHessian_apply
      (((hu z hz).contDiffAt (hU.mem_nhds hz)).of_le
        (WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc])))]
  have hSum : ContDiffOn ℝ k (fun z ↦
      ∑ i, ∑ j, Complex.reCLM
        (fderiv ℝ (fun z ↦ A z i j) z e * complexHessian u z j i)) U := by
    fun_prop
  have hOp : ContDiffOn ℝ k
      (fun z ↦ RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) U := by
    change ContDiffOn ℝ k
      (fun z ↦ Complex.reCLM ((fderiv ℝ A z e * complexHessian u z).trace)) U
    apply hSum.congr
    intro z hz
    simp [Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply, hDerivativeEntry z hz]
  exact hOp

private theorem holderBoundOn_lower_on_convex
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U s : Set E} {k : ℕ} {α C D : ℝ≥0} {f : E → F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U)
    (hs : Convex ℝ s) (hsU : s ⊆ U)
    (hbound : HolderBoundOn (k + 1) α C s f)
    (hdiam : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D)
    (hα : α ≤ 1) :
    HolderBoundOn k α (max C (C * D ^ ((1 : ℝ) - (α : ℝ)))) s f := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hb := hbound.1 j (le_trans hj (Nat.le_succ k)) x hx
    exact hb.trans (by exact_mod_cast (le_max_left C (C * D ^ ((1 : ℝ) - (α : ℝ)))))
  · let g : E → E [×k]→L[ℝ] F := fun x => iteratedFDeriv ℝ k f x
    have hklt : (↑k : ℕ∞ω) < (↑(k + 1) : ℕ∞ω) := by
      exact_mod_cast (Nat.lt_succ_self k)
    have hLipSeg (x : E) (hx : x ∈ s) (y : E) (hy : y ∈ s) :
        LipschitzOnWith C g (segment ℝ x y) := by
      apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
      · intro z hz
        exact (hf.contDiffAt (hU.mem_nhds (hsU (hs.segment_subset hx hy hz)))).differentiableAt_iteratedFDeriv hklt
      · intro z hz
        have hb := hbound.1 (k + 1) le_rfl z (hs.segment_subset hx hy hz)
        have hb' : ‖fderiv ℝ g z‖ ≤ (C : ℝ) := by
          rw [norm_fderiv_iteratedFDeriv]
          exact hb
        exact_mod_cast hb'
      · exact convex_segment x y
    have hLip : LipschitzOnWith C g s := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      exact (lipschitzOnWith_iff_dist_le_mul.mp (hLipSeg x hx y hy)) x
        (left_mem_segment ℝ x y) y (right_mem_segment ℝ x y)
    let Cα : ℝ≥0 := C * D ^ ((1 : ℝ) - (α : ℝ))
    have hholder : HolderOnWith Cα α g s := by
      simpa [Cα] using hLip.holderOnWith.of_le hdiam hα
    intro x hx y hy
    exact hholder.mono_const (le_max_right C (C * D ^ ((1 : ℝ) - (α : ℝ)))) x hx y hy

private theorem open_set_has_nested_ball_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) :
    ∃ r : U → ℝ,
      (∀ p, 0 < r p ∧ Metric.closedBall (p : E) (4 * r p) ⊆ U) ∧
      U ⊆ ⋃ p : U, Metric.ball (p : E) (r p) := by
  classical
  have hex (p : U) : ∃ R : ℝ, 0 < R ∧ Metric.ball (p : E) R ⊆ U := by
    obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds p.property)
    exact ⟨R, hR, hRball⟩
  let r (p : U) : ℝ := Classical.choose (hex p) / 8
  have hr (p : U) : 0 < r p := by
    dsimp [r]
    exact div_pos (Classical.choose_spec (hex p)).1 (by norm_num)
  have hlarge (p : U) : 4 * r p < Classical.choose (hex p) := by
    dsimp [r]
    have hR := (Classical.choose_spec (hex p)).1
    nlinarith
  have hball (p : U) : Metric.closedBall (p : E) (4 * r p) ⊆ U := by
    intro z hz
    apply (Classical.choose_spec (hex p)).2
    rw [Metric.mem_ball]
    have hz' : dist z (p : E) ≤ 4 * r p := Metric.mem_closedBall.mp hz
    exact lt_of_le_of_lt hz' (hlarge p)
  refine ⟨r, ?_, ?_⟩
  · intro p
    exact ⟨hr p, hball p⟩
  · intro x hx
    let p : U := ⟨x, hx⟩
    refine Set.mem_iUnion.mpr ⟨p, ?_⟩
    rw [Metric.mem_ball]
    simpa [p, dist_self] using hr p

private theorem nested_ball_admissible
    {n : ℕ} (p : EuclideanSpace ℂ (Fin n)) {R : ℝ} (hR : 0 < R) :
    IsCompact (closure (Metric.ball p R)) ∧
      closure (Metric.ball p R) ⊆ Metric.ball p (2 * R) := by
  have hclosure : closure (Metric.ball p R) ⊆ Metric.closedBall p R :=
    Metric.closure_ball_subset_closedBall
  refine ⟨(isCompact_closedBall p R).of_isClosed_subset isClosed_closure hclosure, ?_⟩
  intro x hx
  rw [Metric.mem_ball]
  calc
    dist x p ≤ R := Metric.mem_closedBall.mp (hclosure hx)
    _ < 2 * R := by linarith

private theorem holderBoundOn_lower_on_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α C D : ℝ≥0} {f : E → F} {p : E} {R : ℝ}
    (hD : (D : ℝ) = 2 * R)
    (hf : ContDiffOn ℝ (k + 1) f (Metric.ball p R))
    (hbound : HolderBoundOn (k + 1) α C (Metric.ball p R) f)
    (hα : α ≤ 1) :
    HolderBoundOn k α (max C (C * D ^ ((1 : ℝ) - (α : ℝ))))
      (Metric.ball p R) f := by
  apply holderBoundOn_lower_on_convex Metric.isOpen_ball hf (convex_ball p R)
    (Set.Subset.rfl) hbound ?_ hα
  intro x hx y hy
  have hxR : dist x p < R := by simpa [Metric.mem_ball] using hx
  have hpY : dist p y < R := by simpa [Metric.mem_ball, dist_comm] using hy
  have hxy : dist x y ≤ 2 * R := by
    apply le_of_lt
    calc
      dist x y ≤ dist x p + dist p y := dist_triangle x p y
      _ < R + R := add_lt_add hxR hpY
      _ = 2 * R := by ring
  rw [edist_dist]
  calc
    ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal (2 * R) :=
      ENNReal.ofReal_le_ofReal hxy
    _ = (D : ENNReal) := by rw [← hD, ENNReal.ofReal_coe_nnreal]

private theorem holderBoundOn_sub_of_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {k : ℕ} {α C D : ℝ≥0} {f g : E → F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ k f U) (hg : ContDiffOn ℝ k g U)
    (hfb : HolderBoundOn k α C U f) (hgb : HolderBoundOn k α D U g) :
    HolderBoundOn k α (C + D) U (fun x ↦ f x - g x) := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hfj : ContDiffAt ℝ j f x :=
      (hf.contDiffAt (hU.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
    have hgj : ContDiffAt ℝ j g x :=
      (hg.contDiffAt (hU.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
    change ‖iteratedFDeriv ℝ j (f - g) x‖ ≤ (C + D : ℝ≥0)
    rw [iteratedFDeriv_sub_apply hfj hgj]
    calc
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j g x‖ ≤
          ‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖ := norm_sub_le _ _
      _ ≤ C + D := add_le_add (hfb.1 j hj x hx) (hgb.1 j hj x hx)
  · intro x hx y hy
    have hfx : ContDiffAt ℝ k f x := hf.contDiffAt (hU.mem_nhds hx)
    have hgx : ContDiffAt ℝ k g x := hg.contDiffAt (hU.mem_nhds hx)
    have hfy : ContDiffAt ℝ k f y := hf.contDiffAt (hU.mem_nhds hy)
    have hgy : ContDiffAt ℝ k g y := hg.contDiffAt (hU.mem_nhds hy)
    have hderivx : iteratedFDeriv ℝ k (fun z ↦ f z - g z) x =
        iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k g x := by
      change iteratedFDeriv ℝ k (f - g) x = _
      rw [iteratedFDeriv_sub_apply hfx hgx]
    have hderivy : iteratedFDeriv ℝ k (fun z ↦ f z - g z) y =
        iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k g y := by
      change iteratedFDeriv ℝ k (f - g) y = _
      rw [iteratedFDeriv_sub_apply hfy hgy]
    rw [hderivx, hderivy]
    have hgb' : edist (-iteratedFDeriv ℝ k g x) (-iteratedFDeriv ℝ k g y) ≤
        (D : ENNReal) * edist x y ^ (α : ℝ) := by
      simpa only [edist_neg_neg] using hgb.2 x hx y hy
    calc
      edist (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k g x)
          (iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k g y) ≤
          edist (iteratedFDeriv ℝ k f x) (iteratedFDeriv ℝ k f y) +
            edist (-iteratedFDeriv ℝ k g x) (-iteratedFDeriv ℝ k g y) := by
        simpa only [sub_eq_add_neg, edist_neg_neg] using
          (edist_add_add_le (iteratedFDeriv ℝ k f x) (-iteratedFDeriv ℝ k g x)
            (iteratedFDeriv ℝ k f y) (-iteratedFDeriv ℝ k g y))
      _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) +
          (D : ENNReal) * edist x y ^ (α : ℝ) :=
        add_le_add (hfb.2 x hx y hy) hgb'
      _ = ((C + D : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_add]
        ring

private theorem contDiffOn_of_open_cover
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {f : E → F} {k : ℕ}
    (c : ι → Set E) (hcopen : ∀ i, IsOpen (c i))
    (hcover : U ⊆ ⋃ i, c i) (hsubset : ∀ i, c i ⊆ U)
    (hlocal : ∀ i, ContDiffOn ℝ k f (c i)) :
    ContDiffOn ℝ k f U := by
  have hunion : (⋃ i, c i) = U := by
    apply subset_antisymm
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      exact hsubset i hxi
    · exact hcover
  rw [← hunion]
  exact ContDiffOn.iUnion_of_isOpen hlocal hcopen

private theorem directional_forcing_holder
    {n k : ℕ} {α C₁ C₂ : ℝ≥0}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {e : EuclideanSpace ℂ (Fin n)}
    (hU : IsOpen U)
    (hA : ∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U)
    (hu : ContDiffOn ℝ (k + 2) u U)
    (hLu : ContDiffOn ℝ (k + 1) (complexEllipticOp A u) U)
    (hLuHolder : HolderBoundOn k α C₁ U
      (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e))
    (hCommHolder : HolderBoundOn k α C₂ U
      (fun z ↦ RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace))) :
    HolderBoundOn k α (C₁ + C₂) U
      (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e -
        RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) := by
  have hDerivativeMap : ContDiffOn ℝ k
      (fderiv ℝ (complexEllipticOp A u)) U := by
    apply hLu.fderiv_of_isOpen hU
    exact WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc])
  have hDerivative : ContDiffOn ℝ k
      (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e) U :=
    hDerivativeMap.clm_apply contDiffOn_const
  have hComm : ContDiffOn ℝ k
      (fun z ↦ RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) U :=
    directional_commutator_contDiffOn hU hA hu
  exact holderBoundOn_sub_of_contDiffOn hU hDerivative hComm hLuHolder hCommHolder

private theorem compact_convex_ball_cover
    {n : ℕ} {K U : Set (EuclideanSpace ℂ (Fin n))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W ∧ K ⊆ W ∧
      IsCompact (closure W) ∧ closure W ⊆ U ∧
      ∃ s : Finset K, ∃ r : K → ℝ,
        (∀ p ∈ s, 0 < r p ∧ Metric.closedBall (p : EuclideanSpace ℂ (Fin n)) (4 * r p) ⊆ W) ∧
        K ⊆ ⋃ p ∈ s, Metric.ball (p : EuclideanSpace ℂ (Fin n)) (r p / 2) := by
  obtain ⟨ρ, hρ, hρU⟩ := hK.exists_cthickening_subset_open hU hKU
  let δ : ℝ := ρ
  let W : Set (EuclideanSpace ℂ (Fin n)) := Metric.thickening (δ / 2) K
  have hδ : 0 < δ := hρ
  have hhalf : 0 < δ / 2 := by dsimp [δ]; positivity
  have hhalfρ : δ / 2 < ρ := by dsimp [δ]; exact half_lt_self hρ
  have hWopen : IsOpen W := Metric.isOpen_thickening
  have hKW : K ⊆ W := Metric.self_subset_thickening hhalf K
  have hWclosure : closure W ⊆ Metric.cthickening (δ / 2) K :=
    Metric.closure_thickening_subset_cthickening (δ / 2) K
  have hctcompact : IsCompact (Metric.cthickening (δ / 2) K) :=
    hK.cthickening (r := δ / 2)
  have hWcompact : IsCompact (closure W) :=
    hctcompact.of_isClosed_subset isClosed_closure hWclosure
  have hWsubset : Metric.cthickening (δ / 2) K ⊆ Metric.cthickening ρ K :=
    (Metric.cthickening_subset_thickening' hρ hhalfρ K).trans
      (Metric.thickening_subset_cthickening ρ K)
  have hWclosureU : closure W ⊆ U := hWclosure.trans (hWsubset.trans hρU)
  have hex (p : K) : ∃ R : ℝ, 0 < R ∧ Metric.ball (p : EuclideanSpace ℂ (Fin n)) R ⊆ W := by
    obtain ⟨R, hR, hRball⟩ := Metric.mem_nhds_iff.mp (hWopen.mem_nhds (hKW p.property))
    exact ⟨R, hR, hRball⟩
  let r (p : K) : ℝ := Classical.choose (hex p) / 8
  have hrpos (p : K) : 0 < r p := by
    dsimp [r]
    exact div_pos (Classical.choose_spec (hex p)).1 (by norm_num)
  have hlarge (p : K) : Metric.closedBall (p : EuclideanSpace ℂ (Fin n)) (4 * r p) ⊆ W := by
    have hR := (Classical.choose_spec (hex p)).1
    have hRball := (Classical.choose_spec (hex p)).2
    have h4r : 4 * r p < Classical.choose (hex p) := by
      dsimp [r]
      nlinarith
    intro z hz
    apply hRball
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at hz
    have hz' : dist z (p : EuclideanSpace ℂ (Fin n)) ≤ 4 * r p := by
      simpa [dist_comm] using hz
    have hlt : dist z (p : EuclideanSpace ℂ (Fin n)) < Classical.choose (hex p) :=
      lt_of_le_of_lt hz' h4r
    simpa [dist_comm] using hlt
  have hrhalf (p : K) : 0 < r p / 2 := div_pos (hrpos p) (by norm_num)
  have hcover : K ⊆ ⋃ p : K,
      Metric.ball (p : EuclideanSpace ℂ (Fin n)) (r p / 2) := by
    intro z hz
    let p : K := ⟨z, hz⟩
    refine Set.mem_iUnion.2 ⟨p, ?_⟩
    rw [Metric.mem_ball]
    simpa [p, dist_self] using hrhalf p
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun p : K => Metric.ball (p : EuclideanSpace ℂ (Fin n)) (r p / 2))
    (fun _ => Metric.isOpen_ball) hcover
  refine ⟨W, hWopen, hKW, hWcompact, hWclosureU, s, r, ?_, ?_⟩
  · intro p hp
    exact ⟨hrpos p, hlarge p⟩
  · intro z hz
    have hz' := hs hz
    rcases Set.mem_iUnion₂.mp hz' with ⟨p, hp, hzp⟩
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hzp⟩

private theorem iteratedFDeriv_directional_eval_private
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {k : ℕ} {f : E → F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U) {x : E} (hx : x ∈ U) (v : E) :
    ∀ m : Fin k → E, iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ f y v) x m =
      (ContinuousLinearMap.apply ℝ F v)
        (((continuousMultilinearCurryRightEquiv' ℝ k E F)
          (iteratedFDeriv ℝ (k + 1) f x)) m) := by
  have hD : ContDiffOn ℝ k (fderiv ℝ f) U := by
    apply hf.fderiv_of_isOpen hU
    exact_mod_cast (Nat.le_refl (k + 1))
  have hg : ContDiffOn ℝ k (fun y ↦ fderiv ℝ f y v) U :=
    hD.clm_apply contDiffOn_const
  have hDtotal (m : ℕ) (hm : m ≤ k) :
      iteratedFDerivWithin ℝ m (fderiv ℝ f) U x = iteratedFDeriv ℝ m (fderiv ℝ f) x := by
    apply iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    · exact (hD.contDiffAt (hU.mem_nhds hx)).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hm))
    · exact hx
  have hgtotal (m : ℕ) (hm : m ≤ k) :
      iteratedFDerivWithin ℝ m (fun y ↦ fderiv ℝ f y v) U x =
        iteratedFDeriv ℝ m (fun y ↦ fderiv ℝ f y v) x := by
    apply iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    · exact (hg.contDiffAt (hU.mem_nhds hx)).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hm))
    · exact hx
  intro m
  rw [← hgtotal k le_rfl]
  rw [iteratedFDerivWithin_clm_apply_const_apply hU.uniqueDiffOn hD le_rfl hx]
  rw [hDtotal k le_rfl]
  simp [continuousMultilinearCurryRightEquiv_apply', iteratedFDeriv_succ_apply_right]

private theorem iteratedFDeriv_snoc_directional
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {k : ℕ} {f : E → F} {x : E} {e : E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1) f U) (hx : x ∈ U)
    (m : Fin k → E) :
    iteratedFDeriv ℝ (k + 1) f x (Fin.snoc m e) =
      iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ f y e) x m := by
  rw [iteratedFDeriv_directional_eval_private hU hf hx e m]
  simp [continuousMultilinearCurryRightEquiv_apply']

private theorem holderBoundOn_directionalDerivative_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {k : ℕ} {α C : ℝ≥0} {f : E → F}
    (hU : IsOpen U)
    (hf : ContDiffOn ℝ (k + 1) f U)
    (hbound : HolderBoundOn (k + 1) α C U f) (v : E) :
    HolderBoundOn k α (C * ‖v‖₊) U (fun z ↦ fderiv ℝ f z v) := by
  have hD : ContDiffOn ℝ k (fderiv ℝ f) U := by
    apply hf.fderiv_of_isOpen hU
    exact_mod_cast (Nat.le_refl (k + 1))
  let g : E → F := fun z ↦ fderiv ℝ f z v
  let curry := continuousMultilinearCurryRightEquiv' ℝ k E F
  let postOp (j : ℕ) : (E [×j]→L[ℝ] (E →L[ℝ] F)) →L[ℝ] (E [×j]→L[ℝ] F) :=
    ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => E)
      (E →L[ℝ] F) F (ContinuousLinearMap.apply ℝ F v)
  let post : (E [×k]→L[ℝ] (E →L[ℝ] F)) →L[ℝ] (E [×k]→L[ℝ] F) := postOp k
  have hEval : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
    intro L
    simpa [mul_comm] using L.le_opNorm v
  have hPostApplied (j : ℕ) (T : E [×j]→L[ℝ] (E →L[ℝ] F)) :
      ‖postOp j T‖ ≤ ‖v‖ * ‖T‖ := by
    change ‖(ContinuousLinearMap.apply ℝ F v).compContinuousMultilinearMap T‖ ≤ _
    exact ((ContinuousLinearMap.apply ℝ F v).norm_compContinuousMultilinearMap_le T).trans
      (mul_le_mul_of_nonneg_right hEval (norm_nonneg _))
  have hPostNorm (j : ℕ) : ‖postOp j‖ ≤ ‖v‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
    exact hPostApplied j
  have hPostNN : ‖post‖₊ ≤ ‖v‖₊ := by exact_mod_cast hPostNorm k
  have hCurryHolder : HolderOnWith C α
      (fun z ↦ curry (iteratedFDeriv ℝ (k + 1) f z)) U := by
    intro x hx y hy
    simpa [edist_dist, curry.dist_map] using hbound.2 x hx y hy
  have hPostLip : LipschitzWith ‖post‖₊ post := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [dist_eq_norm]
    calc
      ‖post a - post b‖ = ‖post (a - b)‖ := by rw [map_sub]
      _ ≤ ‖post‖ * ‖a - b‖ := post.le_opNorm _
      _ = (‖post‖₊ : ℝ) * dist a b := by simp [dist_eq_norm]
  have hPostHolder : HolderOnWith ‖post‖₊ 1 post Set.univ :=
    (holderWith_one.mpr hPostLip).holderOnWith Set.univ
  have hcomp : HolderOnWith (‖post‖₊ * C) α
      (fun z ↦ post (curry (iteratedFDeriv ℝ (k + 1) f z))) U := by
    simpa [Function.comp_def, NNReal.rpow_one] using
      hPostHolder.comp hCurryHolder (by intro z hz; exact Set.mem_univ _)
  have hconst : ‖post‖₊ * C ≤ C * ‖v‖₊ := by
    calc
      ‖post‖₊ * C ≤ ‖v‖₊ * C :=
        mul_le_mul_of_nonneg_right hPostNN (show 0 ≤ C from bot_le)
      _ = C * ‖v‖₊ := by ring
  have hJetEq (z : E) (hz : z ∈ U) :
      post (curry (iteratedFDeriv ℝ (k + 1) f z)) = iteratedFDeriv ℝ k g z := by
    ext m
    simpa [post, postOp, curry, g, ContinuousLinearMap.compContinuousMultilinearMapL_apply,
        continuousMultilinearCurryRightEquiv_apply'] using
      (iteratedFDeriv_directional_eval_private hU hf hz v m).symm
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hjbound : j + 1 ≤ k + 1 := Nat.succ_le_succ hj
    have hjboundTop : (j : WithTop ℕ) + 1 ≤ (k : WithTop ℕ) + 1 := by
      exact_mod_cast hjbound
    have hf' : ContDiffOn ℝ (j + 1) f U :=
      hf.of_le (WithTop.coe_le_coe.mpr hjboundTop)
    have hJetEqj :
        iteratedFDeriv ℝ j g z = postOp j
          ((continuousMultilinearCurryRightEquiv' ℝ j E F)
            (iteratedFDeriv ℝ (j + 1) f z)) := by
      ext m
      simpa [postOp, ContinuousLinearMap.compContinuousMultilinearMapL_apply] using
        iteratedFDeriv_directional_eval_private hU hf' hz v m
    have hsrc := hbound.1 (j + 1) hjbound z hz
    calc
      ‖iteratedFDeriv ℝ j g z‖ =
          ‖postOp j ((continuousMultilinearCurryRightEquiv' ℝ j E F)
              (iteratedFDeriv ℝ (j + 1) f z))‖ := congrArg norm hJetEqj
      _ ≤ ‖v‖ *
          ‖(continuousMultilinearCurryRightEquiv' ℝ j E F)
            (iteratedFDeriv ℝ (j + 1) f z)‖ := hPostApplied j _
      _ = ‖v‖ * ‖iteratedFDeriv ℝ (j + 1) f z‖ := by
        rw [(continuousMultilinearCurryRightEquiv' ℝ j E F).norm_map]
      _ ≤ ‖v‖ * C := mul_le_mul_of_nonneg_left hsrc (norm_nonneg _)
      _ = (C * ‖v‖₊ : ℝ) := by simp [mul_comm]
  · intro z hz w hw
    rw [← hJetEq z hz, ← hJetEq w hw]
    exact (hcomp.mono_const hconst) z hz w hw

private theorem holderBoundOn_succ_of_all_directional
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U K : Set E} {m : ℕ} {α C₀ C₁ : ℝ≥0} {f : E → F}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ (m + 2) f U)
    (hbase : HolderBoundOn (m + 1) α C₀ K f)
    (hdir : ∀ v : E, HolderBoundOn (m + 1) α (C₁ * ‖v‖₊) K
      (fun x ↦ fderiv ℝ f x v)) :
    HolderBoundOn (m + 2) α (max C₀ C₁) K f := by
  have horder (q : ℕ) (hq : q ≤ m + 1) :
      (q : ℕ∞ω) + 1 ≤ (m : ℕ∞ω) + 2 := by
    calc
      (q : ℕ∞ω) + 1 = ((q + 1 : ℕ) : ℕ∞ω) := by simp
      _ ≤ ((m + 2 : ℕ) : ℕ∞ω) := by exact_mod_cast (show q + 1 ≤ m + 2 by omega)
      _ = (m : ℕ∞ω) + 2 := by simp
  have hdir_bound (q : ℕ) (hq : q ≤ m + 1) (x : E) (hx : x ∈ K) :
      ‖iteratedFDeriv ℝ (q + 1) f x‖ ≤ C₁ := by
    have hfq : ContDiffOn ℝ (q + 1) f U := hf.of_le (horder q hq)
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro w
    let v : E := w (Fin.last q)
    let mv : Fin q → E := Fin.init w
    have heval : iteratedFDeriv ℝ (q + 1) f x w =
        iteratedFDeriv ℝ q (fun y ↦ fderiv ℝ f y v) x mv := by
      rw [← Fin.snoc_init_self w]
      exact iteratedFDeriv_snoc_directional hU hfq (hKU hx) mv
    have hsource := (hdir v).1 q hq x hx
    have hprod : ∏ i : Fin (q + 1), ‖w i‖ =
        (∏ i : Fin q, ‖mv i‖) * ‖v‖ := by
      rw [Fin.prod_univ_castSucc]
      change (∏ i : Fin q, ‖w (Fin.castSucc i)‖) * ‖w (Fin.last q)‖ =
        (∏ i : Fin q, ‖w (Fin.castSucc i)‖) * ‖w (Fin.last q)‖
      rfl
    rw [heval]
    calc
      ‖iteratedFDeriv ℝ q (fun y ↦ fderiv ℝ f y v) x mv‖ ≤
          ‖iteratedFDeriv ℝ q (fun y ↦ fderiv ℝ f y v) x‖ *
            ∏ i : Fin q, ‖mv i‖ :=
        (iteratedFDeriv ℝ q (fun y ↦ fderiv ℝ f y v) x).le_opNorm mv
      _ ≤ (C₁ * ‖v‖₊ : ℝ) * ∏ i : Fin q, ‖mv i‖ := by
        gcongr
        exact hsource
      _ = (C₁ : ℝ) * ((∏ i : Fin q, ‖mv i‖) * ‖v‖) := by
        push_cast
        ring
      _ = (C₁ : ℝ) * ∏ i : Fin (q + 1), ‖w i‖ := by rw [← hprod]
  have htop : HolderOnWith C₁ α (iteratedFDeriv ℝ (m + 2) f) K := by
    intro x hx y hy
    have hdiff : ‖iteratedFDeriv ℝ (m + 2) f x -
        iteratedFDeriv ℝ (m + 2) f y‖ ≤
        (C₁ : ℝ) * dist x y ^ (α : ℝ) := by
      apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
      intro w
      change ‖iteratedFDeriv ℝ (m + 2) f x w - iteratedFDeriv ℝ (m + 2) f y w‖ ≤ _
      let v : E := w (Fin.last (m + 1))
      let mv : Fin (m + 1) → E := Fin.init w
      have hevalx : iteratedFDeriv ℝ (m + 2) f x w =
          iteratedFDeriv ℝ (m + 1) (fun z ↦ fderiv ℝ f z v) x mv := by
        rw [← Fin.snoc_init_self w]
        exact iteratedFDeriv_snoc_directional hU
          (hf.of_le (by norm_num [add_assoc])) (hKU hx) mv
      have hevaly : iteratedFDeriv ℝ (m + 2) f y w =
          iteratedFDeriv ℝ (m + 1) (fun z ↦ fderiv ℝ f z v) y mv := by
        rw [← Fin.snoc_init_self w]
        exact iteratedFDeriv_snoc_directional hU
          (hf.of_le (by norm_num [add_assoc])) (hKU hy) mv
      have hprod : ∏ i : Fin (m + 2), ‖w i‖ =
          (∏ i : Fin (m + 1), ‖mv i‖) * ‖v‖ := by
        rw [Fin.prod_univ_castSucc]
        change (∏ i : Fin (m + 1), ‖w (Fin.castSucc i)‖) * ‖w (Fin.last (m + 1))‖ =
          (∏ i : Fin (m + 1), ‖w (Fin.castSucc i)‖) * ‖w (Fin.last (m + 1))‖
        rfl
      rw [hevalx, hevaly]
      have hdist := (hdir v).2.dist_le hx hy
      rw [dist_eq_norm] at hdist
      calc
        ‖iteratedFDeriv ℝ (m + 1) (fun z ↦ fderiv ℝ f z v) x mv -
            iteratedFDeriv ℝ (m + 1) (fun z ↦ fderiv ℝ f z v) y mv‖ ≤
            ‖iteratedFDeriv ℝ (m + 1) (fun z ↦ fderiv ℝ f z v) x -
              iteratedFDeriv ℝ (m + 1) (fun z ↦ fderiv ℝ f z v) y‖ *
                ∏ i : Fin (m + 1), ‖mv i‖ :=
          (iteratedFDeriv ℝ (m + 1) (fun z ↦ fderiv ℝ f z v) x -
            iteratedFDeriv ℝ (m + 1) (fun z ↦ fderiv ℝ f z v) y).le_opNorm mv
        _ ≤ ((C₁ * ‖v‖₊ : ℝ) * dist x y ^ (α : ℝ)) *
            ∏ i : Fin (m + 1), ‖mv i‖ := by
          gcongr
          simpa only [NNReal.coe_mul] using hdist
        _ = (C₁ : ℝ) * dist x y ^ (α : ℝ) *
            ((∏ i : Fin (m + 1), ‖mv i‖) * ‖v‖) := by
          push_cast
          ring_nf
        _ = (C₁ : ℝ) * dist x y ^ (α : ℝ) *
            ∏ i : Fin (m + 2), ‖w i‖ := by rw [← hprod]
    rw [edist_dist]
    calc
      ENNReal.ofReal (dist (iteratedFDeriv ℝ (m + 2) f x)
          (iteratedFDeriv ℝ (m + 2) f y)) ≤
          ENNReal.ofReal ((C₁ : ℝ) * dist x y ^ (α : ℝ)) := by
        exact ENNReal.ofReal_le_ofReal (by simpa [dist_eq_norm] using hdiff)
      _ = (C₁ : ENNReal) * ENNReal.ofReal (dist x y) ^ (α : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg]
      _ = (C₁ : ENNReal) * edist x y ^ (α : ℝ) := by rw [edist_dist]
  refine ⟨?_, htop.mono_const (le_max_right C₀ C₁)⟩
  intro j hj x hx
  by_cases hj0 : j = 0
  · subst j
    exact (hbase.1 0 (Nat.zero_le _) x hx).trans (by exact_mod_cast le_max_left C₀ C₁)
  · by_cases hjle : j ≤ m + 1
    · exact (hbase.1 j hjle x hx).trans (by exact_mod_cast le_max_left C₀ C₁)
    · have hjEq : j = m + 2 := by omega
      subst j
      exact (hdir_bound (m + 1) le_rfl x hx).trans
        (by exact_mod_cast le_max_right C₀ C₁)

private theorem contDiffOn_clm_apply_private
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : ℕ∞ω} {s : Set D} {f : D → E →L[ℝ] F} :
    ContDiffOn ℝ m f s ↔ ∀ y, ContDiffOn ℝ m (fun x ↦ f x y) s := by
  refine ⟨fun h y ↦ h.clm_apply contDiffOn_const, fun h ↦ ?_⟩
  let d := Module.finrank ℝ E
  have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[ℝ] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  have hcomp : e₂.symm ∘ (e₂ ∘ f) = f := by
    funext x
    simp
  rw [← hcomp]
  exact e₂.symm.contDiff.comp_contDiffOn (contDiffOn_pi.mpr fun i ↦ h _)

private theorem higherStep_differentiated_operator_identity_on
    {n k : ℕ} (hk : 1 ≤ k) {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U)
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U)
    (hu : ContDiffOn ℝ (k + 2) u U)
    (e z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
    complexEllipticOp A (fun w ↦ fderiv ℝ u w e) z =
      fderiv ℝ (complexEllipticOp A u) z e -
        RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace) := by
  have hAorder : (1 : ℕ∞ω) ≤ (k : ℕ∞ω) + 1 := by
    exact WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc])
  have hkle : 3 ≤ k + 2 := by omega
  have hinner : (3 : ℕ∞) ≤ (k : ℕ∞) + 2 := by
    have hcast : (k : ℕ∞) + 2 = ((k + 2 : ℕ) : ℕ∞) := by simp
    rw [hcast]
    exact_mod_cast hkle
  have huOrder : (3 : ℕ∞ω) ≤ (k : ℕ∞ω) + 2 :=
    WithTop.coe_le_coe.mpr hinner
  have hA' : ∀ i j, ContDiffAt ℝ 1 (fun w ↦ A w i j) z := by
    intro i j
    exact ((hA i j).contDiffAt (hU.mem_nhds hz)).of_le hAorder
  have hu' : ContDiffAt ℝ 3 u z := by
    exact (hu.contDiffAt (hU.mem_nhds hz)).of_le huOrder
  have hcomm := fderiv_complexEllipticOp A u (e := e) hA' hu'
  linarith

private theorem differentiated_operator_holder_data
    {n k : ℕ} {α K₁ Kcomm : ℝ≥0}
    {U : Set (EuclideanSpace ℂ (Fin n))}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U)
    (hA : ∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U)
    (hu : ContDiffOn ℝ (k + 2) u U)
    (hLu : ContDiffOn ℝ (k + 1) (complexEllipticOp A u) U)
    (hLuHolder : HolderBoundOn (k + 1) α K₁ U (complexEllipticOp A u))
    (hEq : ∀ e z, z ∈ U →
      complexEllipticOp A (fun w ↦ fderiv ℝ u w e) z =
        fderiv ℝ (complexEllipticOp A u) z e -
          RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace))
    (hCommHolder : ∀ e, HolderBoundOn k α (Kcomm * ‖e‖₊) U
      (fun z ↦ RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace))) :
    ∀ e, ContDiffOn ℝ k (complexEllipticOp A (fun w ↦ fderiv ℝ u w e)) U ∧
      HolderBoundOn k α ((K₁ + Kcomm) * ‖e‖₊) U
        (complexEllipticOp A (fun w ↦ fderiv ℝ u w e)) := by
  have hLuDerivativeMap : ContDiffOn ℝ k
      (fderiv ℝ (complexEllipticOp A u)) U := by
    apply hLu.fderiv_of_isOpen hU
    exact WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc])
  have hCommDiff (e : EuclideanSpace ℂ (Fin n)) : ContDiffOn ℝ k
      (fun z ↦ RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) U :=
    directional_commutator_contDiffOn hU hA hu
  intro e
  have hLuDerivative : ContDiffOn ℝ k
      (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e) U :=
    hLuDerivativeMap.clm_apply contDiffOn_const
  have hLuDirectionalHolder := holderBoundOn_directionalDerivative_local
    hU hLu hLuHolder e
  have hForceHolder := directional_forcing_holder hU hA hu hLu
    hLuDirectionalHolder (hCommHolder e)
  have hForceDiff : ContDiffOn ℝ k
      (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e -
        RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) U :=
    hLuDerivative.sub (hCommDiff e)
  have hPointwise : Set.EqOn (complexEllipticOp A (fun w ↦ fderiv ℝ u w e))
      (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e -
        RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) U := by
    intro z hz
    exact hEq e z hz
  have hForceHolder' : HolderBoundOn k α ((K₁ + Kcomm) * ‖e‖₊) U
      (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e -
        RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) := by
    convert hForceHolder using 1
    ring
  have hOpDiff : ContDiffOn ℝ k
      (complexEllipticOp A (fun w ↦ fderiv ℝ u w e)) U := by
    apply hForceDiff.congr
    intro z hz
    exact hPointwise hz
  have hOpJet (j : ℕ) (hj : j ≤ k) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
      iteratedFDerivWithin ℝ j
          (complexEllipticOp A (fun w ↦ fderiv ℝ u w e)) U z =
        iteratedFDeriv ℝ j (complexEllipticOp A (fun w ↦ fderiv ℝ u w e)) z := by
    apply iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    · exact hOpDiff.contDiffAt (hU.mem_nhds hz) |>.of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
    · exact hz
  have hForceJet (j : ℕ) (hj : j ≤ k) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
      iteratedFDerivWithin ℝ j
          (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e -
            RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) U z =
        iteratedFDeriv ℝ j
          (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e -
            RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) z := by
    apply iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    · exact hForceDiff.contDiffAt (hU.mem_nhds hz) |>.of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
    · exact hz
  have hJet (j : ℕ) (hj : j ≤ k) (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
      iteratedFDeriv ℝ j (complexEllipticOp A (fun w ↦ fderiv ℝ u w e)) z =
        iteratedFDeriv ℝ j
          (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e -
            RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) z := by
    calc
      iteratedFDeriv ℝ j (complexEllipticOp A (fun w ↦ fderiv ℝ u w e)) z =
          iteratedFDerivWithin ℝ j
            (complexEllipticOp A (fun w ↦ fderiv ℝ u w e)) U z := (hOpJet j hj z hz).symm
      _ = iteratedFDerivWithin ℝ j
            (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e -
              RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) U z :=
          iteratedFDerivWithin_congr hPointwise hz j
      _ = iteratedFDeriv ℝ j
            (fun z ↦ fderiv ℝ (complexEllipticOp A u) z e -
              RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) z := hForceJet j hj z hz
  refine ⟨?_, ?_⟩
  · apply hForceDiff.congr
    intro z hz
    exact hPointwise hz
  · refine ⟨?_, ?_⟩
    · intro j hj z hz
      rw [hJet j hj z hz]
      exact hForceHolder'.1 j hj z hz
    · intro z hz w hw
      rw [hJet k le_rfl z hz, hJet k le_rfl w hw]
      exact hForceHolder'.2 z hz w hw

private theorem holderBoundOn_nnreal_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α C c : ℝ≥0} {s U : Set E} {f : E → F}
    (hU : IsOpen U) (hsU : s ⊆ U)
    (hcont : ContDiffOn ℝ k f U)
    (h : HolderBoundOn k α C s f) :
    HolderBoundOn k α (c * C) s (fun x ↦ (c : ℝ) • f x) := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hjet := iteratedFDeriv_const_smul_apply (a := (c : ℝ))
      ((hcont.contDiffAt (hU.mem_nhds (hsU hx))).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast hj)))
    change ‖iteratedFDeriv ℝ j ((c : ℝ) • f) x‖ ≤ _
    rw [hjet, norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg c)]
    exact mul_le_mul_of_nonneg_left (h.1 j hj x hx) (NNReal.coe_nonneg c)
  · have htop : HolderOnWith (C * c) α
        (fun x ↦ (c : ℝ) • iteratedFDeriv ℝ k f x) s := by
      intro x hx y hy
      change edist ((c : ℝ) • iteratedFDeriv ℝ k f x)
        ((c : ℝ) • iteratedFDeriv ℝ k f y) ≤ _
      rw [edist_smul₀]
      have hc : ‖(c : ℝ)‖₊ = c := by simp
      rw [hc]
      calc
        (c : ENNReal) * edist (iteratedFDeriv ℝ k f x)
            (iteratedFDeriv ℝ k f y) ≤
            (c : ENNReal) * ((C : ENNReal) * edist x y ^ (α : ℝ)) := by
          gcongr
          exact h.2 x hx y hy
        _ = (C * c : ℝ≥0) * edist x y ^ (α : ℝ) := by
          simp only [ENNReal.coe_mul]
          ring
    rw [show c * C = C * c by ring]
    intro x hx y hy
    have hxjet := iteratedFDeriv_const_smul_apply (a := (c : ℝ))
      ((hcont.contDiffAt (hU.mem_nhds (hsU hx))).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast le_rfl)))
    have hyjet := iteratedFDeriv_const_smul_apply (a := (c : ℝ))
      ((hcont.contDiffAt (hU.mem_nhds (hsU hy))).of_le
        (WithTop.coe_le_coe.mpr (by exact_mod_cast le_rfl)))
    change edist (iteratedFDeriv ℝ k ((c : ℝ) • f) x)
      (iteratedFDeriv ℝ k ((c : ℝ) • f) y) ≤ _
    rw [hxjet, hyjet]
    exact htop x hx y hy

private theorem holderBoundOn_all_directions_of_unit
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α C : ℝ≥0} {s U : Set E}
    (hU : IsOpen U) (hsU : s ⊆ U)
    (g : E → E → F)
    (hcont : ∀ v, ContDiffOn ℝ k (g v) U)
    (hlinear : ∀ (r : ℝ) (v : E), g (r • v) = fun x ↦ r • g v x)
    (hunit : ∀ v, ‖v‖ ≤ 1 → HolderBoundOn k α C s (g v)) :
    ∀ e, HolderBoundOn k α (C * ‖e‖₊) s (g e) := by
  intro e
  let c : ℝ≥0 := ‖e‖₊
  let v : E := (c : ℝ)⁻¹ • e
  have hcReal : (c : ℝ) = ‖e‖ := by simp [c]
  have hnorm : ‖v‖ ≤ 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg c.coe_nonneg, hcReal]
    by_cases he : ‖e‖ = 0
    · simp [he]
    · have he0 : e ≠ 0 := by
        intro hz
        apply he
        simp [hz]
      have hp : 0 < ‖e‖ := norm_pos_iff.mpr he0
      exact (inv_mul_le_one₀ hp).2 le_rfl

  have heq : (c : ℝ) • v = e := by
    dsimp [v]
    by_cases he : ‖e‖ = 0
    · have he0 : e = 0 := norm_eq_zero.mp he
      simp [he0]
    · simp only [smul_smul]
      have hcne : (c : ℝ) ≠ 0 := by simpa [hcReal] using (norm_ne_zero_iff.mpr he)
      rw [mul_inv_cancel₀ hcne, one_smul]
  have hscaled : HolderBoundOn k α (c * C) s (fun x ↦ (c : ℝ) • g v x) :=
    holderBoundOn_nnreal_smul (c := c) hU hsU (hcont v) (hunit v hnorm)
  have hfunc : g e = fun x ↦ (c : ℝ) • g v x := by
    rw [← heq]
    exact hlinear (c : ℝ) v
  rw [hfunc]
  simpa [c, mul_comm] using hscaled

private theorem exists_directional_commutator_all_directions
    {n k : ℕ} {α K : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {U V W : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hV : IsOpen V) (hVconvex : Convex ℝ V)
    (hVU : closure V ⊆ U) (hWV : W ⊆ V) :
    ∃ Ccomm : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (u : EuclideanSpace ℂ (Fin n) → ℝ) (H : ℝ≥0),
      (∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U) →
      ContDiffOn ℝ (k + 2) u U →
      (∀ i j, HolderBoundOn (k + 1) α K U (fun z ↦ A z i j)) →
      HolderBoundOn (k + 2) α H V u →
      ∀ e : EuclideanSpace ℂ (Fin n),
        HolderBoundOn k α (Ccomm * H * ‖e‖₊) W
          (fun z ↦ RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) := by
  obtain ⟨Ccomm, hunit⟩ := CalabiYau.Schauder.exists_holderBoundOn_directional_commutator
    hα₀ hα₁ hU hV hVconvex hVU hWV
  refine ⟨Ccomm, ?_⟩
  intro A u H hA hu hAHolder huHolder e
  have hcont (v : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ k
        (fun z ↦ RCLike.re ((fderiv ℝ A z v * complexHessian u z).trace)) U :=
    directional_commutator_contDiffOn hU hA hu
  have hlinear (r : ℝ) (v : EuclideanSpace ℂ (Fin n)) :
      (fun z ↦ RCLike.re ((fderiv ℝ A z (r • v) * complexHessian u z).trace)) =
        fun z ↦ r • RCLike.re ((fderiv ℝ A z v * complexHessian u z).trace) := by
    funext z
    simp [map_smul]
  have hunit' (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖ ≤ 1) :
      HolderBoundOn k α (Ccomm * H) W
        (fun z ↦ RCLike.re ((fderiv ℝ A z v * complexHessian u z).trace)) :=
    hunit A u v H hA hu hAHolder huHolder hv
  exact holderBoundOn_all_directions_of_unit hU
    (Set.Subset.trans hWV (subset_closure.trans hVU))
    (fun v z ↦ RCLike.re ((fderiv ℝ A z v * complexHessian u z).trace))
    hcont hlinear hunit' e

private theorem higher_step_local_directional_quantitative
    {n k : ℕ} (hk : 1 ≤ k) (hOrder : InteriorSchauderOrder n k)
    {α lam KA : ℝ≥0}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam)
    {U W : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hW : IsCompact (closure W)) (hWU : closure W ⊆ U) :
    ∃ Corder : ℝ≥0,
      ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
        (u : EuclideanSpace ℂ (Fin n) → ℝ) (Cbase Cforce : ℝ≥0),
      (∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U) →
      (∀ i j, HolderBoundOn k α KA U (fun z ↦ A z i j)) →
      IsUniformlyEllipticOn A lam U →
      ContDiffOn ℝ (k + 2) u U →
      HolderBoundOn (k + 2) α Cbase U u →
      (∀ e : EuclideanSpace ℂ (Fin n),
        ContDiffOn ℝ k (complexEllipticOp A (fun z ↦ fderiv ℝ u z e)) U) →
      (∀ e : EuclideanSpace ℂ (Fin n),
        HolderBoundOn k α (Cforce * ‖e‖₊) U
          (complexEllipticOp A (fun z ↦ fderiv ℝ u z e))) →
      ContDiffOn ℝ (k + 3) u U ∧
        HolderBoundOn (k + 3) α (max Cbase (Corder * (Cforce + Cbase))) W u := by
  obtain ⟨Corder, hCorder⟩ := hOrder α hα₀ hα₁ lam KA hlam U W hU hW hWU
  refine ⟨Corder, ?_⟩
  intro A u Cbase Cforce hA hAHolder hEll hBaseDiff hBaseHolder hOpDiff hOpHolder
  have hACont (i j : Fin n) : ContDiffOn ℝ k (fun z ↦ A z i j) U :=
    (hA i j).of_le (WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc]))
  have hBaseTwo : ContDiffOn ℝ 2 u U :=
    hBaseDiff.of_le (WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc]))
  have hDerivativeSup (e : EuclideanSpace ℂ (Fin n)) (z : EuclideanSpace ℂ (Fin n))
      (hz : z ∈ U) : |fderiv ℝ u z e| ≤ (Cbase * ‖e‖₊ : ℝ) := by
    have hnorm : ‖fderiv ℝ u z‖ ≤ Cbase := by
      rw [← norm_iteratedFDeriv_one]
      exact hBaseHolder.1 1 (by omega) z hz
    have hEval := (fderiv ℝ u z).le_opNorm e
    have hReal : ‖fderiv ℝ u z e‖ ≤ (Cbase * ‖e‖₊ : ℝ) := by
      calc
        ‖fderiv ℝ u z e‖ ≤ ‖fderiv ℝ u z‖ * ‖e‖ := hEval
        _ ≤ (Cbase : ℝ) * ‖e‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ = (Cbase * ‖e‖₊ : ℝ) := by simp
    simpa [Real.norm_eq_abs] using hReal
  let Cdir : ℝ≥0 := Corder * (Cforce + Cbase)
  have hDirectional (e : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ (k + 2) (fun z ↦ fderiv ℝ u z e) U ∧
        HolderBoundOn (k + 2) α (Cdir * ‖e‖₊) W
          (fun z ↦ fderiv ℝ u z e) := by
    have hC2 : ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ u z e) U :=
      directional_derivative_contDiffOn_two hU hk hBaseDiff e
    have hK0 : ∀ z ∈ U, |fderiv ℝ u z e| ≤ (Cbase * ‖e‖₊ : ℝ) :=
      hDerivativeSup e
    have hApplied := hCorder A (fun z ↦ fderiv ℝ u z e) hACont hC2 hEll
      hAHolder (Cbase * ‖e‖₊) (Cforce * ‖e‖₊) (hOpDiff e) (hOpHolder e) hK0
    refine ⟨hApplied.1, ?_⟩
    convert hApplied.2 using 1
    dsimp [Cdir]
    ring
  have hDf : ContDiffOn ℝ (k + 2) (fderiv ℝ u) U := by
    rw [contDiffOn_clm_apply_private]
    intro e
    exact (hDirectional e).1
  have hReg' : ContDiffOn ℝ ((k + 2) + 1) u U := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨hBaseDiff.differentiableOn (by norm_num [Nat.cast_add, add_assoc]), ?_, hDf⟩
    intro htop
    have hfinite : (k + 2 : ℕ∞ω) ≠ ⊤ := WithTop.coe_ne_top
    exact (hfinite htop).elim
  have hsum1 : ((k : ℕ∞ω) + 2) + 1 = (k : ℕ∞ω) + 3 := by
    calc
      ((k : ℕ∞ω) + 2) + 1 = (k : ℕ∞ω) + (2 + 1) := by rw [add_assoc]
      _ = (k : ℕ∞ω) + 3 := by norm_num
  have hReg : ContDiffOn ℝ (k + 3) u U := by
    simpa only [hsum1] using hReg'
  have hWsubset : W ⊆ U := fun _ hx ↦ hWU (subset_closure hx)
  have hBaseOnW : HolderBoundOn (k + 2) α Cbase W u :=
    hBaseHolder.mono_set hWsubset
  let Cfinal : ℝ≥0 := max Cbase Cdir
  have hsum2 : ((k : ℕ∞ω) + 1) + 2 = (k : ℕ∞ω) + 3 := by
    calc
      ((k : ℕ∞ω) + 1) + 2 = (k : ℕ∞ω) + (1 + 2) := by rw [add_assoc]
      _ = (k : ℕ∞ω) + 3 := by norm_num
  have hRegLift : ContDiffOn ℝ ((k + 1) + 2) u U := by
    simpa only [hsum2] using hReg
  have hHolderW' : HolderBoundOn ((k + 1) + 2) α Cfinal W u := by
    simpa [Cdir, Cfinal] using
      (holderBoundOn_succ_of_all_directional (m := k + 1) hU hWsubset
        hRegLift (by simpa [Nat.add_assoc] using hBaseOnW)
        (fun e ↦ by simpa [Nat.add_assoc] using (hDirectional e).2))
  have hHolderW : HolderBoundOn (k + 3) α Cfinal W u := by
    simpa only [hsum2] using hHolderW'
  exact ⟨hReg, hHolderW⟩
private theorem higher_step_ball_quantitative
    {n k : ℕ} (hk : 1 ≤ k) (hOrder : InteriorSchauderOrder n k)
    {α lam K : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam)
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (p : EuclideanSpace ℂ (Fin n)) {R : ℝ} (hR : 0 < R)
    (hOuter : Metric.closedBall p (4 * R) ⊆ U) :
    ∃ Cball : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (u : EuclideanSpace ℂ (Fin n) → ℝ) (K₀ K₁ : ℝ≥0),
      (∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U) →
      (∀ i j, HolderBoundOn (k + 1) α K U (fun z ↦ A z i j)) →
      ContDiffOn ℝ 2 u U →
      ContDiffOn ℝ (k + 1) (complexEllipticOp A u) U →
      HolderBoundOn (k + 1) α K₁ U (complexEllipticOp A u) →
      IsUniformlyEllipticOn A lam U →
      (∀ z ∈ U, |u z| ≤ K₀) →
      ContDiffOn ℝ (k + 3) u (Metric.ball p R) ∧
        HolderBoundOn (k + 3) α (Cball * (K₁ + K₀)) (Metric.ball p (R / 2)) u := by
  let Ubase := Metric.ball p (2 * R)
  let Ustep := Metric.ball p R
  have hBaseDom : Ubase ⊆ U :=
    (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith : 2 * R ≤ 4 * R))).trans hOuter
  have hStepDom : Ustep ⊆ Ubase := Metric.ball_subset_ball (by linarith)
  have hStepOrig := hStepDom.trans hBaseDom
  have hBasePair := nested_ball_admissible p hR
  let Db : ℝ≥0 := ⟨4 * R, by positivity⟩
  let Ds : ℝ≥0 := ⟨2 * R, by positivity⟩
  have hDb : (Db : ℝ) = 2 * (2 * R) := by change 4 * R = _; ring
  have hDs : (Ds : ℝ) = 2 * R := rfl
  let Pb := Db ^ ((1 : ℝ) - (α : ℝ))
  let Ps := Ds ^ ((1 : ℝ) - (α : ℝ))
  obtain ⟨Cb, hCb⟩ := hOrder α hα₀ hα₁ lam (max K (K * Pb)) hlam
    Ubase Ustep Metric.isOpen_ball hBasePair.1 hBasePair.2
  obtain ⟨Cc, hCc⟩ := exists_directional_commutator_all_directions
    (k := k) (K := K) hα₀ hα₁ (U := Ubase) (V := Ustep) (W := Ustep)
    Metric.isOpen_ball Metric.isOpen_ball (convex_ball p R) hBasePair.2 Set.Subset.rfl
  have hHalf : 0 < R / 2 := by positivity
  have hInnerPair := nested_ball_admissible p hHalf
  have hInnerSubset : closure (Metric.ball p (R / 2)) ⊆ Ustep := by
    simpa [Ustep, show 2 * (R / 2) = R by ring] using hInnerPair.2
  obtain ⟨Cd, hCd⟩ := higher_step_local_directional_quantitative hk hOrder
    (KA := max K (K * Ps)) hα₀ hα₁ hlam Metric.isOpen_ball hInnerPair.1 hInnerSubset
  let B := Cb * (2 + Pb)
  let F := 1 + Cc * B
  let Cball := max B (Cd * (F + B))
  refine ⟨Cball, ?_⟩
  intro A u K₀ K₁ hA hAHolder hu hLu hLuHolder hEll huBound
  let S := K₁ + K₀
  have hK₁ : K₁ ≤ S := le_add_right le_rfl
  have hK₀ : K₀ ≤ S := le_add_left le_rfl
  have hAb (i j : Fin n) : HolderBoundOn k α (max K (K * Pb)) Ubase
      (fun z ↦ A z i j) := by
    exact holderBoundOn_lower_on_ball hDb ((hA i j).mono hBaseDom)
      ((hAHolder i j).mono_set hBaseDom) hα₁.le
  have hLulower : HolderBoundOn k α (max K₁ (K₁ * Pb)) Ubase (complexEllipticOp A u) :=
    holderBoundOn_lower_on_ball hDb (hLu.mono hBaseDom)
      (hLuHolder.mono_set hBaseDom) hα₁.le
  have hPrice : max K₁ (K₁ * Pb) ≤ (1 + Pb) * S := by
    apply max_le
    · calc
        K₁ ≤ S := hK₁
        _ ≤ (1 + Pb) * S := by
          rw [add_mul, one_mul]
          exact le_add_of_nonneg_right (by positivity)
    · calc
        K₁ * Pb ≤ S * Pb := mul_le_mul_of_nonneg_right hK₁ (by positivity)
        _ ≤ (1 + Pb) * S := by
          rw [show (1 + Pb) * S = S + S * Pb by ring]
          exact le_add_of_nonneg_left (by positivity)
  have hBase := hCb A u
    (fun i j ↦ ((hA i j).mono hBaseDom).of_le
      (WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc])))
    (hu.mono hBaseDom) (fun z hz ↦ hEll z (hBaseDom hz)) hAb
    S ((1 + Pb) * S)
    ((hLu.mono hBaseDom).of_le
      (WithTop.coe_le_coe.mpr (by norm_num [Nat.cast_add, add_assoc])))
    (hLulower.mono_const hPrice)
    (fun z hz ↦ (huBound z (hBaseDom hz)).trans (by exact_mod_cast hK₀))
  have hBaseHolder : HolderBoundOn (k + 2) α (B * S) Ustep u := by
    convert hBase.2 using 1
    dsimp [B]
    ring
  have hBaseDiff := hBase.1.mono hStepDom
  have hComm (e : EuclideanSpace ℂ (Fin n)) : HolderBoundOn k α
      ((Cc * (B * S)) * ‖e‖₊) Ustep
      (fun z ↦ RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace)) :=
    hCc A u (B * S) (fun i j ↦ (hA i j).mono hBaseDom) hBase.1
      (fun i j ↦ (hAHolder i j).mono_set hBaseDom) hBaseHolder e
  have hAs (i j : Fin n) : HolderBoundOn k α (max K (K * Ps)) Ustep
      (fun z ↦ A z i j) :=
    holderBoundOn_lower_on_ball hDs ((hA i j).mono hStepOrig)
      ((hAHolder i j).mono_set hStepOrig) hα₁.le
  have hAc (i j : Fin n) := (hA i j).mono hStepOrig
  have hEq : ∀ e z, z ∈ Ustep →
      complexEllipticOp A (fun w ↦ fderiv ℝ u w e) z =
        fderiv ℝ (complexEllipticOp A u) z e -
          RCLike.re ((fderiv ℝ A z e * complexHessian u z).trace) := by
    intro e z hz
    exact higherStep_differentiated_operator_identity_on hk Metric.isOpen_ball hAc
      hBaseDiff e z hz
  have hData := differentiated_operator_holder_data Metric.isOpen_ball
    hAc hBaseDiff (hLu.mono hStepOrig) (hLuHolder.mono_set hStepOrig) hEq hComm
  have hForcePrice : K₁ + Cc * (B * S) ≤ F * S := by
    dsimp [F]
    calc
      K₁ + Cc * (B * S) ≤ S + Cc * (B * S) := add_le_add hK₁ le_rfl
      _ = (1 + Cc * B) * S := by ring
  have hFinal := hCd A u (B * S) (F * S) hAc hAs
    (fun z hz ↦ hEll z (hStepOrig hz)) hBaseDiff hBaseHolder
    (fun e ↦ (hData e).1)
    (fun e ↦ ((hData e).2).mono_const (mul_le_mul_of_nonneg_right hForcePrice (by positivity)))
  refine ⟨hFinal.1, ?_⟩
  convert hFinal.2 using 1
  dsimp [Cball, S]
  rw [show Cd * (F * (K₁ + K₀) + B * (K₁ + K₀)) =
    (Cd * (F + B)) * (K₁ + K₀) by ring]
  exact (max_mul_mul_right B (Cd * (F + B)) (K₁ + K₀)).symm
private noncomputable def quantitativeHolderAssemblyFactor (δ α : ℝ≥0) : ℝ≥0 :=
  ⟨max 1 (2 / (δ : ℝ) ^ (α : ℝ)), by positivity⟩

private theorem holderOnWith_compact_assembly_linear
    {E F ι : Type*} [MetricSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {α B S δ : ℝ≥0} {f : E → F} {c : ι → Set E}
    (hδ : 0 < δ)
    (hcover : ∀ x ∈ K, ∃ i, Metric.ball x (δ : ℝ) ⊆ c i)
    (hlocal : ∀ i, HolderOnWith (B * S) α f (K ∩ c i))
    (hbound : ∀ x ∈ K, ‖f x‖ ≤ ((B * S : ℝ≥0) : ℝ)) :
    HolderOnWith (B * quantitativeHolderAssemblyFactor δ α * S) α f K := by
  let Cfactor : ℝ≥0 := quantitativeHolderAssemblyFactor δ α
  let Cglobal : ℝ≥0 := B * Cfactor * S
  have hconst : B * S ≤ Cglobal := by
    dsimp [Cglobal]
    calc
      B * S ≤ B * 1 * S := by simp
      _ ≤ B * Cfactor * S := by
        gcongr
        change 1 ≤ max 1 (2 / (δ : ℝ) ^ (α : ℝ))
        exact le_max_left _ _
  have hδpos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hpowpos : 0 < (δ : ℝ) ^ (α : ℝ) := Real.rpow_pos_of_pos hδpos _
  have hfactor : (2 : ℝ) ≤ max 1 (2 / (δ : ℝ) ^ (α : ℝ)) *
      (δ : ℝ) ^ (α : ℝ) := by
    exact (div_le_iff₀ hpowpos).mp
      (le_max_right (1 : ℝ) (2 / (δ : ℝ) ^ (α : ℝ)))
  intro x hx y hy
  by_cases hnear : dist x y < (δ : ℝ)
  · obtain ⟨i, hi⟩ := hcover x hx
    have hxi : x ∈ c i := hi (by simpa [Metric.mem_ball] using hδ)
    have hyi : y ∈ c i := hi (by simpa [Metric.mem_ball, dist_comm] using hnear)
    calc
      edist (f x) (f y) ≤ (B * S : ENNReal) * edist x y ^ (α : ℝ) :=
        hlocal i x ⟨hx, hxi⟩ y ⟨hy, hyi⟩
      _ ≤ (Cglobal : ENNReal) * edist x y ^ (α : ℝ) := by
        gcongr
        exact_mod_cast hconst
  · have hfar : (δ : ℝ) ≤ dist x y := le_of_not_gt hnear
    have hdist : dist (f x) (f y) ≤ 2 * ((B * S : ℝ≥0) : ℝ) := by
      rw [dist_eq_norm]
      calc
        ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
        _ ≤ (B * S : ℝ) + (B * S : ℝ) := add_le_add (hbound x hx) (hbound y hy)
        _ = 2 * (B * S : ℝ) := by ring
    have hpow : (δ : ℝ) ^ (α : ℝ) ≤ dist x y ^ (α : ℝ) :=
      Real.rpow_le_rpow hδ.le hfar α.coe_nonneg
    have hratio : 2 * ((B * S : ℝ≥0) : ℝ) ≤
        (Cglobal : ℝ) * dist x y ^ (α : ℝ) := by
      calc
        2 * ((B * S : ℝ≥0) : ℝ) = (B : ℝ) * 2 * (S : ℝ) := by push_cast; ring
        _ ≤ (B : ℝ) * (max 1 (2 / (δ : ℝ) ^ (α : ℝ)) *
              (δ : ℝ) ^ (α : ℝ)) * (S : ℝ) := by gcongr
        _ = (Cglobal : ℝ) * (δ : ℝ) ^ (α : ℝ) := by
          dsimp [Cglobal]
          have hfac : (Cfactor : ℝ) =
              max 1 (2 / (δ : ℝ) ^ (α : ℝ)) := by
            change max 1 (2 / (δ : ℝ) ^ (α : ℝ)) = _
            rfl
          rw [hfac]
          ring
        _ ≤ (Cglobal : ℝ) * dist x y ^ (α : ℝ) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
    rw [edist_dist]
    calc
      ENNReal.ofReal (dist (f x) (f y)) ≤
          ENNReal.ofReal ((Cglobal : ℝ) * dist x y ^ (α : ℝ)) :=
        ENNReal.ofReal_le_ofReal (hdist.trans hratio)
      _ = (Cglobal : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Cglobal : ℝ))]
        rw [ENNReal.ofReal_coe_nnreal]
        rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg]
        rw [edist_dist]
private theorem holderBoundOn_compact_local_assembly_quantitative
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {k : ℕ} {α B : ℝ≥0}
    (hK : IsCompact K) (c : ι → Set E)
    (hcopen : ∀ i, IsOpen (c i)) (hcover : K ⊆ ⋃ i, c i) :
    ∃ G : ℝ≥0, ∀ (f : E → F) (S : ℝ≥0),
      (∀ i, HolderBoundOn k α (B * S) (K ∩ c i) f) →
      HolderBoundOn k α (G * S) K f := by
  obtain ⟨δ, hδ, hLeb⟩ := lebesgue_number_lemma_of_metric hK hcopen hcover
  let δ' : ℝ≥0 := ⟨δ, hδ.le⟩
  let factor := quantitativeHolderAssemblyFactor δ' α
  have hFactor : 1 ≤ factor := by
    change (1 : ℝ≥0) ≤ ⟨max 1 (2 / (δ' : ℝ) ^ (α : ℝ)), _⟩
    exact_mod_cast (le_max_left (1 : ℝ) (2 / (δ' : ℝ) ^ (α : ℝ)))
  have hPrice : B ≤ B * factor := by
    calc
      B = B * 1 := by simp
      _ ≤ B * factor := mul_le_mul_of_nonneg_left hFactor (by positivity)
  refine ⟨B * factor, ?_⟩
  intro f S hlocal
  have hbound : ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ (B * S : ℝ≥0) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    exact (hlocal i).1 k le_rfl x ⟨hx, hi⟩
  have hTop := holderOnWith_compact_assembly_linear (B := B) (S := S) (δ := δ')
    (by exact_mod_cast hδ) hLeb (fun i ↦ (hlocal i).2) hbound
  refine ⟨?_, hTop⟩
  intro j hj x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
  exact ((hlocal i).1 j hj x ⟨hx, hi⟩).trans
    (by exact_mod_cast (mul_le_mul_of_nonneg_right hPrice (show 0 ≤ S from bot_le)))
private theorem interiorSchauderOrder_succ_complete {n k : ℕ} (hk : 1 ≤ k) :
    InteriorSchauderOrder n k → InteriorSchauderOrder n (k + 1) := by
  classical
  intro hOrder α hα₀ hα₁ lam K hlam U V hU hV hVU
  obtain ⟨W, hWopen, hVW, hWcompact, hWU, s, r, hr, hcover⟩ :=
    compact_convex_ball_cover hV hU hVU
  let P := {p : closure V // p ∈ s}
  let : Fintype P := Fintype.ofFinite P
  have hBalls (p : P) : ∃ Cball : ℝ≥0,
      ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
        (u : EuclideanSpace ℂ (Fin n) → ℝ) (K₀ K₁ : ℝ≥0),
      (∀ i j, ContDiffOn ℝ (k + 1) (fun z ↦ A z i j) U) →
      (∀ i j, HolderBoundOn (k + 1) α K U (fun z ↦ A z i j)) →
      ContDiffOn ℝ 2 u U →
      ContDiffOn ℝ (k + 1) (complexEllipticOp A u) U →
      HolderBoundOn (k + 1) α K₁ U (complexEllipticOp A u) →
      IsUniformlyEllipticOn A lam U → (∀ z ∈ U, |u z| ≤ K₀) →
      ContDiffOn ℝ (k + 3) u (Metric.ball (p.val : EuclideanSpace ℂ (Fin n)) (r p.val)) ∧
        HolderBoundOn (k + 3) α (Cball * (K₁ + K₀))
          (Metric.ball (p.val : EuclideanSpace ℂ (Fin n)) (r p.val / 2)) u := by
    have hOuter := ((hr p.val p.property).2).trans
      (subset_closure.trans hWU)
    exact higher_step_ball_quantitative hk hOrder hα₀ hα₁ hlam
      (p.val : EuclideanSpace ℂ (Fin n)) (hr p.val p.property).1 hOuter
  choose Cb hb using hBalls
  let B := Finset.univ.sup Cb
  let c (p : P) := Metric.ball (p.val : EuclideanSpace ℂ (Fin n)) (r p.val / 2)
  have hcopen (p : P) : IsOpen (c p) := Metric.isOpen_ball
  have hccover : closure V ⊆ ⋃ p : P, c p := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  obtain ⟨G, hG⟩ := holderBoundOn_compact_local_assembly_quantitative
    (F := ℝ) (k := k + 3) (α := α) (B := B) hV c hcopen hccover
  refine ⟨G, ?_⟩
  intro A u hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound
  obtain ⟨rU, hrU, hcoverU⟩ := open_set_has_nested_ball_cover hU
  let cU (p : U) := Metric.ball (p : EuclideanSpace ℂ (Fin n)) (rU p)
  have hRegLocal (p : U) : ContDiffOn ℝ (k + 3) u (cU p) := by
    obtain ⟨C, hC⟩ := higher_step_ball_quantitative hk hOrder hα₀ hα₁ hlam
      (p : EuclideanSpace ℂ (Fin n)) (hrU p).1 (hrU p).2
    exact (hC A u K₀ K₁ hA hAHolder hu hLu hLuHolder hEll huBound).1
  have hSubset (p : U) : cU p ⊆ U := by
    have hRadius : rU p ≤ 4 * rU p := by nlinarith [(hrU p).1]
    exact (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hRadius)).trans (hrU p).2
  have hReg := contDiffOn_of_open_cover cU (fun _ ↦ Metric.isOpen_ball)
    hcoverU hSubset hRegLocal
  have hLocal (p : P) : HolderBoundOn (k + 3) α (B * (K₁ + K₀))
      (closure V ∩ c p) u := by
    have hBall := (hb p A u K₀ K₁ hA hAHolder hu hLu hLuHolder hEll huBound).2
    exact (hBall.mono_set Set.inter_subset_right).mono_const
      (mul_le_mul_of_nonneg_right (Finset.le_sup (Finset.mem_univ p)) (by positivity))
  have hHolder := (hG u (K₁ + K₀) hLocal).mono_set (subset_closure : V ⊆ closure V)
  constructor
  · have hsum : (1 : ℕ∞ω) + 2 = 3 := by norm_num
    simpa [Nat.cast_add, add_assoc, hsum] using hReg
  · simpa [Nat.add_assoc] using hHolder

end CalabiYau.Schauder

/-- One genuine higher-order induction step for the fixed-order Schauder slices. -/
theorem interiorSchauderOrder_succ {n k : ℕ} (hk : 1 ≤ k) :
    InteriorSchauderOrder n k → InteriorSchauderOrder n (k + 1) := by
  exact CalabiYau.Schauder.interiorSchauderOrder_succ_complete hk

end
