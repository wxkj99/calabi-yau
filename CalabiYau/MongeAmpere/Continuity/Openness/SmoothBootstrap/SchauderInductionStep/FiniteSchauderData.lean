module

public import CalabiYau.Analysis.Elliptic.Schauder
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite local inputs for the lower Schauder pass

A genuine `C^{m+1}` coefficient/forcing jet supplies an order-`m` Hölder bound on a
small relatively compact domain. Positive definite coefficients give a positive local
ellipticity constant. Both nested domains are open: the inner Hölder gain will be
used to differentiate on a neighbourhood, not just on a compact set.
-/

@[expose] public section

open scoped ContDiff NNReal Topology ComplexOrder

open Set Matrix

private theorem compact_positive_quadratic
    {n : ℕ} {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {K : Set (EuclideanSpace ℂ (Fin n))} (hK : IsCompact K) (hKne : K.Nonempty)
    (hn : 0 < n)
    (hAcont : ∀ i j, ContinuousOn (fun z ↦ A z i j) K)
    (hApos : ∀ z ∈ K, (A z).PosDef) :
    ∃ lam : ℝ≥0, 0 < lam ∧
      ∀ z ∈ K, (A z).IsHermitian ∧
        ∀ v : Fin n → ℂ,
          (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤
            RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
  let S : Set (Fin n → ℂ) := Metric.sphere 0 1
  let q : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) → ℝ :=
    fun p ↦ RCLike.re (star p.2 ⬝ᵥ (A p.1 *ᵥ p.2))
  have hScompact : IsCompact S := by
    simpa [S] using (isCompact_sphere (0 : Fin n → ℂ) (1 : ℝ))
  have hSnonempty : S.Nonempty := by
    obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp hn
    refine ⟨Pi.single i 1, ?_⟩
    simp [S, Pi.norm_single]
  have hprod : IsCompact (K ×ˢ S) := hK.prod hScompact
  have hentry (i j : Fin n) : ContinuousOn (fun p : _ × _ ↦ A p.1 i j) (K ×ˢ S) := by
    exact (hAcont i j).comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hqcont : ContinuousOn q (K ×ˢ S) := by
    have hcoord (i : Fin n) :
        ContinuousOn (fun p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) ↦ p.2 i)
          (K ×ˢ S) := by
      fun_prop
    have hinner (i : Fin n) :
        ContinuousOn (fun p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) ↦
          ∑ j, A p.1 i j * p.2 j) (K ×ˢ S) := by
      apply continuousOn_finsetSum
      intro j hj
      exact (hentry i j).mul (hcoord j)
    have houter :
        ContinuousOn (fun p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) ↦
          ∑ i, star (p.2 i) * ∑ j, A p.1 i j * p.2 j) (K ×ˢ S) := by
      apply continuousOn_finsetSum
      intro i hi
      have hstar : ContinuousOn
          (fun p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) ↦ star (p.2 i)) (K ×ˢ S) := by
        fun_prop
      exact hstar.mul (hinner i)
    change ContinuousOn (fun p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) ↦ RCLike.re
      (∑ i, star (p.2 i) * ∑ j, A p.1 i j * p.2 j)) (K ×ˢ S)
    have hre : Continuous (fun x : ℂ ↦ x.re) := by fun_prop
    have hre' : ContinuousOn (fun x : ℂ ↦ x.re) Set.univ := hre.continuousOn
    exact hre'.comp houter (Set.mapsTo_univ _ _)
  have hprodne : (K ×ˢ S).Nonempty := hKne.prod hSnonempty
  obtain ⟨p, hp, hpmin⟩ := hprod.exists_isMinOn hprodne hqcont
  let c : ℝ := q p
  have hcpos : 0 < c := by
    dsimp [c, q]
    have hv : p.2 ≠ 0 := Metric.ne_of_mem_sphere hp.2 (by norm_num)
    have h := (hApos p.1 hp.1).dotProduct_mulVec_pos hv
    exact (RCLike.pos_iff.mp h).1
  have hcle : ∀ p' ∈ K ×ˢ S, c ≤ q p' := by
    intro p' hp'
    exact hpmin hp'
  refine ⟨Real.toNNReal (c / (n : ℝ)), Real.toNNReal_pos.mpr (by positivity), ?_⟩
  intro z hz
  refine ⟨(hApos z hz).isHermitian, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    simp
  · have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let w : Fin n → ℂ := ‖v‖⁻¹ • v
    have hwsphere : w ∈ S := by
      change dist w (0 : Fin n → ℂ) = 1
      rw [dist_zero_right]
      simp only [w, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv))]
      exact inv_mul_cancel₀ hvnorm
    have hmin := hcle (z, w) ⟨hz, hwsphere⟩
    have hscale : q (z, w) = ‖v‖⁻¹ ^ 2 * q (z, v) := by
      simp [q, w, Matrix.mulVec_smul, dotProduct_smul]
      ring
    have hquad : c * ‖v‖ ^ 2 ≤ q (z, v) := by
      rw [hscale] at hmin
      have hnz : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
      have hinv : (‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2 = 1 := by
        field_simp
      calc
        c * ‖v‖ ^ 2 ≤ (‖v‖⁻¹) ^ 2 * q (z, v) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmin (le_of_lt hnz)
        _ = ((‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2) * q (z, v) := by ring
        _ = q (z, v) := by rw [hinv, one_mul]
    have hsum : ∑ i, ‖v i‖ ^ 2 ≤ (n : ℝ) * ‖v‖ ^ 2 := by
      calc
        ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hvi := norm_le_pi_norm v i
          nlinarith [norm_nonneg (v i), norm_nonneg v]
        _ = (n : ℝ) * ‖v‖ ^ 2 := by simp
    have hfinal : (c / (n : ℝ)) * ∑ i, ‖v i‖ ^ 2 ≤ q (z, v) := by
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      calc
        (c / (n : ℝ)) * ∑ i, ‖v i‖ ^ 2 ≤ (c / (n : ℝ)) * ((n : ℝ) * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = c * ‖v‖ ^ 2 := by field_simp
        _ ≤ q (z, v) := hquad
    change max (c / (n : ℝ)) 0 * ∑ i, ‖v i‖ ^ 2 ≤ q (z, v)
    rw [max_eq_left (le_of_lt (div_pos hcpos (by exact_mod_cast hn)))]
    exact hfinal

private theorem compact_derivative_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W : Set E} (hW : IsOpen W) {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ m f W) {K : Set E} (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ C : ℝ≥0, ∀ j ≤ m, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have htop (j : ℕ) (hj : j ≤ m) : (j : ℕ∞ω) ≤ (m : ℕ∞ω) := by
    exact_mod_cast hj
  have hcont (j : ℕ) (hj : j ≤ m) :
      ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ j f x‖) K := by
    have hwithin := hf.continuousOn_iteratedFDerivWithin (htop j hj) hW.uniqueDiffOn
    have heq : EqOn (iteratedFDerivWithin ℝ j f W) (iteratedFDeriv ℝ j f) W := by
      intro x hx
      exact iteratedFDerivWithin_eq_iteratedFDeriv hW.uniqueDiffOn
        ((hf.contDiffAt (hW.mem_nhds hx)).of_le (htop j hj)) hx
    exact (hwithin.congr heq.symm).mono hKW |>.norm
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

/-- Local finite inputs, without an equation or any assumed regularity gain. -/
theorem locally_finite_schauder_data
    {n m : ℕ} {α : ℝ≥0} {W : Set (EuclideanSpace ℂ (Fin n))}
    (hW : IsOpen W) (hα₀ : 0 < α) (hα₁ : α < 1)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (Q u : EuclideanSpace ℂ (Fin n) → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ (m + 1 : ℕ) (fun w ↦ A w i j) W)
    (hpos : ∀ w ∈ W, (A w).PosDef)
    (hQ : ContDiffOn ℝ (m + 1 : ℕ) Q W)
    (hu : ContDiffOn ℝ 2 u W)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ W) :
    ∃ U V : Set (EuclideanSpace ℂ (Fin n)), ∃ lam K K₀ K₁ : ℝ≥0,
      IsOpen U ∧ IsOpen V ∧ IsCompact (closure U) ∧ IsCompact (closure V) ∧
      closure V ⊆ U ∧ closure U ⊆ W ∧ z ∈ V ∧ 0 < lam ∧
      IsUniformlyEllipticOn A lam U ∧
      (∀ i j, HolderBoundOn m α K U (fun w ↦ A w i j)) ∧
      HolderBoundOn m α K₁ U Q ∧ (∀ w ∈ U, |u w| ≤ K₀) := by
  classical
  have _hαpos : 0 < α := hα₀
  obtain ⟨eps, heps, hballW⟩ := Metric.isOpen_iff.mp hW z hz
  let r : ℝ := min (eps / 2) (1 / 2)
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrle : r ≤ 1 / 2 := by dsimp [r]; exact min_le_right _ _
  have hreps : r < eps := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let U : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball z r
  let V : Set (EuclideanSpace ℂ (Fin n)) := Metric.ball z (r / 2)
  have hclosedW : Metric.closedBall z r ⊆ W := by
    intro x hx
    apply hballW
    have hx' : dist x z ≤ r := by simpa [Metric.mem_closedBall] using hx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt hx' hreps)
  have hclU : closure U ⊆ Metric.closedBall z r := by
    exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
  have hclVball : closure V ⊆ Metric.closedBall z (r / 2) := by
    exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
  have hVsub : closure V ⊆ U := by
    intro x hx
    have hx' := hclVball hx
    have hdist : dist x z ≤ r / 2 := by simpa [Metric.mem_closedBall] using hx'
    apply Metric.mem_ball.mpr
    linarith
  have hUcompact : IsCompact (closure U) :=
    (isCompact_closedBall z r).of_isClosed_subset isClosed_closure hclU
  have hVcompact : IsCompact (closure V) :=
    (isCompact_closedBall z (r / 2)).of_isClosed_subset isClosed_closure hclVball
  have hclU_W : closure U ⊆ W := hclU.trans hclosedW
  have hzV : z ∈ V := by
    apply Metric.mem_ball.mpr
    simp [hrpos]
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hVopen : IsOpen V := Metric.isOpen_ball
  have hKcompact : IsCompact (Metric.closedBall z r) := isCompact_closedBall _ _
  have hAcont (i j : Fin n) :
      ContinuousOn (fun w ↦ A w i j) (Metric.closedBall z r) :=
    (hA i j).continuousOn.mono hclosedW
  have hα : α ≤ 1 := by exact_mod_cast (le_of_lt hα₁)
  have hQball : ∃ C : ℝ≥0, HolderBoundOn m α C U Q := by
    let K : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall z r
    have hKsubset : K ⊆ W := by simpa [K] using hclosedW
    obtain ⟨C, hC⟩ := compact_derivative_bound hW hQ hKcompact hKsubset
    have hcont : ContDiffOn ℝ (m + 1 : ℕ) Q U :=
      hQ.mono (Metric.ball_subset_closedBall.trans hclosedW)
    have hbound (j : ℕ) (hj : j ≤ m + 1) (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ U) :
        ‖iteratedFDeriv ℝ j Q x‖ ≤ C := hC j hj x (Metric.ball_subset_closedBall hx)
    have hdiam (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ U)
        (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ U) : dist x y ≤ 1 := by
      have hx' : dist x z < r := by simpa [U, Metric.mem_ball] using hx
      have hy' : dist y z < r := by simpa [U, Metric.mem_ball] using hy
      have htri := dist_triangle x z y
      rw [dist_comm z y] at htri
      linarith
    refine ⟨C, ?_⟩
    exact holderBoundOn_of_contDiffOn_succ_derivative_bound
      Metric.isOpen_ball (convex_ball _ _) hdiam hα hcont hbound
  obtain ⟨K₁, hQholder⟩ := hQball
  have hucont : ContinuousOn (fun w ↦ |u w|) (Metric.closedBall z r) := by
    have := (hu.continuousOn.mono hclosedW)
    fun_prop
  obtain ⟨Bu, hBu0, hBu⟩ :=
    (hKcompact.bddAbove_image hucont).exists_ge (0 : ℝ)
  let K₀ : ℝ≥0 := ⟨Bu, hBu0⟩
  have hUbound (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ U) :
      |u w| ≤ (K₀ : ℝ) := by
    apply hBu
    exact ⟨w, Metric.ball_subset_closedBall hw, rfl⟩
  have hcenter : z ∈ Metric.closedBall z r := by
    apply Metric.mem_closedBall.mpr
    simpa using le_of_lt hrpos
  have hquadData : ∀ hn : 0 < n, ∃ l : ℝ≥0, 0 < l ∧
      ∀ w ∈ Metric.closedBall z r, (A w).IsHermitian ∧
        ∀ v : Fin n → ℂ, (l : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤
          RCLike.re (star v ⬝ᵥ (A w *ᵥ v)) := by
    intro hn
    exact compact_positive_quadratic hKcompact ⟨z, hcenter⟩ hn hAcont
      (fun w hw ↦ hpos w (hclosedW hw))
  let lam : ℝ≥0 := if hn : 0 < n then Classical.choose (hquadData hn) else 1
  have hlampos : 0 < lam := by
    by_cases hn : 0 < n
    · simp only [lam, dite_eq_left hn]
      exact (Classical.choose_spec (hquadData hn)).1
    · have hn0 : n = 0 := by omega
      simp [lam, hn0]
  have hell : IsUniformlyEllipticOn A lam U := by
    intro w hw
    have hwK : w ∈ Metric.closedBall z r := Metric.ball_subset_closedBall hw
    have hwp : (A w).PosDef := hpos w (hclosedW hwK)
    refine ⟨hwp.isHermitian, ?_⟩
    intro v
    by_cases hn : 0 < n
    · simpa [lam, hn] using ((Classical.choose_spec (hquadData hn)).2 w hwK).2 v
    · have hn0 : n = 0 := by omega
      subst n
      simp [lam]
  have hAdata (i j : Fin n) : ∃ C : ℝ≥0,
      HolderBoundOn m α C U (fun w ↦ A w i j) := by
    let K : Set (EuclideanSpace ℂ (Fin n)) := Metric.closedBall z r
    obtain ⟨C, hC⟩ := compact_derivative_bound hW (hA i j) hKcompact (by
      simpa [K] using hclosedW)
    have hcont : ContDiffOn ℝ (m + 1 : ℕ) (fun w ↦ A w i j) U :=
      (hA i j).mono (Metric.ball_subset_closedBall.trans hclosedW)
    have hbound (j' : ℕ) (hj' : j' ≤ m + 1)
        (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ U) :
        ‖iteratedFDeriv ℝ j' (fun w ↦ A w i j) x‖ ≤ C :=
      hC j' hj' x (Metric.ball_subset_closedBall hx)
    have hdiam (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ U)
        (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ U) : dist x y ≤ 1 := by
      have hx' : dist x z < r := by simpa [U, Metric.mem_ball] using hx
      have hy' : dist y z < r := by simpa [U, Metric.mem_ball] using hy
      have htri := dist_triangle x z y
      rw [dist_comm z y] at htri
      linarith
    refine ⟨C, ?_⟩
    exact holderBoundOn_of_contDiffOn_succ_derivative_bound
      Metric.isOpen_ball (convex_ball _ _) hdiam hα hcont hbound
  let cA (i j : Fin n) : ℝ≥0 := Classical.choose (hAdata i j)
  have holderA (i j : Fin n) :
      HolderBoundOn m α (cA i j) U (fun w ↦ A w i j) := Classical.choose_spec (hAdata i j)
  let KA : ℝ≥0 := ∑ i : Fin n, ∑ j : Fin n, cA i j
  have hAholder : ∀ i j, HolderBoundOn m α KA U (fun w ↦ A w i j) := by
    intro i j
    have hle₁ : cA i j ≤ ∑ j' : Fin n, cA i j' := by
      exact Finset.single_le_sum (s := Finset.univ) (f := fun j' ↦ cA i j')
        (fun j' hj' ↦ (cA i j').2) (Finset.mem_univ j)
    have hle₂ : (∑ j' : Fin n, cA i j') ≤ KA := by
      dsimp [KA]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun i' ↦ ∑ j' : Fin n, cA i' j')
        (fun i' hi' ↦ Finset.sum_nonneg fun j' hj' ↦ (cA i' j').2)
        (Finset.mem_univ i)
    exact (holderA i j).mono_const (hle₁.trans hle₂)
  refine ⟨U, V, lam, KA, K₀, K₁, ?_⟩
  exact ⟨hUopen, hVopen, hUcompact, hVcompact, hVsub, hclU_W, hzV,
    hlampos, hell, hAholder, hQholder, hUbound⟩
