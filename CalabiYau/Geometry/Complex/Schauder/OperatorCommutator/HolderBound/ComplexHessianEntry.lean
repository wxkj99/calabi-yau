module

public import CalabiYau.Geometry.Complex.Schauder
public import CalabiYau.Geometry.Complex.Schauder.DerivativeHolder

/-!
# Hölder bounds for complex-Hessian entries

This estimate controls the complex Hessian as a bounded linear coordinate contraction of the
second jet, including every derivative up to the requested order.
-/

@[expose] public section

open Set Matrix Filter
open scoped NNReal Topology

namespace CalabiYau.Schauder

private noncomputable def complexHessianEntryEval {n : ℕ}
    (v w : EuclideanSpace ℂ (Fin n)) :
    (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp
    (ContinuousLinearMap.apply ℝ
      (EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) v)

private noncomputable def complexHessianEntryQ {n : ℕ} (i j : Fin n) :
    (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℂ := by
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let w : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iv := Complex.I • v
  let iw := Complex.I • w
  let e₁ := complexHessianEntryEval v w
  let e₂ := complexHessianEntryEval iv iw
  let e₃ := complexHessianEntryEval v iw
  let e₄ := complexHessianEntryEval iv w
  let realPart
      (e : (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ) :
      (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp e
  exact (1 / 4 : ℝ) •
    (realPart e₁ + realPart e₂ +
      (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp (realPart (e₃ - e₄)))

private theorem complexHessian_eq_Q {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 2 u z) (i j : Fin n) :
    complexHessian u z i j =
      complexHessianEntryQ i j (fderiv ℝ (fderiv ℝ u) z) := by
  rw [complexHessian_apply hu]
  simp [complexHessianEntryQ, complexHessianEntryEval, Complex.ofRealCLM_apply]
  ring

private theorem complexHessianEntryQ_norm_le {n : ℕ} (i j : Fin n) :
    ‖complexHessianEntryQ i j‖ ≤ 1 := by
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let w : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iv := Complex.I • v
  let iw := Complex.I • w
  have hv : ‖v‖ = 1 := by simp [v]
  have hw : ‖w‖ = 1 := by simp [w]
  have hiv : ‖iv‖ = 1 := by simp [iv, hv, norm_smul, Complex.norm_I]
  have hiw : ‖iw‖ = 1 := by simp [iw, hw, norm_smul, Complex.norm_I]
  have hEval (a b : EuclideanSpace ℂ (Fin n)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
      (T : EuclideanSpace ℂ (Fin n) →L[ℝ]
        EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ) : ‖T a b‖ ≤ ‖T‖ := by
    calc
      ‖T a b‖ ≤ ‖T a‖ * ‖b‖ := (T a).le_opNorm b
      _ ≤ ‖T‖ * ‖a‖ * ‖b‖ := by gcongr; exact T.le_opNorm a
      _ = ‖T‖ := by rw [ha, hb]; ring
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  dsimp [complexHessianEntryQ]
  have h1 : ‖Complex.ofReal (T v w)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval v w hv hw T
  have h2 : ‖Complex.ofReal (T iv iw)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval iv iw hiv hiw T
  have h3 : ‖Complex.ofReal (T v iw)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval v iw hv hiw T
  have h4 : ‖Complex.ofReal (T iv w)‖ ≤ ‖T‖ := by
    simpa only [Complex.norm_real] using hEval iv w hiv hw T
  have hrest : ‖Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ ≤
      ‖T‖ + ‖T‖ := by
    rw [norm_mul, Complex.norm_I]
    simpa only [one_mul] using (norm_sub_le _ _).trans (add_le_add h3 h4)
  have hnum : ‖Complex.ofReal (T v w) + Complex.ofReal (T iv iw) +
      Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ ≤ 4 * ‖T‖ := by
    calc
      _ ≤ ‖Complex.ofReal (T v w)‖ + ‖Complex.ofReal (T iv iw)‖ +
          ‖Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ := by
        calc
          _ ≤ ‖Complex.ofReal (T v w) + Complex.ofReal (T iv iw)‖ +
              ‖Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ := norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ 4 * ‖T‖ := by nlinarith
  rw [one_mul]
  rw [_root_.smul_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hscaled : (1 / 4) *
      ‖Complex.ofReal (T v w) + Complex.ofReal (T iv iw) +
        Complex.I * (Complex.ofReal (T v iw) - Complex.ofReal (T iv w))‖ ≤ ‖T‖ := by
    calc
      (1 / 4) * _ ≤ (1 / 4) * (4 * ‖T‖) := mul_le_mul_of_nonneg_left hnum (by norm_num)
      _ = ‖T‖ := by ring
  simpa [complexHessianEntryEval, v, w, iv, iw, mul_sub] using hscaled

private theorem complexHessianEntry_iteratedFDeriv_bound
    {n k : ℕ} {α H : ℝ≥0}
    {U V : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hVU : V ⊆ U)
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (huCont : ContDiffOn ℝ (k + 2) u U)
    (hu : HolderBoundOn (k + 2) α H V u)
    (i j : Fin n) :
    ∀ r ≤ k, ∀ z ∈ V,
      ‖iteratedFDeriv ℝ r (fun z ↦ complexHessian u z i j) z‖ ≤ 4 * H := by
  intro r hr z hz
  let g : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ :=
    fun y ↦ fderiv ℝ (fderiv ℝ u) y
  have hDu : ContDiffOn ℝ (k + 1) (fderiv ℝ u) U := by
    exact huCont.fderiv_of_isOpen hU (by rfl)
  have hg : ContDiffOn ℝ k g U := by
    exact hDu.fderiv_of_isOpen hU (by rfl)
  have hSmoothAt (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ U) :
      ContDiffAt ℝ 2 u y :=
    ((huCont y hy).contDiffAt (hU.mem_nhds hy)).of_le (by
      calc
        (2 : WithTop ℕ∞) ≤ 2 + (k : WithTop ℕ∞) := le_add_of_nonneg_right (by positivity)
        _ = (k : WithTop ℕ∞) + 2 := by rw [add_comm])
  have hEq : (fun y ↦ complexHessian u y i j) =ᶠ[𝓝 z] (complexHessianEntryQ i j ∘ g) := by
    filter_upwards [hU.mem_nhds (hVU hz)] with y hy
    exact complexHessian_eq_Q (hSmoothAt y hy) i j
  have hJet : iteratedFDeriv ℝ r (fun y ↦ complexHessian u y i j) z =
      (complexHessianEntryQ i j).compContinuousMultilinearMap
        (iteratedFDeriv ℝ r g z) := by
    calc
      iteratedFDeriv ℝ r (fun y ↦ complexHessian u y i j) z =
          iteratedFDeriv ℝ r (complexHessianEntryQ i j ∘ g) z :=
        (hEq.iteratedFDeriv ℝ r).eq_of_nhds
      _ = (complexHessianEntryQ i j).compContinuousMultilinearMap
          (iteratedFDeriv ℝ r g z) :=
        (complexHessianEntryQ i j).iteratedFDeriv_comp_left
          ((hg z (hVU hz)).contDiffAt (hU.mem_nhds (hVU hz))) (by exact_mod_cast hr)
  have hjetNorm : ‖iteratedFDeriv ℝ r g z‖ = ‖iteratedFDeriv ℝ (r + 2) u z‖ := by
    dsimp [g]
    rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]
  rw [hJet]
  calc
    ‖(complexHessianEntryQ i j).compContinuousMultilinearMap
        (iteratedFDeriv ℝ r g z)‖ ≤
      ‖complexHessianEntryQ i j‖ * ‖iteratedFDeriv ℝ r g z‖ :=
        (complexHessianEntryQ i j).norm_compContinuousMultilinearMap_le _
    _ ≤ 1 * ‖iteratedFDeriv ℝ (r + 2) u z‖ := by
      calc
        ‖complexHessianEntryQ i j‖ * ‖iteratedFDeriv ℝ r g z‖ ≤
            1 * ‖iteratedFDeriv ℝ r g z‖ :=
          mul_le_mul_of_nonneg_right (complexHessianEntryQ_norm_le i j) (norm_nonneg _)
        _ = 1 * ‖iteratedFDeriv ℝ (r + 2) u z‖ := by rw [hjetNorm]
    _ ≤ 4 * H := by
      have h := hu.1 (r + 2) (by omega) z hz
      have hH : (H : ℝ) ≤ (4 : ℝ) * (H : ℝ) := by
        nlinarith [NNReal.coe_nonneg H]
      simpa only [one_mul, NNReal.coe_mul] using h.trans (by simpa only [NNReal.coe_mul] using hH)

private theorem complexHessianEntry_topDerivative_holder
    {n k : ℕ} {α H : ℝ≥0}
    {U V : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hVU : V ⊆ U)
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (huCont : ContDiffOn ℝ (k + 2) u U)
    (hu : HolderBoundOn (k + 2) α H V u)
    (i j : Fin n) :
    HolderOnWith (4 * H) α
      (iteratedFDeriv ℝ k (fun z ↦ complexHessian u z i j)) V := by
  let E := EuclideanSpace ℂ (Fin n)
  let g : E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦ fderiv ℝ (fderiv ℝ u) z
  let Q := complexHessianEntryQ i j
  let C₁ := continuousMultilinearCurryRightEquiv' ℝ (k + 1) E ℝ
  let C₂ := continuousMultilinearCurryRightEquiv' ℝ k E (E →L[ℝ] ℝ)
  have hDu : ContDiffOn ℝ (k + 1) (fderiv ℝ u) U := by
    exact huCont.fderiv_of_isOpen hU (by rfl)
  have hg : ContDiffOn ℝ k g U := by
    exact hDu.fderiv_of_isOpen hU (by rfl)
  have hSmoothAt (z : E) (hz : z ∈ U) : ContDiffAt ℝ 2 u z :=
    ((huCont z hz).contDiffAt (hU.mem_nhds hz)).of_le (by
      calc
        (2 : WithTop ℕ∞) ≤ 2 + (k : WithTop ℕ∞) := le_add_of_nonneg_right (by positivity)
        _ = (k : WithTop ℕ∞) + 2 := by rw [add_comm])
  have hJetAt (z : E) (hz : z ∈ V) :
      iteratedFDeriv ℝ k (fun y ↦ complexHessian u y i j) z =
        Q.compContinuousMultilinearMap (iteratedFDeriv ℝ k g z) := by
    have hEq : (fun y ↦ complexHessian u y i j) =ᶠ[𝓝 z] (Q ∘ g) := by
      filter_upwards [hU.mem_nhds (hVU hz)] with y hy
      exact complexHessian_eq_Q (hSmoothAt y hy) i j
    calc
      iteratedFDeriv ℝ k (fun y ↦ complexHessian u y i j) z =
          iteratedFDeriv ℝ k (Q ∘ g) z := (hEq.iteratedFDeriv ℝ k).eq_of_nhds
      _ = Q.compContinuousMultilinearMap (iteratedFDeriv ℝ k g z) :=
        Q.iteratedFDeriv_comp_left
          ((hg z (hVU hz)).contDiffAt (hU.mem_nhds (hVU hz))) (by exact_mod_cast Nat.le_refl k)
  have hC₂ (z : E) : iteratedFDeriv ℝ k g z =
      C₂ (iteratedFDeriv ℝ (k + 1) (fderiv ℝ u) z) := by
    rw [iteratedFDeriv_succ_eq_comp_right (f := fderiv ℝ u) (x := z) (n := k)]
    simp [C₂, g, E, LinearIsometryEquiv.apply_symm_apply]
  have hC₁ (z : E) : iteratedFDeriv ℝ (k + 1) (fderiv ℝ u) z =
      C₁ (iteratedFDeriv ℝ (k + 2) u z) := by
    rw [iteratedFDeriv_succ_eq_comp_right (f := u) (x := z) (n := k + 1)]
    simp [C₁, E, LinearIsometryEquiv.apply_symm_apply]
  have hCurryDist (x y : E) :
      dist (iteratedFDeriv ℝ k g x) (iteratedFDeriv ℝ k g y) =
        dist (iteratedFDeriv ℝ (k + 2) u x) (iteratedFDeriv ℝ (k + 2) u y) := by
    rw [hC₂ x, hC₂ y, hC₁ x, hC₁ y]
    simp [C₁, C₂, (continuousMultilinearCurryRightEquiv' ℝ (k + 1) E ℝ).dist_map,
      (continuousMultilinearCurryRightEquiv' ℝ k E (E →L[ℝ] ℝ)).dist_map]
  have hPostDist (S T : E [×k]→L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ)) :
      dist (Q.compContinuousMultilinearMap S) (Q.compContinuousMultilinearMap T) ≤ dist S T := by
    have hdiff : Q.compContinuousMultilinearMap S - Q.compContinuousMultilinearMap T =
        Q.compContinuousMultilinearMap (S - T) := by
      ext m
      simp
    rw [dist_eq_norm, hdiff]
    calc
      ‖Q.compContinuousMultilinearMap (S - T)‖ ≤ ‖Q‖ * ‖S - T‖ :=
        Q.norm_compContinuousMultilinearMap_le _
      _ ≤ 1 * ‖S - T‖ :=
        mul_le_mul_of_nonneg_right (complexHessianEntryQ_norm_le i j) (norm_nonneg _)
      _ = dist S T := by simp [dist_eq_norm]
  have hsource : HolderOnWith (4 * H) α
      (iteratedFDeriv ℝ (k + 2) u) V :=
    hu.2.mono_const (by
      calc
        H = 1 * H := by simp
        _ ≤ 4 * H := mul_le_mul_of_nonneg_right (by norm_num) (bot_le))
  intro x hx y hy
  rw [hJetAt x hx, hJetAt y hy, edist_dist]
  calc
    ENNReal.ofReal (dist (Q.compContinuousMultilinearMap (iteratedFDeriv ℝ k g x))
        (Q.compContinuousMultilinearMap (iteratedFDeriv ℝ k g y))) ≤
      ENNReal.ofReal (dist (iteratedFDeriv ℝ k g x) (iteratedFDeriv ℝ k g y)) :=
        ENNReal.ofReal_le_ofReal (hPostDist _ _)
    _ = ENNReal.ofReal (dist (iteratedFDeriv ℝ (k + 2) u x)
        (iteratedFDeriv ℝ (k + 2) u y)) := by rw [hCurryDist]
    _ ≤ ((4 * H : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by
      rw [← edist_dist]
      exact hsource x hx y hy

/-- Each complex-Hessian entry has a quantitative lower-order Hölder bound controlled by the
corresponding two-higher-order jet of the potential. -/
theorem holderBoundOn_complexHessian_entry
    {n k : ℕ} {α H : ℝ≥0}
    {U V : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hVU : V ⊆ U)
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (huCont : ContDiffOn ℝ (k + 2) u U)
    (hu : HolderBoundOn (k + 2) α H V u) :
    ∀ i j,
      ContDiffOn ℝ k (fun z ↦ complexHessian u z i j) V ∧
      HolderBoundOn k α (4 * H) V (fun z ↦ complexHessian u z i j) := by
  intro i j
  constructor
  · have hDu : ContDiffOn ℝ (k + 1) (fderiv ℝ u) U := by
      exact huCont.fderiv_of_isOpen hU (by rfl)
    have hD₂u : ContDiffOn ℝ k (fderiv ℝ (fderiv ℝ u)) U := by
      exact hDu.fderiv_of_isOpen hU (by rfl)
    have hD₂eval (v w : EuclideanSpace ℂ (Fin n)) :
        ContDiffOn ℝ k (fun z ↦ fderiv ℝ (fderiv ℝ u) z v w) U := by
      have hv : ContDiffOn ℝ k (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) U := contDiffOn_const
      have hw : ContDiffOn ℝ k (fun _ : EuclideanSpace ℂ (Fin n) ↦ w) U := contDiffOn_const
      exact (hD₂u.clm_apply hv).clm_apply hw
    have hFormula : ContDiffOn ℝ k (fun z ↦
        ((fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
            (Complex.I • EuclideanSpace.single j 1) +
          Complex.I * (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single i 1)
            (Complex.I • EuclideanSpace.single j 1) -
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1))) / 4) U := by
      simp only [← Complex.ofRealCLM_apply]
      fun_prop
    have hHess : ContDiffOn ℝ k (fun z ↦ complexHessian u z i j) U := by
      apply hFormula.congr
      intro z hz
      have hSmoothAt : ContDiffAt ℝ 2 u z :=
        ((huCont z hz).contDiffAt (hU.mem_nhds hz)).of_le
          (by
            calc
              (2 : WithTop ℕ∞) ≤ 2 + (k : WithTop ℕ∞) := le_add_of_nonneg_right (by positivity)
              _ = (k : WithTop ℕ∞) + 2 := by rw [add_comm])
      rw [complexHessian_apply hSmoothAt]
    exact hHess.mono hVU
  · refine ⟨?_, ?_⟩
    · intro r hr z hz
      exact complexHessianEntry_iteratedFDeriv_bound hU hVU huCont hu i j r hr z hz
    · exact complexHessianEntry_topDerivative_holder hU hVU huCont hu i j

end CalabiYau.Schauder
