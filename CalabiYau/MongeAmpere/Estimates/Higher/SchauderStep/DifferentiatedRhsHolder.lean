module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Complex.Schauder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.BufferedInterpolation
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.CompactHolder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.DirectionalJets
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.HolderAddition
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.MatrixTraceProduct

/-!
# Hölder bounds for the differentiated Monge–Ampère right-hand side

The differentiated log-determinant equation has a scalar derivative of the prescribed density and
two real matrix-trace products. Directional jet control, inverse-coefficient bounds, and finite
matrix product estimates give a common `C^{r-2,α}` bound for both real and imaginary
coordinate directions. The lower inverse jets are explicitly Hölder, as required by the corrected
family trace-product bound; the reference-metric jets are smooth on the compact chart buffer.
The real directions alone cannot reconstruct all real jets on `ℂⁿ`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

private theorem contDiffOn_complexHessian_entries_of_contDiffOn_local
    {n : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (f : EuclideanSpace ℂ (Fin n) → ℝ)
    (hf : ContDiffOn ℝ ∞ f U) :
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

private theorem contDiffOn_matrixDet_of_contDiffOn_entries_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {U : Set E} {G : E → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U) :
    ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U := by
  simp only [Matrix.det_apply]
  fun_prop

private theorem contDiffOn_matrixInverse_entries_of_contDiffOn_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {U : Set E} {G : E → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U)
    (hdet : ∀ z ∈ U, (G z).det ≠ 0) :
    ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ (G z)⁻¹ i j) U := by
  have hdetfun : ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U :=
    contDiffOn_matrixDet_of_contDiffOn_entries_local hG
  have hinvdet : ContDiffOn ℝ ∞ (fun z ↦ ((G z).det)⁻¹) U :=
    hdetfun.inv hdet
  have hadj (i j : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ (G z).adjugate i j) U := by
    have hUpdate (a b : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ (G z).updateRow j (Pi.single i 1) a b) U := by
      by_cases ha : a = j
      · subst a
        by_cases hb : b = i
        · subst b
          simp [Matrix.updateRow_apply]
          exact contDiffOn_const
        · simp [Matrix.updateRow_apply, hb]
          exact contDiffOn_const
      · simp [Matrix.updateRow_apply, ha]
        exact hG a b
    have hdetUpdate := contDiffOn_matrixDet_of_contDiffOn_entries_local hUpdate
    apply hdetUpdate.congr
    intro z hz
    exact Matrix.adjugate_apply (G z) i j
  intro i j
  have hEq : (fun z ↦ (G z)⁻¹ i j) =
      fun z ↦ ((G z).det)⁻¹ * (G z).adjugate i j := by
    funext z
    rw [Matrix.inv_def]
    simp [Matrix.smul_apply, Ring.inverse_eq_inv]
  rw [hEq]
  exact hinvdet.mul (hadj i j)

omit [T2Space M] [CompactSpace M] in
private theorem contDiffOn_chart_perturbed_metric_inv_entries_of_solves
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2) (x : M)
    {W : Set (EuclideanSpace ℂ (Fin n))}
    (hWtarget : W ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∀ p ∈ S, ∀ i j, ContDiffOn ℝ ∞ (fun z ↦
      (ω₀.metricInChart x z + complexHessian
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ i j) W := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  intro p hp i j
  have hpot : ω₀.IsPotential p.2 := (hS p hp).2.1
  have hpotOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.2 Set.univ :=
    contMDiffOn_univ.mpr hpot.contMDiff
  have hcoord : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
      ∞ (p.2 ∘ e.symm) e.target := by
    exact hpotOn.comp (contMDiffOn_extChartAt_symm x) (by intro u hu; simp)
  have hcoord' : ContDiffOn ℝ ∞ (p.2 ∘ e.symm) e.target := hcoord.contDiffOn
  have hhess := contDiffOn_complexHessian_entries_of_contDiffOn_local
    (isOpen_extChartAt_target x) (p.2 ∘ e.symm) hcoord'
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun z ↦
    ω₀.metricInChart x z + complexHessian (p.2 ∘ e.symm) z
  have hG : ∀ a b, ContDiffOn ℝ ∞ (fun z ↦ G z a b) W := by
    intro a b
    exact ((ω₀.contDiffOn_metricInChart x a b).add (hhess a b)).mono hWtarget
  have hdet : ∀ z ∈ W, (G z).det ≠ 0 := by
    intro z hz
    have hpos : (G z).PosDef := by
      simpa [G, e, ω₀.metricInChart_perturb hpot x (hWtarget hz)] using
        (ω₀.perturb p.2 hpot).posDef_metricInChart x (hWtarget hz)
    have hunit : IsUnit (G z) := Matrix.PosDef.isUnit hpos
    have hunitdet : IsUnit (G z).det := (G z).isUnit_iff_isUnit_det.mp hunit
    exact hunitdet.ne_zero
  have hInv := contDiffOn_matrixInverse_entries_of_contDiffOn_local hG hdet
  simpa [G, e] using hInv i j

private theorem exists_ref_directional_derivative_holder
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₀ : KahlerForm n M) {x : M} {α : ℝ≥0} (hα : α ≤ 1)
    {k : ℕ} {U : Set (EuclideanSpace ℂ (Fin n))}
    (hUcompact : IsCompact (closure U))
    (hUtarget : closure U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ C : ℝ≥0, ∀ i : Fin n, ∀ b : Bool, ∀ j l,
      HolderBoundOn k α C U (fun z ↦ fderiv ℝ
        (fun u ↦ ω₀.metricInChart x u j l) z
        ((if b then Complex.I else 1) • EuclideanSpace.single i 1)) := by
  let W := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  have hW : IsOpen W := isOpen_extChartAt_target x
  let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ ω₀.metricInChart x z
  have hAsmooth : ∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A z j l) W := by
    intro j l
    exact ω₀.contDiffOn_metricInChart x j l
  let v (i : Fin n) (b : Bool) : EuclideanSpace ℂ (Fin n) :=
    (if b then Complex.I else 1) • EuclideanSpace.single i 1
  let Cij (i : Fin n) (b : Bool) : ℝ≥0 :=
    Classical.choose (CompactSmoothHolder.exists_holderBoundOn_matrix_directional_derivative_entries_of_contDiffOn_compact
      (k := k) (α := α) A (v i b) hW hUcompact hUtarget hα hAsmooth)
  have hCij (i : Fin n) (b : Bool) : ∀ j l,
      HolderBoundOn k α (Cij i b) (closure U)
        (fun z ↦ fderiv ℝ (fun u ↦ ω₀.metricInChart x u j l) z (v i b)) := by
    exact Classical.choose_spec
      (CompactSmoothHolder.exists_holderBoundOn_matrix_directional_derivative_entries_of_contDiffOn_compact
        (k := k) (α := α) A (v i b) hW hUcompact hUtarget hα hAsmooth)
  let C : ℝ≥0 := Finset.univ.sup (fun i : Fin n ↦ Finset.univ.sup (Cij i))
  have hle (i : Fin n) (b : Bool) : Cij i b ≤ C := by
    calc
      Cij i b ≤ Finset.univ.sup (Cij i) :=
        Finset.le_sup (s := Finset.univ) (f := Cij i) (Finset.mem_univ b)
      _ ≤ Finset.univ.sup (fun q : Fin n ↦ Finset.univ.sup (Cij q)) :=
        Finset.le_sup (s := Finset.univ)
          (f := fun q : Fin n ↦ Finset.univ.sup (Cij q)) (Finset.mem_univ i)
  refine ⟨C, ?_⟩
  intro i b j l
  have h := (hCij i b j l).mono_const (hle i b)
  exact h.mono_set (by intro z hz; exact subset_closure hz)

private theorem exists_uniform_holderBoundOn_directional_derivative_family
    {P E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set P} {W U L : Set E} {k : ℕ} {α C : ℝ≥0}
    (hW : IsOpen W) (hU : IsOpen U) (hL : IsCompact L)
    (hbuffer : closure U ⊆ interior L) (hLW : L ⊆ W)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (f : P → E → F) (v : P → E)
    (hf : ∀ p ∈ S, ContDiffOn ℝ ∞ (f p) W)
    (hv : ∀ p ∈ S, ‖v p‖ ≤ 1)
    (hbound : ∀ p ∈ S, ∀ j ≤ k + 2, ∀ z ∈ L,
      ‖iteratedFDeriv ℝ j (f p) z‖ ≤ C) :
    ∃ C' : ℝ≥0, ∀ p ∈ S,
      HolderBoundOn k α C' U (fun z ↦ fderiv ℝ (f p) z (v p)) := by
  let g : P → E → F := fun p z ↦ fderiv ℝ (f p) z (v p)
  have hg : ∀ p ∈ S, ContDiffOn ℝ ∞ (g p) W := by
    intro p hp
    have hderiv := (hf p hp).fderiv_of_isOpen hW (m := ∞) (by simp)
    exact hderiv.clm_apply contDiffOn_const
  have hboundg : ∀ p ∈ S, ∀ j ≤ k + 1, ∀ z ∈ L,
      ‖iteratedFDeriv ℝ j (g p) z‖ ≤ C := by
    intro p hp j hj z hz
    let T : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (v p)
    have hEval : ‖T‖ ≤ ‖v p‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (v p))
      intro L'
      change ‖L' (v p)‖ ≤ _
      simpa [mul_comm] using L'.le_opNorm (v p)
    have hiterAt : iteratedFDeriv ℝ j (g p) z =
        T.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ (f p)) z) := by
      have hfz : ContDiffAt ℝ ∞ (f p) z :=
        (hf p hp).contDiffAt (hW.mem_nhds (hLW hz))
      have hfd : ContDiffAt ℝ (k + 1) (fderiv ℝ (f p)) z :=
        hfz.fderiv_right (by
          exact_mod_cast (show ((k + 2 : ℕ) : ℕ∞) ≤ ⊤ from le_top))
      change iteratedFDeriv ℝ j (T ∘ fderiv ℝ (f p)) z = _
      simpa [T, Function.comp_apply, ContinuousLinearMap.apply_apply] using
        T.iteratedFDeriv_comp_left hfd (i := j) (by exact_mod_cast hj)
    rw [hiterAt]
    have hj' : j + 1 ≤ k + 2 := by omega
    calc
      ‖T.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ (f p)) z)‖ ≤
          ‖T‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ (f p)) z‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ ‖v p‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ (f p)) z‖ :=
        mul_le_mul_of_nonneg_right hEval (norm_nonneg _)
      _ ≤ ‖iteratedFDeriv ℝ j (fderiv ℝ (f p)) z‖ := by
        calc
          ‖v p‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ (f p)) z‖ ≤
              1 * ‖iteratedFDeriv ℝ j (fderiv ℝ (f p)) z‖ :=
            mul_le_mul_of_nonneg_right (hv p hp) (norm_nonneg _)
          _ = _ := one_mul _
      _ ≤ C := by
        simpa [norm_iteratedFDeriv_fderiv] using hbound p hp (j + 1) hj' z hz
  exact exists_uniform_holderBoundOn_family_of_buffered_derivative_bounds
    S g hW hU hL hbuffer hLW hα₀ hα₁ hg hboundg

private theorem holderBoundOn_neg_same_order
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α C : ℝ≥0} {K : Set E} (f : E → F)
    (hf : HolderBoundOn k α C K f) :
    HolderBoundOn k α C K (fun z ↦ -f z) := by
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    change ‖iteratedFDeriv ℝ j (-f) z‖ ≤ C
    rw [iteratedFDeriv_neg_apply]
    simpa using hf.1 j hj z hz
  · intro z hz w hw
    change edist (iteratedFDeriv ℝ k (-f) z)
      (iteratedFDeriv ℝ k (-f) w) ≤ _
    rw [iteratedFDeriv_neg_apply, iteratedFDeriv_neg_apply]
    simpa using hf.2.edist_le hz hw

omit [T2Space M] [CompactSpace M] in
/-- The differentiated right-hand side in each real-basis direction, namely `e_i` and
`I • e_i`, has a uniform `C^{r-2,α}` bound on the chart domain. -/
theorem exists_uniform_differentiated_rhs_holder
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    {x : M} {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {r : ℕ} (hr : 2 ≤ r) {CG CA : ℝ≥0}
    {U L : Set (EuclideanSpace ℂ (Fin n))}
    (hUopen : IsOpen U) (hUcompact : IsCompact (closure U))
    (hUtarget : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hLcompact : IsCompact L) (hBuffer : closure U ⊆ interior L)
    (hLtarget : L ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hGouter : ∀ p ∈ S,
      HolderBoundOn (r + 2) 0 CG L
        (p.1 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm))
    (hCoeffLower : ∀ p ∈ S, ∀ j k, ∀ m < r - 2,
      HolderOnWith CA α (iteratedFDeriv ℝ m (fun z ↦
        (ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ j k)) U)
    (hCoeff : ∀ p ∈ S, ∀ j k,
      HolderBoundOn (r - 2) α CA U (fun z ↦
        (ω₀.metricInChart x z +
          complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ j k)) :
    ∃ CR : ℝ≥0, ∀ p ∈ S, ∀ i : Fin n, ∀ β : ℂ,
      (β = 1 ∨ β = Complex.I) → HolderBoundOn (r - 2) α CR U (fun z ↦
        fderiv ℝ (p.1 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z
            (β • EuclideanSpace.single i 1) -
          RCLike.re (((ω₀.metricInChart x z +
            complexHessian (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ *
              (Matrix.of fun j k ↦ fderiv ℝ
                (fun u ↦ ω₀.metricInChart x u j k) z (β • EuclideanSpace.single i 1))).trace) +
          RCLike.re ((ω₀.metricInChart x z)⁻¹ *
            (Matrix.of fun j k ↦ fderiv ℝ
              (fun u ↦ ω₀.metricInChart x u j k) z (β • EuclideanSpace.single i 1))).trace) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let W := e.target
  let k := r - 2
  have hW : IsOpen W := isOpen_extChartAt_target x
  have hUW : U ⊆ W := by
    intro z hz
    exact hUtarget (subset_closure hz)
  let P := ((M → ℝ) × (M → ℝ)) × (Fin n × Bool)
  let Q : Set P := {q | q.1 ∈ S}
  let v : P → EuclideanSpace ℂ (Fin n) := fun q ↦
    (if q.2.2 then Complex.I else 1) • EuclideanSpace.single q.2.1 1
  let g : P → EuclideanSpace ℂ (Fin n) → ℝ := fun q ↦ q.1.1 ∘ e.symm
  have hv : ∀ q ∈ Q, ‖v q‖ ≤ 1 := by
    intro q hq
    by_cases hb : q.2.2
    · simp [v, hb, norm_smul, Complex.norm_I]
    · simp [v, hb]
  have hg : ∀ q ∈ Q, ContDiffOn ℝ ∞ (g q) W := by
    intro q hq
    have hGOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
        ∞ q.1.1 Set.univ := contMDiffOn_univ.mpr (hS q.1 hq).1
    have hcoord : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
        ∞ (q.1.1 ∘ e.symm) W := by
      exact hGOn.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
    exact hcoord.contDiffOn
  have hgBound : ∀ q ∈ Q, ∀ j ≤ k + 2, ∀ z ∈ L,
      ‖iteratedFDeriv ℝ j (g q) z‖ ≤ CG := by
    intro q hq j hj z hz
    have hle : j ≤ r + 2 := by omega
    simpa [g, e] using (hGouter q.1 hq).1 j hle z hz
  obtain ⟨CGD, hGdir⟩ := exists_uniform_holderBoundOn_directional_derivative_family
    hW hUopen hLcompact hBuffer hLtarget hα₀ hα₁ g v hg hv hgBound
  obtain ⟨CrefDir, hRefDir⟩ := exists_ref_directional_derivative_holder
    (k := r - 2) ω₀ hα₁.le hUcompact hUtarget
  let d : Fin n → Bool → Fin n → Fin n → EuclideanSpace ℂ (Fin n) → ℂ :=
    fun i b j l z ↦ fderiv ℝ (fun u ↦ ω₀.metricInChart x u j l) z
      ((if b then Complex.I else 1) • EuclideanSpace.single i 1)
  let A : P → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun q z ↦
    (ω₀.metricInChart x z + complexHessian (q.1.2 ∘ e.symm) z)⁻¹
  let B : P → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun q z ↦
    Matrix.of fun j l ↦ d q.2.1 q.2.2 j l z
  have hAsmooth : ∀ q ∈ Q, ∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A q z j l) W := by
    intro q hq j l
    have hInv := contDiffOn_chart_perturbed_metric_inv_entries_of_solves
      ω₀ S hS x (W := W) (by intro z hz; exact hz) q.1 hq j l
    simpa [A, e] using hInv
  have hdSmooth : ∀ i b j l, ContDiffOn ℝ ∞ (d i b j l) W := by
    intro i b j l
    have hmetric := (ω₀.contDiffOn_metricInChart x j l).fderiv_of_isOpen
      hW (m := ∞) (by simp)
    have hdir : ContDiffOn ℝ ∞ (fun _ : EuclideanSpace ℂ (Fin n) ↦
        (if b then Complex.I else (1 : ℂ)) • EuclideanSpace.single i (1 : ℂ)) W :=
      contDiffOn_const
    simpa [d, W, e] using hmetric.clm_apply hdir
  have hBsmooth : ∀ q ∈ Q, ∀ j l, ContDiffOn ℝ ∞ (fun z ↦ B q z j l) W := by
    intro q hq j l
    simpa [B] using hdSmooth q.2.1 q.2.2 j l
  have hAjets : ∀ q ∈ Q, ∀ j l,
      (∀ m ≤ k, ∀ z ∈ U, ‖iteratedFDeriv ℝ m (fun z ↦ A q z j l) z‖ ≤ CA) ∧
      (∀ m < k, HolderOnWith CA α
        (iteratedFDeriv ℝ m (fun z ↦ A q z j l)) U) ∧
      HolderOnWith CA α (iteratedFDeriv ℝ k (fun z ↦ A q z j l)) U := by
    intro q hq j l
    have htop := hCoeff q.1 hq j l
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · intro m hm z hz
      simpa [A, e] using htop.1 m hm z hz
    · intro m hm
      simpa [A, e] using hCoeffLower q.1 hq j l m hm
    · simpa [A, e] using htop.2
  have hBtop : ∀ q ∈ Q, ∀ j l,
      HolderBoundOn k α CrefDir U (fun z ↦ B q z j l) := by
    intro q hq j l
    simpa [B, d] using hRefDir q.2.1 q.2.2 j l
  let Didx := Fin n × (Bool × Fin k)
  let vLower (i : Fin n) (b : Bool) : EuclideanSpace ℂ (Fin n) :=
    (if b then Complex.I else 1) • EuclideanSpace.single i 1
  let ArefLower : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ ω₀.metricInChart x z
  have hArefLowerSmooth : ∀ j l,
      ContDiffOn ℝ ∞ (fun z ↦ ArefLower z j l) W := by
    intro j l
    exact ω₀.contDiffOn_metricInChart x j l
  let CLower : Didx → ℝ≥0 := fun t ↦ Classical.choose
    (CompactSmoothHolder.exists_holderBoundOn_matrix_directional_derivative_entries_of_contDiffOn_compact
      (k := t.2.2.val) (α := α) ArefLower (vLower t.1 t.2.1)
      hW hUcompact hUtarget hα₁.le hArefLowerSmooth)
  have hCLower (t : Didx) : ∀ j l,
      HolderBoundOn (t.2.2.val) α (CLower t) (closure U)
        (fun z ↦ d t.1 t.2.1 j l z) := by
    simpa [d, ArefLower, vLower, CLower] using Classical.choose_spec
      (CompactSmoothHolder.exists_holderBoundOn_matrix_directional_derivative_entries_of_contDiffOn_compact
        (k := t.2.2.val) (α := α) ArefLower (vLower t.1 t.2.1)
        hW hUcompact hUtarget hα₁.le hArefLowerSmooth)
  let CLowerAll : ℝ≥0 := Finset.univ.sup CLower
  have hCLowerLe (t : Didx) : CLower t ≤ CLowerAll :=
    Finset.le_sup (s := Finset.univ) (f := CLower) (Finset.mem_univ t)
  have hBlower : ∀ q ∈ Q, ∀ j l, ∀ m < k,
      HolderOnWith CLowerAll α
        (iteratedFDeriv ℝ m (fun z ↦ B q z j l)) U := by
    intro q hq j l m hm
    let t : Didx := (q.2.1, (q.2.2, ⟨m, hm⟩))
    have hholder := (hCLower t j l).2.mono_const (hCLowerLe t)
    have hU := hholder.mono (fun z hz ↦ subset_closure hz)
    simpa [B, d, t, Didx] using hU
  let CB : ℝ≥0 := max CrefDir CLowerAll
  have hB : ∀ q ∈ Q, ∀ j l,
      (∀ m ≤ k, ∀ z ∈ U,
        ‖iteratedFDeriv ℝ m (fun z ↦ B q z j l) z‖ ≤ CB) ∧
      (∀ m < k, HolderOnWith CB α
        (iteratedFDeriv ℝ m (fun z ↦ B q z j l)) U) ∧
      HolderOnWith CB α (iteratedFDeriv ℝ k (fun z ↦ B q z j l)) U := by
    intro q hq j l
    have htop := hBtop q hq j l
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · intro m hm z hz
      exact (htop.1 m hm z hz).trans (le_max_left _ _)
    · intro m hm
      exact (hBlower q hq j l m hm).mono_const (le_max_right _ _)
    · exact htop.2.mono_const (le_max_left _ _)
  obtain ⟨Ctrace, htrace⟩ := exists_holderBoundOn_matrix_trace_product
    (P := P) (E := EuclideanSpace ℂ (Fin n)) (n := n) (k := k) (α := α)
    (C := CA) (D := CB) Q hW hUW A B hAsmooth hBsmooth hAjets hB
  let Gref : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ ω₀.metricInChart x z
  have hGrefSmooth : ∀ j l, ContDiffOn ℝ ∞ (fun z ↦ Gref z j l) W := by
    intro j l
    exact ω₀.contDiffOn_metricInChart x j l
  have hGrefDet : ∀ z ∈ W, (Gref z).det ≠ 0 := by
    intro z hz
    have hunit : IsUnit (Gref z) := (ω₀.posDef_metricInChart x (by simpa [W, e] using hz)).isUnit
    exact ((Gref z).isUnit_iff_isUnit_det.mp hunit).ne_zero
  have hGrefInvSmooth := contDiffOn_matrixInverse_entries_of_contDiffOn_local
    hGrefSmooth hGrefDet
  let R : Fin n → Bool → EuclideanSpace ℂ (Fin n) → ℝ := fun i b z ↦
    RCLike.re ((Gref z)⁻¹ * Matrix.of fun j l ↦ d i b j l z).trace
  have hRsmooth : ∀ i b, ContDiffOn ℝ ∞ (R i b) W := by
    intro i b
    have hterm (j l : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ Complex.reCLM ((Gref z)⁻¹ j l * d i b l j z)) W := by
      have hmul := (hGrefInvSmooth j l).mul (hdSmooth i b l j)
      exact Complex.reCLM.contDiff.comp_contDiffOn hmul
    have hRsum : ContDiffOn ℝ ∞ (fun z ↦
        ∑ j : Fin n, ∑ l : Fin n,
          Complex.reCLM ((Gref z)⁻¹ j l * d i b l j z)) W := by
      refine ContDiffOn.sum (fun j _ ↦ ?_)
      exact ContDiffOn.sum (fun l _ ↦ hterm j l)
    have hRidentity : R i b = fun z ↦
        ∑ j : Fin n, ∑ l : Fin n,
          Complex.reCLM ((Gref z)⁻¹ j l * d i b l j z) := by
      funext z
      simp [R, Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]
    rw [hRidentity]
    exact hRsum
  let CRefTrace : Fin n → Bool → ℝ≥0 := fun i b ↦ Classical.choose
    (CompactSmoothHolder.exists_holderBoundOn_of_contDiffOn_neighborhood_of_compact
      (k := k) (α := α) (R i b) hW hUcompact hUtarget hα₁.le (hRsmooth i b))
  have hCRefTrace (i : Fin n) (b : Bool) :
      HolderBoundOn k α (CRefTrace i b) (closure U) (R i b) :=
    Classical.choose_spec
      (CompactSmoothHolder.exists_holderBoundOn_of_contDiffOn_neighborhood_of_compact
        (k := k) (α := α) (R i b) hW hUcompact hUtarget hα₁.le (hRsmooth i b))
  let CRefTraceAll : ℝ≥0 :=
    Finset.univ.sup (fun i : Fin n ↦ Finset.univ.sup (CRefTrace i))
  have hCRefTraceLe (i : Fin n) (b : Bool) : CRefTrace i b ≤ CRefTraceAll := by
    calc
      CRefTrace i b ≤ Finset.univ.sup (CRefTrace i) :=
        Finset.le_sup (s := Finset.univ) (f := CRefTrace i) (Finset.mem_univ b)
      _ ≤ Finset.univ.sup (fun j : Fin n ↦ Finset.univ.sup (CRefTrace j)) :=
        Finset.le_sup (s := Finset.univ)
          (f := fun j : Fin n ↦ Finset.univ.sup (CRefTrace j)) (Finset.mem_univ i)
  have hRholder : ∀ i b, HolderBoundOn k α CRefTraceAll U (R i b) := by
    intro i b
    exact (hCRefTrace i b).mono_const (hCRefTraceLe i b) |>.mono_set
      (by intro z hz; exact subset_closure hz)
  have hPertTraceSmooth : ∀ q ∈ Q, ContDiffOn ℝ ∞
      (fun z ↦ RCLike.re ((A q z * B q z).trace)) W := by
    intro q hq
    have hsum : ContDiffOn ℝ ∞ (fun z ↦
        ∑ j : Fin n, ∑ l : Fin n,
          Complex.reCLM (A q z j l * B q z l j)) W := by
      refine ContDiffOn.sum (fun j _ ↦ ?_)
      refine ContDiffOn.sum (fun l _ ↦ ?_)
      have hmul := (hAsmooth q hq j l).mul (hBsmooth q hq l j)
      exact Complex.reCLM.contDiff.comp_contDiffOn hmul
    have hEq : (fun z ↦ RCLike.re ((A q z * B q z).trace)) = fun z ↦
        ∑ j : Fin n, ∑ l : Fin n,
          Complex.reCLM (A q z j l * B q z l j) := by
      funext z
      simp [Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]
    rw [hEq]
    exact hsum
  have hkTop : (k : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)
  have hGderivSmooth : ∀ q ∈ Q, ContDiffOn ℝ ∞
      (fun z ↦ fderiv ℝ (g q) z (v q)) W := by
    intro q hq
    have hderiv := (hg q hq).fderiv_of_isOpen hW (m := ∞) (by simp)
    have hV : ContDiffOn ℝ ∞ (fun _ : EuclideanSpace ℂ (Fin n) ↦ v q) W :=
      contDiffOn_const
    exact hderiv.clm_apply hV
  let rhs (q : P) : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
    fderiv ℝ (g q) z (v q) - RCLike.re ((A q z * B q z).trace) +
      RCLike.re ((Gref z)⁻¹ * Matrix.of fun j l ↦ d q.2.1 q.2.2 j l z).trace
  let CR : ℝ≥0 := (CGD + Ctrace) + CRefTraceAll
  have hRhsBound : ∀ q ∈ Q, HolderBoundOn k α CR U (rhs q) := by
    intro q hq
    let fG : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ fderiv ℝ (g q) z (v q)
    let fT : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦ RCLike.re ((A q z * B q z).trace)
    let fR : EuclideanSpace ℂ (Fin n) → ℝ := R q.2.1 q.2.2
    have hGboundq : HolderBoundOn k α CGD U fG := by
      simpa [fG] using hGdir q hq
    have hTraceBoundq : HolderBoundOn k α Ctrace U fT := by
      have ht := htrace q hq
      refine ⟨?_, ?_⟩
      · intro m hm z hz
        simpa [fT] using ht.1 m hm z hz
      · simpa [fT] using ht.2
    have hNegBoundq : HolderBoundOn k α Ctrace U (fun z ↦ -fT z) :=
      holderBoundOn_neg_same_order fT hTraceBoundq
    have hGsm : ∀ z ∈ U, ContDiffAt ℝ k fG z := by
      intro z hz
      exact (hGderivSmooth q hq).contDiffAt (hW.mem_nhds (hUW hz)) |>.of_le hkTop
    have hTsm : ∀ z ∈ U, ContDiffAt ℝ k fT z := by
      intro z hz
      exact (hPertTraceSmooth q hq).contDiffAt (hW.mem_nhds (hUW hz)) |>.of_le hkTop
    have hRsm : ∀ z ∈ U, ContDiffAt ℝ k fR z := by
      intro z hz
      exact (hRsmooth q.2.1 q.2.2).contDiffAt
        (hW.mem_nhds (hUW hz)) |>.of_le hkTop
    have hAdd1 := holderBoundOn_add_same_order fG (fun z ↦ -fT z)
      hGboundq hNegBoundq hGsm (fun z hz ↦ (hTsm z hz).neg)
    have hAdd1sm : ∀ z ∈ U,
        ContDiffAt ℝ k (fun z ↦ fG z + -fT z) z := by
      intro z hz
      exact (hGsm z hz).add (hTsm z hz).neg
    have hRefBoundq : HolderBoundOn k α CRefTraceAll U fR := by
      simpa [fR] using hRholder q.2.1 q.2.2
    have hAdd2 := holderBoundOn_add_same_order (fun z ↦ fG z + -fT z) fR
      hAdd1 hRefBoundq hAdd1sm hRsm
    have hEq : rhs q = fun z ↦ (fG z + -fT z) + fR z := by
      funext z
      simp [rhs, fG, fT, fR, R]
      ring
    rw [hEq]
    exact hAdd2
  refine ⟨CR, ?_⟩
  intro p hp i β hβ
  rcases hβ with hβ | hβ
  · subst β
    have hq : ((p, (i, false)) : P) ∈ Q := hp
    simpa [rhs, k, v, g, A, B, d, Gref, R, e, sub_eq_add_neg] using
      hRhsBound (p, (i, false)) hq
  · subst β
    have hq : ((p, (i, true)) : P) ∈ Q := hp
    simpa [rhs, k, v, g, A, B, d, Gref, R, e, sub_eq_add_neg] using
      hRhsBound (p, (i, true)) hq

end KahlerForm

end
