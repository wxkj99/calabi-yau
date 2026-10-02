module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Complex.Schauder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.PositiveLowerBound
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.UniformInverseEntryBound

/-!
# Uniform inverse entries of the perturbed metric

On a compact chart piece the reference determinant has a positive lower bound. The
Monge–Ampère determinant equation and the uniform zeroth-order bound on prescribed data
preserve that bound up to a fixed positive factor. A common potential Hessian bound gives
an upper bound on all perturbed-metric entries. The finite adjugate formula then controls
all inverse entries with ONE constant for the entire solution family.

Source: Yau, *On the Ricci curvature of a compact Kähler manifold and the complex
Monge–Ampère equation* (1978), §4; Székelyhidi, *An Introduction to Extremal Kähler
Metrics*, §2.3, Theorem 2.8, p. 28.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

/-- Determinant nondegeneracy and bounded metric entries yield a common bound on the
perturbed inverse matrix entries, with the existential constant OUTSIDE the family. -/
private theorem complexHessian_norm_le_of_orderTwoBound
    {n : ℕ} {C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hD : ∀ z ∈ K, ‖iteratedFDeriv ℝ 2 f z‖ ≤ (C : ℝ))
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n)
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ K) :
    ‖complexHessian f z i j‖ ≤ (C : ℝ) := by
  let u : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iu := Complex.I • u
  let iv := Complex.I • v
  let D := iteratedFDeriv ℝ 2 f
  have hu : ‖u‖ = 1 := by simp [u]
  have hv : ‖v‖ = 1 := by simp [v]
  have hiu : ‖iu‖ = 1 := by simp [iu, hu, norm_smul, Complex.norm_I]
  have hiv : ‖iv‖ = 1 := by simp [iv, hv, norm_smul, Complex.norm_I]
  have hform : complexHessian f z i j =
      ((D z ![u, v] : ℂ) + D z ![iu, iv] +
        Complex.I * (D z ![u, iv] - D z ![iu, v])) / 4 := by
    rw [complexHessian_apply (hSmooth z hz) i j]
    rw [show fderiv ℝ (fderiv ℝ f) z u v = D z ![u, v] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![u, v]).symm,
      show fderiv ℝ (fderiv ℝ f) z iu iv = D z ![iu, iv] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![iu, iv]).symm,
      show fderiv ℝ (fderiv ℝ f) z u iv = D z ![u, iv] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![u, iv]).symm,
      show fderiv ℝ (fderiv ℝ f) z iu v = D z ![iu, v] by
          simpa [D] using (iteratedFDeriv_two_apply f z ![iu, v]).symm]
  have hEval (w : Fin 2 → EuclideanSpace ℂ (Fin n))
      (hw0 : ‖w 0‖ = 1) (hw1 : ‖w 1‖ = 1) : ‖D z w‖ ≤ ‖D z‖ := by
    calc
      ‖D z w‖ ≤ ‖D z‖ * ∏ k, ‖w k‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖D z‖ := by simp [hw0, hw1]
  have hDz : ‖D z‖ ≤ (C : ℝ) := hD z hz
  have h1 : ‖((D z ![u, v] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![u, v] hu hv).trans hDz
  have h2 : ‖((D z ![iu, iv] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![iu, iv] hiu hiv).trans hDz
  have h3 : ‖((D z ![u, iv] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![u, iv] hu hiv).trans hDz
  have h4 : ‖((D z ![iu, v] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![iu, v] hiu hv).trans hDz
  have hCross : ‖Complex.I * ((D z ![u, iv] : ℂ) - D z ![iu, v])‖ ≤
      (C : ℝ) + C := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (norm_sub_le _ _).trans (add_le_add h3 h4)
  have hNumerator : ‖(D z ![u, v] : ℂ) + D z ![iu, iv] +
      Complex.I * (D z ![u, iv] - D z ![iu, v])‖ ≤
      (C : ℝ) + C + ((C : ℝ) + C) := by
    calc
      _ ≤ ‖(D z ![u, v] : ℂ)‖ + ‖(D z ![iu, iv] : ℂ)‖ +
          ‖Complex.I * ((D z ![u, iv] : ℂ) - D z ![iu, v])‖ := by
        calc
          _ ≤ ‖(D z ![u, v] : ℂ) + D z ![iu, iv]‖ +
              ‖Complex.I * ((D z ![u, iv] : ℂ) - D z ![iu, v])‖ := norm_add_le _ _
          _ ≤ _ := by exact add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (C : ℝ) + C + ((C : ℝ) + C) := add_le_add (add_le_add h1 h2) hCross
  rw [hform, norm_div, Complex.norm_ofNat]
  calc
    ‖(D z ![u, v] : ℂ) + D z ![iu, iv] +
        Complex.I * (D z ![u, iv] - D z ![iu, v])‖ / 4 ≤
        ((C : ℝ) + C + ((C : ℝ) + C)) / 4 := div_le_div_of_nonneg_right hNumerator (by norm_num)
    _ = C := by ring

theorem exists_uniform_perturbed_metric_inverse_entry_bound
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ω₀.SolvesMongeAmpere p.1 p.2)
    {x : M} {α Cφ CG : ℝ≥0} {r : ℕ} (hr : 2 ≤ r)
    {U : Set (EuclideanSpace ℂ (Fin n))}
    (hUcompact : IsCompact (closure U))
    (hUtarget : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hCurrent : ∀ p ∈ S,
      HolderBoundOn r α Cφ (closure U)
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm))
    (hGlocal : ∀ p ∈ S,
      HolderBoundOn (r + 2) 0 CG (closure U)
        (p.1 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)) :
    ∃ B : ℝ≥0, ∀ p ∈ S, ∀ z ∈ U, ∀ i j,
      ‖(ω₀.metricInChart x z + complexHessian
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ i j‖ ≤ B := by
  classical
  by_cases hU : U.Nonempty
  · have hKne : (closure U).Nonempty := hU.mono subset_closure
    let fdet : EuclideanSpace ℂ (Fin n) → ℝ :=
      fun z ↦ RCLike.re (ω₀.metricInChart x z).det
    have hmetricEntry : ∀ i j, ContinuousOn
        (fun z ↦ ω₀.metricInChart x z i j) (closure U) := by
      intro i j
      exact (ω₀.contDiffOn_metricInChart x i j).continuousOn.mono hUtarget
    have hcompactBound : ∀ ij : Fin n × Fin n, ∃ C : ℝ,
        ∀ z ∈ closure U, ‖ω₀.metricInChart x z ij.1 ij.2‖ ≤ C := by
      intro ij
      exact hUcompact.exists_bound_of_continuousOn
        ((ω₀.contDiffOn_metricInChart x ij.1 ij.2).continuousOn.mono hUtarget)
    let Cij : Fin n × Fin n → ℝ := fun ij ↦ max 0 (Classical.choose (hcompactBound ij))
    have hCij : ∀ ij z, z ∈ closure U →
        ‖ω₀.metricInChart x z ij.1 ij.2‖ ≤ Cij ij := by
      intro ij z hz
      exact (Classical.choose_spec (hcompactBound ij) z hz).trans (le_max_right 0 _)
    have hCij_nonneg : ∀ ij, 0 ≤ Cij ij := fun ij ↦ le_max_left 0 _
    let Cref : ℝ := 1 + ∑ ij : Fin n × Fin n, Cij ij
    have hCref : ∀ i j z, z ∈ closure U →
        ‖ω₀.metricInChart x z i j‖ ≤ Cref := by
      intro i j z hz
      have hle : Cij (i, j) ≤ ∑ ij : Fin n × Fin n, Cij ij :=
        Finset.single_le_sum (fun ij _ ↦ hCij_nonneg ij) (Finset.mem_univ (i, j))
      calc
        ‖ω₀.metricInChart x z i j‖ ≤ Cij (i, j) := hCij (i, j) z hz
        _ ≤ (∑ ij : Fin n × Fin n, Cij ij) := hle
        _ ≤ Cref := by simp [Cref]
    have hfdet : ContinuousOn fdet (closure U) := by
      dsimp [fdet]
      have hdetFormula (z : EuclideanSpace ℂ (Fin n)) : (ω₀.metricInChart x z).det =
          ∑ σ : Equiv.Perm (Fin n),
            ((Equiv.Perm.sign σ : ℤ) : ℂ) *
              ∏ k : Fin n, ω₀.metricInChart x z (σ k) k := by
        rw [Matrix.det_apply']
      simp_rw [hdetFormula]
      fun_prop
    have hfpos : ∀ z ∈ closure U, 0 < fdet z := by
      intro z hz
      dsimp [fdet]
      exact (Complex.pos_iff.mp ((ω₀.posDef_metricInChart x (hUtarget hz)).det_pos)).1
    obtain ⟨δ, hδ, hδlower⟩ :=
      PositiveLowerBound.exists_pos_lower_bound_of_continuousOn_of_forall_pos
        hUcompact hKne hfdet hfpos
    by_cases hSne : S.Nonempty
    · obtain ⟨p₀, hp₀⟩ := hSne
      let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
      let f := p₀.2 ∘ e.symm
      have hpot : ω₀.IsPotential p₀.2 := (hS p₀ hp₀).1
      have hfMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f e.target := by
        dsimp [f, e]
        exact ((contMDiffOn_univ.mpr hpot.1).comp
          (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x)
          (by intro z hz; simp))
      have hCrefNonneg : 0 ≤ Cref := by
        dsimp [Cref]
        positivity
      have hC : 0 ≤ Cref + Cφ := by positivity
      have hδ' : 0 < δ * Real.exp (-(CG : ℝ)) := by positivity
      obtain ⟨B, hB⟩ := UniformInverseEntryBound.exists_uniform_matrix_inverse_entry_bound
        (n := n) hC hδ'
      refine ⟨B, ?_⟩
      intro p hp z hz i j
      have hzK : z ∈ closure U := subset_closure hz
      have hzT : z ∈ e.target := hUtarget hzK
      let y := e.symm z
      let fp := p.2 ∘ e.symm
      let A : Matrix (Fin n) (Fin n) ℂ := ω₀.metricInChart x z + complexHessian fp z
      have hpotential : ω₀.IsPotential p.2 := (hS p hp).1
      have hfpMD : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ fp e.target := by
        dsimp [fp, e]
        exact ((contMDiffOn_univ.mpr hpotential.1).comp
          (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x)
          (by intro w hw; simp))
      have hfpSmooth : ContDiffAt ℝ 2 fp z := by
        exact (hfpMD.contDiffOn.contDiffAt
          ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).mem_nhds hzT)).of_le
            (WithTop.coe_le_coe.mpr (by norm_num))
      have hHess : ∀ a b, ‖complexHessian fp z a b‖ ≤ (Cφ : ℝ) := by
        intro a b
        exact complexHessian_norm_le_of_orderTwoBound
          (fun w hw ↦ (hCurrent p hp).1 2 (by omega) w hw) (fun w hw ↦
            (hfpMD.contDiffOn.contDiffAt
              ((isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x).mem_nhds
                (hUtarget hw))).of_le (WithTop.coe_le_coe.mpr (by norm_num))) a b hzK
      have hAentry : ∀ a b, ‖A a b‖ ≤ Cref + Cφ := by
        intro a b
        dsimp [A]
        calc
          ‖ω₀.metricInChart x z a b + complexHessian fp z a b‖ ≤
              ‖ω₀.metricInChart x z a b‖ + ‖complexHessian fp z a b‖ := norm_add_le _ _
          _ ≤ Cref + Cφ := add_le_add
            (hCref a b z hzK) (hHess a b)
      have hGbound : ‖iteratedFDeriv ℝ 0 (p.1 ∘ e.symm) z‖ ≤ (CG : ℝ) :=
        (hGlocal p hp).1 0 (by omega) z hzK
      have hGabs : |p.1 y| ≤ (CG : ℝ) := by
        simpa only [norm_iteratedFDeriv_zero, Function.comp_apply, Real.norm_eq_abs] using hGbound
      have hGlo : -(CG : ℝ) ≤ p.1 y := (abs_le.mp hGabs).1
      have hExp : Real.exp (-(CG : ℝ)) ≤ Real.exp (p.1 y) :=
        Real.exp_le_exp.mpr hGlo
      have hdetRef : δ ≤ (ω₀.metricInChart x z).det.re := hδlower z hzK
      have hySource : y ∈ e.source := e.map_target hzT
      have hyChart : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
        rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))]
        exact hySource
      have hyCoord : e y = z := e.right_inv hzT
      have hMA := (hS p hp).2 y
      rw [mongeAmpere_eq_inChart hpotential.1 x hyChart] at hMA
      rw [hyCoord] at hMA
      have hMA' : ((ω₀.metricInChart x z + complexHessian fp z).det).re /
          (ω₀.metricInChart x z).det.re = Real.exp (p.1 y) := by
        simpa [fp, e] using hMA
      have hdetEq : (A.det).re = Real.exp (p.1 y) * (ω₀.metricInChart x z).det.re := by
        dsimp [A]
        calc
          _ = (((ω₀.metricInChart x z + complexHessian fp z).det).re /
                (ω₀.metricInChart x z).det.re) * (ω₀.metricInChart x z).det.re :=
            (div_mul_cancel₀ _ (Complex.pos_iff.mp
              ((ω₀.posDef_metricInChart x hzT).det_pos)).1.ne').symm
          _ = Real.exp (p.1 y) * (ω₀.metricInChart x z).det.re :=
            congrArg (fun t : ℝ ↦ t * (ω₀.metricInChart x z).det.re) hMA'
      have hdetLower : δ * Real.exp (-(CG : ℝ)) ≤ (A.det).re := by
        calc
          δ * Real.exp (-(CG : ℝ)) ≤ δ * Real.exp (p.1 y) :=
            mul_le_mul_of_nonneg_left hExp hδ.le
          _ ≤ (ω₀.metricInChart x z).det.re * Real.exp (p.1 y) :=
            mul_le_mul_of_nonneg_right hdetRef (Real.exp_nonneg _)
          _ = (A.det).re := by rw [hdetEq]; ring
      have hdetNorm : δ * Real.exp (-(CG : ℝ)) ≤ ‖A.det‖ :=
        hdetLower.trans (le_abs_self (A.det).re |>.trans (Complex.abs_re_le_norm _))
      have hfinal := hB A hAentry hdetNorm i j
      simpa [A, fp, e] using hfinal
    · refine ⟨0, ?_⟩
      intro p hp z hz i j
      exact False.elim (hSne ⟨p, hp⟩)
  · refine ⟨0, ?_⟩
    intro p hp z hz i j
    exact False.elim (hU ⟨z, hz⟩)

end KahlerForm

end
