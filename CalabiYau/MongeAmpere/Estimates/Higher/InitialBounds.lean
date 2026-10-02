module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Analysis.Elliptic.Schauder
import CalabiYau.Geometry.Complex.Forms.Positive

/-!
# Initial local Schauder bound for the bootstrap

The starting `C^{2,α}` estimate on one chart compact follows from the uniform third-order
bound, which makes the trace Laplacian `C^{0,α}`. The interior Schauder estimate then bounds the
potential in `C^{2,α}`, providing the initial step for the differentiated-equation bootstrap.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §2.3, Theorem 2.8, p. 28,
and §3.3, proof of Proposition 3.11, pp. 46–47.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
section

variable [T2Space M] [CompactSpace M]


private theorem holderBoundOn_zero_of_lipschitzOnWith
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} (hK : IsCompact K) {f : E → F} {C L : ℝ≥0}
    (hval : ∀ z ∈ K, ‖iteratedFDeriv ℝ 0 f z‖ ≤ C)
    (hLip : LipschitzOnWith L (iteratedFDeriv ℝ 0 f) K)
    (α : ℝ≥0) (hα : α ≤ 1) :
    HolderBoundOn 0 α (max C (L * (Metric.ediam K).toNNReal ^ ((1 : ℝ) - α))) K f := by
  let D : ℝ≥0 := (Metric.ediam K).toNNReal
  have hdiamTop : Metric.ediam K ≠ ⊤ := hK.isBounded.ediam_ne_top
  have hdiam (z : E) (hz : z ∈ K) (w : E) (hw : w ∈ K) :
      edist z w ≤ (D : ENNReal) := by
    have heq : (D : ENNReal) = Metric.ediam K := by
      change ↑(Metric.ediam K).toNNReal = Metric.ediam K
      exact ENNReal.coe_toNNReal hdiamTop
    rw [heq]
    exact Metric.edist_le_ediam_of_mem hz hw
  have hHolder : HolderOnWith (L * D ^ ((1 : ℝ) - α)) α
      (iteratedFDeriv ℝ 0 f) K := hLip.holderOnWith.of_le hdiam hα
  unfold HolderBoundOn
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact (hval z hz).trans (le_max_left _ _)
  · exact hHolder.mono_const (by simp [D])

private theorem re_coeffMatrix_diag_eq_form_eval
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (j : Fin n) :
    (α.coeffMatrix j j).re =
      (α ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single j 1]) / 2 := by
  simp [ContinuousAlternatingMap.coeffMatrix, Complex.mul_re]

private theorem coeffMatrix_diag_re_nonneg_of_isNonneg
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ)
    (hα : α.IsNonneg) (j : Fin n) : 0 ≤ (α.coeffMatrix j j).re := by
  rw [re_coeffMatrix_diag_eq_form_eval]
  exact div_nonneg (hα.2 (EuclideanSpace.single j 1)) (by norm_num)

private theorem isNonneg_compContinuousLinearMap_of_commutesWithI
    (α : EuclideanSpace ℂ (Fin n) [⋀^Fin 2]→L[ℝ] ℝ) (hα : α.IsNonneg)
    (A : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n))
    (hA : ∀ v, A (Complex.I • v) = Complex.I • A v) :
    (α.compContinuousLinearMap A).IsNonneg := by
  have hmap (u v : EuclideanSpace ℂ (Fin n)) : A ∘ ![u, v] = ![A u, A v] := by
    funext i
    fin_cases i <;> simp
  constructor
  · intro u v
    change α (A ∘ ![Complex.I • u, Complex.I • v]) = α (A ∘ ![u, v])
    rw [hmap, hmap, hA u, hA v]
    exact hα.1 (A u) (A v)
  · intro v
    change 0 ≤ α (A ∘ ![v, Complex.I • v])
    rw [hmap, hA v]
    exact hα.2 (A v)

end

private theorem chartTransition_commutesWithI
    (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    let y := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z
    ∀ v : EuclideanSpace ℂ (Fin n),
      tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y
      (Complex.I • v) = Complex.I •
        tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y v := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  have hOverlap : y ∈ e.source ∩ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    ⟨e.map_target hz, mem_extChartAt_source y⟩
  dsimp only
  intro v
  exact tangentCoordChange_I_smul hOverlap v

private theorem chartRep_isNonneg (β : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hβ : ∀ y, (β y).IsNonneg) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (β.chartRep x z).IsNonneg := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  let A := tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y
  have hA := chartTransition_commutesWithI x hz
  change ((β y).compContinuousLinearMap A).IsNonneg
  exact isNonneg_compContinuousLinearMap_of_commutesWithI (β y) (hβ y) A hA


/-- The `C⁰`, `C²`, and `C³` inputs give a uniform `C^{2,α}` bound on each compact piece of a
chart. This is the initial estimate for `SchauderStep.exists_uniform_chart_holder_bound_succ`.
-/
theorem exists_uniform_chart_holder_bound_two (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : ∀ k, HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) k 0 (Prod.fst '' S))
    {K Λ : ℝ} (hφ : ∀ p ∈ S, ∀ x, |p.2 x| ≤ K)
    (hΛ : ∀ p ∈ S, ∀ x, relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ Λ)
    (hC3 : ∀ (x₀ : M) (K' : Set (EuclideanSpace ℂ (Fin n))), IsCompact K' →
      K' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target →
      ∃ C : ℝ, ∀ p ∈ S, ∀ z ∈ K',
        ‖fderiv ℝ (ddbar (p.2 ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ C)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (x : M) (K' : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K')
    (hKt : K' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ C : ℝ≥0, ∀ p ∈ S,
      HolderBoundOn 2 α C K' (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) := by
  classical
  have complexEllipticOp_one_eq_ddbar_sum {u : EuclideanSpace ℂ (Fin n) → ℝ}
      (z : EuclideanSpace ℂ (Fin n)) :
      complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) u z =
        (∑ j, ddbar u z ![EuclideanSpace.single j 1,
          Complex.I • EuclideanSpace.single j 1]) / 2 := by
    change RCLike.re (((1 : Matrix (Fin n) (Fin n) ℂ) * complexHessian u z).trace) = _
    rw [Matrix.one_mul, Matrix.trace]
    change (∑ j, (complexHessian u z).diag j).re = _
    rw [Complex.re_sum]
    have hdiag (j : Fin n) : RCLike.re (complexHessian u z j j) =
        ddbar u z ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single j 1] / 2 := by
      change ((ddbar u z).coeffMatrix j j).re = _
      simp [ContinuousAlternatingMap.coeffMatrix]
    calc
      _ = ∑ j, ddbar u z ![EuclideanSpace.single j 1,
            Complex.I • EuclideanSpace.single j 1] / 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hdiag j
      _ = (∑ j, ddbar u z ![EuclideanSpace.single j 1,
            Complex.I • EuclideanSpace.single j 1]) / 2 := by rw [Finset.sum_div]
  have norm_fderiv_complexEllipticOp_one_le
      {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
      (hD : DifferentiableAt ℝ (ddbar u) z) {C : ℝ}
      (hC : ‖fderiv ℝ (ddbar u) z‖ ≤ C) :
      ‖fderiv ℝ (complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) u) z‖ ≤
        (n : ℝ) / 2 * C := by
    let E := EuclideanSpace ℂ (Fin n)
    let ev (j : Fin n) : (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
      let a : E := EuclideanSpace.single j (1 : ℂ)
      ContinuousAlternatingMap.apply ℝ E ℝ ![a, Complex.I • a]
    have hev (j : Fin n) : ‖ev j‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro β
      let a : E := EuclideanSpace.single j (1 : ℂ)
      have ha : ‖a‖ = 1 := by
        change ‖PiLp.single (2 : ENNReal) (β := fun _ : Fin n => ℂ) j (1 : ℂ)‖ = 1
        rw [PiLp.norm_single]
        simp
      have hb : ‖Complex.I • a‖ = 1 := by rw [norm_smul, Complex.norm_I, one_mul, ha]
      change ‖β ![a, Complex.I • a]‖ ≤ 1 * ‖β‖
      calc
        ‖β ![a, Complex.I • a]‖ ≤ ‖β‖ * (‖a‖ * ‖Complex.I • a‖) := by
          simpa [Fin.prod_univ_two] using β.le_opNorm ![a, Complex.I • a]
        _ = ‖β‖ := by rw [ha, hb]; ring
        _ = 1 * ‖β‖ := by ring
    let T : (E [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] ℝ := ∑ j, (1 / 2 : ℝ) • ev j
    have hT : ‖T‖ ≤ (n : ℝ) / 2 := by
      calc
        ‖T‖ ≤ ∑ j, ‖(1 / 2 : ℝ) • ev j‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin n, (1 / 2 : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          calc
            ‖(1 / 2 : ℝ) • ev j‖ = (1 / 2 : ℝ) * ‖ev j‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            _ ≤ 1 / 2 := by nlinarith [hev j]
        _ = (n : ℝ) / 2 := by simp [div_eq_mul_inv]
    have htrace :
        complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) u =
          fun w ↦ T (ddbar u w) := by
      funext w
      rw [complexEllipticOp_one_eq_ddbar_sum]
      calc
        (∑ j, (ddbar u w) ![EuclideanSpace.single j 1,
            Complex.I • EuclideanSpace.single j 1]) / 2 =
            ∑ j, (1 / 2 : ℝ) * (ddbar u w) ![EuclideanSpace.single j 1,
              Complex.I • EuclideanSpace.single j 1] := by
                rw [Finset.sum_div]
                simp [div_eq_mul_inv, mul_comm]
        _ = ∑ j, (ev j) (ddbar u w) * (1 / 2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [ev, mul_comm]
        _ = T (ddbar u w) := by simp [T, smul_eq_mul, mul_comm]
    have hTdiff : DifferentiableAt ℝ T (ddbar u z) := T.differentiableAt
    have hfd : fderiv ℝ
        (complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) u) z =
          T.comp (fderiv ℝ (ddbar u) z) := by
      calc
        _ = fderiv ℝ (T ∘ ddbar u) z := by rw [htrace]; rfl
        _ = T.comp (fderiv ℝ (ddbar u) z) := by
          simpa using (fderiv_comp (f := ddbar u) (g := T) (x := z) hTdiff hD)
    have hCnonneg : 0 ≤ C := (norm_nonneg _).trans hC
    calc
      ‖fderiv ℝ
          (complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) u) z‖ =
          ‖T.comp (fderiv ℝ (ddbar u) z)‖ := by rw [hfd]
      _ ≤ ‖T‖ * ‖fderiv ℝ (ddbar u) z‖ := ContinuousLinearMap.opNorm_comp_le T _
      _ ≤ ((n : ℝ) / 2) * C := mul_le_mul hT hC (norm_nonneg _) (by positivity)
  by_cases hSempty : S = ∅
  · refine ⟨0, ?_⟩
    intro p hp
    simp [hSempty] at hp
  · by_cases hn : n = 0
    · subst n
      have hE : Subsingleton (EuclideanSpace ℂ (Fin 0)) := by infer_instance
      obtain ⟨p₀, hp₀⟩ := Set.nonempty_iff_ne_empty.mpr hSempty
      have hKnonneg : 0 ≤ K := (abs_nonneg (p₀.2 x)).trans (hφ p₀ hp₀ x)
      let C : ℝ≥0 := ⟨K, hKnonneg⟩
      have hC : (C : ℝ) = K := rfl
      refine ⟨C, ?_⟩
      intro p hp
      let χ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin 0)) x
      have hconst : p.2 ∘ χ.symm = fun _ : EuclideanSpace ℂ (Fin 0) =>
          p.2 (χ.symm 0) := by
        funext y
        exact congrArg p.2 (congrArg χ.symm (hE.elim y 0))
      refine ⟨?_, ?_⟩
      · intro j hj z hz
        by_cases hj0 : j = 0
        · subst j
          calc
            ‖iteratedFDeriv ℝ 0 (p.2 ∘ χ.symm) z‖ = |p.2 (χ.symm z)| := by simp
            _ ≤ K := hφ p hp (χ.symm z)
            _ = (C : ℝ) := hC.symm
        · rw [hconst, iteratedFDeriv_const_of_ne hj0]
          simp
      · have hderiv : iteratedFDeriv ℝ 2 (p.2 ∘ χ.symm) = 0 := by
          rw [hconst]
          exact iteratedFDeriv_const_of_ne (by omega) _
        intro z hz w hw
        change edist (iteratedFDeriv ℝ 2 (p.2 ∘ χ.symm) z)
            (iteratedFDeriv ℝ 2 (p.2 ∘ χ.symm) w) ≤ _
        simp [hderiv]
    ·
      let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
      obtain ⟨W, hW, hKW, hWtarget, hWcompact⟩ :=
        exists_open_between_and_isCompact_closure hK
          (isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x) hKt
      obtain ⟨U, hU, hKU, hUW, hUcompact⟩ :=
        exists_open_between_and_isCompact_closure hK hW hKW
      have hKclosed : IsClosed K' := hK.isClosed
      have hKclosure : closure K' = K' := hKclosed.closure_eq
      have hVcompact : IsCompact (closure K') := by simpa [hKclosure] using hK
      have hVU : closure K' ⊆ U := by simpa [hKclosure] using hKU
      have hlap : ∀ p ∈ S, ∀ y,
          |ω₀.laplacian p.2 y| ≤ max (n : ℝ) |Λ - n| := by
        intro p hp y
        have hsplit : relTrace (ω₀ y) (ω₀ y + mddbar n p.2 y) =
            (n : ℝ) + ω₀.laplacian p.2 y := by
          rw [relTrace_add, relTrace_self (ω₀.isPositive y)]
          rfl
        have hupper : (n : ℝ) + ω₀.laplacian p.2 y ≤ Λ := by
          simpa [hsplit] using hΛ p hp y
        have hlower : 0 ≤ (n : ℝ) + ω₀.laplacian p.2 y := by
          rw [← hsplit]
          exact relTrace_nonneg (ω₀.isPositive y) ((hS p hp).2.1.2 y).isNonneg
        rw [abs_le]
        constructor
        · have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          have hnmax : (n : ℝ) ≤ max (n : ℝ) |Λ - n| := le_max_left _ _
          linarith
        · have hΛabs : Λ - n ≤ |Λ - n| := le_abs_self _
          have hLapUpper : ω₀.laplacian p.2 y ≤ Λ - n := by linarith [hupper]
          exact (hLapUpper.trans (hΛabs.trans (le_max_right _ _)))
      have hchartSmooth (p : (M → ℝ) × (M → ℝ)) (hp : p ∈ S) :
          ContDiffOn ℝ ∞ (p.2 ∘ e.symm) e.target := by
        have hglobal : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.2
            Set.univ := contMDiffOn_univ.mpr (hS p hp).2.1.1
        have hchart := hglobal.comp (contMDiffOn_extChartAt_symm x)
          (by intro z hz; simp)
        exact hchart.contDiffOn
      have hUniformUpper : ∀ p ∈ S, ∀ y,
          (Λ • ω₀ y - (ω₀ y + mddbar n p.2 y)).IsNonneg := by
        intro p hp y
        let β := ω₀ y + mddbar n p.2 y
        have hβpos : β.IsPositive := by
          simpa [β] using (hS p hp).2.1.2 y
        have hTrace : relTrace (ω₀ y) β ≤ Λ := by
          simpa [β] using hΛ p hp y
        have hFirst : (relTrace (ω₀ y) β • ω₀ y - β).IsNonneg :=
          ContinuousAlternatingMap.isNonneg_relTrace_smul_sub
            (ω₀.isPositive y) hβpos.isNonneg
        have hωnonneg : (ω₀ y).IsNonneg := (ω₀.isPositive y).isNonneg
        have hSecond : ((Λ - relTrace (ω₀ y) β) • ω₀ y).IsNonneg := by
          refine ⟨hωnonneg.1.smul _, ?_⟩
          intro v
          simpa using mul_nonneg (sub_nonneg.mpr hTrace) (hωnonneg.2 v)
        have hdecomp : Λ • ω₀ y - β =
            (relTrace (ω₀ y) β • ω₀ y - β) +
              (Λ - relTrace (ω₀ y) β) • ω₀ y := by
          module
        rw [hdecomp]
        refine ⟨hFirst.1.add hSecond.1, ?_⟩
        intro v
        exact add_nonneg (hFirst.2 v) (hSecond.2 v)
      have hTraceContinuous :
          ContinuousOn (fun z ↦ RCLike.re ((ω₀.metricInChart x z).trace)) (closure W) := by
        have hsum : ContinuousOn
            (fun z ↦ ∑ i : Fin n, Complex.re (ω₀.metricInChart x z i i)) (closure W) := by
          apply continuousOn_finsetSum Finset.univ
          intro i hi
          exact Complex.continuous_re.continuousOn.comp
            (((ω₀.contDiffOn_metricInChart x i i).continuousOn).mono hWtarget)
            (fun _ _ ↦ Set.mem_univ _)
        have hEq : ∀ z, RCLike.re ((ω₀.metricInChart x z).trace) =
            ∑ i : Fin n, Complex.re (ω₀.metricInChart x z i i) := by
          intro z
          simp [Matrix.trace]
        exact hsum.congr (fun z _ ↦ hEq z)
      obtain ⟨Tref, hTref⟩ := hWcompact.exists_bound_of_continuousOn hTraceContinuous
      let Cbg : ℝ := max 1 Tref
      have hCbg : 0 < Cbg := by dsimp [Cbg]; positivity
      have hbgTraceBounds : ∀ z ∈ closure W,
          0 ≤ RCLike.re ((ω₀.metricInChart x z).trace) ∧
            RCLike.re ((ω₀.metricInChart x z).trace) ≤ Cbg := by
        intro z hz
        have hωchart := chartRep_isNonneg ω₀.toFormField
          (fun y ↦ (ω₀.isPositive y).isNonneg) x (hWtarget hz)
        have hdiag (j : Fin n) :
            0 ≤ ((ω₀.metricInChart x z).diag j).re := by
          simpa [KahlerForm.metricInChart] using
            coeffMatrix_diag_re_nonneg_of_isNonneg (ω₀.toFormField.chartRep x z)
              hωchart j
        have hnonneg : 0 ≤ RCLike.re ((ω₀.metricInChart x z).trace) := by
          have hReTrace : RCLike.re ((ω₀.metricInChart x z).trace) =
              ∑ j, (ω₀.metricInChart x z j j).re := by
            simp [Matrix.trace]
          rw [hReTrace]
          exact Finset.sum_nonneg fun j hj ↦ hdiag j
        have hupper : RCLike.re ((ω₀.metricInChart x z).trace) ≤ Cbg := by
          have habs := hTref z hz
          have hle : RCLike.re ((ω₀.metricInChart x z).trace) ≤
              ‖RCLike.re ((ω₀.metricInChart x z).trace)‖ := by
            calc
              RCLike.re ((ω₀.metricInChart x z).trace) ≤
                  |RCLike.re ((ω₀.metricInChart x z).trace)| := le_abs_self _
              _ = _ := by rw [Real.norm_eq_abs]
          exact hle.trans (habs.trans (le_max_right 1 Tref))
        exact ⟨hnonneg, hupper⟩
      have htraceAbs : ∀ p ∈ S, ∀ z ∈ closure U,
          |RCLike.re (complexHessian (p.2 ∘ e.symm) z).trace| ≤
            max 1 |Λ - 1| * Cbg := by
        intro p hp z hz
        let g := ω₀.metricInChart x z
        let H := complexHessian (p.2 ∘ e.symm) z
        let hpot : ω₀.IsPotential p.2 := (hS p hp).2.1
        let ωφ := ω₀.perturb p.2 hpot
        let β : FormField (EuclideanSpace ℂ (Fin n)) M 2 :=
          Λ • ω₀.toFormField - ωφ.toFormField
        have hzW : z ∈ closure W := subset_closure (hUW hz)
        have hωchart := chartRep_isNonneg ω₀.toFormField
          (fun y ↦ (ω₀.isPositive y).isNonneg) x (hWtarget hzW)
        have hφchart := chartRep_isNonneg ωφ.toFormField
          (fun y ↦ (ωφ.isPositive y).isNonneg) x (hWtarget hzW)
        have hβ : ∀ y, (β y).IsNonneg := by
          intro y
          simpa [β, ωφ, KahlerForm.perturb] using hUniformUpper p hp y
        have hβchart := chartRep_isNonneg β hβ x (hWtarget hzW)
        have hφcoeff : ωφ.metricInChart x z = g + H := by
          exact KahlerForm.metricInChart_perturb hpot x (hWtarget hzW)
        have hFcoeff : (ωφ.toFormField.chartRep x z).coeffMatrix = g + H := by
          change ωφ.metricInChart x z = g + H
          exact hφcoeff
        have hFdiag (j : Fin n) : 0 ≤ ((g + H) j j).re := by
          have hj := coeffMatrix_diag_re_nonneg_of_isNonneg
            (ωφ.toFormField.chartRep x z) hφchart j
          rw [hFcoeff] at hj
          exact hj
        have hβchartEq : β.chartRep x z =
            Λ • ω₀.toFormField.chartRep x z - ωφ.toFormField.chartRep x z := by
          ext v
          simp [β, FormField.chartRep, ContinuousAlternatingMap.compContinuousLinearMap_apply]
        have hβcoeff : (β.chartRep x z).coeffMatrix = Λ • g - (g + H) := by
          rw [hβchartEq, ContinuousAlternatingMap.coeffMatrix_sub,
            ContinuousAlternatingMap.coeffMatrix_smul]
          simp [g, H, KahlerForm.metricInChart, hFcoeff]
        have hUpperDiag (j : Fin n) : 0 ≤ ((Λ • g - (g + H)) j j).re := by
          have hj := coeffMatrix_diag_re_nonneg_of_isNonneg (β.chartRep x z) hβchart j
          rw [hβcoeff] at hj
          exact hj
        let gtr := RCLike.re g.trace
        let htr := RCLike.re H.trace
        let ftr := RCLike.re (g + H).trace
        have hftr : 0 ≤ ftr := by
          have hsum : ftr = ∑ j, ((g + H) j j).re := by
            simp [ftr, Matrix.trace, Complex.re_sum]
          rw [hsum]
          exact Finset.sum_nonneg fun j hj ↦ hFdiag j
        have huppertr : 0 ≤ RCLike.re (Λ • g - (g + H)).trace := by
          have hsum : RCLike.re (Λ • g - (g + H)).trace =
              ∑ j, ((Λ • g - (g + H)) j j).re := by
            simp [Matrix.trace]
          rw [hsum]
          exact Finset.sum_nonneg fun j hj ↦ hUpperDiag j
        have hFtrace : ftr = gtr + htr := by
          simp [ftr, gtr, htr, Matrix.trace_add, Complex.add_re]
        have hUpperTrace :
            RCLike.re (Λ • g - (g + H)).trace = Λ * gtr - ftr := by
          simp [gtr, ftr, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re,
            Complex.mul_re]
        have hgBounds := hbgTraceBounds z hzW
        have hLower : -gtr ≤ htr := by
          calc
            -gtr ≤ ftr - gtr := by linarith
            _ = htr := by rw [hFtrace]; ring
        have hUpper : htr ≤ (Λ - 1) * gtr := by
          have hFupper : ftr ≤ Λ * gtr := by
            rw [hUpperTrace] at huppertr
            linarith
          calc
            htr = ftr - gtr := by rw [hFtrace]; ring
            _ ≤ (Λ - 1) * gtr := by linarith
        let MΛ : ℝ := max 1 |Λ - 1|
        have hMΛ : 1 ≤ MΛ := by dsimp [MΛ]; exact le_max_left _ _
        have hAbsFactor : |Λ - 1| ≤ MΛ := by dsimp [MΛ]; exact le_max_right _ _
        have hBgNonneg : 0 ≤ Cbg := hCbg.le
        have hGNonneg : 0 ≤ gtr := hgBounds.1
        have hGBound : gtr ≤ MΛ * Cbg := by
          calc
            gtr ≤ Cbg := hgBounds.2
            _ = 1 * Cbg := by ring
            _ ≤ MΛ * Cbg := mul_le_mul_of_nonneg_right hMΛ hBgNonneg
        have hLowerAbs : -(MΛ * Cbg) ≤ htr := by linarith
        have hUpperAbs : htr ≤ MΛ * Cbg := by
          calc
            htr ≤ (Λ - 1) * gtr := hUpper
            _ ≤ |Λ - 1| * gtr := by
              exact mul_le_mul_of_nonneg_right (le_abs_self _) hGNonneg
            _ ≤ MΛ * Cbg := by
              calc
                |Λ - 1| * gtr ≤ MΛ * gtr :=
                  mul_le_mul_of_nonneg_right hAbsFactor hGNonneg
                _ ≤ MΛ * Cbg := mul_le_mul_of_nonneg_left hgBounds.2 (by positivity)
        change |htr| ≤ MΛ * Cbg
        rw [abs_le]
        exact ⟨hLowerAbs, hUpperAbs⟩
      let Btrace : ℝ := max 1 |Λ - 1| * Cbg
      have hBtrace : 0 ≤ Btrace := by dsimp [Btrace]; positivity
      let BtraceNN : ℝ≥0 := ⟨Btrace, hBtrace⟩
      have hvalue : ∀ p ∈ S, ∀ z ∈ closure U,
          ‖iteratedFDeriv ℝ 0
            (complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ))
              (p.2 ∘ e.symm)) z‖ ≤ BtraceNN := by
        intro p hp z hz
        have habs := htraceAbs p hp z hz
        have hcomplex : |complexEllipticOp
            (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) (p.2 ∘ e.symm) z| ≤ Btrace := by
          change |RCLike.re (((1 : Matrix (Fin n) (Fin n) ℂ) *
            complexHessian (p.2 ∘ e.symm) z).trace)| ≤ Btrace
          rw [Matrix.one_mul]
          simpa [Btrace] using habs
        rw [norm_iteratedFDeriv_zero]
        change |complexEllipticOp
          (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) (p.2 ∘ e.symm) z| ≤ Btrace
        exact hcomplex
      obtain ⟨C₃, hC₃W⟩ := hC3 x (closure W) hWcompact hWtarget
      have htraceDerivative : ∀ p ∈ S, ∀ z ∈ closure W,
          ‖fderiv ℝ (complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ))
            (p.2 ∘ e.symm)) z‖ ≤ (n : ℝ) / 2 * C₃ := by
        intro p hp z hz
        have hddbar : ContDiffOn ℝ ∞ (ddbar (p.2 ∘ e.symm)) e.target :=
          ContDiffOn.ddbar (isOpen_extChartAt_target x) (hchartSmooth p hp)
        have hD : DifferentiableAt ℝ (ddbar (p.2 ∘ e.symm)) z :=
          (hddbar.contDiffAt ((isOpen_extChartAt_target x).mem_nhds
            (hWtarget hz))).differentiableAt
            (by simp)
        exact norm_fderiv_complexEllipticOp_one_le hD (hC₃W p hp z hz)
      have htraceSmooth (p : (M → ℝ) × (M → ℝ)) (hp : p ∈ S) :
          ContDiffOn ℝ ∞ (fun z ↦ complexEllipticOp
            (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) (p.2 ∘ e.symm) z) e.target := by
        let u : EuclideanSpace ℂ (Fin n) → ℝ := p.2 ∘ e.symm
        have hddbar : ContDiffOn ℝ ∞ (ddbar u) e.target :=
          ContDiffOn.ddbar (isOpen_extChartAt_target x) (hchartSmooth p hp)
        have hentry (j : Fin n) : ContDiffOn ℝ ∞
            (fun z ↦ ddbar u z ![EuclideanSpace.single j 1,
              Complex.I • EuclideanSpace.single j 1]) e.target :=
          (ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
            ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single j 1]).contDiff
              |>.comp_contDiffOn hddbar
        have hsum : ContDiffOn ℝ ∞
            (fun z ↦ ∑ j, ddbar u z ![EuclideanSpace.single j 1,
              Complex.I • EuclideanSpace.single j 1]) e.target := by
          apply ContDiffOn.sum
          intro j hj
          exact hentry j
        have hEq : (fun z ↦ complexEllipticOp
              (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) u z) =
              fun z ↦ (∑ j, ddbar u z ![EuclideanSpace.single j 1,
                Complex.I • EuclideanSpace.single j 1]) / 2 := by
          funext z
          exact complexEllipticOp_one_eq_ddbar_sum z
        rw [hEq]
        exact hsum.div_const 2
      have exists_uniform_lipschitzOn_zero (B : ℝ≥0)
          (hvalue : ∀ p ∈ S, ∀ z ∈ closure U,
            ‖iteratedFDeriv ℝ 0
              (fun w ↦ complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ))
                (p.2 ∘ e.symm) w) z‖ ≤ B) :
          ∃ L : ℝ≥0, ∀ p ∈ S,
            LipschitzOnWith L (iteratedFDeriv ℝ 0
              (fun w ↦ complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ))
                (p.2 ∘ e.symm) w)) (closure U) := by
        have hdisj : Disjoint (closure U) Wᶜ := by
          rw [Set.disjoint_left]
          intro z hz hzC
          exact hzC (hUW hz)
        obtain ⟨δ, hδ, hfar⟩ :=
          Metric.exists_pos_forall_lt_edist hUcompact hW.isClosed_compl hdisj
        have hsegmentDist {a b z : EuclideanSpace ℂ (Fin n)}
            (hz : z ∈ segment ℝ a b) : dist a z ≤ dist a b := by
          rw [segment_eq_image] at hz
          rcases hz with ⟨t, ht, rfl⟩
          have hvec : a - ((1 - t) • a + t • b) = t • (a - b) := by module
          rw [dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg ht.1, dist_eq_norm]
          exact mul_le_of_le_one_left (norm_nonneg _) ht.2
        have hsegment (a : EuclideanSpace ℂ (Fin n)) (ha : a ∈ closure U)
            (b : EuclideanSpace ℂ (Fin n)) (hb : b ∈ closure U)
            (hab : dist a b ≤ δ) : segment ℝ a b ⊆ W := by
          intro z hz
          by_contra hzW
          have hfar' := hfar a ha z hzW
          have hnear : edist a z ≤ (δ : ENNReal) := by
            rw [edist_dist, ENNReal.ofReal_le_coe]
            exact (hsegmentDist hz).trans hab
          exact (not_lt_of_ge hnear) hfar'
        let Dreal : ℝ := max 0 ((n : ℝ) / 2 * C₃)
        let D : ℝ≥0 := ⟨Dreal, le_max_left _ _⟩
        let Lfar : ℝ≥0 := 2 * B / δ
        let L : ℝ≥0 := max D Lfar
        refine ⟨L, ?_⟩
        intro p hp
        let f : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
          complexEllipticOp (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ))
            (p.2 ∘ e.symm) z
        apply LipschitzOnWith.of_dist_le_mul
        intro z hz w hw
        by_cases hclose : dist z w ≤ δ
        · have hLipSeg : LipschitzOnWith D (iteratedFDeriv ℝ 0 f) (segment ℝ z w) := by
            apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
            · intro y hy
              have hyW : y ∈ W := hsegment z hz w hw hclose hy
              have hyT : y ∈ e.target := hWtarget (subset_closure hyW)
              exact (htraceSmooth p hp).contDiffAt
                ((isOpen_extChartAt_target x).mem_nhds hyT) |>.differentiableAt_iteratedFDeriv
                  (by norm_num)
            · intro y hy
              have hyW : y ∈ W := hsegment z hz w hw hclose hy
              have hyC : y ∈ closure W := subset_closure hyW
              have hderiv := htraceDerivative p hp y hyC
              have hreal : ‖fderiv ℝ (iteratedFDeriv ℝ 0 f) y‖ ≤ Dreal := by
                rw [norm_fderiv_iteratedFDeriv]
                have hiter : ‖iteratedFDeriv ℝ 1 f y‖ ≤ (n : ℝ) / 2 * C₃ := by
                  simpa [f] using hderiv
                exact hiter.trans (le_max_right _ _)
              exact_mod_cast hreal
            · exact convex_segment z w
          have hseg := (lipschitzOnWith_iff_dist_le_mul.mp hLipSeg) z
            (left_mem_segment ℝ z w) w (right_mem_segment ℝ z w)
          simpa [f] using calc
            dist (iteratedFDeriv ℝ 0 f z) (iteratedFDeriv ℝ 0 f w) ≤
                (D : ℝ) * dist z w := hseg
            _ ≤ (L : ℝ) * dist z w :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left D Lfar) dist_nonneg
        · have hfarDist : (δ : ℝ) ≤ dist z w := le_of_not_ge hclose
          have hzval := hvalue p hp z hz
          have hwval := hvalue p hp w hw
          have hratio : 2 * (B : ℝ) = (↑Lfar : ℝ) * (δ : ℝ) := by
            simp [Lfar, NNReal.coe_div, NNReal.coe_mul]
            field_simp [ne_of_gt (NNReal.coe_pos.mpr hδ)]
          calc
            dist (iteratedFDeriv ℝ 0 f z) (iteratedFDeriv ℝ 0 f w) ≤
                ‖iteratedFDeriv ℝ 0 f z‖ + ‖iteratedFDeriv ℝ 0 f w‖ :=
                  dist_le_norm_add_norm _ _
            _ ≤ (B : ℝ) + B := add_le_add hzval hwval
            _ = 2 * (B : ℝ) := by ring
            _ = (↑Lfar : ℝ) * (δ : ℝ) := hratio
            _ ≤ (↑Lfar : ℝ) * dist z w :=
              mul_le_mul_of_nonneg_left hfarDist (by positivity)
            _ ≤ (L : ℝ) * dist z w :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_right D Lfar) dist_nonneg
      obtain ⟨L, hLip⟩ := exists_uniform_lipschitzOn_zero BtraceNN hvalue
      let K₁ : ℝ≥0 := max BtraceNN
        (L * (Metric.ediam (closure U)).toNNReal ^ ((1 : ℝ) - α))
      have htraceHolder : ∀ p ∈ S, HolderBoundOn 0 α K₁ (closure U)
          (fun z ↦ complexEllipticOp
            (fun _ ↦ (1 : Matrix (Fin n) (Fin n) ℂ)) (p.2 ∘ e.symm) z) := by
        intro p hp
        have h := holderBoundOn_zero_of_lipschitzOnWith hUcompact
          (hvalue p hp) (hLip p hp) α (by exact_mod_cast le_of_lt hα₁)
        simpa [K₁] using h
      let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
        fun _ ↦ 1
      have hAHolder : ∀ j l, HolderBoundOn 0 α 1 U
          (fun z ↦ A z j l) := by
        intro j l
        let c : ℂ := if j = l then 1 else 0
        have hfun : (fun z ↦ A z j l) = fun _ ↦ c := by
          funext z
          simp [A, c, Matrix.one_apply]
        rw [hfun]
        unfold HolderBoundOn
        constructor
        · intro k hk z hz
          have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
          subst k
          rw [norm_iteratedFDeriv_zero]
          by_cases h : j = l <;> simp [c, h]
        · intro z hz w hw
          have hEq : iteratedFDeriv ℝ 0 (fun _ : EuclideanSpace ℂ (Fin n) ↦ c) z =
              iteratedFDeriv ℝ 0 (fun _ : EuclideanSpace ℂ (Fin n) ↦ c) w := by
            rw [iteratedFDeriv_zero_eq_comp]
            rfl
          rw [hEq]
          simp
      obtain ⟨C, hSchauder⟩ := hSch.holderBoundOn_of_contDiffOn
        0 α hα₀ hα₁ 1 1 (by norm_num) U K' hU hVcompact hVU
      refine ⟨C * (K₁ + max 1 (‖K‖₊)), ?_⟩
      intro p hp
      let u : EuclideanSpace ℂ (Fin n) → ℝ := p.2 ∘ e.symm
      have hu : ContDiffOn ℝ ∞ u U := (hchartSmooth p hp).mono
        (subset_trans (subset_closure : U ⊆ closure U)
          (hUW.trans (subset_closure.trans hWtarget)))
      have huBound : ∀ z ∈ U, |u z| ≤ max 1 (‖K‖₊) := by
        intro z hz
        have h := hφ p hp (e.symm z)
        dsimp [u]
        calc
          |p.2 (e.symm z)| ≤ K := h
          _ ≤ |K| := le_abs_self _
          _ = ‖K‖₊ := by simp [Real.norm_eq_abs]
          _ ≤ (max 1 (‖K‖₊ : ℝ≥0) : ℝ) := by exact_mod_cast le_max_right 1 (‖K‖₊)
      have hRhs : HolderBoundOn 0 α K₁ U (complexEllipticOp A u) := by
        have h := (htraceHolder p hp).mono_set (subset_closure : U ⊆ closure U)
        simpa [A, u] using h
      have hresult := hSchauder A u (by
        intro j l
        have hconst : ContDiffOn ℝ ∞
            (fun _ : EuclideanSpace ℂ (Fin n) ↦ if j = l then (1 : ℂ) else 0) U :=
          contDiffOn_const
        simpa [A, Matrix.one_apply] using hconst) hu
        (isUniformlyEllipticOn_one U) hAHolder (max 1 (‖K‖₊)) K₁ hRhs huBound
      simpa [u, e] using hresult

end KahlerForm
