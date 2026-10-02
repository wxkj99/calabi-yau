module

public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderFirstGain
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderInductionStep.FiniteSchauderData
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderInductionStep.DirectionalHessianJets
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderInductionStep.InverseHolderJets
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.SchauderInductionStep.TraceForcingJets

/-!
# Higher-order Schauder induction step

Once the potential has at least three derivatives, its first derivatives are `C²` and can serve as
Schauder inputs.  Differentiate the chartwise log-determinant equation, apply interior Schauder to
these now-`C²` derivatives on nested domains, and identify the derivative limits.  Iterating the
`C^k` to `C^{k+1}` step for `k ≥ 3` supplies the finite-order tower.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology ComplexOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartFirstDerivative_contDiffOn_pred
    {φ : M → ℝ} {k : ℕ} (hk : 3 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ)
    (x : M) (v : EuclideanSpace ℂ (Fin n)) :
    ContDiffOn ℝ (k - 1)
      (fun z ↦ fderiv ℝ
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hφon : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ Set.univ :=
    contMDiffOn_univ.mpr hregular
  have hφchart : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k
      (φ ∘ e.symm) e.target := by
    exact hφon.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
  have hφchart' : ContDiffOn ℝ k (φ ∘ e.symm) e.target := hφchart.contDiffOn
  have hk' : (↑(k - 1) : ℕ∞ω) + 1 ≤ k := by
    exact_mod_cast (show k - 1 + 1 ≤ k by omega)
  have hfd : ContDiffOn ℝ (k - 1) (fderiv ℝ (φ ∘ e.symm)) e.target :=
    hφchart'.fderiv_of_isOpen (isOpen_extChartAt_target x) hk'
  have hv : ContDiffOn ℝ (k - 1) (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) e.target :=
    contDiffOn_const
  exact hfd.clm_apply hv

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartFirstDerivative_locally_bounded
    {φ : M → ℝ} {k : ℕ} (hk : 3 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ)
    (x : M) (z₀ v : EuclideanSpace ℂ (Fin n))
    (hz₀ : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ U : Set (EuclideanSpace ℂ (Fin n)), ∃ K₀ : ℝ≥0,
      IsOpen U ∧ IsCompact (closure U) ∧
        closure U ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target ∧
          z₀ ∈ U ∧
            ∀ w ∈ U, |fderiv ℝ
              (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w v| ≤ K₀ := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let u := fun w ↦ fderiv ℝ (φ ∘ e.symm) w v
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target x) z₀ hz₀
  have hclosed : Metric.closedBall z₀ (R / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (by linarith : R / 2 < R)).trans hball
  have huc : ContinuousOn u (Metric.closedBall z₀ (R / 2)) :=
    (chartFirstDerivative_contDiffOn_pred hk hregular x v).continuousOn.mono hclosed
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ (R / 2)).exists_bound_of_continuousOn huc
  refine ⟨Metric.ball z₀ (R / 2), C.toNNReal, Metric.isOpen_ball,
    (isCompact_closedBall z₀ (R / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall,
    Metric.closure_ball_subset_closedBall.trans hclosed,
    Metric.mem_ball_self (by linarith), ?_⟩
  intro w hw
  have hnorm := hC w (Metric.ball_subset_closedBall hw)
  have habs : |u w| ≤ C := by simpa only [Real.norm_eq_abs] using hnorm
  exact habs.trans (Real.le_coe_toNNReal C)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem contMDiff_succ_of_local_chart_directional_derivatives
    {φ : M → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ)
    (hgain : ∀ (x : M) (z₀ v : EuclideanSpace ℂ (Fin n)),
      z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target →
      ∃ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W ∧ z₀ ∈ W ∧
        ContDiffOn ℝ k
          (fun z ↦ fderiv ℝ
            (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v) W) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) (k + 1) φ := by
  classical
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ((k : ℕ∞ω) + 1) M :=
    IsManifold.of_le (n := ∞) (by
      change ((k + 1 : ℕ) : ℕ∞ω) ≤ ∞
      exact ENat.LEInfty.out)
  have hlocal (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) (k + 1) φ U := by
    let E := EuclideanSpace ℂ (Fin n)
    let e := extChartAt 𝓘(ℝ, E) x
    let f : E → ℝ := φ ∘ e.symm
    let ι := Module.Basis.ofVectorSpaceIndex ℝ E
    let b : Module.Basis ι ℝ E := Module.Basis.ofVectorSpace ℝ E
    have hxSource : x ∈ e.source := mem_extChartAt_source x
    have hzTarget : e x ∈ e.target := e.map_source hxSource
    let Wj : ι → Set E := fun j ↦ Classical.choose (hgain x (e x) (b j) hzTarget)
    have hWj (j : ι) : IsOpen (Wj j) ∧ e x ∈ Wj j ∧
        ContDiffOn ℝ k (fun z ↦ fderiv ℝ f z (b j)) (Wj j) := by
      simpa [Wj, f, e] using Classical.choose_spec (hgain x (e x) (b j) hzTarget)
    let W : Set E := e.target ∩ ⋂ j : ι, Wj j
    have hWopen : IsOpen W :=
      (isOpen_extChartAt_target x).inter (isOpen_iInter_of_finite fun j ↦ (hWj j).1)
    have hzW : e x ∈ W := ⟨hzTarget, Set.mem_iInter.mpr fun j ↦ (hWj j).2.1⟩
    have hWtarget : W ⊆ e.target := Set.inter_subset_left
    have hDcoord (j : ι) : ContDiffOn ℝ k (fun z ↦ fderiv ℝ f z (b j)) W :=
      (hWj j).2.2.mono (fun z hz ↦ Set.mem_iInter.mp hz.2 j)
    let eLin : (E →L[ℝ] ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).symm.trans
        (b.constr ℝ).symm
    let ev : (E →L[ℝ] ℝ) ≃L[ℝ] (ι → ℝ) := eLin.toContinuousLinearEquiv
    have heval (z : E) (j : ι) : ev (fderiv ℝ f z) j = fderiv ℝ f z (b j) := by
      simp [ev, eLin, LinearMap.toContinuousLinearMap, Module.Basis.constr_symm_apply]
    have hcoords : ContDiffOn ℝ k (fun z ↦ ev (fderiv ℝ f z)) W := by
      apply contDiffOn_pi.2
      intro j
      exact (hDcoord j).congr fun z _ ↦ (heval z j).symm
    have hFderiv : ContDiffOn ℝ k (fderiv ℝ f) W := by
      have hcomp := ev.symm.toContinuousLinearMap.contDiff.contDiffOn.comp hcoords
        (Set.mapsTo_univ _ _)
      simpa [ev, Function.comp_def] using hcomp
    have hchart : ContDiffOn ℝ k f e.target := by
      have hφon : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) k φ Set.univ :=
        contMDiffOn_univ.mpr hregular
      exact (hφon.comp (contMDiffOn_extChartAt_symm x)
        (by intro z hz; simp)).contDiffOn
    have hfdiff : DifferentiableOn ℝ f W := by
      intro z hz
      exact (((hchart z (hWtarget hz)).contDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (hWtarget hz))).differentiableAt
          (by exact_mod_cast (show k ≠ 0 by omega))).differentiableWithinAt
    have hchartSucc : ContDiffOn ℝ (k + 1) f W := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hWopen]
      exact ⟨hfdiff, by simp, hFderiv⟩
    let U : Set M := (chartAt E x).source ∩ e ⁻¹' W
    have hUopen : IsOpen U := isOpen_extChartAt_preimage x hWopen
    have hxU : x ∈ U := ⟨mem_chart_source E x, hzW⟩
    have hUsource : U ⊆ e.source := by
      intro y hy
      rw [extChartAt_source (I := 𝓘(ℝ, E)) x]
      exact hy.1
    have himage : e '' U = W := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy.2
      · intro hz
        refine ⟨e.symm z, ⟨?_, ?_⟩, e.right_inv (hWtarget hz)⟩
        · rw [← extChartAt_source (I := 𝓘(ℝ, E)) x]
          exact e.map_target (hWtarget hz)
        · change e (e.symm z) ∈ W
          rw [e.right_inv (hWtarget hz)]
          exact hz
    let et := extChartAt 𝓘(ℝ) (φ x)
    have htarget : ∀ y ∈ U, φ y ∈ et.source := by
      intro y hy
      simp [et, extChartAt, chartAt_self_eq]
    have hreg : ContDiffOn ℝ (k + 1) (et ∘ φ ∘ e.symm) (e '' U) := by
      have heq : et ∘ φ ∘ e.symm = f := by
        funext z
        simp [et, f, extChartAt, chartAt_self_eq]
      rw [heq, himage]
      exact hchartSucc
    refine ⟨U, hUopen, hxU, ?_⟩
    rw [contMDiffOn_iff_of_subset_source' hUsource htarget]
    exact hreg
  exact contMDiff_of_locally_contMDiffOn hlocal

private theorem local_contDiffOn_of_higher_schauder_inputs
    {k : ℕ} (hk : 3 ≤ k) (hSch : InteriorSchauderEstimate n)
    {α lam K K₀ K₁ : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam)
    {U V : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    (hVc : IsCompact (closure V)) (hVU : closure V ⊆ U)
    {z₀ : EuclideanSpace ℂ (Fin n)} (hz₀ : z₀ ∈ V)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (hA : ∀ j l, ContDiffOn ℝ (k - 2 : ℕ) (fun z ↦ A z j l) U)
    (hu : ContDiffOn ℝ 2 u U)
    (hEll : IsUniformlyEllipticOn A lam U)
    (hAH : ∀ j l, HolderBoundOn (k - 2) α K U (fun z ↦ A z j l))
    (hLu : ContDiffOn ℝ (k - 2 : ℕ) (complexEllipticOp A u) U)
    (hLuH : HolderBoundOn (k - 2) α K₁ U (complexEllipticOp A u))
    (huB : ∀ z ∈ U, |u z| ≤ K₀) :
    ∃ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W ∧ z₀ ∈ W ∧
      ContDiffOn ℝ k u W := by
  obtain ⟨C, hC⟩ := hSch (k - 2) α hα₀ hα₁ lam K hlam U V hU hVc hVU
  have hGain := hC A u hA hu hEll hAH K₀ K₁ hLu hLuH huB
  have horder : k - 2 + 2 = k := by omega
  refine ⟨U, hU, hVU (subset_closure hz₀), ?_⟩
  simpa only [horder] using hGain.1

section

open scoped ComplexOrder Matrix.Norms.Elementwise
open Matrix

private theorem det_contDiffOn_of_finite_entry_jets
    {n r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {B : E → Matrix (Fin n) (Fin n) ℂ}
    (hB : ∀ i j, ContDiffOn ℝ r (fun w ↦ B w i j) U) :
    ContDiffOn ℝ r (fun w ↦ (B w).det) U := by
  simp only [Matrix.det_apply]
  fun_prop

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartMetric_inverse_contDiffOn_pred_two
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    {k : ℕ} (hk : 3 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ)
    (x : M) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let B w := ω₀.metricInChart x w + complexHessian (φ ∘ e.symm) w
    (∀ i j, ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ B w i j) e.target) ∧
    (∀ i j, ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ (B w)⁻¹ i j) e.target) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f := φ ∘ e.symm
  let B w := ω₀.metricInChart x w + complexHessian f w
  have hU : IsOpen e.target := isOpen_extChartAt_target x
  have hf : ContDiffOn ℝ k f e.target := by
    have h := (contMDiffOn_univ.mpr hregular).comp
      (contMDiffOn_extChartAt_symm x) (by intro w hw; simp)
    exact h.contDiffOn
  have hfd : ContDiffOn ℝ (k - 1 : ℕ) (fderiv ℝ f) e.target :=
    hf.fderiv_of_isOpen hU (by
      exact_mod_cast (show k - 1 + 1 ≤ k by omega))
  have hfdd : ContDiffOn ℝ (k - 2 : ℕ) (fderiv ℝ (fderiv ℝ f)) e.target :=
    hfd.fderiv_of_isOpen hU (by
      exact_mod_cast (show k - 2 + 1 ≤ k - 1 by omega))
  have heval (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ (k - 2 : ℕ) (fun z ↦ fderiv ℝ (fderiv ℝ f) z v w) e.target :=
    (hfdd.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hHess (i j : Fin n) :
      ContDiffOn ℝ (k - 2 : ℕ) (fun z ↦ complexHessian f z i j) e.target := by
    have hFormula : ContDiffOn ℝ (k - 2 : ℕ) (fun z ↦
        ((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) : ℂ) +
          fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single i 1)
            (Complex.I • EuclideanSpace.single j 1) +
          Complex.I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single i 1)
            (Complex.I • EuclideanSpace.single j 1) -
          fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single i 1)
            (EuclideanSpace.single j 1))) / 4) e.target := by
      simp only [← Complex.ofRealCLM_apply]
      fun_prop
    apply hFormula.congr
    intro z hz
    rw [complexHessian_apply
      ((hf.contDiffAt (hU.mem_nhds hz)).of_le (by
        exact_mod_cast (show 2 ≤ k by omega)))]
  have hB (i j : Fin n) : ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ B w i j) e.target :=
    ((ω₀.contDiffOn_metricInChart x i j).of_le
      (WithTop.coe_le_coe.mpr (show (k - 2 : ℕ∞) ≤ ⊤ from le_top))).add (hHess i j)
  have hdet : ∀ w ∈ e.target, (B w).det ≠ 0 := by
    intro w hw
    have hp : (B w).PosDef := Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨(hEquation x w hw).1, fun v hv ↦ RCLike.pos_iff.mpr
        ⟨(hEquation x w hw).2.1 v hv, (hEquation x w hw).1.im_star_dotProduct_mulVec_self v⟩⟩
    have hpos : 0 < RCLike.re (B w).det := (RCLike.pos_iff.mp hp.det_pos).1
    intro hzero
    rw [hzero] at hpos
    norm_num at hpos
  have hdetfun := det_contDiffOn_of_finite_entry_jets hB
  have hinvdet : ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ ((B w).det)⁻¹) e.target :=
    hdetfun.inv hdet
  have hadj (i j : Fin n) :
      ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ (B w).adjugate i j) e.target := by
    have hUpdate (a b : Fin n) : ContDiffOn ℝ (k - 2 : ℕ)
        (fun w ↦ (B w).updateRow j (Pi.single i 1) a b) e.target := by
      by_cases ha : a = j
      · subst a
        by_cases hb : b = i
        · subst b
          simp [Matrix.updateRow_apply]
          exact contDiffOn_const
        · simp [Matrix.updateRow_apply, hb]
          exact contDiffOn_const
      · simp [Matrix.updateRow_apply, ha]
        exact hB a b
    apply (det_contDiffOn_of_finite_entry_jets hUpdate).congr
    intro w hw
    exact Matrix.adjugate_apply (B w) i j
  refine ⟨hB, ?_⟩
  intro i j
  have hEq : (fun w ↦ (B w)⁻¹ i j) =
      fun w ↦ ((B w).det)⁻¹ * (B w).adjugate i j := by
    funext w
    rw [Matrix.inv_def]
    simp [Matrix.smul_apply, Ring.inverse_eq_inv]
  rw [hEq]
  exact hinvdet.mul (hadj i j)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartDirectionalForcing_contDiffOn_of_inverse_entries
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    {k : ℕ} (x : M)
    (hA : ∀ i j, ContDiffOn ℝ (k - 2 : ℕ)
      (fun w ↦ (ω₀.metricInChart x w +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w)⁻¹ i j)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let g := ω₀.metricInChart x
    let A w := (g w + complexHessian (φ ∘ e.symm) w)⁻¹
    ContDiffOn ℝ (k - 2 : ℕ)
      (fun w ↦ fderiv ℝ (fun z ↦ G (e.symm z) + Real.log (RCLike.re (g z).det)) w v -
        RCLike.re (A w * fderiv ℝ g w v).trace) e.target := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let g := ω₀.metricInChart x
  let A w := (g w + complexHessian (φ ∘ e.symm) w)⁻¹
  let H w := G (e.symm w) + Real.log (RCLike.re (g w).det)
  have hW : IsOpen e.target := isOpen_extChartAt_target x
  have hg : ContDiffOn ℝ ∞ g e.target :=
    contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr fun j ↦ ω₀.contDiffOn_metricInChart x i j
  have hdet : ContDiffOn ℝ ∞ (fun w ↦ (g w).det) e.target := by
    simp only [Matrix.det_apply]
    fun_prop
  have hlog : ContDiffOn ℝ ∞ (fun w ↦ Real.log (RCLike.re (g w).det)) e.target := by
    apply (Complex.reCLM.contDiff.comp_contDiffOn hdet).log
    intro w hw
    exact ne_of_gt ((RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hw).det_pos).1)
  have hGc : ContDiffOn ℝ ∞ (G ∘ e.symm) e.target := by
    exact ((contMDiffOn_univ.mpr hG).comp (contMDiffOn_extChartAt_symm x)
      (by intro w hw; simp)).contDiffOn
  have hH : ContDiffOn ℝ ∞ H e.target := hGc.add hlog
  have hHd : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ H w v) e.target :=
    (hH.fderiv_of_isOpen hW (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffOn_const
  have hgd : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ g w v) e.target :=
    (hg.fderiv_of_isOpen hW (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiffOn_const
  have hgdentry (i j : Fin n) :
      ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ fderiv ℝ g w v i j) e.target :=
    ((contDiffOn_pi.mp (contDiffOn_pi.mp hgd i)) j).of_le (WithTop.coe_le_coe.mpr le_top)
  have htrace : ContDiffOn ℝ (k - 2 : ℕ)
      (fun w ↦ RCLike.re (A w * fderiv ℝ g w v).trace) e.target := by
    have hsum : ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦
        ∑ i, ∑ j, Complex.reCLM (A w i j * fderiv ℝ g w v j i)) e.target := by
      apply ContDiffOn.sum
      intro i hi
      apply ContDiffOn.sum
      intro j hj
      exact Complex.reCLM.contDiff.comp_contDiffOn ((hA i j).mul (hgdentry j i))
    apply hsum.congr
    intro w hw
    simp [Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]
  exact (hHd.of_le (WithTop.coe_le_coe.mpr le_top)).sub htrace

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartLogDetEquation_linearized_finite
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    {k : ℕ} (hk : 3 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ)
    (x : M) (z v : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hComm : fderiv ℝ
      (complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)) z v =
        complexHessian (fun w ↦ fderiv ℝ
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) w v) z) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let f := φ ∘ e.symm
    let g := ω₀.metricInChart x
    let B w := g w + complexHessian f w
    complexEllipticOp (fun w ↦ (B w)⁻¹) (fun w ↦ fderiv ℝ f w v) z =
      fderiv ℝ (fun w ↦ G (e.symm w) + Real.log (RCLike.re (g w).det)) z v -
        RCLike.re ((B z)⁻¹ * fderiv ℝ g z v).trace := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f := φ ∘ e.symm
  let g := ω₀.metricInChart x
  let B w := g w + complexHessian f w
  let H w := G (e.symm w) + Real.log (RCLike.re (g w).det)
  let L : Matrix (Fin n) (Fin n) ℂ → ℝ := fun C ↦ Real.log (RCLike.re C.det)
  have hW : IsOpen e.target := isOpen_extChartAt_target x
  have hg : ContDiffOn ℝ ∞ g e.target :=
    contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr fun j ↦ ω₀.contDiffOn_metricInChart x i j
  have hgdiff : DifferentiableAt ℝ g z :=
    (hg.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
  have hentries := (chartMetric_inverse_contDiffOn_pred_two ω₀ hEquation hk hregular x).1
  have hBdiff : DifferentiableAt ℝ B z := by
    apply differentiableAt_pi.mpr
    intro i
    apply differentiableAt_pi.mpr
    intro j
    exact ((hentries i j).contDiffAt (hW.mem_nhds hz)).differentiableAt
      (by exact_mod_cast (show k - 2 ≠ 0 by omega))
  have hHessdiff : DifferentiableAt ℝ (complexHessian f) z := by
    have heq : (fun w ↦ B w - g w) = complexHessian f := by
      funext w
      simp only [B, add_sub_cancel_left]
    rw [← heq]
    exact hBdiff.sub hgdiff
  have hBderiv : fderiv ℝ B z v =
      fderiv ℝ g z v + complexHessian (fun w ↦ fderiv ℝ f w v) z := by
    have hd : fderiv ℝ B z = fderiv ℝ g z + fderiv ℝ (complexHessian f) z :=
      (hgdiff.hasFDerivAt.add hHessdiff.hasFDerivAt).fderiv
    rw [hd]
    simp only [_root_.add_apply]
    exact congrArg (fun T ↦ fderiv ℝ g z v + T) hComm
  have hp : (B z).PosDef := Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨(hEquation x z hz).1, fun w hw ↦ RCLike.pos_iff.mpr
      ⟨(hEquation x z hz).2.1 w hw,
        (hEquation x z hz).1.im_star_dotProduct_mulVec_self w⟩⟩
  have hLdiff : DifferentiableAt ℝ L (B z) :=
    hp.contDiffAt_log_det.differentiableAt (by simp)
  have hEq : (L ∘ B) =ᶠ[𝓝 z] H := by
    filter_upwards [hW.mem_nhds hz] with w hw
    exact (hEquation x w hw).2.2
  have hchain : fderiv ℝ H z v = RCLike.re ((B z)⁻¹ * fderiv ℝ B z v).trace := by
    rw [← hEq.fderiv_eq, fderiv_comp z hLdiff hBdiff]
    simp only [ContinuousLinearMap.comp_apply]
    exact hp.fderiv_log_det_apply _
  change complexEllipticOp (fun w ↦ (B w)⁻¹) (fun w ↦ fderiv ℝ f w v) z =
    fderiv ℝ H z v - RCLike.re ((B z)⁻¹ * fderiv ℝ g z v).trace
  rw [hchain, hBderiv, Matrix.mul_add, Matrix.trace_add, map_add]
  simp only [complexEllipticOp]
  ring

end

section

open Matrix Filter

private theorem induction_complexHessian_entry_contDiffAt_one {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (j k : Fin n) :
    ContDiffAt ℝ 1 (fun x ↦ complexHessian u x j k) z := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z :=
    hu.fderiv_right (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) z :=
    hD1.fderiv_right (by norm_num)
  have hQ (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x v w) z := by
    have hv : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) z := contDiffAt_const
    have hw : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ w) z := contDiffAt_const
    exact (hD2.clm_apply hv).clm_apply hw
  let q : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦
    ((fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) : ℂ) +
      fderiv ℝ (fderiv ℝ u) x (Complex.I • EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1) +
      Complex.I * (fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single j 1)
        (Complex.I • EuclideanSpace.single k 1) -
      fderiv ℝ (fderiv ℝ u) x (Complex.I • EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1))) / 4
  have hq : ContDiffAt ℝ 1 q z := by
    dsimp [q]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x :=
    hu.eventually (by norm_num)
  have hEq : (fun x ↦ complexHessian u x j k) =ᶠ[𝓝 z] q := by
    filter_upwards [hnear] with x hx
    exact complexHessian_apply (hx.of_le (by norm_num)) j k
  exact hq.congr_of_eventuallyEq hEq

private theorem induction_complexHessian_differentiableAt {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) : DifferentiableAt ℝ (complexHessian u) z := by
  change DifferentiableAt ℝ (fun x i j ↦ complexHessian u x i j) z
  rw [differentiableAt_pi]
  intro j
  rw [differentiableAt_pi]
  intro k
  exact (induction_complexHessian_entry_contDiffAt_one hu j k).differentiableAt (by norm_num)

private theorem induction_fderiv_ofRealCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z : E} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun x ↦ (f x : ℂ)) z = (Complex.ofRealCLM).comp (fderiv ℝ f z) := by
  change fderiv ℝ (fun x ↦ Complex.ofRealCLM (f x)) z = _
  rw [fderiv_clm_apply (differentiableAt_const Complex.ofRealCLM) hf]
  simp

private theorem induction_fderiv_gradient_eval {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (b c : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun x ↦ fderiv ℝ u x c) z b =
      fderiv ℝ (fderiv ℝ u) z b c := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) z := hD1.differentiableAt (by norm_num)
  rw [fderiv_clm_apply hdiff (differentiableAt_const c)]
  simp

private theorem induction_secondDerivative_directional_eq {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z e : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (b c : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun x ↦ fderiv ℝ u x e)) z b c =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x c e) z b := by
  let du : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦ fderiv ℝ u x e
  have hDu : ContDiffAt ℝ 2 du z := by
    dsimp [du]
    exact (hu.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hDdu : ContDiffAt ℝ 1 (fderiv ℝ du) z := hDu.fderiv_right (by norm_num)
  have hDiffDdu : DifferentiableAt ℝ (fderiv ℝ du) z := hDdu.differentiableAt (by norm_num)
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEq : (fun x ↦ fderiv ℝ du x c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ (fderiv ℝ u) x c e := by
    filter_upwards [hnear] with x hx
    exact induction_fderiv_gradient_eval hx c e
  have hEval : fderiv ℝ (fun x ↦ fderiv ℝ du x c) z b =
      fderiv ℝ (fderiv ℝ du) z b c := by
    rw [fderiv_clm_apply hDiffDdu (differentiableAt_const c)]
    simp
  calc
    fderiv ℝ (fderiv ℝ du) z b c = fderiv ℝ (fun x ↦ fderiv ℝ du x c) z b := hEval.symm
    _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x c e) z b := by
      exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L b)
        (hEq.fderiv_eq (𝕜 := ℝ))

private theorem induction_thirdDerivative_swap_hessian_slots {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (a b c : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z a =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x c b) z a := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) z :=
    hD1.fderiv_right (by norm_num)
  have hbc : ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z := by
    have hb : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ b) z := contDiffAt_const
    have hc : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ c) z := contDiffAt_const
    exact (hD2.clm_apply hb).clm_apply hc
  have hcb : ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x c b) z := by
    have hb : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ b) z := contDiffAt_const
    have hc : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ c) z := contDiffAt_const
    exact (hD2.clm_apply hc).clm_apply hb
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEq : (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ (fderiv ℝ u) x c b := by
    filter_upwards [hnear] with x hx
    have hx2 : ContDiffAt ℝ 2 u x := hx.of_le (by norm_num)
    exact (hx2.isSymmSndFDerivAt (by norm_num)) b c
  have hderiv := hEq.fderiv_eq (𝕜 := ℝ)
  exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L a) hderiv

private theorem induction_thirdDerivative_swap_outer_hessian_slot {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (a b c : EuclideanSpace ℂ (Fin n)) :
    fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z a =
      fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x a c) z b := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  let g : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦ fderiv ℝ u x c
  have hgc : ContDiffAt ℝ 2 g z := by
    dsimp [g]
    exact hD1.clm_apply contDiffAt_const
  have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
  have hEqB : (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ g x b := by
    filter_upwards [hnear] with x hx
    exact (induction_fderiv_gradient_eval hx b c).symm
  have hEqA : (fun x ↦ fderiv ℝ (fderiv ℝ u) x a c) =ᶠ[𝓝 z]
      fun x ↦ fderiv ℝ g x a := by
    filter_upwards [hnear] with x hx
    exact (induction_fderiv_gradient_eval hx a c).symm
  have hDg : ContDiffAt ℝ 1 (fderiv ℝ g) z := hgc.fderiv_right (by norm_num)
  have hDgDiff : DifferentiableAt ℝ (fderiv ℝ g) z := hDg.differentiableAt (by norm_num)
  have hEvalB : fderiv ℝ (fun x ↦ fderiv ℝ g x b) z a =
      fderiv ℝ (fderiv ℝ g) z a b := by
    rw [fderiv_clm_apply hDgDiff (differentiableAt_const b)]
    simp
  have hEvalA : fderiv ℝ (fun x ↦ fderiv ℝ g x a) z b =
      fderiv ℝ (fderiv ℝ g) z b a := by
    rw [fderiv_clm_apply hDgDiff (differentiableAt_const a)]
    simp
  have hsymm := hgc.isSymmSndFDerivAt (by norm_num)
  calc
    fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x b c) z a =
        fderiv ℝ (fun x ↦ fderiv ℝ g x b) z a := by
      exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L a)
        (hEqB.fderiv_eq (𝕜 := ℝ))
    _ = fderiv ℝ (fderiv ℝ g) z a b := hEvalB
    _ = fderiv ℝ (fderiv ℝ g) z b a := hsymm a b
    _ = fderiv ℝ (fun x ↦ fderiv ℝ g x a) z b := hEvalA.symm
    _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x a c) z b := by
      exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L b)
        (hEqA.fderiv_eq (𝕜 := ℝ)).symm

private theorem induction_complexHessian_entry_fderiv_directional {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z e : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) (j k : Fin n) :
    (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k =
      complexHessian (fun w ↦ fderiv ℝ u w e) z j k := by
  have hD1 : ContDiffAt ℝ 2 (fderiv ℝ u) z := hu.fderiv_right (by norm_num)
  have hD2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) z :=
    hD1.fderiv_right (by norm_num)
  have hQ (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffAt ℝ 1 (fun x ↦ fderiv ℝ (fderiv ℝ u) x v w) z := by
    have hv : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) z := contDiffAt_const
    have hw : ContDiffAt ℝ 1 (fun _ : EuclideanSpace ℂ (Fin n) ↦ w) z := contDiffAt_const
    exact (hD2.clm_apply hv).clm_apply hw
  let vj : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let vk : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k 1
  let ivj : EuclideanSpace ℂ (Fin n) := Complex.I • EuclideanSpace.single j 1
  let ivk : EuclideanSpace ℂ (Fin n) := Complex.I • EuclideanSpace.single k 1
  let q₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦
    fderiv ℝ (fderiv ℝ u) x vj vk
  let q₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦
    fderiv ℝ (fderiv ℝ u) x ivj ivk
  let q₃ : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦
    fderiv ℝ (fderiv ℝ u) x vj ivk
  let q₄ : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦
    fderiv ℝ (fderiv ℝ u) x ivj vk
  let s : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦
    (q₁ x : ℂ) + (q₂ x : ℂ) + Complex.I * ((q₃ x : ℂ) - (q₄ x : ℂ))
  let q : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ (1 / 4 : ℝ) • s x
  have hq₁ : ContDiffAt ℝ 1 q₁ z := by
    dsimp [q₁, vj, vk]
    exact hQ _ _
  have hq₂ : ContDiffAt ℝ 1 q₂ z := by
    dsimp [q₂, ivj, ivk]
    exact hQ _ _
  have hq₃ : ContDiffAt ℝ 1 q₃ z := by
    dsimp [q₃, vj, ivk]
    exact hQ _ _
  have hq₄ : ContDiffAt ℝ 1 q₄ z := by
    dsimp [q₄, ivj, vk]
    exact hQ _ _
  have hs : ContDiffAt ℝ 1 s z := by
    dsimp [s]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hq : ContDiffAt ℝ 1 q z := by
    dsimp [q]
    fun_prop
  have hEq : (fun x ↦ complexHessian u x j k) =ᶠ[𝓝 z] q := by
    have hnear : ∀ᶠ x in 𝓝 z, ContDiffAt ℝ 3 u x := hu.eventually (by norm_num)
    filter_upwards [hnear] with x hx
    rw [complexHessian_apply (hx.of_le (by norm_num)) j k]
    dsimp [q, s, q₁, q₂, q₃, q₄, vj, vk, ivj, ivk]
    simp only [Complex.ofReal_div]
    norm_num
    ring_nf
  have hq₁C : ContDiffAt ℝ 1 (fun x ↦ (q₁ x : ℂ)) z := by
    dsimp [q₁]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hq₂C : ContDiffAt ℝ 1 (fun x ↦ (q₂ x : ℂ)) z := by
    dsimp [q₂]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hq₃C : ContDiffAt ℝ 1 (fun x ↦ (q₃ x : ℂ)) z := by
    dsimp [q₃]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hq₄C : ContDiffAt ℝ 1 (fun x ↦ (q₄ x : ℂ)) z := by
    dsimp [q₄]
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hcast₁ : fderiv ℝ (fun x ↦ (q₁ x : ℂ)) z e = (fderiv ℝ q₁ z e : ℂ) := by
    have h := induction_fderiv_ofRealCLM (hq₁.differentiableAt (by norm_num))
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) h
    simpa using he
  have hcast₂ : fderiv ℝ (fun x ↦ (q₂ x : ℂ)) z e = (fderiv ℝ q₂ z e : ℂ) := by
    have h := induction_fderiv_ofRealCLM (hq₂.differentiableAt (by norm_num))
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) h
    simpa using he
  have hcast₃ : fderiv ℝ (fun x ↦ (q₃ x : ℂ)) z e = (fderiv ℝ q₃ z e : ℂ) := by
    have h := induction_fderiv_ofRealCLM (hq₃.differentiableAt (by norm_num))
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) h
    simpa using he
  have hcast₄ : fderiv ℝ (fun x ↦ (q₄ x : ℂ)) z e = (fderiv ℝ q₄ z e : ℂ) := by
    have h := induction_fderiv_ofRealCLM (hq₄.differentiableAt (by norm_num))
    have he := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) h
    simpa using he
  have hsumDiff : DifferentiableAt ℝ (fun x ↦ (q₁ x : ℂ) + (q₂ x : ℂ)) z :=
    (hq₁C.differentiableAt (by norm_num)).add (hq₂C.differentiableAt (by norm_num))
  have hdiffCD : DifferentiableAt ℝ (fun x ↦ (q₃ x : ℂ) - (q₄ x : ℂ)) z :=
    (hq₃C.differentiableAt (by norm_num)).sub (hq₄C.differentiableAt (by norm_num))
  have hprodDiff : DifferentiableAt ℝ
      (fun x ↦ Complex.I * ((q₃ x : ℂ) - (q₄ x : ℂ))) z := hdiffCD.const_mul _
  have hsderiv : fderiv ℝ s z e =
      (fderiv ℝ q₁ z e : ℂ) + (fderiv ℝ q₂ z e : ℂ) +
        Complex.I * ((fderiv ℝ q₃ z e : ℂ) - (fderiv ℝ q₄ z e : ℂ)) := by
    change (fderiv ℝ
      ((fun x ↦ (q₁ x : ℂ) + (q₂ x : ℂ)) +
        fun x ↦ Complex.I * ((q₃ x : ℂ) - (q₄ x : ℂ))) z) e = _
    rw [fderiv_add hsumDiff hprodDiff]
    change (fderiv ℝ
        ((fun x ↦ (q₁ x : ℂ)) + (fun x ↦ (q₂ x : ℂ))) z +
      fderiv ℝ (fun x ↦ Complex.I * ((q₃ x : ℂ) - (q₄ x : ℂ))) z) e = _
    rw [fderiv_add (hq₁C.differentiableAt (by norm_num))
      (hq₂C.differentiableAt (by norm_num))]
    change (fderiv ℝ (fun x ↦ (q₁ x : ℂ)) z +
      fderiv ℝ (fun x ↦ (q₂ x : ℂ)) z +
      fderiv ℝ (fun x ↦ Complex.I *
        ((fun x ↦ (q₃ x : ℂ)) x - (fun x ↦ (q₄ x : ℂ)) x)) z) e = _
    rw [fderiv_const_mul hdiffCD Complex.I]
    change (fderiv ℝ (fun x ↦ (q₁ x : ℂ)) z +
      fderiv ℝ (fun x ↦ (q₂ x : ℂ)) z +
      Complex.I • fderiv ℝ ((fun x ↦ (q₃ x : ℂ)) - (fun x ↦ (q₄ x : ℂ))) z) e = _
    rw [fderiv_sub (hq₃C.differentiableAt (by norm_num))
      (hq₄C.differentiableAt (by norm_num))]
    have hsub_eval : (fderiv ℝ (fun x ↦ (q₃ x : ℂ)) z -
        fderiv ℝ (fun x ↦ (q₄ x : ℂ)) z) e =
        fderiv ℝ (fun x ↦ (q₃ x : ℂ)) z e -
          fderiv ℝ (fun x ↦ (q₄ x : ℂ)) z e := rfl
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [hsub_eval]
    rw [hcast₁, hcast₂, hcast₃, hcast₄]
  have hqderiv : fderiv ℝ q z e = (1 / 4 : ℝ) • fderiv ℝ s z e := by
    change (fderiv ℝ (fun y ↦ (1 / 4 : ℝ) • s y) z) e = _
    rw [fderiv_fun_const_smul (hs.differentiableAt (by norm_num))]
    rfl
  let du : EuclideanSpace ℂ (Fin n) → ℝ := fun x ↦ fderiv ℝ u x e
  have hDu : ContDiffAt ℝ 2 du z := by
    dsimp [du]
    exact hD1.clm_apply contDiffAt_const
  have hq₁third : fderiv ℝ q₁ z e = fderiv ℝ (fderiv ℝ du) z vj vk := by
    calc
      fderiv ℝ q₁ z e = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x vj vk) z e := rfl
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x e vk) z vj :=
        induction_thirdDerivative_swap_outer_hessian_slot hu e vj vk
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x vk e) z vj :=
        induction_thirdDerivative_swap_hessian_slots hu vj e vk
      _ = fderiv ℝ (fderiv ℝ du) z vj vk :=
        (induction_secondDerivative_directional_eq hu vj vk).symm
  have hq₂third : fderiv ℝ q₂ z e = fderiv ℝ (fderiv ℝ du) z ivj ivk := by
    calc
      fderiv ℝ q₂ z e = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x ivj ivk) z e := rfl
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x e ivk) z ivj :=
        induction_thirdDerivative_swap_outer_hessian_slot hu e ivj ivk
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x ivk e) z ivj :=
        induction_thirdDerivative_swap_hessian_slots hu ivj e ivk
      _ = fderiv ℝ (fderiv ℝ du) z ivj ivk :=
        (induction_secondDerivative_directional_eq hu ivj ivk).symm
  have hq₃third : fderiv ℝ q₃ z e = fderiv ℝ (fderiv ℝ du) z vj ivk := by
    calc
      fderiv ℝ q₃ z e = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x vj ivk) z e := rfl
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x e ivk) z vj :=
        induction_thirdDerivative_swap_outer_hessian_slot hu e vj ivk
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x ivk e) z vj :=
        induction_thirdDerivative_swap_hessian_slots hu vj e ivk
      _ = fderiv ℝ (fderiv ℝ du) z vj ivk :=
        (induction_secondDerivative_directional_eq hu vj ivk).symm
  have hq₄third : fderiv ℝ q₄ z e = fderiv ℝ (fderiv ℝ du) z ivj vk := by
    calc
      fderiv ℝ q₄ z e = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x ivj vk) z e := rfl
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x e vk) z ivj :=
        induction_thirdDerivative_swap_outer_hessian_slot hu e ivj vk
      _ = fderiv ℝ (fun x ↦ fderiv ℝ (fderiv ℝ u) x vk e) z ivj :=
        induction_thirdDerivative_swap_hessian_slots hu ivj e vk
      _ = fderiv ℝ (fderiv ℝ du) z ivj vk :=
        (induction_secondDerivative_directional_eq hu ivj vk).symm
  have hright := complexHessian_apply hDu j k
  have hleft : (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k = fderiv ℝ q z e := by
    have hMatDiff : DifferentiableAt ℝ (fun w ↦ complexHessian u w) z :=
      induction_complexHessian_differentiableAt hu
    have hRowDiff (i : Fin n) :
        DifferentiableAt ℝ (fun w l ↦ complexHessian u w i l) z := by
      rw [differentiableAt_pi]
      intro l
      exact (induction_complexHessian_entry_contDiffAt_one hu i l).differentiableAt (by norm_num)
    have hOuter := fderiv_apply hMatDiff j
    have hInner := fderiv_apply (hRowDiff j) k
    have hCoordinate : (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k =
        fderiv ℝ (fun w ↦ complexHessian u w j k) z e := by
      change (fderiv ℝ (complexHessian u) z e) j k = _
      calc
        (fderiv ℝ (fun w ↦ complexHessian u w) z e) j k =
            (fderiv ℝ (fun w ↦ complexHessian u w j) z e) k := by
          have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ]
              (Fin n → ℂ) ↦ L e) hOuter.symm
          have h' := congrArg (fun row : Fin n → ℂ ↦ row k) h
          change ((fderiv ℝ (fun w ↦ complexHessian u w) z e) j) k = _ at h'
          exact h'
        _ = fderiv ℝ (fun w ↦ complexHessian u w j k) z e := by
          have h := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e) hInner.symm
          change (fderiv ℝ (fun w l ↦ complexHessian u w j l) z e) k = _ at h
          exact h
    have hderivEq := congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L e)
      (hEq.fderiv_eq (𝕜 := ℝ))
    exact hCoordinate.trans hderivEq
  have hstep : fderiv ℝ q z e = complexHessian du z j k := by
    rw [hqderiv, hsderiv, hq₁third, hq₂third, hq₃third, hq₄third, hright]
    simp [vj, vk, ivj, ivk, Complex.real_smul]
    norm_num
    ring_nf
  exact hleft.trans hstep

/-- The complex Hessian commutes with a real directional derivative. -/
private theorem induction_complexHessian_fderiv_directional {n : ℕ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {z e : EuclideanSpace ℂ (Fin n)}
    (hu : ContDiffAt ℝ 3 u z) :
    fderiv ℝ (fun w ↦ complexHessian u w) z e =
      complexHessian (fun w ↦ fderiv ℝ u w e) z := by
  ext j k
  exact induction_complexHessian_entry_fderiv_directional hu j k

end

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

/-- The lower pass upgrades directional jets before reconstructing the second-pass inputs. -/
private theorem higher_holder_inputs_of_finite_jets
    {n k : ℕ} (hk : 3 ≤ k) (hSch : InteriorSchauderEstimate n)
    {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    {W : Set (EuclideanSpace ℂ (Fin n))} (hW : IsOpen W)
    (f H : EuclideanSpace ℂ (Fin n) → ℝ)
    (g : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hf : ContDiffOn ℝ k f W)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun w ↦ g w i j) W)
    (hH : ContDiffOn ℝ ∞ H W)
    (hB : ∀ i j, ContDiffOn ℝ (k - 2 : ℕ)
      (fun w ↦ (g w + complexHessian f w) i j) W)
    (hA : ∀ i j, ContDiffOn ℝ (k - 2 : ℕ)
      (fun w ↦ (g w + complexHessian f w)⁻¹ i j) W)
    (hpos : ∀ w ∈ W, (g w + complexHessian f w).PosDef)
    (hd : ∀ v, ContDiffOn ℝ (k - 1 : ℕ) (fun w ↦ fderiv ℝ f w v) W)
    (hQ : ∀ v, ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ fderiv ℝ H w v -
      RCLike.re ((g w + complexHessian f w)⁻¹ * fderiv ℝ g w v).trace) W)
    (hEq : ∀ v, Set.EqOn
      (complexEllipticOp (fun w ↦ (g w + complexHessian f w)⁻¹)
        (fun w ↦ fderiv ℝ f w v))
      (fun w ↦ fderiv ℝ H w v -
        RCLike.re ((g w + complexHessian f w)⁻¹ * fderiv ℝ g w v).trace) W)
    (z₀ v : EuclideanSpace ℂ (Fin n)) (hz : z₀ ∈ W)
    {U₀ : Set (EuclideanSpace ℂ (Fin n))} (hU₀ : IsOpen U₀) (hzU₀ : z₀ ∈ U₀) :
    let A w := (g w + complexHessian f w)⁻¹
    let Q w := fderiv ℝ H w v - RCLike.re (A w * fderiv ℝ g w v).trace
    ∃ U V : Set (EuclideanSpace ℂ (Fin n)), ∃ lam K K₁ : ℝ≥0,
      IsOpen U ∧ U ⊆ U₀ ∧ U ⊆ W ∧ IsCompact (closure V) ∧
      closure V ⊆ U ∧ z₀ ∈ V ∧ 0 < lam ∧ IsUniformlyEllipticOn A lam U ∧
      (∀ i j, HolderBoundOn (k - 2) α K U (fun w ↦ A w i j)) ∧
      HolderBoundOn (k - 2) α K₁ U Q := by
  let B w := g w + complexHessian f w
  let A w := (B w)⁻¹
  let Q (d : EuclideanSpace ℂ (Fin n)) w :=
    fderiv ℝ H w d - RCLike.re (A w * fderiv ℝ g w d).trace
  have hAlow (i j : Fin n) : ContDiffOn ℝ (k - 3 + 1 : ℕ)
      (fun w ↦ A w i j) W :=
    (hA i j).of_le (by exact_mod_cast (show k - 3 + 1 ≤ k - 2 by omega))
  have hQlow (d : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ (k - 3 + 1 : ℕ) (Q d) W :=
    (hQ d).of_le (by exact_mod_cast (show k - 3 + 1 ≤ k - 2 by omega))
  have hu (d : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ 2 (fun w ↦ fderiv ℝ f w d) W :=
    (hd d).of_le (by exact_mod_cast (show 2 ≤ k - 1 by omega))
  have hApos (w) (hw : w ∈ W) : (A w).PosDef := (hpos w hw).inv
  have hfirst : ∀ z ∈ W, ∀ d : EuclideanSpace ℂ (Fin n),
      ∃ V : Set (EuclideanSpace ℂ (Fin n)), ∃ C : ℝ≥0,
        IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        HolderBoundOn (k - 1) α C V (fun w ↦ fderiv ℝ f w d) := by
    intro z hz d
    obtain ⟨U, V, lam, K, K₀, K₁, hU, hV, hUc, hVc, hVU, hUW,
      hzV, hlam, hEll, hAH, hQH, huB⟩ :=
      locally_finite_schauder_data hW hα₀ hα₁ A (Q d)
        (fun w ↦ fderiv ℝ f w d) hAlow hApos (hQlow d) (hu d) z hz
    have hUt : U ⊆ W := subset_closure.trans hUW
    have hEqU := (hEq d).mono hUt
    have hLu : ContDiffOn ℝ (k - 3 : ℕ)
        (complexEllipticOp A (fun w ↦ fderiv ℝ f w d)) U :=
      ((hQ d).of_le (by exact_mod_cast (show k - 3 ≤ k - 2 by omega))).mono hUt
        |>.congr hEqU
    have hLuH := holderBoundOn_congr_of_isOpen hU hEqU hQH
    obtain ⟨C, hC⟩ := hSch (k - 3) α hα₀ hα₁ lam K hlam U V hU hVc hVU
    have hGain := hC A (fun w ↦ fderiv ℝ f w d)
      (fun i j ↦ ((hA i j).of_le
        (by exact_mod_cast (show k - 3 ≤ k - 2 by omega))).mono hUt)
      ((hu d).mono hUt) hEll hAH K₀ K₁ hLu hLuH huB
    refine ⟨V, C * (K₁ + K₀), hV, hzV, subset_closure.trans (hVU.trans hUt), ?_⟩
    simpa only [show k - 3 + 2 = k - 1 by omega] using hGain.2
  obtain ⟨WB, KB, hWB, hzWB, hWBt, hBH⟩ :=
    locally_holder_metric_of_directional_derivatives hk hW hα₀ hα₁ f g hf hg hfirst z₀ hz
  obtain ⟨WI, KI, hWI, hzWI, hWIB, hIH⟩ :=
    locally_holder_matrix_inverse hWB hα₀ hα₁ B
      (fun i j ↦ (hB i j).mono hWBt)
      (fun w hw ↦ (hpos w (hWBt hw)).isUnit) hBH z₀ hzWB
  obtain ⟨UB, VB, lam, KL, K₀, KQ, hUB, hVB, hUBc, hVBc, hVBU, hUBt,
    hzVB, hlam, hEll, hAL, hQL, huB⟩ :=
    locally_finite_schauder_data hW hα₀ hα₁ A (Q v)
      (fun w ↦ fderiv ℝ f w v) hAlow hApos (hQlow v) (hu v) z₀ hz
  let WI' := WI ∩ (UB ∩ U₀)
  have hWI' : IsOpen WI' := hWI.inter (hUB.inter hU₀)
  have hzWI' : z₀ ∈ WI' := ⟨hzWI, hVBU (subset_closure hzVB), hzU₀⟩
  have hWI't : WI' ⊆ W := fun w hw ↦ hWBt (hWIB hw.1)
  have hI' (i j : Fin n) : HolderBoundOn (k - 2) α KI WI' (fun w ↦ A w i j) :=
    (hIH i j).mono_set Set.inter_subset_left
  obtain ⟨U, K₁, hU, hzU, hUI, hQH⟩ :=
    locally_holder_directional_trace_forcing hWI' hα₀ hα₁ A H g
      (fun i j ↦ (hA i j).mono hWI't) hI' (hH.mono hWI't)
      (fun i j ↦ (hg i j).mono hWI't) v z₀ hzWI'
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU z₀ hzU
  have hclosed : Metric.closedBall z₀ (R / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith : R / 2 < R)).trans hball
  refine ⟨U, Metric.ball z₀ (R / 2), lam, KI, K₁, hU,
    (fun w hw ↦ (hUI hw).2.2), hUI.trans hWI't,
    (isCompact_closedBall z₀ (R / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall,
    Metric.closure_ball_subset_closedBall.trans hclosed,
    Metric.mem_ball_self (by linarith), hlam,
    (fun w hw ↦ hEll w (hUI hw).2.1),
    (fun i j ↦ (hI' i j).mono_set hUI), hQH⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- The finite-order Schauder passes supply common-domain Hölder control. The commutation identity uses genuine third-derivative symmetry; the remaining
witness supplies the two finite-order Hölder passes. -/
private theorem chartFirstDerivative_higher_holder_forcing_inputs
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (_hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    {k : ℕ} (hk : 3 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ)
    {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    (x : M) (z₀ v : EuclideanSpace ℂ (Fin n))
    (hz₀ : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (_hn : 0 < n) (_hv : v ≠ 0)
    (U₀ : Set (EuclideanSpace ℂ (Fin n))) (hU₀ : IsOpen U₀)
    (_hU₀c : IsCompact (closure U₀))
    (_hU₀t : closure U₀ ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hzU₀ : z₀ ∈ U₀) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let f := φ ∘ e.symm
    let A w := (ω₀.metricInChart x w + complexHessian f w)⁻¹
    let u w := fderiv ℝ f w v
    ∃ U V : Set (EuclideanSpace ℂ (Fin n)), ∃ lam K K₁ : ℝ≥0,
      IsOpen U ∧ U ⊆ U₀ ∧ U ⊆ e.target ∧ IsCompact (closure V) ∧
        closure V ⊆ U ∧ z₀ ∈ V ∧ 0 < lam ∧
        IsUniformlyEllipticOn A lam U ∧
        (∀ j l, HolderBoundOn (k - 2) α K U (fun w ↦ A w j l)) ∧
        (∀ w ∈ U, fderiv ℝ (complexHessian f) w v = complexHessian u w) ∧
        HolderBoundOn (k - 2) α K₁ U (complexEllipticOp A u) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f := φ ∘ e.symm
  let A w := (ω₀.metricInChart x w + complexHessian f w)⁻¹
  let u w := fderiv ℝ f w v
  let Q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦
    fderiv ℝ (fun z ↦ G (e.symm z) + Real.log (RCLike.re (ω₀.metricInChart x z).det)) w v -
      RCLike.re ((A w) * fderiv ℝ (ω₀.metricInChart x) w v).trace
  suffices hInputs :
      ∃ U V : Set (EuclideanSpace ℂ (Fin n)), ∃ lam K K₁ : ℝ≥0,
        IsOpen U ∧ U ⊆ U₀ ∧ U ⊆ e.target ∧ IsCompact (closure V) ∧
          closure V ⊆ U ∧ z₀ ∈ V ∧ 0 < lam ∧
          IsUniformlyEllipticOn A lam U ∧
          (∀ j l, HolderBoundOn (k - 2) α K U (fun w ↦ A w j l)) ∧
          HolderBoundOn (k - 2) α K₁ U Q by
    obtain ⟨U, V, lam, K, K₁, hU, hUU₀, hUt, hVc, hVU, hzV,
      hlam, hEll, hAH, hQ⟩ := hInputs
    have hf : ContDiffOn ℝ k f e.target := by
      have h := (contMDiffOn_univ.mpr hregular).comp
        (contMDiffOn_extChartAt_symm x) (by intro w hw; simp)
      exact h.contDiffOn
    have hComm (w : EuclideanSpace ℂ (Fin n)) (hw : w ∈ U) :
        fderiv ℝ (complexHessian f) w v = complexHessian u w := by
      exact induction_complexHessian_fderiv_directional
        ((hf.contDiffAt ((isOpen_extChartAt_target x).mem_nhds (hUt hw))).of_le
          (by exact_mod_cast hk))
    refine ⟨U, V, lam, K, K₁, hU, hUU₀, hUt, hVc, hVU, hzV,
      hlam, hEll, hAH, hComm, ?_⟩
    apply holderBoundOn_congr_of_isOpen hU ?_ hQ
    intro w hw
    exact chartLogDetEquation_linearized_finite ω₀ hEquation hk hregular x w v
      (hUt hw) (hComm w hw)
  have hW : IsOpen e.target := isOpen_extChartAt_target x
  have hf : ContDiffOn ℝ k f e.target := by
    exact ((contMDiffOn_univ.mpr hregular).comp (contMDiffOn_extChartAt_symm x)
      (by intro w hw; simp)).contDiffOn
  have hBA := chartMetric_inverse_contDiffOn_pred_two ω₀ hEquation hk hregular x
  have hpos (w) (hw : w ∈ e.target) :
      (ω₀.metricInChart x w + complexHessian f w).PosDef :=
    Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨(hEquation x w hw).1, fun d hd ↦ RCLike.pos_iff.mpr
        ⟨(hEquation x w hw).2.1 d hd,
          (hEquation x w hw).1.im_star_dotProduct_mulVec_self d⟩⟩
  let g := ω₀.metricInChart x
  let H w := G (e.symm w) + Real.log (RCLike.re (g w).det)
  have hg (i j : Fin n) : ContDiffOn ℝ ∞ (fun w ↦ g w i j) e.target :=
    ω₀.contDiffOn_metricInChart x i j
  have hdet : ContDiffOn ℝ ∞ (fun w ↦ (g w).det) e.target := by
    simp only [Matrix.det_apply]
    fun_prop
  have hlog : ContDiffOn ℝ ∞ (fun w ↦ Real.log (RCLike.re (g w).det)) e.target := by
    apply (Complex.reCLM.contDiff.comp_contDiffOn hdet).log
    intro w hw
    exact ne_of_gt ((RCLike.pos_iff.mp (ω₀.posDef_metricInChart x hw).det_pos).1)
  have hGc : ContDiffOn ℝ ∞ (G ∘ e.symm) e.target := by
    exact ((contMDiffOn_univ.mpr hG).comp (contMDiffOn_extChartAt_symm x)
      (by intro w hw; simp)).contDiffOn
  have hH : ContDiffOn ℝ ∞ H e.target := hGc.add hlog
  have hEq (d : EuclideanSpace ℂ (Fin n)) : Set.EqOn
      (complexEllipticOp A (fun w ↦ fderiv ℝ f w d))
      (fun w ↦ fderiv ℝ H w d - RCLike.re (A w * fderiv ℝ g w d).trace) e.target := by
    intro w hw
    apply chartLogDetEquation_linearized_finite ω₀ hEquation hk hregular x w d hw
    exact induction_complexHessian_fderiv_directional
      ((hf.contDiffAt (hW.mem_nhds hw)).of_le (by exact_mod_cast hk))
  exact higher_holder_inputs_of_finite_jets hk hSch hα₀ hα₁ hW f H g hf
    (fun i j ↦ ω₀.contDiffOn_metricInChart x i j) hH hBA.1 hBA.2 hpos
    (fun d ↦ chartFirstDerivative_contDiffOn_pred hk hregular x d)
    (fun d ↦ chartDirectionalForcing_contDiffOn_of_inverse_entries ω₀ hG x hBA.2 d)
    hEq z₀ v hz₀ hU₀ hzU₀

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- The first finite-order Schauder pass supplies the Hölder inputs for the second pass. -/
private theorem chartFirstDerivative_higher_schauder_inputs
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    {k : ℕ} (hk : 3 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ)
    {α : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    (x : M) (z₀ v : EuclideanSpace ℂ (Fin n))
    (hz₀ : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hn : 0 < n) (hv : v ≠ 0) :
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
    let f := φ ∘ e.symm
    let A w := (ω₀.metricInChart x w + complexHessian f w)⁻¹
    let u w := fderiv ℝ f w v
    ∃ U V : Set (EuclideanSpace ℂ (Fin n)), ∃ lam K K₀ K₁ : ℝ≥0,
      IsOpen U ∧ U ⊆ e.target ∧ IsCompact (closure V) ∧ closure V ⊆ U ∧ z₀ ∈ V ∧
        0 < lam ∧
        (∀ j l, ContDiffOn ℝ (k - 2 : ℕ) (fun w ↦ A w j l) U) ∧
        IsUniformlyEllipticOn A lam U ∧
        (∀ j l, HolderBoundOn (k - 2) α K U (fun w ↦ A w j l)) ∧
        ContDiffOn ℝ (k - 2 : ℕ) (complexEllipticOp A u) U ∧
        HolderBoundOn (k - 2) α K₁ U (complexEllipticOp A u) ∧
        (∀ w ∈ U, |u w| ≤ K₀) := by
  obtain ⟨U₀, K₀, hU₀, hU₀c, hU₀t, hzU₀, huB⟩ :=
    chartFirstDerivative_locally_bounded hk hregular x z₀ v hz₀
  obtain ⟨U, V, lam, K, K₁, hU, hUU₀, hUt, hVc, hVU, hzV,
    hlam, hEll, hAH, hComm, hLuH⟩ :=
    chartFirstDerivative_higher_holder_forcing_inputs hSch ω₀ hG hφ hEquation
      hk hregular hα₀ hα₁ x z₀ v hz₀ hn hv U₀ hU₀ hU₀c hU₀t hzU₀
  have hA := (chartMetric_inverse_contDiffOn_pred_two ω₀ hEquation hk hregular x).2
  have hAU (j l : Fin n) := (hA j l).mono hUt
  have hQ := chartDirectionalForcing_contDiffOn_of_inverse_entries ω₀ hG x hA v
  have hEq := fun w hw ↦ chartLogDetEquation_linearized_finite ω₀ hEquation hk hregular
    x w v (hUt hw) (hComm w hw)
  have hLu := (hQ.mono hUt).congr hEq
  exact ⟨U, V, lam, K, K₀, K₁, hU, hUt, hVc, hVU, hzV,
    hlam, hAU, hEll, hAH, hLu, hLuH, fun w hw ↦ huB w (hUU₀ hw)⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- The nonzero-direction gain uses a genuine `C²` Schauder input. -/
private theorem chartFirstDerivative_local_contDiffOn_of_schauder_nonzero
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    {k : ℕ} (hk : 3 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ)
    (x : M) (z₀ v : EuclideanSpace ℂ (Fin n))
    (hz₀ : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hn : 0 < n) (hv : v ≠ 0)
    (hC2 : ContDiffOn ℝ 2
      (fun z ↦ fderiv ℝ
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W ∧ z₀ ∈ W ∧
      ContDiffOn ℝ k
        (fun z ↦ fderiv ℝ
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v) W := by
  let α : ℝ≥0 := 1 / 2
  have hα₀ : 0 < α := by norm_num [α]
  have hα₁ : α < 1 := by norm_num [α]
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f := φ ∘ e.symm
  let A w := (ω₀.metricInChart x w + complexHessian f w)⁻¹
  let u w := fderiv ℝ f w v
  obtain ⟨U, V, lam, K, K₀, K₁, hU, hUt, hVc, hVU, hzV,
    hlam, hA, hEll, hAH, hLu, hLuH, huB⟩ :=
    chartFirstDerivative_higher_schauder_inputs hSch ω₀ hG hφ hEquation hk hregular
      hα₀ hα₁ x z₀ v hz₀ hn hv
  exact local_contDiffOn_of_higher_schauder_inputs hk hSch hα₀ hα₁ hlam hU hVc hVU
    hzV A u hA (hC2.mono hUt) hEll hAH hLu hLuH huB

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- The two finite-order Schauder passes give each directional derivative the required local
regularity; their neighborhoods may depend on the direction. -/
private theorem chartFirstDerivative_local_contDiffOn_of_schauder
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    {k : ℕ} (hk : 3 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ)
    (x : M) (z₀ v : EuclideanSpace ℂ (Fin n))
    (hz₀ : z₀ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ W : Set (EuclideanSpace ℂ (Fin n)), IsOpen W ∧ z₀ ∈ W ∧
      ContDiffOn ℝ k
        (fun z ↦ fderiv ℝ
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v) W := by
  by_cases hv : v = 0
  · subst v
    refine ⟨(extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
      isOpen_extChartAt_target x, hz₀, ?_⟩
    simpa only [map_zero] using
      (contDiffOn_const : ContDiffOn ℝ k (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : ℝ))
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
  · have hn : 0 < n := by
      apply Nat.pos_of_ne_zero
      intro hn
      subst n
      exact hv (Subsingleton.elim v 0)
    have hregular3 : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 3 φ :=
      hregular.of_le (by exact_mod_cast hk)
    have hC2 : ContDiffOn ℝ 2
        (fun z ↦ fderiv ℝ
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
      chartFirstDerivative_contDiffOn_pred (k := 3) (by omega) hregular3 x v
    exact chartFirstDerivative_local_contDiffOn_of_schauder_nonzero hSch ω₀ hG hφ
      hEquation hk hregular x z₀ v hz₀ hn hv hC2

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Higher-order interior regularity: for `k ≥ 3`, a `C^k` positive solution with smooth
right-hand side is `C^{k+1}`.  This hypothesis ensures the differentiated unknowns are already `C²`
Schauder inputs. -/
theorem solvesMongeAmpereC2_contMDiff_succ_of_contMDiff
    (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    {k : ℕ} (hk : 3 ≤ k)
    (hregular : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) k φ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) (k + 1) φ := by
  apply contMDiff_succ_of_local_chart_directional_derivatives (by omega) hregular
  intro x z₀ v hz₀
  exact chartFirstDerivative_local_contDiffOn_of_schauder hSch ω₀ hG hφ hEquation
    hk hregular x z₀ v hz₀

end KahlerForm
