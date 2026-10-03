module

public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualNormalization
public import CalabiYau.MongeAmpere.Continuity.Openness.ChartHolderC2Regularity.CompletedChartJets
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetMatrixRemainder
public import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetBaseVariation
public import CalabiYau.Mathlib.Analysis.Holder.Bilinear
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.RawMatrixIdentity
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.CompactControl
import CalabiYau.MongeAmpere.Continuity.Openness.ResidualDerivative.LogDetRemainder.PairwiseHolderEstimate

/-!
# Transfer matrix Taylor bounds to chartwise Hölder control

This leaf carries the chartwise transfer step: the fixed-base and variable-base matrix Taylor
bounds are combined with the completed order-two chart jets and Hölder bilinear estimates to control
the evaluated residual remainder on each chart piece. The finite constants are uniform on the
positive neighborhood supplied by the residual radius.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology ComplexOrder Matrix.Norms.Frobenius
open MeasureTheory

namespace Matrix

set_option maxHeartbeats 200000 in
/-- Positive definiteness persists along an affine segment, including its endpoints. -/
private theorem posDef_affine_segment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (s : ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : ((1 - s) • A + s • B).PosDef := by
  by_cases hs0 : s = 0
  · simpa [hs0] using hA
  · by_cases hs1 : s = 1
    · simpa [hs1] using hB
    · have hleft : 0 < 1 - s :=
        lt_of_le_of_ne (sub_nonneg.mpr hs.2) (by intro h; apply hs1; linarith)
      have hright : 0 < s :=
        lt_of_le_of_ne hs.1 (by intro h; apply hs0; linarith)
      exact (hA.smul hleft).add (hB.smul hright)

/-- The synchronous affine rectangle between four positive corners remains in the positive cone.
This is the common-rectangle positivity step for chartwise two-point estimates. -/
private theorem posDef_affine_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℂ) (s t : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef) (hD : D.PosDef)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((1 - t) • ((1 - s) • A + s • B) +
      t • ((1 - s) • C + s • D)).PosDef := by
  exact posDef_affine_segment ((1 - s) • A + s • B) ((1 - s) • C + s • D) t
    (posDef_affine_segment A B s hA hB hs)
    (posDef_affine_segment C D s hC hD hs) ht

end Matrix

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem holderBoundOn_of_contDiffOn_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U K : Set E} {f : E → F} {α : ℝ≥0}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderBoundOn 0 α C K f := by
  classical
  have hNormCont : ContinuousOn (fun x => ‖f x‖) K :=
    (hf.continuousOn.mono hKU).norm
  obtain ⟨B, hB₀, hB⟩ := (hK.bddAbove_image hNormCont).exists_ge 0
  let C : ℝ≥0 := ⟨B, hB₀⟩
  have hBound (x : E) (hx : x ∈ K) : ‖f x‖ ≤ (C : ℝ) := by
    exact_mod_cast hB (‖f x‖) ⟨x, hx, rfl⟩
  have hLoc : LocallyLipschitzOn K f := by
    intro x hx
    have hxU : x ∈ U := hKU hx
    have hfx : ContDiffAt ℝ 1 f x :=
      (hf.contDiffAt (hU.mem_nhds hxU)).of_le (by simp)
    obtain ⟨L, t, ht, hLip⟩ := hfx.exists_lipschitzOnWith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨L, Metric.ball x δ ∩ K,
      Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩, ?_⟩
    · exact fun y hy => ⟨hy.1, hy.2⟩
    · apply hLip.mono
      intro y hy
      exact hball hy.1
  obtain ⟨L, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hLoc
  have hdiamTop : Metric.ediam K ≠ ⊤ := hK.isBounded.ediam_ne_top
  let D : ℝ≥0 := (Metric.ediam K).toNNReal
  have hdist (x : E) (hx : x ∈ K) (y : E) (hy : y ∈ K) :
      edist x y ≤ (D : ENNReal) := by
    have heq : (D : ENNReal) = Metric.ediam K := ENNReal.coe_toNNReal hdiamTop
    rw [heq]
    exact Metric.edist_le_ediam_of_mem hx hy
  have hHolderF := hLip.holderOnWith.of_le hdist hα
  let Cα : ℝ≥0 := L * D ^ ((1 : ℝ) - (α : ℝ))
  let Ctot : ℝ≥0 := max (2 * C) Cα
  let JI : F ≃ₗᵢ[ℝ] (E [×0]→L[ℝ] F) :=
    (continuousMultilinearCurryFin0 ℝ E F).symm
  let J : F →L[ℝ] (E [×0]→L[ℝ] F) := JI.toContinuousLinearMap
  have hJlip : LipschitzWith 1 J := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (J x) (J y) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact JI.norm_map _
      _ ≤ 1 * dist x y := by simp
  have hJ : HolderWith 1 1 J := hJlip.holderWith
  have hHolderJet : HolderOnWith Cα α (iteratedFDeriv ℝ 0 f) K := by
    have hcomp : HolderOnWith (1 * Cα ^ (1 : ℝ)) (1 * α) (J ∘ f) K :=
      (hJ.holderOnWith Set.univ).comp hHolderF (by intro x hx; exact Set.mem_univ _)
    have hcomp' : HolderOnWith Cα α (J ∘ f) K := by
      simpa [NNReal.rpow_one, one_mul] using hcomp
    have heq : iteratedFDeriv ℝ 0 f = J ∘ f := by
      simpa [J] using (iteratedFDeriv_zero_eq_comp (𝕜 := ℝ) (f := f))
    rw [heq]
    exact hcomp'
  refine ⟨Ctot, ?_⟩
  constructor
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero]
    exact (hBound x hx).trans (by
      calc
        (C : ℝ) = 1 * C := by ring
        _ ≤ (2 * C : ℝ) := by gcongr; norm_num
        _ ≤ (Ctot : ℝ) := by exact_mod_cast (le_max_left (2 * C) Cα))
  · exact hHolderJet.mono_const (le_max_right _ _)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] in
private theorem exists_metricInChartInverseEntryHolderBound
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₁ : α < 1) (i : cover.ι) (j k : Fin n) :
    ∃ C : ℝ≥0, HolderBoundOn 0 α C (cover.piece i)
      (fun z => (ω₁.metricInChart (cover.base i) z)⁻¹ j k) := by
  let x := cover.base i
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let U := e.target
  let K := cover.piece i
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z => ω₁.metricInChart x z
  have hG_entry (a b : Fin n) : ContDiffOn ℝ ∞ (fun z => G z a b) U := by
    exact ω₁.contDiffOn_metricInChart x a b
  have hdet : ContDiffOn ℝ ∞ (fun z => (G z).det) U := by
    simp_rw [Matrix.det_apply]
    fun_prop
  have hdet_ne {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ U) : (G z).det ≠ 0 := by
    have hpos := (RCLike.pos_iff.mp (ω₁.posDef_metricInChart x hz).det_pos).1
    exact fun h => hpos.ne' (congrArg RCLike.re h)
  have hdetInv : ContDiffOn ℝ ∞ (fun z => ((G z).det)⁻¹) U :=
    hdet.inv (fun z hz => hdet_ne hz)
  have hUpdate (r c s t : Fin n) :
      ContDiffOn ℝ ∞ (fun z => (G z).updateRow r (Pi.single c (1 : ℂ)) s t) U := by
    simp_rw [Matrix.updateRow_apply]
    by_cases hrs : s = r
    · subst s
      simp only [Pi.single_apply]
      exact contDiffOn_const
    · simp only [ite_eq_right hrs]
      exact hG_entry s t
  have hAdj_entry (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun z => (G z).adjugate a b) U := by
    simp_rw [Matrix.adjugate_apply, Matrix.det_apply']
    apply ContDiffOn.sum
    intro σ hσ
    have hp : ContDiffOn ℝ ∞ (fun z =>
        ∏ t, (G z).updateRow b (Pi.single a (1 : ℂ)) (σ t) t) U := by
      exact contDiffOn_prod (t := Finset.univ) (fun t ht => hUpdate b a (σ t) t)
    change ContDiffOn ℝ ∞ (fun z =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ t, (G z).updateRow b (Pi.single a (1 : ℂ)) (σ t) t) U
    exact contDiffOn_const.mul hp
  have hInv_entry (a b : Fin n) :
      ContDiffOn ℝ ∞ (fun z => (G z)⁻¹ a b) U := by
    have hmul : ContDiffOn ℝ ∞
        (fun z => ((G z).det)⁻¹ * (G z).adjugate a b) U :=
      hdetInv.mul (hAdj_entry a b)
    refine hmul.congr ?_
    intro z hz
    rw [Matrix.inv_def]
    simp [Matrix.smul_apply, smul_eq_mul]
  exact holderBoundOn_of_contDiffOn_compact (isOpen_extChartAt_target x)
    (cover.isCompact_piece i) (cover.piece_in_target i) (hInv_entry j k)
    (le_of_lt hα₁)

section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
private theorem holderBoundOn_zero_sub
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α Kf Kg : ℝ≥0} {s : Set E} {f g : E → F}
    (hf : HolderBoundOn 0 α Kf s f)
    (hg : HolderBoundOn 0 α Kg s g) :
    HolderBoundOn 0 α (Kf + Kg) s (fun x ↦ f x - g x) := by
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    have hfnorm : ‖f x‖ ≤ (Kf : ℝ) := by
      simpa [iteratedFDeriv_zero_eq_comp] using hf.1 0 le_rfl x hx
    have hgnorm : ‖g x‖ ≤ (Kg : ℝ) := by
      simpa [iteratedFDeriv_zero_eq_comp] using hg.1 0 le_rfl x hx
    simpa [iteratedFDeriv_zero_eq_comp] using
      (calc ‖f x - g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_sub_le _ _
        _ ≤ (Kf : ℝ) + (Kg : ℝ) := add_le_add hfnorm hgnorm)
  · intro x hx y hy
    let e := continuousMultilinearCurryFin0 ℝ E F
    change edist (e.symm (f x - g x)) (e.symm (f y - g y)) ≤ _
    calc
      edist (e.symm (f x - g x)) (e.symm (f y - g y)) =
          edist (f x - g x) (f y - g y) := (IsometryClass.isometry e.symm).edist_eq _ _
      _ = edist (f x + -g x) (f y + -g y) := by congr <;> abel
      _ ≤ edist (f x) (f y) + edist (-g x) (-g y) := edist_add_add_le _ _ _ _
      _ = edist (f x) (f y) + edist (g x) (g y) := by simp
      _ ≤ (Kf : ENNReal) * edist x y ^ (α : ℝ) +
          (Kg : ENNReal) * edist x y ^ (α : ℝ) := by
        have hfh : edist (e.symm (f x)) (e.symm (f y)) ≤
            (Kf : ENNReal) * edist x y ^ (α : ℝ) := hf.2 x hx y hy
        have hgh : edist (e.symm (g x)) (e.symm (g y)) ≤
            (Kg : ENNReal) * edist x y ^ (α : ℝ) := hg.2 x hx y hy
        have hfh' : edist (f x) (f y) ≤ (Kf : ENNReal) * edist x y ^ (α : ℝ) := by
          calc
            edist (f x) (f y) = edist (e.symm (f x)) (e.symm (f y)) :=
              (IsometryClass.isometry e.symm).edist_eq _ _ |>.symm
            _ ≤ _ := hfh
        have hgh' : edist (g x) (g y) ≤ (Kg : ENNReal) * edist x y ^ (α : ℝ) := by
          calc
            edist (g x) (g y) = edist (e.symm (g x)) (e.symm (g y)) :=
              (IsometryClass.isometry e.symm).edist_eq _ _ |>.symm
            _ ≤ _ := hgh
        exact add_le_add hfh' hgh'
      _ = ((↑Kf + ↑Kg) * edist x y ^ (α : ℝ)) := by rw [add_mul]
      _ = ((Kf + Kg : ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ) := by rw [ENNReal.coe_add]

private theorem hessian_entry_holderOnWith_of_orderTwoBound
    {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n) :
    HolderOnWith C α (fun z ↦ complexHessian f z i j) K := by
  let u : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single i 1
  let v : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let iu := Complex.I • u
  let iv := Complex.I • v
  let D := iteratedFDeriv ℝ 2 f
  have hu : ‖u‖ = 1 := by simp [u]
  have hv : ‖v‖ = 1 := by simp [v]
  have hiu : ‖iu‖ = 1 := by simp [iu, hu, norm_smul, Complex.norm_I]
  have hiv : ‖iv‖ = 1 := by simp [iv, hv, norm_smul, Complex.norm_I]
  have hform (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K) :
      complexHessian f z i j =
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
  have hD (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ K)
      (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ K) :
      ‖D x - D y‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    have h := hf.2.dist_le hx hy
    simpa only [dist_eq_norm] using h
  have hEval (T : (EuclideanSpace ℂ (Fin n) [×2]→L[ℝ] ℝ))
      (w : Fin 2 → EuclideanSpace ℂ (Fin n)) (hw : ∀ k, ‖w k‖ = 1) :
      ‖T w‖ ≤ ‖T‖ := by
    calc
      ‖T w‖ ≤ ‖T‖ * ∏ k, ‖w k‖ := ContinuousMultilinearMap.le_opNorm T w
      _ = ‖T‖ := by simp [hw]
  have huvv (w : Fin 2 → EuclideanSpace ℂ (Fin n))
      (w0 : ‖w 0‖ = 1) (w1 : ‖w 1‖ = 1) : ∀ k, ‖w k‖ = 1 := by
    intro k
    fin_cases k
    · exact w0
    · exact w1
  have hdiff (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ K)
      (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ K) :
      complexHessian f x i j - complexHessian f y i j =
        (((D x - D y) ![u, v] : ℂ) + (D x - D y) ![iu, iv] +
          Complex.I * ((D x - D y) ![u, iv] - (D x - D y) ![iu, v])) / 4 := by
    rw [hform x hx, hform y hy]
    simp only [sub_apply]
    field_simp
    push_cast
    ring
  intro x hx y hy
  rw [edist_dist]
  have hnum :
      ‖(((D x - D y) ![u, v] : ℝ) : ℂ) + (D x - D y) ![iu, iv] +
        Complex.I * ((D x - D y) ![u, iv] - (D x - D y) ![iu, v])‖ ≤
      4 * ‖D x - D y‖ := by
    have h1 := hEval (D x - D y) ![u, v] (huvv _ hu hv)
    have h2 := hEval (D x - D y) ![iu, iv] (huvv _ hiu hiv)
    have h3 := hEval (D x - D y) ![u, iv] (huvv _ hu hiv)
    have h4 := hEval (D x - D y) ![iu, v] (huvv _ hiu hv)
    let a : ℝ := (D x) ![u, v]
    let b : ℝ := (D x) ![iu, iv]
    let c : ℝ := (D x) ![u, iv]
    let d : ℝ := (D x) ![iu, v]
    let a' : ℝ := (D y) ![u, v]
    let b' : ℝ := (D y) ![iu, iv]
    let c' : ℝ := (D y) ![u, iv]
    let d' : ℝ := (D y) ![iu, v]
    have h1C : ‖Complex.ofReal a - Complex.ofReal a'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [a, a', sub_apply] using h1
    have h2C : ‖Complex.ofReal b - Complex.ofReal b'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [b, b', sub_apply] using h2
    have h3C : ‖Complex.ofReal c - Complex.ofReal c'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [c, c', sub_apply] using h3
    have h4C : ‖Complex.ofReal d - Complex.ofReal d'‖ ≤ ‖D x - D y‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [d, d', sub_apply] using h4
    have hrest : ‖Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
        (Complex.ofReal d - Complex.ofReal d'))‖ ≤
        ‖D x - D y‖ + ‖D x - D y‖ := by
      rw [norm_mul, Complex.norm_I]
      simpa only [one_mul] using (norm_sub_le _ _).trans (add_le_add h3C h4C)
    have htri : ‖Complex.ofReal (a - a') + Complex.ofReal (b - b') +
        Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
          (Complex.ofReal d - Complex.ofReal d'))‖ ≤
        ‖Complex.ofReal (a - a')‖ + ‖Complex.ofReal (b - b')‖ +
          ‖D x - D y‖ + ‖D x - D y‖ := by
      calc
        _ ≤ ‖Complex.ofReal (a - a')‖ + ‖Complex.ofReal (b - b')‖ +
            ‖Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
              (Complex.ofReal d - Complex.ofReal d'))‖ := by
          calc
            _ ≤ ‖Complex.ofReal (a - a') + Complex.ofReal (b - b')‖ +
                ‖Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
                  (Complex.ofReal d - Complex.ofReal d'))‖ := norm_add_le _ _
            _ ≤ _ := by exact add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by
          have h := add_le_add_left hrest
            (‖Complex.ofReal (a - a')‖ + ‖Complex.ofReal (b - b')‖)
          nlinarith
    calc
      _ = ‖Complex.ofReal (a - a') + Complex.ofReal (b - b') +
          Complex.I * ((Complex.ofReal c - Complex.ofReal c') -
            (Complex.ofReal d - Complex.ofReal d'))‖ := by
        simp [a, b, c, d, a', b', c', d', Complex.ofReal_sub]
      _ ≤ ‖D x - D y‖ + ‖D x - D y‖ +
          (‖D x - D y‖ + ‖D x - D y‖) := by
        have h1R : ‖Complex.ofReal (a - a')‖ ≤ ‖D x - D y‖ := by
          simpa [Complex.norm_real] using h1C
        have h2R : ‖Complex.ofReal (b - b')‖ ≤ ‖D x - D y‖ := by
          simpa [Complex.norm_real] using h2C
        have hrest' := hrest
        nlinarith [htri, h1R, h2R, hrest']
      _ = 4 * ‖D x - D y‖ := by ring
  calc
    ENNReal.ofReal (dist (complexHessian f x i j) (complexHessian f y i j)) =
        ENNReal.ofReal ‖complexHessian f x i j - complexHessian f y i j‖ := by
          rw [dist_eq_norm]
    _ ≤ ENNReal.ofReal (‖D x - D y‖) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hdiff x hx y hy, norm_div, Complex.norm_ofNat]
      have hden : (0 : ℝ) < 4 := by norm_num
      calc
        ‖(((D x - D y) ![u, v] : ℝ) : ℂ) + (D x - D y) ![iu, iv] +
            Complex.I * ((D x - D y) ![u, iv] - (D x - D y) ![iu, v])‖ / 4 ≤
            (4 * ‖D x - D y‖) / 4 := div_le_div_of_nonneg_right hnum (by positivity)
        _ = ‖D x - D y‖ := by norm_num
    _ ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (α : ℝ)) :=
      ENNReal.ofReal_le_ofReal (hD x hx y hy)
    _ = (C : ENNReal) * edist x y ^ (α : ℝ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg, ← edist_dist]
      rw [ENNReal.ofReal_coe_nnreal]

private theorem hessian_entry_norm_le_of_orderTwoBound
    {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
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
  have hD : ‖D z‖ ≤ (C : ℝ) := hf.1 2 le_rfl z hz
  have h1 : ‖((D z ![u, v] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![u, v] hu hv).trans hD
  have h2 : ‖((D z ![iu, iv] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![iu, iv] hiu hiv).trans hD
  have h3 : ‖((D z ![u, iv] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![u, iv] hu hiv).trans hD
  have h4 : ‖((D z ![iu, v] : ℝ) : ℂ)‖ ≤ (C : ℝ) := by
    simpa [Complex.norm_real] using (hEval ![iu, v] hiu hv).trans hD
  have hCross : ‖Complex.I * ((D z ![u, iv] : ℂ) - D z ![iu, v])‖ ≤
      (C : ℝ) + C := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (norm_sub_le _ _).trans (add_le_add h3 h4)
  have hNumerator : ‖(D z ![u, v] : ℂ) + D z ![iu, iv] +
      Complex.I * (D z ![u, iv] - D z ![iu, v])‖ ≤
      (C : ℝ) + C + ((C : ℝ) + C) := by
    calc
      _ ≤ ‖(D z ![u, v] : ℂ)‖ + ‖(D z ![iu, iv] : ℂ)‖ +
          ‖Complex.I * (D z ![u, iv] - D z ![iu, v])‖ := by
        calc
          _ ≤ ‖(D z ![u, v] : ℂ) + D z ![iu, iv]‖ +
              ‖Complex.I * (D z ![u, iv] - D z ![iu, v])‖ := norm_add_le _ _
          _ ≤ _ := by exact add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (C : ℝ) + C + ((C : ℝ) + C) := add_le_add (add_le_add h1 h2) hCross
  rw [hform, norm_div, Complex.norm_ofNat]
  calc
    ‖(D z ![u, v] : ℂ) + D z ![iu, iv] +
        Complex.I * (D z ![u, iv] - D z ![iu, v])‖ / 4 ≤
        ((C : ℝ) + C + ((C : ℝ) + C)) / 4 :=
      div_le_div_of_nonneg_right hNumerator (by norm_num)
    _ = C := by ring

private theorem holderBoundOn_zero_from_holderOnWith
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E}
    {α C : ℝ≥0} {f : E → F}
    (hf : HolderOnWith C α f K) (hBound : ∀ x ∈ K, ‖f x‖ ≤ C) :
    HolderBoundOn 0 α C K f := by
  let L := continuousMultilinearCurryFin0 ℝ E F
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa [norm_iteratedFDeriv_zero] using hBound x hx
  · intro x hx y hy
    rw [iteratedFDeriv_zero_eq_comp]
    change edist (L.symm (f x)) (L.symm (f y)) ≤ _
    rw [L.symm.edist_map]
    exact hf x hx y hy

private theorem frobenius_norm_le_of_entry_bound {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ i j, ‖A i j‖ ≤ B) :
    ‖A‖ ≤ Real.sqrt (Fintype.card (ι × ι) : ℝ) * B := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two, pow_two]
  calc
    Real.sqrt (∑ i, ∑ j, ‖A i j‖ * ‖A i j‖) ≤
        Real.sqrt ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * (B * B)) := by
      apply Real.sqrt_le_sqrt
      calc
        (∑ i, ∑ j, ‖A i j‖ * ‖A i j‖) ≤
            ∑ i, ∑ j, B * B := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact mul_le_mul (hA i j) (hA i j) (norm_nonneg _) hB
        _ = (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * (B * B) := by
          simp [mul_assoc]
    _ = Real.sqrt (Fintype.card (ι × ι) : ℝ) * B := by
      rw [Fintype.card_prod, Nat.cast_mul, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity), Real.sqrt_mul_self hB]

private theorem holderOnWith_frobenius_of_entrywise {E : Type*} [PseudoMetricSpace E]
    {ι : Type*} [Fintype ι] {α C : ℝ≥0} {K : Set E}
    {A : E → Matrix ι ι ℂ}
    (hA : ∀ i j, HolderOnWith C α (fun x ↦ A x i j) K) :
    HolderOnWith ((Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)).toNNReal) α A K := by
  intro x hx y hy
  rw [edist_dist]
  have hentry (i j : ι) : ‖A x i j - A y i j‖ ≤
      (C : ℝ) * dist x y ^ (α : ℝ) := by
    have h := (hA i j).edist_le hx hy
    rw [edist_dist, edist_dist,
      ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at h
    have h' : dist (A x i j) (A y i j) ≤
        (C : ℝ) * dist x y ^ (α : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff
        (p := dist (A x i j) (A y i j))
        (q := (C : ℝ) * dist x y ^ (α : ℝ)) (by positivity)).mp h
    rw [dist_eq_norm] at h'
    simpa only [norm_sub_rev] using h'
  have hmat := frobenius_norm_le_of_entry_bound (A x - A y)
    ((C : ℝ) * dist x y ^ (α : ℝ)) (by positivity) (by
      intro i j
      simpa only [Matrix.sub_apply] using hentry i j)
  have hnorm : dist (A x) (A y) ≤
      (Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)) * dist x y ^ (α : ℝ) := by
    rw [dist_eq_norm]
    calc
      ‖A x - A y‖ ≤ Real.sqrt (Fintype.card (ι × ι) : ℝ) *
          ((C : ℝ) * dist x y ^ (α : ℝ)) := hmat
      _ = (Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)) *
          dist x y ^ (α : ℝ) := by ring
  calc
    ENNReal.ofReal (dist (A x) (A y)) ≤
        ENNReal.ofReal ((Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)) *
          dist x y ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal hnorm
    _ = ((((Real.sqrt (Fintype.card (ι × ι) : ℝ) * (C : ℝ)).toNNReal :
          ℝ≥0) : ENNReal) * edist x y ^ (α : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg,
        ← edist_dist, ENNReal.ofReal_eq_coe_nnreal (by positivity)]
      apply congrArg (fun c : ℝ≥0 => (c : ENNReal) * edist x y ^ (α : ℝ))
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _)
        (NNReal.coe_nonneg C))]
      rfl

private theorem hessian_matrix_holderBoundOn_zero_of_orderTwoBound
    {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) :
    @HolderBoundOn (EuclideanSpace ℂ (Fin n)) _ _ (Matrix (Fin n) (Fin n) ℂ)
      Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace 0 α
      ((Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ)).toNNReal) K
      (fun z ↦ (fun i j ↦ complexHessian f z i j : Matrix (Fin n) (Fin n) ℂ)) := by
  let H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z i j ↦ complexHessian f z i j
  change @HolderBoundOn (EuclideanSpace ℂ (Fin n)) _ _ (Matrix (Fin n) (Fin n) ℂ)
    Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace 0 α
    ((Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ)).toNNReal) K H
  apply holderBoundOn_zero_from_holderOnWith
    (holderOnWith_frobenius_of_entrywise (fun i j ↦
      hessian_entry_holderOnWith_of_orderTwoBound hf hSmooth i j))
  intro z hz
  change ‖H z‖ ≤ _
  calc
    ‖H z‖ ≤ Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ) :=
      frobenius_norm_le_of_entry_bound (H z) (C : ℝ) (NNReal.coe_nonneg C) (by
        intro i j
        exact hessian_entry_norm_le_of_orderTwoBound hf hSmooth i j hz)
    _ = ((Real.sqrt (Fintype.card (Fin n × Fin n) : ℝ) * (C : ℝ)).toNNReal : ℝ) :=
      (Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (NNReal.coe_nonneg C))).symm
private theorem hessian_entry_holderBoundOn_zero_of_orderTwoBound
    {α C : ℝ≥0} {K : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℝ}
    (hf : HolderBoundOn 2 α C K f)
    (hSmooth : ∀ z ∈ K, ContDiffAt ℝ 2 f z) (i j : Fin n) :
    HolderBoundOn 0 α C K (fun z ↦ complexHessian f z i j) := by
  apply holderBoundOn_zero_from_holderOnWith
    (hessian_entry_holderOnWith_of_orderTwoBound hf hSmooth i j)
  intro z hz
  exact hessian_entry_norm_le_of_orderTwoBound hf hSmooth i j hz

end

section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
private theorem laplacian_eq_inChart_c2
    (ω₁ : KahlerForm n M) {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 f) (x : M)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    ω₁.laplacian f y = RCLike.re
      ((ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))⁻¹ *
        complexHessian (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).trace := by
  let ψ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let z := ψ y
  have hy' : y ∈ ψ.source := by simpa [ψ, ← extChartAt_source] using hy
  have hz : z ∈ ψ.target := ψ.map_source hy'
  have hzpoint : ψ.symm z = y := ψ.left_inv hy'
  have hychart : y ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hyC : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [extChartAt_real_eq, ← extChartAt_source] using hy
  have hyCy : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by simp
  have hOverlap : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source ∩
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source := ⟨hy', hychart⟩
  let A : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) := {
    toLinearEquiv := {
      toFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
      invFun := tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
      left_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
              (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source :=
          ⟨⟨hyC, hyCy⟩, hyC⟩
        have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v) htriple
        calc
          _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v := hc
          _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (x := x) (z := y) hyC
      right_inv := by
        intro v
        have htriple : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source ∩
            (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source ∩
              (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source :=
          ⟨⟨hyCy, hyC⟩, hyCy⟩
        have hc := tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v) htriple
        calc
          _ = tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v := hc
          _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
            (x := y) (z := y) (by simp)
      map_add' := by
        intro u v
        exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_add u v
      map_smul' := by
        intro c v
        exact (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).map_smul c v
    }
    continuous_toFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).continuous
    continuous_invFun := (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y).continuous
  }
  have hA : fderiv ℝ
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ := by
    have hdef : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
        fderiv ℝ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
      rw [tangentCoordChange_def]
      simp [z, ψ]
    calc
      _ = tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y := hdef.symm
      _ = (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y).restrictScalars ℝ :=
        tangentCoordChange_real_eq hOverlap
      _ = _ := rfl
  have hrep (β : FormField (EuclideanSpace ℂ (Fin n)) M 2) :
      β.chartRep x z = (β y).compContinuousLinearMap
        ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ) := by
    rw [FormField.chartRep_eq_chartRep_comp (x := x) (x' := y) (z := z) hz]
    · rw [hzpoint, FormField.chartRep_self, hA]
    · have heq : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z = y := by
        simpa [ψ] using hzpoint
      rw [heq]
      exact hychart
  let ey := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
  let zy := ey y
  have hzy : zy ∈ ey.target := mem_extChartAt_target y
  have hzyN : ey.target ∈ 𝓝 zy := (isOpen_extChartAt_target y).mem_nhds hzy
  have hey : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ ey.symm zy :=
    (contMDiffOn_extChartAt_symm y).contMDiffAt hzyN
  have hey₂ : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 2 ey.symm zy := by
    exact hey.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hfc : ContDiffAt ℝ 2 (f ∘ ey.symm) zy :=
    (hf.contMDiffAt.comp zy hey₂).contDiffAt
  have hddOne : (mddbar n f y).IsOneOne := by
    change (ddbar (f ∘ ey.symm) zy).IsOneOne
    exact isOneOne_ddbar hfc
  have htrace := ContinuousAlternatingMap.relTrace_compContinuousLinearMap
    (ω₁.isOneOne y) hddOne A
  have hddbar := chartRep_mddbar_of_contMDiff_two hf x hz
  calc
    ω₁.laplacian f y = ContinuousAlternatingMap.relTrace (ω₁ y) (mddbar n f y) := rfl
    _ = ContinuousAlternatingMap.relTrace ((ω₁ y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ))
        ((mddbar n f y).compContinuousLinearMap
          ((A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ)) :=
      htrace.symm
    _ = RCLike.re ((ω₁.metricInChart x z)⁻¹ * complexHessian (f ∘ ψ.symm) z).trace := by
      rw [← hrep ω₁.toFormField, ← hrep (mddbar n f), hddbar]
      rfl

private theorem logMongeAmpere_eq_chart_logdet_of_c2
    (ω₁ : KahlerForm n M) (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ)
    (hpositive : ω₁.IsC2Potential ψ) (x : M)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    Real.log (ω₁.mongeAmpere ψ y) =
      Real.log (RCLike.re (ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) +
        complexHessian (ψ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det) -
      Real.log (RCLike.re (ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det) := by
  have hMA := ω₁.mongeAmpere_eq_inChart_of_contMDiff_two hψ x hy
  have hz : extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y ∈
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    have hy' : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).source := by
      simpa only [extChartAt_source] using hy
    exact (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).map_source hy'
  have hA : (ω₁.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).PosDef :=
    ω₁.posDef_metricInChart x hz
  have hAdet : 0 < RCLike.re (ω₁.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det :=
    (RCLike.pos_iff.mp hA.det_pos).1
  have hMApos : 0 < ω₁.mongeAmpere ψ y := by
    change 0 < ContinuousAlternatingMap.relDet (ω₁ y) (ω₁ y + mddbar n ψ y)
    exact ContinuousAlternatingMap.relDet_pos (ω₁.isPositive y) (hpositive.2 y)
  have hBdet : 0 < RCLike.re (ω₁.metricInChart x
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y) +
        complexHessian (ψ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)).det := by
    rw [hMA] at hMApos
    exact (div_pos_iff_of_pos_right hAdet).mp hMApos
  rw [hMA, Real.log_div (ne_of_gt hBdet) (ne_of_gt hAdet)]

private theorem logMongeAmpere_sub_laplacian_eq_logDetTaylorRemainder
    (ω₁ : KahlerForm n M) (ψ : M → ℝ)
    (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 ψ)
    (hpositive : ω₁.IsC2Potential ψ) (x : M)
    {y : M} (hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source) :
    Real.log (ω₁.mongeAmpere ψ y) - ω₁.laplacian ψ y =
      Matrix.logDetTaylorRemainder
        (ω₁.metricInChart x (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y))
        (complexHessian (ψ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y)) := by
  have hLap := laplacian_eq_inChart_c2 ω₁ hψ x hy
  rw [logMongeAmpere_eq_chart_logdet_of_c2 ω₁ ψ hψ hpositive x hy, hLap]
  rfl

private theorem chartRep_isPositive_of_pointwise
    (α : FormField (EuclideanSpace ℂ (Fin n)) M 2)
    (hα : ∀ x, (α x).IsPositive) (x : M) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (α.chartRep x z).IsPositive := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let y := e.symm z
  have hyx : y ∈ e.source := e.map_target hz
  have hyyℝ : y ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y).source :=
    mem_extChartAt_source y
  have hyxℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).source := by
    simpa only [← extChartAt_real_eq] using hyx
  have hyyℂ : y ∈ (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y).source := by
    simpa only [← extChartAt_real_eq] using hyyℝ
  let A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
  let B : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
  have hBA : ∀ v, B (A v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := x) (x := y) (y := x) (z := y) (v := v) ⟨⟨hyxℂ, hyyℂ⟩, hyxℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := x) (z := y) (v := v) hyxℂ
  have hAB : ∀ v, A (B v) = v := by
    intro v
    dsimp [A, B]
    calc
      tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x y y
          (tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y x y v) =
          tangentCoordChange 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) y y y v :=
        tangentCoordChange_comp (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
          (w := y) (x := x) (y := y) (z := y) (v := v) ⟨⟨hyyℂ, hyxℂ⟩, hyyℂ⟩
      _ = v := tangentCoordChange_self (I := 𝓘(ℂ, EuclideanSpace ℂ (Fin n)))
        (x := y) (z := y) (v := v) hyyℂ
  let AEquiv : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
    { toLinearEquiv :=
        { toFun := A
          invFun := B
          left_inv := hBA
          right_inv := hAB
          map_add' := A.map_add
          map_smul' := A.map_smul }
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }
  have hAreal : tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y =
      (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)).restrictScalars ℝ :=
    tangentCoordChange_real_eq ⟨hyx, hyyℝ⟩
  have hchart : α.chartRep x z =
      (α y).compContinuousLinearMap (A.restrictScalars ℝ) := by
    change (α y).compContinuousLinearMap
      (tangentCoordChange 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x y y) = _
    rw [hAreal]
  rw [hchart]
  exact (hα y).compContinuousLinearMap AEquiv

set_option maxHeartbeats 800000 in
end

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Transfer the fixed-base and variable-base matrix Taylor estimates, completed order-two chart
jets, and Hölder bilinear estimates to the pairwise chartwise remainder bound. -/
theorem exists_centeredResidual_chartwiseRemainderBound_transfer
    (ω₀ : KahlerForm n M) (F : M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (t : ℝ) (φ : M → ℝ)
    (hsol : ω₀.SolvesMongeAmpere (fun x ↦ t * F x + ω₀.pathConstant F t) φ)
    (α : ℝ≥0) (hα₁ : α < 1)
    [P : ContinuityHolderPair (ω₀.perturb φ hsol.1) α]
    (D : CenteredPathResidualData ω₀ F hF t φ hsol α)
    (L : P.C2 ≃L[ℝ] P.C0)
    (hL : ∀ u, P.evalC0 (L u) = (ω₀.perturb φ hsol.1).laplacian (P.evalC2 u))
    (b : P.C0)
    (hb : ∀ x, P.evalC0 b x =
      (∫ y, F y ∂(ω₀.perturb φ hsol.1).volume) /
        (ω₀.perturb φ hsol.1).volume.real Set.univ - F x)
    (hfixed : ∀ (A X Y : Matrix (Fin n) (Fin n) ℂ) (μ : ℝ),
      0 < μ → A.PosDef →
      ‖A⁻¹‖ ≤ Real.sqrt (Fintype.card (Fin n) : ℝ) / μ →
      (∀ s ∈ Set.Icc (0 : ℝ) 1, (A + (1 - s) • Y + s • X).PosDef) →
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖(A + (1 - s) • Y + s • X)⁻¹‖ ≤
          Real.sqrt (Fintype.card (Fin n) : ℝ) / μ) →
      |Matrix.logDetTaylorRemainder A X - Matrix.logDetTaylorRemainder A Y| ≤
        ((Fintype.card (Fin n) : ℝ) / μ ^ 2) * max ‖X‖ ‖Y‖ * ‖X - Y‖)
    (hbase : ∀ (Mbound : ℝ≥0), 0 < Mbound →
      ∃ C : ℝ≥0, ∀ A B H : Matrix (Fin n) (Fin n) ℂ,
        (∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
          (A + (1 - s) • (B - A) + t • H).PosDef) →
        (∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
          ‖(A + (1 - s) • (B - A) + t • H)⁻¹‖ ≤ Mbound) →
        |Matrix.logDetTaylorRemainder A H - Matrix.logDetTaylorRemainder B H| ≤
          C * ‖A - B‖ * ‖H‖ ^ 2)
    (hjet : ∀ (u : P.C2) (i),
      HolderBoundOn 2 α ‖u‖₊ (P.finiteChartCover.piece i)
        ((P.evalC2 u) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            (P.finiteChartCover.base i)).symm)) :
    ∃ C : ℝ≥0, ∃ r : ℝ, 0 < r ∧
      ∀ p q : P.C2 × ℝ, ‖p‖ < r → ‖q‖ < r →
        ‖p.1‖ < D.radius → ‖q.1‖ < D.radius →
        ∀ i, HolderBoundOn 0 α
          (C * (‖p‖₊ + ‖q‖₊) * ‖p - q‖₊)
          (P.finiteChartCover.piece i)
          ((P.evalC0 (D.residual p - D.residual q -
            (L (p.1 - q.1) + (p.2 - q.2) • b))) ∘
            (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
              (P.finiteChartCover.base i)).symm) := by
  have hmeanZero (w : P.C0) :
      ∫ x, P.evalC0 w x ∂(ω₀.perturb φ hsol.1).volume = 0 := by
    change littleHolderMeanFunctional (ω₀.perturb φ hsol.1) P.finiteChartCover
      0 α P.normedDataC0 w = 0
    exact w.property
  have haverageBound (μ : Measure M) [IsFiniteMeasure μ] (f : M → ℝ)
      (B V : ℝ) (hV : 0 < V) (hVeq : V = μ.real Set.univ)
      (hf : Integrable f μ) (hb : ∀ x, |f x| ≤ B) :
      |(∫ x, f x ∂μ) / V| ≤ B := by
    have hmono : (∫ x, |f x| ∂μ) ≤ ∫ _ : M, B ∂μ := by
      apply integral_mono_ae (hf.abs) (integrable_const B)
      filter_upwards [] with x
      exact hb x
    have hnum : |∫ x, f x ∂μ| ≤ B * V := by
      calc
        |∫ x, f x ∂μ| ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _ : M, B ∂μ := hmono
        _ = B * V := by rw [integral_const, smul_eq_mul, hVeq]; ring
    rw [abs_div, abs_of_pos hV]
    exact (div_le_iff₀ hV).2 hnum
  have hcenterHolder
      {S : Set (EuclideanSpace ℂ (Fin n))} {f : EuclideanSpace ℂ (Fin n) → ℝ}
      {C : ℝ≥0} (c : ℝ) (hf : HolderBoundOn 0 α C S f)
      (hc : |c| ≤ (C : ℝ)) :
      HolderBoundOn 0 α (3 * C) S (fun z ↦ f z - c) := by
    refine ⟨?_, ?_⟩
    · intro j hj z hz
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      have hfx : |f z| ≤ (C : ℝ) := by
        simpa [norm_iteratedFDeriv_zero] using hf.1 0 le_rfl z hz
      have hbound : |f z - c| ≤ 2 * (C : ℝ) := by
        calc
          |f z - c| ≤ |f z| + |c| := abs_sub _ _
          _ ≤ (C : ℝ) + C := add_le_add hfx hc
          _ = 2 * (C : ℝ) := by ring
      have hthree : 2 * (C : ℝ) ≤ (3 * C : ℝ) := by
        nlinarith [NNReal.coe_nonneg C]
      simpa [iteratedFDeriv_zero_eq_comp, norm_iteratedFDeriv_zero] using
        hbound.trans hthree
    · have hff : HolderOnWith C α f S := by
        intro x hx y hy
        let e := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        have h := hf.2 x hx y hy
        rw [iteratedFDeriv_zero_eq_comp] at h
        change edist (e.symm (f x)) (e.symm (f y)) ≤ _ at h
        calc
          edist (f x) (f y) = edist (e.symm (f x)) (e.symm (f y)) :=
            (IsometryClass.isometry e.symm).edist_eq _ _ |>.symm
          _ ≤ _ := h
      intro x hx y hy
      let e := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
      change edist (e.symm (f x - c)) (e.symm (f y - c)) ≤ _
      calc
        edist (e.symm (f x - c)) (e.symm (f y - c)) =
            edist (f x - c) (f y - c) := (IsometryClass.isometry e.symm).edist_eq _ _
        _ = edist (f x + -c) (f y + -c) := by congr 1
        _ ≤ edist (f x) (f y) + edist (-c) (-c) := edist_add_add_le _ _ _ _
        _ = edist (f x) (f y) := by simp
        _ ≤ (C : ENNReal) * edist x y ^ (α : ℝ) := hff x hx y hy
        _ ≤ (3 * C : ENNReal) * edist x y ^ (α : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast (by nlinarith [NNReal.coe_nonneg C] : (C : ℝ) ≤ 3 * C)
          · positivity

  obtain ⟨ctrl⟩ := exists_actualChartTaylorControl (ω₀.perturb φ hsol.1) α hα₁ hjet
  obtain ⟨C, r, hr, hmatrix⟩ := exists_matrixPairwiseTaylor_holderBound α
    P.finiteChartCover.piece
    (fun i z ↦ (ω₀.perturb φ hsol.1).metricInChart (P.finiteChartCover.base i) z)
    (chartTaylorH P) ctrl hfixed hbase
  have hvol : 0 < (ω₀.perturb φ hsol.1).volume.real Set.univ := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt (isOpen_univ.measure_pos _ Set.univ_nonempty)
    · exact ne_of_lt (measure_lt_top _ _)
  refine ⟨3 * C, r, hr, ?_⟩
  intro p q hp hq hpD hqD
  have hpfirst : ‖p.1‖ < r := (norm_fst_le p).trans_lt hp
  have hqfirst : ‖q.1‖ < r := (norm_fst_le q).trans_lt hq
  let B : ℝ≥0 := C * (‖p‖₊ + ‖q‖₊) * ‖p - q‖₊
  have hB : C * (‖p.1‖₊ + ‖q.1‖₊) * ‖p.1 - q.1‖₊ ≤ B := by
    dsimp [B]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (add_le_add (by exact_mod_cast norm_fst_le p)
          (by exact_mod_cast norm_fst_le q)) (by positivity)
    · exact_mod_cast norm_fst_le (p - q)
    · positivity
    · positivity
  have hrawChart (i : P.finiteChartCover.ι) :
      HolderBoundOn 0 α B (P.finiteChartCover.piece i)
        ((actualPairwiseTaylor ω₀ φ L p.1 q.1) ∘
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (P.finiteChartCover.base i)).symm) := by
    apply holderBoundOn_zero_congr
      ((hmatrix p.1 q.1 hpfirst hqfirst i).mono_const hB)
    intro z hz
    exact (actualPairwiseTaylor_eq_chartMatrix ω₀ F hF t φ hsol α D L hL
      p.1 q.1 hpD hqD i z hz).symm
  have hrawBound (x : M) : |actualPairwiseTaylor ω₀ φ L p.1 q.1 x| ≤ (B : ℝ) := by
    obtain ⟨i, z, hz, hzx⟩ := P.finiteChartCover.interior_covers x
    rw [← hzx]
    simpa only [norm_iteratedFDeriv_zero, Function.comp_apply, Real.norm_eq_abs]
      using (hrawChart i).1 0 le_rfl z (interior_subset hz)
  let avg : ℝ := (∫ y, actualPairwiseTaylor ω₀ φ L p.1 q.1 y
      ∂(ω₀.perturb φ hsol.1).volume) /
      (ω₀.perturb φ hsol.1).volume.real Set.univ
  have havg : |avg| ≤ (B : ℝ) := by
    apply haverageBound (ω₀.perturb φ hsol.1).volume _ (B : ℝ) _ hvol rfl
    · exact (actualPairwiseTaylor_continuous ω₀ F hF t φ hsol α D L
        p.1 q.1 hpD hqD).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact hrawBound
  intro i
  have hc := hcenterHolder avg (hrawChart i) havg
  have hconst : 3 * B = (3 * C) * (‖p‖₊ + ‖q‖₊) * ‖p - q‖₊ := by
    dsimp [B]
    ring
  rw [hconst] at hc
  apply holderBoundOn_zero_congr hc
  intro z hz
  exact (actualPairwiseTaylor_centering ω₀ F hF t φ hsol α D L b hb
    p q hpD hqD hvol _).symm

end KahlerForm
