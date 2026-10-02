module

public import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientIdentity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.SegmentMatrixHolder
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.CorrectedRhsHolder
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.MatrixInverse
import CalabiYau.MongeAmpere.Continuity.Openness.SmoothBootstrap.DifferenceQuotientBounds.IntervalAverage

/-!
# Uniform translated coefficient and forcing bounds

This is the chart-local geometric input to the difference-quotient estimates. Compact containment
and the `C^{2,α}` gauge control the Hessian coefficients on every translated segment; smoothness of
the background metric and prescribed data controls their secants independently of the step size.
The segment matrices remain positive, and their inverse entries are integrable in the segment
parameter.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Matrix Set MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

open scoped ComplexOrder MatrixOrder in
private theorem posDef_segment_of_endpoints {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hC : C.PosDef)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (A + s • (C - A)).PosDef := by
  have hcomb : A + s • (C - A) = (1 - s) • A + s • C := by
    ext i j
    simp
    ring
  rw [hcomb]
  by_cases hs0 : s = 0
  · simp [hs0]
    exact hA
  · by_cases hs1 : s = 1
    · simp [hs1]
      exact hC
    · have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
      have hpos : 0 < 1 - s := sub_pos.mpr hslt
      exact (hA.smul hpos).add_posSemidef (hC.posSemidef.smul hs.1)

/-- The positive matrix on the segment from the chart matrix at `z` to its translate.
The averaging variable is explicit so the coefficient estimates can be passed through its
interval integral. -/
noncomputable def chartBootstrapSegmentMatrix (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (v : EuclideanSpace ℂ (Fin n)) (h s : ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  chartBootstrapMatrix ω₀ φ x z + s •
    (chartBootstrapMatrix ω₀ φ x (z + h • v) - chartBootstrapMatrix ω₀ φ x z)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
open scoped ComplexOrder MatrixOrder in
private theorem chartBootstrapSegmentMatrix_posDef
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    (x : M) (v : EuclideanSpace ℂ (Fin n)) (h s : ℝ)
    (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hz' : z + h • v ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (chartBootstrapSegmentMatrix ω₀ φ x v h s z).PosDef := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let B₀ := chartBootstrapMatrix ω₀ φ x z
  let B₁ := chartBootstrapMatrix ω₀ φ x (z + h • v)
  have hEq₀ := hEquation x z hz
  have hEq₁ := hEquation x (z + h • v) hz'
  have hB₀herm : B₀.IsHermitian := by
    simpa [B₀, chartBootstrapMatrix, e] using hEq₀.1
  have hB₁herm : B₁.IsHermitian := by
    simpa [B₁, chartBootstrapMatrix, e] using hEq₁.1
  have hB₀quad : ∀ w : Fin n → ℂ, w ≠ 0 →
      0 < RCLike.re (star w ⬝ᵥ (B₀ *ᵥ w)) := by
    simpa [B₀, chartBootstrapMatrix, e] using hEq₀.2.1
  have hB₁quad : ∀ w : Fin n → ℂ, w ≠ 0 →
      0 < RCLike.re (star w ⬝ᵥ (B₁ *ᵥ w)) := by
    simpa [B₁, chartBootstrapMatrix, e] using hEq₁.2.1
  have hB₀pos : B₀.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hB₀herm
    intro w hw
    exact RCLike.lt_iff_re_im.mpr
      ⟨hB₀quad w hw, (hB₀herm.im_star_dotProduct_mulVec_self w).symm⟩
  have hB₁pos : B₁.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hB₁herm
    intro w hw
    exact RCLike.lt_iff_re_im.mpr
      ⟨hB₁quad w hw, (hB₁herm.im_star_dotProduct_mulVec_self w).symm⟩
  simpa [B₀, B₁, chartBootstrapSegmentMatrix] using
    posDef_segment_of_endpoints B₀ B₁ hB₀pos hB₁pos hs

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
open scoped ComplexOrder MatrixOrder in
private theorem chartBootstrapSegmentMatrix_inverse_intervalData
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    (x : M) (v : EuclideanSpace ℂ (Fin n)) (h : ℝ)
    (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hz' : z + h • v ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∀ i j, ContinuousOn
        (fun s : ℝ ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ i j)
        (Set.Icc (0 : ℝ) 1) ∧
      IntervalIntegrable
        (fun s : ℝ ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ i j)
        MeasureTheory.volume 0 1 := by
  intro i j
  let P : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun s ↦ chartBootstrapSegmentMatrix ω₀ φ x v h s z
  have hdetCont : ContinuousOn (fun s : ℝ ↦ (P s).det) (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn
      (fun s : ℝ ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z).det)
      (Set.Icc (0 : ℝ) 1)
    fun_prop [chartBootstrapSegmentMatrix]
  have hdetNe : ∀ s ∈ Set.Icc (0 : ℝ) 1, (P s).det ≠ 0 := by
    intro s hs
    have hpos := chartBootstrapSegmentMatrix_posDef ω₀ hEquation x v h s z hz hz' hs
    change (P s).det ≠ 0
    exact ne_of_gt hpos.det_pos
  have hdetInv : ContinuousOn (fun s : ℝ ↦ ((P s).det)⁻¹) (Set.Icc (0 : ℝ) 1) :=
    hdetCont.inv₀ hdetNe
  have hAdj : ContinuousOn (fun s : ℝ ↦ (P s).adjugate i j) (Set.Icc (0 : ℝ) 1) := by
    change ContinuousOn
      (fun s : ℝ ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z).adjugate i j)
      (Set.Icc (0 : ℝ) 1)
    fun_prop [chartBootstrapSegmentMatrix]
  have hformula (s : ℝ) : (P s)⁻¹ i j = ((P s).det)⁻¹ * (P s).adjugate i j := by
    rw [Matrix.inv_def]
    simp [smul_eq_mul, Ring.inverse_eq_inv]
  have hEntry := hdetInv.mul hAdj
  have hcontinuous : ContinuousOn (fun s : ℝ ↦ (P s)⁻¹ i j) (Set.Icc (0 : ℝ) 1) := by
    refine hEntry.congr ?_
    intro s hs
    exact hformula s
  have hcontinuous' : ContinuousOn
      (fun s : ℝ ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ i j)
      (Set.Icc (0 : ℝ) 1) := by
    simpa [P] using hcontinuous
  exact ⟨hcontinuous',
    hcontinuous'.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)⟩

private theorem holderBoundOn_zero_interval_average
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α K : ℝ≥0) (hα₀ : 0 < α) (_hα₁ : α < 1)
    (U : Set E) (F : ℝ → E → ℂ)
    (hHolder : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HolderBoundOn 0 α K U (F s))
    (hIntegrable : ∀ z ∈ U,
      IntervalIntegrable (fun s ↦ F s z) MeasureTheory.volume 0 1)
    (_hContinuous : ∀ z ∈ U,
      ContinuousOn (fun s ↦ F s z) (Set.Icc (0 : ℝ) 1)) :
    HolderBoundOn 0 α K U (fun z ↦ ∫ s in (0 : ℝ)..1, F s z) := by
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (z : E) (hz : z ∈ U) :
      ‖F s z‖ ≤ (K : ℝ) := by
    have h := (hHolder s hs).1 0 le_rfl z hz
    simpa only [norm_iteratedFDeriv_zero] using h
  have hinterval (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) 1) (z : E) (hz : z ∈ U) :
      ‖F s z‖ ≤ (K : ℝ) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact hpoint s ⟨hs.1.le, hs.2⟩ z hz
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    have hbound : ‖∫ s in (0 : ℝ)..1, F s z‖ ≤ (K : ℝ) := by
      calc
        ‖∫ s in (0 : ℝ)..1, F s z‖ ≤ (K : ℝ) * |(1 : ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
            (C := (K : ℝ)) (fun s hs ↦ hinterval s hs z hz)
        _ = (K : ℝ) := by norm_num
    simpa only [norm_iteratedFDeriv_zero] using hbound
  · intro z hz w hw
    have hdiffint :
        (∫ s in (0 : ℝ)..1, F s z) - (∫ s in (0 : ℝ)..1, F s w) =
          ∫ s in (0 : ℝ)..1, (F s z - F s w) := by
      rw [intervalIntegral.integral_sub (hIntegrable z hz) (hIntegrable w hw)]
    have hnorm (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
        ‖F s z - F s w‖ ≤ (K : ℝ) * dist z w ^ (α : ℝ) := by
      let e := continuousMultilinearCurryFin0 ℝ E ℂ
      have heq : ‖e.symm (F s z) - e.symm (F s w)‖ = ‖F s z - F s w‖ := by
        rw [← e.symm.map_sub, LinearIsometryEquiv.norm_map]
      have h := (hHolder s hs).2.dist_le hz hw
      rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_apply] at h
      rw [dist_eq_norm, heq] at h
      simpa only [dist_eq_norm] using h
    have hnormint :
        ‖∫ s in (0 : ℝ)..1, (F s z - F s w)‖ ≤
          (K : ℝ) * dist z w ^ (α : ℝ) := by
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := (K : ℝ) * dist z w ^ (α : ℝ)) (fun s hs ↦ by
          have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
            rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
            exact ⟨hs.1.le, hs.2⟩
          exact hnorm s hs')
      simpa using h
    have hdist :
        dist (∫ s in (0 : ℝ)..1, F s z) (∫ s in (0 : ℝ)..1, F s w) ≤
          (K : ℝ) * dist z w ^ (α : ℝ) := by
      rw [dist_eq_norm, hdiffint]
      exact hnormint
    have havg : edist (∫ s in (0 : ℝ)..1, F s z) (∫ s in (0 : ℝ)..1, F s w) ≤
        (K : ENNReal) * edist z w ^ (α : ℝ) := by
      calc
        edist (∫ s in (0 : ℝ)..1, F s z) (∫ s in (0 : ℝ)..1, F s w) =
            ENNReal.ofReal (dist (∫ s in (0 : ℝ)..1, F s z)
              (∫ s in (0 : ℝ)..1, F s w)) := edist_dist _ _
        _ ≤ ENNReal.ofReal ((K : ℝ) * dist z w ^ (α : ℝ)) := ENNReal.ofReal_le_ofReal hdist
        _ = (K : ENNReal) * edist z w ^ (α : ℝ) := by
          rw [edist_dist, ENNReal.coe_nnreal_eq,
            ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity : 0 ≤ (α : ℝ)),
            ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ))]
    let e := continuousMultilinearCurryFin0 ℝ E ℂ
    change edist (e.symm (∫ s in (0 : ℝ)..1, F s z))
      (e.symm (∫ s in (0 : ℝ)..1, F s w)) ≤ (K : ENNReal) * edist z w ^ (α : ℝ)
    simpa only [e.symm.edist_map] using havg

open scoped ComplexOrder MatrixOrder in
private theorem compact_positiveHermitian_uniformEllipticity
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (K : Set X) (hK : IsCompact K)
    (A : X → Matrix (Fin n) (Fin n) ℂ)
    (hAcont : ∀ j k, ContinuousOn (fun z => A z j k) K)
    (hAhermitian : ∀ z ∈ K, (A z).IsHermitian)
    (hApositive : ∀ z ∈ K, ∀ v, v ≠ 0 →
      0 < RCLike.re (star v ⬝ᵥ (A z *ᵥ v))) :
    ∃ lam : ℝ≥0, 0 < lam ∧ ∀ z ∈ K,
      (A z).IsHermitian ∧ ∀ v,
        (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
  classical
  by_cases hKne : K.Nonempty
  · by_cases hn : n = 0
    · subst n
      refine ⟨1, by norm_num, ?_⟩
      intro z hz
      constructor
      · exact hAhermitian z hz
      · intro v
        have hv : v = 0 := Subsingleton.elim _ _
        subst v
        simp
    · let S : Set (Fin n → ℂ) := Metric.sphere 0 1
      have hScompact : IsCompact S := by
        simpa [S] using (isCompact_sphere (0 : Fin n → ℂ) 1)
      let T : Set (X × (Fin n → ℂ)) := K ×ˢ S
      have hTcompact : IsCompact T := hK.prod hScompact
      let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      let v₀ : Fin n → ℂ := Pi.single i₀ 1
      have hv₀norm : ‖v₀‖ = 1 := by simp [v₀, Pi.norm_single]
      have hTne : T.Nonempty := by
        obtain ⟨z, hz⟩ := hKne
        refine ⟨(z, v₀), ?_⟩
        constructor
        · exact hz
        · simpa [S, Metric.mem_sphere, dist_eq_norm] using hv₀norm
      let Q : X × (Fin n → ℂ) → ℝ := fun p =>
        RCLike.re (star p.2 ⬝ᵥ (A p.1 *ᵥ p.2))
      have hAcontProd (j k : Fin n) : ContinuousOn (fun p => A p.1 j k) T := by
        exact (hAcont j k).comp continuousOn_fst (fun p hp => hp.1)
      have hcoord (k : Fin n) :
          ContinuousOn (fun p : X × (Fin n → ℂ) => p.2 k) T := by
        fun_prop
      let inner (j : Fin n) (p : X × (Fin n → ℂ)) :=
        ∑ k, A p.1 j k * p.2 k
      have hinner (j : Fin n) : ContinuousOn (inner j) T := by
        dsimp [inner]
        apply continuousOn_finsetSum
        intro k hk
        exact (hAcontProd j k).mul (hcoord k)
      have hterm (j : Fin n) : ContinuousOn
          (fun p : X × (Fin n → ℂ) =>
            Complex.re (star (p.2 j) * inner j p)) T := by
        have hm : ContinuousOn (fun p => star (p.2 j) * inner j p) T := by
          exact (hcoord j).star.mul (hinner j)
        exact Complex.continuous_re.continuousOn.comp hm (fun p hp => Set.mem_univ _)
      have hQsum : ContinuousOn (fun p => ∑ j, Complex.re
          (star (p.2 j) * ∑ k, A p.1 j k * p.2 k)) T := by
        apply continuousOn_finsetSum
        intro j hj
        exact hterm j
      have hQcont : ContinuousOn Q T := by
        refine hQsum.congr ?_
        intro p hp
        simp [Q, Matrix.mulVec, dotProduct]
      have hQpos (p : X × (Fin n → ℂ)) (hp : p ∈ T) :
          0 < Q p := by
        have hz : p.1 ∈ K := hp.1
        have hvSphere : p.2 ∈ S := hp.2
        have hvnorm : ‖p.2‖ = 1 := by
          have hs := Metric.mem_sphere.mp hvSphere
          simpa [dist_eq_norm] using hs
        have hvne : p.2 ≠ 0 := by
          intro hv
          simp [hv] at hvnorm
        exact hApositive p.1 hz p.2 hvne
      obtain ⟨p₀, hp₀, hmin⟩ := hTcompact.exists_isMinOn hTne hQcont
      let δ : ℝ := Q p₀
      have hδ : 0 < δ := hQpos p₀ hp₀
      have hquad (z : X) (hz : z ∈ K)
          (v : Fin n → ℂ) :
          δ * ‖v‖ ^ 2 ≤ RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
        by_cases hv : v = 0
        · simp [hv]
        · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
          let u : Fin n → ℂ := (‖v‖⁻¹ : ℝ) • v
          have hunorm : ‖u‖ = 1 := by
            calc
              ‖u‖ = ‖(‖v‖⁻¹ : ℝ) • v‖ := rfl
              _ = ‖‖v‖⁻¹‖ * ‖v‖ := norm_smul _ _
              _ = ‖v‖⁻¹ * ‖v‖ := by
                rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
              _ = 1 := by field_simp [ne_of_gt hnorm]
          have huSphere : u ∈ S := by
            simpa [S, Metric.mem_sphere, dist_eq_norm] using hunorm
          have hmin' : δ ≤ Q (z, u) := by
            dsimp [δ]
            exact (isMinOn_iff.mp hmin) (z, u) ⟨hz, huSphere⟩
          have hscale : Q (z, u) = (‖v‖⁻¹)^2 *
              RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
            dsimp [Q, u]
            simp [star_smul, Matrix.mulVec_smul, dotProduct_smul]
            ring
          have hmin'' : δ ≤ (‖v‖⁻¹)^2 *
              RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
            dsimp [δ] at hmin'
            rw [hscale] at hmin'
            exact hmin'
          have hmul := mul_le_mul_of_nonneg_left hmin'' (sq_nonneg ‖v‖)
          have hmul' : δ * ‖v‖ ^ 2 ≤ RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
            calc
              δ * ‖v‖ ^ 2 = ‖v‖ ^ 2 * δ := by ring
              _ ≤ ‖v‖ ^ 2 * ((‖v‖⁻¹)^2 *
                  RCLike.re (star v ⬝ᵥ (A z *ᵥ v))) := hmul
              _ = RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
                field_simp [ne_of_gt hnorm]
          exact hmul'
      let lam : ℝ≥0 := ⟨δ / n, (div_nonneg hδ.le (by positivity))⟩
      have hlam : 0 < lam := by
        dsimp [lam]
        exact div_pos hδ (by exact_mod_cast Nat.pos_of_ne_zero hn)
      refine ⟨lam, hlam, ?_⟩
      intro z hz
      constructor
      · exact hAhermitian z hz
      · intro v
        have hsum : ∑ j, ‖v j‖ ^ 2 ≤ (n : ℝ) * ‖v‖ ^ 2 := by
          calc
            ∑ j, ‖v j‖ ^ 2 ≤ ∑ j : Fin n, ‖v‖ ^ 2 :=
              Finset.sum_le_sum fun j hj => by
                have h : ‖v j‖ ≤ ‖v‖ := by
                  have hnn : ‖v j‖₊ ≤ Finset.univ.sup
                      (fun i : Fin n => ‖v i‖₊) :=
                    Finset.le_sup (f := fun i : Fin n => ‖v i‖₊) (Finset.mem_univ j)
                  calc
                    ‖v j‖ = (‖v j‖₊ : ℝ) := by norm_cast
                    _ ≤ (↑(Finset.univ.sup (fun i : Fin n => ‖v i‖₊) : ℝ≥0) : ℝ) := by
                      exact_mod_cast hnn
                    _ = ‖v‖ := by rfl
                simpa [pow_two] using (mul_self_le_mul_self (norm_nonneg _) h)
            _ = (n : ℝ) * ‖v‖ ^ 2 := by simp
        calc
          (lam : ℝ) * ∑ j, ‖v j‖ ^ 2 ≤ δ * ‖v‖ ^ 2 := by
            dsimp [lam]
            calc
              (δ / (n : ℝ)) * ∑ j, ‖v j‖ ^ 2 ≤
                  (δ / (n : ℝ)) * ((n : ℝ) * ‖v‖ ^ 2) :=
                mul_le_mul_of_nonneg_left hsum (div_nonneg hδ.le (by positivity))
              _ = δ * ‖v‖ ^ 2 := by
                field_simp [ne_of_gt (by exact_mod_cast Nat.pos_of_ne_zero hn)]
          _ ≤ RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := hquad z hz v
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact (hKne ⟨z, hz⟩).elim

open scoped ComplexOrder MatrixOrder in
private theorem compact_parameter_family_uniformEllipticity
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}
    (P : Set X) (hP : IsCompact P) (K : Set Y) (hK : IsCompact K)
    (A : X → Y → Matrix (Fin n) (Fin n) ℂ)
    (hAcont : ∀ j k, ContinuousOn (fun q : X × Y ↦ A q.1 q.2 j k) (P ×ˢ K))
    (hAherm : ∀ p ∈ P, ∀ z ∈ K, (A p z).IsHermitian)
    (hApos : ∀ p ∈ P, ∀ z ∈ K, ∀ v, v ≠ 0 →
      0 < RCLike.re (star v ⬝ᵥ (A p z *ᵥ v))) :
    ∃ lam : ℝ≥0, 0 < lam ∧ ∀ p ∈ P, ∀ z ∈ K,
      (A p z).IsHermitian ∧ ∀ v,
        (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤ RCLike.re (star v ⬝ᵥ (A p z *ᵥ v)) := by
  let Q : Set (X × Y) := P ×ˢ K
  let A' : X × Y → Matrix (Fin n) (Fin n) ℂ := fun q ↦ A q.1 q.2
  have hQcompact : IsCompact Q := hP.prod hK
  have hAherm' : ∀ q ∈ Q, (A' q).IsHermitian := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    exact hAherm p hp z hz
  have hApos' : ∀ q ∈ Q, ∀ v, v ≠ 0 →
      0 < RCLike.re (star v ⬝ᵥ (A' q *ᵥ v)) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩ v hv
    exact hApos p hp z hz v hv
  obtain ⟨lam, hlam, hbound⟩ :=
    compact_positiveHermitian_uniformEllipticity Q hQcompact A' hAcont hAherm' hApos'
  refine ⟨lam, hlam, ?_⟩
  intro p hp z hz
  exact hbound (p, z) ⟨hp, hz⟩

open scoped ComplexOrder MatrixOrder in
private theorem compact_positiveHermitian_inverse_uniformEllipticity
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (K : Set X) (hK : IsCompact K)
    (A : X → Matrix (Fin n) (Fin n) ℂ)
    (hAcont : ∀ j k, ContinuousOn (fun z ↦ A z j k) K)
    (hApos : ∀ z ∈ K, (A z).PosDef) :
    ∃ lam : ℝ≥0, 0 < lam ∧ ∀ z ∈ K,
      (A z)⁻¹.IsHermitian ∧ ∀ v,
        (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤
          RCLike.re (star v ⬝ᵥ ((A z)⁻¹ *ᵥ v)) := by
  classical
  have hAmat : ContinuousOn A K := by
    apply continuousOn_pi.2
    intro i
    apply continuousOn_pi.2
    intro j
    exact hAcont i j
  have hA : Continuous (fun z : K ↦ A z.1) :=
    continuousOn_iff_continuous_domRestrict.mp hAmat
  have hdet : Continuous (fun z : K ↦ (A z.1).det) := hA.matrix_det
  have hdetne : ∀ z : K, (A z.1).det ≠ 0 := by
    intro z
    exact ne_of_gt (hApos z.1 z.2).det_pos
  have hdetInv : Continuous (fun z : K ↦ ((A z.1).det)⁻¹) := hdet.inv₀ hdetne
  have hAdj : Continuous (fun z : K ↦ (A z.1).adjugate) := hA.matrix_adjugate
  have hInv : Continuous (fun z : K ↦ (A z.1)⁻¹) := by
    have h := hdetInv.smul hAdj
    refine h.congr ?_
    intro z
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv]
  have hInvCont : ∀ i j, ContinuousOn (fun z ↦ (A z)⁻¹ i j) K := by
    intro i j
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_apply_apply i j).comp hInv
  apply compact_positiveHermitian_uniformEllipticity K hK
    (fun z ↦ (A z)⁻¹) hInvCont
  · intro z hz
    exact (hApos z hz).inv.isHermitian
  · intro z hz v hv
    exact (RCLike.pos_iff.mp ((hApos z hz).inv.dotProduct_mulVec_pos hv)).1

open scoped ComplexOrder MatrixOrder in
private theorem compact_parameter_family_inverse_uniformEllipticity
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}
    (P : Set X) (hP : IsCompact P) (K : Set Y) (hK : IsCompact K)
    (A : X → Y → Matrix (Fin n) (Fin n) ℂ)
    (hAcont : ∀ j k, ContinuousOn (fun q : X × Y ↦ A q.1 q.2 j k) (P ×ˢ K))
    (hApos : ∀ p ∈ P, ∀ z ∈ K, (A p z).PosDef) :
    ∃ lam : ℝ≥0, 0 < lam ∧ ∀ p ∈ P, ∀ z ∈ K,
      (A p z)⁻¹.IsHermitian ∧ ∀ v,
        (lam : ℝ) * ∑ i, ‖v i‖ ^ 2 ≤
          RCLike.re (star v ⬝ᵥ ((A p z)⁻¹ *ᵥ v)) := by
  let Q : Set (X × Y) := P ×ˢ K
  let A' : X × Y → Matrix (Fin n) (Fin n) ℂ := fun q ↦ A q.1 q.2
  have hQcompact : IsCompact Q := hP.prod hK
  have hApos' : ∀ q ∈ Q, (A' q).PosDef := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    exact hApos p hp z hz
  obtain ⟨lam, hlam, hbound⟩ :=
    compact_positiveHermitian_inverse_uniformEllipticity Q hQcompact A' hAcont hApos'
  refine ⟨lam, hlam, ?_⟩
  intro p hp z hz
  exact hbound (p, z) ⟨hp, hz⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem exists_uniform_small_chart_translate
    (K target : Set (EuclideanSpace ℂ (Fin n)))
    (hK : IsCompact K) (hKtarget : K ⊆ target) (htarget : IsOpen target)
    (v : EuclideanSpace ℂ (Fin n)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, |h| < δ → ∀ z ∈ K, z + h • v ∈ target := by
  let N : Set (EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n)) :=
    {p | p.1 + p.2 ∈ target}
  have hNopen : IsOpen N := by
    have hadd : Continuous fun p : EuclideanSpace ℂ (Fin n) × EuclideanSpace ℂ (Fin n) ↦
        p.1 + p.2 := by fun_prop
    exact htarget.preimage hadd
  have hN : K ×ˢ ({0} : Set (EuclideanSpace ℂ (Fin n))) ⊆ N := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    have hw0 : w = 0 := Set.mem_singleton_iff.mp hw
    simp [N, hw0, hKtarget hz]
  obtain ⟨V, W, _hVopen, hWopen, hKV, h0W, hVW⟩ :=
    generalized_tube_lemma hK isCompact_singleton hNopen hN
  have h0 : (0 : EuclideanSpace ℂ (Fin n)) ∈ W := h0W (Set.mem_singleton 0)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hWopen 0 h0
  let δ : ℝ := ε / (2 * (1 + ‖v‖))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro h hh z hz
  have hdisp : ‖h • v‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |h| * ‖v‖ ≤ δ * ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt hh) (norm_nonneg _)
      _ ≤ δ * (1 + ‖v‖) := by gcongr; linarith [norm_nonneg v]
      _ = ε / 2 := by dsimp [δ]; field_simp
      _ < ε := by linarith
  have hhv : h • v ∈ W := by
    apply hball
    apply Metric.mem_ball.mpr
    simpa [dist_eq_norm] using hdisp
  have hpair : (z, h • v) ∈ V ×ˢ W := ⟨hKV hz, hhv⟩
  have hsum : z + h • v ∈ target := hVW hpair
  simpa [N] using hsum

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartBootstrapMatrix_entry_continuousOn
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (x : M) (j k : Fin n) :
    ContinuousOn (fun z ↦ chartBootstrapMatrix ω₀ φ x z j k)
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let f : EuclideanSpace ℂ (Fin n) → ℝ := φ ∘ e.symm
  have hφOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) 2 φ Set.univ :=
    contMDiffOn_univ.mpr hφ.1.1
  have hf : ContDiffOn ℝ 2 f e.target := by
    have hchart := hφOn.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
    exact hchart.contDiffOn
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  have hD : ContDiffOn ℝ 1 (fderiv ℝ f) e.target := by
    apply hf.fderiv_of_isOpen hopen
    apply WithTop.coe_le_coe.mpr
    norm_num
  have hD₂ : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ f)) e.target := by
    apply hD.fderiv_of_isOpen hopen
    apply WithTop.coe_le_coe.mpr
    norm_num
  have hD₂eval (a b : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ 0 (fun z ↦ fderiv ℝ (fderiv ℝ f) z a b) e.target := by
    have ha : ContDiffOn ℝ 0 (fun _ : EuclideanSpace ℂ (Fin n) ↦ a) e.target := contDiffOn_const
    have hb : ContDiffOn ℝ 0 (fun _ : EuclideanSpace ℂ (Fin n) ↦ b) e.target := contDiffOn_const
    exact (hD₂.clm_apply ha).clm_apply hb
  have hFormula : ContDiffOn ℝ 0 (fun z ↦
      ((fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) : ℂ) +
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) +
        Complex.I * (fderiv ℝ (fderiv ℝ f) z (EuclideanSpace.single j 1)
          (Complex.I • EuclideanSpace.single k 1) -
        fderiv ℝ (fderiv ℝ f) z (Complex.I • EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1))) / 4) e.target := by
    simp only [← Complex.ofRealCLM_apply]
    fun_prop
  have hHess : ContDiffOn ℝ 0 (fun z ↦ complexHessian f z j k) e.target := by
    apply hFormula.congr
    intro z hz
    rw [complexHessian_apply ((hf z hz).contDiffAt (hopen.mem_nhds hz))]
  have hmetric : ContDiffOn ℝ ∞ (fun z ↦ ω₀.metricInChart x z j k) e.target :=
    ω₀.contDiffOn_metricInChart x j k
  change ContinuousOn (fun z ↦ ω₀.metricInChart x z j k + complexHessian f z j k) e.target
  exact hmetric.continuousOn.add hHess.continuousOn

set_option maxHeartbeats 500000 in
omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
open scoped ComplexOrder MatrixOrder in
private theorem exists_uniform_chart_segment_ellipticity
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    (x : M) (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) :
    ∃ δ lam : ℝ≥0, 0 < δ ∧ 0 < lam ∧
      ∀ h : ℝ, |h| < (δ : ℝ) → ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsUniformlyEllipticOn
          (fun z ↦ chartBootstrapSegmentMatrix ω₀ φ x v h s z) lam K := by
  let target := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  have htarget : IsOpen target := isOpen_extChartAt_target x
  obtain ⟨δ₀, hδ₀, htranslate⟩ :=
    exists_uniform_small_chart_translate K target hK hKtarget htarget v
  let δ : ℝ≥0 := ⟨δ₀ / 2, by positivity⟩
  have hδreal : (0 : ℝ) < (δ : ℝ) := by
    change (0 : ℝ) < δ₀ / 2
    linarith
  have hδ : 0 < δ := NNReal.coe_pos.mp hδreal
  let H : Set ℝ := Set.Icc (-(δ : ℝ)) (δ : ℝ)
  let S : Set ℝ := Set.Icc (0 : ℝ) 1
  let P : Set (ℝ × ℝ) := H ×ˢ S
  have hP : IsCompact P := isCompact_Icc.prod isCompact_Icc
  have hKcompact : IsCompact K := hK
  let B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ chartBootstrapMatrix ω₀ φ x z
  let A : ℝ × ℝ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun p z ↦ B z + p.2 • (B (z + p.1 • v) - B z)
  have hAcont : ∀ j k,
      ContinuousOn (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦
        A q.1 q.2 j k) (P ×ˢ K) := by
    intro j k
    have hBase := chartBootstrapMatrix_entry_continuousOn ω₀ hφ x j k
    have hPoint : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦ q.2) (P ×ˢ K) := by
      fun_prop
    have hStep : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦ q.2 + q.1.1 • v)
        (P ×ˢ K) := by
      fun_prop
    have hBase' : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦
          chartBootstrapMatrix ω₀ φ x q.2 j k) (P ×ˢ K) :=
      hBase.comp hPoint (fun q hq ↦ hKtarget hq.2)
    have hStep' : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦
          chartBootstrapMatrix ω₀ φ x (q.2 + q.1.1 • v) j k) (P ×ˢ K) := by
      apply hBase.comp hStep
      intro q hq
      have hh : q.1.1 ∈ H := hq.1.1
      have habs' : |q.1.1| ≤ (δ : ℝ) := abs_le.mpr ⟨hh.1, hh.2⟩
      have hδlt : (δ : ℝ) < δ₀ := by
        change δ₀ / 2 < δ₀
        linarith
      have habs : |q.1.1| < δ₀ := lt_of_le_of_lt habs' hδlt
      exact htranslate q.1.1 habs q.2 hq.2
    have hS : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦ q.1.2) (P ×ˢ K) := by
      fun_prop
    change ContinuousOn (fun q ↦
      B q.2 j k + q.1.2 • (B (q.2 + q.1.1 • v) j k - B q.2 j k)) (P ×ˢ K)
    exact hBase'.add (hS.smul (hStep'.sub hBase'))
  have hAherm : ∀ p ∈ P, ∀ z ∈ K, (A p z).IsHermitian := by
    intro p hp z hz
    have hh : |p.1| < δ₀ := by
      have hpH : p.1 ∈ H := hp.1
      have hpabs : |p.1| ≤ (δ : ℝ) := abs_le.mpr ⟨hpH.1, hpH.2⟩
      have hδlt : (δ : ℝ) < δ₀ := by
        change δ₀ / 2 < δ₀
        linarith
      exact lt_of_le_of_lt hpabs hδlt
    have hz0 : z ∈ target := hKtarget hz
    have hz1 : z + p.1 • v ∈ target := htranslate p.1 hh z hz
    have hpos := chartBootstrapSegmentMatrix_posDef ω₀ hEquation x v p.1 p.2 z hz0 hz1 hp.2
    simpa [A, B, chartBootstrapSegmentMatrix] using hpos.isHermitian
  have hApos : ∀ p ∈ P, ∀ z ∈ K, ∀ w, w ≠ 0 →
      0 < RCLike.re (star w ⬝ᵥ (A p z *ᵥ w)) := by
    intro p hp z hz w hw
    have hh : |p.1| < δ₀ := by
      have hpH : p.1 ∈ H := hp.1
      have hpabs : |p.1| ≤ (δ : ℝ) := abs_le.mpr ⟨hpH.1, hpH.2⟩
      have hδlt : (δ : ℝ) < δ₀ := by
        change δ₀ / 2 < δ₀
        linarith
      exact lt_of_le_of_lt hpabs hδlt
    have hz0 : z ∈ target := hKtarget hz
    have hz1 : z + p.1 • v ∈ target := htranslate p.1 hh z hz
    have hpos := chartBootstrapSegmentMatrix_posDef ω₀ hEquation x v p.1 p.2 z hz0 hz1 hp.2
    have hquad := hpos.dotProduct_mulVec_pos hw
    have hreal := (RCLike.pos_iff.mp hquad).1
    simpa [A, B, chartBootstrapSegmentMatrix] using hreal
  obtain ⟨lam, hlam, hUniform⟩ :=
    compact_parameter_family_uniformEllipticity P hP K hKcompact A hAcont hAherm hApos
  refine ⟨δ, lam, hδ, hlam, ?_⟩
  intro h hh s hs
  have hhH : h ∈ H := by
    dsimp [H]
    exact abs_le.mp (le_of_lt hh)
  have hp : (h, s) ∈ P := ⟨hhH, hs⟩
  have hEll := hUniform (h, s) hp
  change IsUniformlyEllipticOn (fun z ↦ chartBootstrapSegmentMatrix ω₀ φ x v h s z) lam K
  intro z hz
  have hPoint := hEll z hz
  simpa [A, B, chartBootstrapSegmentMatrix] using hPoint

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem exists_uniform_chart_segment_geometry
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    (x : M) (U : Set (EuclideanSpace ℂ (Fin n)))
    (hUcompact : IsCompact (closure U))
    (hUchart : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) :
    ∃ δ lam : ℝ≥0, 0 < δ ∧ 0 < lam ∧
      ∀ h : ℝ, |h| < δ →
        (∀ z ∈ U, z + h • v ∈
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1,
          IsUniformlyEllipticOn
            (fun z ↦ chartBootstrapSegmentMatrix ω₀ φ x v h s z) lam U) ∧
        ∀ z ∈ U, ∀ j l,
          IntervalIntegrable
            (fun s ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ j l)
            MeasureTheory.volume 0 1 ∧
          ContinuousOn
            (fun s ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ j l)
            (Set.Icc (0 : ℝ) 1) := by
  let target := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  obtain ⟨δraw, hδraw, htranslate⟩ :=
    exists_uniform_small_chart_translate (closure U) target hUcompact hUchart
      (isOpen_extChartAt_target x) v
  obtain ⟨δell, lam, hδell, hlam, hell⟩ :=
    exists_uniform_chart_segment_ellipticity ω₀ hφ hEquation x (closure U)
      hUcompact hUchart v
  let δgeo : ℝ≥0 := ⟨δraw / 2, by positivity⟩
  let δ := min δgeo δell
  have hδgeo : 0 < δgeo := by
    apply NNReal.coe_pos.mp
    change 0 < δraw / 2
    linarith
  have hδ : 0 < δ := lt_min hδgeo hδell
  refine ⟨δ, lam, hδ, hlam, ?_⟩
  intro h hh
  have hstep : |h| < (δgeo : ℝ) ∧ |h| < (δell : ℝ) := by
    simpa only [δ, NNReal.coe_min, lt_min_iff] using hh
  have hraw : |h| < δraw := by
    have hhalf : (δgeo : ℝ) < δraw := by
      change δraw / 2 < δraw
      linarith
    exact lt_trans hstep.1 hhalf
  have htranslateU : ∀ z ∈ U, z + h • v ∈ target := by
    intro z hz
    exact htranslate h hraw z (subset_closure hz)
  have hellU : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      IsUniformlyEllipticOn
        (fun z ↦ chartBootstrapSegmentMatrix ω₀ φ x v h s z) lam U := by
    intro s hs z hz
    exact hell h hstep.2 s hs z (subset_closure hz)
  refine ⟨htranslateU, hellU, ?_⟩
  intro z hz j l
  have hz' : z ∈ target := hUchart (subset_closure hz)
  have htranslated := htranslateU z hz
  have hdata := chartBootstrapSegmentMatrix_inverse_intervalData ω₀ hEquation x v h z
    hz' htranslated j l
  exact ⟨hdata.2, hdata.1⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
open scoped ComplexOrder MatrixOrder in
private theorem exists_uniform_chart_inverse_segment_ellipticity
    (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    (x : M) (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) :
    ∃ δ lam : ℝ≥0, 0 < δ ∧ 0 < lam ∧
      ∀ h : ℝ, |h| < (δ : ℝ) → ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsUniformlyEllipticOn
          (fun z ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹) lam K := by
  let target := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
  have htarget : IsOpen target := isOpen_extChartAt_target x
  obtain ⟨δ₀, hδ₀, htranslate⟩ :=
    exists_uniform_small_chart_translate K target hK hKtarget htarget v
  let δ : ℝ≥0 := ⟨δ₀ / 2, by positivity⟩
  have hδreal : (0 : ℝ) < (δ : ℝ) := by
    change (0 : ℝ) < δ₀ / 2
    linarith
  have hδ : 0 < δ := NNReal.coe_pos.mp hδreal
  let H : Set ℝ := Set.Icc (-(δ : ℝ)) (δ : ℝ)
  let S : Set ℝ := Set.Icc (0 : ℝ) 1
  let P : Set (ℝ × ℝ) := H ×ˢ S
  have hP : IsCompact P := isCompact_Icc.prod isCompact_Icc
  let B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z ↦ chartBootstrapMatrix ω₀ φ x z
  let A : ℝ × ℝ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun p z ↦ B z + p.2 • (B (z + p.1 • v) - B z)
  have hAcont : ∀ j k,
      ContinuousOn (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦
        A q.1 q.2 j k) (P ×ˢ K) := by
    intro j k
    have hBase := chartBootstrapMatrix_entry_continuousOn ω₀ hφ x j k
    have hPoint : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦ q.2) (P ×ˢ K) := by fun_prop
    have hStep : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦ q.2 + q.1.1 • v)
        (P ×ˢ K) := by fun_prop
    have hBase' : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦
          chartBootstrapMatrix ω₀ φ x q.2 j k) (P ×ˢ K) :=
      hBase.comp hPoint (fun q hq ↦ hKtarget hq.2)
    have hStep' : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦
          chartBootstrapMatrix ω₀ φ x (q.2 + q.1.1 • v) j k) (P ×ˢ K) := by
      apply hBase.comp hStep
      intro q hq
      have hh : q.1.1 ∈ H := hq.1.1
      have habs' : |q.1.1| ≤ (δ : ℝ) := abs_le.mpr ⟨hh.1, hh.2⟩
      have hδlt : (δ : ℝ) < δ₀ := by
        change δ₀ / 2 < δ₀
        linarith
      exact htranslate q.1.1 (lt_of_le_of_lt habs' hδlt) q.2 hq.2
    have hS : ContinuousOn
        (fun q : (ℝ × ℝ) × EuclideanSpace ℂ (Fin n) ↦ q.1.2) (P ×ˢ K) := by fun_prop
    change ContinuousOn (fun q ↦
      B q.2 j k + q.1.2 • (B (q.2 + q.1.1 • v) j k - B q.2 j k)) (P ×ˢ K)
    exact hBase'.add (hS.smul (hStep'.sub hBase'))
  have hApos : ∀ p ∈ P, ∀ z ∈ K, (A p z).PosDef := by
    intro p hp z hz
    have hpH : p.1 ∈ H := hp.1
    have hpabs : |p.1| ≤ (δ : ℝ) := abs_le.mpr ⟨hpH.1, hpH.2⟩
    have hδlt : (δ : ℝ) < δ₀ := by
      change δ₀ / 2 < δ₀
      linarith
    have hz1 : z + p.1 • v ∈ target :=
      htranslate p.1 (lt_of_le_of_lt hpabs hδlt) z hz
    simpa [A, B, chartBootstrapSegmentMatrix] using
      chartBootstrapSegmentMatrix_posDef ω₀ hEquation x v p.1 p.2 z
        (hKtarget hz) hz1 hp.2
  obtain ⟨lam, hlam, hUniform⟩ :=
    compact_parameter_family_inverse_uniformEllipticity P hP K hK A hAcont hApos
  refine ⟨δ, lam, hδ, hlam, ?_⟩
  intro h hh s hs z hz
  have hhH : h ∈ H := by
    dsimp [H]
    exact abs_le.mp hh.le
  have hp : (h, s) ∈ P := ⟨hhH, hs⟩
  simpa [A, B, chartBootstrapSegmentMatrix] using hUniform (h, s) hp z hz

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem averagedChartInverse_entry_holderBoundOn_of_segment
    (ω₀ : KahlerForm n M) (φ : M → ℝ) (x : M)
    (U : Set (EuclideanSpace ℂ (Fin n))) (v : EuclideanSpace ℂ (Fin n))
    (α δ lam Kmat : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1) (hlam : 0 < lam)
    (hEll : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      IsUniformlyEllipticOn (chartBootstrapSegmentMatrix ω₀ φ x v h s) lam U)
    (hMat : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j l,
      HolderBoundOn 0 α Kmat U (fun z => chartBootstrapSegmentMatrix ω₀ φ x v h s z j l))
    (hInt : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ z ∈ U, ∀ j l,
      IntervalIntegrable (fun s => (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ j l)
        MeasureTheory.volume 0 1)
    (hCont : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ z ∈ U, ∀ j l,
      ContinuousOn (fun s => (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ j l)
        (Set.Icc (0 : ℝ) 1)) :
    ∃ CA : ℝ≥0, ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ j l,
      HolderBoundOn 0 α CA U (fun z ↦ averagedChartInverse ω₀ φ x v h z j l) := by
  let P : Set ℝ := {h | h ≠ 0 ∧ |h| < δ}
  obtain ⟨CA, hCA⟩ := exists_uniform_holderBoundOn_matrix_inverse
    α lam Kmat hα₀ hα₁ hlam U P
    (fun h s z => chartBootstrapSegmentMatrix ω₀ φ x v h s z)
    (fun h hh => hEll h hh.1 hh.2) (fun h hh => hMat h hh.1 hh.2)
  refine ⟨CA, ?_⟩
  intro h hne hh j l
  have hAvg := holderBoundOn_interval_average α CA hα₀ hα₁ U
    (fun s z => (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ j l)
    (fun s hs => hCA h ⟨hne, hh⟩ s hs j l)
    (fun z hz => hInt h hne hh z hz j l)
    (fun z hz => hCont h hne hh z hz j l)
  simpa only [averagedChartInverse, chartBootstrapSegmentMatrix] using hAvg

private theorem ellipticity_mono_constant
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (U : Set (EuclideanSpace ℂ (Fin n))) {mu lam : ℝ≥0}
    (hmu : mu ≤ lam) (hA : IsUniformlyEllipticOn A lam U) :
    IsUniformlyEllipticOn A mu U := by
  intro z hz
  refine ⟨(hA z hz).1, ?_⟩
  intro v
  exact (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hmu)
    (Finset.sum_nonneg fun i _ => sq_nonneg ‖v i‖)).trans ((hA z hz).2 v)

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- The local chart estimates used by the averaged-inverse and average lemmas. The constants and
step radius are uniform in `h`; the segment parameter ranges over the closed unit interval. -/
theorem exists_uniform_chart_segment_bounds
    (ω₀ : KahlerForm n M) (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    {G φ : M → ℝ}
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ω₀.SolvesMongeAmpereC2 G φ)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (hφGauge : HasFiniteChartHolderGauge cover 2 α φ)
    (hEquation : HasChartLogDetEquation ω₀ G φ)
    (x : M) (U : Set (EuclideanSpace ℂ (Fin n)))
    (hU : IsOpen U) (hUcompact : IsCompact (closure U))
    (hUchart : closure U ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (v : EuclideanSpace ℂ (Fin n)) :
    ∃ δ lam Kmat Krhs : ℝ≥0, 0 < δ ∧ 0 < lam ∧
      ∀ h : ℝ, h ≠ 0 → |h| < δ →
        (∀ z ∈ U, z + h • v ∈
          (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) ∧
          IsUniformlyEllipticOn
              (fun z ↦ averagedChartInverse ω₀ φ x v h z) lam U ∧
            (∀ s ∈ Set.Icc (0 : ℝ) 1,
              IsUniformlyEllipticOn
                (fun z ↦ chartBootstrapSegmentMatrix ω₀ φ x v h s z) lam U) ∧
            (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j l,
              HolderBoundOn 0 α Kmat U
                (fun z ↦ chartBootstrapSegmentMatrix ω₀ φ x v h s z j l)) ∧
            (∀ z ∈ U, ∀ j l,
              IntervalIntegrable
                (fun s ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ j l)
                MeasureTheory.volume 0 1) ∧
            (∀ z ∈ U, ∀ j l,
              ContinuousOn
                (fun s ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ j l)
                (Set.Icc (0 : ℝ) 1)) ∧
            HolderBoundOn 0 α Krhs U (chartDifferenceQuotientRhs ω₀ G φ x v h) := by
  classical
  have _hU : IsOpen U := hU
  obtain ⟨δgeo, lamSegment, hδgeo, hlamSegment, hGeometry⟩ :=
    exists_uniform_chart_segment_geometry ω₀ hφ hEquation x U hUcompact hUchart v
  obtain ⟨δinv, lamInv, hδinv, hlamInv, hInverse⟩ :=
    exists_uniform_chart_inverse_segment_ellipticity ω₀ hφ hEquation x (closure U)
      hUcompact hUchart v
  obtain ⟨δmat, Kmat, hδmat, hMatRaw⟩ :=
    exists_uniform_chart_segment_holderBoundOn ω₀ α hα₁ φ hφ.1.1 cover hφGauge
      x U hUcompact hUchart v
  let δA := min δgeo (min δinv δmat)
  have hδA : 0 < δA := lt_min hδgeo (lt_min hδinv hδmat)
  have hStepA (h : ℝ) (hh : |h| < (δA : ℝ)) :
      |h| < (δgeo : ℝ) ∧ |h| < (δinv : ℝ) ∧ |h| < (δmat : ℝ) := by
    simpa only [δA, NNReal.coe_min, lt_min_iff] using hh
  have hTranslate (h : ℝ) (hh : |h| < (δA : ℝ)) (z) (hz : z ∈ U) :
      z + h • v ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target :=
    (hGeometry h (hStepA h hh).1).1 z hz
  have hSegment (h : ℝ) (_hne : h ≠ 0) (hh : |h| < (δA : ℝ)) :
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsUniformlyEllipticOn (chartBootstrapSegmentMatrix ω₀ φ x v h s) lamSegment U :=
    (hGeometry h (hStepA h hh).1).2.1
  have hMat (h : ℝ) (_hne : h ≠ 0) (hh : |h| < (δA : ℝ)) :
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j l, HolderBoundOn 0 α Kmat U
        (fun z => chartBootstrapSegmentMatrix ω₀ φ x v h s z j l) := by
    simpa only [chartBootstrapSegmentMatrix] using hMatRaw h (hStepA h hh).2.2
  have hInterval (h : ℝ) (hh : |h| < (δA : ℝ)) (z) (hz : z ∈ U) (j l : Fin n) :=
    (hGeometry h (hStepA h hh).1).2.2 z hz j l
  have hInvFamily (h : ℝ) (hh : |h| < (δA : ℝ)) :
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsUniformlyEllipticOn
          (fun z ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹) lamInv U := by
    intro s hs z hz
    exact hInverse h (hStepA h hh).2.1 s hs z (subset_closure hz)
  obtain ⟨CA, hAverageEntry⟩ := averagedChartInverse_entry_holderBoundOn_of_segment
    ω₀ φ x U v α δA lamSegment Kmat hα₀ hα₁ hlamSegment hSegment hMat
    (fun h _ hh z hz j l => (hInterval h hh z hz j l).1)
    (fun h _ hh z hz j l => (hInterval h hh z hz j l).2)
  obtain ⟨δrhs, Krhs, hδrhs, _hδrhsA, hRhs⟩ :=
    exists_uniform_chartDifferenceQuotientRhs_holderBoundOn_of_average
      ω₀ φ hG x U hUcompact hUchart v α hα₁ δA CA hδA hAverageEntry
  let δ := min δA δrhs
  let lam := min lamSegment lamInv
  have hδ : 0 < δ := lt_min hδA hδrhs
  have hlam : 0 < lam := lt_min hlamSegment hlamInv
  refine ⟨δ, lam, Kmat, Krhs, hδ, hlam, ?_⟩
  intro h hne hh
  have hStep : |h| < (δA : ℝ) ∧ |h| < (δrhs : ℝ) := by
    simpa only [δ, NNReal.coe_min, lt_min_iff] using hh
  have hRhsData := hRhs h hne hStep.2
  have hInvAverage : IsUniformlyEllipticOn
      (fun z ↦ averagedChartInverse ω₀ φ x v h z) lam U := by
    have hContinuous : ∀ z ∈ U, ∀ i j,
        ContinuousOn
          (fun s ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹ i j)
          (Set.Icc (0 : ℝ) 1) := by
      intro z hz i j
      exact (hInterval h hStep.1 z hz i j).2
    have hFamily : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        IsUniformlyEllipticOn
          (fun z ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹) lam U := by
      intro s hs
      apply ellipticity_mono_constant _ U (min_le_right lamSegment lamInv)
      exact hInvFamily h hStep.1 s hs
    exact isUniformlyEllipticOn_intervalAverage
      (fun s z ↦ (chartBootstrapSegmentMatrix ω₀ φ x v h s z)⁻¹) U lam
      hContinuous hFamily
  have hSegmentEll : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      IsUniformlyEllipticOn
        (fun z ↦ chartBootstrapSegmentMatrix ω₀ φ x v h s z) lam U := by
    intro s hs
    apply ellipticity_mono_constant _ U (min_le_left lamSegment lamInv)
    exact hSegment h hne hStep.1 s hs
  refine ⟨hRhsData.1, hInvAverage, hSegmentEll, hMat h hne hStep.1,
    (fun z hz j l => (hInterval h hStep.1 z hz j l).1),
    (fun z hz j l => (hInterval h hStep.1 z hz j l).2), hRhsData.2⟩

end KahlerForm
