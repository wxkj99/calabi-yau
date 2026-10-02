module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces
public import CalabiYau.MongeAmpere.Continuity.Openness.CompactChartCover
public import CalabiYau.Geometry.Complex.Schauder
public import CalabiYau.Geometry.Kahler.Laplacian
import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.Chartwise.RhsTransfer
import CalabiYau.MongeAmpere.Continuity.Openness.LaplacianInverse.Chartwise.CompactPatch

/-!
# Finite-chart local Schauder estimate

This follows Székelyhidi, Theorem 2.8, p. 27, equation (2.3), and the finite-cover argument
on pp. 31–32 preceding Theorem 2.10. The latter theorem states an `L¹` remainder; here the
local estimate's `C⁰` remainder is retained. Buffered balls lie in each original output chart,
so only the order-zero RHS needs an overlap transfer, not the order-two output jets. The
coefficient controls and the interior Schauder application remain the already-proved ones.
The fixed top complex-manifold regularity supplies `C¹` overlap transitions for BufferedBalls.
Here `⊤` spells out the existing `ContDiff`-scoped `ω` notation, so the public endpoints are
unchanged; a merely continuous charted-space structure would not suffice.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ENNReal Topology
open MeasureTheory

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- The local Schauder estimate on a fixed finite chart cover, before removing its `C⁰` term.
The pointwise bound `K` is the global supremum contribution appearing in the classical local
interior estimate. All gauge values used through `toReal` are explicitly finite. -/
def HasFiniteChartLocalLaplacianHolderEstimate (ω₁ : KahlerForm n M)
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (α : ℝ≥0) : Prop :=
  ∃ C : ℝ≥0, ∀ f : M → ℝ,
    ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
    ∀ K : ℝ, (∀ x, |f x| ≤ K) →
      finiteChartHolderGauge cover 2 α f < ⊤ ∧
      finiteChartHolderGauge cover 0 α (ω₁.laplacian f) < ⊤ ∧
      (finiteChartHolderGauge cover 2 α f).toReal ≤
        (C : ℝ) * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal + K)

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
      edist x y ≤ (D : ℝ≥0∞) := by
    have heq : (D : ℝ≥0∞) = Metric.ediam K := ENNReal.coe_toNNReal hdiamTop
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
    have hcomp : HolderOnWith (1 * Cα ^ (1 : ℝ)) (1 * α)
        (J ∘ f) K := (hJ.holderOnWith Set.univ).comp hHolderF
          (by intro x hx; trivial)
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

private theorem smooth_finiteChartHolderGauge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (cover : CompactChartCover E M) (k : ℕ) (α : ℝ≥0)
    (hα₁ : α < 1) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) :
    finiteChartHolderGauge cover k α f < ⊤ := by
  classical
  have hα : α ≤ 1 := by exact_mod_cast le_of_lt hα₁
  have hcharts : HolderBoundedInCharts E k α ({f} : Set (M → ℝ)) :=
    HolderBoundedInCharts.singleton hf hα
  change (⨆ i : cover.ι,
    CalabiYau.Schauder.eContDiffHolderGaugeOn k α (cover.piece i)
      (f ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) < ⊤
  apply lt_top_iff_ne_top.mpr
  apply iSup_ne_top
  intro i
  obtain ⟨C, hC⟩ := hcharts (cover.base i) (cover.piece i)
    (cover.isCompact_piece i) (cover.piece_in_target i)
  have hbound := hC f (Set.mem_singleton _)
  have hholder : HolderWith C α
      ((cover.piece i).domRestrict
        (iteratedFDeriv ℝ k
          (f ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm))) := by
    simpa [Function.comp_def] using hbound.2.holderWith
  have hle := CalabiYau.Schauder.eContDiffHolderGaugeOn_le
    (fun _ : ℕ => C) C hbound.1 hholder
  have hsum : (∑ j ∈ Finset.range (k + 1), (C : ℝ≥0∞)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro j hj
    exact ENNReal.coe_ne_top
  have htotal : (∑ j ∈ Finset.range (k + 1), (C : ℝ≥0∞)) + C ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hsum, ENNReal.coe_ne_top⟩
  exact ne_top_of_le_ne_top htotal hle

private theorem exists_metricInChartInverseEntryHolderBound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M) (K : Set (EuclideanSpace ℂ (Fin n)))
    (hK : IsCompact K)
    (hKU : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (α : ℝ≥0) (hα₁ : α < 1) (j k : Fin n) :
    ∃ C : ℝ≥0, HolderBoundOn 0 α C K
        (fun z => (ω₁.metricInChart x z)⁻¹ j k) ∧
      ContDiffOn ℝ ∞ (fun z => (ω₁.metricInChart x z)⁻¹ j k)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
  let U := (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target
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
    · simp only [if_neg hrs]
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
  have hInv_entry (a b : Fin n) : ContDiffOn ℝ ∞ (fun z => (G z)⁻¹ a b) U := by
    have hmul : ContDiffOn ℝ ∞
        (fun z => ((G z).det)⁻¹ * (G z).adjugate a b) U :=
      hdetInv.mul (hAdj_entry a b)
    refine hmul.congr ?_
    intro z hz
    rw [Matrix.inv_def]
    simp [Matrix.smul_apply, smul_eq_mul]
  obtain ⟨C, hBound⟩ := holderBoundOn_of_contDiffOn_compact
    (isOpen_extChartAt_target x) hK hKU (hInv_entry j k) (le_of_lt hα₁)
  exact ⟨C, hBound, hInv_entry j k⟩

open Matrix in
private theorem exists_uniformEllipticityOn_compact
    {n : ℕ} (K : Set (EuclideanSpace ℂ (Fin n))) (hK : IsCompact K)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (hAcont : ∀ j k, ContinuousOn (fun z => A z j k) K)
    (hAhermitian : ∀ z ∈ K, (A z).IsHermitian)
    (hApositive : ∀ z ∈ K, ∀ v, v ≠ 0 →
      0 < RCLike.re (star v ⬝ᵥ (A z *ᵥ v))) :
    ∃ lam : ℝ≥0, 0 < lam ∧ IsUniformlyEllipticOn A lam K := by
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
      let T : Set (EuclideanSpace ℂ (Fin n) × (Fin n → ℂ)) := K ×ˢ S
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
      let Q : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) → ℝ := fun p =>
        RCLike.re (star p.2 ⬝ᵥ (A p.1 *ᵥ p.2))
      have hAcontProd (j k : Fin n) : ContinuousOn (fun p => A p.1 j k) T := by
        exact (hAcont j k).comp continuousOn_fst (fun p hp => hp.1)
      have hcoord (k : Fin n) :
          ContinuousOn (fun p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) => p.2 k) T := by
        fun_prop
      let inner (j : Fin n) (p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ)) :=
        ∑ k, A p.1 j k * p.2 k
      have hinner (j : Fin n) : ContinuousOn (inner j) T := by
        dsimp [inner]
        apply continuousOn_finsetSum
        intro k hk
        exact (hAcontProd j k).mul (hcoord k)
      have hterm (j : Fin n) : ContinuousOn
          (fun p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ) =>
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
      have hQpos (p : EuclideanSpace ℂ (Fin n) × (Fin n → ℂ)) (hp : p ∈ T) :
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
      have hquad (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ K)
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
              _ = δ * ‖v‖ ^ 2 := by field_simp [ne_of_gt (by exact_mod_cast Nat.pos_of_ne_zero hn)]
          _ ≤ RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := hquad z hz v
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact (hKne ⟨z, hz⟩).elim

open Matrix in
open scoped ComplexOrder in
private theorem exists_metricInChartInverseUniformlyElliptic
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M) (K : Set (EuclideanSpace ℂ (Fin n)))
    (hK : IsCompact K)
    (hKU : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ∃ lam : ℝ≥0, 0 < lam ∧
      IsUniformlyEllipticOn (fun z => (ω₁.metricInChart x z)⁻¹) lam K := by
  let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z => (ω₁.metricInChart x z)⁻¹
  have hAcont (j k : Fin n) : ContinuousOn (fun z => A z j k) K := by
    obtain ⟨_, _, hInv⟩ := exists_metricInChartInverseEntryHolderBound
      ω₁ x K hK hKU 0 (by norm_num) j k
    exact hInv.continuousOn.mono hKU
  have hAhermitian : ∀ z ∈ K, (A z).IsHermitian := by
    intro z hz
    exact (ω₁.posDef_metricInChart x (hKU hz)).inv.isHermitian
  have hApositive : ∀ z ∈ K, ∀ v, v ≠ 0 →
      0 < RCLike.re (star v ⬝ᵥ (A z *ᵥ v)) := by
    intro z hz v hv
    have hpos := (ω₁.posDef_metricInChart x (hKU hz)).inv.dotProduct_mulVec_pos hv
    exact (RCLike.pos_iff.mp hpos).1
  obtain ⟨lam, hlam, hEll⟩ := exists_uniformEllipticityOn_compact
    K hK A hAcont hAhermitian hApositive
  exact ⟨lam, hlam, by simpa [A] using hEll⟩

private theorem exists_inverse_metric_coefficients_on_compact
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (x : M) (K : Set (EuclideanSpace ℂ (Fin n)))
    (hK : IsCompact K)
    (hKU : K ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (α : ℝ≥0) (hα₁ : α < 1) :
    ∃ lam C : ℝ≥0, 0 < lam ∧
      IsUniformlyEllipticOn (fun z => (ω₁.metricInChart x z)⁻¹) lam K ∧
      ∀ j k, HolderBoundOn 0 α C K (fun z => (ω₁.metricInChart x z)⁻¹ j k) := by
  classical
  let A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z => (ω₁.metricInChart x z)⁻¹
  obtain ⟨lam, hlam, hEll⟩ := exists_metricInChartInverseUniformlyElliptic
    ω₁ x K hK hKU
  let input (p : Fin n × Fin n) :
      ∃ C : ℝ≥0, HolderBoundOn 0 α C K (fun z => A z p.1 p.2) := by
    obtain ⟨C, hC, _⟩ := exists_metricInChartInverseEntryHolderBound
      ω₁ x K hK hKU α hα₁ p.1 p.2
    exact ⟨C, hC⟩
  let c (p : Fin n × Fin n) : ℝ≥0 := Classical.choose (input p)
  have hc (p : Fin n × Fin n) : HolderBoundOn 0 α (c p) K
      (fun z => A z p.1 p.2) := Classical.choose_spec (input p)
  let C : ℝ≥0 := ∑ p : Fin n × Fin n, c p
  have hle (j k : Fin n) : c (j, k) ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (fun p hp => (zero_le : 0 ≤ c p))
      (Finset.mem_univ (j, k))
  refine ⟨lam, C, hlam, ?_, ?_⟩
  · simpa [A] using hEll
  · intro j k
    exact (hc (j, k)).mono_const (hle j k)

private theorem chartLaplacian_eq_complexEllipticOp
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
    (ω₁ : KahlerForm n M) (f : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f)
    (x : M) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    ω₁.laplacian f ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z) =
      complexEllipticOp (fun w => (ω₁.metricInChart x w)⁻¹)
        (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hy : e.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
    simpa [e, ← extChartAt_source] using e.map_target hz
  have hLap := ω₁.laplacian_eq_inChart hf x hy
  rw [e.right_inv hz] at hLap
  change ω₁.laplacian f (e.symm z) =
    RCLike.re ((ω₁.metricInChart x z)⁻¹ *
      complexHessian (f ∘ e.symm) z).trace at hLap
  exact hLap

private theorem finiteChartHolderGauge_le_of_chartwiseHolderBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (cover : CompactChartCover E M) (k : ℕ) (α C : ℝ≥0) (f : M → ℝ)
    (hC : ∀ i, HolderBoundOn k α C (cover.piece i)
      (f ∘ (extChartAt 𝓘(ℝ, E) (cover.base i)).symm)) :
    finiteChartHolderGauge cover k α f ≤
      (∑ _j ∈ Finset.range (k + 1), (C : ℝ≥0∞)) + C := by
  classical
  unfold finiteChartHolderGauge
  apply iSup_le
  intro i
  exact CalabiYau.Schauder.eContDiffHolderGaugeOn_le (fun _ => C) C
    (hC i).1 (HolderWith.restrict_iff.mpr (hC i).2)

private theorem holderBoundOn_zero_comp_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {α C : ℝ≥0} {K U : Set E} {τ : E → E} {g : E → ℝ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hτ : ContDiffOn ℝ 1 τ U)
    (hbound : HolderBoundOn 0 α C (τ '' K) g) :
    ∃ C' : ℝ≥0, HolderBoundOn 0 α C' K (g ∘ τ) := by
  classical
  have hLoc : LocallyLipschitzOn K τ := by
    intro x hx
    have hxU : x ∈ U := hKU hx
    have hfx : ContDiffAt ℝ 1 τ x := hτ.contDiffAt (hU.mem_nhds hxU)
    obtain ⟨L, t, ht, hLip⟩ := hfx.exists_lipschitzOnWith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨L, Metric.ball x δ ∩ K,
      Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩, ?_⟩
    · exact fun y hy => ⟨hy.1, hy.2⟩
    · apply hLip.mono
      intro y hy
      exact hball hy.1
  obtain ⟨L, hLip⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hLoc
  have hτHolder : HolderOnWith L 1 τ K := hLip.holderOnWith
  have hG : HolderOnWith C α g (τ '' K) := by
    have hJet : HolderOnWith C α (iteratedFDeriv ℝ 0 g) (τ '' K) := hbound.2
    let JI : ℝ ≃ₗᵢ[ℝ] (E [×0]→L[ℝ] ℝ) :=
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm
    have hInv : HolderWith 1 1 (JI.symm : (E [×0]→L[ℝ] ℝ) → ℝ) :=
      JI.symm.lipschitz.holderWith
    have hComp : HolderOnWith C α
        ((JI.symm : (E [×0]→L[ℝ] ℝ) → ℝ) ∘ iteratedFDeriv ℝ 0 g) (τ '' K) := by
      simpa [NNReal.rpow_one, one_mul] using
        (hInv.holderOnWith Set.univ).comp hJet (by intro x hx; trivial)
    have hEq : ((JI.symm : (E [×0]→L[ℝ] ℝ) → ℝ) ∘ iteratedFDeriv ℝ 0 g) = g := by
      funext x
      simp [Function.comp_def, iteratedFDeriv_zero_eq_comp, JI]
    simpa [hEq] using hComp
  have hGτ : HolderOnWith (C * L ^ (α : ℝ)) α (g ∘ τ) K := by
    have h := hG.comp hτHolder (by
      intro x hx
      exact Set.mem_image_of_mem _ hx)
    simpa using h
  have hJ : HolderWith 1 1
      ((continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap) := by
    exact (((continuousMultilinearCurryFin0 ℝ E ℝ).symm).lipschitz.holderWith)
  have hJet : HolderOnWith (C * L ^ (α : ℝ)) α
      (iteratedFDeriv ℝ 0 (g ∘ τ)) K := by
    have hcomp := (hJ.holderOnWith Set.univ).comp hGτ (by intro x hx; trivial)
    have hEq : iteratedFDeriv ℝ 0 (g ∘ τ) =
        ((continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearMap) ∘ (g ∘ τ) := by
      funext x
      simp [Function.comp_def, iteratedFDeriv_zero_eq_comp]
    simpa [hEq, NNReal.rpow_one, one_mul] using hcomp
  refine ⟨max C (C * L ^ (α : ℝ)), ?_⟩
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [norm_iteratedFDeriv_zero]
    have hb := hbound.1 0 le_rfl (τ x) ⟨x, hx, rfl⟩
    have hb' : |g (τ x)| ≤ (C : ℝ) := by
      simpa [norm_iteratedFDeriv_zero] using hb
    change |g (τ x)| ≤ _
    exact hb'.trans (by exact_mod_cast (le_max_left C (C * L ^ (α : ℝ))))
  · exact hJet.mono_const (le_max_right _ _)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem exists_holderOnWith_and_bound_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} {f : E → F} {α : ℝ≥0} {k : ℕ}
    (hα : α ≤ 1) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ (k + 1) f U) :
    ∃ C B : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ k f) K ∧
      ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ B := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) U := by
    intro x hx
    exact (hf.contDiffAt (hU.mem_nhds hx)).continuousAt_iteratedFDeriv
      (by exact_mod_cast (Nat.le_add_right k 1)) |>.continuousWithinAt
  have hnorm : ContinuousOn (fun x ↦ ‖iteratedFDeriv ℝ k f x‖) K :=
    (hcont.mono hKU).norm
  obtain ⟨B, hB₀, hB⟩ := hK.bddAbove_image hnorm |>.exists_ge 0
  let Bn : ℝ≥0 := ⟨B, hB₀⟩
  have hbound (x : E) (hx : x ∈ K) : ‖iteratedFDeriv ℝ k f x‖ ≤ (Bn : ℝ) := by
    exact_mod_cast hB (‖iteratedFDeriv ℝ k f x‖) ⟨x, hx, rfl⟩
  have hLoc : LocallyLipschitzOn K (iteratedFDeriv ℝ k f) := by
    intro x hx
    have hxU : x ∈ U := hKU hx
    have hAt : ContDiffAt ℝ (k + 1) f x := hf.contDiffAt (hU.mem_nhds hxU)
    have hDer : ContDiffAt ℝ 1 (iteratedFDeriv ℝ k f) x := by
      exact hAt.iteratedFDeriv_right
        (by exact_mod_cast (show (1 : ℕ) + k ≤ k + 1 by omega))
    obtain ⟨L, t, ht, hLip⟩ := hDer.exists_lipschitzOnWith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨L, Metric.ball x δ ∩ K,
      Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩, ?_⟩
    · intro y hy
      exact ⟨hy.1, hy.2⟩
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
  refine ⟨L * D ^ ((1 : ℝ) - (α : ℝ)), Bn, ?_, hbound⟩
  exact hLip.holderOnWith.of_le hdist hα

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem exists_lipschitzOnWith_of_contDiffOn_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set E} {f : E → F}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) : ∃ L : ℝ≥0, LipschitzOnWith L f K := by
  have hLoc : LocallyLipschitzOn K f := by
    intro x hx
    have hAt : ContDiffAt ℝ 1 f x := hf.contDiffAt (hU.mem_nhds (hKU hx))
    obtain ⟨L, t, ht, hLip⟩ := hAt.exists_lipschitzOnWith
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
    refine ⟨L, Metric.ball x δ ∩ K,
      Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩, ?_⟩
    · intro y hy
      exact ⟨hy.1, hy.2⟩
    · apply hLip.mono
      intro y hy
      exact hball hy.1
  exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK hLoc

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem holderOnWith_taylorComp_two
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} {α : ℝ≥0} {p : E → FormalMultilinearSeries ℝ F G}
    {q : E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ k ≤ 2, ∃ C : ℝ≥0, HolderOnWith C α (fun x ↦ p x k) K)
    (hq : ∀ k ≤ 2, ∃ C : ℝ≥0, HolderOnWith C α (fun x ↦ q x k) K)
    (hpb : ∀ k ≤ 2, ∃ B : ℝ≥0, ∀ x ∈ K, ‖p x k‖ ≤ B)
    (hqb : ∀ k ≤ 2, ∃ B : ℝ≥0, ∀ x ∈ K, ‖q x k‖ ≤ B) :
    ∃ C : ℝ≥0, HolderOnWith C α (fun x ↦ (p x).taylorComp (q x) 2) K := by
  let l : Filter (E × E) := Filter.principal (K ×ˢ K)
  let d : E × E → ℝ := fun a ↦ Real.rpow (dist a.1 a.2) (α : ℝ)
  have hpbdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a ↦ ‖p a.1 k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hpb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.1 ha.1
  have hq1bdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a ↦ ‖q a.1 k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hqb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.1 ha.1
  have hq2bdd : ∀ k ≤ 2, l.IsBoundedUnder (· ≤ ·) (fun a ↦ ‖q a.2 k‖) := by
    intro k hk
    obtain ⟨B, hB⟩ := hqb k hk
    apply Filter.isBoundedUnder_of_eventually_le
    rw [Filter.eventually_principal]
    intro a ha
    exact hB a.2 ha.2
  have hpf : ∀ k ≤ 2, (fun a : E × E ↦ p a.1 k - p a.2 k) =O[l] d := by
    intro k hk
    obtain ⟨C, hC⟩ := hp k hk
    rw [Asymptotics.isBigO_iff]
    refine ⟨(C : ℝ), ?_⟩
    rw [Filter.eventually_principal]
    intro a ha
    have h := hC.dist_le ha.1 ha.2
    rw [dist_eq_norm] at h
    change ‖p a.1 k - p a.2 k‖ ≤ (C : ℝ) * ‖d a‖
    simpa [d, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using h
  have hqf : ∀ k ≤ 2, (fun a : E × E ↦ q a.1 k - q a.2 k) =O[l] d := by
    intro k hk
    obtain ⟨C, hC⟩ := hq k hk
    rw [Asymptotics.isBigO_iff]
    refine ⟨(C : ℝ), ?_⟩
    rw [Filter.eventually_principal]
    intro a ha
    have h := hC.dist_le ha.1 ha.2
    rw [dist_eq_norm] at h
    change ‖q a.1 k - q a.2 k‖ ≤ (C : ℝ) * ‖d a‖
    simpa [d, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using h
  have hcomp := FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
    hpbdd hpf hq1bdd hq2bdd hqf
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hcomp
  let C' : ℝ≥0 := ⟨max 0 C, le_max_left 0 C⟩
  refine ⟨C', ?_⟩
  intro x hx y hy
  have h := (Filter.eventually_principal.mp hC) (x, y) ⟨hx, hy⟩
  have h' : ‖(p x).taylorComp (q x) 2 - (p y).taylorComp (q y) 2‖ ≤
      C * Real.rpow (dist x y) (α : ℝ) := by
    simpa [d, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (dist_nonneg) _)] using h
  have hC' : C ≤ (C' : ℝ) := le_max_right 0 C
  have h'' := h'.trans (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg (dist_nonneg) _))
  have hENN : ENNReal.ofReal (dist ((p x).taylorComp (q x) 2) ((p y).taylorComp (q y) 2)) ≤
      ENNReal.ofReal (C' * Real.rpow (dist x y) (α : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    simpa only [dist_eq_norm] using h''
  change edist ((p x).taylorComp (q x) 2) ((p y).taylorComp (q y) 2) ≤
    (C' : ENNReal) * edist x y ^ (α : ℝ)
  simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg,
    Real.rpow_nonneg] using hENN

private theorem holderBoundOn_comp_contDiffOn_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {α C : ℝ≥0} {K U V : Set E} {τ : E → E} {g : E → ℝ}
    (hα : α ≤ 1) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hτ : ContDiffOn ℝ 3 τ U) (hV : IsOpen V) (hτV : τ '' K ⊆ V)
    (hg : ContDiffOn ℝ 2 g V)
    (hbound : HolderBoundOn 2 α C (τ '' K) g) :
    ∃ C' : ℝ≥0, HolderBoundOn 2 α C' K (g ∘ τ) := by
  classical
  let Kτ := τ '' K
  have hτcont : ContinuousOn τ K := hτ.continuousOn.mono hKU
  have hKτ : IsCompact Kτ := hK.image_of_continuousOn hτcont
  have hτLip : ∃ L : ℝ≥0, HolderOnWith L 1 τ K := by
    obtain ⟨L, hL⟩ := exists_lipschitzOnWith_of_contDiffOn_compact hK hU hKU
      (hτ.of_le (by norm_num))
    exact ⟨L, hL.holderOnWith⟩
  obtain ⟨Lτ, hτHolder1⟩ := hτLip
  let p : E → FormalMultilinearSeries ℝ E ℝ := fun y ↦ ftaylorSeries ℝ g (τ y)
  let q : E → FormalMultilinearSeries ℝ E E := fun y ↦ ftaylorSeries ℝ τ y
  have hqData : ∀ k ≤ 2, ∃ Ck Bk : ℝ≥0,
      HolderOnWith Ck α (fun y ↦ iteratedFDeriv ℝ k τ y) K ∧
      ∀ y ∈ K, ‖iteratedFDeriv ℝ k τ y‖ ≤ Bk := by
    intro k hk
    exact exists_holderOnWith_and_bound_iteratedFDeriv hα hK hU hKU
      (hτ.of_le (by exact_mod_cast (show k + 1 ≤ 3 by omega)))
  have hp : ∀ k ≤ 2, ∃ Ck : ℝ≥0,
      HolderOnWith Ck α (fun y ↦ p y k) K := by
    intro k hk
    by_cases hk2 : k = 2
    · subst k
      refine ⟨C * Lτ ^ (α : ℝ), ?_⟩
      have h := hbound.2.comp hτHolder1 (by
        intro y hy
        exact ⟨y, hy, rfl⟩)
      simpa [p, ftaylorSeries, Function.comp_def, mul_one] using h
    · have hk1 : k + 1 ≤ 2 := by omega
      obtain ⟨Ck, _, hG, _⟩ := exists_holderOnWith_and_bound_iteratedFDeriv hα hKτ hV
        (by simpa [Kτ] using hτV)
        (hg.of_le (by exact_mod_cast hk1))
      refine ⟨Ck * Lτ ^ (α : ℝ), ?_⟩
      have h := hG.comp hτHolder1 (by
        intro y hy
        exact ⟨y, hy, rfl⟩)
      simpa [p, ftaylorSeries, Function.comp_def, mul_one] using h
  have hq : ∀ k ≤ 2, ∃ Ck : ℝ≥0,
      HolderOnWith Ck α (fun y ↦ q y k) K := by
    intro k hk
    obtain ⟨Ck, _, hQ, _⟩ := hqData k hk
    exact ⟨Ck, by simpa [q, ftaylorSeries] using hQ⟩
  have hpb : ∀ k ≤ 2, ∃ Bk : ℝ≥0, ∀ y ∈ K, ‖p y k‖ ≤ Bk := by
    intro k hk
    refine ⟨C, ?_⟩
    intro y hy
    simpa [p, ftaylorSeries] using hbound.1 k hk (τ y) ⟨y, hy, rfl⟩
  have hqb : ∀ k ≤ 2, ∃ Bk : ℝ≥0, ∀ y ∈ K, ‖q y k‖ ≤ Bk := by
    intro k hk
    obtain ⟨_, Bk, _, hQ⟩ := hqData k hk
    exact ⟨Bk, by simpa [q, ftaylorSeries] using hQ⟩
  obtain ⟨Ccomp, hCompTaylor⟩ := holderOnWith_taylorComp_two hp hq hpb hqb
  have hCompEq (y : E) (hy : y ∈ K) :
      iteratedFDeriv ℝ 2 (g ∘ τ) y = (p y).taylorComp (q y) 2 := by
    dsimp [p, q]
    exact iteratedFDeriv_comp
      (hg.contDiffAt (hV.mem_nhds (hτV ⟨y, hy, rfl⟩)))
      ((hτ.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by norm_num)) le_rfl
  have hTaylorJet : HolderOnWith Ccomp α (iteratedFDeriv ℝ 2 (g ∘ τ)) K := by
    intro y hy z hz
    rw [hCompEq y hy, hCompEq z hz]
    exact hCompTaylor y hy z hz
  let O := U ∩ τ ⁻¹' V
  have hOopen : IsOpen O := hτ.continuousOn.isOpen_inter_preimage hU hV
  have hKO : K ⊆ O := by
    intro y hy
    exact ⟨hKU hy, hτV ⟨y, hy, rfl⟩⟩
  have hτO : Set.MapsTo τ O V := by
    intro y hy
    exact hy.2
  have hCompDiff : ContDiffOn ℝ 2 (g ∘ τ) O :=
    hg.comp ((hτ.of_le (by norm_num)).mono (by intro y hy; exact hy.1)) hτO
  have hJetBound : ∀ k ≤ 2, ∃ Bk : ℝ≥0, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ k (g ∘ τ) y‖ ≤ Bk := by
    intro k hk
    have hCont : ContinuousOn (iteratedFDeriv ℝ k (g ∘ τ)) K := by
      intro y hy
      have hAt : ContDiffAt ℝ 2 (g ∘ τ) y :=
        hCompDiff.contDiffAt (hOopen.mem_nhds (hKO hy))
      exact hAt.continuousAt_iteratedFDeriv (by exact_mod_cast hk) |>.continuousWithinAt
    have hNorm : ContinuousOn (fun y ↦ ‖iteratedFDeriv ℝ k (g ∘ τ) y‖) K := hCont.norm
    obtain ⟨B, hB₀, hB⟩ := hK.bddAbove_image hNorm |>.exists_ge 0
    refine ⟨⟨B, hB₀⟩, ?_⟩
    intro y hy
    exact_mod_cast hB (‖iteratedFDeriv ℝ k (g ∘ τ) y‖) ⟨y, hy, rfl⟩
  obtain ⟨B0, hB0⟩ := hJetBound 0 (by omega)
  obtain ⟨B1, hB1⟩ := hJetBound 1 (by omega)
  obtain ⟨B2, hB2⟩ := hJetBound 2 (by omega)
  let B := max B0 (max B1 B2)
  let C' := max Ccomp B
  have hBound : ∀ k ≤ 2, ∀ y ∈ K, ‖iteratedFDeriv ℝ k (g ∘ τ) y‖ ≤ B := by
    intro k hk y hy
    interval_cases k
    · exact (hB0 y hy).trans (by exact_mod_cast (le_max_left B0 (max B1 B2)))
    · exact (hB1 y hy).trans (by exact_mod_cast
        (le_trans (le_max_left B1 B2) (le_max_right B0 (max B1 B2))))
    · exact (hB2 y hy).trans (by exact_mod_cast
        (le_trans (le_max_right B1 B2) (le_max_right B0 (max B1 B2))))
  refine ⟨C', ?_⟩
  constructor
  · intro k hk y hy
    exact (hBound k hk y hy).trans (by exact_mod_cast (le_max_right Ccomp B))
  · exact hTaylorJet.mono_const (le_max_left _ _)

private theorem exists_finite_compact_patch_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ≥0} {K : Set E} {f : E → ℝ} {ι : Type*} [Fintype ι]
    (patch : ι → Set E) (hcover : K ⊆ ⋃ i, interior (patch i))
    (localBound : ∀ i, ∃ C : ℝ≥0, HolderBoundOn 2 α C (patch i) f) :
    ∃ C : ℝ≥0, ∀ j ≤ 2, ∀ z ∈ K, ‖iteratedFDeriv ℝ j f z‖ ≤ C := by
  classical
  let c (i : ι) : ℝ≥0 := Classical.choose (localBound i)
  have hc (i : ι) : HolderBoundOn 2 α (c i) (patch i) f :=
    Classical.choose_spec (localBound i)
  let C : ℝ≥0 := ∑ i : ι, c i
  refine ⟨C, ?_⟩
  intro j hj z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hz)
  have hzi : z ∈ patch i := interior_subset hi
  have hci : c i ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ c k)) (Finset.mem_univ i)
  have hb := (hc i).1 j hj z hzi
  exact hb.trans (by exact_mod_cast hci)

private theorem exists_holderBoundOn_of_finite_compact_patch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ≥0} {K : Set E} {f : E → ℝ} {ι : Type*} [Fintype ι]
    (hK : IsCompact K) (patch : ι → Set E)
    (hcover : K ⊆ ⋃ i, interior (patch i))
    (localBound : ∀ i, ∃ C : ℝ≥0, HolderBoundOn 2 α C (patch i) f) :
    ∃ C : ℝ≥0, HolderBoundOn 2 α C K f := by
  classical
  obtain ⟨D, hD⟩ := exists_finite_compact_patch_derivative_bound patch hcover localBound
  let c (i : ι) : ℝ≥0 := Classical.choose (localBound i)
  have hc (i : ι) : HolderBoundOn 2 α (c i) (patch i) f :=
    Classical.choose_spec (localBound i)
  let S : ℝ≥0 := ∑ i : ι, c i
  have hcs : ∀ i, c i ≤ S := by
    intro i
    dsimp [S]
    exact Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ c k)) (Finset.mem_univ i)
  let C : ℝ≥0 := max D S
  have hC : ∀ j ≤ 2, ∀ z ∈ K, ‖iteratedFDeriv ℝ j f z‖ ≤ C := by
    intro j hj z hz
    exact (hD j hj z hz).trans (by exact_mod_cast (le_max_left D S))
  let U (i : ι) : Set E := interior (patch i)
  have hUopen (i : ι) : IsOpen (U i) := isOpen_interior
  have hUcover : K ⊆ ⋃ i : ι, U i := hcover
  have hlocal : ∀ i, HolderBoundOn 2 α C (U i) f := by
    intro i
    exact (hc i).mono_set interior_subset |>.mono_const (by
      exact_mod_cast (le_trans (hcs i) (le_max_right D S)))
  have hglobal : ∀ x ∈ K, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C := fun x hx =>
    hC 2 (by omega) x hx
  obtain ⟨V, hV, hLebesgue⟩ := lebesgue_number_lemma hK hUopen hUcover
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  let δ : ℝ≥0 := Real.toNNReal (ε / 2)
  have hδpos : 0 < δ := Real.toNNReal_pos.mpr (by linarith)
  have hδeq : (δ : ℝ) = ε / 2 := by
    simp [δ, Real.coe_toNNReal (ε / 2) (by positivity : 0 ≤ ε / 2)]
  have hnear : ∀ x ∈ K, ∀ y ∈ K, nndist x y ≤ δ →
      ∃ i, x ∈ U i ∧ y ∈ U i := by
    intro x hx y hy hxy
    obtain ⟨i, hball⟩ := hLebesgue x hx
    have hdist : dist x y ≤ (δ : ℝ) := by exact_mod_cast hxy
    have hdistlt : dist x y < ε := by
      rw [hδeq] at hdist
      linarith
    have hyV : y ∈ UniformSpace.ball x V := by
      change (x, y) ∈ V
      exact hεV hdistlt
    exact ⟨i, hball (UniformSpace.mem_ball_self x hV), hball hyV⟩
  let Cfar : ℝ≥0 := (2 * C) / δ ^ (α : ℝ)
  let C' : ℝ≥0 := max C Cfar
  refine ⟨C', ?_⟩
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hUcover hx)
    exact ((hlocal i).1 j hj x hxi).trans (by
      exact_mod_cast (le_max_left C Cfar))
  · intro x hx y hy
    by_cases hxy : nndist x y ≤ δ
    · obtain ⟨i, hxi, hyi⟩ := hnear x hx y hy hxy
      exact ((hlocal i).mono_const (le_max_left C Cfar)).2 x hxi y hyi
    · have hδle : δ ≤ nndist x y := le_of_not_ge hxy
      have hpowpos : 0 < δ ^ (α : ℝ) := NNReal.rpow_pos hδpos
      have hpowle : δ ^ (α : ℝ) ≤ nndist x y ^ (α : ℝ) :=
        NNReal.rpow_le_rpow hδle α.coe_nonneg
      have hfarCoeff : 2 * C ≤ Cfar * nndist x y ^ (α : ℝ) := by
        dsimp [Cfar]
        calc
          2 * C = ((2 * C) / δ ^ (α : ℝ)) * δ ^ (α : ℝ) := by field_simp
          _ ≤ ((2 * C) / δ ^ (α : ℝ)) * nndist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_left hpowle (by positivity)
      have hfarENN : (↑(2 * C) : ENNReal) ≤
          (↑Cfar : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [edist_nndist, ← ENNReal.coe_rpow_of_nonneg (nndist x y) α.coe_nonneg,
          ← ENNReal.coe_mul]
        exact_mod_cast hfarCoeff
      have htopx : ‖iteratedFDeriv ℝ 2 f x‖ ≤ (C : ℝ) := hglobal x hx
      have htopy : ‖iteratedFDeriv ℝ 2 f y‖ ≤ (C : ℝ) := hglobal y hy
      calc
        edist (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y) =
            ENNReal.ofReal (dist (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y)) :=
          edist_dist _ _
        _ ≤ ENNReal.ofReal
            (‖iteratedFDeriv ℝ 2 f x‖ + ‖iteratedFDeriv ℝ 2 f y‖) :=
          ENNReal.ofReal_le_ofReal (dist_le_norm_add_norm _ _)
        _ ≤ ENNReal.ofReal ((C : ℝ) + C) :=
          ENNReal.ofReal_le_ofReal (add_le_add htopx htopy)
        _ = (↑(2 * C) : ENNReal) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          simp [two_mul]
        _ ≤ (↑Cfar : ENNReal) * edist x y ^ (α : ℝ) := hfarENN
        _ ≤ (↑C' : ENNReal) * edist x y ^ (α : ℝ) :=
          mul_le_mul_of_nonneg_right
            (ENNReal.coe_le_coe.mpr (le_max_right C Cfar)) (by positivity)

private theorem holderBoundOn_two_of_interiorSchauder
    {n : ℕ} (hSch : InteriorSchauderEstimate n)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (lam K : ℝ≥0) (hlam : 0 < lam)
    (U V : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (hV : IsCompact (closure V)) (hVU : closure V ⊆ U)
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ)
    (hA : ∀ j l, ContDiffOn ℝ 0 (fun z => A z j l) U)
    (hu : ContDiffOn ℝ 2 u U) (hEll : IsUniformlyEllipticOn A lam U)
    (hAHolder : ∀ j l, HolderBoundOn 0 α K U (fun z => A z j l))
    (K₀ K₁ : ℝ≥0)
    (hLu : ContDiffOn ℝ 0 (complexEllipticOp A u) U)
    (hLuHolder : HolderBoundOn 0 α K₁ U (complexEllipticOp A u))
    (huBound : ∀ z ∈ U, |u z| ≤ K₀) :
    ∃ C : ℝ≥0, ContDiffOn ℝ 2 u U ∧
      HolderBoundOn 2 α (C * (K₁ + K₀)) V u := by
  obtain ⟨C, hC⟩ := hSch 0 α hα₀ hα₁ lam K hlam U V hU hV hVU
  refine ⟨C, ?_⟩
  exact hC A u hA hu hEll hAHolder K₀ K₁ hLu hLuHolder huBound

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartPiece_interior_refinement
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M) (i : cover.ι)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ cover.piece i) :
    ∃ j : cover.ι, ∃ y : EuclideanSpace ℂ (Fin n),
      z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target ∧
      y ∈ interior (cover.piece j) ∧
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).symm y =
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z := by
  let eᵢ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  let x := eᵢ.symm z
  obtain ⟨j, y, hy, hxy⟩ := cover.interior_covers x
  exact ⟨j, y, cover.piece_in_target i hz, hy, hxy⟩

private theorem holderBoundOn_zero_scalar_holder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {α C : ℝ≥0} {K : Set E} {f : E → ℝ}
    (h : HolderBoundOn 0 α C K f) : HolderOnWith C α f K := by
  let JI : ℝ ≃ₗᵢ[ℝ] (E [×0]→L[ℝ] ℝ) :=
    (continuousMultilinearCurryFin0 ℝ E ℝ).symm
  let J : ℝ →L[ℝ] (E [×0]→L[ℝ] ℝ) := JI.toContinuousLinearMap
  have hjet : iteratedFDeriv ℝ 0 f = J ∘ f := by
    simpa [J] using (iteratedFDeriv_zero_eq_comp (𝕜 := ℝ) (f := f))
  have hsource : HolderOnWith C α (J ∘ f) K := by
    rw [← hjet]
    exact h.2
  intro x hx y hy
  calc
    edist (f x) (f y) = edist (JI (f x)) (JI (f y)) := (JI.edist_map _ _).symm
    _ = edist (J (f x)) (J (f y)) := rfl
    _ ≤ (C : ℝ≥0∞) * edist x y ^ (α : ℝ) := hsource x hx y hy

private theorem holderBoundOn_zero_of_scalar_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {α C : ℝ≥0} {K : Set E} {f : E → ℝ}
    (hnorm : ∀ x ∈ K, |f x| ≤ C)
    (hHolder : HolderOnWith C α f K) : HolderBoundOn 0 α C K f := by
  let JI : ℝ ≃ₗᵢ[ℝ] (E [×0]→L[ℝ] ℝ) :=
    (continuousMultilinearCurryFin0 ℝ E ℝ).symm
  let J : ℝ →L[ℝ] (E [×0]→L[ℝ] ℝ) := JI.toContinuousLinearMap
  have hJlip : LipschitzWith 1 J := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      dist (J x) (J y) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact JI.norm_map _
      _ ≤ 1 * dist x y := by simp
  have hJ : HolderWith 1 1 J := hJlip.holderWith
  have hjet : iteratedFDeriv ℝ 0 f = J ∘ f := by
    simpa [J] using (iteratedFDeriv_zero_eq_comp (𝕜 := ℝ) (f := f))
  have hHolderJet : HolderOnWith C α (iteratedFDeriv ℝ 0 f) K := by
    rw [hjet]
    have hcomp := (hJ.holderOnWith Set.univ).comp hHolder (by
      intro x hx
      trivial)
    simpa [NNReal.rpow_one, one_mul] using hcomp
  refine ⟨?_, hHolderJet⟩
  intro j hj x hx
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
  subst j
  rw [norm_iteratedFDeriv_zero]
  exact hnorm x hx

private theorem transfer_zeroHolder_across_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {α C L : ℝ≥0} {S R : Set E} {g : E → ℝ} {T : E → E}
    (hG : HolderBoundOn 0 α C R g) (hT : LipschitzOnWith L T S)
    (hmap : Set.MapsTo T S R) :
    HolderOnWith (C * L ^ (α : ℝ)) α (g ∘ T) S := by
  simpa only [mul_one] using
    (holderBoundOn_zero_scalar_holder hG).comp hT.holderOnWith hmap

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem transfer_chartwise_rhs_holder
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (q : M → ℝ) (α C L : ℝ≥0) (i j : cover.ι)
    (S : Set (EuclideanSpace ℂ (Fin n))) (T : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n))
    (hGauge : HolderBoundOn 0 α C (cover.piece j)
      (q ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).symm))
    (hT : LipschitzOnWith L T S)
    (hmap : Set.MapsTo T S (cover.piece j))
    (hEq : Set.EqOn
      (q ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)
      ((q ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).symm) ∘ T) S) :
    HolderOnWith (C * L ^ (α : ℝ)) α
      (q ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) S := by
  intro x hx y hy
  rw [hEq hx, hEq hy]
  exact transfer_zeroHolder_across_lipschitz hGauge hT hmap x hx y hy

private theorem exists_local_lipschitzOn_ball
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T : E → F} {x : E} (hT : ContDiffAt ℝ 1 T x) :
    ∃ L : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      LipschitzOnWith L T (Metric.ball x δ) := by
  obtain ⟨L, t, ht, hLip⟩ := hT.exists_lipschitzOnWith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp ht
  exact ⟨L, δ, hδ, hLip.mono hball⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem chartTransition_contDiffAt
    (x y : M) (z : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hzy : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm z ∈
      (chartAt (EuclideanSpace ℂ (Fin n)) y).source) :
    ContDiffAt ℝ 1
      (fun w => extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm w)) z := by
  let I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let eₓ := extChartAt I x
  let eᵧ := extChartAt I y
  have hsymm : ContMDiffAt I I ∞ eₓ.symm z := by
    exact (contMDiffOn_extChartAt_symm (I := I) x z hz).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x).mem_nhds hz)
  have hchart : ContMDiffAt I I ∞ eᵧ (eₓ.symm z) :=
    contMDiffAt_extChartAt' (I := I) (x := y) hzy
  have hcomp : ContMDiffAt I I ∞ (eᵧ ∘ eₓ.symm) z := hchart.comp z hsymm
  have hcomp' : ContMDiffAt I I ∞
      (fun w => extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) y
        ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm w)) z := by
    simpa [I, eₓ, eᵧ, Function.comp_def] using hcomp
  exact hcomp'.contDiffAt.of_le (by norm_num)

private theorem exists_local_smoothTransition_holder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {α C : ℝ≥0} {R : Set E} {g : E → ℝ} {T : E → E} {x : E}
    (hG : HolderBoundOn 0 α C R g) (hT : ContDiffAt ℝ 1 T x)
    (hTx : T x ∈ interior R) :
    ∃ L : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      Set.MapsTo T (Metric.ball x δ) (interior R) ∧
      HolderOnWith (C * L ^ (α : ℝ)) α (g ∘ T) (Metric.ball x δ) := by
  obtain ⟨L, δ₁, hδ₁, hLip⟩ := exists_local_lipschitzOn_ball hT
  obtain ⟨δ₂, hδ₂, hBall₂⟩ := Metric.mem_nhds_iff.mp
    (hT.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hTx))
  let δ : ℝ := min δ₁ δ₂
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min hδ₁ hδ₂
  have hBall₁ : Metric.ball x δ ⊆ Metric.ball x δ₁ :=
    Metric.ball_subset_ball (by dsimp [δ]; exact min_le_left _ _)
  have hBall₂' : Metric.ball x δ ⊆ Metric.ball x δ₂ :=
    Metric.ball_subset_ball (by dsimp [δ]; exact min_le_right _ _)
  have hLip' : LipschitzOnWith L T (Metric.ball x δ) := hLip.mono hBall₁
  have hmapInterior : Set.MapsTo T (Metric.ball x δ) (interior R) := by
    intro z hz
    have hzt : z ∈ Metric.ball x δ₂ := hBall₂' hz
    apply hBall₂
    exact hzt
  have hmap : Set.MapsTo T (Metric.ball x δ) R :=
    hmapInterior.mono_right interior_subset
  exact ⟨L, δ, hδ, hmapInterior,
    transfer_zeroHolder_across_lipschitz hG hLip' hmap⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem exists_chart_rhs_holder_on_overlap
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (q : M → ℝ) (α C : ℝ≥0) (i j : cover.ι)
    (z y : EuclideanSpace ℂ (Fin n))
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target)
    (hy : y ∈ interior (cover.piece j))
    (hxy : (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).symm y =
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z)
    (hGauge : HolderBoundOn 0 α C (cover.piece j)
      (q ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).symm)) :
    ∃ L : ℝ≥0, ∃ ρ : ℝ, 0 < ρ ∧ IsCompact (Metric.closedBall z ρ) ∧
      HolderBoundOn 0 α (max C (C * L ^ (α : ℝ))) (Metric.closedBall z ρ)
        (q ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
  let eᵢ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
  let eⱼ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)
  let T : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun w => eⱼ (eᵢ.symm w)
  have hyPiece : y ∈ cover.piece j := interior_subset hy
  have hyTarget : y ∈ eⱼ.target := cover.piece_in_target j hyPiece
  have hsource : eᵢ.symm z ∈ eⱼ.source := by
    rw [← hxy]
    exact eⱼ.map_target hyTarget
  have hsource' : eᵢ.symm z ∈ (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base j)).source := by
    have hs : eⱼ.source = (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base j)).source :=
      extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (cover.base j)
    rw [← hs]
    exact hsource
  have hT : ContDiffAt ℝ 1 T z := by
    simpa [T, eᵢ, eⱼ] using chartTransition_contDiffAt
      (cover.base i) (cover.base j) z hz hsource'
  have hTz : T z ∈ interior (cover.piece j) := by
    change eⱼ (eᵢ.symm z) ∈ interior (cover.piece j)
    rw [← hxy, eⱼ.right_inv hyTarget]
    exact hy
  obtain ⟨L, δ₁, hδ₁, hmapInterior, hHolder⟩ :=
    exists_local_smoothTransition_holder hGauge hT hTz
  have hSymmCont : ContinuousAt eᵢ.symm z := continuousAt_extChartAt_symm'' hz
  obtain ⟨δ₂, hδ₂, hball₂⟩ := Metric.mem_nhds_iff.mp
    (hSymmCont.preimage_mem_nhds
      ((chartAt (EuclideanSpace ℂ (Fin n)) (cover.base j)).open_source.mem_nhds hsource'))
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min hδ₁ hδ₂
  have hsub₁ : Metric.ball z δ ⊆ Metric.ball z δ₁ :=
    Metric.ball_subset_ball (by dsimp [δ]; exact min_le_left _ _)
  have hsub₂ : Metric.ball z δ ⊆ Metric.ball z δ₂ :=
    Metric.ball_subset_ball (by dsimp [δ]; exact min_le_right _ _)
  have hHolder' : HolderOnWith (C * L ^ (α : ℝ)) α
      ((q ∘ eⱼ.symm) ∘ T) (Metric.ball z δ) := hHolder.mono hsub₁
  have hEq : Set.EqOn (q ∘ eᵢ.symm) ((q ∘ eⱼ.symm) ∘ T) (Metric.ball z δ) := by
    intro w hw
    have hwsource' : eᵢ.symm w ∈
        (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base j)).source := hball₂ (hsub₂ hw)
    have hs : eⱼ.source = (chartAt (EuclideanSpace ℂ (Fin n)) (cover.base j)).source :=
      extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (cover.base j)
    have hwsource : eᵢ.symm w ∈ eⱼ.source := by rw [hs]; exact hwsource'
    have hinv := eⱼ.left_inv hwsource
    change q (eᵢ.symm w) = q (eⱼ.symm (eⱼ (eᵢ.symm w)))
    rw [hinv]
  let ρ := δ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hclosed : Metric.closedBall z ρ ⊆ Metric.ball z δ :=
    Metric.closedBall_subset_ball (by dsimp [ρ]; linarith)
  have hHolderClosed : HolderOnWith (C * L ^ (α : ℝ)) α
      (q ∘ eᵢ.symm) (Metric.closedBall z ρ) := by
    intro w hw w' hw'
    rw [hEq (hclosed hw), hEq (hclosed hw')]
    exact hHolder' w (hclosed hw) w' (hclosed hw')
  let C' : ℝ≥0 := max C (C * L ^ (α : ℝ))
  have hNormScalar : ∀ w ∈ Metric.closedBall z ρ, |q (eᵢ.symm w)| ≤ C' := by
    intro w hw
    have hTw : T w ∈ interior (cover.piece j) :=
      hmapInterior (hsub₁ (hclosed hw))
    have hSourceBound := hGauge.1 0 (by norm_num) (T w) (interior_subset hTw)
    rw [norm_iteratedFDeriv_zero] at hSourceBound
    have hSourceAbs :
        |q ((chartAt (EuclideanSpace ℂ (Fin n)) (cover.base j)).symm (T w))| ≤ (C : ℝ) := by
      simpa [Function.comp_def, Real.norm_eq_abs] using hSourceBound
    have hEqw := hEq (hclosed hw)
    change q (eᵢ.symm w) = q (eⱼ.symm (eⱼ (eᵢ.symm w))) at hEqw
    have hValue :
        q ((chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).symm w) =
          q ((chartAt (EuclideanSpace ℂ (Fin n)) (cover.base j)).symm (T w)) := by
      rw [extChartAt_coe_symm] at hEqw
      rw [extChartAt_coe_symm] at hEqw
      simpa [T, eᵢ, eⱼ, extChartAt_coe_symm] using hEqw
    change |q ((chartAt (EuclideanSpace ℂ (Fin n)) (cover.base i)).symm w)| ≤ (C' : ℝ)
    rw [hValue]
    exact hSourceAbs.trans (by
      exact_mod_cast (le_max_left C (C * L ^ (α : ℝ))))
  have hHolderClosed' : HolderOnWith C' α (q ∘ eᵢ.symm) (Metric.closedBall z ρ) :=
    hHolderClosed.mono_const (le_max_right C _)
  exact ⟨L, ρ, hρ, isCompact_closedBall z ρ,
    holderBoundOn_zero_of_scalar_data hNormScalar hHolderClosed'⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem exists_local_rhs_holder_from_finiteChartGauge
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (q : M → ℝ) (α : ℝ≥0) (i : cover.ι)
    (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ cover.piece i)
    (hGauge : finiteChartHolderGauge cover 0 α q < ⊤) :
    ∃ (C : ℝ≥0) (j : cover.ι) (y : EuclideanSpace ℂ (Fin n))
      (L : ℝ≥0) (ρ : ℝ),
      z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).target ∧
      y ∈ interior (cover.piece j) ∧
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base j)).symm y =
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm z ∧
      0 < ρ ∧ IsCompact (Metric.closedBall z ρ) ∧
      HolderBoundOn 0 α (max C (C * L ^ (α : ℝ))) (Metric.closedBall z ρ)
        (q ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
  obtain ⟨C, hChart⟩ := (finiteChartHolderGauge_lt_top_iff cover 0 α q).mp hGauge
  obtain ⟨j, y, hzTarget, hy, hxy⟩ := chartPiece_interior_refinement cover i z hz
  obtain ⟨L, ρ, hρ, hCompact, hHolder⟩ := exists_chart_rhs_holder_on_overlap
    cover q α C i j z y hzTarget hy hxy (hChart j)
  exact ⟨C, j, y, L, ρ, hzTarget, hy, hxy, hρ, hCompact, hHolder⟩

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem finiteChartHolderGauge_toReal_le_of_chartwiseBound
    (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α C : ℝ≥0) (f : M → ℝ)
    (hchart : ∀ i : cover.ι,
      HolderBoundOn 2 α C (cover.piece i)
        (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm)) :
    (finiteChartHolderGauge cover 2 α f).toReal ≤ 4 * (C : ℝ) := by
  have hGauge : finiteChartHolderGauge cover 2 α f ≤
      (∑ _j ∈ Finset.range (2 + 1), (C : ℝ≥0∞)) + C := by
    unfold finiteChartHolderGauge
    apply iSup_le
    intro i
    exact CalabiYau.Schauder.eContDiffHolderGaugeOn_le (fun _ ↦ C) C
      (hchart i).1 (HolderWith.restrict_iff.mpr (hchart i).2)
  have hGauge' : finiteChartHolderGauge cover 2 α f ≤ (4 * C : ℝ≥0∞) := by
    convert hGauge using 1; norm_num; ring
  calc
    (finiteChartHolderGauge cover 2 α f).toReal ≤ ((4 * C : ℝ≥0) : ℝ≥0∞).toReal :=
      ENNReal.toReal_mono ENNReal.coe_ne_top hGauge'
    _ = 4 * (C : ℝ) := by simp

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- The per-chart interior estimate after coefficient and overlap transfer. The hard local
nested-ball and finite compact-patch argument is isolated here with its quantitative common bound. -/
private theorem exists_finiteChart_local_laplacian_holder_chartwise [Nonempty M]
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hSch : InteriorSchauderEstimate n) :
    ∃ C : ℝ≥0, ∀ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
      ∀ K : ℝ, (hK : 0 ≤ K) → (∀ x, |f x| ≤ K) →
        finiteChartHolderGauge cover 0 α (ω₁.laplacian f) < ⊤ →
        ∀ i : cover.ι, ∃ Ci : ℝ≥0,
          HolderBoundOn 2 α Ci (cover.piece i)
            (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) ∧
          Ci ≤ C * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toNNReal +
            ⟨K, hK⟩) := by
  classical
  have hpiece (i : cover.ι) : ∃ C : ℝ≥0, ∀ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
      ∀ K₀ : ℝ≥0, (∀ x, |f x| ≤ K₀) →
        finiteChartHolderGauge cover 0 α (ω₁.laplacian f) < ⊤ →
        HolderBoundOn 2 α
          (C * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toNNReal + K₀))
          (cover.piece i)
          (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
    obtain ⟨D⟩ := exists_bufferedChartBalls cover i
    obtain ⟨B, hB⟩ := exists_bufferedBalls_rhs_gauge_factor cover i D α
    obtain ⟨A, hA⟩ := exists_compactPatch_holder_factor (cover.piece i)
      (cover.isCompact_piece i) (fun p : D.ι => Metric.closedBall (D.center p) (D.radius p))
      D.inner_covers α
    let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)
    have hlocal (p : D.ι) : ∃ c : ℝ≥0, ∀ f : M → ℝ,
        ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
        ∀ K₀ : ℝ≥0, (∀ x, |f x| ≤ K₀) →
          finiteChartHolderGauge cover 0 α (ω₁.laplacian f) < ⊤ →
          HolderBoundOn 2 α
            (c * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toNNReal + K₀))
            (Metric.closedBall (D.center p) (D.radius p)) (f ∘ e.symm) := by
      let U := Metric.ball (D.center p) (2 * D.radius p)
      let V := Metric.closedBall (D.center p) (D.radius p)
      let W := Metric.closedBall (D.center p) (2 * D.radius p)
      have hUW : U ⊆ W := Metric.ball_subset_closedBall
      have hWU : W ⊆ e.target := D.outer_in_target p
      have hVU : closure V ⊆ U := by
        rw [Metric.isClosed_closedBall.closure_eq]
        exact Metric.closedBall_subset_ball (by linarith [D.radius_pos p])
      obtain ⟨lam, Q, hlam, hEll, hCoeff⟩ := exists_inverse_metric_coefficients_on_compact
        ω₁ (cover.base i) W (isCompact_closedBall _ _) hWU α hα₁
      obtain ⟨S, hS⟩ := hSch.holderBoundOn_of_contDiffOn 0 α hα₀ hα₁ lam Q hlam U V
        Metric.isOpen_ball (by simpa [V] using isCompact_closedBall (D.center p) (D.radius p)) hVU
      refine ⟨S * (B + 1), ?_⟩
      intro f hf K₀ hbound hGauge
      let u := f ∘ e.symm
      let G := (finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toNNReal
      have hu : ContDiffOn ℝ ∞ u U := by
        have h := (contMDiff_iff.mp hf).2 (cover.base i) 0
        have ht : ContDiffOn ℝ ∞ u e.target := by
          simpa [u, e, extChartAt, chartAt_self_eq] using h
        exact ht.mono (hUW.trans hWU)
      have hmetric (j k : Fin n) :
          ContDiffOn ℝ ∞ (fun z => (ω₁.metricInChart (cover.base i) z)⁻¹ j k) U := by
        obtain ⟨_, _, ht⟩ := exists_metricInChartInverseEntryHolderBound
          ω₁ (cover.base i) W (isCompact_closedBall _ _) hWU α hα₁ j k
        exact ht.mono (hUW.trans hWU)
      have hRhs := (hB (ω₁.laplacian f) hGauge p).mono_set hUW
      have hop (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
          ω₁.laplacian f (e.symm z) =
          complexEllipticOp (fun w => (ω₁.metricInChart (cover.base i) w)⁻¹) u z :=
        chartLaplacian_eq_complexEllipticOp ω₁ f hf (cover.base i) z (hWU (hUW hz))
      have hLu : HolderBoundOn 0 α (B * G) U
          (complexEllipticOp (fun w => (ω₁.metricInChart (cover.base i) w)⁻¹) u) := by
        apply holderBoundOn_zero_of_scalar_data
        · intro z hz
          rw [← hop z hz]
          simpa [e, G, norm_iteratedFDeriv_zero, Function.comp_def] using hRhs.1 0 le_rfl z hz
        · intro z hz w hw
          rw [← hop z hz, ← hop w hw]
          exact holderBoundOn_zero_scalar_holder hRhs z hz w hw
      have hEstimate := hS (fun w => (ω₁.metricInChart (cover.base i) w)⁻¹) u
        hmetric hu (fun z hz => hEll z (hUW hz))
        (fun j k => (hCoeff j k).mono_set hUW) K₀ (B * G) hLu (fun z _ => hbound (e.symm z))
      apply hEstimate.mono_const
      calc
        S * (B * G + K₀) ≤ S * ((B + 1) * (G + K₀)) := by
          gcongr
          calc
            B * G + K₀ ≤ B * G + K₀ + (B * K₀ + G) := le_add_of_nonneg_right (by positivity)
            _ = (B + 1) * (G + K₀) := by ring
        _ = (S * (B + 1)) * (G + K₀) := by ring
    let c (p : D.ι) := Classical.choose (hlocal p)
    have hc (p : D.ι) := Classical.choose_spec (hlocal p)
    let T : ℝ≥0 := ∑ p : D.ι, c p
    refine ⟨A * T, ?_⟩
    intro f hf K₀ hbound hGauge
    have hpatch : ∀ p : D.ι, HolderBoundOn 2 α
        (T * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toNNReal + K₀))
        (Metric.closedBall (D.center p) (D.radius p)) (f ∘ e.symm) := by
      intro p
      apply (hc p f hf K₀ hbound hGauge).mono_const
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum (fun q _ => (zero_le : 0 ≤ c q)) (Finset.mem_univ p)
    simpa [e, mul_assoc] using hA (f ∘ e.symm)
      (T * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toNNReal + K₀)) hpatch
  let c (i : cover.ι) := Classical.choose (hpiece i)
  have hc (i : cover.ι) := Classical.choose_spec (hpiece i)
  let C : ℝ≥0 := ∑ i : cover.ι, c i
  refine ⟨C, ?_⟩
  intro f hf K hK hbound hGauge i
  refine ⟨c i * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toNNReal + ⟨K, hK⟩),
    hc i f hf ⟨K, hK⟩ hbound hGauge, ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact Finset.single_le_sum (fun j _ => (zero_le : 0 ≤ c j)) (Finset.mem_univ i)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
private theorem exists_finiteChart_local_laplacian_holder_inequality [Nonempty M]
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hSch : InteriorSchauderEstimate n) :
    ∃ C : ℝ≥0, ∀ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
      ∀ K : ℝ, (∀ x, |f x| ≤ K) →
        finiteChartHolderGauge cover 2 α f < ⊤ →
        finiteChartHolderGauge cover 0 α (ω₁.laplacian f) < ⊤ →
        (finiteChartHolderGauge cover 2 α f).toReal ≤
          (C : ℝ) * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal + K) := by
  obtain ⟨Cbase, hbase⟩ := exists_finiteChart_local_laplacian_holder_chartwise
    ω₁ cover α hα₀ hα₁ hSch
  refine ⟨4 * Cbase, ?_⟩
  intro f hf K hbound _hGauge₂ hGauge₀
  have hK : 0 ≤ K := by
    obtain ⟨x⟩ := ‹Nonempty M›
    exact (abs_nonneg (f x)).trans (hbound x)
  let K0 : ℝ≥0 := ⟨K, hK⟩
  let G0 : ℝ≥0 := (finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toNNReal
  let Ccharts : ℝ≥0 := Cbase * (G0 + K0)
  have hcharts := hbase f hf K hK hbound hGauge₀
  have hcommon : ∀ i : cover.ι, HolderBoundOn 2 α Ccharts (cover.piece i)
      (f ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (cover.base i)).symm) := by
    intro i
    obtain ⟨Ci, hCi, hCi_le⟩ := hcharts i
    exact hCi.mono_const (by simpa [Ccharts, G0, K0] using hCi_le)
  have hGauge₂bound := finiteChartHolderGauge_toReal_le_of_chartwiseBound
    cover α Ccharts f hcommon
  have hGco : (G0 : ℝ≥0∞) = finiteChartHolderGauge cover 0 α (ω₁.laplacian f) :=
    ENNReal.coe_toNNReal (ne_of_lt hGauge₀)
  have hGreal : (G0 : ℝ) =
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal := by
    calc
      (G0 : ℝ) = ((G0 : ℝ≥0∞).toReal) := by simp
      _ = _ := by rw [hGco]
  have hSum : ((G0 + K0 : ℝ≥0) : ℝ) =
      (finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal + K := by
    change (G0 : ℝ) + (K0 : ℝ) = _
    rw [hGreal]
    rfl
  have hCcast : (Ccharts : ℝ) =
      (Cbase : ℝ) * ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal + K) := by
    change ((Cbase * (G0 + K0) : ℝ≥0) : ℝ) = _
    calc
      _ = (Cbase : ℝ) * ((G0 + K0 : ℝ≥0) : ℝ) := by simp
      _ = _ := by rw [hSum]
  calc
    (finiteChartHolderGauge cover 2 α f).toReal ≤ 4 * (Ccharts : ℝ) := hGauge₂bound
    _ = (4 * (Cbase : ℝ)) *
        ((finiteChartHolderGauge cover 0 α (ω₁.laplacian f)).toReal + K) := by
      rw [hCcast]
      ring

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] in
/-- Finite-chart Schauder estimate conditional on the local interior Schauder theorem. -/
theorem exists_finiteChart_local_laplacian_holder_estimate [Nonempty M]
    (ω₁ : KahlerForm n M) (cover : CompactChartCover (EuclideanSpace ℂ (Fin n)) M)
    (α : ℝ≥0) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hSch : InteriorSchauderEstimate n) :
    HasFiniteChartLocalLaplacianHolderEstimate ω₁ cover α := by
  obtain ⟨C, hIneq⟩ := exists_finiteChart_local_laplacian_holder_inequality
    ω₁ cover α hα₀ hα₁ hSch
  refine ⟨C, ?_⟩
  intro f hf K hbound
  have hfFinite := smooth_finiteChartHolderGauge cover 2 α hα₁ f hf
  have hLapSmooth := ω₁.contMDiff_laplacian hf
  have hLapFinite := smooth_finiteChartHolderGauge cover 0 α hα₁
    (ω₁.laplacian f) hLapSmooth
  exact ⟨hfFinite, hLapFinite, hIneq f hf K hbound hfFinite hLapFinite⟩

end KahlerForm
