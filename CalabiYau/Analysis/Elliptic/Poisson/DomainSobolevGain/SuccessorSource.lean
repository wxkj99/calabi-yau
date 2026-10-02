module

public import CalabiYau.Analysis.Elliptic.Poisson.DomainSobolevGain.DifferentiatedData
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.Differentiated.BilinearH1Compl

/-!
# Compensated forcing for the next differentiated chart equation

Adapted from DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/VariationalIdentity/SuccessorSource.lean`, lines 251–289 and 851–920.
The density occurs once in the weak equation; the forcing itself is the
compact-support indicator of the numerator divided by that density.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.Analysis.Laplacian
open CalabiYau.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open CalabiYau.Analysis.Laplacian.ChartBilinearH1Compl
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The divergence coefficient commutator and the differentiated density/source terms. -/
def successorChartForcingNumerator
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (previousForcing : EuclN → ℝ) (l : Fin (Module.finrank ℝ E))
    (y : EuclN) : ℝ :=
  (∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1) *
        chosenMthMixedPartialChartPushedU
          (I := I) (M := M) g α u_h (m + 1) (Fin.cons i dirs) y)
  + (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU
            (I := I) (M := M) g α u_h (m + 2)
            (Fin.cons i (Fin.snoc dirs j)) y)
  - densityDerivOnEuclid (I := I) g α l y *
      chosenMthMixedPartialChartPushedU
        (I := I) (M := M) g α u_h m dirs y
  + densityDerivOnEuclid (I := I) g α l y * previousForcing y
  + densityOnEuclid (I := I) g α y *
      Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 l previousForcing
        (chartTargetEuclid (I := I) (M := M) α) y

/-- Raw successor forcing, not multiplied by an additional density or chart cutoff. -/
def successorChartForcing
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (previousForcing : EuclN → ℝ) (l : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  Set.indicator (chartImagePOUTsupport (I := I) (M := M) α)
    (fun y => successorChartForcingNumerator
        (I := I) (M := M) g α u_h m dirs previousForcing l y /
      densityOnEuclid (I := I) g α y)

omit [NeZero (Module.finrank ℝ E)] in
/-- The compactly supported successor forcing belongs to weighted L².
This does not assert W¹,² regularity of the previous or successor forcing. -/
private theorem chosenMth_memWkp_of_chartPushed_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) :
    ∀ k : ℕ,
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (k + m) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) →
      ∀ idx : Fin m → Fin (Module.finrank ℝ E),
        Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) k 2
          (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
          (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h _idx
      simpa [chosenMthMixedPartialChartPushedU] using h
  | succ m ih =>
      intro k h idx
      have h' : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) ((k + 1) + m) 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (chartTargetEuclid (I := I) (M := M) α) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 m] using h
      exact (ih (k + 1) h' (Fin.init idx)).chosenWeakPartial_mem
        (idx (Fin.last m))

omit [NeZero (Module.finrank ℝ E)] in
private theorem chosenMth_memLp_of_chartPushed_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) m 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    MemLp (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx) 2
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  exact (chosenMth_memWkp_of_chartPushed_memWkp g α u_h m 0
    (by simpa only [Nat.zero_add] using h) idx).memLp

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem chosenWeakPartialOrZero_memLp_unconditionally
    {u : EuclN → ℝ} {Ω : Set EuclN} (l : Fin (Module.finrank ℝ E)) :
    MemLp (Sobolev.Euclidean.chosenWeakPartialOrZero
      (d := Module.finrank ℝ E) 2 l u Ω) 2
      ((volume : Measure EuclN).restrict Ω) := by
  classical
  by_cases hW : Sobolev.Euclidean.MemW1p 2 u Ω
  · exact Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem hW l
  · rw [Sobolev.Euclidean.chosenWeakPartialOrZero_of_not_mem hW l]
    exact MemLp.zero

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem abs_bound_on_compact
    {K : Set EuclN} (hK : IsCompact K) {f : EuclN → ℝ}
    (hf : ContinuousOn f K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f y| ≤ C := by
  classical
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_rfl, ?_⟩
    intro y hy
    rw [hK_empty] at hy
    exact absurd hy (Set.notMem_empty y)
  have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
  have habs : ContinuousOn (fun y => |f y|) K := continuous_abs.comp_continuousOn hf
  obtain ⟨ymax, hymax, hmax⟩ := hK.exists_isMaxOn hK_ne habs
  exact ⟨|f ymax|, abs_nonneg _, fun y hy => hmax hy⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem secondDirectional_weightedInvGram_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j l q : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (EuclideanSpace.single q 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hΩopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hbase := weightedInvGramDerivOnEuclid_contDiffOn
    (I := I) (M := M) g α i j l
  have hder : ContDiffOn ℝ ∞
      (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩopen).1 hbase).2
  have heval : ContDiff ℝ ∞
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single q (1 : ℝ))) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single q (1 : ℝ))).contDiff
  exact (heval.contDiffOn.comp hder (mapsTo_univ _ _)).continuousOn

private theorem memLp_mul_of_bounded_left
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f b : X → ℝ}
    (hf : MemLp f 2 μ) (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂μ, ‖b x‖ ≤ C) :
    MemLp (fun x => b x * f x) 2 μ := by
  refine MemLp.mono (hf.const_mul C) (hb.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hbound] with x hx
  calc
    ‖b x * f x‖ = ‖b x‖ * ‖f x‖ := norm_mul _ _
    _ ≤ C * ‖f x‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = ‖C * f x‖ := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg hC]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem memLp_mul_of_continuousOn_bounded
    {K : Set EuclN} (hK : IsCompact K) (hKmeas : MeasurableSet K)
    {b f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict K))
    (hb : ContinuousOn b K) :
    MemLp (fun y => b y * f y) 2 ((volume : Measure EuclN).restrict K) := by
  obtain ⟨C, hC, hbound⟩ := abs_bound_on_compact hK hb
  have hbmeas : AEStronglyMeasurable b
      ((volume : Measure EuclN).restrict K) :=
    hb.aestronglyMeasurable_of_isCompact hK hKmeas
  have hboundAE : ∀ᵐ y ∂((volume : Measure EuclN).restrict K), ‖b y‖ ≤ C := by
    filter_upwards [MeasureTheory.ae_restrict_mem hKmeas] with y hy
    simpa only [Real.norm_eq_abs] using hbound y hy
  exact memLp_mul_of_bounded_left hf hbmeas hC hboundAE

private theorem memLp_restrict_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {Ω K : Set X}
    {f : X → ℝ} {p : ℝ≥0∞}
    (hK_meas : MeasurableSet K) (hK_sub : K ⊆ Ω)
    (hf : MemLp f p (μ.restrict Ω)) :
    MemLp f p (μ.restrict K) := by
  have hrestrict := hf.restrict K
  have hEq : (μ.restrict Ω).restrict K = μ.restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_left.mpr hK_sub
  rw [hEq] at hrestrict
  exact hrestrict

private theorem memLp_fin_sum
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → X → ℝ} {p : ℝ≥0∞}
    (h : ∀ i, MemLp (f i) p μ) :
    MemLp (fun x => ∑ i, f i x) p μ := by
  classical
  refine Finset.induction_on Finset.univ ?_ ?_
  · simp
  · intro a s ha ih
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem memLp_volume_compact_of_memLp_weighted
    {g : SmoothRiemannianMetric I M} (α : M) {K : Set EuclN}
    (hKcompact : IsCompact K) (hKmeas : MeasurableSet K)
    (hKin : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {f : EuclN → ℝ}
    (hf : MemLp f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α))) :
    MemLp f 2 ((volume : Measure EuclN).restrict K) := by
  obtain ⟨c, hc, hle⟩ :=
    volume_restrict_compact_le_chartPulledWeightedMeasure (I := I) (M := M)
      (g := g) α hKcompact hKmeas hKin
  exact hf.of_measure_le_smul (c := ENNReal.ofReal c)
    ENNReal.ofReal_ne_top hle

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private theorem chartPulledWeighted_restrict_compact_le_volume_local
    {g : SmoothRiemannianMetric I M} (α : M) {K : Set EuclN}
    (hKcompact : IsCompact K)
    (hKin : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ c : ℝ, 0 < c ∧
      (chartPulledWeightedMeasure (I := I) g α).restrict K ≤
        ENNReal.ofReal c • ((volume : Measure EuclN).restrict K) := by
  classical
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  obtain ⟨_cmin, cmax, hcmin, hcminmax, hbd⟩ :=
    densityOnEuclid_bounded_on_compact (I := I) (M := M) g α hKcompact hKin
  refine ⟨cmax, lt_of_lt_of_le hcmin hcminmax, ?_⟩
  refine Measure.le_iff.2 ?_
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.restrict_apply hA]
  unfold chartPulledWeightedMeasure
  rw [withDensity_apply _ (hA.inter hKmeas)]
  have hbd_integral :
      ∫⁻ y in A ∩ K, ENNReal.ofReal (densityOnEuclid (I := I) g α y)
        ∂(volume : Measure EuclN) ≤
      ∫⁻ _y in A ∩ K, ENNReal.ofReal cmax ∂(volume : Measure EuclN) := by
    apply MeasureTheory.setLIntegral_mono_ae'
    · exact hA.inter hKmeas
    · refine Filter.Eventually.of_forall fun y hy => ?_
      apply ENNReal.ofReal_le_ofReal
      exact (hbd y hy.2).2
  have hconst :
      ∫⁻ _y in A ∩ K, ENNReal.ofReal cmax ∂(volume : Measure EuclN) =
        ENNReal.ofReal cmax * (volume : Measure EuclN) (A ∩ K) := by
    rw [MeasureTheory.setLIntegral_const]
  rw [smul_eq_mul]
  exact hbd_integral.trans (le_of_eq hconst)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private theorem memLp_weighted_compact_of_memLp_volume
    {g : SmoothRiemannianMetric I M} (α : M) {K : Set EuclN}
    (hKcompact : IsCompact K)
    (hKin : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    {f : EuclN → ℝ}
    (hf : MemLp f 2 ((volume : Measure EuclN).restrict K)) :
    MemLp f 2 ((chartPulledWeightedMeasure (I := I) g α).restrict K) := by
  obtain ⟨c, hc, hle⟩ :=
    chartPulledWeighted_restrict_compact_le_volume_local (I := I) (M := M)
      (g := g) α hKcompact hKin
  exact hf.of_measure_le_smul (c := ENNReal.ofReal c)
    ENNReal.ofReal_ne_top hle

omit [NeZero (Module.finrank ℝ E)] in
private theorem successorNumerator_memLp_compact
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}
    {dirs : Fin m → Fin (Module.finrank ℝ E)}
    {previousForcing : EuclN → ℝ}
    (h_chart_H_m_plus_1 : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (h_previous_memLp : MemLp previousForcing 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    {l : Fin (Module.finrank ℝ E)}
    {K : Set EuclN} (hK : IsCompact K)
    (hKin : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    MemLp (successorChartForcingNumerator g α u_h m dirs previousForcing l) 2
      ((volume : Measure EuclN).restrict K) := by
  classical
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hX1 : ∀ i : Fin (Module.finrank ℝ E),
      MemLp (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
        (m + 1) (Fin.cons i dirs)) 2 ((volume : Measure EuclN).restrict K) := by
    intro i
    exact memLp_restrict_subset hKmeas hKin
      (chosenMth_memLp_of_chartPushed_memWkp g α u_h (m + 1)
        h_chart_H_m_plus_1 (Fin.cons i dirs))
  have hX2 : ∀ i j : Fin (Module.finrank ℝ E),
      MemLp (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
        (m + 2) (Fin.cons i (Fin.snoc dirs j))) 2
        ((volume : Measure EuclN).restrict K) := by
    intro i j
    exact memLp_restrict_subset hKmeas hKin
      (chosenMth_memLp_of_chartPushed_memWkp g α u_h (m + 2)
        h_chart_H_m_plus_2 (Fin.cons i (Fin.snoc dirs j)))
  have hX0 : MemLp (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
        m dirs) 2 ((volume : Measure EuclN).restrict K) := by
    apply memLp_restrict_subset hKmeas hKin
    apply chosenMth_memLp_of_chartPushed_memWkp g α u_h m
    exact h_chart_H_m_plus_1.le_of_le (by omega)
  have hprevVol := memLp_volume_compact_of_memLp_weighted
    (I := I) (M := M) (g := g) α hK hKmeas hKin h_previous_memLp
  have hweak : MemLp (Sobolev.Euclidean.chosenWeakPartialOrZero
      (d := Module.finrank ℝ E) 2 l previousForcing
      (chartTargetEuclid (I := I) (M := M) α)) 2
      ((volume : Measure EuclN).restrict K) := by
    apply memLp_restrict_subset hKmeas hKin
    exact chosenWeakPartialOrZero_memLp_unconditionally l
  have hdercoef (i j : Fin (Module.finrank ℝ E)) :
      ContinuousOn
        (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j 1)) K :=
    (secondDirectional_weightedInvGram_continuousOn g α i j l j).mono hKin
  have hgramcoef (i j : Fin (Module.finrank ℝ E)) :
      ContinuousOn (weightedInvGramDerivOnEuclid (I := I) g α i j l) K :=
    (weightedInvGramDerivOnEuclid_contDiffOn (I := I) (M := M) g α i j l).continuousOn.mono hKin
  have hdensityDeriv : ContinuousOn (densityDerivOnEuclid (I := I) g α l) K :=
    (densityDerivOnEuclid_continuousOn (I := I) (M := M) g α l).mono hKin
  have hdensity : ContinuousOn (densityOnEuclid (I := I) g α) K :=
    (densityOnEuclid_contDiffOn (I := I) (M := M) g α).continuousOn.mono hKin
  have hterm1 : MemLp (fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
          (EuclideanSpace.single j (1 : ℝ)) *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 1) (Fin.cons i dirs) y) 2 ((volume : Measure EuclN).restrict K) := by
    apply memLp_fin_sum
    intro i
    apply memLp_fin_sum
    intro j
    exact memLp_mul_of_continuousOn_bounded hK hKmeas (hX1 i) (hdercoef i j)
  have hterm2 : MemLp (fun y => ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        weightedInvGramDerivOnEuclid (I := I) g α i j l y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            (m + 2) (Fin.cons i (Fin.snoc dirs j)) y) 2
      ((volume : Measure EuclN).restrict K) := by
    apply memLp_fin_sum
    intro i
    apply memLp_fin_sum
    intro j
    exact memLp_mul_of_continuousOn_bounded hK hKmeas (hX2 i j) (hgramcoef i j)
  have hterm3 : MemLp (fun y => densityDerivOnEuclid (I := I) g α l y *
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs y) 2
      ((volume : Measure EuclN).restrict K) :=
    memLp_mul_of_continuousOn_bounded hK hKmeas hX0 hdensityDeriv
  have hterm4 : MemLp (fun y => densityDerivOnEuclid (I := I) g α l y *
      previousForcing y) 2 ((volume : Measure EuclN).restrict K) :=
    memLp_mul_of_continuousOn_bounded hK hKmeas hprevVol hdensityDeriv
  have hterm5 : MemLp (fun y => densityOnEuclid (I := I) g α y *
      Sobolev.Euclidean.chosenWeakPartialOrZero
        (d := Module.finrank ℝ E) 2 l previousForcing
        (chartTargetEuclid (I := I) (M := M) α) y) 2
      ((volume : Measure EuclN).restrict K) :=
    memLp_mul_of_continuousOn_bounded hK hKmeas hweak hdensity
  unfold successorChartForcingNumerator
  have hsum := (((hterm1.add hterm2).sub hterm3).add hterm4).add hterm5
  convert hsum using 1
  ext y
  simp only [Pi.add_apply, Pi.sub_apply]

private theorem memLp_indicator_of_memLp_restrict
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {Ω K : Set X}
    {f : X → ℝ}
    (hK_meas : MeasurableSet K) (hK_sub : K ⊆ Ω)
    (hf : MemLp f 2 (μ.restrict K)) :
    MemLp (K.indicator f) 2 (μ.restrict Ω) := by
  rw [memLp_indicator_iff_restrict hK_meas]
  have hEq : (μ.restrict Ω).restrict K = μ.restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_left.mpr hK_sub
  rw [hEq]
  exact hf

omit [NeZero (Module.finrank ℝ E)] in
theorem successorChartForcing_memLp
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}
    {dirs : Fin m → Fin (Module.finrank ℝ E)}
    (h_chart_H_m_plus_1 :
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (h_chart_H_m_plus_2 :
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((h1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    {previousForcing : EuclN → ℝ}
    (h_previous_memLp : MemLp previousForcing 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))
    {l : Fin (Module.finrank ℝ E)} :
    MemLp (successorChartForcing g α u_h m dirs previousForcing l) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  let K := chartImagePOUTsupport (I := I) (M := M) α
  have hK : IsCompact K := chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hKin : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hnum := successorNumerator_memLp_compact
    (I := I) (M := M) (dirs := dirs) h_chart_H_m_plus_1 h_chart_H_m_plus_2
    h_previous_memLp (l := l) hK hKin
  have hInv : ContinuousOn (fun y => 1 / densityOnEuclid (I := I) g α y) K :=
    (one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α).continuousOn.mono hKin
  have hquot_vol : MemLp
      (fun y => successorChartForcingNumerator (I := I) (M := M)
        g α u_h m dirs previousForcing l y / densityOnEuclid (I := I) g α y)
      2 ((volume : Measure EuclN).restrict K) := by
    have hmul := memLp_mul_of_continuousOn_bounded hK hKmeas hnum hInv
    convert hmul using 1
    ext y
    simp [div_eq_mul_inv, mul_comm]
  have hquot_weighted := memLp_weighted_compact_of_memLp_volume
    (I := I) (M := M) (g := g) α hK hKin hquot_vol
  have hforcing := memLp_indicator_of_memLp_restrict hKmeas hKin hquot_weighted
  simpa [successorChartForcing, K] using hforcing

end CalabiYau.PoissonDomainRegularity
