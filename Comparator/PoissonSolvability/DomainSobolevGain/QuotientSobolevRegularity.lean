module

public import Comparator.PoissonSolvability.DomainSobolevGain.NumeratorSobolevRegularity
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CrossTermIBP
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

/-!
# Sobolev regularity of the successor numerator divided by density

Adapted from DifferentialGeometry at `7a48598d35109aa99d1cc678e2724c213cdf4ff3`,
`Iterated/NirenbergInterior/EffectiveSourceSuccessorRegularity.lean`, lines 989–1042.
This is the quotient before the POU-support indicator, not the successor forcing.
The finite descending application takes `K = r - (m + 1)` and needs only the
current solution H^(r+1). Checked local multiplier and exact-order support
providers are private; the numerator product estimates are imported separately.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace CalabiYau.PoissonDomainRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.Analysis.Laplacian
open Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open CalabiYau.PoissonDomainRegularity Sobolev.Euclidean
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DifferentiatedCrossTermIBP
open CalabiYau.Laplacian.MetricExtension hiding chartTargetEuclid chartTargetEuclid_isOpen

private theorem chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) :
    ∀ (k : ℕ),
      Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (k + m) 2
        (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) →
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) k 2
          (chosenMthMixedPartialChartPushedU g α u_h m idx)
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent _idx
      simpa [chosenMthMixedPartialChartPushedU] using h_parent
  | succ m ih =>
      intro k h_parent idx
      have h_parent' : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E)
          ((k + 1) + m) 2
          (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
            ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
          (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
        simpa only [Nat.add_assoc, Nat.add_comm 1 m] using h_parent
      exact (ih (k + 1) h_parent' (Fin.init idx)).chosenWeakPartial_mem
        (idx (Fin.last m))

private theorem chosenMthMixedPartialChartPushedU_memW1p_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ)
    (h_parent : Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) (m + 1) 2
      (Sobolev.Chart.chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α))
    (idx : Fin m → Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chosenMthMixedPartialChartPushedU g α u_h m idx)
      (Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α) := by
  apply Sobolev.Euclidean.MemWkp.one_iff_memW1p.mp
  exact chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    g α u_h m 1 (by simpa only [Nat.add_comm 1 m] using h_parent) idx

private lemma chosenPartial_ae_zero_on_open_sub
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω V : Set (EuclideanSpace ℝ (Fin d))}
    (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : DeGiorgi.MemW1p (d := d) p u Ω)
    (hu_zero : u =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict V]
      (fun _ => (0 : ℝ))) (i : Fin d) :
    chosenWeakPartialOrZero p i u Ω
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict V]
      (fun _ => (0 : ℝ)) := by
  classical
  have huV : DeGiorgi.MemW1p (d := d) p u V := by
    refine ⟨hu.1.mono_measure (Measure.restrict_mono_set _ hV_sub), ?_⟩
    intro j
    obtain ⟨g, hg, hw⟩ := hu.2 j
    exact ⟨g, hg.mono_measure (Measure.restrict_mono_set _ hV_sub),
      DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub hw⟩
  have hΩV := DeGiorgi.HasWeakPartialDeriv.restrict hV hV_sub
    (chosenWeakPartialOrZero_isWeakPartial_of_mem hu i)
  have hVweak := chosenWeakPartialOrZero_isWeakPartial_of_mem huV i
  have huniq := DeGiorgi.HasWeakPartialDeriv.ae_eq hV hΩV hVweak
    (((chosenWeakPartialOrZero_memLp_of_mem hu i).mono_measure
      (Measure.restrict_mono_set _ hV_sub)).locallyIntegrable hp)
    ((chosenWeakPartialOrZero_memLp_of_mem huV i).locallyIntegrable hp)
  exact huniq.trans (chosenWeakPartialOrZero_ae_zero_of_ae_zero hp hV hu_zero i)

lemma successor_numerator_ae_zero
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hK : IsClosed K)
    (A B X Y : Fin d → Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (C D Z q : EuclideanSpace ℝ (Fin d) → ℝ)
    (hq : DeGiorgi.MemW1p (d := d) 2 q Ω) (l : Fin d)
    (hX : ∀ i j, X i j =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
      (Ω \ K)] (fun _ => (0 : ℝ)))
    (hY : ∀ i j, Y i j =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
      (Ω \ K)] (fun _ => (0 : ℝ)))
    (hZ : Z =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
      (Ω \ K)] (fun _ => (0 : ℝ)))
    (hq0 : q =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
      (Ω \ K)] (fun _ => (0 : ℝ))) :
    (fun y => (∑ i, ∑ j, A i j y * X i j y) +
      (∑ i, ∑ j, B i j y * Y i j y) - C y * Z y + C y * q y +
      D y * chosenWeakPartialOrZero 2 l q Ω y)
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (Ω \ K)]
      (fun _ => (0 : ℝ)) := by
  have hV := hΩ.sdiff hK
  have hE := chosenPartial_ae_zero_on_open_sub
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV (fun _ hy => hy.1) hq hq0 l
  have hXa : ∀ᵐ y ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
      (Ω \ K)), ∀ i j, X i j y = 0 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    exact hX i
  have hYa : ∀ᵐ y ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict
      (Ω \ K)), ∀ i j, Y i j y = 0 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    exact hY i
  filter_upwards [hXa, hYa, hZ, hq0, hE] with y hx hy hz hqz he
  simp [hx, hy, hz, hqz, he]

private lemma selectedMixed_ae_zero_of_exact_chart_order
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) (m : ℕ) :
    MemWkp m 2
      (chartPushed (chartAtlasPOU I M) α ((H1ComplToLp g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) →
    ∀ dirs : Fin m → Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU g α u_h m dirs
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
  induction m with
  | zero =>
    intro _ dirs
    have hV := (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
    refine (ae_restrict_iff' hV.measurableSet).mpr (Filter.Eventually.of_forall ?_)
    intro y hy
    exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _ hy.1 hy.2
  | succ m ih =>
    intro h dirs
    have h_inner := chosenMthMixedPartialChartPushedU_memW1p_two g α u_h m h
      (Fin.init dirs)
    have h_low : MemWkp m 2
        (chartPushed (chartAtlasPOU I M) α ((H1ComplToLp g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
      h.le_of_le (by omega)
    exact chosenPartial_ae_zero_on_open_sub (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
        (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed)
      Set.sdiff_subset h_inner (ih h_low (Fin.init dirs)) (dirs (Fin.last m))

private lemma highestCommutator_hY_Kzero
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h : MemWkp (m + 2) 2
      (chartPushed (chartAtlasPOU I M) α ((H1ComplToLp g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α)) :
    ∀ i j : Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU g α u_h (m + 2)
        (Fin.cons i (Fin.snoc dirs j))
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)] (fun _ => (0 : ℝ)) := by
  intro i j
  exact selectedMixed_ae_zero_of_exact_chart_order g α u_h (m + 2) h
    (Fin.cons i (Fin.snoc dirs j))

private theorem memWkp_chart_smooth_mul_supported
    (α : M) (k : ℕ) {coef factor : EuclN → ℝ}
    (hcoef : ContDiffOn ℝ (⊤ : ℕ∞) coef (chartTargetEuclid (I := I) (M := M) α))
    (hfactor : MemWkp (d := Module.finrank ℝ E) k 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hzero : factor =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) k 2 (fun y => coef y * factor y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  let Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α
  let C : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α
  have hΩopen : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hCc : IsCompact C := chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hCΩ : C ⊆ Ω := chartImagePOUTsupport_subset_target (I := I) (M := M) α
  obtain ⟨δ, ext, hδ, _, hext, heq⟩ :=
    exists_smooth_global_extension (I := I) (M := M) (φ := coef) α hcoef hCc hCΩ
  obtain ⟨ε, χ, hε, _, hχ, hχc, _, hχone, _⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E) hCc hΩopen hCΩ
  have hmult : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * ext y) := hχ.mul hext
  have hmultc : HasCompactSupport (fun y => χ y * ext y) := hχc.mul_right
  obtain ⟨B, _, hB⟩ := exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
    (d := Module.finrank ℝ E) hmult hmultc k
  have hprod : MemWkp (d := Module.finrank ℝ E) k 2
      (fun y => (χ y * ext y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) k
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩopen hmult
      (fun j hj y _ => hB y j hj) hfactor
  have hzvol : ∀ᵐ y ∂(volume : Measure EuclN), y ∈ Ω \ C → factor y = 0 :=
    (ae_restrict_iff' (hΩopen.measurableSet.diff hCc.isClosed.measurableSet)).mp hzero
  have hAE : (fun y => (χ y * ext y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω] (fun y => coef y * factor y) := by
    apply (ae_restrict_iff' hΩopen.measurableSet).mpr
    filter_upwards [hzvol] with y hy
    intro hyΩ
    by_cases hyC : y ∈ C
    · have heqy := heq y ((Metric.self_subset_cthickening (δ := δ) C) hyC)
      have hχy := hχone y ((Metric.self_subset_cthickening (δ := ε) C) hyC)
      rw [heqy, hχy, one_mul]
    · rw [hy ⟨hyΩ, hyC⟩]
      simp
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩopen hAE).mp hprod

private theorem memWkp_div_chartDensity_supported
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ) {factor : EuclN → ℝ}
    (hfactor : MemWkp (d := Module.finrank ℝ E) k 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hzero : factor =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    MemWkp (d := Module.finrank ℝ E) k 2
      (fun y => factor y / CalabiYau.Laplacian.MetricExtension.densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h := memWkp_chart_smooth_mul_supported (I := I) (M := M) α k
    (CalabiYau.Laplacian.MetricExtension.one_div_densityOnEuclid_contDiffOn (I := I) (M := M) g α)
    hfactor hzero
  convert h using 1
  funext y
  rw [one_div, mul_comm, ← div_eq_mul_inv]

private theorem actual_quotient_memWkp_of_numerator_memWkp
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) (m k : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E)) (q : EuclN → ℝ)
    (l : Fin (Module.finrank ℝ E))
    (hq : MemWkp (k + 1) 2 q (chartTargetEuclid (I := I) (M := M) α))
    (hq0 : q =ᵐ[(volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \ chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ => (0 : ℝ)))
    (hu : MemWkp (m + 2 + k) 2
      (chartPushed (chartAtlasPOU I M) α ((H1ComplToLp g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α))
    (hnum : MemWkp k 2 (successorChartForcingNumerator g α u_h m dirs q l)
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp k 2 (fun y => successorChartForcingNumerator g α u_h m dirs q l y /
      densityOnEuclid (I := I) g α y) (chartTargetEuclid (I := I) (M := M) α) := by
  have hq1 : DeGiorgi.MemW1p 2 q (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.one_iff_memW1p.mp (hq.le_of_le (by omega))
  have hX : ∀ i, chosenMthMixedPartialChartPushedU g α u_h (m + 1) (Fin.cons i dirs)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := fun i =>
    selectedMixed_ae_zero_of_exact_chart_order g α u_h (m + 1)
      (hu.le_of_le (by omega)) (Fin.cons i dirs)
  have hY := highestCommutator_hY_Kzero g α u_h m dirs (hu.le_of_le (by omega))
  have hZ := selectedMixed_ae_zero_of_exact_chart_order g α u_h m
    (hu.le_of_le (by omega)) dirs
  have hzero : successorChartForcingNumerator g α u_h m dirs q l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \ chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ => (0 : ℝ)) := by
    exact successor_numerator_ae_zero
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
      (fun i j y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α i j l) y)
        (EuclideanSpace.single j 1))
      (fun i j => weightedInvGramDerivOnEuclid (I := I) g α i j l)
      (fun i _ => chosenMthMixedPartialChartPushedU g α u_h (m + 1) (Fin.cons i dirs))
      (fun i j => chosenMthMixedPartialChartPushedU g α u_h (m + 2)
        (Fin.cons i (Fin.snoc dirs j)))
      (densityDerivOnEuclid (I := I) g α l) (densityOnEuclid (I := I) g α)
      (chosenMthMixedPartialChartPushedU g α u_h m dirs) q hq1 l
      (fun i _ => hX i) hY hZ hq0
  exact memWkp_div_chartDensity_supported g α k hnum hzero

variable [NeZero (Module.finrank ℝ E)]

/-- Exact quotient regularity with the source's finite solution order. -/
theorem successorChartForcingQuotient_memWkp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m K : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (previousForcing : EuclN → ℝ) (l : Fin (Module.finrank ℝ E))
    (h_previous_memWkp : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (K + 1) 2 previousForcing
      (chartTargetEuclid (I := I) (M := M) α))
    (h_previous_ae_zero :
      previousForcing =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)))
    (h_chart_H_u : Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2 + K) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) :
    Sobolev.Euclidean.MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => successorChartForcingNumerator g α u_h m dirs previousForcing l y /
        CalabiYau.Laplacian.MetricExtension.densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  exact actual_quotient_memWkp_of_numerator_memWkp
    g α u_h m K dirs previousForcing l
    h_previous_memWkp h_previous_ae_zero h_chart_H_u
    (successorChartForcingNumerator_memWkp g α u_h m K dirs previousForcing l
      h_previous_memWkp h_previous_ae_zero h_chart_H_u)

end CalabiYau.PoissonDomainRegularity
