module
public import CalabiYau.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Elliptic.MetricExtension
public import CalabiYau.Analysis.Sobolev.Approximation.Density.Smooth
public import Comparator.PoissonSolvability.DomainSobolevGain.NumeratorProductRegularity.MixedRegularity
public import CalabiYau.Analysis.Elliptic.Regularity.DiffChart.Differentiated.BilinearH1Compl

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
namespace CalabiYau.PoissonDomainRegularity.NumeratorSolutionProducts
open Sobolev.Euclidean

lemma mul_contDiffOn_of_ae_zero_off_compact
    {d : ℕ} (k : ℕ) {Ω K : Set (EuclideanSpace ℝ (Fin d))}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {coef f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hcoef : ContDiffOn ℝ (⊤ : ℕ∞) coef Ω) (hf : MemWkp k 2 f Ω)
    (hzero : f =ᵐ[volume.restrict (Ω \ K)] (fun _ => 0)) :
    MemWkp k 2 (fun y => coef y * f y) Ω := by
  classical
  obtain ⟨ε, χ, hε, _, hχ, hχcs, _, hχone, hχsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood hK hΩ hKΩ
  have hη : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport χ
    · exact hχ.contDiffAt.mul ((hcoef y (hχsupp hy)).contDiffAt
        (hΩ.mem_nhds (hχsupp hy)))
    · have hz : (fun y => χ y * coef y) =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hz
  have hηcs : HasCompactSupport (fun y => χ y * coef y) := hχcs.mul_right
  obtain ⟨C, _, hC⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport hη hηcs k
  have hprod : MemWkp k 2 (fun y => (χ y * coef y) * f y) Ω :=
    MemWkp.smul_smooth_bounded k (by norm_num) hΩ hη
      (fun j hj y _ => hC y j hj) hf
  have hdiff : MeasurableSet (Ω \ K) := hΩ.measurableSet.diff hK.isClosed.measurableSet
  have hz := (ae_restrict_iff' hdiff).mp hzero
  have heq : (fun y => (χ y * coef y) * f y) =ᵐ[volume.restrict Ω]
      (fun y => coef y * f y) := by
    apply (ae_restrict_iff' hΩ.measurableSet).mpr
    filter_upwards [hz] with y hy hyΩ
    by_cases hyK : y ∈ K
    · rw [hχone y (Metric.self_subset_cthickening K hyK), one_mul]
    · rw [hy ⟨hyΩ, hyK⟩, mul_zero, mul_zero]
  exact (MemWkp_congr_ae (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ heq).mp hprod

lemma chosenPartial_ae_zero_on_open_sub
    {d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω V : Set (EuclideanSpace ℝ (Fin d))} (hV : IsOpen V) (hV_sub : V ⊆ Ω)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hu : DeGiorgi.MemW1p (d := d) p u Ω)
    (hu_zero : u =ᵐ[volume.restrict V] (fun _ => (0 : ℝ))) (i : Fin d) :
    chosenWeakPartialOrZero p i u Ω =ᵐ[volume.restrict V] (fun _ => (0 : ℝ)) := by
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

open Bundle Manifold Function
open scoped Manifold BigOperators
open Sobolev.Chart CalabiYau.RiemannianVolume CalabiYau.Analysis.Laplacian
open CalabiYau.PoissonDomainRegularity CalabiYau.PoissonDomainRegularity.NumeratorMixedRegularity CalabiYau.Laplacian.MetricExtension
open CalabiYau.Analysis.Laplacian.DiffChartBilinearH1Compl
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
local notation "Ω" => Sobolev.Chart.chartTargetEuclid (I := I) (M := M)

lemma selectedMixed_ae_zero_of_exact_chart_order
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) (m : ℕ) :
    MemWkp m 2 (chartPushed (chartAtlasPOU I M) α ((H1ComplToLp g u_h) : M → ℝ)) (Ω α) →
    ∀ dirs : Fin m → Fin (Module.finrank ℝ E),
      chosenMthMixedPartialChartPushedU g α u_h m dirs
        =ᵐ[volume.restrict (Ω α \ chartImagePOUTsupport (I := I) (M := M) α)]
          (fun _ => (0 : ℝ)) := by
  induction m with
  | zero =>
    intro _ dirs
    have hV := (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
      (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
    refine (ae_restrict_iff' hV.measurableSet).mpr (Filter.Eventually.of_forall ?_)
    intro y hy
    exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _ hy.1 hy.2
  | succ m ih =>
    intro h dirs
    have h_inner := chosenMthMixedPartialChartPushedU_memW1p_two g α u_h m h (Fin.init dirs)
    have h_low : MemWkp m 2
        (chartPushed (chartAtlasPOU I M) α ((H1ComplToLp g u_h) : M → ℝ)) (Ω α) :=
      h.le_of_le (by omega)
    exact chosenPartial_ae_zero_on_open_sub (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
        (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed)
      Set.sdiff_subset h_inner (ih h_low (Fin.init dirs)) (dirs (Fin.last m))

lemma coef_mul_selectedMixed_memWkp
    (g : SmoothRiemannianMetric I M) (α : M) (u_h : H1Compl g) (s K : ℕ)
    (dirs : Fin s → Fin (Module.finrank ℝ E)) {coef : EuclN → ℝ}
    (hcoef : ContDiffOn ℝ (⊤ : ℕ∞) coef (Ω α))
    (h : MemWkp (s + K) 2
      (chartPushed (chartAtlasPOU I M) α ((H1ComplToLp g u_h) : M → ℝ)) (Ω α)) :
    MemWkp K 2 (fun y => coef y * chosenMthMixedPartialChartPushedU g α u_h s dirs y)
      (Ω α) := by
  have hreg := chosenMthMixedPartialChartPushedU_memWkp_of_chartPushed_memWkp
    g α u_h s K (by simpa only [Nat.add_comm K s] using h) dirs
  have hlow : MemWkp s 2
      (chartPushed (chartAtlasPOU I M) α ((H1ComplToLp g u_h) : M → ℝ)) (Ω α) :=
    h.le_of_le (by omega)
  have hzero := selectedMixed_ae_zero_of_exact_chart_order g α u_h s hlow dirs
  exact mul_contDiffOn_of_ae_zero_off_compact K
    (Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α)
    (chartImagePOUTsupport_subset_target (I := I) (M := M) α) hcoef hreg hzero

omit [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
lemma memWkp_finset_sum {α : M} {K : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclN → ℝ} (hf : ∀ i ∈ s, MemWkp K 2 (f i) (Ω α)) :
    MemWkp K 2 (fun y => ∑ i ∈ s, f i y) (Ω α) := by
  classical
  have hΩ := Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MemWkp_zero_fun (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
  | insert i s his ih =>
    have hi := hf i (Finset.mem_insert_self _ _)
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have heq : (fun y => ∑ j ∈ insert i s, f j y) =
        (fun y => f i y + ∑ j ∈ s, f j y) := by
      funext y; rw [Finset.sum_insert his]
    rw [heq]
    exact MemWkp.add (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hi hs

end CalabiYau.PoissonDomainRegularity.NumeratorSolutionProducts
