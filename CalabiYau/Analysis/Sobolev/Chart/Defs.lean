-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Chart/Defs.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
public import CalabiYau.Geometry.Riemannian.Volume.Properties
public import Mathlib.Geometry.Manifold.DerivationBundle
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.InnerProductSpace.Dual
public import CalabiYau.Geometry.Manifold.Bundle.Section
public import CalabiYau.Geometry.Manifold.Tensor.RSTensor.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.RingTheory.Derivation.Lie
public import CalabiYau.Geometry.Riemannian.L2.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below..

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace Sobolev
namespace Chart
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartPushed
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    (ρ α : C^∞⟮I, M; ℝ⟯) ((extChartAt I α).symm (toEuclidean.symm y)) *
      u ((extChartAt I α).symm (toEuclidean.symm y))

def chartTargetEuclid (α : M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  toEuclidean '' (extChartAt I α).target

def MemWkpChart [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : Prop :=
  ∀ α : M,
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α)

def wkpNormChart [T2Space M] [SigmaCompactSpace M]
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : ℝ≥0∞ :=
  ∑' α : M,
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E)
      k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α)

omit [IsManifold I ∞ M] in
theorem chartPushed_zero
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    chartPushed (I := I) (M := M) ρ α (fun _ => (0 : ℝ)) =
      (fun _ => (0 : ℝ)) := by
  funext y
  unfold chartPushed
  simp

omit [IsManifold I ∞ M] in
theorem chartTargetEuclid_isOpen
    [I.Boundaryless] (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α) := by
  unfold chartTargetEuclid
  have hOpenE : IsOpen ((extChartAt I α).target) :=
    isOpen_extChartAt_target (I := I) α
  exact toEuclidean.toHomeomorph.isOpenMap _ hOpenE

theorem MemWkpChart_zero_fun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemWkpChart (I := I) (M := M) k p (fun _ : M => (0 : ℝ)) := by
  intro α
  rw [chartPushed_zero]
  exact Sobolev.Euclidean.MemWkp_zero_fun
    (d := Module.finrank ℝ E) hp (chartTargetEuclid_isOpen (I := I) (M := M) α)

omit [IsManifold I ∞ M] in
theorem chartPushed_add
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (u v : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => u x + v x) =
      (fun y =>
        chartPushed (I := I) (M := M) ρ α u y +
          chartPushed (I := I) (M := M) ρ α v y) := by
  funext y
  unfold chartPushed
  ring

omit [IsManifold I ∞ M] in
theorem chartPushed_const_smul
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (c : ℝ) (u : M → ℝ) :
    chartPushed (I := I) (M := M) ρ α (fun x => c * u x) =
      (fun y => c * chartPushed (I := I) (M := M) ρ α u y) := by
  funext y
  unfold chartPushed
  ring

theorem MemWkpChart_add
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) k p u)
    (hv : MemWkpChart (I := I) (M := M) k p v) :
    MemWkpChart (I := I) (M := M) k p (fun x => u x + v x) := by
  intro α
  rw [chartPushed_add]
  exact Sobolev.Euclidean.MemWkp.add
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

theorem MemWkpChart_const_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) k p u) :
    MemWkpChart (I := I) (M := M) k p (fun x => c * u x) := by
  intro α
  rw [chartPushed_const_smul]
  exact Sobolev.Euclidean.MemWkp.const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

theorem MemWkpChart_neg
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) k p u) :
    MemWkpChart (I := I) (M := M) k p (fun x => -u x) := by
  have h := MemWkpChart_const_smul (I := I) (M := M) hp (-1) hu
  have hEq : (fun x : M => (-1 : ℝ) * u x) = (fun x : M => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

theorem MemWkpChart_sub
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) k p u)
    (hv : MemWkpChart (I := I) (M := M) k p v) :
    MemWkpChart (I := I) (M := M) k p (fun x => u x - v x) := by
  have hneg := MemWkpChart_neg (I := I) (M := M) hp hv
  have h := MemWkpChart_add (I := I) (M := M) hp hu hneg
  have hEq : (fun x : M => u x + -v x) = (fun x : M => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

def wkpChartSubmodule
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Submodule ℝ (M → ℝ) where
  carrier := { u | MemWkpChart (I := I) (M := M) k p u }
  zero_mem' := MemWkpChart_zero_fun (I := I) (M := M) hp
  add_mem' := fun hu hv => MemWkpChart_add (I := I) (M := M) hp hu hv
  smul_mem' := fun c u hu => by
    have h := MemWkpChart_const_smul (I := I) (M := M) hp c hu
    have hEq : (c • u : M → ℝ) = fun x => c * u x := by
      funext x
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hEq]
    exact h

def WkpChart
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  ↥(wkpChartSubmodule (I := I) (M := M) k p hp)

instance
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    AddCommGroup (WkpChart (I := I) (M := M) k p hp) :=
  inferInstanceAs (AddCommGroup ↥(wkpChartSubmodule (I := I) (M := M) k p hp))

instance
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Module ℝ (WkpChart (I := I) (M := M) k p hp) :=
  inferInstanceAs (Module ℝ ↥(wkpChartSubmodule (I := I) (M := M) k p hp))

theorem MemWkpChart.le_succ
    [T2Space M] [SigmaCompactSpace M] {k : ℕ} {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemWkpChart (I := I) (M := M) (k + 1) p u) :
    MemWkpChart (I := I) (M := M) k p u := by
  intro α
  exact (h α).le_succ

theorem MemWkpChart.le_of_le
    [T2Space M] [SigmaCompactSpace M] {k k' : ℕ} {p : ℝ≥0∞} {u : M → ℝ}
    (hk : k ≤ k') (h : MemWkpChart (I := I) (M := M) k' p u) :
    MemWkpChart (I := I) (M := M) k p u := by
  intro α
  exact (h α).le_of_le hk

def ChartPushedAEEq
    [T2Space M] [SigmaCompactSpace M]
    (u v : M → ℝ) : Prop :=
  ∀ α : M,
    chartPushed (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
        =ᵐ[MeasureTheory.volume.restrict
            (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α v

theorem ChartPushedAEEq.rfl
    [T2Space M] [SigmaCompactSpace M] (u : M → ℝ) :
    ChartPushedAEEq (I := I) (M := M) u u := by
  intro α
  exact Filter.EventuallyEq.rfl

theorem ChartPushedAEEq.symm
    [T2Space M] [SigmaCompactSpace M] {u v : M → ℝ} (h : ChartPushedAEEq (I := I) (M := M) u v) :
    ChartPushedAEEq (I := I) (M := M) v u := by
  intro α
  exact (h α).symm

theorem ChartPushedAEEq.trans
    [T2Space M] [SigmaCompactSpace M] {u v w : M → ℝ}
    (huv : ChartPushedAEEq (I := I) (M := M) u v)
    (hvw : ChartPushedAEEq (I := I) (M := M) v w) :
    ChartPushedAEEq (I := I) (M := M) u w := by
  intro α
  exact (huv α).trans (hvw α)

theorem MemWkpChart_congr_chartPushed_ae
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ} (huv : ChartPushedAEEq (I := I) (M := M) u v) :
    MemWkpChart (I := I) (M := M) k p u ↔
      MemWkpChart (I := I) (M := M) k p v := by
  refine ⟨fun h α => ?_, fun h α => ?_⟩
  · exact (Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (huv α)).mp (h α)
  · exact (Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (huv α).symm).mp (h α)

theorem wkpNormChart_add_le
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) k p u)
    (hv : MemWkpChart (I := I) (M := M) k p v) :
    wkpNormChart (I := I) (M := M) k p (fun x => u x + v x) ≤
      wkpNormChart (I := I) (M := M) k p u +
        wkpNormChart (I := I) (M := M) k p v := by
  unfold wkpNormChart
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [chartPushed_add]
  exact Sobolev.Euclidean.wkpNorm_add_le
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) (hv α)

theorem wkpNormChart_const_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) k p u) :
    wkpNormChart (I := I) (M := M) k p (fun x => c * u x) =
      ‖c‖ₑ * wkpNormChart (I := I) (M := M) k p u := by
  unfold wkpNormChart
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [chartPushed_const_smul]
  exact Sobolev.Euclidean.wkpNorm_const_smul
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (hu α) c

theorem wkpNormChart_lt_top_of_memWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) k p u) :
    wkpNormChart (I := I) (M := M) k p u < ⊤ := by
  classical
  unfold wkpNormChart
  set f : M → ℝ≥0∞ := fun α =>
    Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) with hf_def
  have hPOU_localFin : LocallyFinite
      (fun α : M => Function.support
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ)) :=
    (CalabiYau.RiemannianVolume.chartAtlasPOU I M).locallyFinite
  have hSupport_finite : {α : M | (Function.support
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ)).Nonempty}.Finite :=
    hPOU_localFin.finite_nonempty_of_compact
  have hf_zero_off : ∀ α : M, (Function.support
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ)) = ∅ →
        f α = 0 := by
    intro α hα
    have hρ_empty : ∀ x : M, (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : M → ℝ) x = 0 := by
      intro x
      have : x ∉ Function.support (CalabiYau.RiemannianVolume.chartAtlasPOU
          I M α : M → ℝ) := by
        rw [hα]
        exact Set.notMem_empty x
      simpa [Function.mem_support] using this
    have hChartPushed_zero : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u =
        (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [hρ_empty]
      ring
    change Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) k p
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) = 0
    rw [hChartPushed_zero]
    exact Sobolev.Euclidean.wkpNorm_zero_fun_zero
      (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  set S : Set M := {α : M | (Function.support
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ)).Nonempty}
      with hS_def
  have hS_finite : S.Finite := hSupport_finite
  have hf_support_S : Function.support f ⊆ S := by
    intro α hα
    by_contra hαS
    apply hα
    have h_not_in_S : (Function.support
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α h_not_in_S
  have htsum_eq : ∑' α : M, f α = ∑ α ∈ hS_finite.toFinset, f α := by
    rw [tsum_eq_sum]
    intro α hα
    have hαS : α ∉ S := by
      intro hαS
      apply hα
      exact (Set.Finite.mem_toFinset _).mpr hαS
    have hempty : (Function.support
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ)) = ∅ := by
      have h_not_nonempty : ¬ (Function.support
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M α : M → ℝ)).Nonempty := by
        intro hne
        exact hαS hne
      exact Set.not_nonempty_iff_eq_empty.mp h_not_nonempty
    exact hf_zero_off α hempty
  rw [htsum_eq]
  apply ENNReal.sum_lt_top.mpr
  intro α _
  rw [hf_def]
  exact Sobolev.Euclidean.wkpNorm_lt_top_of_memWkp
    (d := Module.finrank ℝ E) (hu α)

end Chart
end Sobolev
