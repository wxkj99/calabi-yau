-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Calculus/Compactness/ArzelaAscoli.lean
-- Locally modified.
module
public import CalabiYau.Mathlib.Topology.ContinuousMap.Compactness.PointwiseCompact
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IsLocallyClosed
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import Mathlib.Topology.UniformSpace.Real

@[expose] public section

set_option autoImplicit false

namespace CalabiYau
open Filter Set Topology
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X]

theorem arzela_ascoli_subseq_tendsto_of_pointwise_compact
    [SigmaCompactSpace X]
    {Y : Type*} [UniformSpace Y] [T2Space Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    (f : ℕ → C(X, Y))
    (hequi : Equicontinuous (fun k => (f k : X → Y)))
    (hpoint : ∀ x : X, ∃ Q : Set Y, IsCompact Q ∧ ∀ᶠ k in atTop, f k x ∈ Q) :
    ∃ (phi : ℕ → ℕ) (g : C(X, Y)),
      StrictMono phi ∧ Tendsto (fun n => f (phi n)) atTop (𝓝 g) := by
  have hpointAll : ∀ x : X, ∃ Q : Set Y, IsCompact Q ∧ ∀ k, f k x ∈ Q := by
    intro x
    obtain ⟨Q, hQ, htail⟩ := hpoint x
    obtain ⟨N, hN⟩ := eventually_atTop.mp htail
    refine ⟨Q ∪ (fun k => f k x) '' Iio N, hQ.union ((finite_Iio N).image _).isCompact, ?_⟩
    intro k
    by_cases hk : N ≤ k
    · exact Or.inl (hN k hk)
    · exact Or.inr ⟨k, lt_of_not_ge hk, rfl⟩
  have hmem : ∀ n, f n ∈ closure (Set.range f : Set C(X, Y)) :=
    fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨g, _, phi, hphi, hconv⟩ :=
    (arzela_ascoli_isCompact_closure_of_pointwise_compact f hequi hpointAll).tendsto_subseq hmem
  exact ⟨phi, g, hphi, hconv⟩

end CalabiYau

namespace CalabiYau
namespace CheegerGromovCompactness

open Filter Set Topology
open scoped Topology

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
  [SigmaCompactSpace X] [T2Space X]

section VectorTarget

variable {V : Type*} [NormedAddCommGroup V] [ProperSpace V]

omit [SigmaCompactSpace X] [T2Space X] in
theorem arzelaAscoli_isCompact_closure
    (f : Nat -> C(X, V))
    (hequi : Equicontinuous (fun k => (f k : X -> V)))
    (hbdd : forall x : X, exists M : Real, forall k : Nat, ‖f k x‖ <= M) :
    IsCompact (closure (Set.range f : Set C(X, V))) := by
  apply CalabiYau.arzela_ascoli_isCompact_closure_of_pointwise_compact f hequi
  intro x
  obtain ⟨B, hB⟩ := hbdd x
  exact ⟨Metric.closedBall 0 B, isCompact_closedBall 0 B,
    fun k => mem_closedBall_zero_iff.mpr (hB k)⟩

omit [T2Space X] in
theorem arzelaAscoli_subseq_vec
    (f : Nat -> C(X, V))
    (hequi : Equicontinuous (fun k => (f k : X -> V)))
    (hbdd : forall x : X, exists M : Real, forall k : Nat, ‖f k x‖ <= M) :
    exists (phi : Nat -> Nat) (g : C(X, V)),
      StrictMono phi ∧
        forall K : Set X, IsCompact K ->
          TendstoUniformlyOn (fun n => f (phi n)) g atTop K := by
  have hmem : forall n : Nat, f n ∈ closure (Set.range f : Set C(X, V)) :=
    fun n => subset_closure ⟨n, rfl⟩
  rcases (arzelaAscoli_isCompact_closure f hequi hbdd).tendsto_subseq hmem with
    ⟨g, _hg, phi, hphi, htendsto⟩
  exact
    ⟨phi, g, hphi,
      ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
        (by simpa [Function.comp_def] using htendsto)⟩

end VectorTarget

end CheegerGromovCompactness
end CalabiYau

namespace CalabiYau

open Filter Set Topology
open scoped Topology BoundedContinuousFunction

alias arzela_ascoli_subseq_tendsto_locally_uniformly :=
  CheegerGromovCompactness.arzelaAscoli_subseq_vec

end CalabiYau

namespace ArzelaAscoli
open Filter Set
open scoped Topology NNReal ENNReal

variable {X : Type*} [PseudoMetricSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X]

end ArzelaAscoli
