-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Calculus/Compactness/PointwiseCompact.lean
-- Locally modified.
module
public import CalabiYau.Topology.Equicontinuity
public import CalabiYau.Topology.Compactness.DiagonalSubsequence
public import Mathlib.Topology.Order.IsLocallyClosed
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Topology.Order.Compact
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

section CompactClosure

variable {X : Type*} [TopologicalSpace X] [CompactlyCoherentSpace X]
  {Y ι : Type*} [UniformSpace Y] [T2Space Y]

theorem arzela_ascoli_isCompact_closure_of_pointwise_compact
    (f : ι -> C(X, Y))
    (hequi : Equicontinuous (fun k => (f k : X -> Y)))
    (hpoint : ∀ x : X, ∃ K : Set Y, IsCompact K ∧ ∀ k : ι, f k x ∈ K) :
    IsCompact (closure (Set.range f : Set C(X, Y))) := by
  classical
  have hclosedEmbedding :
      IsClosedEmbedding
        (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
          (fun g : C(X, Y) => (g : X -> Y))) := by
    refine ⟨⟨⟨?_⟩, DFunLike.coe_injective⟩, ?_⟩
    · change ContinuousMap.compactOpen =
        TopologicalSpace.induced ContinuousMap.toUniformOnFunIsCompact _
      unfold UniformOnFun.topologicalSpace
      rw [← (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
          (α := X) (β := Y)).isInducing.eq_induced]
      unfold ContinuousMap.compactConvergenceUniformSpace
      rfl
    · rw [show
          Set.range
              (UniformOnFun.ofFun {K : Set X | IsCompact K} ∘
                (fun g : C(X, Y) => (g : X -> Y))) =
            {g : UniformOnFun X Y {K : Set X | IsCompact K} |
              Continuous (UniformOnFun.toFun {K : Set X | IsCompact K} g)} by
          exact ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOfPred_continuous
        (β := Y) (𝔖 := {K : Set X | IsCompact K})
        CompactlyCoherentSpace.isCoherentWith
  have hEq :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        EquicontinuousOn
          ((fun g : C(X, Y) => (g : X -> Y)) ∘
            ((↑) : {g : C(X, Y) // g ∈ Set.range f} -> C(X, Y))) K := by
    intro K _hK
    let idx : {g : C(X, Y) // g ∈ Set.range f} -> ι :=
      fun g => Classical.choose g.2
    have hidx :
        forall g : {g : C(X, Y) // g ∈ Set.range f}, f (idx g) = g.1 :=
      fun g => Classical.choose_spec g.2
    have hglobal :
        Equicontinuous (fun g : {g : C(X, Y) // g ∈ Set.range f} =>
          (g.1 : X -> Y)) := by
      have hsub := hequi.comp idx
      have hfun :
          ((fun k : ι => (f k : X -> Y)) ∘ idx) =
            (fun g : {g : C(X, Y) // g ∈ Set.range f} => (g.1 : X -> Y)) := by
        funext g x
        change f (idx g) x = g.1 x
        rw [hidx g]
      simpa [hfun] using hsub
    simpa [Function.comp_def] using hglobal.equicontinuousOn K
  have hPoint :
      forall K : Set X, K ∈ ({K : Set X | IsCompact K}) ->
        forall x : X, x ∈ K ->
        exists Q : Set Y, IsCompact Q ∧
          forall i : C(X, Y), i ∈ (Set.range f : Set C(X, Y)) ->
            ((fun g : C(X, Y) => (g : X -> Y)) i) x ∈ Q := by
    intro _K _hK x _hx
    obtain ⟨Q, hQ, hmem⟩ := hpoint x
    refine ⟨Q, hQ, ?_⟩
    intro i hi
    obtain ⟨k, rfl⟩ := hi
    exact hmem k
  exact
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (X := X) (α := Y) (ι := C(X, Y))
      (𝔖 := {K : Set X | IsCompact K})
      (F := fun g : C(X, Y) => (g : X -> Y))
      (fun K hK => hK) hclosedEmbedding
      (s := Set.range f) hEq hPoint

end CompactClosure

variable {X : Type*} [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
  {Y : Type*} [PseudoMetricSpace Y] [T2Space Y]

end CalabiYau
