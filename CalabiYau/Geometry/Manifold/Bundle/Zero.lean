-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Bundle/Zero.lean
-- Locally modified.
/-
Authors: Jack McCarthy
-/
module
public import Mathlib.Topology.VectorBundle.Basic

@[expose] public section

open Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

theorem continuous_zeroSection (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] :
    Continuous (zeroSection F E) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuousAt_id, ?_⟩
  set e := trivializationAt F E x₀
  have hmem : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F E x₀
  have hbase : e.baseSet ∈ nhds x₀ := e.open_baseSet.mem_nhds hmem
  apply Filter.Tendsto.congr'
  · change ∀ᶠ x in nhds x₀, (fun _ => (e (zeroSection F E x₀)).2) x =
        (fun x => (e (zeroSection F E x)).2) x
    filter_upwards [hbase] with x hx
    rw [e.zeroSection (R := 𝕜) hmem, e.zeroSection (R := 𝕜) hx]
  · exact tendsto_const_nhds
