-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Bundle/Frame.lean
-- Locally modified.
/-
Authors: Jack McCarthy
Modified by: Ziyang Qin
-/
module
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.BumpFunction

@[expose] public section

-- The upstream module-system setting is documented in NOTICE.

open scoped Manifold Topology ContDiff
open Bundle Filter

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    [IsScalarTower ℝ 𝕜 F]
  {n : ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, IsScalarTower ℝ 𝕜 (V x)]
  [VectorBundle ℝ F V]

variable {ι : Type*} {s : ι → (x : M) → V x} {u : Set M} {p : M}

theorem exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    (hs : ∀ i, CMDiff[u] n (T% (s i))) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x := by
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hu.mem_nhds hp)
  refine ⟨fun i => ⟨fun x => χ x • s i x, ?_⟩, ?_⟩
  · exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn.smul_section_of_tsupport
      hu hχ (hs i)
  · filter_upwards [χ.eventuallyEq_one] with x hx i
    simp [hx]

theorem IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x := by
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hu.mem_nhds hp)
  refine ⟨fun i => ⟨fun x => χ x • s i x, ?_⟩, ?_⟩
  · exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn.smul_section_of_tsupport
      hu hχ (hs.contMDiffOn i)
  · filter_upwards [χ.eventuallyEq_one] with x hx i
    simp [hx]
