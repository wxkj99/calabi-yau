-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Bundle/Section.lean
-- Locally modified.
/-
Authors: Jack McCarthy
-/
module
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
public import CalabiYau.Geometry.Manifold.Bundle.Equiv
public import CalabiYau.Geometry.Manifold.Bundle.Frame

@[expose] public section

open scoped Manifold ContDiff Topology
open Bundle

section FixedTrivializationSmoothness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V I]
  {s : ∀ x, V x} {x₀ : M}

variable [IsManifold I n M]

end FixedTrivializationSmoothness

section ModuleOverSmoothFunctions

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

namespace ContMDiffSection

instance instSMulContMDiffMap : SMul C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ :=
  ⟨fun f s => ⟨fun x => f x • s x, f.2.smul_section s.contMDiff⟩⟩

@[simp]
theorem coe_smulContMDiffMap (f : C^n⟮I, M; 𝕜⟯) (s : Cₛ^n⟮I; F, V⟯) :
    ⇑(f • s) = fun x => f x • s x :=
  rfl

instance instModuleContMDiffMap : Module C^n⟮I, M; 𝕜⟯ Cₛ^n⟮I; F, V⟯ where
  one_smul s := by ext x; exact one_smul 𝕜 (s x)
  mul_smul f g s := by ext x; exact mul_smul (f x) (g x) (s x)
  smul_zero f := by ext x; exact smul_zero (f x)
  smul_add f s t := by ext x; exact smul_add (f x) (s x) (t x)
  add_smul f g s := by ext x; exact add_smul (f x) (g x) (s x)
  zero_smul s := by ext x; exact zero_smul 𝕜 (s x)

end ContMDiffSection

end ModuleOverSmoothFunctions

section BundledFamilies

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : WithTop ℕ∞}

theorem ContMDiffWithinAt.smul_bundle
    {b : M → B} {f : M → 𝕜} {s : ∀ x, V (b x)} {U : Set M} {x : M}
    (hf : ContMDiffWithinAt IM 𝓘(𝕜, 𝕜) n f U x)
    (hs : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (s y)) U x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (f y • s y)) U x := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hs ⊢
  refine ⟨hs.1, ?_⟩
  let e := trivializationAt F V (b x)
  have he : ∀ᶠ y in 𝓝[U] x, b y ∈ e.baseSet :=
    hs.1.continuousWithinAt
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V (b x)))
  refine (hf.smul hs.2).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [he] with y hy
    exact (e.linear 𝕜 hy).map_smul (f y) (s y)
  · exact (e.linear 𝕜 (mem_baseSet_trivializationAt F V (b x))).map_smul (f x) (s x)

theorem ContMDiffAt.smul_bundle
    {b : M → B} {f : M → 𝕜} {s : ∀ x, V (b x)} {x : M}
    (hf : ContMDiffAt IM 𝓘(𝕜, 𝕜) n f x)
    (hs : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (s y)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (f y • s y)) x := by
  rw [← contMDiffWithinAt_univ] at hf hs ⊢
  exact hf.smul_bundle hs

theorem ContMDiffOn.smul_bundle
    {b : M → B} {f : M → 𝕜} {s : ∀ x, V (b x)} {U : Set M}
    (hf : ContMDiffOn IM 𝓘(𝕜, 𝕜) n f U)
    (hs : ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (s x)) U) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (f x • s x)) U :=
  fun x hx => (hf x hx).smul_bundle (hs x hx)

theorem ContMDiff.smul_bundle
    {b : M → B} {f : M → 𝕜} {s : ∀ x, V (b x)}
    (hf : ContMDiff IM 𝓘(𝕜, 𝕜) n f)
    (hs : ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (s x))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (f x • s x)) :=
  fun x => (hf x).smul_bundle (hs x)

theorem ContMDiffWithinAt.zero_bundle
    {b : M → B} {U : Set M} {x : M} (hb : ContMDiffWithinAt IM IB n b U x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (0 : V (b y))) U x := by
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨hb, ?_⟩
  let e := trivializationAt F V (b x)
  have he : ∀ᶠ y in 𝓝[U] x, b y ∈ e.baseSet :=
    hb.continuousWithinAt
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V (b x)))
  refine (contMDiffWithinAt_const (I := IM) (I' := 𝓘(𝕜, F)) (n := n)
    (x := x) (s := U) (c := (0 : F))).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [he] with y hy
    exact (e.linear 𝕜 hy).map_zero
  · exact (e.linear 𝕜 (mem_baseSet_trivializationAt F V (b x))).map_zero

theorem ContMDiffAt.zero_bundle
    {b : M → B} {x : M} (hb : ContMDiffAt IM IB n b x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (0 : V (b y))) x := by
  rw [← contMDiffWithinAt_univ] at hb ⊢
  exact hb.zero_bundle

theorem ContMDiffOn.zero_bundle
    {b : M → B} {U : Set M} (hb : ContMDiffOn IM IB n b U) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (0 : V (b y))) U :=
  fun x hx => (hb x hx).zero_bundle

theorem ContMDiff.zero_bundle
    {b : M → B} (hb : ContMDiff IM IB n b) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (0 : V (b x))) :=
  fun x => (hb x).zero_bundle

theorem ContMDiffWithinAt.add_bundle
    {b : M → B} {s t : ∀ x, V (b x)} {U : Set M} {x : M}
    (hs : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (s y)) U x)
    (ht : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (t y)) U x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (s y + t y)) U x := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hs ht ⊢
  refine ⟨hs.1, ?_⟩
  let e := trivializationAt F V (b x)
  have he : ∀ᶠ y in 𝓝[U] x, b y ∈ e.baseSet :=
    hs.1.continuousWithinAt
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V (b x)))
  refine (hs.2.add ht.2).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [he] with y hy
    exact (e.linear 𝕜 hy).map_add (s y) (t y)
  · exact (e.linear 𝕜 (mem_baseSet_trivializationAt F V (b x))).map_add (s x) (t x)

theorem ContMDiffAt.add_bundle
    {b : M → B} {s t : ∀ x, V (b x)} {x : M}
    (hs : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (s y)) x)
    (ht : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (t y)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (s y + t y)) x := by
  rw [← contMDiffWithinAt_univ] at hs ht ⊢
  exact hs.add_bundle ht

theorem ContMDiffOn.add_bundle
    {b : M → B} {s t : ∀ x, V (b x)} {U : Set M}
    (hs : ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (s y)) U)
    (ht : ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (t y)) U) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (s y + t y)) U :=
  fun x hx => (hs x hx).add_bundle (ht x hx)

theorem ContMDiff.add_bundle
    {b : M → B} {s t : ∀ x, V (b x)}
    (hs : ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (s x)))
    (ht : ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (t x))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (s x + t x)) :=
  fun x => (hs x).add_bundle (ht x)

theorem ContMDiffWithinAt.sum_bundle
    {b : M → B} {U : Set M} {x : M} (hb : ContMDiffWithinAt IM IB n b U x)
    {ι : Type*} {u : ι → ∀ y, V (b y)} (S : Finset ι)
    (hu : ∀ i ∈ S, ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (u i y)) U x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (∑ i ∈ S, u i y)) U x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using hb.zero_bundle (F := F)
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hu i (Finset.mem_insert_self i S)).add_bundle
        (ih fun j hj => hu j (Finset.mem_insert_of_mem hj))

theorem ContMDiffAt.sum_bundle
    {b : M → B} {x : M} (hb : ContMDiffAt IM IB n b x)
    {ι : Type*} {u : ι → ∀ y, V (b y)} (S : Finset ι)
    (hu : ∀ i ∈ S, ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (u i y)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (∑ i ∈ S, u i y)) x := by
  simp only [← contMDiffWithinAt_univ] at hb hu ⊢
  exact hb.sum_bundle S hu

theorem ContMDiffOn.sum_bundle
    {b : M → B} {U : Set M} (hb : ContMDiffOn IM IB n b U)
    {ι : Type*} {u : ι → ∀ y, V (b y)} (S : Finset ι)
    (hu : ∀ i ∈ S, ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (u i y)) U) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, F)) n
      (fun y => TotalSpace.mk' F (b y) (∑ i ∈ S, u i y)) U :=
  fun x hx => (hb x hx).sum_bundle S (fun i hi => hu i hi x hx)

theorem ContMDiff.sum_bundle
    {b : M → B} (hb : ContMDiff IM IB n b)
    {ι : Type*} {u : ι → ∀ x, V (b x)} (S : Finset ι)
    (hu : ∀ i ∈ S, ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (u i x))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, F)) n
      (fun x => TotalSpace.mk' F (b x) (∑ i ∈ S, u i x)) :=
  fun x => (hb x).sum_bundle S (fun i hi => hu i hi x)

end BundledFamilies

section MapSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

namespace ContMDiffVectorBundleHom

end ContMDiffVectorBundleHom

section SectionConstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

end SectionConstruction

section ActsHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞} [h1n : Fact (1 ≤ n)]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [IsManifold I ∞ M] [T2Space M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁]
  [ContMDiffVectorBundle n F₁ E₁ I]

end ActsHelpers

section VBC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞} [h1n : Fact (1 ≤ n)]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {E₁ : M → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : M → Type*} [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
  [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]

end VBC

end MapSection

section TrivializationSymmL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]

end TrivializationSymmL
