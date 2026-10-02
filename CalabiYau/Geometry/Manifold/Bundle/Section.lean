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

theorem contMDiffAt_section_of_trivializationAt_eventuallyEq
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (hx₀ : x₀ ∈ e.baseSet)
    {A : M → F}
    (hA : ContMDiffAt I 𝓘(𝕜, F) n A x₀)
    (hEq : (fun x => (e ⟨x, s x⟩).2) =ᶠ[𝓝 x₀] A) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n
      (fun x => (⟨x, s x⟩ : TotalSpace F V)) x₀ := by
  exact (e.contMDiffAt_section_iff hx₀).mpr (hA.congr_of_eventuallyEq hEq)

variable [IsManifold I n M]

theorem contMDiffAt_section_of_chart_model_eventuallyEq
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (hx₀ : x₀ ∈ e.baseSet)
    {A : E → F}
    (hA :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, F) n A (Set.range I)
        (extChartAt I x₀ x₀))
    (hEq :
      (fun x => (e ⟨x, s x⟩).2) =ᶠ[𝓝 x₀]
        fun x => A (extChartAt I x₀ x)) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n
      (fun x => (⟨x, s x⟩ : TotalSpace F V)) x₀ := by
  refine contMDiffAt_section_of_trivializationAt_eventuallyEq (I := I)
    (e := e) hx₀ ?_ hEq
  rw [contMDiffAt_iff_source_of_mem_source (x := x₀)
    (x' := x₀) (mem_chart_source H x₀)]
  refine hA.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    change A (extChartAt I x₀ ((extChartAt I x₀).symm y)) = A y
    rw [(extChartAt I x₀).right_inv hy]
  · change A (extChartAt I x₀
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀))) =
      A (extChartAt I x₀ x₀)
    rw [(extChartAt I x₀).right_inv (mem_extChartAt_target (I := I) x₀)]

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

noncomputable def mapSection
    (Φ : ContMDiffVectorBundleHom 𝕜 I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; 𝕜⟯] Cₛ^n⟮I; F₂, E₂⟯ := by
  obtain ⟨baseMap, toFun, hc, φ, compat⟩ := Φ
  subst hΦ
  exact
  { toFun := fun σ =>
      ⟨fun x => φ x (σ x), (hc.comp σ.contMDiff).congr fun x => (compat x (σ x)).symm⟩
    map_add' := fun σ τ => by ext x; exact (φ x).map_add (σ x) (τ x)
    map_smul' := fun f σ => by ext x; exact (φ x).map_smul (f x) (σ x) }

theorem mapSection_apply :
    ∀ (Φ : ContMDiffVectorBundleHom 𝕜 I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M),
    Φ.toFun ⟨x, σ x⟩ = ⟨x, (Φ.mapSection hΦ σ) x⟩
  | ⟨_, _, _, _, compat⟩, rfl, σ, x => compat x (σ x)

theorem tensorialAt
    (Φ : ContMDiffVectorBundleHom 𝕜 I n F₁ E₁ F₂ E₂) (x : M) :
    TensorialAt I F₁ (fun σ => Φ.fiberLinearMap x (σ x)) x :=
  ⟨fun _ _ => map_smul (Φ.fiberLinearMap x) _ _,
   fun _ _ => map_add (Φ.fiberLinearMap x) _ _⟩

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

theorem ContMDiffSection.finset_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → Cₛ^n⟮I; F, V⟯) (x : M) :
    (∑ i ∈ s, f i : Cₛ^n⟮I; F, V⟯) x = ∑ i ∈ s, f i x := by
  change (ContMDiffSection.coeAddHom I F (↑n) V (∑ i ∈ s, f i)) x = _
  rw [map_sum]; simp [ContMDiffSection.coeAddHom_apply, Finset.sum_apply]

theorem ContMDiffSection.exists_eq_at
    [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle n F V I]
    (p : M) (v : V p) : ∃ (σ : Cₛ^n⟮I; F, V⟯), σ p = v := by
  let e := trivializationAt F V p
  let b := Module.finBasis ℝ F
  have he : p ∈ e.baseSet := mem_baseSet_trivializationAt F V p
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (↑n) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  refine ⟨∑ i, ((hframe.toBasisAt he).repr v i) • s' i, ?_⟩
  rw [ContMDiffSection.finset_sum_apply]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  simp_rw [hs'.self_of_nhds, ← hframe.toBasisAt_coe he]
  exact (hframe.toBasisAt he).sum_repr v

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

omit [FiniteDimensional ℝ F₁] [ContMDiffVectorBundle n F₁ E₁ I] h1n in
theorem ContMDiffVectorBundleHom.linearMap_acts_locally
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯)
    (σ : Cₛ^n⟮I; F₁, E₁⟯) {U : Set M} (hU : IsOpen U)
    (hσU : ∀ x ∈ U, σ x = 0) : ∀ p ∈ U, (F σ) p = 0 := by
  intro p hp
  obtain ⟨ψ, -, hψsupport⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hU.mem_nhds hp)
  let ψ' : C^n⟮I, M; ℝ⟯ :=
    ⟨ψ, ψ.contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)⟩
  have hψσ : ψ' • σ = 0 := by
    ext x
    simp only [ContMDiffSection.coe_smulContMDiffMap, Pi.zero_apply, ContMDiffSection.coe_zero]
    by_cases hx : x ∈ Function.support (ψ : M → ℝ)
    · exact smul_eq_zero_of_right _ (hσU x (hψsupport (subset_closure hx)))
    · simp only [Function.mem_support, not_not] at hx
      exact smul_eq_zero_of_left hx _
  have key : ψ' • F σ = 0 := by rw [← F.map_smul, hψσ, map_zero]
  have := DFunLike.congr_fun key p
  simp only [ContMDiffSection.coe_smulContMDiffMap, ContMDiffSection.coe_zero,
    Pi.zero_apply] at this
  rwa [show (ψ' p : ℝ) = 1 from ψ.eq_one, one_smul] at this

theorem ContMDiffVectorBundleHom.linearMap_acts_pointwise
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯)
    (σ₁ σ₂ : Cₛ^n⟮I; F₁, E₁⟯) (p : M) (hσ : σ₁ p = σ₂ p) :
    (F σ₁) p = (F σ₂) p := by
  have : ContMDiffVectorBundle 1 F₁ E₁ I :=
    ContMDiffVectorBundle.of_le (show (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr h1n.out)
  suffices h : ∀ (τ : Cₛ^n⟮I; F₁, E₁⟯), τ p = 0 → (F τ) p = 0 by
    have h₁ := h (σ₁ - σ₂) (by
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero]; exact hσ)
    simp only [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h₁
    exact h₁
  intro τ hτ
  let e := trivializationAt F₁ E₁ p
  let b := Module.finBasis ℝ F₁
  have he : p ∈ e.baseSet := mem_baseSet_trivializationAt F₁ E₁ p
  have hframe := e.isLocalFrameOn_localFrame_baseSet I (↑n) b
  obtain ⟨s', hs'⟩ := hframe.exists_contMDiffSection_eqOn_nhd e.open_baseSet he
  obtain ⟨χ, -, hχsupport⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp
    (e.open_baseSet.mem_nhds he)
  have hcoeff_smooth : ∀ i, ContMDiff I 𝓘(ℝ) (↑n)
      (fun x => χ x • hframe.coeff i x (τ x)) := by
    intro i
    have hsmooth_lfc : ContMDiff I 𝓘(ℝ) (↑n)
        (fun x => χ x • e.localFrameCoeff I b i x (τ x)) := by
      intro x
      by_cases hx : x ∈ tsupport (χ : M → ℝ)
      · exact (χ.contMDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contMDiffAt.smul
          (contMDiffAt_localFrameCoeff b (hχsupport hx) τ.contMDiff.contMDiffAt i)
      · have hχ_zero : ∀ᶠ y in nhds x, (χ : M → ℝ) y = 0 := by
          apply Filter.Eventually.mono
            ((isClosed_tsupport (χ : M → ℝ)).isOpen_compl.mem_nhds hx)
          intro y hy
          exact (notMem_tsupport_iff_eventuallyEq.mp hy).self_of_nhds
        exact (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
          (hχ_zero.mono fun y hy => by simp [hy])
    refine hsmooth_lfc.congr fun x => ?_
    by_cases hx : x ∈ e.baseSet
    · have hbasis : e.basisAt b hx = hframe.toBasisAt hx := by
        ext j; simp [IsLocalFrameOn.toBasisAt, Trivialization.localFrame,
          Trivialization.basisAt, hx]
      simp only [hframe.coeff_apply_of_mem hx,
        e.localFrameCoeff_apply_of_mem_baseSet b hx, hbasis]
    · simp [hframe.coeff_apply_of_notMem hx,
        e.localFrameCoeff_apply_of_notMem_baseSet b hx]
  let u' : Fin (Module.finrank ℝ F₁) → C^n⟮I, M; ℝ⟯ := fun i =>
    ⟨fun x => χ x • hframe.coeff i x (τ x), hcoeff_smooth i⟩
  have hu'_zero : ∀ i, (u' i) p = 0 := by
    intro i; change χ p • hframe.coeff i p (τ p) = 0
    rw [χ.eq_one, one_smul, hτ, map_zero]
  have hτ_eq_near : ∀ᶠ x in nhds p, τ x = ∑ i, (u' i) x • (s' i) x := by
    filter_upwards [hs', χ.eventuallyEq_one,
      e.open_baseSet.mem_nhds he] with x hs'x hχx hx
    change τ x = ∑ i, (χ x • hframe.coeff i x (τ x)) • (s' i) x
    simp only [show χ x = (1 : M → ℝ) x from hχx, Pi.one_apply, one_smul]
    conv_lhs => rw [hframe.coeff_sum_eq (⇑τ) hx]
    congr 1; ext i; rw [hs'x i]
  obtain ⟨W, hW_open, hpW, hW_vanish⟩ : ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      ∀ x ∈ W, (τ - ∑ i, u' i • s' i) x = 0 := by
    obtain ⟨W, hW_nhds, hW⟩ := Filter.Eventually.exists_mem hτ_eq_near
    obtain ⟨W', hW'W, hW'_open, hpW'⟩ := mem_nhds_iff.mp hW_nhds
    exact ⟨W', hW'_open, hpW', fun x hx => by
      simp only [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero,
        ContMDiffSection.finset_sum_apply, ContMDiffSection.coe_smulContMDiffMap]
      exact hW x (hW'W hx)⟩
  have h_local := linearMap_acts_locally F (τ - ∑ i, u' i • s' i) hW_open hW_vanish p hpW
  rw [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h_local
  rw [h_local, map_sum]
  simp_rw [F.map_smul]
  rw [ContMDiffSection.finset_sum_apply]
  simp only [ContMDiffSection.coe_smulContMDiffMap]
  exact Finset.sum_eq_zero fun i _ => by rw [hu'_zero i, zero_smul]

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

noncomputable def ContMDiffVectorBundleHom.ofLinearMapSection
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    ContMDiffVectorBundleHom ℝ I n F₁ E₁ F₂ E₂ := by
  haveI : ContMDiffVectorBundle 1 F₁ E₁ I :=
    ContMDiffVectorBundle.of_le (show (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr h1n.out)
  haveI : ContMDiffVectorBundle 1 F₂ E₂ I :=
    ContMDiffVectorBundle.of_le (show (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr h1n.out)
  have acts_pointwise := ContMDiffVectorBundleHom.linearMap_acts_pointwise F
  have exists_section : ∀ (p : M) (v : E₁ p),
      ∃ (σ : Cₛ^n⟮I; F₁, E₁⟯), σ p = v := ContMDiffSection.exists_eq_at
  let φ : ∀ x : M, E₁ x →ₗ[ℝ] E₂ x := fun x =>
    { toFun := fun v => (F (exists_section x v).choose) x
      map_add' := fun v w => by
        let σ_v := (exists_section x v).choose
        let σ_w := (exists_section x w).choose
        let σ_vw := (exists_section x (v + w)).choose
        have hv : σ_v x = v := (exists_section x v).choose_spec
        have hw : σ_w x = w := (exists_section x w).choose_spec
        have h_add : (σ_v + σ_w) x = v + w := by
          simp [ContMDiffSection.coe_add, Pi.add_apply, hv, hw]
        calc (F σ_vw) x
            = (F (σ_v + σ_w)) x := acts_pointwise σ_vw (σ_v + σ_w) x
                ((exists_section x (v + w)).choose_spec ▸ h_add ▸ rfl)
          _ = (F σ_v) x + (F σ_w) x := by
                rw [map_add, ContMDiffSection.coe_add, Pi.add_apply]
      map_smul' := fun c v => by
        let σ_v := (exists_section x v).choose
        let σ_cv := (exists_section x (c • v)).choose
        have hv : σ_v x = v := (exists_section x v).choose_spec
        have h_smul : (c • σ_v) x = c • v := by
          simp [ContMDiffSection.coe_smul, Pi.smul_apply, hv]
        let c' : C^n⟮I, M; ℝ⟯ := ⟨fun _ => c, contMDiff_const⟩
        have hc_eq : c • σ_v = c' • σ_v := by
          ext y
          rfl
        calc (F σ_cv) x
            = (F (c • σ_v)) x := acts_pointwise σ_cv (c • σ_v) x
                ((exists_section x (c • v)).choose_spec ▸ h_smul ▸ rfl)
          _ = c • (F σ_v) x := by
                rw [hc_eq, F.map_smul, ContMDiffSection.coe_smulContMDiffMap]; rfl }
  have φ_spec : ∀ (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M), φ x (σ x) = (F σ) x :=
    fun σ x => acts_pointwise _ σ x (exists_section x (σ x)).choose_spec
  have Φ_smooth : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F₂ E₂)) := by
    intro p₀
    rw [contMDiffAt_totalSpace]
    refine ⟨?_, ?_⟩
    · exact (contMDiff_proj E₁).contMDiffAt
    · let e₁ := trivializationAt F₁ E₁ p₀.proj
      let e₂ := trivializationAt F₂ E₂ p₀.proj
      let b₁ := Module.finBasis ℝ F₁
      have he₁ : p₀.proj ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ p₀.proj
      have he₂ : p₀.proj ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ p₀.proj
      have hframe₁ := e₁.isLocalFrameOn_localFrame_baseSet I (↑n) b₁
      obtain ⟨σ', hσ'⟩ := hframe₁.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
      have hφ_eq : ∀ᶠ x in nhds p₀,
          (e₂ ⟨x.proj, φ x.proj x.2⟩).2 =
          ∑ i, b₁.repr (e₁ x).2 i •
            (e₂ ⟨x.proj, (F (σ' i)) x.proj⟩).2 := by
        have h_base : ∀ᶠ x in nhds p₀,
            x.proj ∈ e₁.baseSet ∧ x.proj ∈ e₂.baseSet :=
          (e₁.open_baseSet.inter e₂.open_baseSet).preimage
            (FiberBundle.continuous_proj F₁ E₁) |>.mem_nhds ⟨he₁, he₂⟩
        have h_σ'_pull : ∀ᶠ x in nhds p₀,
            ∀ i, (σ' i) x.proj = e₁.localFrame b₁ i x.proj := by
          have := hσ'.mono (fun q hq => hq)
          exact this.filter_mono
            ((FiberBundle.continuous_proj F₁ E₁).continuousAt)
        filter_upwards [h_base, h_σ'_pull] with ⟨q, v⟩ ⟨hq₁, hq₂⟩ hσ'q
        let le₁ := e₁.linearEquivAt ℝ q hq₁
        let le₂ := e₂.linearEquivAt ℝ q hq₂
        have hv_decomp : v = ∑ i, b₁.repr (le₁ v) i • le₁.symm (b₁ i) := by
          calc v = le₁.symm (le₁ v) := (le₁.symm_apply_apply v).symm
            _ = le₁.symm (∑ i, b₁.repr (le₁ v) i • b₁ i) := by rw [b₁.sum_repr]
            _ = _ := by rw [map_sum]; congr 1; ext j; rw [LinearEquiv.map_smul]
        have hφv : φ q v = ∑ i, b₁.repr (le₁ v) i • (F (σ' i)) q := by
          conv_lhs => rw [hv_decomp]
          simp only [map_sum, LinearMap.map_smul]
          congr 1; ext j; congr 1
          rw [show le₁.symm (b₁ j) = e₁.localFrame b₁ j q from by
            simp [Trivialization.localFrame, hq₁, Trivialization.basisAt, le₁]]
          rw [← hσ'q j]; exact φ_spec (σ' j) q
        rw [hφv]
        simp only [show ∀ w : E₂ q, (e₂ ⟨q, w⟩).2 = le₂ w from fun _ => rfl]
        rw [map_sum]; simp only [map_smul]; rfl
      refine ContMDiffAt.congr_of_eventuallyEq ?_ hφ_eq
      apply ContMDiffAt.sum
      intro i _
      apply ContMDiffAt.smul (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, F₂))
      · have h_e₁_snd : ContMDiffAt (I.prod 𝓘(ℝ, F₁)) 𝓘(ℝ, F₁) (↑n)
            (fun x => (e₁ x).2) p₀ :=
          (contMDiffAt_totalSpace (f := _root_.id)).mp contMDiffAt_id |>.2
        have hcl : ContDiff ℝ (↑n) (fun w : F₁ => b₁.repr w i) :=
          (ContinuousLinearMap.proj i |>.comp
            b₁.equivFun.toContinuousLinearEquiv.toContinuousLinearMap).contDiff
        exact hcl.contDiffAt.contMDiffAt.comp _ h_e₁_snd
      · have h_sect : ContMDiffAt I 𝓘(ℝ, F₂) (↑n)
            (fun q => (e₂ ⟨q, (F (σ' i)) q⟩).2) p₀.proj :=
          (contMDiffAt_section p₀.proj).mp (F (σ' i)).contMDiff.contMDiffAt
        exact h_sect.comp _ (contMDiff_proj E₁).contMDiffAt
  exact ⟨_root_.id, fun p => ⟨p.proj, φ p.proj p.2⟩, Φ_smooth, φ, fun _ _ => rfl⟩

omit [SigmaCompactSpace M] [FiniteDimensional ℝ F₂] [ContMDiffVectorBundle (↑n) F₂ E₂ I] in
theorem ContMDiffVectorBundleHom.ofLinearMapSection_baseMap
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    (ofLinearMapSection F).baseMap = _root_.id := rfl

omit [SigmaCompactSpace M] [FiniteDimensional ℝ F₂] [ContMDiffVectorBundle (↑n) F₂ E₂ I] in
theorem ContMDiffVectorBundleHom.ofLinearMapSection_spec
    (F : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) (σ) :
    F σ = (ofLinearMapSection F).mapSection (ofLinearMapSection_baseMap F) σ := by
  ext x
  exact (linearMap_acts_pointwise F σ _ x
    (ContMDiffSection.exists_eq_at x (σ x)).choose_spec.symm)

omit h1n in
omit [SigmaCompactSpace M] [FiniteDimensional ℝ F₂] [ContMDiffVectorBundle (↑n) F₂ E₂ I] in
theorem ContMDiffVectorBundleHom.ofLinearMapSection_mapSection
    (Φ Ψ : ContMDiffVectorBundleHom ℝ I n F₁ E₁ F₂ E₂)
    (hΦ : Φ.baseMap = _root_.id) (hΨ : Ψ.baseMap = _root_.id)
    (h_eq : ∀ σ, Φ.mapSection hΦ σ = Ψ.mapSection hΨ σ) :
    Φ.toFun = Ψ.toFun := by
  funext ⟨x, v⟩
  obtain ⟨σ, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₁) (n := n) x v
  rw [Φ.mapSection_apply hΦ, Ψ.mapSection_apply hΨ, h_eq]

noncomputable def ContMDiffVectorBundleEquiv.ofLinearEquivSection
    (F : Cₛ^n⟮I; F₁, E₁⟯ ≃ₗ[C^n⟮I, M; ℝ⟯] Cₛ^n⟮I; F₂, E₂⟯) :
    ContMDiffVectorBundleEquiv ℝ I n F₁ E₁ F₂ E₂ := by
  let Φ := ContMDiffVectorBundleHom.ofLinearMapSection F.toLinearMap
  let hΦ : Φ.baseMap = _root_.id :=
    ContMDiffVectorBundleHom.ofLinearMapSection_baseMap F.toLinearMap
  have hΦ_spec : ∀ σ, F σ = Φ.mapSection hΦ σ :=
    ContMDiffVectorBundleHom.ofLinearMapSection_spec F.toLinearMap
  let Ψ := ContMDiffVectorBundleHom.ofLinearMapSection F.symm.toLinearMap
  let hΨ : Ψ.baseMap = _root_.id :=
    ContMDiffVectorBundleHom.ofLinearMapSection_baseMap F.symm.toLinearMap
  have hΨ_spec : ∀ σ, F.symm σ = Ψ.mapSection hΨ σ :=
    ContMDiffVectorBundleHom.ofLinearMapSection_spec F.symm.toLinearMap
  have hΨΦ : ∀ p, Ψ.toFun (Φ.toFun p) = p := by
    intro ⟨x, v⟩
    obtain ⟨σ, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₁) (n := n) x v
    rw [Φ.mapSection_apply hΦ, Ψ.mapSection_apply hΨ (Φ.mapSection hΦ σ) x]
    congr 1
    exact DFunLike.congr_fun
      (show Ψ.mapSection hΨ (Φ.mapSection hΦ σ) = σ from by
        rw [← hΨ_spec, ← hΦ_spec]; simp) x
  have hΦΨ : ∀ p, Φ.toFun (Ψ.toFun p) = p := by
    intro ⟨x, v⟩
    obtain ⟨σ, rfl⟩ := ContMDiffSection.exists_eq_at (I := I) (F := F₂) (n := n) x v
    rw [Ψ.mapSection_apply hΨ, Φ.mapSection_apply hΦ (Ψ.mapSection hΨ σ) x]
    congr 1
    exact DFunLike.congr_fun
      (show Φ.mapSection hΦ (Ψ.mapSection hΨ σ) = σ from by
        rw [← hΦ_spec, ← hΨ_spec]; simp) x
  exact ContMDiffVectorBundleEquiv.ofMutualInverseHoms Φ Ψ hΦ hΨΦ hΦΨ

open FiberBundle in
noncomputable def ContMDiffVectorBundleHom.ofTensorialAt
    (Ψ : (Π x : M, E₁ x) → (Π x : M, E₂ x))
    (hΨ : ∀ x, TensorialAt I F₁ (fun σ => Ψ σ x) x)
    (hΨ_smooth : ∀ σ : Cₛ^n⟮I; F₁, E₁⟯,
      ContMDiff I (I.prod 𝓘(ℝ, F₂)) n (T% (Ψ ⇑σ))) :
    ContMDiffVectorBundleHom ℝ I n F₁ E₁ F₂ E₂ := by
  have h1n' : (1 : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := WithTop.coe_le_coe.mpr h1n.out
  have hn_ne : (↑n : WithTop ℕ∞) ≠ 0 := (zero_lt_one.trans_le h1n').ne'
  haveI : ContMDiffVectorBundle 1 F₁ E₁ I := ContMDiffVectorBundle.of_le h1n'
  haveI : ContMDiffVectorBundle 1 F₂ E₂ I := ContMDiffVectorBundle.of_le h1n'
  let φ : ∀ x : M, E₁ x →ₗ[ℝ] E₂ x := fun x =>
    { toFun := fun v => Ψ (extend F₁ v) x
      map_add' := fun v₁ v₂ => by
        rw [← (hΨ x).add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
        exact (hΨ x).pointwise (mdifferentiableAt_extend ..)
          (mdifferentiableAt_add_section (mdifferentiableAt_extend ..)
            (mdifferentiableAt_extend ..)) (by simp)
      map_smul' := fun c v => by
        dsimp
        rw [← (hΨ x).smul (f := fun _ => c) (mdifferentiable_const ..)
          (mdifferentiableAt_extend ..)]
        exact (hΨ x).pointwise (mdifferentiableAt_extend ..)
          (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)) (by simp) }
  have φ_spec : ∀ (σ : Cₛ^n⟮I; F₁, E₁⟯) (x : M), φ x (σ x) = Ψ (⇑σ) x :=
    fun σ x => (hΨ x).pointwise (mdifferentiableAt_extend ..)
      (σ.contMDiff.contMDiffAt.mdifferentiableAt hn_ne) (by simp)
  have Φ_smooth : ContMDiff (I.prod 𝓘(ℝ, F₁)) (I.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ E₁ => (⟨p.proj, φ p.proj p.2⟩ : TotalSpace F₂ E₂)) := by
    intro p₀
    rw [contMDiffAt_totalSpace]
    refine ⟨(contMDiff_proj E₁).contMDiffAt, ?_⟩
    let e₁ := trivializationAt F₁ E₁ p₀.proj
    let e₂ := trivializationAt F₂ E₂ p₀.proj
    let b₁ := Module.finBasis ℝ F₁
    have he₁ : p₀.proj ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ p₀.proj
    have he₂ : p₀.proj ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ p₀.proj
    have hframe₁ := e₁.isLocalFrameOn_localFrame_baseSet I (↑n) b₁
    obtain ⟨σ', hσ'⟩ := hframe₁.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have hφ_eq : ∀ᶠ x in nhds p₀,
        (e₂ ⟨x.proj, φ x.proj x.2⟩).2 =
        ∑ i, b₁.repr (e₁ x).2 i •
          (e₂ ⟨x.proj, Ψ (⇑(σ' i)) x.proj⟩).2 := by
      have h_base : ∀ᶠ x in nhds p₀,
          x.proj ∈ e₁.baseSet ∧ x.proj ∈ e₂.baseSet :=
        (e₁.open_baseSet.inter e₂.open_baseSet).preimage
          (FiberBundle.continuous_proj F₁ E₁) |>.mem_nhds ⟨he₁, he₂⟩
      have h_σ'_pull : ∀ᶠ x in nhds p₀,
          ∀ i, (σ' i) x.proj = e₁.localFrame b₁ i x.proj := by
        have := hσ'.mono (fun q hq => hq)
        exact this.filter_mono ((FiberBundle.continuous_proj F₁ E₁).continuousAt)
      filter_upwards [h_base, h_σ'_pull] with ⟨q, v⟩ ⟨hq₁, hq₂⟩ hσ'q
      let le₁ := e₁.linearEquivAt ℝ q hq₁
      let le₂ := e₂.linearEquivAt ℝ q hq₂
      have hv_decomp : v = ∑ i, b₁.repr (le₁ v) i • le₁.symm (b₁ i) := by
        calc v = le₁.symm (le₁ v) := (le₁.symm_apply_apply v).symm
          _ = le₁.symm (∑ i, b₁.repr (le₁ v) i • b₁ i) := by rw [b₁.sum_repr]
          _ = _ := by rw [map_sum]; congr 1; ext j; rw [LinearEquiv.map_smul]
      have hφv : φ q v = ∑ i, b₁.repr (le₁ v) i • Ψ (⇑(σ' i)) q := by
        conv_lhs => rw [hv_decomp]
        simp only [map_sum, LinearMap.map_smul]
        congr 1; ext j; congr 1
        rw [show le₁.symm (b₁ j) = e₁.localFrame b₁ j q from by
          simp [Trivialization.localFrame, hq₁, Trivialization.basisAt, le₁]]
        rw [← hσ'q j]; exact φ_spec (σ' j) q
      rw [hφv]
      simp only [show ∀ w : E₂ q, (e₂ ⟨q, w⟩).2 = le₂ w from fun _ => rfl]
      rw [map_sum]; simp only [map_smul]; rfl
    refine ContMDiffAt.congr_of_eventuallyEq ?_ hφ_eq
    apply ContMDiffAt.sum
    intro i _
    apply ContMDiffAt.smul (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, F₂))
    · have h_e₁_snd : ContMDiffAt (I.prod 𝓘(ℝ, F₁)) 𝓘(ℝ, F₁) (↑n)
          (fun x => (e₁ x).2) p₀ :=
        (contMDiffAt_totalSpace (f := _root_.id)).mp contMDiffAt_id |>.2
      have hcl : ContDiff ℝ (↑n) (fun w : F₁ => b₁.repr w i) :=
        (ContinuousLinearMap.proj i |>.comp
          b₁.equivFun.toContinuousLinearEquiv.toContinuousLinearMap).contDiff
      exact hcl.contDiffAt.contMDiffAt.comp _ h_e₁_snd
    · have h_sect : ContMDiffAt I 𝓘(ℝ, F₂) (↑n)
          (fun q => (e₂ ⟨q, Ψ (⇑(σ' i)) q⟩).2) p₀.proj :=
        (contMDiffAt_section p₀.proj).mp (hΨ_smooth (σ' i)).contMDiffAt
      exact h_sect.comp _ (contMDiff_proj E₁).contMDiffAt
  exact ⟨_root_.id, fun p => ⟨p.proj, φ p.proj p.2⟩, Φ_smooth, φ, fun _ _ => rfl⟩

end VBC

end MapSection

section TrivializationSymmL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]

theorem Bundle.Trivialization.contMDiffOn_symmL_section
    [ContMDiffVectorBundle ∞ F V I]
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (w : F) :
    ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
      (fun x => (⟨x, e.symmL ℝ x w⟩ : Bundle.TotalSpace F V)) e.baseSet := by
  rw [Bundle.Trivialization.contMDiffOn_section_iff (s := fun x => e.symmL ℝ x w)
    e e.open_baseSet (fun _ hx => hx)]
  exact (contMDiffOn_const (c := w)).congr (fun x hx => by
    rw [Bundle.Trivialization.symmL_apply e hx w, Bundle.Trivialization.apply_mk_symm e hx w])

end TrivializationSymmL
