-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Elliptic/Operator/SmoothDenseLp.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Elliptic.Regularity.LaplacianDomain.L2
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Geometry.Manifold.BumpFunction

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Set Filter BoundedContinuousFunction
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace BoundedContinuousFunction

namespace CalabiYau
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩



def SmoothScalar.toContinuousMap {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) : C(M, ℝ) :=
  ⟨f.toFun, f.smooth.continuous⟩

@[simp] lemma SmoothScalar.toContinuousMap_smul {g : SmoothRiemannianMetric I M}
    (c : ℝ) (f : SmoothScalar g) :
    (c • f).toContinuousMap = c • f.toContinuousMap := by
  ext x
  rfl

@[simp] lemma SmoothScalar.toContinuousMap_add {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    (f + h).toContinuousMap = f.toContinuousMap + h.toContinuousMap := by
  ext x
  rfl

@[simp] lemma SmoothScalar.toContinuousMap_zero {g : SmoothRiemannianMetric I M} :
    (0 : SmoothScalar g).toContinuousMap = (0 : C(M, ℝ)) := by
  ext x
  rfl

@[simp] lemma SmoothScalar.toContinuousMap_apply {g : SmoothRiemannianMetric I M}
    (f : SmoothScalar g) (x : M) :
    f.toContinuousMap x = f.toFun x := rfl

def SmoothScalar.one (g : SmoothRiemannianMetric I M) : SmoothScalar g where
  toFun := fun _ => (1 : ℝ)
  smooth := contMDiff_const

@[simp] lemma SmoothScalar.one_toFun (g : SmoothRiemannianMetric I M) :
    (SmoothScalar.one g).toFun = fun _ : M => (1 : ℝ) := rfl

def SmoothScalar.mul {g : SmoothRiemannianMetric I M} (f h : SmoothScalar g) :
    SmoothScalar g where
  toFun := fun x => f.toFun x * h.toFun x
  smooth := f.smooth.mul h.smooth

@[simp] lemma SmoothScalar.mul_toFun {g : SmoothRiemannianMetric I M}
    (f h : SmoothScalar g) :
    (SmoothScalar.mul f h).toFun = fun x => f.toFun x * h.toFun x := rfl

def SmoothScalar.imageInContinuousMap (g : SmoothRiemannianMetric I M) :
    Set C(M, ℝ) :=
  { φ : C(M, ℝ) | ∃ f : SmoothScalar g, f.toContinuousMap = φ }

def smoothScalarSubalgebra (g : SmoothRiemannianMetric I M) :
    Subalgebra ℝ C(M, ℝ) where
  carrier := SmoothScalar.imageInContinuousMap g
  mul_mem' := by
    rintro φ ψ ⟨f, hf⟩ ⟨h, hh⟩
    refine ⟨SmoothScalar.mul f h, ?_⟩
    ext x
    have h1 : φ x = f.toFun x := by rw [← hf]; rfl
    have h2 : ψ x = h.toFun x := by rw [← hh]; rfl
    change f.toFun x * h.toFun x = (φ * ψ) x
    rw [ContinuousMap.mul_apply, h1, h2]
  one_mem' := ⟨SmoothScalar.one g, by ext x; rfl⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf⟩ ⟨h, hh⟩
    refine ⟨f + h, ?_⟩
    ext x
    have h1 : φ x = f.toFun x := by rw [← hf]; rfl
    have h2 : ψ x = h.toFun x := by rw [← hh]; rfl
    change f.toFun x + h.toFun x = (φ + ψ) x
    rw [ContinuousMap.add_apply, h1, h2]
  zero_mem' := ⟨(0 : SmoothScalar g), by ext x; rfl⟩
  algebraMap_mem' c := by
    refine ⟨c • SmoothScalar.one g, ?_⟩
    apply ContinuousMap.ext
    intro x
    change c * (1 : ℝ) = (algebraMap ℝ C(M, ℝ) c) x
    rw [mul_one, Algebra.algebraMap_eq_smul_one]
    change c = (c • (1 : C(M, ℝ))) x
    rw [ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]

@[simp] lemma mem_smoothScalarSubalgebra_iff {g : SmoothRiemannianMetric I M}
    {φ : C(M, ℝ)} :
    φ ∈ smoothScalarSubalgebra (I := I) (M := M) g ↔
      ∃ f : SmoothScalar g, f.toContinuousMap = φ := Iff.rfl

variable [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] in
private lemma exists_smooth_separating
    (x y : M) (hxy : x ≠ y) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ f x = 1 ∧ f y = 0 := by
  classical
  have h_compl_open : IsOpen ({y}ᶜ : Set M) := isOpen_compl_singleton
  have h_x_in_compl : x ∈ ({y}ᶜ : Set M) := by
    intro hx
    rw [Set.mem_singleton_iff] at hx
    exact hxy hx
  have h_compl_mem : ({y}ᶜ : Set M) ∈ 𝓝 x :=
    h_compl_open.mem_nhds h_x_in_compl
  have hbasis := SmoothBumpFunction.nhds_basis_support (I := I) h_compl_mem
  obtain ⟨φ, hφ_tsupp⟩ := hbasis.ex_mem
  refine ⟨(φ : M → ℝ), φ.contMDiff, ?_, ?_⟩
  · exact φ.eq_one
  · by_contra hy
    have hy_support : y ∈ tsupport (φ : M → ℝ) := subset_tsupport _ hy
    have hy_in_compl : y ∈ ({y}ᶜ : Set M) := hφ_tsupp hy_support
    exact hy_in_compl rfl

variable [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] in
theorem smoothScalarSubalgebra_separatesPoints (g : SmoothRiemannianMetric I M) :
    (smoothScalarSubalgebra (I := I) (M := M) g).SeparatesPoints := by
  intro x y hxy
  obtain ⟨f, hf, hfx, hfy⟩ := exists_smooth_separating (I := I) (M := M) x y hxy
  refine ⟨f, ?_, ?_⟩
  · refine ⟨(⟨f, hf⟩ : SmoothScalar g).toContinuousMap, ?_, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  · rw [hfx, hfy]
    exact one_ne_zero

variable [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] in
theorem exists_smoothScalar_sup_close (g : SmoothRiemannianMetric I M)
    (φ : C(M, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : SmoothScalar g, ‖f.toContinuousMap - φ‖ < ε := by
  obtain ⟨g', hg'_lt⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (smoothScalarSubalgebra (I := I) (M := M) g)
      (smoothScalarSubalgebra_separatesPoints (I := I) (M := M) g) φ ε hε
  obtain ⟨f, hf⟩ := g'.2
  refine ⟨f, ?_⟩
  rw [hf]
  exact hg'_lt

variable [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] in
private lemma eLpNorm_two_le_of_norm_le [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (φ : M → ℝ) (_hφ : Continuous φ) (K : ℝ)
    (hK : ∀ x, ‖φ x‖ ≤ K) :
    eLpNorm φ 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g
          (Set.univ : Set M)) ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ENNReal.ofReal K := by
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  exact MeasureTheory.eLpNorm_le_of_ae_bound (μ := riemannianVolumeMeasure (I := I) (M := M) g)
    (f := φ) (C := K) _hφ.aestronglyMeasurable (Filter.Eventually.of_forall hK)

variable [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] in
private lemma eLpNorm_smooth_sub_bc_le
    (g : SmoothRiemannianMetric I M)
    (f : SmoothScalar g) (ψ : M →ᵇ ℝ) (δ : ℝ)
    (h_pt : ∀ x : M, ‖f.toFun x - ψ x‖ ≤ δ) :
    eLpNorm (fun x : M => f.toFun x - ψ x) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      (riemannianVolumeMeasure (I := I) (M := M) g) Set.univ ^
          ((2 : ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal δ := by
  classical
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have h_diff_cont : Continuous (fun x : M => f.toFun x - ψ x) :=
    f.smooth.continuous.sub ψ.continuous
  exact eLpNorm_two_le_of_norm_le (I := I) (M := M) g _ h_diff_cont δ h_pt

variable [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] in
private lemma edist_toLp_eq_eLpNorm
    {μ : Measure M} (a b : M → ℝ) (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    edist (ha.toLp a) (hb.toLp b) = eLpNorm (fun x : M => a x - b x) 2 μ := by
  rw [Lp.edist_toLp_toLp]
  rfl

variable [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M] in
private lemma exists_smoothToLp_close_to_memLp
    (g : SmoothRiemannianMetric I M)
    [hμ_fin : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g)]
    [hμ_wreg : (riemannianVolumeMeasure (I := I) (M := M) g).WeaklyRegular]
    (h : M → ℝ) (h_mem : MemLp h 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f : SmoothScalar g,
      edist (f.memLp_two.toLp f.toFun) (h_mem.toLp h) ≤ ε := by
  classical
  set μvol := riemannianVolumeMeasure (I := I) (M := M) g with hμvol_def
  have h2 : (ε / 2 : ℝ≥0∞) ≠ 0 := by
    rw [Ne, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hε, ENNReal.ofNat_ne_top⟩
  obtain ⟨ψ_bc, hψ_eLpNorm_le, _hψ_mem⟩ :=
    h_mem.exists_boundedContinuous_eLpNorm_sub_le (E := ℝ) (μ := μvol) (p := 2)
      ENNReal.ofNat_ne_top h2
  have h_finite : μvol Set.univ < ⊤ := IsFiniteMeasure.measure_univ_lt_top
  set Cμ_enn : ℝ≥0∞ := μvol Set.univ ^ ((2 : ℝ≥0∞).toReal⁻¹) with hCμ_enn_def
  have hCμ_enn_ne_top : Cμ_enn ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ ((2 : ℝ≥0∞).toReal⁻¹))
      h_finite.ne
  obtain ⟨δ_real, hδ_pos, hδ_bound⟩ :
      ∃ δ_real : ℝ, 0 < δ_real ∧ Cμ_enn * ENNReal.ofReal δ_real ≤ ε / 2 := by
    by_cases h_top : ε / 2 = ⊤
    · refine ⟨1, by norm_num, ?_⟩
      rw [h_top]; exact le_top
    · set Cμ : ℝ := Cμ_enn.toReal with hCμ_def
      have hCμ_nn : 0 ≤ Cμ := ENNReal.toReal_nonneg
      set δ_real : ℝ := (ε / 2).toReal / (Cμ + 1) with hδ_def
      have hε2_pos : 0 < (ε / 2).toReal := by
        rw [ENNReal.toReal_pos_iff]
        exact ⟨pos_iff_ne_zero.mpr h2, lt_top_iff_ne_top.mpr h_top⟩
      have hCμ1_pos : 0 < Cμ + 1 := by linarith
      have hδ_pos : 0 < δ_real := by positivity
      refine ⟨δ_real, hδ_pos, ?_⟩
      have hCμ_enn_eq : Cμ_enn = ENNReal.ofReal Cμ := by
        rw [hCμ_def, ENNReal.ofReal_toReal hCμ_enn_ne_top]
      rw [hCμ_enn_eq, ← ENNReal.ofReal_mul hCμ_nn]
      have hreal_le : Cμ * δ_real ≤ (ε / 2).toReal := by
        rw [hδ_def]
        rw [mul_comm Cμ ((ε / 2).toReal / (Cμ + 1))]
        rw [div_mul_eq_mul_div]
        rw [div_le_iff₀ hCμ1_pos]
        nlinarith
      calc ENNReal.ofReal (Cμ * δ_real)
          ≤ ENNReal.ofReal (ε / 2).toReal := ENNReal.ofReal_le_ofReal hreal_le
        _ = ε / 2 := ENNReal.ofReal_toReal h_top
  set ψ_cont : C(M, ℝ) := ψ_bc.toContinuousMap with hψ_cont_def
  obtain ⟨f_smooth, hf_close⟩ := exists_smoothScalar_sup_close (I := I) (M := M) g ψ_cont hδ_pos
  have h_pointwise_bound : ∀ x : M, ‖f_smooth.toFun x - ψ_bc x‖ ≤ δ_real := by
    intro x
    have heq : f_smooth.toFun x - ψ_bc x =
        (f_smooth.toContinuousMap - ψ_cont) x := rfl
    rw [heq]
    exact (norm_coe_le_norm _ x).trans hf_close.le
  have h_eLpNorm_diff :
      eLpNorm (fun x : M => f_smooth.toFun x - ψ_bc x) 2 μvol ≤
        Cμ_enn * ENNReal.ofReal δ_real :=
    eLpNorm_smooth_sub_bc_le (I := I) (M := M) g f_smooth ψ_bc δ_real h_pointwise_bound
  refine ⟨f_smooth, ?_⟩
  have hψ_mem : MemLp (ψ_bc : M → ℝ) 2 μvol := _hψ_mem
  have h1 :
      edist (f_smooth.memLp_two.toLp f_smooth.toFun)
          (hψ_mem.toLp (ψ_bc : M → ℝ)) ≤ ε / 2 := by
    rw [edist_toLp_eq_eLpNorm]
    exact le_trans h_eLpNorm_diff hδ_bound
  have h2_bound :
      edist (hψ_mem.toLp (ψ_bc : M → ℝ)) (h_mem.toLp h) ≤ ε / 2 := by
    rw [edist_toLp_eq_eLpNorm]
    rw [show (fun x : M => (ψ_bc : M → ℝ) x - h x) = -(fun x : M => h x - ψ_bc x) from
        funext fun x => by rw [Pi.neg_apply]; ring]
    rw [eLpNorm_neg]
    exact hψ_eLpNorm_le
  calc edist (f_smooth.memLp_two.toLp f_smooth.toFun) (h_mem.toLp h)
      ≤ edist (f_smooth.memLp_two.toLp f_smooth.toFun)
            (hψ_mem.toLp (ψ_bc : M → ℝ)) +
          edist (hψ_mem.toLp (ψ_bc : M → ℝ)) (h_mem.toLp h) :=
        edist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2_bound
    _ = ε := ENNReal.add_halves _

variable [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem denseRange_smoothToLp (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToLp (I := I) (M := M) g) := by
  classical
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have : (riemannianVolumeMeasure (I := I) (M := M) g).WeaklyRegular :=
    (riemannianVolumeMeasure_regular (I := I) (M := M) g).weaklyRegular
  intro v
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε ↦ ?_
  obtain ⟨f, hf⟩ := exists_smoothToLp_close_to_memLp (I := I) (M := M) g
    (v : M → ℝ) (Lp.memLp v) (ne_of_gt hε)
  refine ⟨smoothToLp (I := I) (M := M) g f, mem_range_self _, ?_⟩
  rw [Metric.mem_closedEBall]
  have h_smooth_eq : (smoothToLp (I := I) (M := M) g f : Lp ℝ 2 _) =
      f.memLp_two.toLp f.toFun := rfl
  rw [h_smooth_eq]
  have h_v_eq : v = (Lp.memLp v).toLp (v : M → ℝ) := (Lp.toLp_coeFn v _).symm
  conv_lhs => rw [show v = (Lp.memLp v).toLp (v : M → ℝ) from h_v_eq]
  exact hf

variable [Module.Finite ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] in
theorem denseRange_H1ComplToLp (g : SmoothRiemannianMetric I M) :
    DenseRange (h1ComplToLp (I := I) (M := M) g) := by
  refine Dense.mono ?_ (denseRange_smoothToLp (I := I) (M := M) g)
  rintro y ⟨u, hu⟩
  refine ⟨smoothToH1Compl (I := I) (M := M) g u, ?_⟩
  rw [h1ComplToLp_smoothToH1Compl]
  exact hu

end Laplacian
end Analysis
end CalabiYau

end
