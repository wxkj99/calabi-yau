-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Spectral/Scalar/EigenBasis.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Spectral.Scalar.Compactness
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace CalabiYau
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open CalabiYau.RiemannianVolume
open CalabiYau.DivergenceTheorem
open CalabiYau.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem resolventL2_injective (g : SmoothRiemannianMetric I M) :
    Function.Injective (resolventL2 (I := I) (M := M) g) := by
  rw [injective_iff_map_eq_zero]
  intro u hRu
  have h_var := resolvent_inner_eq_lpFunctional (I := I) (M := M) g u
    (resolvent (I := I) (M := M) g u)
  have h_self_norm : ⟪resolvent (I := I) (M := M) g u,
        resolvent (I := I) (M := M) g u⟫_ℝ =
      ‖resolvent (I := I) (M := M) g u‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  have h_replace : H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g u) =
      resolventL2 (I := I) (M := M) g u := by
    rw [resolventL2_apply]
  rw [h_self_norm] at h_var
  rw [h_replace, hRu, inner_zero_left] at h_var
  have h_resolvent_zero : resolvent (I := I) (M := M) g u = 0 := by
    have h_norm_sq_zero : ‖resolvent (I := I) (M := M) g u‖ ^ 2 = 0 := h_var
    have h_norm_zero : ‖resolvent (I := I) (M := M) g u‖ = 0 :=
      pow_eq_zero_iff (two_ne_zero) |>.mp h_norm_sq_zero
    exact norm_eq_zero.mp h_norm_zero
  apply resolvent_injective (I := I) (M := M) g
  rw [(resolvent (I := I) (M := M) g).map_zero]
  exact h_resolvent_zero

omit [NeZero (Module.finrank ℝ E)] in
theorem H1ComplToLp_injective_on_laplacianDomain
    (g : SmoothRiemannianMetric I M)
    {u v : laplacianDomain (I := I) (M := M) g}
    (h_eq : H1ComplToLp (I := I) (M := M) g (u : H1Compl g) =
            H1ComplToLp (I := I) (M := M) g (v : H1Compl g)) :
    (u : H1Compl g) = (v : H1Compl g) := by
  set wu : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g u with hwu_def
  set wv : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g v with hwv_def
  have h_u_res : (u : H1Compl g) =
      resolvent (I := I) (M := M) g wu :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g u).symm
  have h_v_res : (v : H1Compl g) =
      resolvent (I := I) (M := M) g wv :=
    (resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g v).symm
  have hLHS : resolventL2 (I := I) (M := M) g wu =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g wu) :=
    resolventL2_apply (I := I) (M := M) g _
  have hRHS : resolventL2 (I := I) (M := M) g wv =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g wv) :=
    resolventL2_apply (I := I) (M := M) g _
  have h_eq_L2 :
      resolventL2 (I := I) (M := M) g wu =
      resolventL2 (I := I) (M := M) g wv := by
    rw [hLHS, hRHS, ← h_u_res, ← h_v_res]
    exact h_eq
  have h_pre_eq : wu = wv := by
    have h_inj := resolventL2_injective (I := I) (M := M) g
    exact h_inj h_eq_L2
  rw [h_u_res, h_v_res, h_pre_eq]

omit [NeZero (Module.finrank ℝ E)] in
theorem resolventEigenspace_zero_eq_bot (g : SmoothRiemannianMetric I M) :
    resolventEigenspace (I := I) (M := M) g 0 = ⊥ := by
  unfold resolventEigenspace
  rw [Module.End.eigenspace_zero]
  rw [LinearMap.ker_eq_bot]
  exact resolventL2_injective (I := I) (M := M) g

def NonzeroResolventEigenvalue (g : SmoothRiemannianMetric I M) : Type _ :=
  { μ : ℝ // μ ≠ 0 ∧
    Module.End.HasEigenvalue ((resolventL2 (I := I) (M := M) g).toLinearMap) μ }

namespace NonzeroResolventEigenvalue

variable {g : SmoothRiemannianMetric I M}

def val (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) : ℝ := μ.1

omit [NeZero (Module.finrank ℝ E)] in
lemma val_ne_zero (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    μ.val ≠ 0 := μ.2.1

omit [NeZero (Module.finrank ℝ E)] in
lemma hasEigenvalue (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    Module.End.HasEigenvalue
      ((resolventL2 (I := I) (M := M) g).toLinearMap) μ.val :=
  μ.2.2

end NonzeroResolventEigenvalue

omit [NeZero (Module.finrank ℝ E)] in
private lemma nonzero_resolvent_eigenvalues_set_eq_iUnion
    (g : SmoothRiemannianMetric I M) :
    { μ : ℝ | μ ≠ 0 ∧
        Module.End.HasEigenvalue
          ((resolventL2 (I := I) (M := M) g).toLinearMap) μ } =
      ⋃ n : ℕ, { μ : ℝ |
        Module.End.HasEigenvalue
          ((resolventL2 (I := I) (M := M) g).toLinearMap) μ ∧
        (1 : ℝ) / (n + 1) ≤ |μ| } := by
  ext μ
  constructor
  · rintro ⟨hμ_ne, hμ_eig⟩
    have h_abs_pos : 0 < |μ| := abs_pos.mpr hμ_ne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt h_abs_pos
    refine Set.mem_iUnion.mpr ⟨n, hμ_eig, ?_⟩
    exact le_of_lt hn
  · rintro hμ_in_union
    obtain ⟨n, hμ_in_n⟩ := Set.mem_iUnion.mp hμ_in_union
    obtain ⟨hμ_eig, hμ_size⟩ := hμ_in_n
    refine ⟨?_, hμ_eig⟩
    have h_pos : (0 : ℝ) < 1 / (n + 1) := by positivity
    have h_abs_pos : 0 < |μ| := lt_of_lt_of_le h_pos hμ_size
    exact abs_pos.mp h_abs_pos

omit [NeZero (Module.finrank ℝ E)] in
theorem nonzeroResolventEigenvalue_pos
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    0 < μ.val := by
  obtain ⟨u, hu_mem, hu_ne⟩ := μ.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ resolventEigenspace (I := I) (M := M) g μ.val := hu_mem
  have h_nn : 0 ≤ μ.val :=
    resolvent_eigenvalue_nonneg (I := I) (M := M) g hu_in hu_ne
  have h_ne : μ.val ≠ 0 := μ.val_ne_zero
  exact lt_of_le_of_ne h_nn (Ne.symm h_ne)

omit [NeZero (Module.finrank ℝ E)] in
theorem nonzeroResolventEigenvalue_le_one
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    μ.val ≤ 1 := by
  obtain ⟨u, hu_mem, hu_ne⟩ := μ.hasEigenvalue.exists_hasEigenvector
  have hu_in : u ∈ resolventEigenspace (I := I) (M := M) g μ.val := hu_mem
  exact resolvent_eigenvalue_le_one (I := I) (M := M) g hu_in hu_ne

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacianEigenvalueOf_nonneg
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    0 ≤ laplacianEigenvalueOf μ.val := by
  unfold laplacianEigenvalueOf
  have h_pos : 0 < μ.val := nonzeroResolventEigenvalue_pos μ
  have h_le_one : μ.val ≤ 1 := nonzeroResolventEigenvalue_le_one μ
  have h_num_nn : 0 ≤ 1 - μ.val := by linarith
  exact div_nonneg h_num_nn h_pos.le

instance NonzeroResolventEigenvalue.instFiniteDimensional
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    FiniteDimensional ℝ
      (resolventEigenspace (I := I) (M := M) g μ.val) :=
  resolventEigenspace_finiteDim_of_eigenvalue_ne_zero (I := I) (M := M) g μ.val_ne_zero

noncomputable def resolventEigenspaceONB
    {g : SmoothRiemannianMetric I M}
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    OrthonormalBasis
      (Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val)))
      ℝ (resolventEigenspace (I := I) (M := M) g μ.val) :=
  stdOrthonormalBasis ℝ (resolventEigenspace (I := I) (M := M) g μ.val)

omit [NeZero (Module.finrank ℝ E)] in
theorem resolventEigenspace_orthogonalFamily_nonzero
    (g : SmoothRiemannianMetric I M) :
    OrthogonalFamily ℝ
      (fun μ : NonzeroResolventEigenvalue (I := I) (M := M) g =>
        ↥(resolventEigenspace (I := I) (M := M) g μ.val))
      (fun μ => (resolventEigenspace (I := I) (M := M) g μ.val).subtypeₗᵢ) := by
  have hSymm :
      ((resolventL2 (I := I) (M := M) g).toLinearMap).IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (resolventL2_isSelfAdjoint (I := I) (M := M) g)
  have h_full : OrthogonalFamily ℝ
      (fun μ : ℝ =>
        ↥(resolventEigenspace (I := I) (M := M) g μ))
      (fun μ => (resolventEigenspace (I := I) (M := M) g μ).subtypeₗᵢ) := by
    exact hSymm.orthogonalFamily_eigenspaces
  have h_inj : Function.Injective
      (fun μ : NonzeroResolventEigenvalue (I := I) (M := M) g => μ.val) :=
    fun μ ν h => Subtype.ext h
  exact h_full.comp h_inj

noncomputable def resolventEigenbasisVec
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  ((resolventEigenspaceONB i.1 i.2 :
    resolventEigenspace (I := I) (M := M) g i.1.val) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))

theorem resolventEigenbasisVec_mem
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    resolventEigenbasisVec (I := I) (M := M) g i ∈
      resolventEigenspace (I := I) (M := M) g i.1.val := by
  unfold resolventEigenbasisVec
  exact (resolventEigenspaceONB (I := I) (M := M) i.1 i.2).property

theorem resolventEigenbasisVec_orthonormal (g : SmoothRiemannianMetric I M) :
    Orthonormal ℝ
      (resolventEigenbasisVec (I := I) (M := M) g) := by
  have h_fam := resolventEigenspace_orthogonalFamily_nonzero (I := I) (M := M) g
  have h_each : ∀ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Orthonormal ℝ (resolventEigenspaceONB (I := I) (M := M) μ) :=
    fun μ => (resolventEigenspaceONB (I := I) (M := M) μ).orthonormal
  have h_sig := h_fam.orthonormal_sigma_orthonormal h_each
  convert h_sig using 1
  funext a
  rfl

private lemma span_resolventEigenbasisVec_le_iSup_eigenspace
    (g : SmoothRiemannianMetric I M) :
    Submodule.span ℝ (Set.range
        (resolventEigenbasisVec (I := I) (M := M) g)) ≤
      ⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        resolventEigenspace (I := I) (M := M) g μ.val := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  refine SetLike.mem_coe.mpr ?_
  refine Submodule.mem_iSup_of_mem i.1 ?_
  exact resolventEigenbasisVec_mem (I := I) (M := M) g i

private lemma resolventEigenspace_le_span_resolventEigenbasisVec
    (g : SmoothRiemannianMetric I M)
    (μ : NonzeroResolventEigenvalue (I := I) (M := M) g) :
    resolventEigenspace (I := I) (M := M) g μ.val ≤
      Submodule.span ℝ (Set.range
        (resolventEigenbasisVec (I := I) (M := M) g)) := by
  intro x hx
  set b := resolventEigenspaceONB (I := I) (M := M) μ
  have h_basis_span : Submodule.span ℝ
      (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)) →
        resolventEigenspace (I := I) (M := M) g μ.val)) = ⊤ :=
    b.toBasis.span_eq
  have h_subtype_apply : ((resolventEigenspace (I := I) (M := M) g μ.val).subtype '' Set.range b) =
      Set.range (fun k =>
        ((b k : resolventEigenspace (I := I) (M := M) g μ.val) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨k, hk⟩, hzy⟩
      exact ⟨k, by rw [← hzy, ← hk]; rfl⟩
    · rintro ⟨k, hk⟩
      exact ⟨b k, ⟨k, rfl⟩, hk⟩
  have h_in_basis_set : ∀ k : Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val)),
      ((b k : resolventEigenspace (I := I) (M := M) g μ.val) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) ∈
      Set.range (resolventEigenbasisVec (I := I) (M := M) g) := by
    intro k
    refine ⟨⟨μ, k⟩, ?_⟩
    rfl
  have h_subtype_subset : Set.range (fun k =>
      ((b k : resolventEigenspace (I := I) (M := M) g μ.val) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))) ⊆
      Set.range (resolventEigenbasisVec (I := I) (M := M) g) := by
    rintro y ⟨k, rfl⟩
    exact h_in_basis_set k
  have hx_subtype : x = (resolventEigenspace (I := I) (M := M) g μ.val).subtype ⟨x, hx⟩ := rfl
  have h_top_mem : (⟨x, hx⟩ : resolventEigenspace (I := I) (M := M) g μ.val) ∈
      Submodule.span ℝ (Set.range (b.toBasis :
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)) →
        resolventEigenspace (I := I) (M := M) g μ.val)) := by
    rw [h_basis_span]; trivial
  have h_after_map : x ∈ Submodule.map
        (resolventEigenspace (I := I) (M := M) g μ.val).subtype
        (Submodule.span ℝ (Set.range (b.toBasis :
          Fin (Module.finrank ℝ
            (resolventEigenspace (I := I) (M := M) g μ.val)) →
          resolventEigenspace (I := I) (M := M) g μ.val))) := by
    refine ⟨⟨x, hx⟩, h_top_mem, rfl⟩
  rw [Submodule.map_span] at h_after_map
  have h_eq_basis : ((b.toBasis :
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)) →
        resolventEigenspace (I := I) (M := M) g μ.val)) = (b : _ → _) := by
    funext k
    have := OrthonormalBasis.coe_toBasis b
    exact congr_fun this k
  rw [h_eq_basis] at h_after_map
  rw [h_subtype_apply] at h_after_map
  exact Submodule.span_mono h_subtype_subset h_after_map

theorem span_resolventEigenbasisVec_eq_iSup_eigenspace
    (g : SmoothRiemannianMetric I M) :
    Submodule.span ℝ (Set.range
        (resolventEigenbasisVec (I := I) (M := M) g)) =
      ⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        resolventEigenspace (I := I) (M := M) g μ.val := by
  refine le_antisymm
    (span_resolventEigenbasisVec_le_iSup_eigenspace (I := I) (M := M) g) ?_
  exact iSup_le (resolventEigenspace_le_span_resolventEigenbasisVec
    (I := I) (M := M) g)

theorem nonzero_iSup_resolventEigenspace_orthogonal_eq_bot
    (g : SmoothRiemannianMetric I M) :
    (⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        resolventEigenspace (I := I) (M := M) g μ.val)ᗮ = ⊥ := by
  suffices h_iSup_eq :
      (⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        resolventEigenspace (I := I) (M := M) g μ.val) =
      (⨆ μ : ℝ, resolventEigenspace (I := I) (M := M) g μ) by
    rw [h_iSup_eq]
    exact resolventEigenspaces_iSup_orthogonal_eq_bot_on_closed
      (I := I) (M := M) g
  refine le_antisymm ?_ ?_
  · refine iSup_le (fun μ => ?_)
    exact le_iSup (fun ν : ℝ => resolventEigenspace (I := I) (M := M) g ν) μ.val
  · refine iSup_le (fun ν => ?_)
    by_cases hν : ν = 0
    · rw [hν, resolventEigenspace_zero_eq_bot (I := I) (M := M) g]
      exact bot_le
    · by_cases h_eig_bot : resolventEigenspace (I := I) (M := M) g ν = ⊥
      · rw [h_eig_bot]; exact bot_le
      · have h_ev : Module.End.HasEigenvalue
            ((resolventL2 (I := I) (M := M) g).toLinearMap) ν := by
          unfold resolventEigenspace at h_eig_bot
          exact h_eig_bot
        let hν_in_subtype : NonzeroResolventEigenvalue (I := I) (M := M) g :=
          ⟨ν, hν, h_ev⟩
        have hval : hν_in_subtype.val = ν := rfl
        calc resolventEigenspace (I := I) (M := M) g ν
            = resolventEigenspace (I := I) (M := M) g hν_in_subtype.val := by rw [hval]
          _ ≤ ⨆ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
                resolventEigenspace (I := I) (M := M) g μ.val :=
              le_iSup
                (fun μ : NonzeroResolventEigenvalue (I := I) (M := M) g =>
                  resolventEigenspace (I := I) (M := M) g μ.val) hν_in_subtype

theorem span_resolventEigenbasisVec_orthogonal_eq_bot
    (g : SmoothRiemannianMetric I M) :
    (Submodule.span ℝ (Set.range
        (resolventEigenbasisVec (I := I) (M := M) g)))ᗮ = ⊥ := by
  rw [span_resolventEigenbasisVec_eq_iSup_eigenspace]
  exact nonzero_iSup_resolventEigenspace_orthogonal_eq_bot (I := I) (M := M) g

noncomputable def resolventHilbertEigenbasisSigma
    (g : SmoothRiemannianMetric I M) :
    HilbertBasis
      (Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)))
      ℝ (Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (resolventEigenbasisVec_orthonormal (I := I) (M := M) g)
    (span_resolventEigenbasisVec_orthogonal_eq_bot (I := I) (M := M) g)

@[simp] lemma resolventHilbertEigenbasisSigma_apply
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    resolventHilbertEigenbasisSigma (I := I) (M := M) g i =
      resolventEigenbasisVec (I := I) (M := M) g i := by
  unfold resolventHilbertEigenbasisSigma
  exact congr_fun
    (HilbertBasis.coe_mkOfOrthogonalEqBot
      (resolventEigenbasisVec_orthonormal (I := I) (M := M) g)
      (span_resolventEigenbasisVec_orthogonal_eq_bot (I := I) (M := M) g))
    i

noncomputable def resolventEigenbasisSigma
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  resolventHilbertEigenbasisSigma (I := I) (M := M) g i

@[simp] lemma resolventEigenbasisSigma_eq_resolventEigenbasisVec
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    resolventEigenbasisSigma (I := I) (M := M) g i =
      resolventEigenbasisVec (I := I) (M := M) g i := by
  unfold resolventEigenbasisSigma
  exact resolventHilbertEigenbasisSigma_apply (I := I) (M := M) g i

theorem resolventL2_apply_resolventEigenbasisSigma
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    resolventL2 (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i) =
      i.1.val • resolventEigenbasisSigma (I := I) (M := M) g i := by
  rw [resolventEigenbasisSigma_eq_resolventEigenbasisVec]
  have h_mem : resolventEigenbasisVec (I := I) (M := M) g i ∈
      resolventEigenspace (I := I) (M := M) g i.1.val :=
    resolventEigenbasisVec_mem (I := I) (M := M) g i
  exact (mem_resolventEigenspace_iff (I := I) (M := M) g i.1.val
    (resolventEigenbasisVec (I := I) (M := M) g i)).mp h_mem

noncomputable def laplacianEigenfunction
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    laplacianDomain (I := I) (M := M) g := by
  refine ⟨(i.1.val)⁻¹ • resolvent (I := I) (M := M) g
      (resolventEigenbasisSigma (I := I) (M := M) g i), ?_⟩
  rw [laplacianDomain_mem_iff]
  refine ⟨(i.1.val)⁻¹ • resolventEigenbasisSigma (I := I) (M := M) g i, ?_⟩
  rw [(resolvent (I := I) (M := M) g).map_smul]

theorem H1ComplToLp_laplacianEigenfunction
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    H1ComplToLp (I := I) (M := M) g
        (laplacianEigenfunction (I := I) (M := M) g i :
          H1Compl (I := I) (M := M) g) =
      resolventEigenbasisSigma (I := I) (M := M) g i := by
  have hRb : resolventL2 (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i) =
      i.1.val • resolventEigenbasisSigma (I := I) (M := M) g i :=
    resolventL2_apply_resolventEigenbasisSigma (I := I) (M := M) g i
  have h_replace : H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (resolventEigenbasisSigma (I := I) (M := M) g i)) =
      resolventL2 (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i) := by
    rw [resolventL2_apply]
  change H1ComplToLp (I := I) (M := M) g
      ((i.1.val)⁻¹ • resolvent (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i)) =
    resolventEigenbasisSigma (I := I) (M := M) g i
  rw [(H1ComplToLp (I := I) (M := M) g).map_smul]
  rw [h_replace, hRb, smul_smul, inv_mul_cancel₀ i.1.val_ne_zero, one_smul]

theorem laplacianOp_laplacianEigenfunction
    (g : SmoothRiemannianMetric I M)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    laplacianOp (I := I) (M := M) g
        (laplacianEigenfunction (I := I) (M := M) g i) =
      -(laplacianEigenvalueOf i.1.val) •
        resolventEigenbasisSigma (I := I) (M := M) g i := by
  have h_mem : resolventEigenbasisSigma (I := I) (M := M) g i ∈
      resolventEigenspace (I := I) (M := M) g i.1.val := by
    rw [resolventEigenbasisSigma_eq_resolventEigenbasisVec]
    exact resolventEigenbasisVec_mem (I := I) (M := M) g i
  have h := laplacianOp_of_resolventEigenvector_lift (I := I) (M := M) g
    i.1.val_ne_zero h_mem
  have h_subtype_eq :
      (laplacianEigenfunction (I := I) (M := M) g i :
        laplacianDomain (I := I) (M := M) g) =
      ⟨(i.1.val)⁻¹ • resolvent (I := I) (M := M) g
          (resolventEigenbasisSigma (I := I) (M := M) g i),
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr
          ⟨(i.1.val)⁻¹ • resolventEigenbasisSigma (I := I) (M := M) g i, by
            rw [(resolvent (I := I) (M := M) g).map_smul]⟩⟩ := by
    apply Subtype.ext
    rfl
  rw [h_subtype_eq]
  exact h

theorem laplacianOp_inner_eigenbasis
    (g : SmoothRiemannianMetric I M)
    (u_h : laplacianDomain (I := I) (M := M) g)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ
        (resolventEigenspace (I := I) (M := M) g μ.val))) :
    ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
      laplacianOp (I := I) (M := M) g u_h⟫_ℝ =
      -(laplacianEigenvalueOf i.1.val) *
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
          H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g)⟫_ℝ := by
  have h := laplacianOp_symmetric (I := I) (M := M) g
    (laplacianEigenfunction (I := I) (M := M) g i) u_h
  rw [H1ComplToLp_laplacianEigenfunction,
    laplacianOp_laplacianEigenfunction, real_inner_smul_left] at h
  exact h

theorem exists_laplacianDomain_lift_iff_inner_eigenbasis
    {g : SmoothRiemannianMetric I M}
    {u w : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)} :
    (∃ u_h : laplacianDomain (I := I) (M := M) g,
      H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) = u ∧
        laplacianOp (I := I) (M := M) g u_h = w) ↔
      ∀ i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
        Fin (Module.finrank ℝ
          (resolventEigenspace (I := I) (M := M) g μ.val)),
        ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, w⟫_ℝ =
          -(laplacianEigenvalueOf i.1.val) *
            ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i, u⟫_ℝ := by
  constructor
  · rintro ⟨u_h, hu_h, hw⟩ i
    rw [← hu_h, ← hw]
    exact laplacianOp_inner_eigenbasis (I := I) (M := M) g u_h i
  · intro hcoeff
    let z := u - w
    let u_h : laplacianDomain (I := I) (M := M) g :=
      ⟨resolvent (I := I) (M := M) g z,
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨z, rfl⟩⟩
    have hu_h : H1ComplToLp (I := I) (M := M) g (u_h : H1Compl g) = u := by
      set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g
      apply b.repr.injective
      ext i
      rw [b.repr_apply_apply, b.repr_apply_apply]
      change ⟪b i, H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g z)⟫_ℝ = ⟪b i, u⟫_ℝ
      rw [← resolventL2_apply]
      have hself := resolventL2_isSelfAdjoint (I := I) (M := M) g
      have hsym : (resolventL2 (I := I) (M := M) g).IsSymmetric :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hself
      have hswap : ⟪b i, resolventL2 (I := I) (M := M) g z⟫_ℝ =
          ⟪resolventL2 (I := I) (M := M) g (b i), z⟫_ℝ :=
        (hsym.apply_clm (b i) z).symm
      rw [hswap]
      change ⟪resolventL2 (I := I) (M := M) g
        (resolventEigenbasisSigma (I := I) (M := M) g i), z⟫_ℝ = ⟪b i, u⟫_ℝ
      rw [resolventL2_apply_resolventEigenbasisSigma,
        real_inner_smul_left]
      change i.1.val * ⟪b i, u - w⟫_ℝ = ⟪b i, u⟫_ℝ
      rw [inner_sub_right, hcoeff]
      have hmul : i.1.val * (1 + laplacianEigenvalueOf i.1.val) = 1 := by
        unfold laplacianEigenvalueOf
        field_simp [i.1.val_ne_zero]
        ring
      calc
        i.1.val * (⟪b i, u⟫_ℝ -
            (-(laplacianEigenvalueOf i.1.val) * ⟪b i, u⟫_ℝ)) =
            (i.1.val * (1 + laplacianEigenvalueOf i.1.val)) * ⟪b i, u⟫_ℝ := by ring
        _ = ⟪b i, u⟫_ℝ := by rw [hmul, one_mul]
    refine ⟨u_h, hu_h, ?_⟩
    change laplacianOp (I := I) (M := M) g
      ⟨resolvent (I := I) (M := M) g z,
        (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨z, rfl⟩⟩ = w
    rw [laplacianOp_resolvent, hu_h]
    change u - (u - w) = w
    abel

end Laplacian
end CalabiYau

end
