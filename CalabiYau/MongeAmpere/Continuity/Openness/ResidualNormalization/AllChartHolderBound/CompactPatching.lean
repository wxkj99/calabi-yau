module

public import CalabiYau.MongeAmpere.Continuity.Openness.HolderSpaces

/-!
# Patching finite local Hölder bounds on a compact set

A finite open refinement of compact patches provides one patch containing every sufficiently close
pair.  For pairs farther apart the uniform derivative bound gives the required Hölder estimate.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology

namespace KahlerForm

private theorem exists_finite_compact_patch_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ≥0} {K : Set E} {f : E → ℝ} {ι : Type*} [Fintype ι]
    (patch : ι → Set E) (hcover : K ⊆ ⋃ i, interior (patch i))
    (localBound : ∀ i, ∃ C : ℝ≥0, HolderBoundOn 2 α C (patch i) f) :
    ∃ C : ℝ≥0, ∀ j ≤ 2, ∀ z ∈ K, ‖iteratedFDeriv ℝ j f z‖ ≤ C := by
  classical
  let c (i : ι) : ℝ≥0 := Classical.choose (localBound i)
  have hc (i : ι) : HolderBoundOn 2 α (c i) (patch i) f :=
    Classical.choose_spec (localBound i)
  let C : ℝ≥0 := ∑ i : ι, c i
  refine ⟨C, ?_⟩
  intro j hj z hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hz)
  have hzi : z ∈ patch i := interior_subset hi
  have hci : c i ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ c k)) (Finset.mem_univ i)
  have hb := (hc i).1 j hj z hzi
  exact hb.trans (by exact_mod_cast hci)

/-- A finite compact patch cover with local C²,α bounds gives one C²,α bound on the whole compact
set.  The interiors cover `K` so that close pairs lie in one patch; the compactness of `K` yields
a positive Lebesgue number, while the local zeroth-order bounds control far pairs. -/
theorem exists_holderBoundOn_of_finite_compact_patch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ≥0} {K : Set E} {f : E → ℝ} {ι : Type*} [Fintype ι]
    (hK : IsCompact K) (patch : ι → Set E)
    (hcover : K ⊆ ⋃ i, interior (patch i))
    (localBound : ∀ i, ∃ C : ℝ≥0, HolderBoundOn 2 α C (patch i) f) :
    ∃ C : ℝ≥0, HolderBoundOn 2 α C K f := by
  classical
  obtain ⟨D, hD⟩ := exists_finite_compact_patch_derivative_bound patch hcover localBound
  let c (i : ι) : ℝ≥0 := Classical.choose (localBound i)
  have hc (i : ι) : HolderBoundOn 2 α (c i) (patch i) f :=
    Classical.choose_spec (localBound i)
  let S : ℝ≥0 := ∑ i : ι, c i
  have hcs : ∀ i, c i ≤ S := by
    intro i
    dsimp [S]
    exact Finset.single_le_sum (fun k _ => (zero_le : 0 ≤ c k)) (Finset.mem_univ i)
  let C : ℝ≥0 := max D S
  have hC : ∀ j ≤ 2, ∀ z ∈ K, ‖iteratedFDeriv ℝ j f z‖ ≤ C := by
    intro j hj z hz
    exact (hD j hj z hz).trans (by exact_mod_cast (le_max_left D S))
  let U (i : ι) : Set E := interior (patch i)
  have hUopen (i : ι) : IsOpen (U i) := isOpen_interior
  have hUcover : K ⊆ ⋃ i : ι, U i := hcover
  have hlocal : ∀ i, HolderBoundOn 2 α C (U i) f := by
    intro i
    exact (hc i).mono_set interior_subset |>.mono_const (by
      exact_mod_cast (le_trans (hcs i) (le_max_right D S)))
  have hglobal : ∀ x ∈ K, ‖iteratedFDeriv ℝ 2 f x‖ ≤ C := fun x hx =>
    hC 2 (by omega) x hx
  obtain ⟨V, hV, hLebesgue⟩ := lebesgue_number_lemma hK hUopen hUcover
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_uniformity_dist.mp hV
  let δ : ℝ≥0 := Real.toNNReal (ε / 2)
  have hδpos : 0 < δ := Real.toNNReal_pos.mpr (by linarith)
  have hδeq : (δ : ℝ) = ε / 2 := by
    simp [δ, Real.coe_toNNReal (ε / 2) (by positivity : 0 ≤ ε / 2)]
  have hnear : ∀ x ∈ K, ∀ y ∈ K, nndist x y ≤ δ →
      ∃ i, x ∈ U i ∧ y ∈ U i := by
    intro x hx y hy hxy
    obtain ⟨i, hball⟩ := hLebesgue x hx
    have hdist : dist x y ≤ (δ : ℝ) := by exact_mod_cast hxy
    have hdistlt : dist x y < ε := by
      rw [hδeq] at hdist
      linarith
    have hyV : y ∈ UniformSpace.ball x V := by
      change (x, y) ∈ V
      exact hεV hdistlt
    exact ⟨i, hball (UniformSpace.mem_ball_self x hV), hball hyV⟩
  let Cfar : ℝ≥0 := (2 * C) / δ ^ (α : ℝ)
  let C' : ℝ≥0 := max C Cfar
  refine ⟨C', ?_⟩
  refine ⟨?_, ?_⟩
  · intro j hj x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hUcover hx)
    exact ((hlocal i).1 j hj x hxi).trans (by
      exact_mod_cast (le_max_left C Cfar))
  · intro x hx y hy
    by_cases hxy : nndist x y ≤ δ
    · obtain ⟨i, hxi, hyi⟩ := hnear x hx y hy hxy
      exact ((hlocal i).mono_const (le_max_left C Cfar)).2 x hxi y hyi
    · have hδle : δ ≤ nndist x y := le_of_not_ge hxy
      have hpowpos : 0 < δ ^ (α : ℝ) := NNReal.rpow_pos hδpos
      have hpowle : δ ^ (α : ℝ) ≤ nndist x y ^ (α : ℝ) :=
        NNReal.rpow_le_rpow hδle α.coe_nonneg
      have hfarCoeff : 2 * C ≤ Cfar * nndist x y ^ (α : ℝ) := by
        dsimp [Cfar]
        calc
          2 * C = ((2 * C) / δ ^ (α : ℝ)) * δ ^ (α : ℝ) := by field_simp
          _ ≤ ((2 * C) / δ ^ (α : ℝ)) * nndist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_left hpowle (by positivity)
      have hfarENN : (↑(2 * C) : ENNReal) ≤
          (↑Cfar : ENNReal) * edist x y ^ (α : ℝ) := by
        rw [edist_nndist, ← ENNReal.coe_rpow_of_nonneg (nndist x y) α.coe_nonneg,
          ← ENNReal.coe_mul]
        exact_mod_cast hfarCoeff
      have htopx : ‖iteratedFDeriv ℝ 2 f x‖ ≤ (C : ℝ) := hglobal x hx
      have htopy : ‖iteratedFDeriv ℝ 2 f y‖ ≤ (C : ℝ) := hglobal y hy
      calc
        edist (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y) =
            ENNReal.ofReal (dist (iteratedFDeriv ℝ 2 f x) (iteratedFDeriv ℝ 2 f y)) :=
          edist_dist _ _
        _ ≤ ENNReal.ofReal
            (‖iteratedFDeriv ℝ 2 f x‖ + ‖iteratedFDeriv ℝ 2 f y‖) :=
          ENNReal.ofReal_le_ofReal (dist_le_norm_add_norm _ _)
        _ ≤ ENNReal.ofReal ((C : ℝ) + C) :=
          ENNReal.ofReal_le_ofReal (add_le_add htopx htopy)
        _ = (↑(2 * C) : ENNReal) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          simp [two_mul]
        _ ≤ (↑Cfar : ENNReal) * edist x y ^ (α : ℝ) := hfarENN
        _ ≤ (↑C' : ENNReal) * edist x y ^ (α : ℝ) :=
          mul_le_mul_of_nonneg_right
            (ENNReal.coe_le_coe.mpr (le_max_right C Cfar)) (by positivity)

end KahlerForm
