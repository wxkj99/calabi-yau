module

public import CalabiYau.Mathlib.Analysis.Holder.Basic
public import CalabiYau.Mathlib.Geometry.Manifold.Holder

@[expose] public section

open scoped ENNReal NNReal BigOperators

namespace CalabiYau.Schauder

private def coordinateJet {V W F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : V ≃ₗᵢ[ℝ] W) (j : ℕ) (A : V → V [×j]→L[ℝ] F) :
    W → W [×j]→L[ℝ] F :=
  fun y => (A (e.symm y)).compContinuousLinearMap (fun _ => e.symm)

private theorem iteratedFDeriv_comp_coordinate
    {V W F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : V ≃ₗᵢ[ℝ] W) (j : ℕ) (f : V → F) (y : W) :
    iteratedFDeriv ℝ j (f ∘ e.symm) y =
      coordinateJet e j (iteratedFDeriv ℝ j f) y := by
  simp only [← iteratedFDerivWithin_univ]
  simpa [coordinateJet, Set.preimage_univ] using
    (e.symm.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right
      (s := Set.univ) f uniqueDiffOn_univ (x := y) (by simp) j)

private theorem iteratedFDeriv_comp_coordinate_fun
    {V W F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : V ≃ₗᵢ[ℝ] W) (j : ℕ) (f : V → F) :
    iteratedFDeriv ℝ j (f ∘ e.symm) = coordinateJet e j (iteratedFDeriv ℝ j f) := by
  funext y
  exact iteratedFDeriv_comp_coordinate e j f y

private theorem edist_coordinateJet_eq
    {V W F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : V ≃ₗᵢ[ℝ] W) (j : ℕ) (A B : V → V [×j]→L[ℝ] F) (y z : W) :
    edist (coordinateJet e j A y) (coordinateJet e j B z) =
      edist (A (e.symm y)) (B (e.symm z)) := by
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
  have hsub :
      coordinateJet e j A y - coordinateJet e j B z =
        (A (e.symm y) - B (e.symm z)).compContinuousLinearMap
          (fun _ => e.symm) := by
    ext v
    simp [coordinateJet, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hsub, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]

private theorem holderWithOn_coordinateJet_iff
    {V W F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {C α : ℝ≥0} (e : V ≃ₗᵢ[ℝ] W) (s : Set V) (j : ℕ)
    (A : V → V [×j]→L[ℝ] F) :
    HolderWith C α (s.domRestrict A) ↔
      HolderWith C α ((e '' s).domRestrict (coordinateJet e j A)) := by
  rw [HolderWith.restrict_iff, HolderWith.restrict_iff]
  constructor
  · intro h y hy z hz
    have hy' : e.symm y ∈ s := by
      rcases hy with ⟨x, hx, hxy⟩
      rw [← hxy, e.symm_apply_apply]
      exact hx
    have hz' : e.symm z ∈ s := by
      rcases hz with ⟨x, hx, hxz⟩
      rw [← hxz, e.symm_apply_apply]
      exact hx
    calc
      edist (coordinateJet e j A y) (coordinateJet e j A z) =
          edist (A (e.symm y)) (A (e.symm z)) :=
        edist_coordinateJet_eq e j A A y z
      _ ≤ (C : ℝ≥0∞) * edist (e.symm y) (e.symm z) ^ (α : ℝ) := h _ hy' _ hz'
      _ = (C : ℝ≥0∞) * edist y z ^ (α : ℝ) := by
        rw [e.symm.edist_map y z]
  · intro h x hx y hy
    calc
      edist (A x) (A y) = edist (coordinateJet e j A (e x))
          (coordinateJet e j A (e y)) := by
        rw [edist_coordinateJet_eq]
        simp
      _ ≤ (C : ℝ≥0∞) * edist (e x) (e y) ^ (α : ℝ) :=
        h (e x) (Set.mem_image_of_mem e hx) (e y) (Set.mem_image_of_mem e hy)
      _ = (C : ℝ≥0∞) * edist x y ^ (α : ℝ) := by
        rw [e.edist_map x y]

/-- `HolderBoundOn` transfers with the same constant across an explicit real-linear isometry of
complex and real coordinate spaces. -/
theorem holderBoundOn_coordinate_iff
    {n k : ℕ} {α C : ℝ≥0} (e :
      EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin 2))
    (s : Set (EuclideanSpace ℂ (Fin n)))
    (f : EuclideanSpace ℂ (Fin n) → ℝ) :
    HolderBoundOn k α C s f ↔
      HolderBoundOn k α C (e '' s) (f ∘ e.symm) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hjnorm :=
        (e.symm).norm_iteratedFDeriv_comp_right f (e x) j
      rw [hjnorm]
      simpa using h.1 j hj x hx
    · have hsource := HolderWith.restrict_iff.mpr h.2
      have hcoord := (holderWithOn_coordinateJet_iff (e := e) (s := s) (j := k)
        (A := iteratedFDeriv ℝ k f) (C := C) (α := α)).mp hsource
      have hjet := iteratedFDeriv_comp_coordinate_fun e k f
      have htarget : HolderWith C α
          ((e '' s).domRestrict (iteratedFDeriv ℝ k (f ∘ e.symm))) := by
        rw [hjet]
        exact hcoord
      exact HolderWith.restrict_iff.mp htarget
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj x hx
      have hcoord := h.1 j hj (e x) (Set.mem_image_of_mem e hx)
      have hjnorm := (e.symm).norm_iteratedFDeriv_comp_right f (e x) j
      calc
        ‖iteratedFDeriv ℝ j f x‖ =
            ‖iteratedFDeriv ℝ j (f ∘ e.symm) (e x)‖ := by
          rw [hjnorm, e.symm_apply_apply]
        _ ≤ C := by simpa using hcoord
    · have htarget := HolderWith.restrict_iff.mpr h.2
      have hjet := iteratedFDeriv_comp_coordinate_fun e k f
      rw [hjet] at htarget
      exact HolderWith.restrict_iff.mp
        ((holderWithOn_coordinateJet_iff (e := e) (s := s) (j := k)
          (A := iteratedFDeriv ℝ k f) (C := C) (α := α)).mpr htarget)

end CalabiYau.Schauder
