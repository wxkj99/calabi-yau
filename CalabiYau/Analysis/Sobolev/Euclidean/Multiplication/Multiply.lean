-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/Multiplication/Multiply.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below..

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

lemma norm_iteratedFDeriv_partial_le
    {η : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (i : Fin d) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y : E => (fderiv ℝ η y) (EuclideanSpace.single i 1)) x‖ ≤
      ‖iteratedFDeriv ℝ (j + 1) η x‖ := by
  have hη_succ : ContDiff ℝ ((j + 1 : ℕ) : ℕ∞) η := by
    refine hη.of_le ?_
    exact_mod_cast (le_top : ((j + 1 : ℕ) : ℕ∞) ≤ ⊤)
  have hf : ContDiff ℝ ((j : ℕ) : ℕ∞) (fderiv ℝ η) := by
    refine hη_succ.fderiv_right (m := ((j : ℕ) : ℕ∞)) ?_
    push_cast; exact le_refl _
  have h1 : ‖iteratedFDeriv ℝ j (fun y : E => (fderiv ℝ η y) (EuclideanSpace.single i 1)) x‖
      ≤ ‖(EuclideanSpace.single i (1 : ℝ))‖ *
          ‖iteratedFDeriv ℝ j (fderiv ℝ η) x‖ := by
    refine norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ η)
      (c := EuclideanSpace.single i (1 : ℝ)) (n := j)
      (x := x) hf.contDiffAt ?_
    exact le_refl _
  have h2 : ‖iteratedFDeriv ℝ j (fderiv ℝ η) x‖ = ‖iteratedFDeriv ℝ (j + 1) η x‖ :=
    norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := η) (n := j) (x := x)
  calc
    ‖iteratedFDeriv ℝ j (fun y : E => (fderiv ℝ η y) (EuclideanSpace.single i 1)) x‖
        ≤ ‖(EuclideanSpace.single i (1 : ℝ))‖ *
            ‖iteratedFDeriv ℝ j (fderiv ℝ η) x‖ := h1
    _ = 1 * ‖iteratedFDeriv ℝ (j + 1) η x‖ := by
          rw [h2]
          congr 1
          simp
    _ = ‖iteratedFDeriv ℝ (j + 1) η x‖ := one_mul _

lemma contDiff_partial_eta
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : E => (fderiv ℝ η x) (EuclideanSpace.single i 1)) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η := by
    simpa using hη
  have hfd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ η) := by
    refine h.fderiv_right (m := (⊤ : ℕ∞)) ?_
    simp
  have hfd' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ η) := by
    simpa using hfd
  exact hfd'.clm_apply contDiff_const

theorem MemW1p.mulSmoothBounded
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {η u : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound : ∀ x ∈ Ω, ‖η x‖ ≤ C)
    (hη_grad_bound : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C)
    (hu : DeGiorgi.MemW1p (d := d) p u Ω) :
    DeGiorgi.MemW1p (d := d) p (fun x => η x * u x) Ω := by
  classical
  refine ⟨?_, ?_⟩
  · refine MemLp.of_le_mul (g := u) (c := C) hu.1 ?_ ?_
    · exact hη.continuous.aestronglyMeasurable.mul hu.1.aestronglyMeasurable
    · refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
      exact Filter.Eventually.of_forall fun x hx => by
        calc
          ‖η x * u x‖ = ‖η x‖ * ‖u x‖ := norm_mul _ _
          _ ≤ C * ‖u x‖ := by
                gcongr
                exact hη_bound x hx
  · intro i
    obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 i
    refine ⟨fun x => η x * g x + (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x, ?_, ?_⟩
    · have h1 : MemLp (fun x => η x * g x) p (volume.restrict Ω) := by
        refine MemLp.of_le_mul (g := g) (c := C) hg_memLp ?_ ?_
        · exact hη.continuous.aestronglyMeasurable.mul hg_memLp.aestronglyMeasurable
        · refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
          exact Filter.Eventually.of_forall fun x hx => by
            calc
              ‖η x * g x‖ = ‖η x‖ * ‖g x‖ := norm_mul _ _
              _ ≤ C * ‖g x‖ := by
                    gcongr
                    exact hη_bound x hx
      have hderiv_cont :
          Continuous (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) :=
        (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const
      have h2 : MemLp (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x)
          p (volume.restrict Ω) := by
        refine MemLp.of_le_mul (g := u) (c := C) hu.1 ?_ ?_
        · exact hderiv_cont.aestronglyMeasurable.mul hu.1.aestronglyMeasurable
        · refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
          exact Filter.Eventually.of_forall fun x hx => by
            calc
              ‖(fderiv ℝ η x) (EuclideanSpace.single i 1) * u x‖
                  = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖u x‖ := norm_mul _ _
              _ ≤ ‖fderiv ℝ η x‖ * ‖u x‖ := by
                    gcongr
                    exact ContinuousLinearMap.le_opNorm _ _ |>.trans (by
                      rw [show ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 by simp,
                          mul_one])
              _ ≤ C * ‖u x‖ := by
                    gcongr
                    exact hη_grad_bound x hx
      exact MemLp.ae_eq (Filter.Eventually.of_forall fun _ ↦ rfl) (h1.add h2)
    · have hu_local : LocallyIntegrable u (volume.restrict Ω) :=
        hu.1.locallyIntegrable hp
      have hg_local : LocallyIntegrable g (volume.restrict Ω) :=
        hg_memLp.locallyIntegrable hp
      exact DeGiorgi.HasWeakPartialDeriv.mul_smooth hΩ hg_weak hη hu_local hg_local

theorem chosenWeakPartialOrZero_smul_smooth_bounded_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {η u : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound : ∀ x ∈ Ω, ‖η x‖ ≤ C)
    (hη_grad_bound : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C)
    (hu : DeGiorgi.MemW1p (d := d) p u Ω) (i : Fin d) :
    chosenWeakPartialOrZero (d := d) p i (fun x => η x * u x) Ω
      =ᵐ[volume.restrict Ω]
      (fun x => η x * chosenWeakPartialOrZero (d := d) p i u Ω x +
        (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) := by
  classical
  have hηu : DeGiorgi.MemW1p (d := d) p (fun x => η x * u x) Ω :=
    MemW1p.mulSmoothBounded (d := d) hp hΩ hη hη_bound hη_grad_bound hu
  have hLHS : DeGiorgi.HasWeakPartialDeriv (d := d) i
      (chosenWeakPartialOrZero p i (fun x => η x * u x) Ω) (fun x => η x * u x) Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hηu i
  have hu_local : LocallyIntegrable u (volume.restrict Ω) :=
    hu.1.locallyIntegrable hp
  have hcwp_local : LocallyIntegrable (chosenWeakPartialOrZero p i u Ω) (volume.restrict Ω) :=
    (chosenWeakPartialOrZero_memLp_of_mem hu i).locallyIntegrable hp
  have hcwp_weak : DeGiorgi.HasWeakPartialDeriv (d := d) i
      (chosenWeakPartialOrZero p i u Ω) u Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hu i
  have hRHS : DeGiorgi.HasWeakPartialDeriv (d := d) i
      (fun x => η x * chosenWeakPartialOrZero p i u Ω x +
        (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x)
      (fun x => η x * u x) Ω :=
    DeGiorgi.HasWeakPartialDeriv.mul_smooth hΩ hcwp_weak hη hu_local hcwp_local
  have hLHS_local : LocallyIntegrable
      (chosenWeakPartialOrZero p i (fun x => η x * u x) Ω) (volume.restrict Ω) :=
    (chosenWeakPartialOrZero_memLp_of_mem hηu i).locallyIntegrable hp
  have hηcwp_memLp :
      MemLp (fun x => η x * chosenWeakPartialOrZero p i u Ω x) p (volume.restrict Ω) := by
    refine MemLp.of_le_mul (g := chosenWeakPartialOrZero p i u Ω) (c := C)
      (chosenWeakPartialOrZero_memLp_of_mem hu i) ?_ ?_
    · exact hη.continuous.aestronglyMeasurable.mul
        (chosenWeakPartialOrZero_memLp_of_mem hu i).aestronglyMeasurable
    · refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
      exact Filter.Eventually.of_forall fun x hx => by
        calc
          ‖η x * chosenWeakPartialOrZero p i u Ω x‖
              = ‖η x‖ * ‖chosenWeakPartialOrZero p i u Ω x‖ := norm_mul _ _
          _ ≤ C * ‖chosenWeakPartialOrZero p i u Ω x‖ := by
                gcongr
                exact hη_bound x hx
  have hderiv_cont :
      Continuous (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) :=
    (hη.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have hdηu_memLp :
      MemLp (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x)
        p (volume.restrict Ω) := by
    refine MemLp.of_le_mul (g := u) (c := C) hu.1 ?_ ?_
    · exact hderiv_cont.aestronglyMeasurable.mul hu.1.aestronglyMeasurable
    · refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
      exact Filter.Eventually.of_forall fun x hx => by
        calc
          ‖(fderiv ℝ η x) (EuclideanSpace.single i 1) * u x‖
              = ‖(fderiv ℝ η x) (EuclideanSpace.single i 1)‖ * ‖u x‖ := norm_mul _ _
          _ ≤ ‖fderiv ℝ η x‖ * ‖u x‖ := by
                gcongr
                exact ContinuousLinearMap.le_opNorm _ _ |>.trans (by
                  rw [show ‖(EuclideanSpace.single i (1 : ℝ))‖ = 1 by simp, mul_one])
          _ ≤ C * ‖u x‖ := by
                gcongr
                exact hη_grad_bound x hx
  have hRHS_local : LocallyIntegrable
      (fun x => η x * chosenWeakPartialOrZero p i u Ω x +
        (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) (volume.restrict Ω) :=
    (hηcwp_memLp.add hdηu_memLp).locallyIntegrable hp
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hLHS hRHS hLHS_local hRHS_local

theorem MemWkp.smul_smooth_bounded
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {η : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound : ∀ j ≤ k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j η x‖ ≤ C)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω) :
    MemWkp (d := d) k p (fun x => η x * u x) Ω := by
  induction k generalizing η u with
  | zero =>
      rw [MemWkp_zero] at hu ⊢
      have h0 : ∀ x ∈ Ω, ‖η x‖ ≤ C := by
        intro x hx
        have h := hη_bound 0 (le_refl 0) x hx
        rwa [norm_iteratedFDeriv_zero] at h
      refine MemLp.of_le_mul (g := u) (c := C) hu ?_ ?_
      · exact hη.continuous.aestronglyMeasurable.mul hu.aestronglyMeasurable
      · refine (ae_restrict_iff' hΩ.measurableSet).mpr ?_
        exact Filter.Eventually.of_forall fun x hx => by
          calc
            ‖η x * u x‖ = ‖η x‖ * ‖u x‖ := norm_mul _ _
            _ ≤ C * ‖u x‖ := by
                  gcongr
                  exact h0 x hx
  | succ k ih =>
      rw [MemWkp_succ] at hu ⊢
      have h0 : ∀ x ∈ Ω, ‖η x‖ ≤ C := by
        intro x hx
        have h := hη_bound 0 (Nat.zero_le _) x hx
        rwa [norm_iteratedFDeriv_zero] at h
      have h1 : ∀ x ∈ Ω, ‖fderiv ℝ η x‖ ≤ C := by
        intro x hx
        have h := hη_bound 1 (Nat.succ_le_succ (Nat.zero_le _)) x hx
        rwa [norm_iteratedFDeriv_one] at h
      refine ⟨MemW1p.mulSmoothBounded (d := d) hp hΩ hη h0 h1 hu.1, ?_⟩
      intro i
      have hae : chosenWeakPartialOrZero p i (fun x => η x * u x) Ω
          =ᵐ[volume.restrict Ω]
          (fun x => η x * chosenWeakPartialOrZero p i u Ω x +
            (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) :=
        chosenWeakPartialOrZero_smul_smooth_bounded_ae (d := d) hp hΩ hη h0 h1 hu.1 i
      have hRHS_in_Wk : MemWkp (d := d) k p
          (fun x => η x * chosenWeakPartialOrZero p i u Ω x +
            (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) Ω := by
        have hT1 : MemWkp (d := d) k p
            (fun x => η x * chosenWeakPartialOrZero p i u Ω x) Ω := by
          have hbnd : ∀ j ≤ k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j η x‖ ≤ C :=
            fun j hj x hx => hη_bound j (hj.trans (Nat.le_succ _)) x hx
          exact ih (η := η) hη hbnd (hu.2 i)
        have hT2 : MemWkp (d := d) k p
            (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1) * u x) Ω := by
          have h_inner_smooth : ContDiff ℝ (⊤ : ℕ∞)
              (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) :=
            contDiff_partial_eta (d := d) hη i
          have h_inner_bound : ∀ j ≤ k, ∀ x ∈ Ω,
              ‖iteratedFDeriv ℝ j
                (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) x‖ ≤ C := by
            intro j hj x hx
            calc
              ‖iteratedFDeriv ℝ j
                  (fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1)) x‖
                  ≤ ‖iteratedFDeriv ℝ (j + 1) η x‖ :=
                    norm_iteratedFDeriv_partial_le (d := d) hη i j x
              _ ≤ C := hη_bound (j + 1) (Nat.succ_le_succ hj) x hx
          have hu_succ : MemWkp (d := d) (k + 1) p u Ω := by
            rw [MemWkp_succ]; exact hu
          have hu_inner : MemWkp (d := d) k p u Ω := hu_succ.le_succ
          exact ih (η := fun x => (fderiv ℝ η x) (EuclideanSpace.single i 1))
            h_inner_smooth h_inner_bound hu_inner
        exact MemWkp.add (d := d) hp hΩ hT1 hT2
      exact (MemWkp_congr_ae (d := d) hp hΩ hae).mpr hRHS_in_Wk

theorem wkpNorm_smul_smooth_bounded_lt_top
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {η : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    {C : ℝ}
    (hη_bound : ∀ j ≤ k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j η x‖ ≤ C)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω) :
    iteratedWeakSobolevNorm (d := d) k p (fun x => η x * u x) Ω < (⊤ : ℝ≥0∞) :=
  wkpNorm_lt_top_of_memWkp
    (MemWkp.smul_smooth_bounded (d := d) k hp hΩ hη hη_bound hu)

end Euclidean
end Sobolev
