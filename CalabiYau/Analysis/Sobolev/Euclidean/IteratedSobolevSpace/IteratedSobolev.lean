-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Euclidean/IteratedSobolevSpace/IteratedSobolev.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section

-- Private declarations used in public declarations require the compatibility option below..

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Sobolev
namespace Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

def chosenWeakPartialOrZero (p : ℝ≥0∞) (i : Fin d) (u : E → ℝ) (Ω : Set E) : E → ℝ := by
  classical
  exact
    if h : Sobolev.Euclidean.MemW1p p u Ω then
      fun x => (Sobolev.Euclidean.MemW1p.someWitness h).weakGrad x i
    else 0

theorem chosenWeakPartialOrZero_memLp_of_mem
    {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : Sobolev.Euclidean.MemW1p p u Ω) (i : Fin d) :
    MemLp (chosenWeakPartialOrZero p i u Ω) p (volume.restrict Ω) := by
  classical
  unfold chosenWeakPartialOrZero
  simp only [dite_eq_left h]
  exact (Sobolev.Euclidean.MemW1p.someWitness h).weakGrad_component_memLp i

theorem chosenWeakPartialOrZero_isWeakPartial_of_mem
    {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : Sobolev.Euclidean.MemW1p p u Ω) (i : Fin d) :
    Sobolev.Euclidean.HasWeakPartialDeriv i (chosenWeakPartialOrZero p i u Ω) u Ω := by
  classical
  unfold chosenWeakPartialOrZero
  simp only [dite_eq_left h]
  exact (Sobolev.Euclidean.MemW1p.someWitness h).isWeakGrad i

theorem chosenWeakPartialOrZero_of_not_mem
    {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : ¬ Sobolev.Euclidean.MemW1p p u Ω) (i : Fin d) :
    chosenWeakPartialOrZero p i u Ω = 0 := by
  classical
  unfold chosenWeakPartialOrZero
  simp only [dite_eq_right h]

def MemWkp : ℕ → ℝ≥0∞ → (E → ℝ) → Set E → Prop
  | 0,     p, u, Ω => MemLp u p (volume.restrict Ω)
  | k + 1, p, u, Ω =>
      Sobolev.Euclidean.MemW1p p u Ω ∧ ∀ i : Fin d, MemWkp k p (chosenWeakPartialOrZero p i u Ω) Ω

@[simp] lemma MemWkp_zero (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    MemWkp (d := d) 0 p u Ω ↔ MemLp u p (volume.restrict Ω) := Iff.rfl

@[simp] lemma MemWkp_succ (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    MemWkp (d := d) (k + 1) p u Ω ↔
      Sobolev.Euclidean.MemW1p p u Ω ∧
        ∀ i : Fin d, MemWkp (d := d) k p (chosenWeakPartialOrZero p i u Ω) Ω := Iff.rfl

theorem MemWkp.one_iff_memW1p
    {p : ℝ≥0∞} {u : E → ℝ} {Ω : Set E} :
    MemWkp (d := d) 1 p u Ω ↔ Sobolev.Euclidean.MemW1p p u Ω := by
  unfold MemWkp
  refine ⟨fun h => h.1, fun h => ⟨h, fun i => ?_⟩⟩
  exact chosenWeakPartialOrZero_memLp_of_mem h i

theorem MemWkp.memLp
    {k : ℕ} {p : ℝ≥0∞} {u : E → ℝ} {Ω : Set E}
    (h : MemWkp (d := d) k p u Ω) :
    MemLp u p (volume.restrict Ω) := by
  cases k with
  | zero => exact h
  | succ k =>
      rw [MemWkp_succ] at h
      exact h.1.1

theorem MemWkp.memW1p
    {k : ℕ} {p : ℝ≥0∞} {u : E → ℝ} {Ω : Set E}
    (h : MemWkp (d := d) (k + 1) p u Ω) :
    Sobolev.Euclidean.MemW1p p u Ω := by
  rw [MemWkp_succ] at h
  exact h.1

theorem MemWkp.chosenWeakPartial_mem
    {k : ℕ} {p : ℝ≥0∞} {u : E → ℝ} {Ω : Set E}
    (h : MemWkp (d := d) (k + 1) p u Ω) (i : Fin d) :
    MemWkp (d := d) k p (chosenWeakPartialOrZero p i u Ω) Ω := by
  rw [MemWkp_succ] at h
  exact h.2 i

theorem MemWkp.le_succ
    {k : ℕ} {p : ℝ≥0∞} {u : E → ℝ} {Ω : Set E}
    (h : MemWkp (d := d) (k + 1) p u Ω) :
    MemWkp (d := d) k p u Ω := by
  induction k generalizing u with
  | zero =>
      rw [MemWkp_zero]
      exact h.memLp
  | succ k ih =>
      rw [MemWkp_succ] at h ⊢
      refine ⟨h.1, fun i => ?_⟩
      exact ih (h.2 i)

theorem MemWkp.le_of_le
    {k k' : ℕ} {p : ℝ≥0∞} {u : E → ℝ} {Ω : Set E}
    (hk : k ≤ k') (h : MemWkp (d := d) k' p u Ω) :
    MemWkp (d := d) k p u Ω := by
  induction k', hk using Nat.le_induction with
  | base => exact h
  | succ k' _hk ih => exact ih h.le_succ

def iterWeakPartial (p : ℝ≥0∞) :
    ∀ (j : ℕ), (Fin j → Fin d) → (E → ℝ) → Set E → (E → ℝ)
  | 0,     _, u, _ => u
  | j + 1, α, u, Ω =>
      iterWeakPartial p j (fun i : Fin j => α i.succ)
        (chosenWeakPartialOrZero p (α 0) u Ω) Ω

@[simp] lemma iterWeakPartial_zero
    (p : ℝ≥0∞) (α : Fin 0 → Fin d) (u : E → ℝ) (Ω : Set E) :
    iterWeakPartial (d := d) p 0 α u Ω = u := rfl

lemma iterWeakPartial_succ
    (p : ℝ≥0∞) (j : ℕ) (α : Fin (j + 1) → Fin d)
    (u : E → ℝ) (Ω : Set E) :
    iterWeakPartial (d := d) p (j + 1) α u Ω =
      iterWeakPartial p j (fun i : Fin j => α i.succ)
        (chosenWeakPartialOrZero p (α 0) u Ω) Ω := rfl

theorem iterWeakPartial_memLp_of_memWkp
    {j : ℕ} {p : ℝ≥0∞} {u : E → ℝ} {Ω : Set E}
    (h : MemWkp (d := d) j p u Ω) (α : Fin j → Fin d) :
    MemLp (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω) := by
  induction j generalizing u with
  | zero =>
      simpa [iterWeakPartial_zero] using h
  | succ j ih =>
      rw [iterWeakPartial_succ]
      exact ih (h.chosenWeakPartial_mem (α 0)) (fun i : Fin j => α i.succ)

theorem hasWeakPartialDeriv_congr_ae
    {Ω : Set E} (i : Fin d) {g u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v)
    (h : Sobolev.Euclidean.HasWeakPartialDeriv i g u Ω) :
    Sobolev.Euclidean.HasWeakPartialDeriv i g v Ω := by
  intro φ hφ_smooth hφ_support hφ_sub
  have h_ae :
      (fun x : E => v x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        =ᵐ[volume.restrict Ω]
      (fun x : E => u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
    filter_upwards [huv.symm] with x hx
    simp [hx]
  rw [integral_congr_ae h_ae]
  exact h φ hφ_smooth hφ_support hφ_sub

theorem MemW1p_congr_ae
    {p : ℝ≥0∞} {Ω : Set E}
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict Ω] v) :
    Sobolev.Euclidean.MemW1p p u Ω ↔ Sobolev.Euclidean.MemW1p p v Ω := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨?_, ?_⟩
    · exact (memLp_congr_ae huv).mp h.1
    · intro i
      obtain ⟨g, hg_memLp, hg_weak⟩ := h.2 i
      exact ⟨g, hg_memLp, hasWeakPartialDeriv_congr_ae i huv hg_weak⟩
  · refine ⟨?_, ?_⟩
    · exact (memLp_congr_ae huv.symm).mp h.1
    · intro i
      obtain ⟨g, hg_memLp, hg_weak⟩ := h.2 i
      exact ⟨g, hg_memLp, hasWeakPartialDeriv_congr_ae i huv.symm hg_weak⟩

theorem chosenWeakPartialOrZero_ae_congr
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict Ω] v)
    (i : Fin d) :
    chosenWeakPartialOrZero p i u Ω =ᵐ[volume.restrict Ω] chosenWeakPartialOrZero p i v Ω := by
  classical
  by_cases hu : Sobolev.Euclidean.MemW1p p u Ω
  · have hv : Sobolev.Euclidean.MemW1p p v Ω := (MemW1p_congr_ae huv).mp hu
    have hPu := chosenWeakPartialOrZero_isWeakPartial_of_mem hu i
    have hPv := chosenWeakPartialOrZero_isWeakPartial_of_mem hv i
    have hPv_u : Sobolev.Euclidean.HasWeakPartialDeriv i (chosenWeakPartialOrZero p i v Ω) u Ω :=
      hasWeakPartialDeriv_congr_ae i huv.symm hPv
    have hLpu : LocallyIntegrable (chosenWeakPartialOrZero p i u Ω) (volume.restrict Ω) :=
      (chosenWeakPartialOrZero_memLp_of_mem hu i).locallyIntegrable hp
    have hLpv : LocallyIntegrable (chosenWeakPartialOrZero p i v Ω) (volume.restrict Ω) :=
      (chosenWeakPartialOrZero_memLp_of_mem hv i).locallyIntegrable hp
    exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ hPu hPv_u hLpu hLpv
  · have hv : ¬ Sobolev.Euclidean.MemW1p p v Ω := fun hv => hu ((MemW1p_congr_ae huv).mpr hv)
    rw [chosenWeakPartialOrZero_of_not_mem hu, chosenWeakPartialOrZero_of_not_mem hv]

theorem MemWkp_congr_ae
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict Ω] v) :
    MemWkp (d := d) k p u Ω ↔ MemWkp (d := d) k p v Ω := by
  induction k generalizing u v with
  | zero =>
      simp only [MemWkp_zero]
      exact memLp_congr_ae huv
  | succ k ih =>
      simp only [MemWkp_succ]
      refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
      · exact (MemW1p_congr_ae huv).mp h.1
      · intro i
        have hae := chosenWeakPartialOrZero_ae_congr (d := d) hp hΩ huv i
        exact (ih hae).mp (h.2 i)
      · exact (MemW1p_congr_ae huv).mpr h.1
      · intro i
        have hae := chosenWeakPartialOrZero_ae_congr (d := d) hp hΩ huv.symm i
        exact (ih hae).mp (h.2 i)

theorem chosenWeakPartialOrZero_ae_zero_of_ae_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu_ae : u =ᵐ[volume.restrict Ω] (fun _ => 0))
    (i : Fin d) :
    chosenWeakPartialOrZero p i u Ω =ᵐ[volume.restrict Ω] (fun _ : E => (0 : ℝ)) := by
  classical
  by_cases hW : Sobolev.Euclidean.MemW1p p u Ω
  · have h_zero_is_weak : Sobolev.Euclidean.HasWeakPartialDeriv i (fun _ : E => (0 : ℝ)) u Ω := by
      intro φ hφ hφ_support hφ_sub
      have h_ae_lhs :
          (fun x : E => u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
            =ᵐ[volume.restrict Ω]
          (fun x : E => 0 * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
        filter_upwards [hu_ae] with x hx
        simp [hx]
      have hLHS_zero :
          ∫ x in Ω, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) = 0 := by
        rw [integral_congr_ae h_ae_lhs]
        simp
      rw [hLHS_zero]
      simp
    have hPartial : Sobolev.Euclidean.HasWeakPartialDeriv i
        (chosenWeakPartialOrZero p i u Ω) u Ω :=
      chosenWeakPartialOrZero_isWeakPartial_of_mem hW i
    have hLp1 : LocallyIntegrable (chosenWeakPartialOrZero p i u Ω)
        (volume.restrict Ω) :=
      (chosenWeakPartialOrZero_memLp_of_mem hW i).locallyIntegrable hp
    have hLp2 : LocallyIntegrable (fun _ : E => (0 : ℝ)) (volume.restrict Ω) :=
      locallyIntegrable_const 0
    exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ hPartial h_zero_is_weak hLp1 hLp2
  · rw [chosenWeakPartialOrZero_of_not_mem hW]
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem iterWeakPartial_ae_zero_of_input_ae_zero
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (j : ℕ) (α : Fin j → Fin d) {u : E → ℝ}
    (hu : u =ᵐ[volume.restrict Ω] (fun _ => 0)) :
    iterWeakPartial (d := d) p j α u Ω =ᵐ[volume.restrict Ω]
      (fun _ : E => (0 : ℝ)) := by
  induction j generalizing u with
  | zero =>
      simpa [iterWeakPartial_zero] using hu
  | succ j ih =>
      rw [iterWeakPartial_succ]
      have h_chosen_ae : chosenWeakPartialOrZero p (α 0) u Ω
          =ᵐ[volume.restrict Ω] (fun _ : E => (0 : ℝ)) :=
        chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := d) hp hΩ hu (α 0)
      exact ih (fun i : Fin j => α i.succ) h_chosen_ae

theorem MemWkp_zero_fun
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω) :
    MemWkp (d := d) k p (fun _ : E => (0 : ℝ)) Ω := by
  classical
  induction k with
  | zero =>
      rw [MemWkp_zero]
      exact MemLp.zero
  | succ k ih =>
      rw [MemWkp_succ]
      refine ⟨?_, ?_⟩
      · refine ⟨MemLp.zero, ?_⟩
        intro i
        refine ⟨fun _ => (0 : ℝ), MemLp.zero, ?_⟩
        intro φ hφ hφ_support hφ_sub
        simp
      · intro i
        have hae : chosenWeakPartialOrZero p i (fun _ : E => (0 : ℝ)) Ω
            =ᵐ[volume.restrict Ω] (fun _ : E => (0 : ℝ)) :=
          chosenWeakPartialOrZero_ae_zero_of_ae_zero (d := d) hp hΩ
            (Filter.Eventually.of_forall (fun _ => rfl)) i
        exact (MemWkp_congr_ae (d := d) hp hΩ hae).mpr ih

theorem MemW1p.add
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    {u v : E → ℝ}
    (hu : Sobolev.Euclidean.MemW1p p u Ω) (hv : Sobolev.Euclidean.MemW1p p v Ω) :
    Sobolev.Euclidean.MemW1p p (fun x => u x + v x) Ω := by
  refine ⟨?_, ?_⟩
  · exact hu.1.add hv.1
  · intro i
    obtain ⟨gu, hgu_memLp, hgu_weak⟩ := hu.2 i
    obtain ⟨gv, hgv_memLp, hgv_weak⟩ := hv.2 i
    refine ⟨fun x => gu x + gv x, hgu_memLp.add hgv_memLp, ?_⟩
    intro φ hφ_smooth hφ_support hφ_sub
    have h_u_eq := hgu_weak φ hφ_smooth hφ_support hφ_sub
    have h_v_eq := hgv_weak φ hφ_smooth hφ_support hφ_sub
    have hu_int : Integrable
        (fun x => u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        (volume.restrict Ω) := by
      have hu_local : LocallyIntegrable u (volume.restrict Ω) :=
        hu.1.locallyIntegrable hp
      have hderiv_cont :
          Continuous (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        (hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const
      have hderiv_support : HasCompactSupport
          (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      simpa [smul_eq_mul] using
        hu_local.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_support
    have hv_int : Integrable
        (fun x => v x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        (volume.restrict Ω) := by
      have hv_local : LocallyIntegrable v (volume.restrict Ω) :=
        hv.1.locallyIntegrable hp
      have hderiv_cont :
          Continuous (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        (hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const
      have hderiv_support : HasCompactSupport
          (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      simpa [smul_eq_mul] using
        hv_local.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_support
    have hgu_int : Integrable (fun x => gu x * φ x) (volume.restrict Ω) := by
      have hgu_local : LocallyIntegrable gu (volume.restrict Ω) :=
        hgu_memLp.locallyIntegrable hp
      simpa [smul_eq_mul] using
        hgu_local.integrable_smul_right_of_hasCompactSupport hφ_smooth.continuous hφ_support
    have hgv_int : Integrable (fun x => gv x * φ x) (volume.restrict Ω) := by
      have hgv_local : LocallyIntegrable gv (volume.restrict Ω) :=
        hgv_memLp.locallyIntegrable hp
      simpa [smul_eq_mul] using
        hgv_local.integrable_smul_right_of_hasCompactSupport hφ_smooth.continuous hφ_support
    calc
      ∫ x in Ω, (u x + v x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1)
          = ∫ x in Ω,
              u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) +
              v x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
            congr 1; funext x; ring
      _ = (∫ x in Ω, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) +
            ∫ x in Ω, v x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) :=
            integral_add hu_int hv_int
      _ = (- ∫ x in Ω, gu x * φ x) + (- ∫ x in Ω, gv x * φ x) := by
            rw [h_u_eq, h_v_eq]
      _ = - ((∫ x in Ω, gu x * φ x) + (∫ x in Ω, gv x * φ x)) := by ring
      _ = - ∫ x in Ω, gu x * φ x + gv x * φ x := by
            rw [integral_add hgu_int hgv_int]
      _ = - ∫ x in Ω, (gu x + gv x) * φ x := by
            congr 1; congr 1; funext x; ring

theorem chosenWeakPartialOrZero_add_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ} (hu : Sobolev.Euclidean.MemW1p p u Ω) (hv : Sobolev.Euclidean.MemW1p p v Ω)
    (i : Fin d) :
    chosenWeakPartialOrZero p i (fun x => u x + v x) Ω
      =ᵐ[volume.restrict Ω]
      (fun x => chosenWeakPartialOrZero p i u Ω x + chosenWeakPartialOrZero p i v Ω x) := by
  classical
  have huv : Sobolev.Euclidean.MemW1p p (fun x => u x + v x) Ω :=
    MemW1p.add hp hu hv
  have hPartial_left : Sobolev.Euclidean.HasWeakPartialDeriv i
      (chosenWeakPartialOrZero p i (fun x => u x + v x) Ω) (fun x => u x + v x) Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem huv i
  have hPartial_right : Sobolev.Euclidean.HasWeakPartialDeriv i
      (fun x => chosenWeakPartialOrZero p i u Ω x + chosenWeakPartialOrZero p i v Ω x)
      (fun x => u x + v x) Ω := by
    intro φ hφ_smooth hφ_support hφ_sub
    have h_u_eq := chosenWeakPartialOrZero_isWeakPartial_of_mem hu i φ hφ_smooth hφ_support hφ_sub
    have h_v_eq := chosenWeakPartialOrZero_isWeakPartial_of_mem hv i φ hφ_smooth hφ_support hφ_sub
    have hu_int : Integrable
        (fun x => u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        (volume.restrict Ω) := by
      have hu_local : LocallyIntegrable u (volume.restrict Ω) :=
        hu.1.locallyIntegrable hp
      have hderiv_cont :
          Continuous (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        (hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const
      have hderiv_support : HasCompactSupport
          (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      simpa [smul_eq_mul] using
        hu_local.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_support
    have hv_int : Integrable
        (fun x => v x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        (volume.restrict Ω) := by
      have hv_local : LocallyIntegrable v (volume.restrict Ω) :=
        hv.1.locallyIntegrable hp
      have hderiv_cont :
          Continuous (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        (hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const
      have hderiv_support : HasCompactSupport
          (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      simpa [smul_eq_mul] using
        hv_local.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_support
    have hgu_int : Integrable (fun x => chosenWeakPartialOrZero p i u Ω x * φ x)
        (volume.restrict Ω) := by
      have hgu_local : LocallyIntegrable (chosenWeakPartialOrZero p i u Ω) (volume.restrict Ω) :=
        (chosenWeakPartialOrZero_memLp_of_mem hu i).locallyIntegrable hp
      simpa [smul_eq_mul] using
        hgu_local.integrable_smul_right_of_hasCompactSupport hφ_smooth.continuous hφ_support
    have hgv_int : Integrable (fun x => chosenWeakPartialOrZero p i v Ω x * φ x)
        (volume.restrict Ω) := by
      have hgv_local : LocallyIntegrable (chosenWeakPartialOrZero p i v Ω) (volume.restrict Ω) :=
        (chosenWeakPartialOrZero_memLp_of_mem hv i).locallyIntegrable hp
      simpa [smul_eq_mul] using
        hgv_local.integrable_smul_right_of_hasCompactSupport hφ_smooth.continuous hφ_support
    calc
      ∫ x in Ω, (u x + v x) * (fderiv ℝ φ x) (EuclideanSpace.single i 1)
          = ∫ x in Ω,
              u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) +
              v x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
            congr 1; funext x; ring
      _ = (∫ x in Ω, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) +
            ∫ x in Ω, v x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) :=
            integral_add hu_int hv_int
      _ = (- ∫ x in Ω, chosenWeakPartialOrZero p i u Ω x * φ x) +
            (- ∫ x in Ω, chosenWeakPartialOrZero p i v Ω x * φ x) := by
            rw [h_u_eq, h_v_eq]
      _ = - ((∫ x in Ω, chosenWeakPartialOrZero p i u Ω x * φ x) +
              (∫ x in Ω, chosenWeakPartialOrZero p i v Ω x * φ x)) := by ring
      _ = - ∫ x in Ω,
              chosenWeakPartialOrZero p i u Ω x * φ x +
              chosenWeakPartialOrZero p i v Ω x * φ x := by
            rw [integral_add hgu_int hgv_int]
      _ = - ∫ x in Ω,
              (chosenWeakPartialOrZero p i u Ω x + chosenWeakPartialOrZero p i v Ω x) * φ x := by
            congr 1; congr 1; funext x; ring
  have hLp_left : LocallyIntegrable (chosenWeakPartialOrZero p i (fun x => u x + v x) Ω)
      (volume.restrict Ω) :=
    (chosenWeakPartialOrZero_memLp_of_mem huv i).locallyIntegrable hp
  have hLp_right : LocallyIntegrable
      (fun x => chosenWeakPartialOrZero p i u Ω x + chosenWeakPartialOrZero p i v Ω x)
      (volume.restrict Ω) :=
    ((chosenWeakPartialOrZero_memLp_of_mem hu i).add
      (chosenWeakPartialOrZero_memLp_of_mem hv i)).locallyIntegrable hp
  exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ hPartial_left hPartial_right
    hLp_left hLp_right

theorem MemWkp.add
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ}
    (hu : MemWkp (d := d) k p u Ω) (hv : MemWkp (d := d) k p v Ω) :
    MemWkp (d := d) k p (fun x => u x + v x) Ω := by
  induction k generalizing u v with
  | zero =>
      rw [MemWkp_zero] at hu hv ⊢
      exact hu.add hv
  | succ k ih =>
      rw [MemWkp_succ] at hu hv ⊢
      refine ⟨MemW1p.add hp hu.1 hv.1, ?_⟩
      intro i
      have hae := chosenWeakPartialOrZero_add_ae (d := d) hp hΩ hu.1 hv.1 i
      have hSum : MemWkp (d := d) k p
          (fun x => chosenWeakPartialOrZero p i u Ω x + chosenWeakPartialOrZero p i v Ω x) Ω :=
        ih (hu.2 i) (hv.2 i)
      exact (MemWkp_congr_ae (d := d) hp hΩ hae).mpr hSum

theorem MemW1p.const_smul
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    {u : E → ℝ} (hu : Sobolev.Euclidean.MemW1p p u Ω) (c : ℝ) :
    Sobolev.Euclidean.MemW1p p (fun x => c * u x) Ω := by
  refine ⟨?_, ?_⟩
  · exact hu.1.const_mul c
  · intro i
    obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 i
    refine ⟨fun x => c * g x, hg_memLp.const_mul c, ?_⟩
    intro φ hφ_smooth hφ_support hφ_sub
    have h := hg_weak φ hφ_smooth hφ_support hφ_sub
    have hg_int : Integrable (fun x => g x * φ x) (volume.restrict Ω) := by
      have hg_local : LocallyIntegrable g (volume.restrict Ω) :=
        hg_memLp.locallyIntegrable hp
      simpa [smul_eq_mul] using
        hg_local.integrable_smul_right_of_hasCompactSupport hφ_smooth.continuous hφ_support
    have hu_int : Integrable
        (fun x => u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        (volume.restrict Ω) := by
      have hu_local : LocallyIntegrable u (volume.restrict Ω) :=
        hu.1.locallyIntegrable hp
      have hderiv_cont :
          Continuous (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        (hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const
      have hderiv_support : HasCompactSupport
          (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      simpa [smul_eq_mul] using
        hu_local.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_support
    calc
      ∫ x in Ω, c * u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)
          = ∫ x in Ω, c * (u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
            congr 1; funext x; ring
      _ = c * ∫ x in Ω, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
            rw [integral_const_mul]
      _ = c * (- ∫ x in Ω, g x * φ x) := by rw [h]
      _ = - (c * ∫ x in Ω, g x * φ x) := by ring
      _ = - ∫ x in Ω, c * (g x * φ x) := by rw [integral_const_mul]
      _ = - ∫ x in Ω, c * g x * φ x := by
            congr 1; congr 1; funext x; ring

theorem chosenWeakPartialOrZero_const_smul_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : Sobolev.Euclidean.MemW1p p u Ω) (c : ℝ) (i : Fin d) :
    chosenWeakPartialOrZero p i (fun x => c * u x) Ω
      =ᵐ[volume.restrict Ω] (fun x => c * chosenWeakPartialOrZero p i u Ω x) := by
  classical
  have hcu : Sobolev.Euclidean.MemW1p p (fun x => c * u x) Ω :=
    MemW1p.const_smul hp hu c
  have hPartial_left : Sobolev.Euclidean.HasWeakPartialDeriv i
      (chosenWeakPartialOrZero p i (fun x => c * u x) Ω) (fun x => c * u x) Ω :=
    chosenWeakPartialOrZero_isWeakPartial_of_mem hcu i
  have hPartial_right : Sobolev.Euclidean.HasWeakPartialDeriv i
      (fun x => c * chosenWeakPartialOrZero p i u Ω x) (fun x => c * u x) Ω := by
    intro φ hφ_smooth hφ_support hφ_sub
    have hu_eq := chosenWeakPartialOrZero_isWeakPartial_of_mem hu i φ hφ_smooth hφ_support hφ_sub
    have hg_int : Integrable (fun x => chosenWeakPartialOrZero p i u Ω x * φ x)
        (volume.restrict Ω) := by
      have hg_local : LocallyIntegrable (chosenWeakPartialOrZero p i u Ω) (volume.restrict Ω) :=
        (chosenWeakPartialOrZero_memLp_of_mem hu i).locallyIntegrable hp
      simpa [smul_eq_mul] using
        hg_local.integrable_smul_right_of_hasCompactSupport hφ_smooth.continuous hφ_support
    have hu_int : Integrable
        (fun x => u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
        (volume.restrict Ω) := by
      have hu_local : LocallyIntegrable u (volume.restrict Ω) :=
        hu.1.locallyIntegrable hp
      have hderiv_cont :
          Continuous (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        (hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
          continuous_const
      have hderiv_support : HasCompactSupport
          (fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) :=
        hφ_support.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      simpa [smul_eq_mul] using
        hu_local.integrable_smul_right_of_hasCompactSupport hderiv_cont hderiv_support
    calc
      ∫ x in Ω, c * u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)
          = ∫ x in Ω, c * (u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) := by
            congr 1; funext x; ring
      _ = c * ∫ x in Ω, u x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
            rw [integral_const_mul]
      _ = c * (- ∫ x in Ω, chosenWeakPartialOrZero p i u Ω x * φ x) := by rw [hu_eq]
      _ = - (c * ∫ x in Ω, chosenWeakPartialOrZero p i u Ω x * φ x) := by ring
      _ = - ∫ x in Ω, c * (chosenWeakPartialOrZero p i u Ω x * φ x) := by
            rw [integral_const_mul]
      _ = - ∫ x in Ω, c * chosenWeakPartialOrZero p i u Ω x * φ x := by
            congr 1; congr 1; funext x; ring
  have hLp_left : LocallyIntegrable (chosenWeakPartialOrZero p i (fun x => c * u x) Ω)
      (volume.restrict Ω) :=
    (chosenWeakPartialOrZero_memLp_of_mem hcu i).locallyIntegrable hp
  have hLp_right : LocallyIntegrable (fun x => c * chosenWeakPartialOrZero p i u Ω x)
      (volume.restrict Ω) :=
    ((chosenWeakPartialOrZero_memLp_of_mem hu i).const_mul c).locallyIntegrable hp
  exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ hPartial_left hPartial_right
    hLp_left hLp_right

theorem MemWkp.const_smul
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω) (c : ℝ) :
    MemWkp (d := d) k p (fun x => c * u x) Ω := by
  induction k generalizing u with
  | zero =>
      rw [MemWkp_zero] at hu ⊢
      exact hu.const_mul c
  | succ k ih =>
      rw [MemWkp_succ] at hu ⊢
      refine ⟨MemW1p.const_smul hp hu.1 c, ?_⟩
      intro i
      have hae := chosenWeakPartialOrZero_const_smul_ae (d := d) hp hΩ hu.1 c i
      have hScaled : MemWkp (d := d) k p
          (fun x => c * chosenWeakPartialOrZero p i u Ω x) Ω :=
        ih (hu.2 i)
      exact (MemWkp_congr_ae (d := d) hp hΩ hae).mpr hScaled

theorem MemWkp.neg
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω) :
    MemWkp (d := d) k p (fun x => - u x) Ω := by
  have h := MemWkp.const_smul (d := d) hp hΩ hu (-1)
  have hEq : (fun x => (-1 : ℝ) * u x) = (fun x => -u x) := by
    funext x; ring
  rw [hEq] at h
  exact h

theorem MemWkp.sub
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ}
    (hu : MemWkp (d := d) k p u Ω) (hv : MemWkp (d := d) k p v Ω) :
    MemWkp (d := d) k p (fun x => u x - v x) Ω := by
  have hneg := MemWkp.neg (d := d) hp hΩ hv
  have h := MemWkp.add (d := d) hp hΩ hu hneg
  have hEq : (fun x => u x + -v x) = (fun x => u x - v x) := by
    funext x; ring
  rw [hEq] at h
  exact h

def iteratedWeakSobolevNorm (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (k + 1),
    ∑ α : Fin j → Fin d,
      eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω)

theorem wkpNorm_eq_sum
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    iteratedWeakSobolevNorm (d := d) k p u Ω =
      ∑ j ∈ Finset.range (k + 1),
        ∑ α : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω) := rfl

theorem wkpNorm_zero
    (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    iteratedWeakSobolevNorm (d := d) 0 p u Ω = eLpNorm u p (volume.restrict Ω) := by
  classical
  unfold iteratedWeakSobolevNorm
  rw [Finset.sum_range_one]
  have hUniq : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) := fun α => by
    funext i; exact i.elim0
  have : Unique (Fin 0 → Fin d) :=
    { default := fun i : Fin 0 => i.elim0
      uniq := fun α => (hUniq α).symm ▸ rfl }
  rw [Fintype.sum_unique
        (f := fun α : Fin 0 → Fin d =>
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω))]
  simp [iterWeakPartial_zero]

theorem wkpNorm_zero_fun_zero
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω) :
    iteratedWeakSobolevNorm (d := d) k p (fun _ : E => (0 : ℝ)) Ω = 0 := by
  classical
  unfold iteratedWeakSobolevNorm
  refine Finset.sum_eq_zero ?_
  intro j _
  refine Finset.sum_eq_zero ?_
  intro α _
  have h_zero_ae : (fun _ : E => (0 : ℝ)) =ᵐ[volume.restrict Ω] (fun _ => 0) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have h_iter_ae := iterWeakPartial_ae_zero_of_input_ae_zero (d := d)
    (p := p) hp hΩ j α h_zero_ae
  rw [eLpNorm_congr_ae h_iter_ae]
  simp

theorem wkpNorm_lt_top_of_memWkp
    {k : ℕ} {p : ℝ≥0∞} {u : E → ℝ} {Ω : Set E}
    (h : MemWkp (d := d) k p u Ω) :
    iteratedWeakSobolevNorm (d := d) k p u Ω < (⊤ : ℝ≥0∞) := by
  classical
  unfold iteratedWeakSobolevNorm
  refine ENNReal.sum_lt_top.mpr ?_
  intro j hj
  refine ENNReal.sum_lt_top.mpr ?_
  intro α _
  have hj_le : j ≤ k := by
    rw [Finset.mem_range] at hj
    omega
  have h_uWj : MemWkp (d := d) j p u Ω := MemWkp.le_of_le hj_le h
  have h_iter := iterWeakPartial_memLp_of_memWkp (d := d) (p := p) h_uWj α
  exact h_iter.eLpNorm_lt_top

theorem MemWkp.eLpNorm_lt_top
    {k : ℕ} {p : ℝ≥0∞} {u : E → ℝ} {Ω : Set E}
    (h : MemWkp (d := d) k p u Ω) :
    eLpNorm u p (volume.restrict Ω) < (⊤ : ℝ≥0∞) :=
  h.memLp.eLpNorm_lt_top

theorem iterWeakPartial_ae_congr
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (j : ℕ) (α : Fin j → Fin d) {u v : E → ℝ}
    (huv : u =ᵐ[volume.restrict Ω] v) :
    iterWeakPartial (d := d) p j α u Ω
      =ᵐ[volume.restrict Ω] iterWeakPartial (d := d) p j α v Ω := by
  induction j generalizing u v with
  | zero =>
      simpa [iterWeakPartial_zero] using huv
  | succ j ih =>
      rw [iterWeakPartial_succ, iterWeakPartial_succ]
      have h_chosen_ae : chosenWeakPartialOrZero p (α 0) u Ω
          =ᵐ[volume.restrict Ω] chosenWeakPartialOrZero p (α 0) v Ω :=
        chosenWeakPartialOrZero_ae_congr (d := d) hp hΩ huv (α 0)
      exact ih (fun i : Fin j => α i.succ) h_chosen_ae

theorem wkpNorm_congr_ae
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ} (huv : u =ᵐ[volume.restrict Ω] v) :
    iteratedWeakSobolevNorm (d := d) k p u Ω = iteratedWeakSobolevNorm (d := d) k p v Ω := by
  classical
  unfold iteratedWeakSobolevNorm
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro α _
  have h_iter_ae : iterWeakPartial (d := d) p j α u Ω
      =ᵐ[volume.restrict Ω] iterWeakPartial (d := d) p j α v Ω :=
    iterWeakPartial_ae_congr (d := d) hp hΩ j α huv
  exact eLpNorm_congr_ae h_iter_ae

theorem iterWeakPartial_add_ae
    {j : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (α : Fin j → Fin d) {u v : E → ℝ}
    (hu : MemWkp (d := d) j p u Ω) (hv : MemWkp (d := d) j p v Ω) :
    iterWeakPartial (d := d) p j α (fun x => u x + v x) Ω
      =ᵐ[volume.restrict Ω]
      (fun x => iterWeakPartial (d := d) p j α u Ω x +
        iterWeakPartial (d := d) p j α v Ω x) := by
  induction j generalizing u v with
  | zero =>
      simp only [iterWeakPartial_zero]
      exact Filter.EventuallyEq.rfl
  | succ j ih =>
      rw [iterWeakPartial_succ, iterWeakPartial_succ, iterWeakPartial_succ]
      have h_chosen_ae : chosenWeakPartialOrZero p (α 0) (fun x => u x + v x) Ω
          =ᵐ[volume.restrict Ω]
          (fun x => chosenWeakPartialOrZero p (α 0) u Ω x +
            chosenWeakPartialOrZero p (α 0) v Ω x) :=
        chosenWeakPartialOrZero_add_ae (d := d) hp hΩ hu.memW1p hv.memW1p (α 0)
      have h_iter_congr : iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ)
            (chosenWeakPartialOrZero p (α 0) (fun x => u x + v x) Ω) Ω
          =ᵐ[volume.restrict Ω]
          iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ)
            (fun x => chosenWeakPartialOrZero p (α 0) u Ω x +
              chosenWeakPartialOrZero p (α 0) v Ω x) Ω :=
        iterWeakPartial_ae_congr (d := d) hp hΩ j (fun i : Fin j => α i.succ)
          h_chosen_ae
      have h_uW : MemWkp (d := d) j p (chosenWeakPartialOrZero p (α 0) u Ω) Ω :=
        hu.chosenWeakPartial_mem (α 0)
      have h_vW : MemWkp (d := d) j p (chosenWeakPartialOrZero p (α 0) v Ω) Ω :=
        hv.chosenWeakPartial_mem (α 0)
      have h_iter_sum := ih (α := fun i : Fin j => α i.succ) h_uW h_vW
      exact h_iter_congr.trans h_iter_sum

theorem iterWeakPartial_const_smul_ae
    {j : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    (α : Fin j → Fin d) {u : E → ℝ}
    (hu : MemWkp (d := d) j p u Ω) (c : ℝ) :
    iterWeakPartial (d := d) p j α (fun x => c * u x) Ω
      =ᵐ[volume.restrict Ω]
      (fun x => c * iterWeakPartial (d := d) p j α u Ω x) := by
  induction j generalizing u with
  | zero =>
      simp only [iterWeakPartial_zero]
      exact Filter.EventuallyEq.rfl
  | succ j ih =>
      rw [iterWeakPartial_succ, iterWeakPartial_succ]
      have h_chosen_ae : chosenWeakPartialOrZero p (α 0) (fun x => c * u x) Ω
          =ᵐ[volume.restrict Ω]
          (fun x => c * chosenWeakPartialOrZero p (α 0) u Ω x) :=
        chosenWeakPartialOrZero_const_smul_ae (d := d) hp hΩ hu.memW1p c (α 0)
      have h_iter_congr :
          iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ)
              (chosenWeakPartialOrZero p (α 0) (fun x => c * u x) Ω) Ω
          =ᵐ[volume.restrict Ω]
          iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ)
              (fun x => c * chosenWeakPartialOrZero p (α 0) u Ω x) Ω :=
        iterWeakPartial_ae_congr (d := d) hp hΩ j (fun i : Fin j => α i.succ)
          h_chosen_ae
      have h_uW : MemWkp (d := d) j p (chosenWeakPartialOrZero p (α 0) u Ω) Ω :=
        hu.chosenWeakPartial_mem (α 0)
      have h_iter_smul := ih (α := fun i : Fin j => α i.succ) h_uW
      exact h_iter_congr.trans h_iter_smul

theorem wkpNorm_add_le
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : E → ℝ}
    (hu : MemWkp (d := d) k p u Ω) (hv : MemWkp (d := d) k p v Ω) :
    iteratedWeakSobolevNorm (d := d) k p (fun x => u x + v x) Ω ≤
      iteratedWeakSobolevNorm (d := d) k p u Ω + iteratedWeakSobolevNorm (d := d) k p v Ω := by
  classical
  unfold iteratedWeakSobolevNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro j hj
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro α _
  have hj_le : j ≤ k := by
    rw [Finset.mem_range] at hj; omega
  have h_uWj : MemWkp (d := d) j p u Ω := MemWkp.le_of_le hj_le hu
  have h_vWj : MemWkp (d := d) j p v Ω := MemWkp.le_of_le hj_le hv
  have h_iter_add_ae :=
    iterWeakPartial_add_ae (d := d) hp hΩ α h_uWj h_vWj
  rw [eLpNorm_congr_ae h_iter_add_ae]
  have htriangle :
      eLpNorm (fun x => iterWeakPartial (d := d) p j α u Ω x +
        iterWeakPartial (d := d) p j α v Ω x)
          p (volume.restrict Ω)
      ≤ eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω) +
          eLpNorm (iterWeakPartial (d := d) p j α v Ω) p (volume.restrict Ω) := by
    have h := eLpNorm_add_le (μ := volume.restrict Ω) (p := p)
      (f := iterWeakPartial (d := d) p j α u Ω)
      (g := iterWeakPartial (d := d) p j α v Ω) hp
    have hEq : (iterWeakPartial (d := d) p j α u Ω +
        iterWeakPartial (d := d) p j α v Ω) =
        fun x => iterWeakPartial (d := d) p j α u Ω x +
          iterWeakPartial (d := d) p j α v Ω x := by
      funext x
      simp [Pi.add_apply]
    rw [hEq] at h
    exact h
  exact htriangle

theorem wkpNorm_const_smul
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → ℝ}
    (hu : MemWkp (d := d) k p u Ω) (c : ℝ) :
    iteratedWeakSobolevNorm (d := d) k p (fun x => c * u x) Ω =
      ‖c‖ₑ * iteratedWeakSobolevNorm (d := d) k p u Ω := by
  classical
  unfold iteratedWeakSobolevNorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro α _
  have hj_le : j ≤ k := by
    rw [Finset.mem_range] at hj; omega
  have h_uWj : MemWkp (d := d) j p u Ω := MemWkp.le_of_le hj_le hu
  have h_iter_smul_ae :=
    iterWeakPartial_const_smul_ae (d := d) hp hΩ α h_uWj c
  rw [eLpNorm_congr_ae h_iter_smul_ae]
  have heq : (fun x => c * iterWeakPartial (d := d) p j α u Ω x) =
      (c : ℝ) • iterWeakPartial (d := d) p j α u Ω := by
    funext x
    simp [Pi.smul_apply, smul_eq_mul]
  rw [heq]
  rw [eLpNorm_const_smul]

theorem MemW1p.mono_set
    {p : ℝ≥0∞} {Ω Ω' : Set E} (hΩΩ' : Ω' ⊆ Ω)
    {u : E → ℝ} (hu : Sobolev.Euclidean.MemW1p p u Ω) :
    Sobolev.Euclidean.MemW1p p u Ω' := by
  refine ⟨?_, ?_⟩
  · exact hu.1.mono_measure (Measure.restrict_mono_set volume hΩΩ')
  · intro i
    obtain ⟨g, hg_memLp, hg_weak⟩ := hu.2 i
    refine ⟨g, ?_, ?_⟩
    · exact hg_memLp.mono_measure (Measure.restrict_mono_set volume hΩΩ')
    · exact Sobolev.Euclidean.HasWeakPartialDeriv.restrict hΩΩ' hg_weak

theorem chosenWeakPartialOrZero_mono_set_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω Ω' : Set E}
    (hΩ' : IsOpen Ω') (hΩΩ' : Ω' ⊆ Ω)
    {u : E → ℝ} (hu : Sobolev.Euclidean.MemW1p p u Ω) (i : Fin d) :
    chosenWeakPartialOrZero p i u Ω
      =ᵐ[volume.restrict Ω'] chosenWeakPartialOrZero p i u Ω' := by
  classical
  have hu_Ω' : Sobolev.Euclidean.MemW1p p u Ω' := MemW1p.mono_set hΩΩ' hu
  have hP_Ω := chosenWeakPartialOrZero_isWeakPartial_of_mem hu i
  have hP_Ω' := chosenWeakPartialOrZero_isWeakPartial_of_mem hu_Ω' i
  have hP_Ω_restricted : Sobolev.Euclidean.HasWeakPartialDeriv i
      (chosenWeakPartialOrZero p i u Ω) u Ω' :=
    Sobolev.Euclidean.HasWeakPartialDeriv.restrict hΩΩ' hP_Ω
  have hP_Ω_local : LocallyIntegrable (chosenWeakPartialOrZero p i u Ω)
      (volume.restrict Ω') := by
    have hmem : MeasureTheory.MemLp (chosenWeakPartialOrZero p i u Ω) p
        (volume.restrict Ω) :=
      chosenWeakPartialOrZero_memLp_of_mem hu i
    have hmem' : MeasureTheory.MemLp (chosenWeakPartialOrZero p i u Ω) p
        (volume.restrict Ω') :=
      hmem.mono_measure (Measure.restrict_mono_set volume hΩΩ')
    exact hmem'.locallyIntegrable hp
  have hP_Ω'_local : LocallyIntegrable (chosenWeakPartialOrZero p i u Ω')
      (volume.restrict Ω') :=
    (chosenWeakPartialOrZero_memLp_of_mem hu_Ω' i).locallyIntegrable hp
  exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ' hP_Ω_restricted hP_Ω'
    hP_Ω_local hP_Ω'_local

theorem MemWkp.mono_set
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω Ω' : Set E}
    (hΩ' : IsOpen Ω') (hΩΩ' : Ω' ⊆ Ω)
    {u : E → ℝ} (hu : MemWkp (d := d) k p u Ω) :
    MemWkp (d := d) k p u Ω' := by
  induction k generalizing u with
  | zero =>
      rw [MemWkp_zero] at hu ⊢
      exact hu.mono_measure (Measure.restrict_mono_set volume hΩΩ')
  | succ k ih =>
      rw [MemWkp_succ] at hu ⊢
      refine ⟨MemW1p.mono_set hΩΩ' hu.1, ?_⟩
      intro i
      have h_partial_Ω' : MemWkp (d := d) k p (chosenWeakPartialOrZero p i u Ω) Ω' :=
        ih (hu.2 i)
      have hae := chosenWeakPartialOrZero_mono_set_ae (d := d) hp hΩ' hΩΩ' hu.1 i
      exact (MemWkp_congr_ae (d := d) hp hΩ' hae).mp h_partial_Ω'

theorem wkpNorm_mono_order
    {k k' : ℕ} (hk : k ≤ k') {p : ℝ≥0∞} (u : E → ℝ) (Ω : Set E) :
    iteratedWeakSobolevNorm (d := d) k p u Ω ≤ iteratedWeakSobolevNorm (d := d) k' p u Ω := by
  classical
  unfold iteratedWeakSobolevNorm
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro j _ _
    exact bot_le

end Euclidean
end Sobolev
