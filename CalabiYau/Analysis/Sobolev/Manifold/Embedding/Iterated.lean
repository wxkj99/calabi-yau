-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Sobolev/Manifold/Embedding/Iterated.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Subcritical
public import CalabiYau.Analysis.Sobolev.Manifold.Morrey.Basic
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Witness
public import CalabiYau.Analysis.Sobolev.Euclidean.W1p.Approximation
public import CalabiYau.Analysis.Sobolev.Euclidean.Poincare.Ball
public import CalabiYau.Analysis.Sobolev.Euclidean.Poincare.SobolevPoincare
public import CalabiYau.Analysis.Sobolev.Euclidean.Ball.Approximation
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.RieszKernel
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.SmoothHolderBound
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.Morrey.SmoothInequality
public import CalabiYau.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev
public import CalabiYau.Analysis.Sobolev.Euclidean.Density
public import CalabiYau.Analysis.Sobolev.Intrinsic.Equivalence.Basic
public import CalabiYau.Analysis.Sobolev.Approximation.Density.FirstOrder
public import CalabiYau.Analysis.Sobolev.Euclidean.Embedding.GagliardoNirenberg

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open Sobolev.Euclidean Sobolev.Chart
open scoped Manifold ContDiff ENNReal NNReal

namespace CalabiYau
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace EuclideanIterated

variable {d : ℕ}

local notation "EuN" => EuclideanSpace ℝ (Fin d)

theorem wkpNorm_mono_order
    {j k : ℕ} (hjk : j ≤ k) {p : ℝ≥0∞} {f : EuN → ℝ} {Ω : Set EuN} :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) j p f Ω ≤
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := d) k p f Ω := by
  classical
  unfold Sobolev.Euclidean.iteratedWeakSobolevNorm
  refine Finset.sum_le_sum_of_subset ?_
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Finset.mem_range]
  omega

theorem chosenWeakPartialOrZero_cross_exponent_ae_eq
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) {Ω : Set EuN}
    (hΩ_open : IsOpen Ω) {f : EuN → ℝ}
    (hfp : Sobolev.Euclidean.MemW1p p f Ω) (hfq : Sobolev.Euclidean.MemW1p q f Ω) (i : Fin d) :
    Sobolev.Euclidean.chosenWeakPartialOrZero (d := d)
        p i f Ω
      =ᵐ[volume.restrict Ω]
      Sobolev.Euclidean.chosenWeakPartialOrZero (d := d)
        q i f Ω := by
  classical
  have h_p_isWeak :=
    Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
      (d := d) hfp i
  have h_q_isWeak :=
    Sobolev.Euclidean.chosenWeakPartialOrZero_isWeakPartial_of_mem
      (d := d) hfq i
  have h_p_local : LocallyIntegrable
      (Sobolev.Euclidean.chosenWeakPartialOrZero p i f Ω)
      (volume.restrict Ω) :=
    (Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      (d := d) hfp i).locallyIntegrable hp
  have h_q_local : LocallyIntegrable
      (Sobolev.Euclidean.chosenWeakPartialOrZero q i f Ω)
      (volume.restrict Ω) :=
    (Sobolev.Euclidean.chosenWeakPartialOrZero_memLp_of_mem
      (d := d) hfq i).locallyIntegrable hq
  exact Sobolev.Euclidean.HasWeakPartialDeriv.ae_eq hΩ_open h_p_isWeak h_q_isWeak
    h_p_local h_q_local

open Sobolev.Euclidean in
theorem wkpNorm_succ_eq
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) :
    iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω =
      eLpNorm u p (volume.restrict Ω) +
        ∑ i : Fin d,
          iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero p i u Ω) Ω := by
  classical
  unfold iteratedWeakSobolevNorm
  rw [Finset.sum_range_succ' (n := k + 1)
      (f := fun j =>
        ∑ α : Fin j → Fin d,
          eLpNorm (iterWeakPartial (d := d) p j α u Ω) p (volume.restrict Ω))]
  have h_zero_term :
      (∑ α : Fin 0 → Fin d,
          eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω)) =
        eLpNorm u p (volume.restrict Ω) := by
    have hUniq : ∀ α : Fin 0 → Fin d, α = (fun i : Fin 0 => i.elim0) := fun α => by
      funext i; exact i.elim0
    have : Unique (Fin 0 → Fin d) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun α => (hUniq α).symm ▸ rfl }
    rw [Fintype.sum_unique
          (f := fun α : Fin 0 → Fin d =>
            eLpNorm (iterWeakPartial (d := d) p 0 α u Ω) p (volume.restrict Ω))]
    simp [iterWeakPartial_zero]
  rw [h_zero_term, add_comm]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro j _
  have h_unfold : ∀ α : Fin (j + 1) → Fin d,
      iterWeakPartial (d := d) p (j + 1) α u Ω =
        iterWeakPartial (d := d) p j (fun i : Fin j => α i.succ)
          (chosenWeakPartialOrZero p (α 0) u Ω) Ω :=
    fun α => iterWeakPartial_succ p j α u Ω
  let e : Fin d × (Fin j → Fin d) ≃ (Fin (j + 1) → Fin d) :=
    { toFun := fun p => Fin.cons p.1 p.2
      invFun := fun α => (α 0, fun i : Fin j => α i.succ)
      left_inv := fun p => by
        refine Prod.ext ?_ ?_
        · simp
        · funext i
          change (Fin.cons p.1 p.2 : Fin (j + 1) → Fin d) i.succ = p.2 i
          rw [Fin.cons_succ]
      right_inv := fun α => by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro k
          change (Fin.cons (α 0) (fun i : Fin j => α i.succ) : Fin (j + 1) → Fin d) k.succ
            = α k.succ
          rw [Fin.cons_succ] }
  rw [show
      ∑ α : Fin (j + 1) → Fin d,
        eLpNorm (iterWeakPartial (d := d) p (j + 1) α u Ω) p (volume.restrict Ω) =
      ∑ p' : Fin d × (Fin j → Fin d),
        eLpNorm (iterWeakPartial (d := d) p (j + 1) (e p') u Ω) p (volume.restrict Ω) from
    (Fintype.sum_equiv e
      (fun p' => eLpNorm (iterWeakPartial (d := d) p (j + 1) (e p') u Ω) p
        (volume.restrict Ω))
      (fun α => eLpNorm (iterWeakPartial (d := d) p (j + 1) α u Ω) p
        (volume.restrict Ω))
      (fun _ => rfl)).symm]
  rw [show
      ∑ p' : Fin d × (Fin j → Fin d),
        eLpNorm (iterWeakPartial (d := d) p (j + 1) (e p') u Ω) p (volume.restrict Ω) =
      ∑ i : Fin d, ∑ α' : Fin j → Fin d,
        eLpNorm (iterWeakPartial (d := d) p (j + 1) (e (i, α')) u Ω) p (volume.restrict Ω) from
    Fintype.sum_prod_type _]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro α' _
  have hcons_zero : (Fin.cons i α' : Fin (j + 1) → Fin d) 0 = i := Fin.cons_zero _ _
  have hcons_succ : ∀ k : Fin j, (Fin.cons i α' : Fin (j + 1) → Fin d) k.succ = α' k :=
    fun k => Fin.cons_succ _ _ _
  have hiter_eq :
      iterWeakPartial (d := d) p (j + 1) (e (i, α')) u Ω =
        iterWeakPartial (d := d) p j α' (chosenWeakPartialOrZero p i u Ω) Ω := by
    change iterWeakPartial (d := d) p (j + 1) (Fin.cons i α') u Ω =
      iterWeakPartial (d := d) p j α' (chosenWeakPartialOrZero p i u Ω) Ω
    rw [iterWeakPartial_succ]
    have h_tail : (fun k : Fin j => (Fin.cons i α' : Fin (j + 1) → Fin d) k.succ) = α' := by
      funext k; exact hcons_succ k
    rw [h_tail, hcons_zero]
  rw [hiter_eq]

open Sobolev.Euclidean in
theorem wkpNorm_chosenWeakPartial_le_wkpNorm_succ
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) (i : Fin d) :
    iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero p i u Ω) Ω ≤
      iteratedWeakSobolevNorm (d := d) (k + 1) p u Ω := by
  classical
  rw [wkpNorm_succ_eq (d := d) k p u Ω]
  have h_single : iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero p i u Ω) Ω ≤
      ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero p i u Ω) Ω :=
    Finset.single_le_sum
      (f := fun i : Fin d =>
        iteratedWeakSobolevNorm (d := d) k p (chosenWeakPartialOrZero p i u Ω) Ω)
      (s := (Finset.univ : Finset (Fin d)))
      (fun _ _ => zero_le)
      (Finset.mem_univ i)
  exact le_trans h_single (le_add_self)

open Sobolev.Euclidean in
theorem eLpNorm_le_wkpNorm
    (k : ℕ) (p : ℝ≥0∞) (u : EuN → ℝ) (Ω : Set EuN) :
    eLpNorm u p (volume.restrict Ω) ≤ iteratedWeakSobolevNorm (d := d) k p u Ω := by
  have h := wkpNorm_mono_order (d := d) (Nat.zero_le k) (p := p) (f := u) (Ω := Ω)
  rwa [wkpNorm_zero] at h

end EuclideanIterated

local instance : MeasurableSpace M := borel M

theorem wkpNormChart_one_le_wkpNormChart_succ
    [T2Space M] [SigmaCompactSpace M] (k : ℕ) (hk : 1 ≤ k) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChart (I := I) (M := M) 1 p u ≤
      wkpNormChart (I := I) (M := M) k p u := by
  unfold wkpNormChart
  refine ENNReal.tsum_le_tsum ?_
  intro α
  exact EuclideanIterated.wkpNorm_mono_order (d := Module.finrank ℝ E) hk

theorem MemWkpChart.le_one
    [T2Space M] [SigmaCompactSpace M] {k : ℕ} (hk : 1 ≤ k) {p : ℝ≥0∞} {u : M → ℝ}
    (h : MemWkpChart (I := I) (M := M) k p u) :
    MemWkpChart (I := I) (M := M) 1 p u :=
  MemWkpChart.le_of_le hk h

theorem iterated_sobolev_embedding_chart_C0_supercritical
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {k : ℕ} (hk : 1 ≤ k)
    {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : (Module.finrank ℝ E : ℝ) < p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) k (ENNReal.ofReal p) u) :
    ∃ (ũ : M → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ x ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)),
        ũ x = u x) ∧
      (∀ x : M, ‖ũ x‖ ≤ C *
        (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u).toReal) := by
  have hu_one : MemWkpChart (I := I) (M := M) 1 (ENNReal.ofReal p) u :=
    MemWkpChart.le_one hk hu
  obtain ⟨ũ, C, hũ_cont, hC_nn, hũ_ae, hũ_bound⟩ :=
    morrey_C0_embedding_of_compact (I := I) (M := M) g hp_dim hu_meas hu_one
  refine ⟨ũ, C, hũ_cont, hC_nn, hũ_ae, ?_⟩
  intro x
  refine (hũ_bound x).trans ?_
  have h_k_lt_top : wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M)
      (by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
        exact ENNReal.ofReal_le_ofReal hp_one)
      hu
  have h_norm_le := wkpNormChart_one_le_wkpNormChart_succ
    (I := I) (M := M) k hk (ENNReal.ofReal p) u
  have h_toReal_le :
      (wkpNormChart (I := I) (M := M) 1 (ENNReal.ofReal p) u).toReal ≤
        (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u).toReal :=
    ENNReal.toReal_mono h_k_lt_top.ne h_norm_le
  exact mul_le_mul_of_nonneg_left h_toReal_le hC_nn

namespace TowerStep

variable {d : ℕ}

def pOne (d : ℕ) (p : ℝ) : ℝ := (d : ℝ) * p / ((d : ℝ) - p)

section

variable [NeZero d]

lemma pOne_pos {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) :
    0 < pOne d p := by
  unfold pOne
  have hp_pos : 0 < p := by linarith
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hd_p_pos : 0 < (d : ℝ) - p := by linarith
  exact div_pos (mul_pos hd_pos hp_pos) hd_p_pos

lemma pOne_ge_p {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) :
    p ≤ pOne d p := by
  unfold pOne
  have hp_pos : 0 < p := by linarith
  have hd_pos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hd_p_pos : 0 < (d : ℝ) - p := by linarith
  rw [le_div_iff₀ hd_p_pos]
  nlinarith [hp_pos]

lemma pOne_ge_one {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ)) :
    1 ≤ pOne d p :=
  le_trans hp_one (pOne_ge_p hp_one hp_dim)

end

noncomputable def subcriticalConstantBase (d : ℕ) [NeZero d] (p : ℝ) : ℝ :=
  Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p * (d : ℝ)

variable [NeZero d] in
lemma subcriticalConstantBase_nonneg (d : ℕ) [NeZero d] (p : ℝ) :
    0 ≤ subcriticalConstantBase d p := by
  unfold subcriticalConstantBase
  exact mul_nonneg (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant_nonneg d p) (Nat.cast_nonneg _)

noncomputable def subcriticalConstant : ∀ (_k : ℕ) (d : ℕ) [NeZero d] (_p : ℝ), ℝ
  | 0,     d, _, p => subcriticalConstantBase d p
  | k + 1, d, _, p => subcriticalConstantBase d p + (d : ℝ) * subcriticalConstant k d p

section

variable [NeZero d]

lemma subcriticalConstant_zero (d : ℕ) [NeZero d] (p : ℝ) :
    subcriticalConstant 0 d p = subcriticalConstantBase d p := rfl

lemma subcriticalConstant_succ (k d : ℕ) [NeZero d] (p : ℝ) :
    subcriticalConstant (k + 1) d p =
      subcriticalConstantBase d p + (d : ℝ) * subcriticalConstant k d p := rfl

lemma subcriticalConstant_nonneg (k d : ℕ) [NeZero d] (p : ℝ) :
    0 ≤ subcriticalConstant k d p := by
  induction k with
  | zero => exact subcriticalConstantBase_nonneg d p
  | succ k ih =>
      rw [subcriticalConstant_succ]
      exact add_nonneg (subcriticalConstantBase_nonneg d p)
        (mul_nonneg (Nat.cast_nonneg _) ih)

local notation "EuN" => EuclideanSpace ℝ (Fin d)

open Sobolev.Euclidean
  EuclideanSubcritical EuclideanIterated

theorem MemWkp_subcritical_iterated
    (k : ℕ) {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) :
    ∀ {f : EuN → ℝ},
      HasCompactSupport f → tsupport f ⊆ Ω →
      MemWkp (d := d) (k + 1) (ENNReal.ofReal p) f Ω →
      MemWkp (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ∧
        iteratedWeakSobolevNorm (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ≤
          ENNReal.ofReal (subcriticalConstant k d p) *
            iteratedWeakSobolevNorm (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  classical
  set p_enn : ℝ≥0∞ := ENNReal.ofReal p with hp_enn_def
  set p_1_enn : ℝ≥0∞ := ENNReal.ofReal (pOne d p) with hp_1_enn_def
  have hp_pos : 0 < p := by linarith
  have hp_1_pos : 0 < pOne d p := pOne_pos hp_one hp_dim
  have hp_1_one : 1 ≤ pOne d p := pOne_ge_one hp_one hp_dim
  have hp_enn_one : (1 : ℝ≥0∞) ≤ p_enn := by
    rw [hp_enn_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_one
  have hp_1_enn_one : (1 : ℝ≥0∞) ≤ p_1_enn := by
    rw [hp_1_enn_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_1_one
  induction k with
  | zero =>
      intro f hf_compact hf_support hf
      have h_subcritical :
          eLpNorm f p_1_enn (volume.restrict Ω) ≤
            ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) * (d : ℝ≥0∞) *
              iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω := by
        have h := eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp (d := d)
          hp_one hp_dim hΩ_open (f := f) hf hf_compact hf_support
        change eLpNorm f (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)))
          (volume.restrict Ω) ≤ _ at h
        have hpOne_eq : pOne d p = (d : ℝ) * p / ((d : ℝ) - p) := rfl
        rw [show p_1_enn = ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)) from by
          rw [hp_1_enn_def, hpOne_eq]]
        exact h
      have hf_W1p : Sobolev.Euclidean.MemW1p p_enn f Ω := MemWkp.one_iff_memW1p.mp hf
      have h_eLp_lt_top : eLpNorm f p_1_enn (volume.restrict Ω) < ⊤ := by
        refine lt_of_le_of_lt h_subcritical ?_
        have h_wkp_lt_top : iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω < ⊤ :=
          wkpNorm_lt_top_of_memWkp hf
        have h_first : (ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) : ℝ≥0∞) ≠ ⊤ := ENNReal.ofReal_ne_top
        have h_d_top : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        refine ENNReal.mul_lt_top ?_ h_wkp_lt_top
        exact ENNReal.mul_lt_top h_first.lt_top h_d_top.lt_top
      have hf_memLp_p1 : MemLp f p_1_enn (volume.restrict Ω) :=
        memLp_iff.mpr h_eLp_lt_top
      refine ⟨?_, ?_⟩
      · rw [MemWkp_zero]
        exact hf_memLp_p1
      · rw [wkpNorm_zero]
        rw [subcriticalConstant_zero]
        unfold subcriticalConstantBase
        have hC_nn : 0 ≤ Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p := Sobolev.Euclidean.gagliardoNirenbergSobolevConstant_nonneg d p
        have hd_nn : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
        rw [show ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p * (d : ℝ)) =
            ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) * (d : ℝ≥0∞) from by
          rw [ENNReal.ofReal_mul hC_nn, ENNReal.ofReal_natCast]]
        exact h_subcritical
  | succ k ih =>
      intro f hf_compact hf_support hf
      set K : Set EuN := tsupport f with hK_def
      have hK_compact : IsCompact K := hf_compact
      have hK_closed : IsClosed K := isClosed_tsupport f
      have hKΩ : K ⊆ Ω := hf_support
      have hf_W1p : Sobolev.Euclidean.MemW1p p_enn f Ω := hf.memW1p
      have h_base :
          MemWkp (d := d) 0 p_1_enn f Ω ∧
            iteratedWeakSobolevNorm (d := d) 0 p_1_enn f Ω ≤
              ENNReal.ofReal (subcriticalConstant 0 d p) *
                iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω := by
        have hf1 : MemWkp (d := d) 1 p_enn f Ω :=
          MemWkp.le_of_le (Nat.succ_le_succ (Nat.zero_le _)) hf
        have h_subcritical :
            eLpNorm f p_1_enn (volume.restrict Ω) ≤
              ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) * (d : ℝ≥0∞) *
                iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω := by
          have h := eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp (d := d)
            hp_one hp_dim hΩ_open (f := f) hf1 hf_compact hf_support
          change eLpNorm f (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)))
            (volume.restrict Ω) ≤ _ at h
          have hpOne_eq : pOne d p = (d : ℝ) * p / ((d : ℝ) - p) := rfl
          rw [show p_1_enn = ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p)) from by
            rw [hp_1_enn_def, hpOne_eq]]
          exact h
        have h_eLp_lt_top : eLpNorm f p_1_enn (volume.restrict Ω) < ⊤ := by
          refine lt_of_le_of_lt h_subcritical ?_
          have h_wkp_lt_top : iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω < ⊤ :=
            wkpNorm_lt_top_of_memWkp hf1
          refine ENNReal.mul_lt_top ?_ h_wkp_lt_top
          exact ENNReal.mul_lt_top
            (ENNReal.ofReal_lt_top) (ENNReal.natCast_lt_top _)
        refine ⟨?_, ?_⟩
        · rw [MemWkp_zero]; exact memLp_iff.mpr h_eLp_lt_top
        · rw [wkpNorm_zero, subcriticalConstant_zero]
          unfold subcriticalConstantBase
          have hC_nn : 0 ≤ Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p := Sobolev.Euclidean.gagliardoNirenbergSobolevConstant_nonneg d p
          rw [show ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p * (d : ℝ)) =
              ENNReal.ofReal (Sobolev.Euclidean.gagliardoNirenbergSobolevConstant d p) * (d : ℝ≥0∞) from by
            rw [ENNReal.ofReal_mul hC_nn, ENNReal.ofReal_natCast]]
          exact h_subcritical
      let g : Fin d → EuN → ℝ :=
        fun i => K.indicator (chosenWeakPartialOrZero p_enn i f Ω)
      have hg_eq_iter : ∀ i,
          g i = iteratedZeroExtension (d := d) p_enn Ω K 1 (fun _ : Fin 1 => i) f := by
        intro i
        change K.indicator (chosenWeakPartialOrZero p_enn i f Ω) = _
        rw [iteratedZeroExtension_one]
      have hg_support : ∀ i, tsupport (g i) ⊆ K := by
        intro i
        rw [hg_eq_iter i]
        exact tsupport_iteratedZeroExtension_subset (d := d) hK_closed
          (subset_refl K) 1 (fun _ : Fin 1 => i)
      have hg_compact : ∀ i, HasCompactSupport (g i) := by
        intro i
        exact hK_compact.of_isClosed_subset (isClosed_tsupport _) (hg_support i)
      have hg_support_Ω : ∀ i, tsupport (g i) ⊆ Ω := fun i => (hg_support i).trans hKΩ
      have hf_chosen_mem : ∀ i,
          MemWkp (d := d) (k + 1) p_enn (chosenWeakPartialOrZero p_enn i f Ω) Ω :=
        fun i => hf.chosenWeakPartial_mem i
      have h_iterWP_one : ∀ i,
          iterWeakPartial (d := d) p_enn 1 (fun _ : Fin 1 => i) f Ω
            = chosenWeakPartialOrZero p_enn i f Ω := by
        intro i
        rw [iterWeakPartial_succ]
        simp [iterWeakPartial_zero]
      have hg_ae : ∀ i,
          g i =ᵐ[volume.restrict Ω] chosenWeakPartialOrZero p_enn i f Ω := by
        intro i
        rw [hg_eq_iter i]
        have h := iteratedZeroExtension_ae_eq_iterWeakPartial (d := d) hp_enn_one
          hΩ_open hK_closed 1 (k + 1 + 1) (by omega : 1 ≤ k + 1 + 1)
          (fun _ : Fin 1 => i) (u := f) hf (subset_refl _)
        rw [h_iterWP_one] at h
        exact h
      have hg_mem_kplus1 : ∀ i,
          MemWkp (d := d) (k + 1) p_enn (g i) Ω := by
        intro i
        exact (MemWkp_congr_ae (d := d) hp_enn_one hΩ_open (hg_ae i)).mpr (hf_chosen_mem i)
      have h_ih_g : ∀ i,
          MemWkp (d := d) k p_1_enn (g i) Ω ∧
            iteratedWeakSobolevNorm (d := d) k p_1_enn (g i) Ω ≤
              ENNReal.ofReal (subcriticalConstant k d p) *
                iteratedWeakSobolevNorm (d := d) (k + 1) p_enn (g i) Ω :=
        fun i => ih (hg_compact i) (hg_support_Ω i) (hg_mem_kplus1 i)
      have hf_chosen_mem_p1 : ∀ i,
          MemWkp (d := d) k p_1_enn (chosenWeakPartialOrZero p_enn i f Ω) Ω := by
        intro i
        exact (MemWkp_congr_ae (d := d) hp_1_enn_one hΩ_open (hg_ae i)).mp (h_ih_g i).1
      have h_wkp_eq : ∀ i,
          iteratedWeakSobolevNorm (d := d) k p_1_enn (chosenWeakPartialOrZero p_enn i f Ω) Ω =
            iteratedWeakSobolevNorm (d := d) k p_1_enn (g i) Ω := fun i =>
        (wkpNorm_congr_ae (d := d) hp_1_enn_one hΩ_open (hg_ae i)).symm
      have h_wkp_eq_p : ∀ i,
          iteratedWeakSobolevNorm (d := d) (k + 1) p_enn (chosenWeakPartialOrZero p_enn i f Ω) Ω =
            iteratedWeakSobolevNorm (d := d) (k + 1) p_enn (g i) Ω := fun i =>
        (wkpNorm_congr_ae (d := d) hp_enn_one hΩ_open (hg_ae i)).symm
      have hf_W1p_p1 : Sobolev.Euclidean.MemW1p p_1_enn f Ω := by
        refine ⟨?_, ?_⟩
        · exact h_base.1
        · intro i
          refine ⟨chosenWeakPartialOrZero p_enn i f Ω, ?_, ?_⟩
          · exact (hf_chosen_mem_p1 i).memLp
          · exact chosenWeakPartialOrZero_isWeakPartial_of_mem hf_W1p i
      have hf_mem_p1 : MemWkp (d := d) (k + 1) p_1_enn f Ω := by
        rw [MemWkp_succ]
        refine ⟨hf_W1p_p1, ?_⟩
        intro i
        have h_cross : chosenWeakPartialOrZero p_1_enn i f Ω
            =ᵐ[volume.restrict Ω] chosenWeakPartialOrZero p_enn i f Ω :=
          chosenWeakPartialOrZero_cross_exponent_ae_eq (d := d)
            hp_1_enn_one hp_enn_one hΩ_open hf_W1p_p1 hf_W1p i
        exact (MemWkp_congr_ae (d := d) hp_1_enn_one hΩ_open h_cross).mpr (hf_chosen_mem_p1 i)
      refine ⟨hf_mem_p1, ?_⟩
      rw [wkpNorm_succ_eq (d := d) k p_1_enn f Ω]
      have h_eLp_bound :
          eLpNorm f p_1_enn (volume.restrict Ω) ≤
            ENNReal.ofReal (subcriticalConstantBase d p) *
              iteratedWeakSobolevNorm (d := d) 1 p_enn f Ω := by
        have h := h_base.2
        rw [wkpNorm_zero, subcriticalConstant_zero] at h
        exact h
      have h_sum_term_bound : ∀ i,
          iteratedWeakSobolevNorm (d := d) k p_1_enn (chosenWeakPartialOrZero p_1_enn i f Ω) Ω ≤
            ENNReal.ofReal (subcriticalConstant k d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω := by
        intro i
        have h_cross : chosenWeakPartialOrZero p_1_enn i f Ω
            =ᵐ[volume.restrict Ω] chosenWeakPartialOrZero p_enn i f Ω :=
          chosenWeakPartialOrZero_cross_exponent_ae_eq (d := d)
            hp_1_enn_one hp_enn_one hΩ_open hf_W1p_p1 hf_W1p i
        rw [wkpNorm_congr_ae (d := d) hp_1_enn_one hΩ_open h_cross]
        rw [h_wkp_eq i]
        refine le_trans (h_ih_g i).2 ?_
        rw [← h_wkp_eq_p i]
        gcongr
        exact wkpNorm_chosenWeakPartial_le_wkpNorm_succ (d := d)
          (k + 1) p_enn f Ω i
      have h_sum_bound :
          ∑ i : Fin d,
            iteratedWeakSobolevNorm (d := d) k p_1_enn (chosenWeakPartialOrZero p_1_enn i f Ω) Ω ≤
          ∑ _i : Fin d,
            ENNReal.ofReal (subcriticalConstant k d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω :=
        Finset.sum_le_sum (fun i _ => h_sum_term_bound i)
      have h_sum_const :
          ∑ _i : Fin d,
            ENNReal.ofReal (subcriticalConstant k d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω =
            (d : ℝ≥0∞) *
              (ENNReal.ofReal (subcriticalConstant k d p) *
                iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul]
      have h_eLp_full : eLpNorm f p_1_enn (volume.restrict Ω) ≤
          ENNReal.ofReal (subcriticalConstantBase d p) *
            iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω := by
        refine le_trans h_eLp_bound ?_
        gcongr
        exact wkpNorm_mono_order (d := d) (by omega : 1 ≤ k + 1 + 1)
          (p := p_enn) (f := f) (Ω := Ω)
      calc
        eLpNorm f p_1_enn (volume.restrict Ω) +
            ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) k p_1_enn
              (chosenWeakPartialOrZero p_1_enn i f Ω) Ω
          ≤ ENNReal.ofReal (subcriticalConstantBase d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω +
              ∑ _i : Fin d,
                ENNReal.ofReal (subcriticalConstant k d p) *
                  iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω :=
            add_le_add h_eLp_full h_sum_bound
        _ = ENNReal.ofReal (subcriticalConstantBase d p) *
              iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω +
              (d : ℝ≥0∞) *
                (ENNReal.ofReal (subcriticalConstant k d p) *
                  iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω) := by
              rw [h_sum_const]
        _ = (ENNReal.ofReal (subcriticalConstantBase d p) +
              (d : ℝ≥0∞) * ENNReal.ofReal (subcriticalConstant k d p)) *
            iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω := by
              rw [add_mul, mul_assoc]
        _ = ENNReal.ofReal (subcriticalConstant (k + 1) d p) *
            iteratedWeakSobolevNorm (d := d) (k + 1 + 1) p_enn f Ω := by
              rw [subcriticalConstant_succ]
              rw [ENNReal.ofReal_add (subcriticalConstantBase_nonneg d p)
                (mul_nonneg (Nat.cast_nonneg _) (subcriticalConstant_nonneg k d p))]
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
              rw [ENNReal.ofReal_natCast]

theorem MemWkp_succ_subcritical_step
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {f : EuN → ℝ}
    (hf_compact : HasCompactSupport f) (hf_support : tsupport f ⊆ Ω)
    (hf : MemWkp (d := d) (k + 1) (ENNReal.ofReal p) f Ω) :
    MemWkp (d := d) k (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧
        iteratedWeakSobolevNorm (d := d) k
            (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ≤
          ENNReal.ofReal C *
            iteratedWeakSobolevNorm (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  obtain ⟨h_mem, h_norm⟩ :=
    MemWkp_subcritical_iterated (d := d) k hp_one hp_dim hΩ_open
      hf_compact hf_support hf
  have hpOne_eq : pOne d p = (d : ℝ) * p / ((d : ℝ) - p) := rfl
  refine ⟨?_, ?_⟩
  · rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_mem
  · refine ⟨subcriticalConstant k d p, subcriticalConstant_nonneg k d p, ?_⟩
    rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_norm

end

end TowerStep

namespace ChartTower

variable [T2Space M] [SigmaCompactSpace M]

lemma toEuclidean_extChartAt_tsupport_pou_compact_subset
    [CompactSpace M] (α : M) :
    IsCompact (toEuclidean ''
        ((extChartAt I α) ''
          (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)))) ∧
      toEuclidean ''
          ((extChartAt I α) ''
            (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ))) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
  set Tα : Set M := tsupport
    ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hTα_def
  have hTα_compact : IsCompact Tα := (isClosed_tsupport _).isCompact
  have hTα_chart_source : Tα ⊆ (chartAt H α).source :=
    CalabiYau.RiemannianVolume.chartAtlasPOU_isSubordinate I M α
  have hTα_ext_source : Tα ⊆ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source]; exact hTα_chart_source hx
  have hcont_ext : ContinuousOn (extChartAt I α) Tα :=
    (continuousOn_extChartAt α).mono hTα_ext_source
  have hImage_ext_compact : IsCompact ((extChartAt I α) '' Tα) :=
    hTα_compact.image_of_continuousOn hcont_ext
  have hImage_eucl_compact : IsCompact (toEuclidean '' ((extChartAt I α) '' Tα)) :=
    hImage_ext_compact.image (toEuclidean (E := E)).continuous
  refine ⟨hImage_eucl_compact, ?_⟩
  rintro y ⟨z, ⟨x, hx_support, hxz⟩, hzy⟩
  refine ⟨z, ?_, hzy⟩
  rw [← hxz]
  exact (extChartAt I α).map_source (hTα_ext_source hx_support)

lemma tsupport_chartPushedRaw_pou_mul_subset
    [CompactSpace M] (α : M) (u : M → ℝ) :
    tsupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
      toEuclidean ''
        ((extChartAt I α) ''
          (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ))) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := toEuclidean ''
    ((extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ))) with hK_def
  have hK_compact : IsCompact K :=
    (toEuclidean_extChartAt_tsupport_pou_compact_subset (I := I) (M := M) α).1
  have hK_closed : IsClosed K := hK_compact.isClosed
  have h_support_sub : Function.support (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    classical
    by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_target]
      set z : M := (extChartAt I α).symm
        ((toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))).symm y)
        with hz_def
      have hρ_z : (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) z = 0 := by
        by_contra hρne
        apply hyK
        have hz_support : z ∈ tsupport
            ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
          subset_tsupport _ (Function.mem_support.mpr hρne)
        refine ⟨(toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ
            (Fin (Module.finrank ℝ E))).symm y,
          ⟨z, hz_support, ?_⟩, ?_⟩
        · rw [hz_def]
          rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
          exact (extChartAt I α).right_inv hy_target
        · exact (toEuclidean (E := E)).apply_symm_apply y
      change (((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) z) * u z = 0
      rw [hρ_z]; ring
    · exact chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy_target
  rw [tsupport]
  exact hK_closed.closure_subset_iff.mpr h_support_sub

lemma hasCompactSupport_chartPushedRaw_pou_mul
    [CompactSpace M] (α : M) (u : M → ℝ) :
    HasCompactSupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) := by
  have hK_compact : IsCompact (toEuclidean '' ((extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)))) :=
    (toEuclidean_extChartAt_tsupport_pou_compact_subset (I := I) (M := M) α).1
  exact hK_compact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_chartPushedRaw_pou_mul_subset (I := I) (M := M) α u)

lemma tsupport_chartPushedRaw_pou_mul_subset_target
    [CompactSpace M] (α : M) (u : M → ℝ) :
    tsupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  (tsupport_chartPushedRaw_pou_mul_subset (I := I) (M := M) α u).trans
    (toEuclidean_extChartAt_tsupport_pou_compact_subset (I := I) (M := M) α).2

section

variable [I.Boundaryless]

lemma memWkp_chartPushedRaw_pou_mul_of_memWkpChart
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) k p u) (α : M) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E)
      k p
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_chart_pushed := hu α
  have h_ae : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
      =ᵐ[(volume :
            Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) :=
    chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
  have hopen := chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) hp_one hopen h_ae).mp h_chart_pushed

private lemma wkpNorm_chartPushedRaw_pou_mul_eq_chartPushed
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp_one : 1 ≤ p) (u : M → ℝ) (α : M) :
    Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E)
        k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) =
      Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E)
        k p
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) := by
  let _ := g
  refine Sobolev.Euclidean.wkpNorm_congr_ae
    (d := Module.finrank ℝ E) hp_one
    (chartTargetEuclid_isOpen (I := I) (M := M) α) ?_
  exact (chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u).symm

end

end ChartTower

theorem wkpNormChart_succ_subcritical_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (Module.finrank ℝ E : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ},
        MemWkpChart (I := I) (M := M) (k + 1) (ENNReal.ofReal p) u →
          MemWkpChart (I := I) (M := M) k
            (ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * p /
              ((Module.finrank ℝ E : ℝ) - p))) u ∧
          wkpNormChart (I := I) (M := M) k
              (ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * p /
                ((Module.finrank ℝ E : ℝ) - p))) u
            ≤ ENNReal.ofReal C *
              wkpNormChart (I := I) (M := M) (k + 1) (ENNReal.ofReal p) u := by
  classical
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  set d : ℕ := Module.finrank ℝ E with hd_def
  set p_enn : ℝ≥0∞ := ENNReal.ofReal p with hp_enn_def
  set p_1_real : ℝ := (d : ℝ) * p / ((d : ℝ) - p) with hp_1_real_def
  set p_1_enn : ℝ≥0∞ := ENNReal.ofReal p_1_real with hp_1_enn_def
  have hp_pos : 0 < p := by linarith
  have hd_pos : 0 < d := NeZero.pos d
  have hd_p_pos : 0 < (d : ℝ) - p := by
    have hd_real_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    linarith
  have hp_enn_one : (1 : ℝ≥0∞) ≤ p_enn := by
    rw [hp_enn_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_one
  have hp_1_real_pos : 0 < p_1_real := by
    rw [hp_1_real_def]
    have hd_real_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos
    exact div_pos (mul_pos hd_real_pos hp_pos) hd_p_pos
  have hp_1_real_ge_p : p ≤ p_1_real := by
    rw [hp_1_real_def, le_div_iff₀ hd_p_pos]
    nlinarith [hp_pos]
  have hp_1_real_one : 1 ≤ p_1_real := le_trans hp_one hp_1_real_ge_p
  have hp_1_enn_one : (1 : ℝ≥0∞) ≤ p_1_enn := by
    rw [hp_1_enn_def, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp_1_real_one
  set C : ℝ := TowerStep.subcriticalConstant k d p with hC_def
  have hC_nn : 0 ≤ C := TowerStep.subcriticalConstant_nonneg k d p
  refine ⟨C, hC_nn, ?_⟩
  intro u hu
  set f : M → EuclideanSpace ℝ (Fin d) → ℝ := fun α =>
    chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x) with hf_def
  have hf_compact : ∀ α : M, HasCompactSupport (f α) := fun α =>
    ChartTower.hasCompactSupport_chartPushedRaw_pou_mul (I := I) (M := M) α u
  have hf_support : ∀ α : M,
      tsupport (f α) ⊆ chartTargetEuclid (I := I) (M := M) α := fun α =>
    ChartTower.tsupport_chartPushedRaw_pou_mul_subset_target (I := I) (M := M) α u
  have hf_memWkp : ∀ α : M,
      Sobolev.Euclidean.MemWkp (d := d)
        (k + 1) p_enn (f α) (chartTargetEuclid (I := I) (M := M) α) := fun α =>
    ChartTower.memWkp_chartPushedRaw_pou_mul_of_memWkpChart (I := I) (M := M)
      (k := k + 1) hp_enn_one hu α
  have h_step : ∀ α : M,
      Sobolev.Euclidean.MemWkp (d := d) k p_1_enn
        (f α) (chartTargetEuclid (I := I) (M := M) α) ∧
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) k p_1_enn
          (f α) (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C *
          Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) (k + 1)
            p_enn
            (f α) (chartTargetEuclid (I := I) (M := M) α) := by
    intro α
    have hp_dim_d : p < (d : ℝ) := by rw [hd_def]; exact hp_dim
    have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    have h := TowerStep.MemWkp_succ_subcritical_step (d := d)
      hp_one hp_dim_d hOpen (hf_compact α) (hf_support α) (hf_memWkp α)
    obtain ⟨h_mem, C', hC'_nn, h_norm⟩ := h
    have h_iter := TowerStep.MemWkp_subcritical_iterated (d := d) k hp_one hp_dim_d
      hOpen (hf_compact α) (hf_support α) (hf_memWkp α)
    obtain ⟨h_mem', h_norm'⟩ := h_iter
    have h_pOne_eq : TowerStep.pOne d p = p_1_real := by
      rw [TowerStep.pOne, hp_1_real_def]
    refine ⟨?_, ?_⟩
    · rw [hp_1_enn_def, ← h_pOne_eq]
      exact h_mem'
    · rw [hp_1_enn_def, ← h_pOne_eq, hC_def, hp_enn_def]
      exact h_norm'
  have h_norm_raw_eq_pushed_p_1 : ∀ α : M,
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) k p_1_enn
          (f α) (chartTargetEuclid (I := I) (M := M) α) =
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) k p_1_enn
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := fun α =>
    ChartTower.wkpNorm_chartPushedRaw_pou_mul_eq_chartPushed (I := I) (M := M) g
      (k := k) hp_1_enn_one u α
  have h_norm_raw_eq_pushed_p : ∀ α : M,
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) (k + 1) p_enn
          (f α) (chartTargetEuclid (I := I) (M := M) α) =
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) (k + 1) p_enn
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) := fun α =>
    ChartTower.wkpNorm_chartPushedRaw_pou_mul_eq_chartPushed (I := I) (M := M) g
      (k := k + 1) hp_enn_one u α
  have h_mem_pushed : ∀ α : M,
      Sobolev.Euclidean.MemWkp (d := d) k p_1_enn
        (chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro α
    have h_ae : f α =ᵐ[(volume :
          Measure (EuclideanSpace ℝ (Fin d))).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        chartPushed (I := I) (M := M)
          (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u := by
      symm
      exact chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
    have hOpen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    exact (Sobolev.Euclidean.MemWkp_congr_ae
      (d := d) hp_1_enn_one hOpen h_ae).mp (h_step α).1
  have h_mem_chart : MemWkpChart (I := I) (M := M) k p_1_enn u := h_mem_pushed
  have h_per_chart_norm : ∀ α : M,
      Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) k p_1_enn
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C *
          Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) (k + 1)
            p_enn
            (chartPushed (I := I) (M := M)
              (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := by
    intro α
    rw [← h_norm_raw_eq_pushed_p_1 α, ← h_norm_raw_eq_pushed_p α]
    exact (h_step α).2
  refine ⟨h_mem_chart, ?_⟩
  unfold wkpNormChart
  rw [show ENNReal.ofReal C * ∑' α : M,
        Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) (k + 1)
          p_enn
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) =
      ∑' α : M, ENNReal.ofReal C *
        Sobolev.Euclidean.iteratedWeakSobolevNorm (d := d) (k + 1)
          p_enn
          (chartPushed (I := I) (M := M)
            (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) from
      (ENNReal.tsum_mul_left).symm]
  refine ENNReal.tsum_le_tsum h_per_chart_norm

namespace IterationCalc

private lemma kp1_gt_n_of_kp1p_gt_n
    (n : ℝ) (k : ℕ) (p : ℝ) (hp_pos : 0 < p) (hp_dim : p < n)
    (hkp : n < (k + 1 : ℝ) * p) :
    n < (k : ℝ) * (n * p / (n - p)) := by
  have hn_pos : 0 < n := lt_of_lt_of_le hp_pos hp_dim.le
  have hn_p_pos : 0 < n - p := by linarith
  have hkp_gt : (k : ℝ) * p > n - p := by
    have : (k + 1 : ℝ) * p = (k : ℝ) * p + p := by ring
    linarith [hkp]
  have h_eq : (k : ℝ) * (n * p / (n - p)) = n * ((k : ℝ) * p) / (n - p) := by
    field_simp
  rw [h_eq]
  rw [lt_div_iff₀ hn_p_pos]
  have h_factor : n * ((k : ℝ) * p) - n * (n - p) = n * ((k : ℝ) * p - (n - p)) := by
    ring
  nlinarith [hkp_gt, hn_pos]

lemma kp1_real_gt_d_of_kp1p_gt_d
    (d : ℕ) (k : ℕ) (p : ℝ) (hp_pos : 0 < p) (hp_dim : p < (d : ℝ))
    (hkp : (d : ℝ) < (k + 1 : ℝ) * p) :
    (d : ℝ) < (k : ℝ) * ((d : ℝ) * p / ((d : ℝ) - p)) :=
  kp1_gt_n_of_kp1p_gt_n (d : ℝ) k p hp_pos hp_dim hkp

end IterationCalc

namespace IteratedC0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

variable [I.Boundaryless] in
variable [NeZero (Module.finrank ℝ E)] in
private def Statement
    (g : CalabiYau.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ) (u : M → ℝ) : Prop :=
  ∃ (ũ : M → ℝ) (C : ℝ),
    Continuous ũ ∧ 0 ≤ C ∧
    (∀ᵐ x ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M)),
      ũ x = u x) ∧
    (∀ x : M, ‖ũ x‖ ≤ C *
      (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u).toReal)

end IteratedC0

namespace RegularExponent

def IsRegular (n : ℝ) (p : ℝ) (k : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ k → ((m : ℝ) * p ≠ n)

lemma IsRegular.zero (n : ℝ) (p : ℝ) : IsRegular n p 0 := by
  intro m hm hm_le
  exact absurd hm_le (by omega)

lemma IsRegular.p_ne_n_of_one_le {n p : ℝ} {k : ℕ}
    (h : IsRegular n p k) (hk : 1 ≤ k) : p ≠ n := by
  intro hp_eq
  have h1 : ((1 : ℕ) : ℝ) * p ≠ n := h 1 (le_refl 1) hk
  have : (1 : ℝ) * p = p := by ring
  rw [Nat.cast_one] at h1
  rw [this] at h1
  exact h1 hp_eq

lemma IsRegular.tower_step
    {n p : ℝ} {k : ℕ}
    (hp_one : 1 ≤ p) (hp_lt : p < n) (h : IsRegular n p (k + 1)) :
    IsRegular n (n * p / (n - p)) k := by
  intro m hm hm_le
  have hp_pos : 0 < p := by linarith
  have hd_pos : 0 < n := lt_of_lt_of_le hp_pos hp_lt.le
  have hd_p_pos : 0 < n - p := by linarith
  have h_succ : ((m + 1 : ℕ) : ℝ) * p ≠ n := h (m + 1) (by omega) (by omega)
  intro h_eq
  have h_eq' : (m : ℝ) * (n * p) = n * (n - p) := by
    have : (m : ℝ) * (n * p / (n - p)) * (n - p) = n * (n - p) := by
      rw [h_eq]
    rw [show (m : ℝ) * (n * p / (n - p)) * (n - p) =
        (m : ℝ) * (n * p) by
      field_simp] at this
    exact this
  have h_eq2 : ((m + 1 : ℕ) : ℝ) * p = n := by
    have h_mul : (m : ℝ) * (n * p) = n * (n - p) := h_eq'
    have hn_ne : n ≠ 0 := hd_pos.ne'
    push_cast
    have : (m : ℝ) * (n * p) + n * p = n * (n - p) + n * p := by rw [h_mul]
    nlinarith [hn_ne]
  exact h_succ h_eq2

end RegularExponent

namespace IteratedC0

private theorem statement_holds :
    ∀ (k : ℕ),
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E]
        {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
        {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
        [NeZero (Module.finrank ℝ E)],
      ∀ (g : CalabiYau.SmoothRiemannianMetric I M),
      ∀ {p : ℝ}, 1 ≤ p →
        RegularExponent.IsRegular (Module.finrank ℝ E : ℝ) p (k + 1) →
        (Module.finrank ℝ E : ℝ) < (k + 1 : ℝ) * p →
        ∀ {u : M → ℝ}, Measurable u →
          MemWkpChart (I := I) (M := M) (k + 1) (ENNReal.ofReal p) u →
            Statement (I := I) (M := M) g (k + 1) p u := by
  intro k
  induction k with
  | zero =>
      intro E _ _ _ H _ I M _ _ _ _ _ _ _ _ g p hp_one _hreg hkp u hu_meas hu
      have hp_dim : (Module.finrank ℝ E : ℝ) < p := by
        have : ((0 : ℕ) + 1 : ℝ) * p = p := by ring
        linarith [hkp, this]
      exact iterated_sobolev_embedding_chart_C0_supercritical (I := I) (M := M) g
        (k := 1) (Nat.le_refl 1) hp_one hp_dim hu_meas hu
  | succ k ih =>
      intro E _ _ _ H _ I M _ _ _ _ _ _ _ _ g p hp_one hreg hkp u hu_meas hu
      have hp_ne_n : p ≠ (Module.finrank ℝ E : ℝ) :=
        hreg.p_ne_n_of_one_le (by omega)
      rcases lt_or_gt_of_ne hp_ne_n with hp_lt | hp_gt
      · have hp_pos : 0 < p := by linarith
        obtain ⟨C_step, hC_step_nn, h_step⟩ :=
          wkpNormChart_succ_subcritical_step (I := I) (M := M) g (k := k + 1)
            hp_one hp_lt
        obtain ⟨h_mem_p1, h_norm_p1⟩ := h_step hu
        set p_1 : ℝ := (Module.finrank ℝ E : ℝ) * p /
          ((Module.finrank ℝ E : ℝ) - p) with hp_1_def
        have hd_pos : 0 < (Module.finrank ℝ E : ℝ) := by
          have : 0 < Module.finrank ℝ E := NeZero.pos _
          exact_mod_cast this
        have hd_p_pos : 0 < (Module.finrank ℝ E : ℝ) - p := by linarith
        have hp_1_ge_p : p ≤ p_1 := by
          rw [hp_1_def, le_div_iff₀ hd_p_pos]
          nlinarith [hp_pos]
        have hp_1_one : 1 ≤ p_1 := le_trans hp_one hp_1_ge_p
        have h_id := IterationCalc.kp1_real_gt_d_of_kp1p_gt_d
          (Module.finrank ℝ E) (k + 1) p hp_pos hp_lt (by
            push_cast at hkp ⊢
            linarith)
        have h_id_cast : (Module.finrank ℝ E : ℝ) <
            ((k : ℕ) + 1 : ℝ) * p_1 := by
          rw [hp_1_def]
          push_cast at h_id
          linarith
        have hreg_p_1 : RegularExponent.IsRegular (Module.finrank ℝ E : ℝ) p_1 (k + 1) := by
          rw [hp_1_def]
          exact hreg.tower_step hp_one hp_lt
        have h_IH := ih (E := E) (H := H) (I := I) (M := M) g hp_1_one hreg_p_1
          h_id_cast hu_meas h_mem_p1
        obtain ⟨ũ, C_IH, hũ_cont, hC_IH_nn, hũ_ae, hũ_bound⟩ := h_IH
        refine ⟨ũ, C_IH * C_step, hũ_cont, mul_nonneg hC_IH_nn hC_step_nn, hũ_ae, ?_⟩
        intro x
        refine (hũ_bound x).trans ?_
        have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
          rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
          exact ENNReal.ofReal_le_ofReal hp_one
        have h_wkp_kp2_lt_top :
            wkpNormChart (I := I) (M := M) (k + 1 + 1) (ENNReal.ofReal p) u < ⊤ :=
          wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp_enn_one hu
        have h_wkp_kp1_lt_top :
            wkpNormChart (I := I) (M := M) (k + 1)
              (ENNReal.ofReal p_1) u < ⊤ := by
          have hp_1_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p_1 := by
            rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
            exact ENNReal.ofReal_le_ofReal hp_1_one
          exact wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M)
            hp_1_enn_one h_mem_p1
        have h_C_wkp_lt_top : ENNReal.ofReal C_step *
            wkpNormChart (I := I) (M := M) (k + 1 + 1) (ENNReal.ofReal p) u < ⊤ :=
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_wkp_kp2_lt_top
        have h_norm_p1' :
            wkpNormChart (I := I) (M := M) (k + 1)
              (ENNReal.ofReal p_1) u ≤
              ENNReal.ofReal C_step *
                wkpNormChart (I := I) (M := M) (k + 1 + 1) (ENNReal.ofReal p) u := by
          rw [hp_1_def]
          exact h_norm_p1
        have h_toReal_le := ENNReal.toReal_mono h_C_wkp_lt_top.ne h_norm_p1'
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_step_nn] at h_toReal_le
        calc C_IH *
              (wkpNormChart (I := I) (M := M) (k + 1) (ENNReal.ofReal p_1) u).toReal
            ≤ C_IH * (C_step *
              (wkpNormChart (I := I) (M := M) (k + 1 + 1) (ENNReal.ofReal p) u).toReal) :=
              mul_le_mul_of_nonneg_left h_toReal_le hC_IH_nn
          _ = C_IH * C_step *
              (wkpNormChart (I := I) (M := M) (k + 1 + 1) (ENNReal.ofReal p) u).toReal := by
              ring
      · exact iterated_sobolev_embedding_chart_C0_supercritical (I := I) (M := M) g
          (k := k + 2) (by omega) hp_one hp_gt hu_meas hu

end IteratedC0

theorem iterated_sobolev_embedding_chart_C0_of_regular_exponent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {k : ℕ} (hk : 1 ≤ k) {p : ℝ} (hp_one : 1 ≤ p)
    (hreg : RegularExponent.IsRegular (Module.finrank ℝ E : ℝ) p k)
    (hkp : (Module.finrank ℝ E : ℝ) < (k : ℝ) * p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) k (ENNReal.ofReal p) u) :
    ∃ (ũ : M → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ x ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)),
        ũ x = u x) ∧
      (∀ x : M, ‖ũ x‖ ≤ C *
        (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u).toReal) := by
  classical
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hkp' : (Module.finrank ℝ E : ℝ) < (j + 1 : ℝ) * p := by
    have : ((j + 1 : ℕ) : ℝ) = (j + 1 : ℝ) := by push_cast; ring
    rw [this] at hkp
    exact hkp
  exact IteratedC0.statement_holds j g hp_one hreg hkp' hu_meas hu

namespace RegularExponent

private noncomputable def borderlineSet (n : ℝ) (k : ℕ) : Finset ℝ :=
  (Finset.Icc 1 k).image (fun m : ℕ => n / (m : ℝ))

private lemma isRegular_iff_notMem_borderlineSet
    {n p : ℝ} {k : ℕ} :
    IsRegular n p k ↔ p ∉ borderlineSet n k := by
  classical
  unfold IsRegular borderlineSet
  refine ⟨fun h hmem => ?_, fun hnot m hm_one hm_le hmp_eq => ?_⟩
  · rw [Finset.mem_image] at hmem
    obtain ⟨m, hm_mem, hm_eq⟩ := hmem
    rw [Finset.mem_Icc] at hm_mem
    obtain ⟨hm_one, hm_le⟩ := hm_mem
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hjp : (m : ℝ) * p = n := by
      have hp_eq : p = n / (m : ℝ) := hm_eq.symm
      rw [hp_eq]; field_simp
    exact h m hm_one hm_le hjp
  · apply hnot
    rw [Finset.mem_image]
    refine ⟨m, ?_, ?_⟩
    · rw [Finset.mem_Icc]; exact ⟨hm_one, hm_le⟩
    · have hm_pos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      field_simp
      linarith [hmp_eq]

private lemma exists_notMem_finset_in_open_interval
    {lb p : ℝ} (hlb_lt_p : lb < p) (S : Finset ℝ) :
    ∃ p' : ℝ, lb < p' ∧ p' < p ∧ p' ∉ S := by
  classical
  set T : Finset ℝ := S.filter (fun x => lb < x ∧ x < p) with hT_def
  by_cases hT : T = ∅
  · refine ⟨(lb + p) / 2, by linarith, by linarith, ?_⟩
    intro hmem
    have : (lb + p) / 2 ∈ T := by
      rw [hT_def, Finset.mem_filter]
      exact ⟨hmem, by linarith, by linarith⟩
    rw [hT] at this
    exact (Finset.notMem_empty _) this
  · have hT_nonempty : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
    set M : ℝ := T.max' hT_nonempty with hM_def
    have hM_mem : M ∈ T := T.max'_mem hT_nonempty
    have hM_lt_p : M < p := (Finset.mem_filter.mp hM_mem).2.2
    have hM_gt_lb : lb < M := (Finset.mem_filter.mp hM_mem).2.1
    refine ⟨(M + p) / 2, by linarith, by linarith, ?_⟩
    intro hmem
    have h_in_T : (M + p) / 2 ∈ T := by
      rw [hT_def, Finset.mem_filter]
      exact ⟨hmem, by linarith, by linarith⟩
    have h_le : (M + p) / 2 ≤ M := T.le_max' _ h_in_T
    linarith

lemma exists_regular_exponent_below
    (n : ℝ) (k : ℕ) (hk : 1 ≤ k) {p : ℝ} (hp_one : 1 < p)
    (hkp : n < (k : ℝ) * p) :
    ∃ p' : ℝ, 1 ≤ p' ∧ p' < p ∧ n < (k : ℝ) * p' ∧
      IsRegular n p' k := by
  classical
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  set lb : ℝ := max 1 (n / (k : ℝ)) with hlb_def
  have hnk_lt_p : n / (k : ℝ) < p := by
    rw [div_lt_iff₀ hk_pos]; linarith
  have hlb_lt_p : lb < p := by
    rw [hlb_def, max_lt_iff]; exact ⟨hp_one, hnk_lt_p⟩
  obtain ⟨p', hp'_lb, hp'_lt, hp'_notMem⟩ :=
    exists_notMem_finset_in_open_interval hlb_lt_p (borderlineSet n k)
  refine ⟨p', ?_, hp'_lt, ?_, ?_⟩
  · have h1_le_lb : (1 : ℝ) ≤ lb := by rw [hlb_def]; exact le_max_left _ _
    linarith
  · have hnk_le_lb : n / (k : ℝ) ≤ lb := by rw [hlb_def]; exact le_max_right _ _
    have h_n_lt_kp' : n / (k : ℝ) < p' := lt_of_le_of_lt hnk_le_lb hp'_lb
    rw [div_lt_iff₀ hk_pos] at h_n_lt_kp'; linarith
  · exact (isRegular_iff_notMem_borderlineSet (n := n) (p := p') (k := k)).mpr
      hp'_notMem

end RegularExponent

namespace EuclideanIteratedMonoExp

variable {d : ℕ}

local notation "EuN" => EuclideanSpace ℝ (Fin d)

open Sobolev.Euclidean

private lemma diff_K_subset_diff_subset
    {S K Ω : Set EuN} (hSK : S ⊆ K) :
    Ω \ K ⊆ Ω \ S := fun _ ⟨hx_Ω, hx_notK⟩ =>
  ⟨hx_Ω, fun h => hx_notK (hSK h)⟩

private lemma ae_eq_indicator_of_ae_zero_off_subset
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) {S K : Set EuN} (hSK : S ⊆ K)
    (hK_meas : MeasurableSet K)
    {g : EuN → ℝ}
    (hg_ae_zero : g =ᵐ[(MeasureTheory.volume :
        MeasureTheory.Measure EuN).restrict (Ω \ S)] (fun _ : EuN => (0 : ℝ))) :
    g =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω]
      K.indicator g := by
  classical
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hΩK_meas : MeasurableSet (Ω \ K) := hΩ_meas.diff hK_meas
  have h_ae_zero_diffK : ∀ᵐ x ∂((MeasureTheory.volume :
      MeasureTheory.Measure EuN).restrict (Ω \ K)), g x = 0 := by
    have h := MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (s := Ω \ K) (t := Ω \ S)
      (diff_K_subset_diff_subset (Ω := Ω) hSK) hg_ae_zero
    exact h
  rw [MeasureTheory.ae_restrict_iff' hΩK_meas] at h_ae_zero_diffK
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hΩ_meas]
  filter_upwards [h_ae_zero_diffK] with x hx hx_Ω
  by_cases h_in_K : x ∈ K
  · simp [Set.indicator_of_mem h_in_K]
  · have hx_diff : x ∈ Ω \ K := ⟨hx_Ω, h_in_K⟩
    have : g x = 0 := hx hx_diff
    simp [Set.indicator_of_notMem h_in_K, this]

private lemma chosenWeakPartialOrZero_ae_eq_indicator_of_tsupport_subset
    {p : ℝ≥0∞} (hp_one : 1 ≤ p)
    {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {K : Set EuN} (hK_meas : MeasurableSet K)
    {f : EuN → ℝ}
    (hf_W1p : Sobolev.Euclidean.MemW1p p f Ω)
    (hf_support : tsupport f ⊆ K) (i : Fin d) :
    chosenWeakPartialOrZero (d := d) p i f Ω
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω]
      K.indicator (chosenWeakPartialOrZero (d := d) p i f Ω) := by
  have h_ae_zero_sdiff :
      chosenWeakPartialOrZero (d := d) p i f Ω
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict
          (Ω \ tsupport f)] (fun _ : EuN => (0 : ℝ)) :=
    chosenWeakPartialOrZero_ae_zero_on_sdiff_tsupport (d := d) hp_one hΩ_open
      hf_W1p i
  exact ae_eq_indicator_of_ae_zero_off_subset (Ω := Ω) hΩ_open
    (S := tsupport f) (K := K) hf_support hK_meas h_ae_zero_sdiff

theorem memWkp_mono_exponent_of_tsupport_subset
    (k : ℕ) {Ω : Set EuN} (hΩ_open : IsOpen Ω)
    {K : Set EuN} (hK_closed : IsClosed K)
    (hK_meas_lt_top : MeasureTheory.volume K ≠ ⊤)
    {p p' : ℝ≥0∞} (hp'_one : 1 ≤ p') (hp'_le_p : p' ≤ p)
    {f : EuN → ℝ}
    (hf_support : tsupport f ⊆ K)
    (hfp : MemWkp (d := d) k p f Ω) :
    MemWkp (d := d) k p' f Ω := by
  have hp_one : (1 : ℝ≥0∞) ≤ p := le_trans hp'_one hp'_le_p
  have hK_meas : MeasurableSet K := hK_closed.measurableSet
  have hKΩ_meas_lt_top :
      ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) K ≠ ⊤ :=
    ne_top_of_le_ne_top hK_meas_lt_top
      (MeasureTheory.Measure.restrict_apply_le _ _)
  have memLp_mono : ∀ {q q' : ℝ≥0∞} (_hq_le : q' ≤ q) {h : EuN → ℝ},
      h =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω]
        K.indicator h →
      MeasureTheory.MemLp h q
        ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) →
      MeasureTheory.MemLp h q'
        ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) := by
    intro q q' hq_le h h_eq h_memLp
    have h_zero_off : ∀ x, x ∉ K → K.indicator h x = 0 := fun x hx =>
      Set.indicator_of_notMem hx _
    have h_clean_memLp_q : MeasureTheory.MemLp (K.indicator h) q
        ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) :=
      (MeasureTheory.memLp_congr_ae h_eq).mp h_memLp
    have h_clean_memLp_q' : MeasureTheory.MemLp (K.indicator h) q'
        ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) :=
      h_clean_memLp_q.mono_exponent_of_measure_support_ne_top h_zero_off
        hKΩ_meas_lt_top hq_le
    exact (MeasureTheory.memLp_congr_ae h_eq).mpr h_clean_memLp_q'
  have indicator_tsupport_subset : ∀ (g : EuN → ℝ),
      tsupport (K.indicator g) ⊆ K := by
    intro g
    have h_support_sub : Function.support (K.indicator g) ⊆ K := by
      intro x hx
      by_contra hxK
      have h_zero : K.indicator g x = 0 := Set.indicator_of_notMem hxK _
      exact (Function.mem_support.mp hx) h_zero
    calc tsupport (K.indicator g)
        = closure (Function.support (K.indicator g)) := rfl
      _ ⊆ closure K := closure_mono h_support_sub
      _ = K := hK_closed.closure_eq
  have ae_eq_indicator_of_tsupport : ∀ {h : EuN → ℝ}, tsupport h ⊆ K →
      h =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω]
        K.indicator h := by
    intro h hh_support
    refine MeasureTheory.ae_of_all _ ?_
    intro x
    by_cases h_in_K : x ∈ K
    · rw [Set.indicator_of_mem h_in_K]
    · have hx_not_support : x ∉ tsupport h := fun hsx => h_in_K (hh_support hsx)
      have hh_x_zero : h x = 0 := image_eq_zero_of_notMem_tsupport hx_not_support
      rw [Set.indicator_of_notMem h_in_K, hh_x_zero]
  induction k generalizing f with
  | zero =>
      rw [MemWkp_zero] at hfp ⊢
      exact memLp_mono hp'_le_p (ae_eq_indicator_of_tsupport hf_support) hfp
  | succ k ih =>
      rw [MemWkp_succ] at hfp ⊢
      obtain ⟨hf_W1p, hf_recursive⟩ := hfp
      have hf_ae_eq_indicator := ae_eq_indicator_of_tsupport hf_support
      have hf_W1p' : Sobolev.Euclidean.MemW1p p' f Ω := by
        refine ⟨memLp_mono hp'_le_p hf_ae_eq_indicator hf_W1p.1, ?_⟩
        intro i
        set g : EuN → ℝ := chosenWeakPartialOrZero (d := d) p i f Ω with hg_def
        have hg_memLp_p : MeasureTheory.MemLp g p
            ((MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω) :=
          chosenWeakPartialOrZero_memLp_of_mem (d := d) hf_W1p i
        have hg_weak : Sobolev.Euclidean.HasWeakPartialDeriv i g f Ω :=
          chosenWeakPartialOrZero_isWeakPartial_of_mem (d := d) hf_W1p i
        have hg_ae_eq_indicator : g =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure EuN).restrict Ω] K.indicator g :=
          chosenWeakPartialOrZero_ae_eq_indicator_of_tsupport_subset
            (d := d) hp_one hΩ_open hK_meas hf_W1p hf_support i
        exact ⟨g, memLp_mono hp'_le_p hg_ae_eq_indicator hg_memLp_p, hg_weak⟩
      refine ⟨hf_W1p', ?_⟩
      intro i
      set g_p : EuN → ℝ := chosenWeakPartialOrZero (d := d) p i f Ω with hg_p_def
      have hg_p_mem : MemWkp (d := d) k p g_p Ω := hf_recursive i
      have hg_p_ae_eq_indicator : g_p =ᵐ[(MeasureTheory.volume :
          MeasureTheory.Measure EuN).restrict Ω] K.indicator g_p :=
        chosenWeakPartialOrZero_ae_eq_indicator_of_tsupport_subset
          (d := d) hp_one hΩ_open hK_meas hf_W1p hf_support i
      have h_indicator_tsupport : tsupport (K.indicator g_p) ⊆ K :=
        indicator_tsupport_subset g_p
      have h_indicator_memWkp_p : MemWkp (d := d) k p (K.indicator g_p) Ω :=
        (MemWkp_congr_ae (d := d) hp_one hΩ_open hg_p_ae_eq_indicator).mp hg_p_mem
      have h_indicator_memWkp_p' : MemWkp (d := d) k p' (K.indicator g_p) Ω :=
        ih h_indicator_tsupport h_indicator_memWkp_p
      have hg_p_memWkp_p' : MemWkp (d := d) k p' g_p Ω :=
        (MemWkp_congr_ae (d := d) hp'_one hΩ_open hg_p_ae_eq_indicator).mpr
          h_indicator_memWkp_p'
      have h_cross_ae : chosenWeakPartialOrZero (d := d) p' i f Ω
          =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure EuN).restrict Ω] g_p :=
        Analysis.Sobolev.Chart.EuclideanIterated.chosenWeakPartialOrZero_cross_exponent_ae_eq
          (d := d) hp'_one hp_one hΩ_open hf_W1p' hf_W1p i
      exact (MemWkp_congr_ae (d := d) hp'_one hΩ_open h_cross_ae).mpr hg_p_memWkp_p'

end EuclideanIteratedMonoExp

namespace ChartLevelMonoExp

variable [T2Space M] [SigmaCompactSpace M]

open Sobolev.Euclidean

variable [I.Boundaryless] in
private noncomputable def carrierK (α : M) :
    Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  toEuclidean ''
    ((extChartAt I α) ''
      (tsupport ((CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)))

private lemma carrierK_isCompact [CompactSpace M] (α : M) :
    IsCompact (carrierK (I := I) (M := M) α) :=
  (ChartTower.toEuclidean_extChartAt_tsupport_pou_compact_subset
    (I := I) (M := M) α).1

private lemma carrierK_isClosed [CompactSpace M] (α : M) :
    IsClosed (carrierK (I := I) (M := M) α) :=
  (carrierK_isCompact (I := I) (M := M) α).isClosed

private lemma carrierK_volume_lt_top [CompactSpace M] (α : M) :
    MeasureTheory.volume (carrierK (I := I) (M := M) α) ≠ ⊤ :=
  (carrierK_isCompact (I := I) (M := M) α).measure_lt_top.ne

private lemma tsupport_chartPushedRaw_pou_mul_subset_carrier [CompactSpace M]
    (α : M) (u : M → ℝ) :
    tsupport (chartPushedRaw (I := I) (M := M) α
      (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
      carrierK (I := I) (M := M) α := by
  unfold carrierK
  exact ChartTower.tsupport_chartPushedRaw_pou_mul_subset (I := I) (M := M) α u

section

variable [I.Boundaryless]

theorem memWkp_chartPushed_mono_exponent [CompactSpace M]
    {k : ℕ} {p p' : ℝ≥0∞} (hp'_one : 1 ≤ p') (hp'_le_p : p' ≤ p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) k p u) (α : M) :
    Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E)
      k p'
      (chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_target_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_chartRaw_tsupport :
      tsupport (chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x)) ⊆
        carrierK (I := I) (M := M) α :=
    tsupport_chartPushedRaw_pou_mul_subset_carrier (I := I) (M := M) α u
  have hp_one : (1 : ℝ≥0∞) ≤ p := le_trans hp'_one hp'_le_p
  have h_chartRaw_memWkp_p :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E)
        k p
        (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) :=
    ChartTower.memWkp_chartPushedRaw_pou_mul_of_memWkpChart
      (I := I) (M := M) hp_one hu α
  have h_chartRaw_memWkp_p' :
      Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E)
        k p'
        (chartPushedRaw (I := I) (M := M) α
          (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) x * u x))
        (chartTargetEuclid (I := I) (M := M) α) :=
    EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset
      (d := Module.finrank ℝ E) k h_target_open
      (carrierK_isClosed (I := I) (M := M) α)
      (carrierK_volume_lt_top (I := I) (M := M) α)
      hp'_one hp'_le_p h_chartRaw_tsupport h_chartRaw_memWkp_p
  have h_ae : chartPushed (I := I) (M := M)
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
      =ᵐ[(MeasureTheory.volume :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) (M := M) α
        (fun x : M => (CalabiYau.RiemannianVolume.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x) :=
    chartPushed_eq_chartPushedRaw_pou_ae (I := I) (M := M)
      (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u
  exact (Sobolev.Euclidean.MemWkp_congr_ae
      (d := Module.finrank ℝ E) hp'_one h_target_open h_ae).mpr
    h_chartRaw_memWkp_p'

theorem memWkpChart_mono_exponent [CompactSpace M]
    {k : ℕ} {p p' : ℝ≥0∞} (hp'_one : 1 ≤ p') (hp'_le_p : p' ≤ p)
    {u : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) k p u) :
    MemWkpChart (I := I) (M := M) k p' u := by
  intro α
  exact memWkp_chartPushed_mono_exponent (I := I) (M := M) hp'_one hp'_le_p hu α

end

end ChartLevelMonoExp

theorem iterated_sobolev_embedding_chart_C0
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : CalabiYau.SmoothRiemannianMetric I M)
    {k : ℕ} (hk : 1 ≤ k) {p : ℝ} (hp_one : 1 ≤ p)
    (hkp : (Module.finrank ℝ E : ℝ) < (k : ℝ) * p)
    (h_n_ge_2_or_p_gt_1 : 2 ≤ Module.finrank ℝ E ∨ 1 < p)
    {u : M → ℝ} (hu_meas : Measurable u)
    (hu : MemWkpChart (I := I) (M := M) k (ENNReal.ofReal p) u) :
    ∃ (ũ : M → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ x ∂(CalabiYau.RiemannianVolume.riemannianMeasure (I := I) g
        (CalabiYau.RiemannianVolume.chartAtlasPOU I M)),
        ũ x = u x) ∧
      (∀ x : M, ‖ũ x‖ ≤ C *
        (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u).toReal) := by
  classical
  by_cases hreg : RegularExponent.IsRegular (Module.finrank ℝ E : ℝ) p k
  · exact iterated_sobolev_embedding_chart_C0_of_regular_exponent (I := I) (M := M) g hk hp_one hreg
      hkp hu_meas hu
  · by_cases hp_strict_one : 1 < p
    · obtain ⟨p', hp'_one, hp'_lt, hkp', hp'_regularity⟩ :=
        RegularExponent.exists_regular_exponent_below
          (Module.finrank ℝ E : ℝ) k hk hp_strict_one hkp
      have hp'_le_p_enn : ENNReal.ofReal p' ≤ ENNReal.ofReal p :=
        ENNReal.ofReal_le_ofReal hp'_lt.le
      have hp'_one_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p' := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
        exact ENNReal.ofReal_le_ofReal hp'_one
      have hp_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
        exact ENNReal.ofReal_le_ofReal hp_one
      have hu_p' : MemWkpChart (I := I) (M := M) k (ENNReal.ofReal p') u :=
        ChartLevelMonoExp.memWkpChart_mono_exponent (I := I) (M := M)
          hp'_one_enn hp'_le_p_enn hu
      obtain ⟨ũ, C₁, hũ_cont, hC₁_nn, hũ_ae, hũ_bound₁⟩ :=
        iterated_sobolev_embedding_chart_C0_of_regular_exponent (I := I) (M := M) g hk hp'_one
          hp'_regularity hkp' hu_meas hu_p'
      have h_norm_p_lt :
          wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u < ⊤ :=
        wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp_enn_one hu
      have h_norm_p'_lt :
          wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p') u < ⊤ :=
        wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp'_one_enn hu_p'
      set N_p : ℝ := (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u).toReal
        with hN_p_def
      set N_p' : ℝ := (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p') u).toReal
        with hN_p'_def
      have hN_p_nn : 0 ≤ N_p := ENNReal.toReal_nonneg
      have hN_p'_nn : 0 ≤ N_p' := ENNReal.toReal_nonneg
      by_cases hN_p_pos : 0 < N_p
      · refine ⟨ũ, C₁ * N_p' / N_p, hũ_cont, ?_, hũ_ae, ?_⟩
        · exact div_nonneg (mul_nonneg hC₁_nn hN_p'_nn) hN_p_nn
        · intro x
          have h_bnd := hũ_bound₁ x
          calc ‖ũ x‖
              ≤ C₁ * N_p' := h_bnd
            _ = (C₁ * N_p' / N_p) * N_p := by field_simp
            _ = C₁ * N_p' / N_p *
                (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u).toReal := rfl
      · rw [not_lt] at hN_p_pos
        have hN_p_zero : N_p = 0 := le_antisymm hN_p_pos hN_p_nn
        have h_wkpNormChart_p_eq_zero :
            wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u = 0 := by
          have hN_eq : N_p = 0 := hN_p_zero
          rw [show N_p =
            (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u).toReal
            from rfl] at hN_eq
          exact (ENNReal.toReal_eq_zero_iff _).mp hN_eq |>.resolve_right h_norm_p_lt.ne
        have h_per_chart_p_zero : ∀ α : M,
            Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) k (ENNReal.ofReal p)
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α) = 0 := by
          intro α
          have h_le := ENNReal.le_tsum α
              (f := fun β : M =>
                Sobolev.Euclidean.iteratedWeakSobolevNorm
                  (d := Module.finrank ℝ E) k (ENNReal.ofReal p)
                  (chartPushed (I := I) (M := M)
                    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) β u)
                  (chartTargetEuclid (I := I) (M := M) β))
          rw [show (∑' β : M,
                Sobolev.Euclidean.iteratedWeakSobolevNorm
                  (d := Module.finrank ℝ E) k (ENNReal.ofReal p)
                  (chartPushed (I := I) (M := M)
                    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) β u)
                  (chartTargetEuclid (I := I) (M := M) β)) =
              wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p) u from rfl] at h_le
          rw [h_wkpNormChart_p_eq_zero] at h_le
          exact le_antisymm h_le (zero_le)
        have h_chart_pushed_ae_zero : ∀ α : M,
            (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
              =ᵐ[(MeasureTheory.volume :
                  MeasureTheory.Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)]
              (fun _ => (0 : ℝ)) := by
          intro α
          have h_eLp_zero :
              MeasureTheory.eLpNorm (chartPushed (I := I) (M := M)
                  (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
                (ENNReal.ofReal p)
                ((MeasureTheory.volume :
                    MeasureTheory.Measure (EuclideanSpace ℝ
                      (Fin (Module.finrank ℝ E)))).restrict
                  (chartTargetEuclid (I := I) (M := M) α)) = 0 := by
            have h_le := EuclideanIterated.eLpNorm_le_wkpNorm
              (d := Module.finrank ℝ E) k (ENNReal.ofReal p)
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α)
            rw [h_per_chart_p_zero α] at h_le
            exact le_antisymm h_le (zero_le)
          have hp_pos : ENNReal.ofReal p ≠ 0 := by
            rw [Ne, ENNReal.ofReal_eq_zero]; linarith
          exact (MeasureTheory.eLpNorm_eq_zero_iff hp_pos).mp h_eLp_zero
        have h_per_chart_p'_zero : ∀ α : M,
            Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) k (ENNReal.ofReal p')
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α) = 0 := by
          intro α
          have h_pushed_ae_zero := h_chart_pushed_ae_zero α
          have h_target_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
            chartTargetEuclid_isOpen (I := I) (M := M) α
          rw [Sobolev.Euclidean.wkpNorm_congr_ae
            (d := Module.finrank ℝ E) hp'_one_enn h_target_open h_pushed_ae_zero]
          exact Sobolev.Euclidean.wkpNorm_zero_fun_zero
            (d := Module.finrank ℝ E) hp'_one_enn h_target_open
        have h_N_p'_enn_zero :
            wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p') u = 0 := by
          unfold wkpNormChart
          simp only [h_per_chart_p'_zero]
          exact tsum_zero
        have hN_p'_zero : N_p' = 0 := by
          change (wkpNormChart (I := I) (M := M) k (ENNReal.ofReal p') u).toReal = 0
          rw [h_N_p'_enn_zero]; simp
        refine ⟨ũ, 0, hũ_cont, le_refl _, hũ_ae, ?_⟩
        intro x
        rw [zero_mul]
        have h_bnd := hũ_bound₁ x
        rw [hN_p'_zero, mul_zero] at h_bnd
        exact h_bnd
    · have hp_eq_one : p = 1 := le_antisymm (by linarith) hp_one
      subst hp_eq_one
      have h_finrank_pos : 0 < Module.finrank ℝ E := NeZero.pos _
      have h_n_ge_two : 2 ≤ Module.finrank ℝ E := by
        rcases h_n_ge_2_or_p_gt_1 with h | h
        · exact h
        · exact absurd h (by linarith : ¬ (1 : ℝ) < 1)
      have hkp_real : (Module.finrank ℝ E : ℝ) < (k : ℝ) := by
        rw [show (k : ℝ) * (1 : ℝ) = (k : ℝ) from mul_one _] at hkp; exact hkp
      obtain ⟨k', rfl⟩ : ∃ k' : ℕ, k = k' + 1 := by
        obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        exact ⟨k', rfl⟩
      have hk'_pos : 1 ≤ k' := by
        have h1 : (Module.finrank ℝ E : ℝ) < ((k' + 1 : ℕ) : ℝ) := hkp_real
        have h_n_real_ge_two : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
          exact_mod_cast h_n_ge_two
        have h2 : (2 : ℝ) < ((k' + 1 : ℕ) : ℝ) := lt_of_le_of_lt h_n_real_ge_two h1
        push_cast at h2
        have : (1 : ℝ) < (k' : ℝ) := by linarith
        exact_mod_cast this.le
      have hp_lt_n : (1 : ℝ) < (Module.finrank ℝ E : ℝ) := by
        exact_mod_cast (by omega : 1 < Module.finrank ℝ E)
      obtain ⟨C_step, hC_step_nn, h_step⟩ :=
        wkpNormChart_succ_subcritical_step (I := I) (M := M) g (k := k')
          le_rfl hp_lt_n
      obtain ⟨h_mem_p1, h_norm_p1⟩ := h_step hu
      set p_1 : ℝ := (Module.finrank ℝ E : ℝ) * 1 /
        ((Module.finrank ℝ E : ℝ) - 1) with hp_1_def
      have hd_pos : 0 < (Module.finrank ℝ E : ℝ) := by exact_mod_cast h_finrank_pos
      have hd_minus_one_pos : 0 < (Module.finrank ℝ E : ℝ) - 1 := by linarith
      have hp_1_eq : p_1 = (Module.finrank ℝ E : ℝ) /
          ((Module.finrank ℝ E : ℝ) - 1) := by
        rw [hp_1_def, mul_one]
      have hp_1_pos : 0 < p_1 := by
        rw [hp_1_eq]; exact div_pos hd_pos hd_minus_one_pos
      have hp_1_gt_one : 1 < p_1 := by
        rw [hp_1_eq, lt_div_iff₀ hd_minus_one_pos]; linarith
      have hp_1_ge_one : 1 ≤ p_1 := hp_1_gt_one.le
      have h_kp1_gt_n : (Module.finrank ℝ E : ℝ) < (k' : ℝ) * p_1 := by
        have h_id := IterationCalc.kp1_real_gt_d_of_kp1p_gt_d
          (Module.finrank ℝ E) k' (1 : ℝ) (by norm_num) hp_lt_n (by
            push_cast at hkp_real ⊢
            linarith)
        rw [hp_1_eq]
        rw [mul_one] at h_id
        exact h_id
      obtain ⟨p', hp'_one, hp'_lt, hkp', hp'_regularity⟩ :=
        RegularExponent.exists_regular_exponent_below
          (Module.finrank ℝ E : ℝ) k' hk'_pos hp_1_gt_one h_kp1_gt_n
      have hp'_le_p_1_enn : ENNReal.ofReal p' ≤ ENNReal.ofReal p_1 :=
        ENNReal.ofReal_le_ofReal hp'_lt.le
      have hp'_one_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p' := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
        exact ENNReal.ofReal_le_ofReal hp'_one
      have hp_1_enn_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p_1 := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
        exact ENNReal.ofReal_le_ofReal hp_1_ge_one
      have h_mem_p1' : MemWkpChart (I := I) (M := M) k' (ENNReal.ofReal p_1) u := by
        rw [hp_1_def] at h_mem_p1; exact h_mem_p1
      have hu_p' : MemWkpChart (I := I) (M := M) k' (ENNReal.ofReal p') u :=
        ChartLevelMonoExp.memWkpChart_mono_exponent (I := I) (M := M)
          hp'_one_enn hp'_le_p_1_enn h_mem_p1'
      obtain ⟨ũ, C₁, hũ_cont, hC₁_nn, hũ_ae, hũ_bound₁⟩ :=
        iterated_sobolev_embedding_chart_C0_of_regular_exponent (I := I) (M := M) g hk'_pos hp'_one
          hp'_regularity hkp' hu_meas hu_p'
      have hp_enn_one : (1 : ℝ≥0∞) ≤ (ENNReal.ofReal 1) := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
      have h_norm_1_lt :
          wkpNormChart (I := I) (M := M) (k' + 1) (ENNReal.ofReal 1) u < ⊤ :=
        wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp_enn_one hu
      have h_norm_p1_lt :
          wkpNormChart (I := I) (M := M) k' (ENNReal.ofReal p_1) u < ⊤ :=
        wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) hp_1_enn_one h_mem_p1'
      set N_1 : ℝ := (wkpNormChart (I := I) (M := M) (k' + 1) (ENNReal.ofReal 1) u).toReal
        with hN_1_def
      set N_p1 : ℝ := (wkpNormChart (I := I) (M := M) k' (ENNReal.ofReal p_1) u).toReal
        with hN_p1_def
      set N_p' : ℝ := (wkpNormChart (I := I) (M := M) k' (ENNReal.ofReal p') u).toReal
        with hN_p'_def
      have hN_1_nn : 0 ≤ N_1 := ENNReal.toReal_nonneg
      have hN_p1_nn : 0 ≤ N_p1 := ENNReal.toReal_nonneg
      have hN_p'_nn : 0 ≤ N_p' := ENNReal.toReal_nonneg
      have h_step_real : N_p1 ≤ C_step * N_1 := by
        have h_norm_p1_le :
            wkpNormChart (I := I) (M := M) k' (ENNReal.ofReal p_1) u ≤
              ENNReal.ofReal C_step *
                wkpNormChart (I := I) (M := M) (k' + 1) (ENNReal.ofReal 1) u := by
          rw [hp_1_def]; exact h_norm_p1
        have h_C_lt : ENNReal.ofReal C_step *
            wkpNormChart (I := I) (M := M) (k' + 1) (ENNReal.ofReal 1) u < ⊤ :=
          ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_norm_1_lt
        have h_le := ENNReal.toReal_mono h_C_lt.ne h_norm_p1_le
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC_step_nn] at h_le
        exact h_le
      by_cases hN_p1_pos : 0 < N_p1
      · refine ⟨ũ, C₁ * N_p' / N_p1 * C_step, hũ_cont, ?_, hũ_ae, ?_⟩
        · refine mul_nonneg (div_nonneg ?_ hN_p1_nn) hC_step_nn
          exact mul_nonneg hC₁_nn hN_p'_nn
        · intro x
          have h_bnd := hũ_bound₁ x
          calc ‖ũ x‖
              ≤ C₁ * N_p' := h_bnd
            _ = (C₁ * N_p' / N_p1) * N_p1 := by field_simp
            _ ≤ (C₁ * N_p' / N_p1) * (C_step * N_1) :=
                mul_le_mul_of_nonneg_left h_step_real
                  (div_nonneg (mul_nonneg hC₁_nn hN_p'_nn) hN_p1_nn)
            _ = C₁ * N_p' / N_p1 * C_step *
                (wkpNormChart (I := I) (M := M) (k' + 1) (ENNReal.ofReal 1) u).toReal :=
                by ring
      · rw [not_lt] at hN_p1_pos
        have hN_p1_zero : N_p1 = 0 := le_antisymm hN_p1_pos hN_p1_nn
        have h_wkpNormChart_p1_eq_zero :
            wkpNormChart (I := I) (M := M) k' (ENNReal.ofReal p_1) u = 0 := by
          have hN_eq : N_p1 = 0 := hN_p1_zero
          rw [show N_p1 =
            (wkpNormChart (I := I) (M := M) k' (ENNReal.ofReal p_1) u).toReal
            from rfl] at hN_eq
          exact (ENNReal.toReal_eq_zero_iff _).mp hN_eq |>.resolve_right h_norm_p1_lt.ne
        have h_per_chart_p1_zero : ∀ α : M,
            Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) k' (ENNReal.ofReal p_1)
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α) = 0 := by
          intro α
          have h_le := ENNReal.le_tsum α
              (f := fun β : M =>
                Sobolev.Euclidean.iteratedWeakSobolevNorm
                  (d := Module.finrank ℝ E) k' (ENNReal.ofReal p_1)
                  (chartPushed (I := I) (M := M)
                    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) β u)
                  (chartTargetEuclid (I := I) (M := M) β))
          rw [show (∑' β : M,
                Sobolev.Euclidean.iteratedWeakSobolevNorm
                  (d := Module.finrank ℝ E) k' (ENNReal.ofReal p_1)
                  (chartPushed (I := I) (M := M)
                    (CalabiYau.RiemannianVolume.chartAtlasPOU I M) β u)
                  (chartTargetEuclid (I := I) (M := M) β)) =
              wkpNormChart (I := I) (M := M) k' (ENNReal.ofReal p_1) u from rfl] at h_le
          rw [h_wkpNormChart_p1_eq_zero] at h_le
          exact le_antisymm h_le (zero_le)
        have h_chart_pushed_ae_zero : ∀ α : M,
            (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
              =ᵐ[(MeasureTheory.volume :
                  MeasureTheory.Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)]
              (fun _ => (0 : ℝ)) := by
          intro α
          have h_eLp_zero :
              MeasureTheory.eLpNorm (chartPushed (I := I) (M := M)
                  (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
                (ENNReal.ofReal p_1)
                ((MeasureTheory.volume :
                    MeasureTheory.Measure (EuclideanSpace ℝ
                      (Fin (Module.finrank ℝ E)))).restrict
                  (chartTargetEuclid (I := I) (M := M) α)) = 0 := by
            have h_le := EuclideanIterated.eLpNorm_le_wkpNorm
              (d := Module.finrank ℝ E) k' (ENNReal.ofReal p_1)
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α)
            rw [h_per_chart_p1_zero α] at h_le
            exact le_antisymm h_le (zero_le)
          have hp1_pos : ENNReal.ofReal p_1 ≠ 0 := by
            rw [Ne, ENNReal.ofReal_eq_zero]; linarith
          exact (MeasureTheory.eLpNorm_eq_zero_iff hp1_pos).mp h_eLp_zero
        have h_per_chart_p'_zero : ∀ α : M,
            Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) k' (ENNReal.ofReal p')
              (chartPushed (I := I) (M := M)
                (CalabiYau.RiemannianVolume.chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α) = 0 := by
          intro α
          have h_pushed_ae_zero := h_chart_pushed_ae_zero α
          have h_target_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
            chartTargetEuclid_isOpen (I := I) (M := M) α
          rw [Sobolev.Euclidean.wkpNorm_congr_ae
            (d := Module.finrank ℝ E) hp'_one_enn h_target_open h_pushed_ae_zero]
          exact Sobolev.Euclidean.wkpNorm_zero_fun_zero
            (d := Module.finrank ℝ E) hp'_one_enn h_target_open
        have h_N_p'_enn_zero :
            wkpNormChart (I := I) (M := M) k' (ENNReal.ofReal p') u = 0 := by
          unfold wkpNormChart
          simp only [h_per_chart_p'_zero]
          exact tsum_zero
        have hN_p'_zero : N_p' = 0 := by
          change (wkpNormChart (I := I) (M := M) k' (ENNReal.ofReal p') u).toReal = 0
          rw [h_N_p'_enn_zero]; simp
        refine ⟨ũ, 0, hũ_cont, le_refl _, hũ_ae, ?_⟩
        intro x
        rw [zero_mul]
        have h_bnd := hũ_bound₁ x
        rw [hN_p'_zero, mul_zero] at h_bnd
        exact h_bnd

end Chart
end Sobolev
end Analysis
end CalabiYau
