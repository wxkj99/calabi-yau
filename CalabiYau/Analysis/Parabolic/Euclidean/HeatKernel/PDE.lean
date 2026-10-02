-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Parabolic/Euclidean/HeatKernel/PDE.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Lp

@[expose] public section

noncomputable section

open Real
open scoped RealInnerProductSpace

namespace HeatEquation

section PointwiseEquation

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Nontrivial V]

def heatDt (t : ℝ) (x : V) : ℝ :=
  let r := heatScale t
  let n := Module.finrank ℝ V
  let z := r⁻¹ • x
  (r ^ n)⁻¹ * t⁻¹ *
    ((4 : ℝ)⁻¹ * ‖z‖ ^ 2 - (n : ℝ) / 2) * baseHeat z

omit [Nontrivial V] in
theorem sum_baseD2 (x : V) :
    (∑ i : Fin (Module.finrank ℝ V),
      baseD2 ((stdOrthonormalBasis ℝ V) i)
        ((stdOrthonormalBasis ℝ V) i) x) =
      ((4 : ℝ)⁻¹ * ‖x‖ ^ 2 - (Module.finrank ℝ V : ℝ) / 2) * baseHeat x := by
  let b := stdOrthonormalBasis ℝ V
  change (∑ i : Fin (Module.finrank ℝ V), baseD2 (b i) (b i) x) = _
  unfold baseD2
  rw [← Finset.sum_mul]
  simp_rw [b.inner_eq_ite, if_pos]
  rw [Finset.sum_sub_distrib]
  simp_rw [mul_assoc, ← pow_two]
  rw [← Finset.mul_sum, b.sum_sq_inner_left]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

omit [Nontrivial V] in
theorem heatDt_eq_trace {t : ℝ} (ht : 0 < t) (x : V) :
    heatDt t x =
      ∑ i : Fin (Module.finrank ℝ V),
        heatD2 t ((stdOrthonormalBasis ℝ V) i)
          ((stdOrthonormalBasis ℝ V) i) x := by
  have hr : heatScale t ≠ 0 := (heatScale_pos ht).ne'
  have hsquare : heatScale t ^ 2 = t := by
    simpa [heatScale] using Real.sq_sqrt ht.le
  have hscale : (heatScale t)⁻¹ * (heatScale t)⁻¹ = t⁻¹ := by
    field_simp [hr, ht.ne']
    nlinarith [hsquare]
  simp only [heatD2]
  rw [← Finset.mul_sum, sum_baseD2]
  unfold heatDt
  rw [← hscale]
  ring

theorem heatKernel_time {t : ℝ} (ht : 0 < t) (x : V) :
    HasDerivAt (fun s : ℝ => heatKernel s x) (heatDt t x) t := by
  let n := Module.finrank ℝ V
  let r := heatScale t
  let z := r⁻¹ • x
  have hr : 0 < r := by
    simpa only [r] using heatScale_pos ht
  have hrsq : r ^ 2 = t := by
    simpa only [r, heatScale] using Real.sq_sqrt ht.le
  have hn : 0 < n := by
    simpa only [n] using (Module.finrank_pos : 0 < Module.finrank ℝ V)
  have hscale : HasDerivAt heatScale (1 / (2 * r)) t := by
    change HasDerivAt (fun s : ℝ => Real.sqrt s) (1 / (2 * Real.sqrt t)) t
    exact Real.hasDerivAt_sqrt ht.ne'
  have hcoeff0 := (hscale.fun_pow n).inv (pow_ne_zero n hr.ne')
  change HasDerivAt (fun s : ℝ => ((heatScale s) ^ n)⁻¹)
    (-((n : ℝ) * r ^ (n - 1) * (1 / (2 * r))) / (r ^ n) ^ 2) t at hcoeff0
  have hcoeff :
      HasDerivAt (fun s : ℝ => ((heatScale s) ^ n)⁻¹)
        (-((n : ℝ) / (2 * t)) * (r ^ n)⁻¹) t := by
    convert hcoeff0 using 1
    rw [← hrsq]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hm]
    simp only [Nat.cast_succ, Nat.succ_sub_one, pow_succ]
    field_simp [hr.ne']
  have hz0 := (hscale.inv hr.ne').smul_const x
  change HasDerivAt (fun s : ℝ => (heatScale s)⁻¹ • x)
    ((-(1 / (2 * r)) / r ^ 2) • x) t at hz0
  have hz : HasDerivAt (fun s : ℝ => (heatScale s)⁻¹ • x)
      ((-(2 * t)⁻¹) • z) t := by
    convert hz0 using 1
    simp only [z, smul_smul]
    congr 1
    rw [← hrsq]
    field_simp [hr.ne']
  have hbase : HasDerivAt (fun s : ℝ => baseHeat ((heatScale s)⁻¹ • x))
      (baseD1Map z ((-(2 * t)⁻¹) • z)) t := by
    exact (baseHeat_hasFDeriv z).comp_hasDerivAt t hz
  have hprod := hcoeff.mul hbase
  have hder :
      -((n : ℝ) / (2 * t)) * (r ^ n)⁻¹ * baseHeat z +
          (r ^ n)⁻¹ * baseD1Map z ((-(2 * t)⁻¹) • z) = heatDt t x := by
    unfold heatDt
    simp only [n, r, z, baseD1Map, smul_apply,
      innerSL_apply_apply, real_inner_smul_right, real_inner_self_eq_norm_sq,
      smul_eq_mul]
    field_simp [ht.ne']
    ring
  change HasDerivAt
    ((fun s : ℝ => ((heatScale s) ^ n)⁻¹) *
      fun s => baseHeat ((heatScale s)⁻¹ • x)) (heatDt t x) t
  rw [← hder]
  exact hprod

end PointwiseEquation

end HeatEquation
