module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Real calculus for inverse matrix entries

This Mathlib-only bridge is shared by chart connection calculus and higher-order estimates.
It applies Mathlib's Neumann-series proof of Banach-algebra inversion, rather than expanding
an adjugate. The matrix operator norm is an implementation detail: every public derivative
is a continuous real-linear map with scalar codomain, and no matrix norm instance is exported.

The source declarations are `contDiffAt_ringInverse` and `hasFDerivAt_ringInverse`;
`Matrix.nonsing_inv_eq_ringInverse` identifies their inverse with the matrix inverse.
The derivative convention is `D(A⁻¹)[v] = -A⁻¹ * DA[v] * A⁻¹`. There is no conjugation,
transpose, or factor of two. Empty index sets require no special nonemptiness hypothesis.
-/

noncomputable section
open scoped ContDiff

namespace Matrix

variable {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike κ]
variable {n : ℕ}

section

-- This scope ends before every public declaration. In particular, it cannot change the
-- entrywise matrix norms used by existing consumers.
open scoped Matrix.Norms.Operator

private def assembleEntries : (Fin n × Fin n → κ) →L[ℝ] Matrix (Fin n) (Fin n) κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f i j => f (i, j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private def entryProjection (i j : Fin n) : Matrix (Fin n) (Fin n) κ →L[ℝ] κ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => B i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem smoothMatrix {A : E → Matrix (Fin n) (Fin n) κ} {W : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W) : ContDiffOn ℝ ∞ A W := by
  exact (assembleEntries (n := n) (κ := κ)).contDiff.comp_contDiffOn
    (contDiffOn_pi.mpr fun p => hA p.1 p.2)

private theorem smoothInverse {A : E → Matrix (Fin n) (Fin n) κ} {W : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hunit : ∀ z ∈ W, IsUnit (A z)) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => (A z)⁻¹ i j) W := by
  have h := smoothMatrix hA
  intro z hz
  obtain ⟨u, hu⟩ := hunit z hz
  have huinv : ContDiffAt ℝ ∞ Ring.inverse (A z) := by
    simpa only [hu] using contDiffAt_ringInverse ℝ u (n := ∞)
  have hi := huinv.comp_contDiffWithinAt z (h z hz)
  have hip := (entryProjection (κ := κ) i j).contDiff.contDiffAt.comp_contDiffWithinAt z hi
  change ContDiffWithinAt ℝ ∞ (fun x => Ring.inverse (A x) i j) W z at hip
  simpa only [← nonsing_inv_eq_ringInverse] using hip

private theorem inverseEntryDerivative
    {A : E → Matrix (Fin n) (Fin n) κ} {z : E}
    {d : Fin n → Fin n → E →L[ℝ] κ}
    (hA : ∀ a b, HasFDerivAt (fun x => A x a b) (d a b) z)
    (hunit : IsUnit (A z)) (i j : Fin n) :
    HasFDerivAt (fun x => (A x)⁻¹ i j)
      (-∑ a, ∑ b, ((A z)⁻¹ i a * (A z)⁻¹ b j) • d a b) z := by
  let D := (assembleEntries (n := n) (κ := κ)).comp
    (ContinuousLinearMap.pi fun p : Fin n × Fin n => d p.1 p.2)
  have hmat : HasFDerivAt A D z :=
    (assembleEntries (n := n) (κ := κ)).hasFDerivAt.comp z
      (hasFDerivAt_pi.mpr fun p => hA p.1 p.2)
  obtain ⟨u, hu⟩ := hunit
  have hinv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Matrix (Fin n) (Fin n) κ)
        (A z)⁻¹ (A z)⁻¹) (A z) := by
    simpa only [coe_units_inv, hu] using hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hp := (entryProjection (κ := κ) i j).hasFDerivAt.comp z (hinv.comp z hmat)
  change HasFDerivAt (fun x => Ring.inverse (A x) i j) _ z at hp
  simp only [← nonsing_inv_eq_ringInverse] at hp
  apply hp.congr_fderiv
  ext v
  simp only [_root_.neg_apply, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  change (-((A z)⁻¹ * D v * (A z)⁻¹)) i j = _
  simp only [neg_apply, mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  change (A z)⁻¹ i a * d a b v * (A z)⁻¹ b j =
    ((A z)⁻¹ i a * (A z)⁻¹ b j) * d a b v
  ac_rfl

end

/-- A smooth matrix field has smooth inverse entries wherever it is a unit.

This within-set statement works for any set `W`; in particular it needs no assumptions on
`A` outside an open chart domain. -/
public theorem contDiffOn_inverse_entries
    {A : E → Matrix (Fin n) (Fin n) κ} {W : Set E}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun z => A z i j) W)
    (hunit : ∀ z ∈ W, IsUnit (A z)) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => (A z)⁻¹ i j) W :=
  smoothInverse hA hunit i j

/-- Pointwise real derivative of an inverse entry, with the input derivatives specified
entrywise. Invertibility is needed only at the base point. -/
public theorem hasFDerivAt_inverse_entry
    {A : E → Matrix (Fin n) (Fin n) κ} {z : E}
    {d : Fin n → Fin n → E →L[ℝ] κ}
    (hA : ∀ a b, HasFDerivAt (fun x => A x a b) (d a b) z)
    (hunit : IsUnit (A z)) (i j : Fin n) :
    HasFDerivAt (fun x => (A x)⁻¹ i j)
      (-∑ a, ∑ b, ((A z)⁻¹ i a * (A z)⁻¹ b j) • d a b) z :=
  inverseEntryDerivative hA hunit i j

/-- Evaluating the real Fréchet derivative gives the usual ordered double-sum formula. -/
public theorem fderiv_inverse_entry_apply
    {A : E → Matrix (Fin n) (Fin n) κ} {z : E}
    (hA : ∀ a b, DifferentiableAt ℝ (fun x => A x a b) z)
    (hunit : IsUnit (A z)) (i j : Fin n) (v : E) :
    fderiv ℝ (fun x => (A x)⁻¹ i j) z v =
      -∑ a, ∑ b, (A z)⁻¹ i a * fderiv ℝ (fun x => A x a b) z v * (A z)⁻¹ b j := by
  rw [(hasFDerivAt_inverse_entry (fun a b => (hA a b).hasFDerivAt) hunit i j).fderiv]
  simp only [_root_.neg_apply, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ac_rfl

/-- Open-domain smoothness suffices for the ordinary derivative formula at an interior point.
No extension of the matrix field through singular points outside the domain is required. -/
public theorem fderiv_inverse_entry_apply_of_contDiffOn
    {A : E → Matrix (Fin n) (Fin n) κ} {W : Set E} {z : E}
    (hW : IsOpen W) (hz : z ∈ W)
    (hA : ∀ a b, ContDiffOn ℝ ∞ (fun x => A x a b) W)
    (hunit : IsUnit (A z)) (i j : Fin n) (v : E) :
    fderiv ℝ (fun x => (A x)⁻¹ i j) z v =
      -∑ a, ∑ b, (A z)⁻¹ i a * fderiv ℝ (fun x => A x a b) z v * (A z)⁻¹ b j := by
  apply fderiv_inverse_entry_apply _ hunit
  intro a b
  exact ((hA a b) z hz).contDiffAt (hW.mem_nhds hz) |>.differentiableAt (by simp)

end Matrix
