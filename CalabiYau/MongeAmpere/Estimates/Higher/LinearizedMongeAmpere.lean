module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Complex.Schauder
import CalabiYau.Geometry.Complex.Forms.Positive

/-!
# Chartwise linearization of the complex Monge–Ampère equation

This module contains the finite-dimensional determinant differentiation and chart-coordinate
identities used by the higher-order Schauder step. The final public theorem is the source-faithful
linearized equation for a first real directional derivative of a smooth Monge–Ampère solution.
The matrix-calculus and Hessian-symmetry lemmas are private implementation details.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics* (GSM 152), §3.3, proof of
Proposition 3.11, p. 47; the logarithmic determinant derivative is the standard matrix identity
`D log det B = tr(B⁻¹ DB)`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]
private theorem hasDerivAt_det_one_add_smul (M : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun z : ℂ ↦ (1 + z • M).det) M.trace 0 := by
  let P : Polynomial ℂ :=
    (1 + (Polynomial.X : Polynomial ℂ) • M.map (Polynomial.C : ℂ →+* Polynomial ℂ)).det
  have hP : HasDerivAt (fun z : ℂ ↦ P.eval z) (P.derivative.eval 0) 0 := P.hasDerivAt 0
  have htrace : P.derivative.eval 0 = M.trace := by
    simpa [P] using Matrix.derivative_det_one_add_X_smul M
  have heval : (fun z : ℂ ↦ P.eval z) = fun z ↦ (1 + z • M).det := by
    funext z
    simp only [P, Matrix.det_apply', Polynomial.eval_finsetSum, Polynomial.eval_prod,
      Polynomial.eval_mul, Polynomial.eval_intCast]
    apply Finset.sum_congr rfl
    intro σ hσ
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    simp [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : σ i = i <;> simp [h] <;> ring
  rw [htrace] at hP
  exact hP.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heval.symm)

private theorem hasDerivAt_det_add_smul {A H : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    HasDerivAt (fun t : ℝ ↦ (A + t • H).det) (A.det * (A⁻¹ * H).trace) 0 := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  let B := A⁻¹ * H
  have hline := (hasDerivAt_det_one_add_smul B).comp_ofReal
  have hprod : HasDerivAt (fun t : ℝ ↦ A.det * (1 + (t : ℂ) • B).det)
      (A.det * B.trace) 0 := hline.const_mul A.det
  have hfactor (t : ℝ) : (A + t • H).det = A.det * (1 + (t : ℂ) • B).det := by
    have hAB : A * (A⁻¹ * H) = H := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hdet, Matrix.one_mul]
    have htsmul : t • H = (t : ℂ) • H := by ext i j; simp
    have hmat : A + t • H = A * (1 + (t : ℂ) • B) := by
      calc
        A + t • H = A + (t : ℂ) • H := by rw [htsmul]
        _ = A + (t : ℂ) • (A * (A⁻¹ * H)) := by rw [hAB]
        _ = A * (1 + (t : ℂ) • B) := by simp [B, Matrix.mul_add, hAB]
    rw [hmat, Matrix.det_mul]
  have hfunc : (fun t : ℝ ↦ (A + t • H).det) =
      fun t : ℝ ↦ A.det * (1 + (t : ℂ) • B).det := funext hfactor
  simpa [B] using hprod.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfunc)

private theorem real_hasDerivAt_log_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt Real.log x⁻¹ x := by
  let f : EuclideanSpace ℂ (Fin 1) → ℝ := fun z ↦ ‖z‖ ^ 2
  let θ : EuclideanSpace ℂ (Fin 1) [⋀^Fin 2]→L[ℝ] ℝ :=
    ddbar (n := 1) f (0 : EuclideanSpace ℂ (Fin 1))
  have hf : ContDiffAt ℝ 2 f (0 : EuclideanSpace ℂ (Fin 1)) := by
    exact contDiffAt_id.norm_sq ℝ
  have hω₁₁ : θ.IsOneOne := isOneOne_ddbar hf
  have hcoeff : θ.coeffMatrix = 1 := by
    change complexHessian f (0 : EuclideanSpace ℂ (Fin 1)) = 1
    exact complexHessian_normSq (0 : EuclideanSpace ℂ (Fin 1))
  have hω : θ.IsPositive := by
    apply (isPositive_iff (α := θ)).2
    exact ⟨hω₁₁, by rw [hcoeff]; exact Matrix.PosDef.one⟩
  have hα : (x • θ).IsPositive := hω.smul hx
  have hrel (t : ℝ) : relDet θ (x • θ + t • θ) = x + t := by
    rw [← add_smul, relDet_smul hω, relDet_self hω]
    simp
  have hlog := hasDerivAt_log_relDet hω hα hω₁₁ (α := x • θ) (β := θ)
  have hlog' : HasDerivAt (fun t : ℝ ↦ Real.log (x + t))
      (relTrace (x • θ) θ) 0 := by
    have heq : (fun t : ℝ ↦ Real.log (relDet θ (x • θ + t • θ))) =
        fun t ↦ Real.log (x + t) := funext fun t ↦ congrArg Real.log (hrel t)
    exact hlog.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq.symm)
  have hrelTrace : relTrace (x • θ) θ = x⁻¹ := by
    have heq : θ = x⁻¹ • (x • θ) := by
      simp [smul_smul, hx.ne']
    nth_rewrite 2 [heq]
    rw [relTrace_smul, relTrace_self hα]
    simp
  have htrans : HasDerivAt (fun y : ℝ ↦ y - x) 1 x := by
    simpa using (hasDerivAt_id x).sub_const x
  have hcomp := hlog'.comp_of_eq x htrans (by simp)
  simpa [Function.comp_def, add_sub_cancel_left, hrelTrace] using hcomp

private theorem hasDerivAt_log_det_add_smul {A H : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) :
    HasDerivAt (fun t : ℝ ↦ Real.log (RCLike.re (A + t • H).det))
      (RCLike.re (A⁻¹ * H).trace) 0 := by
  have hdetpos : 0 < A.det := hA.det_pos
  have hre : 0 < RCLike.re A.det := (RCLike.pos_iff.mp hdetpos).1
  have him : RCLike.im A.det = 0 := (RCLike.pos_iff.mp hdetpos).2
  have hdet := hasDerivAt_det_add_smul hA (H := H)
  have hCLM : HasFDerivAt Complex.reCLM Complex.reCLM A.det := Complex.reCLM.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ ↦ RCLike.re (A + t • H).det)
      (RCLike.re (A.det * (A⁻¹ * H).trace)) 0 := by
    simpa [Function.comp_def, Complex.reCLM_apply] using
      hCLM.comp_hasDerivAt_of_eq 0 hdet (by simp)
  have hlog := (real_hasDerivAt_log_of_pos hre).comp_of_eq 0 hline (by simp)
  have hmul : RCLike.re (A.det * (A⁻¹ * H).trace) =
      RCLike.re A.det * RCLike.re (A⁻¹ * H).trace := by
    rw [RCLike.mul_re]
    simp [him]
  have hcancel : (RCLike.re A.det)⁻¹ * RCLike.re (A.det * (A⁻¹ * H).trace) =
      RCLike.re (A⁻¹ * H).trace := by
    rw [hmul]
    field_simp [hre.ne']
  have hlog' := hlog.congr_deriv hcancel
  exact hlog'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq rfl)

private theorem hasDerivAt_det_of_entrywise {A H : Matrix (Fin n) (Fin n) ℂ}
    {F : ℝ → Matrix (Fin n) (Fin n) ℂ} {t : ℝ}
    (hF : ∀ i j, HasDerivAt (fun s ↦ F s i j) (H i j) t) (hFt : F t = A) :
    HasDerivAt (fun s ↦ (F s).det)
      (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * H (σ i) i) t := by
  have hprod (σ : Equiv.Perm (Fin n)) :
      HasDerivAt (fun s : ℝ ↦ ∏ i, F s (σ i) i)
        (∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * H (σ i) i) t := by
    convert HasDerivAt.finsetProd
      (u := Finset.univ) (f := fun i s ↦ F s (σ i) i)
      (f' := fun i ↦ H (σ i) i) (fun i hi ↦ hF (σ i) i) using 1 <;>
      first | rfl | apply Subsingleton.elim |
        (funext s; exact (Fintype.prod_apply s (fun i s ↦ F s (σ i) i)).symm) |
        try simp [hFt, smul_eq_mul]
  have hterm (σ : Equiv.Perm (Fin n)) :
      HasDerivAt (fun s : ℝ ↦ ((Equiv.Perm.sign σ : ℤ) : ℂ) *
          (∏ i, F s (σ i) i))
        (((Equiv.Perm.sign σ : ℤ) : ℂ) *
          ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * H (σ i) i) t :=
    (hprod σ).const_mul _
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (A := fun σ s ↦ ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, F s (σ i) i)
    (A' := fun σ ↦ ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A (σ j) j) * H (σ i) i)
    (fun σ hσ ↦ hterm σ)
  have hdet : (fun s : ℝ ↦ (F s).det) =
      fun s ↦ ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, F s (σ i) i := by
    funext s
    exact Matrix.det_apply' (F s)
  exact hsum.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hdet)

private theorem hasDerivAt_adjugate_entry_of_entrywise
    {A H : Matrix (Fin n) (Fin n) ℂ} {F : ℝ → Matrix (Fin n) (Fin n) ℂ} {t : ℝ}
    (hF : ∀ i j, HasDerivAt (fun s ↦ F s i j) (H i j) t) (hFt : F t = A)
    (i j : Fin n) :
    HasDerivAt (fun s ↦ (F s).adjugate i j)
      (deriv (fun s ↦ (F s).adjugate i j) t) t := by
  let Q : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s ↦
    (F s).updateRow j (Pi.single i 1)
  let H' : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a b ↦ if a = j then 0 else H a b
  have hQ (a b : Fin n) : HasDerivAt (fun s ↦ Q s a b) (H' a b) t := by
    by_cases ha : a = j
    · subst a
      let c : ℂ := if b = i then 1 else 0
      have hEq : (fun s ↦ Q s j b) = fun _ : ℝ ↦ c := by
        funext s
        simp [Q, c, Matrix.updateRow_apply, Pi.single_apply]
      have hconst : HasDerivAt (fun _ : ℝ ↦ c) 0 t := hasDerivAt_const t c
      have h := hconst.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hEq)
      exact h.congr_deriv (by simp [H'])
    · have hEq : (fun s ↦ Q s a b) = fun s ↦ F s a b := by
        funext s
        simp [Q, Matrix.updateRow_apply, ha]
      have h := (hF a b).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hEq)
      exact h.congr_deriv (by simp [H', ha])
  have hQt : Q t = A.updateRow j (Pi.single i 1) := by
    ext a b
    simp [Q, hFt]
  have hdet := hasDerivAt_det_of_entrywise (F := Q) (H := H') hQ hQt
  have hAdjEq : (fun s ↦ (F s).adjugate i j) = fun s ↦ (Q s).det := by
    funext s
    exact Matrix.adjugate_apply (F s) i j
  have hAdj := hdet.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hAdjEq)
  exact hAdj.congr_deriv hAdj.deriv.symm

private theorem hasDerivAt_matrix_inv_entry_of_entrywise
    {A H : Matrix (Fin n) (Fin n) ℂ} {F : ℝ → Matrix (Fin n) (Fin n) ℂ} {t : ℝ}
    (hF : ∀ i j, HasDerivAt (fun s ↦ F s i j) (H i j) t) (hFt : F t = A)
    (hdet : A.det ≠ 0) (i j : Fin n) :
    HasDerivAt (fun s ↦ (F s)⁻¹ i j)
      (deriv (fun s ↦ (F s).det⁻¹ * (F s).adjugate i j) t) t := by
  have hdetLine := hasDerivAt_det_of_entrywise hF hFt
  have hdetLineInv := hdetLine.inv (by simpa [hFt] using hdet)
  have hAdjLine := hasDerivAt_adjugate_entry_of_entrywise hF hFt i j
  have hProd := hdetLineInv.mul hAdjLine
  have hEq : (fun s ↦ (F s)⁻¹ i j) = fun s ↦ (F s).det⁻¹ * (F s).adjugate i j := by
    funext s
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
    simp [Matrix.smul_apply, smul_eq_mul]
  have hInv := hProd.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hEq)
  exact hInv.congr_deriv hProd.deriv.symm

private theorem hasDerivAt_det_of_entrywise_posDef {A H : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {F : ℝ → Matrix (Fin n) (Fin n) ℂ} {t : ℝ}
    (hF : ∀ i j, HasDerivAt (fun s ↦ F s i j) (H i j) t) (hFt : F t = A) :
    HasDerivAt (fun s ↦ (F s).det) (A.det * (A⁻¹ * H).trace) t := by
  let G : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s ↦ F (t + s)
  have hshift : HasDerivAt (fun s : ℝ ↦ t + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add t
  have hG (i j : Fin n) : HasDerivAt (fun s : ℝ ↦ G s i j) (H i j) 0 := by
    have h := HasDerivAt.scomp_of_eq 0 (hF i j) hshift (by simp)
    simpa [G, Function.comp_def] using h
  have hG0 : G 0 = A := by
    simpa [G] using hFt
  have hGdet := hasDerivAt_det_of_entrywise hG hG0
  let L : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s ↦ A + s • H
  have hL (i j : Fin n) : HasDerivAt (fun s : ℝ ↦ L s i j) (H i j) 0 := by
    have hcast : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).comp_ofReal
    have hmul := hcast.mul_const (H i j)
    have h := (hasDerivAt_const (0 : ℝ) (A i j)).add hmul
    have heq : (fun s : ℝ ↦ L s i j) =
        (fun s : ℝ ↦ A i j + (s : ℂ) * H i j) := by
      funext s
      simp [L, Matrix.add_apply, Complex.real_smul]
    exact (h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq)).congr_deriv (by simp)
  have hL0 : L 0 = A := by simp [L]
  have hLdet := hasDerivAt_det_of_entrywise hL hL0
  have hline := hasDerivAt_det_add_smul hA (H := H)
  have hD := hLdet.unique hline
  have hGdet' := hGdet.congr_deriv hD
  have hback : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hcomp := HasDerivAt.scomp_of_eq t hGdet' hback (by simp)
  simpa [G, Function.comp_def, add_sub_cancel_left] using hcomp

private theorem hasDerivAt_log_det_of_entrywise_posDef {A H : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) {F : ℝ → Matrix (Fin n) (Fin n) ℂ} {t : ℝ}
    (hF : ∀ i j, HasDerivAt (fun s ↦ F s i j) (H i j) t) (hFt : F t = A) :
    HasDerivAt (fun s ↦ Real.log (RCLike.re (F s).det))
      (RCLike.re (A⁻¹ * H).trace) t := by
  have hdet := hasDerivAt_det_of_entrywise_posDef hA hF hFt
  have hdetpos : 0 < A.det := hA.det_pos
  have hre : 0 < RCLike.re A.det := (RCLike.pos_iff.mp hdetpos).1
  have him : RCLike.im A.det = 0 := (RCLike.pos_iff.mp hdetpos).2
  have hCLM : HasFDerivAt Complex.reCLM Complex.reCLM A.det := Complex.reCLM.hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ ↦ RCLike.re (F s).det)
      (RCLike.re (A.det * (A⁻¹ * H).trace)) t := by
    simpa [Function.comp_def, Complex.reCLM_apply] using
      hCLM.comp_hasDerivAt_of_eq t hdet (by simp [hFt])
  have hlog := (real_hasDerivAt_log_of_pos hre).comp_of_eq t hline (by simp [hFt])
  have hmul : RCLike.re (A.det * (A⁻¹ * H).trace) =
      RCLike.re A.det * RCLike.re (A⁻¹ * H).trace := by
    rw [RCLike.mul_re]
    simp [him]
  have hcancel : (RCLike.re A.det)⁻¹ *
      RCLike.re (A.det * (A⁻¹ * H).trace) = RCLike.re (A⁻¹ * H).trace := by
    rw [hmul]
    field_simp [hre.ne']
  have hlog' := hlog.congr_deriv hcancel
  exact hlog'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq rfl)

private theorem hasDerivAt_log_det_along_line {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : E → Matrix (Fin n) (Fin n) ℂ}
    {D : Matrix (Fin n) (Fin n) (E →L[ℝ] ℂ)} {H : Matrix (Fin n) (Fin n) ℂ}
    {x v : E} (hF : (F x).PosDef) (hH : ∀ i j, H i j = D i j v)
    (hderiv : ∀ i j, HasFDerivAt (fun y : E ↦ F y i j) (D i j) x) :
    HasDerivAt (fun t : ℝ ↦ Real.log (RCLike.re (F (x + t • v)).det))
      (RCLike.re ((F x)⁻¹ * H).trace) 0 := by
  let Fline : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t ↦ F (x + t • v)
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hentry (i j : Fin n) :
      HasDerivAt (fun t : ℝ ↦ Fline t i j) (H i j) 0 := by
    have h := (hderiv i j).comp_hasDerivAt_of_eq 0 hline (by simp)
    have h' : HasDerivAt (fun t : ℝ ↦ Fline t i j) (D i j v) 0 := by
      simpa [Fline, Function.comp_def] using h
    exact h'.congr_deriv (hH i j).symm
  have h0 : Fline 0 = F x := by simp [Fline]
  have hlog := hasDerivAt_log_det_of_entrywise_posDef hF hentry h0
  simpa [Fline] using hlog

private theorem hasDerivAt_log_det_contDiff_along_line {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → Matrix (Fin n) (Fin n) ℂ}
    {H : Matrix (Fin n) (Fin n) ℂ} {x v : E} (hF : (F x).PosDef)
    (hH : ∀ i j, H i j = fderiv ℝ (fun y : E ↦ F y i j) x v)
    (hcont : ∀ i j, ContDiffAt ℝ 1 (fun y : E ↦ F y i j) x) :
    HasDerivAt (fun t : ℝ ↦ Real.log (RCLike.re (F (x + t • v)).det))
      (RCLike.re ((F x)⁻¹ * H).trace) 0 := by
  let D : Matrix (Fin n) (Fin n) (E →L[ℝ] ℂ) :=
    fun i j ↦ fderiv ℝ (fun y : E ↦ F y i j) x
  have hderiv (i j : Fin n) :
      HasFDerivAt (fun y : E ↦ F y i j) (D i j) x := by
    exact ((hcont i j).differentiableAt (by norm_num)).hasFDerivAt
  have hH' : ∀ i j, H i j = D i j v := by
    intro i j
    simpa [D] using hH i j
  exact hasDerivAt_log_det_along_line hF hH' hderiv

private theorem hasDerivAt_log_det_ratio_of_entrywise
    {A B H K : Matrix (Fin n) (Fin n) ℂ}
    {F J : ℝ → Matrix (Fin n) (Fin n) ℂ} {G : ℝ → ℝ}
    (hA : A.PosDef) (hB : B.PosDef)
    (hF : ∀ i j, HasDerivAt (fun t ↦ F t i j) (H i j) 0) (hF0 : F 0 = A)
    (hJ : ∀ i j, HasDerivAt (fun t ↦ J t i j) (K i j) 0) (hJ0 : J 0 = B)
    (hEq : (fun t : ℝ ↦ G t) =ᶠ[nhds 0]
      fun t ↦ Real.log (RCLike.re (F t).det) - Real.log (RCLike.re (J t).det)) :
    HasDerivAt G
      (RCLike.re (A⁻¹ * H).trace - RCLike.re (B⁻¹ * K).trace) 0 := by
  have hFlog := hasDerivAt_log_det_of_entrywise_posDef hA hF hF0
  have hJlog := hasDerivAt_log_det_of_entrywise_posDef hB hJ hJ0
  have hsub : HasDerivAt (fun t : ℝ ↦
      Real.log (RCLike.re (F t).det) - Real.log (RCLike.re (J t).det))
      (RCLike.re (A⁻¹ * H).trace - RCLike.re (B⁻¹ * K).trace) 0 := by
    exact hFlog.sub hJlog
  exact hsub.congr_of_eventuallyEq hEq

omit [T2Space M] [CompactSpace M] in
private theorem chart_log_det_ratio_eventually (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M) {z v : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    (fun t : ℝ ↦ G ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (z + t • v))) =ᶠ[nhds 0]
      fun t ↦ Real.log (RCLike.re
        (ω₀.metricInChart x (z + t • v) +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)
            (z + t • v)).det) -
        Real.log (RCLike.re (ω₀.metricInChart x (z + t • v)).det) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let F : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun u ↦
    ω₀.metricInChart x u + complexHessian (φ ∘ e.symm) u
  let J : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun u ↦
    ω₀.metricInChart x u
  have hpath : ContinuousAt (fun t : ℝ ↦ z + t • v) 0 := by fun_prop
  have htarget : ∀ᶠ t : ℝ in nhds 0,
      z + t • v ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by
    have hz0 : (fun t : ℝ ↦ z + t • v) 0 ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target := by simpa using hz
    exact hpath.eventually ((isOpen_extChartAt_target x).mem_nhds hz0)
  filter_upwards [htarget] with t ht
  let y := e.symm (z + t • v)
  have hy : y ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by
    rw [← extChartAt_source (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))]
    exact e.map_target ht
  have hma : Real.exp (G y) = RCLike.re (F (z + t • v)).det /
      RCLike.re (J (z + t • v)).det := by
    have hcoord : e (e.symm (z + t • v)) = z + t • v := e.right_inv ht
    have hchart := mongeAmpere_eq_inChart (ω₀ := ω₀) hφ x hy
    rw [hcoord] at hchart
    calc
      Real.exp (G y) = ω₀.mongeAmpere φ y := (hsol.2 y).symm
      _ = RCLike.re (F (z + t • v)).det / RCLike.re (J (z + t • v)).det := by
        simpa [F, J, y, e] using hchart
  have hnumPos : 0 < RCLike.re (F (z + t • v)).det := by
    have hpos : (F (z + t • v)).PosDef := by
      have hpos' := (ω₀.perturb φ hsol.1).posDef_metricInChart x ht
      rw [KahlerForm.metricInChart_perturb hsol.1 x ht] at hpos'
      simpa [F, e] using hpos'
    exact (RCLike.pos_iff.mp hpos.det_pos).1
  have hdenPos : 0 < RCLike.re (J (z + t • v)).det := by
    have hpos : (J (z + t • v)).PosDef := by
      simpa [J] using ω₀.posDef_metricInChart x ht
    exact (RCLike.pos_iff.mp hpos.det_pos).1
  have hlog := congrArg Real.log hma
  rw [Real.log_exp, Real.log_div hnumPos.ne' hdenPos.ne'] at hlog
  simpa [F, J, y, e] using hlog

private theorem hasDerivAt_of_eventually_log_det_ratio {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F J : E → Matrix (Fin n) (Fin n) ℂ} {G : E → ℝ}
    {DF DJ : Matrix (Fin n) (Fin n) (E →L[ℝ] ℂ)}
    {H K : Matrix (Fin n) (Fin n) ℂ} {x v : E}
    (hFpos : (F x).PosDef) (hJpos : (J x).PosDef)
    (hH : ∀ i j, H i j = DF i j v) (hK : ∀ i j, K i j = DJ i j v)
    (hF : ∀ i j, HasFDerivAt (fun y : E ↦ F y i j) (DF i j) x)
    (hJ : ∀ i j, HasFDerivAt (fun y : E ↦ J y i j) (DJ i j) x)
    (hEq : (fun t : ℝ ↦ G (x + t • v)) =ᶠ[nhds 0]
      fun t ↦ Real.log (RCLike.re (F (x + t • v)).det) -
        Real.log (RCLike.re (J (x + t • v)).det)) :
    HasDerivAt (fun t : ℝ ↦ G (x + t • v))
      (RCLike.re ((F x)⁻¹ * H).trace - RCLike.re ((J x)⁻¹ * K).trace) 0 := by
  let Fline : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t ↦ F (x + t • v)
  let Jline : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t ↦ J (x + t • v)
  have hpath : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hFline (i j : Fin n) : HasDerivAt (fun t : ℝ ↦ Fline t i j) (H i j) 0 := by
    have h := (hF i j).comp_hasDerivAt_of_eq 0 hpath (by simp)
    have h' : HasDerivAt (fun t : ℝ ↦ Fline t i j) (DF i j v) 0 := by
      simpa [Fline, Function.comp_def] using h
    exact h'.congr_deriv (hH i j).symm
  have hJline (i j : Fin n) : HasDerivAt (fun t : ℝ ↦ Jline t i j) (K i j) 0 := by
    have h := (hJ i j).comp_hasDerivAt_of_eq 0 hpath (by simp)
    have h' : HasDerivAt (fun t : ℝ ↦ Jline t i j) (DJ i j v) 0 := by
      simpa [Jline, Function.comp_def] using h
    exact h'.congr_deriv (hK i j).symm
  have hF0 : Fline 0 = F x := by simp [Fline]
  have hJ0 : Jline 0 = J x := by simp [Jline]
  have hEq' : (fun t : ℝ ↦ G (x + t • v)) =ᶠ[nhds 0]
      fun t ↦ Real.log (RCLike.re (Fline t).det) -
        Real.log (RCLike.re (Jline t).det) := by
    simpa [Fline, Jline] using hEq
  have h := hasDerivAt_log_det_ratio_of_entrywise hFpos hJpos hFline hF0 hJline hJ0 hEq'
  simpa [Fline, Jline] using h

omit [T2Space M] [CompactSpace M] in
private theorem hasDerivAt_G_along_chart_line (ω₀ : KahlerForm n M) {G φ : M → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M) {z v : EuclideanSpace ℂ (Fin n)}
    {H K : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hH : ∀ j k, H j k = fderiv ℝ
      (fun u ↦ ω₀.metricInChart x u j k +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) u j k) z v)
    (hK : ∀ j k, K j k = fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v)
    (hFcont : ∀ j k, ContDiffAt ℝ 1
      (fun u ↦ ω₀.metricInChart x u j k +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) u j k) z)
    (hJcont : ∀ j k, ContDiffAt ℝ 1 (fun u ↦ ω₀.metricInChart x u j k) z) :
    HasDerivAt (fun t : ℝ ↦
      G ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (z + t • v)))
      (RCLike.re (((ω₀.metricInChart x z +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ * H).trace) -
        RCLike.re ((ω₀.metricInChart x z)⁻¹ * K).trace) 0 := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hFpos : (ω₀.metricInChart x z + complexHessian (φ ∘ e.symm) z).PosDef := by
    have hp := (ω₀.perturb φ hsol.1).posDef_metricInChart x hz
    rw [KahlerForm.metricInChart_perturb hsol.1 x hz] at hp
    exact hp
  have hJpos : (ω₀.metricInChart x z).PosDef := ω₀.posDef_metricInChart x hz
  have hFderiv (j k : Fin n) : HasFDerivAt
      (fun u ↦ ω₀.metricInChart x u j k + complexHessian (φ ∘ e.symm) u j k)
      (fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k +
        complexHessian (φ ∘ e.symm) u j k) z) z := by
    exact ((hFcont j k).differentiableAt (by norm_num)).hasFDerivAt
  have hJderiv (j k : Fin n) : HasFDerivAt
      (fun u ↦ ω₀.metricInChart x u j k) (fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z) z := by
    exact ((hJcont j k).differentiableAt (by norm_num)).hasFDerivAt
  have hEq := chart_log_det_ratio_eventually ω₀ hφ hsol x (z := z) (v := v) hz
  have hH' : ∀ j k, H j k =
      (fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k +
        complexHessian (φ ∘ e.symm) u j k) z) v := by
    simpa [e] using hH
  have hK' : ∀ j k, K j k = (fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z) v := hK
  have hderiv := hasDerivAt_of_eventually_log_det_ratio
    (E := EuclideanSpace ℂ (Fin n))
    (F := fun u ↦ ω₀.metricInChart x u + complexHessian (φ ∘ e.symm) u)
    (J := fun u ↦ ω₀.metricInChart x u)
    (G := fun u ↦ G (e.symm u))
    (DF := fun j k ↦ fderiv ℝ
      (fun u ↦ ω₀.metricInChart x u j k + complexHessian (φ ∘ e.symm) u j k) z)
    (DJ := fun j k ↦ fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z)
    (H := H) (K := K) (x := z) (v := v) hFpos hJpos hH' hK'
    hFderiv hJderiv hEq
  simpa [e] using hderiv

private noncomputable def chartPerturbedMetricDirection (ω₀ : KahlerForm n M)
    (φ : M → ℝ) (x : M) (z v : EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun j k ↦ fderiv ℝ
    (fun u ↦ ω₀.metricInChart x u j k +
      complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) u j k) z v

private noncomputable def chartBackgroundMetricDirection (ω₀ : KahlerForm n M)
    (x : M) (z v : EuclideanSpace ℂ (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k ↦ fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v

omit [T2Space M] [CompactSpace M] in
private theorem hasDerivAt_G_along_chart_line_of_smooth (ω₀ : KahlerForm n M)
    {G φ : M → ℝ} (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M) {z v : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    HasDerivAt (fun t : ℝ ↦
      G ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (z + t • v)))
      (RCLike.re (((ω₀.metricInChart x z +
        complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ *
          chartPerturbedMetricDirection ω₀ φ x z v).trace) -
        RCLike.re ((ω₀.metricInChart x z)⁻¹ * chartBackgroundMetricDirection ω₀ x z v).trace) 0 := by
  let I0 := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
  let e := extChartAt I0 x
  let H := chartPerturbedMetricDirection ω₀ φ x z v
  let K := chartBackgroundMetricDirection ω₀ x z v
  have hH : ∀ j k, H j k = fderiv ℝ
      (fun u ↦ ω₀.metricInChart x u j k +
        complexHessian (φ ∘ e.symm) u j k) z v := by
    intro j k
    rfl
  have hK : ∀ j k, K j k = fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v := by
    intro j k
    rfl
  have hφon : ContMDiffOn I0 𝓘(ℝ) ∞ φ Set.univ := contMDiffOn_univ.mpr hφ
  have hφchart : ContDiffOn ℝ ∞ (φ ∘ e.symm) e.target := by
    have h := hφon.comp (contMDiffOn_extChartAt_symm x) (by intro u hu; simp)
    exact h.contDiffOn
  have hddbar : ContDiffOn ℝ ∞ (ddbar (φ ∘ e.symm)) e.target :=
    ContDiffOn.ddbar (isOpen_extChartAt_target x) hφchart
  have hcomplexEntry (j k : Fin n) :
      ContDiffOn ℝ ∞ (fun u ↦ complexHessian (φ ∘ e.symm) u j k) e.target := by
    let f₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun u ↦
      ddbar (φ ∘ e.symm) u ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]
    let f₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun u ↦
      ddbar (φ ∘ e.symm) u ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]
    have hf₁ : ContDiffOn ℝ ∞ f₁ e.target := by
      dsimp [f₁]
      exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]).contDiff).comp_contDiffOn
          hddbar
    have hf₂ : ContDiffOn ℝ ∞ f₂ e.target := by
      dsimp [f₂]
      exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]).contDiff).comp_contDiffOn hddbar
    have hf₁c : ContDiffOn ℝ ∞ (fun u ↦ (f₁ u : ℂ)) e.target := by
      convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₁ using 1
      ext u
      simp [f₁, Complex.ofRealCLM_apply]
    have hf₂c : ContDiffOn ℝ ∞ (fun u ↦ (f₂ u : ℂ)) e.target := by
      convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₂ using 1
      ext u
      simp [f₂, Complex.ofRealCLM_apply]
    have hnum : ContDiffOn ℝ ∞
        (fun u ↦ (f₁ u : ℂ) - Complex.I * (f₂ u : ℂ)) e.target := by
      exact hf₁c.sub (contDiffOn_const.mul hf₂c)
    change ContDiffOn ℝ ∞
      (fun u ↦ ((f₁ u : ℂ) - Complex.I * (f₂ u : ℂ)) / 2) e.target
    exact hnum.div_const (2 : ℂ)
  have hFcont (j k : Fin n) : ContDiffAt ℝ 1
      (fun u ↦ ω₀.metricInChart x u j k + complexHessian (φ ∘ e.symm) u j k) z := by
    have h := (ω₀.contDiffOn_metricInChart x j k).add (hcomplexEntry j k)
    exact (h.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le (by norm_num)
  have hJcont (j k : Fin n) : ContDiffAt ℝ 1
      (fun u ↦ ω₀.metricInChart x u j k) z := by
    exact (ω₀.contDiffOn_metricInChart x j k).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz) |>.of_le (by norm_num)
  exact hasDerivAt_G_along_chart_line ω₀ hφ hsol x hz hH hK hFcont hJcont

private theorem fderiv_second_apply_comm {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z a b c : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c =
      fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b a) z c := by
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w a b
  let r : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w b a
  have hfd1 : ContDiffAt ℝ 2 (fderiv ℝ f) z := hf.fderiv_right (m := 2) (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) z :=
    hfd1.fderiv_right (m := 1) (by norm_num)
  have hqcont : ContDiffAt ℝ 1 q z := by
    dsimp [q]
    exact (hfd2.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hrcont : ContDiffAt ℝ 1 r z := by
    dsimp [r]
    exact (hfd2.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hq : HasFDerivAt q (fderiv ℝ q z) z :=
    (hqcont.differentiableAt (by norm_num)).hasFDerivAt
  have hr : HasFDerivAt r (fderiv ℝ r z) z :=
    (hrcont.differentiableAt (by norm_num)).hasFDerivAt
  have hsymm := hf.eventually (by norm_num : (3 : ℕ∞ω) ≠ ∞)
  have heq : q =ᶠ[nhds z] r := by
    filter_upwards [hsymm] with w hw
    exact hw.isSymmSndFDerivAt (by norm_num) a b
  have hq' := hq.congr_of_eventuallyEq heq.symm
  have hderivEq : fderiv ℝ q z = fderiv ℝ r z := hq'.unique hr
  exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L c) hderivEq

private theorem fderiv_second_apply_comm_outer {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z a b c : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c =
      fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w c b) z a := by
  let F2 : EuclideanSpace ℂ (Fin n) →
      EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ :=
    fun w ↦ fderiv ℝ (fderiv ℝ f) w
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ F2 w a b
  let r : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ F2 w c b
  have hfd1 : ContDiffAt ℝ 2 (fderiv ℝ f) z := hf.fderiv_right (m := 2) (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 F2 z := by
    simpa [F2] using hfd1.fderiv_right (m := 1) (by norm_num)
  have hF2 : HasFDerivAt F2 (fderiv ℝ F2 z) z :=
    (hfd2.differentiableAt (by norm_num)).hasFDerivAt
  have hq := (hF2.clm_apply (hasFDerivAt_const a z)).clm_apply (hasFDerivAt_const b z)
  have hr := (hF2.clm_apply (hasFDerivAt_const c z)).clm_apply (hasFDerivAt_const b z)
  have hqder (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ q z u = (fderiv ℝ F2 z u a) b := by
    have hq' := hq.fderiv
    simpa [q, F2] using congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L u) hq'
  have hrder (u : EuclideanSpace ℂ (Fin n)) :
      fderiv ℝ r z u = (fderiv ℝ F2 z u c) b := by
    have hr' := hr.fderiv
    simpa [r, F2] using congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L u) hr'
  have hSymm : IsSymmSndFDerivAt ℝ (fderiv ℝ f) z :=
    hfd1.isSymmSndFDerivAt (by norm_num)
  have hthird : (fderiv ℝ F2 z c a) b = (fderiv ℝ F2 z a c) b := by
    exact congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L b) (hSymm c a)
  calc
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c = fderiv ℝ q z c := by
      rfl
    _ = (fderiv ℝ F2 z c a) b := hqder c
    _ = (fderiv ℝ F2 z a c) b := hthird
    _ = fderiv ℝ r z a := (hrder a).symm
    _ = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w c b) z a := by rfl

private theorem fderiv_second_apply_cyclic {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z a b c : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c =
      fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b c) z a := by
  calc
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a b) z c =
        fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b a) z c :=
      fderiv_second_apply_comm hf
    _ = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w c a) z b :=
      fderiv_second_apply_comm_outer hf
    _ = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w a c) z b :=
      fderiv_second_apply_comm hf
    _ = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b c) z a :=
      fderiv_second_apply_comm_outer hf

private theorem fderiv_second_directionalDerivative {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z a b v : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) :
    fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b v) z a =
      fderiv ℝ (fderiv ℝ (fun w ↦ fderiv ℝ f w v)) z a b := by
  let g : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ f w v
  let q : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w b v
  let r : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ g w b
  have hfd1 : ContDiffAt ℝ 2 (fderiv ℝ f) z := hf.fderiv_right (m := 2) (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ (fderiv ℝ f) w) z :=
    hfd1.fderiv_right (m := 1) (by norm_num)
  have hg : ContDiffAt ℝ 2 g z := by
    exact hfd1.clm_apply contDiffAt_const
  have hqcont : ContDiffAt ℝ 1 q z := by
    dsimp [q]
    exact (hfd2.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hrcont : ContDiffAt ℝ 1 r z := by
    exact hg.fderiv_right (m := 1) (by norm_num) |>.clm_apply contDiffAt_const
  have hq : HasFDerivAt q (fderiv ℝ q z) z :=
    (hqcont.differentiableAt (by norm_num)).hasFDerivAt
  have hr : HasFDerivAt r (fderiv ℝ r z) z :=
    (hrcont.differentiableAt (by norm_num)).hasFDerivAt
  have hsame : q =ᶠ[nhds z] r := by
    filter_upwards [hf.eventually (by norm_num : (3 : ℕ∞ω) ≠ ∞)] with w hw
    have hF1 : DifferentiableAt ℝ (fderiv ℝ f) w :=
      (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hconst : DifferentiableAt ℝ (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) w :=
      differentiableAt_const _
    have h := fderiv_clm_apply hF1 hconst
    change fderiv ℝ (fderiv ℝ f) w b v = fderiv ℝ g w b
    rw [h]
    simp
  have hq' := hq.congr_of_eventuallyEq hsame.symm
  have hderivEq : fderiv ℝ q z = fderiv ℝ r z := hq'.unique hr
  have hrg : fderiv ℝ r z a = fderiv ℝ (fderiv ℝ g) z a b := by
    have hG : DifferentiableAt ℝ (fderiv ℝ g) z :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [fderiv_clm_apply hG (differentiableAt_const b)]
    simp
  calc
    fderiv ℝ q z a = fderiv ℝ r z a := congrArg (fun L :
      EuclideanSpace ℂ (Fin n) →L[ℝ] ℝ ↦ L a) hderivEq
    _ = fderiv ℝ (fderiv ℝ g) z a b := hrg
    _ = fderiv ℝ (fderiv ℝ (fun w ↦ fderiv ℝ f w v)) z a b := by rfl

private theorem fderiv_complexHessian_direction {f : EuclideanSpace ℂ (Fin n) → ℝ}
    {z v : EuclideanSpace ℂ (Fin n)} (hf : ContDiffAt ℝ 3 f z) (j k : Fin n) :
    fderiv ℝ (fun w ↦ complexHessian f w j k) z v =
      complexHessian (fun w ↦ fderiv ℝ f w v) z j k := by
  let a : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let b : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single k 1
  let ia := Complex.I • a
  let ib := Complex.I • b
  let g : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ f w v
  let q₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w a b
  let q₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w ia ib
  let q₃ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w a ib
  let q₄ : EuclideanSpace ℂ (Fin n) → ℝ := fun w ↦ fderiv ℝ (fderiv ℝ f) w ia b
  let S : EuclideanSpace ℂ (Fin n) → ℂ := fun w ↦
    (4 : ℂ)⁻¹ * ((q₁ w : ℂ) + q₂ w + Complex.I * ((q₃ w : ℂ) - q₄ w))
  let D : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ := (4 : ℂ)⁻¹ •
    (Complex.ofRealCLM.comp (fderiv ℝ q₁ z) +
      Complex.ofRealCLM.comp (fderiv ℝ q₂ z) +
      Complex.I • (Complex.ofRealCLM.comp (fderiv ℝ q₃ z) -
        Complex.ofRealCLM.comp (fderiv ℝ q₄ z)))
  have hfd1 : ContDiffAt ℝ 2 (fderiv ℝ f) z := hf.fderiv_right (m := 2) (by norm_num)
  have hfd2 : ContDiffAt ℝ 1 (fun w ↦ fderiv ℝ (fderiv ℝ f) w) z :=
    hfd1.fderiv_right (m := 1) (by norm_num)
  have hg : ContDiffAt ℝ 2 g z :=
    hfd1.clm_apply (contDiffAt_const (x := z) (c := v))
  have hq₁ : HasFDerivAt q₁ (fderiv ℝ q₁ z) z := by
    have hc := (hfd2.clm_apply (contDiffAt_const (x := z) (c := a))).clm_apply
      (contDiffAt_const (x := z) (c := b))
    simpa [q₁] using (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hq₂ : HasFDerivAt q₂ (fderiv ℝ q₂ z) z := by
    have hc := (hfd2.clm_apply (contDiffAt_const (x := z) (c := ia))).clm_apply
      (contDiffAt_const (x := z) (c := ib))
    simpa [q₂] using (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hq₃ : HasFDerivAt q₃ (fderiv ℝ q₃ z) z := by
    have hc := (hfd2.clm_apply (contDiffAt_const (x := z) (c := a))).clm_apply
      (contDiffAt_const (x := z) (c := ib))
    simpa [q₃] using (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hq₄ : HasFDerivAt q₄ (fderiv ℝ q₄ z) z := by
    have hc := (hfd2.clm_apply (contDiffAt_const (x := z) (c := ia))).clm_apply
      (contDiffAt_const (x := z) (c := b))
    simpa [q₄] using (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hq₁c : HasFDerivAt (fun w ↦ (q₁ w : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ q₁ z)) z := by
    have hCLM : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (q₁ z) :=
      Complex.ofRealCLM.hasFDerivAt
    simpa [Function.comp_def] using HasFDerivAt.comp z hCLM hq₁
  have hq₂c : HasFDerivAt (fun w ↦ (q₂ w : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ q₂ z)) z := by
    have hCLM : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (q₂ z) :=
      Complex.ofRealCLM.hasFDerivAt
    simpa [Function.comp_def] using HasFDerivAt.comp z hCLM hq₂
  have hq₃c : HasFDerivAt (fun w ↦ (q₃ w : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ q₃ z)) z := by
    have hCLM : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (q₃ z) :=
      Complex.ofRealCLM.hasFDerivAt
    simpa [Function.comp_def] using HasFDerivAt.comp z hCLM hq₃
  have hq₄c : HasFDerivAt (fun w ↦ (q₄ w : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ q₄ z)) z := by
    have hCLM : HasFDerivAt Complex.ofRealCLM Complex.ofRealCLM (q₄ z) :=
      Complex.ofRealCLM.hasFDerivAt
    simpa [Function.comp_def] using HasFDerivAt.comp z hCLM hq₄
  have h34 := (hq₃c.sub hq₄c).const_mul Complex.I
  have h1234 := (hq₁c.add hq₂c).add h34
  have hdiv := h1234.const_mul (4 : ℂ)⁻¹
  have hS : HasFDerivAt S D z := by
    change HasFDerivAt (fun w : EuclideanSpace ℂ (Fin n) ↦
      (4 : ℂ)⁻¹ * ((q₁ w : ℂ) + q₂ w + Complex.I * ((q₃ w : ℂ) - q₄ w))) D z
    exact hdiv
  have hEq : (fun w ↦ complexHessian f w j k) =ᶠ[nhds z] S := by
    filter_upwards [hf.eventually (by norm_num : (3 : ℕ∞ω) ≠ ∞)] with w hw
    have hw2 : ContDiffAt ℝ 2 f w := hw.of_le (by norm_num)
    rw [complexHessian_apply hw2 j k]
    simp only [S, q₁, q₂, q₃, q₄, a, b, ia, ib, div_eq_mul_inv]
    ring
  have hComplex := hS.congr_of_eventuallyEq hEq
  have hleft : fderiv ℝ (fun w ↦ complexHessian f w j k) z v = D v :=
    congrArg (fun L : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ ↦ L v) hComplex.fderiv
  have hq₁eq : fderiv ℝ q₁ z v = fderiv ℝ (fderiv ℝ g) z a b := by
    calc
      fderiv ℝ q₁ z v = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b v) z a := by
        exact fderiv_second_apply_cyclic hf
      _ = fderiv ℝ (fderiv ℝ g) z a b := by
        simpa [q₁, g] using fderiv_second_directionalDerivative
          (f := f) (z := z) (a := a) (b := b) (v := v) hf
  have hq₂eq : fderiv ℝ q₂ z v = fderiv ℝ (fderiv ℝ g) z ia ib := by
    calc
      fderiv ℝ q₂ z v = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w ib v) z ia := by
        exact fderiv_second_apply_cyclic hf
      _ = fderiv ℝ (fderiv ℝ g) z ia ib := by
        simpa [q₂, g] using fderiv_second_directionalDerivative
          (f := f) (z := z) (a := ia) (b := ib) (v := v) hf
  have hq₃eq : fderiv ℝ q₃ z v = fderiv ℝ (fderiv ℝ g) z a ib := by
    calc
      fderiv ℝ q₃ z v = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w ib v) z a := by
        exact fderiv_second_apply_cyclic hf
      _ = fderiv ℝ (fderiv ℝ g) z a ib := by
        simpa [q₃, g] using fderiv_second_directionalDerivative
          (f := f) (z := z) (a := a) (b := ib) (v := v) hf
  have hq₄eq : fderiv ℝ q₄ z v = fderiv ℝ (fderiv ℝ g) z ia b := by
    calc
      fderiv ℝ q₄ z v = fderiv ℝ (fun w ↦ fderiv ℝ (fderiv ℝ f) w b v) z ia := by
        exact fderiv_second_apply_cyclic hf
      _ = fderiv ℝ (fderiv ℝ g) z ia b := by
        simpa [q₄, g] using fderiv_second_directionalDerivative
          (f := f) (z := z) (a := ia) (b := b) (v := v) hf
  have hright : D v = complexHessian g z j k := by
    rw [complexHessian_apply hg j k]
    simp [D, Complex.ofRealCLM_apply, hq₁eq, hq₂eq, hq₃eq, hq₄eq, a, b, ia, ib]
    ring_nf
  exact hleft.trans hright
omit [T2Space M] [CompactSpace M] in
private theorem chartPerturbedMetricDirection_eq (ω₀ : KahlerForm n M) {φ : M → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (x : M) {z v : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    chartPerturbedMetricDirection ω₀ φ x z v =
      chartBackgroundMetricDirection ω₀ x z v +
        complexHessian (fun u ↦ fderiv ℝ
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) u v) z := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hφon : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ Set.univ :=
    contMDiffOn_univ.mpr hφ
  have hφchart : ContDiffOn ℝ ∞ (φ ∘ e.symm) e.target := by
    have h := hφon.comp (contMDiffOn_extChartAt_symm x) (by intro u hu; simp)
    exact h.contDiffOn
  have h3le : (3 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
  have h1le : (1 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
  have hf : ContDiffAt ℝ 3 (φ ∘ e.symm) z :=
    (hφchart.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)).of_le h3le
  have hJdiff (j k : Fin n) : DifferentiableAt ℝ
      (fun u ↦ ω₀.metricInChart x u j k) z :=
    ((ω₀.contDiffOn_metricInChart x j k).contDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hz)).differentiableAt (by norm_num)
  have hFdiff (j k : Fin n) : DifferentiableAt ℝ
      (fun u ↦ ω₀.metricInChart x u j k +
        complexHessian (φ ∘ e.symm) u j k) z := by
    have hmetric : ContDiffAt ℝ 1 (fun u ↦ ω₀.metricInChart x u j k) z :=
      ((ω₀.contDiffOn_metricInChart x j k).contDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hz)).of_le h1le
    have hddbar : ContDiffOn ℝ ∞ (ddbar (φ ∘ e.symm)) e.target :=
      ContDiffOn.ddbar (isOpen_extChartAt_target x) hφchart
    let f₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun u ↦
      ddbar (φ ∘ e.symm) u ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]
    let f₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun u ↦
      ddbar (φ ∘ e.symm) u ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]
    have hf₁ : ContDiffOn ℝ ∞ f₁ e.target := by
      dsimp [f₁]
      exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]).contDiff).comp_contDiffOn
          hddbar
    have hf₂ : ContDiffOn ℝ ∞ f₂ e.target := by
      dsimp [f₂]
      exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
        ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]).contDiff).comp_contDiffOn hddbar
    have hf₁c : ContDiffOn ℝ ∞ (fun u ↦ (f₁ u : ℂ)) e.target := by
      convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₁ using 1
      ext u
      simp [f₁, Complex.ofRealCLM_apply]
    have hf₂c : ContDiffOn ℝ ∞ (fun u ↦ (f₂ u : ℂ)) e.target := by
      convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₂ using 1
      ext u
      simp [f₂, Complex.ofRealCLM_apply]
    have hIcont : ContDiffOn ℝ ∞ (fun _ : EuclideanSpace ℂ (Fin n) ↦ (Complex.I : ℂ))
        e.target := contDiffOn_const
    have hIprod : ContDiffOn ℝ ∞ (fun u ↦ Complex.I * (f₂ u : ℂ)) e.target :=
      hIcont.mul hf₂c
    have hcomplex : ContDiffAt ℝ 1
        (fun u ↦ complexHessian (φ ∘ e.symm) u j k) z := by
      have hentry : ContDiffAt ℝ 1
          (fun u ↦ ((f₁ u : ℂ) - Complex.I * (f₂ u : ℂ)) / 2) z := by
        have hcont := (hf₁c.sub hIprod).contDiffAt
          ((isOpen_extChartAt_target x).mem_nhds hz)
        exact (hcont.div_const (2 : ℂ)).of_le h1le
      have hEq : (fun u ↦ complexHessian (φ ∘ e.symm) u j k) =ᶠ[nhds z]
          fun u ↦ ((f₁ u : ℂ) - Complex.I * (f₂ u : ℂ)) / 2 := by
        filter_upwards [isOpen_extChartAt_target x |>.mem_nhds hz] with u hu
        change (ddbar (φ ∘ e.symm) u).coeffMatrix j k = _
        simp [ContinuousAlternatingMap.coeffMatrix, f₁, f₂]
      exact hentry.congr_of_eventuallyEq hEq.symm
    exact (hmetric.add hcomplex).differentiableAt (by norm_num)
  have hHessdiff (j k : Fin n) : DifferentiableAt ℝ
      (fun u ↦ complexHessian (φ ∘ e.symm) u j k) z := by
    have hsub := (hFdiff j k).sub (hJdiff j k)
    have hEq : (fun u ↦ complexHessian (φ ∘ e.symm) u j k) =ᶠ[nhds z]
        fun u ↦ (ω₀.metricInChart x u j k +
          complexHessian (φ ∘ e.symm) u j k) - ω₀.metricInChart x u j k := by
      filter_upwards with u
      simp
    exact hsub.congr_of_eventuallyEq hEq
  ext j k
  change fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k +
      complexHessian (φ ∘ e.symm) u j k) z v =
    fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v +
      complexHessian (fun u ↦ fderiv ℝ (φ ∘ e.symm) u v) z j k
  rw [fderiv_fun_add (hJdiff j k) (hHessdiff j k)]
  simp only [_root_.add_apply]
  rw [fderiv_complexHessian_direction hf]

omit [T2Space M] [CompactSpace M] in
private theorem hasDerivAt_G_along_chart_line_linearized (ω₀ : KahlerForm n M)
    {G φ : M → ℝ} (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M) {z v : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    HasDerivAt (fun t : ℝ ↦
      G ((extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm (z + t • v)))
      (complexEllipticOp (fun _ ↦
          (ω₀.metricInChart x z +
            complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹)
          (fun u ↦ fderiv ℝ
            (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) u v) z +
        RCLike.re (((ω₀.metricInChart x z +
          complexHessian (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ *
            chartBackgroundMetricDirection ω₀ x z v).trace) -
        RCLike.re ((ω₀.metricInChart x z)⁻¹ *
          chartBackgroundMetricDirection ω₀ x z v).trace) 0 := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let dφ : EuclideanSpace ℂ (Fin n) → ℝ := fun u ↦ fderiv ℝ (φ ∘ e.symm) u v
  let gφ : Matrix (Fin n) (Fin n) ℂ := ω₀.metricInChart x z + complexHessian (φ ∘ e.symm) z
  have hbase := hasDerivAt_G_along_chart_line_of_smooth ω₀ hφ hsol x
    (z := z) (v := v) hz
  have hdir := chartPerturbedMetricDirection_eq ω₀ hφ x (z := z) (v := v) hz
  have hcoeff : RCLike.re
      ((gφ⁻¹ * chartPerturbedMetricDirection ω₀ φ x z v).trace) =
        complexEllipticOp (fun _ ↦ gφ⁻¹) dφ z +
          RCLike.re ((gφ⁻¹ * chartBackgroundMetricDirection ω₀ x z v).trace) := by
    rw [hdir]
    simp [complexEllipticOp, gφ, dφ, e, Matrix.mul_add, Matrix.trace_add]
    exact add_comm _ _
  have hderiv : RCLike.re
      ((gφ⁻¹ * chartPerturbedMetricDirection ω₀ φ x z v).trace) -
        RCLike.re ((ω₀.metricInChart x z)⁻¹ *
          chartBackgroundMetricDirection ω₀ x z v).trace =
      complexEllipticOp (fun _ ↦ gφ⁻¹) dφ z +
        RCLike.re ((gφ⁻¹ * chartBackgroundMetricDirection ω₀ x z v).trace) -
        RCLike.re ((ω₀.metricInChart x z)⁻¹ *
          chartBackgroundMetricDirection ω₀ x z v).trace := by
    rw [hcoeff]
  have hbase' := hbase.congr_deriv hderiv
  simpa [gφ, dφ, e] using hbase'

omit [T2Space M] [CompactSpace M] in
theorem complexEllipticOp_eq_fderiv_chart_G (ω₀ : KahlerForm n M)
    {G φ : M → ℝ} (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G)
    (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φ)
    (hsol : ω₀.SolvesMongeAmpere G φ) (x : M) {z v : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) :
    complexEllipticOp (fun _ ↦
        (ω₀.metricInChart x z + complexHessian
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹)
        (fun u ↦ fderiv ℝ
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) u v) z =
      fderiv ℝ (G ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v -
        RCLike.re (((ω₀.metricInChart x z + complexHessian
          (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ *
            (Matrix.of fun j k ↦ fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v)).trace) +
        RCLike.re ((ω₀.metricInChart x z)⁻¹ *
          (Matrix.of fun j k ↦ fderiv ℝ (fun u ↦ ω₀.metricInChart x u j k) z v)).trace := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  let γ : ℝ → EuclideanSpace ℂ (Fin n) := fun t ↦ z + t • v
  have hGon : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ G Set.univ :=
    contMDiffOn_univ.mpr hG
  have hGchart : ContDiffOn ℝ ∞ (G ∘ e.symm) e.target := by
    have h := hGon.comp (contMDiffOn_extChartAt_symm x) (by intro u hu; simp)
    exact h.contDiffOn
  have hGat : ContDiffAt ℝ ∞ (G ∘ e.symm) z :=
    hGchart.contDiffAt ((isOpen_extChartAt_target x).mem_nhds hz)
  have hsmul : HasDerivAt (fun t : ℝ ↦ t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hγ : HasDerivAt γ v 0 := hsmul.const_add z
  have hcomp : HasDerivAt (fun t : ℝ ↦ G (e.symm (z + t • v)))
      (fderiv ℝ (G ∘ e.symm) z v) 0 := by
    have h := (hGat.differentiableAt (by norm_num)).hasFDerivAt
    have h' : HasFDerivAt (G ∘ e.symm) (fderiv ℝ (G ∘ e.symm) z) (γ 0) := by
      simpa [γ] using h
    have h' := h'.comp_hasDerivAt 0 hγ
    simpa [Function.comp_def, γ, e] using h'
  have hline := hasDerivAt_G_along_chart_line_linearized ω₀ hφ hsol x
    (z := z) (v := v) hz
  have heq := hline.deriv.symm.trans hcomp.deriv
  change complexEllipticOp (fun _ ↦
      (ω₀.metricInChart x z + complexHessian
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹)
      (fun u ↦ fderiv ℝ
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) u v) z =
    fderiv ℝ (G ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z v -
      RCLike.re (((ω₀.metricInChart x z + complexHessian
        (φ ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)⁻¹ *
          chartBackgroundMetricDirection ω₀ x z v).trace) +
      RCLike.re ((ω₀.metricInChart x z)⁻¹ *
        chartBackgroundMetricDirection ω₀ x z v).trace
  linarith

private theorem hasDerivAt_log_det_affine {A H : Matrix (Fin n) (Fin n) ℂ}
    (t : ℝ) (hAt : (A + t • H).PosDef) :
    HasDerivAt (fun s : ℝ ↦ Real.log (RCLike.re (A + s • H).det))
      (RCLike.re ((A + t • H)⁻¹ * H).trace) t := by
  let B := A + t • H
  have hline := hasDerivAt_log_det_add_smul (A := B) (H := H) hAt
  have hshift : (fun s : ℝ ↦ Real.log (RCLike.re (B + s • H).det)) =
      fun s : ℝ ↦ Real.log (RCLike.re (A + (t + s) • H).det) := by
    funext s
    congr 2
    dsimp [B]
    rw [add_assoc, ← add_smul]
  have hshift' := hline.congr_of_eventuallyEq
    (Filter.EventuallyEq.of_eq hshift.symm)
  have htrans : HasDerivAt (fun s : ℝ ↦ s - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have hcomp := hshift'.comp_of_eq t htrans (by simp)
  simpa [Function.comp_def, add_sub_cancel_left, B] using hcomp

end KahlerForm
