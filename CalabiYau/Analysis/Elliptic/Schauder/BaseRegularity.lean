module

public import CalabiYau.Analysis.Elliptic.Schauder
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.SmoothBallRestriction
import CalabiYau.Analysis.Elliptic.Schauder.BaseRegularity.LocalApproximation

/-!
# Base interior Schauder regularity

This file isolates the `k = 0` slice of the interior Schauder provider: continuous
coefficients and continuous right-hand side imply `C²` regularity on the smaller domain, with the
corresponding interior `C^{2,α}` bound. The approximation/limit and base-estimate APIs needed to
prove this slice are not currently available in the extracted provider, so the analytic statement
is recorded independently rather than assumed through the provider theorem.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal Topology
open Set Matrix

/-- A compactly contained open-set problem admits finitely many nested ball patches, with the
smallest balls covering the target closure and the largest closed balls contained in the source. -/
private def BaseSchauderFinitePatchCover {n : ℕ}
    (U V : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  ∃ N : ℕ, ∃ c : Fin N → EuclideanSpace ℂ (Fin n),
    ∃ r R S : Fin N → ℝ,
      (∀ i, 0 < r i ∧ r i < R i ∧ R i < S i) ∧
      (∀ i, Metric.closedBall (c i) (S i) ⊆ U) ∧
      closure V ⊆ ⋃ i, Metric.ball (c i) (r i / 4)

/-- Compactness produces nested local radii without requiring one ball to contain `closure V`.
The constants are chosen solely from `U` and `V`, before any coefficient or solution data. -/
private theorem exists_baseSchauderFinitePatchCover {n : ℕ}
    {U V : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hV : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    BaseSchauderFinitePatchCover U V := by
  classical
  have hLocal (x : closure V) :
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (x : EuclideanSpace ℂ (Fin n)) ρ ⊆ U := by
    obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hVU x.2))
    refine ⟨ε / 2, half_pos hε, ?_⟩
    intro z hz
    apply hBall
    apply Metric.mem_ball.mpr
    exact (Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hε)
  choose ρ hρ hSub using hLocal
  have hCover : closure V ⊆ ⋃ x : closure V,
      Metric.ball (x : EuclideanSpace ℂ (Fin n)) (ρ x / 16) := by
    intro z hz
    have hpos := hρ ⟨z, hz⟩
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (by positivity)⟩
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover
    (fun x : closure V => Metric.ball (x : EuclideanSpace ℂ (Fin n)) (ρ x / 16))
    (fun _ => Metric.isOpen_ball) hCover
  let p : Fin s.card → closure V := fun i => (s.equivFin.symm i).val
  let c : Fin s.card → EuclideanSpace ℂ (Fin n) := fun i => (p i).val
  let r : Fin s.card → ℝ := fun i => ρ (p i) / 4
  let R : Fin s.card → ℝ := fun i => ρ (p i) / 2
  let S : Fin s.card → ℝ := fun i => ρ (p i)
  refine ⟨s.card, c, r, R, S, ?_, ?_, ?_⟩
  · intro i
    have hp := hρ (p i)
    dsimp [r, R, S]
    exact ⟨by positivity, by linarith, by linarith⟩
  · intro i
    exact hSub (p i)
  · intro z hz
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hs hz)
    obtain ⟨hxs, hball⟩ := Set.mem_iUnion.mp hx
    let i : Fin s.card := s.equivFin ⟨x, hxs⟩
    have hpi : p i = x := by simp [p, i]
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    change z ∈ Metric.ball (p i).val ((ρ (p i) / 4) / 4)
    rw [hpi]
    have hr : (ρ x / 4) / 4 = ρ x / 16 := by ring
    simpa only [hr] using hball

/-- A local order-two Hölder estimate on the half-radius balls of a finite quarter-radius cover
of `closure V` globalizes with a constant independent of the function and scale bound. The
near-pair estimate uses a patch containing both points; separated pairs use the global second-jet
supremum bound and the positive minimum patch radius. -/
private theorem holderBoundOn_two_of_finiteQuarterCover {n : ℕ}
    {V : Set (EuclideanSpace ℂ (Fin n))} {α : ℝ≥0}
    (hα : 0 < α)
    (N : ℕ) (c : Fin N → EuclideanSpace ℂ (Fin n))
    (r R S : Fin N → ℝ)
    (hr : ∀ i, 0 < r i ∧ r i < R i ∧ R i < S i)
    (hcover : closure V ⊆ ⋃ i, Metric.ball (c i) (r i / 4))
    (C : Fin N → ℝ≥0) :
    ∃ Cglobal : ℝ≥0, ∀ (B : ℝ≥0) (u : EuclideanSpace ℂ (Fin n) → ℝ),
      (∀ i, HolderBoundOn 2 α (C i * B)
        (Metric.closedBall (c i) (R i / 2)) u) →
      HolderBoundOn 2 α (Cglobal * B) V u := by
  classical
  by_cases hN : N = 0
  · subst N
    have hV : V = ∅ := by
      ext x
      constructor
      · intro hx
        have hcl : x ∈ closure V := subset_closure hx
        have hcover' := hcover hcl
        simp at hcover'
      · simp
    subst V
    exact ⟨0, by intro B u hlocal; exact ⟨by simp, by simp⟩⟩
  · let F : Finset (Fin N) := Finset.univ
    have hF : F.Nonempty := by
      refine ⟨⟨0, by omega⟩, ?_⟩
      exact Finset.mem_univ _
    obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image F (fun i => r i / 4) hF
    let δ : ℝ := r i₀ / 4
    have hδ : 0 < δ := by
      dsimp [δ]
      have := (hr i₀).1
      positivity
    have hδi (i : Fin N) : δ ≤ r i / 4 := by
      dsimp [δ]
      exact hmin i (Finset.mem_univ i)
    let dNN : ℝ≥0 := Real.toNNReal δ
    have hdNN : 0 < dNN := Real.toNNReal_pos.mpr hδ
    let Csum : ℝ≥0 := ∑ i : Fin N, C i
    let Cglobal : ℝ≥0 := if V = ∅ then 0 else Csum * (1 + 2 / (dNN ^ (α : ℝ)))
    refine ⟨Cglobal, ?_⟩
    intro B u hlocal
    have hCi (i : Fin N) : C i ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
    have hnorm (x : EuclideanSpace ℂ (Fin n)) (hx : x ∈ V) (j : ℕ) (hj : j ≤ 2) :
        ‖iteratedFDeriv ℝ j u x‖ ≤ (Csum * B : ℝ) := by
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover (subset_closure hx))
      have hxball : dist x (c i) < r i / 4 := by simpa using hxi
      have hxhalf : x ∈ Metric.closedBall (c i) (R i / 2) := by
        rw [Metric.mem_closedBall]
        have hrpos : 0 < r i := (hr i).1
        have hrad : r i / 4 < R i / 2 := by
          calc
            r i / 4 < r i / 2 := by nlinarith [hrpos]
            _ < R i / 2 := by gcongr; exact (hr i).2.1
        exact le_of_lt (hxball.trans hrad)
      have hlocal' := (hlocal i).1 j hj x hxhalf
      have hmul : C i * B ≤ Csum * B := mul_le_mul_of_nonneg_right (hCi i) (by positivity)
      exact hlocal'.trans (by exact_mod_cast hmul)
    have hholder : HolderOnWith (Cglobal * B) α (iteratedFDeriv ℝ 2 u) V := by
      intro x hx y hy
      have hVne : V ≠ ∅ := by
        intro hV
        subst V
        simp at hx
      have hCglobalFormula : Cglobal = Csum * (1 + 2 / (dNN ^ (α : ℝ))) := by
        simp [Cglobal, hVne]
      by_cases hnear : dist x y < δ
      · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover (subset_closure hx))
        have hxball : dist x (c i) < r i / 4 := by simpa using hxi
        have hxhalf : x ∈ Metric.closedBall (c i) (R i / 2) := by
          rw [Metric.mem_closedBall]
          have hrpos : 0 < r i := (hr i).1
          have hrad : r i / 4 < R i / 2 := by
            calc
              r i / 4 < r i / 2 := by nlinarith [hrpos]
              _ < R i / 2 := by gcongr; exact (hr i).2.1
          exact le_of_lt (hxball.trans hrad)
        have hyhalf : y ∈ Metric.closedBall (c i) (R i / 2) := by
          rw [Metric.mem_closedBall]
          have hytri : dist y (c i) ≤ dist y x + dist x (c i) := dist_triangle _ _ _
          have hd : dist y x < δ := by simpa [dist_comm] using hnear
          have hfinal : dist y (c i) < R i / 2 := by
            calc
              dist y (c i) ≤ dist y x + dist x (c i) := hytri
              _ < δ + r i / 4 := add_lt_add_of_lt_of_le hd (le_of_lt hxball)
              _ < R i / 2 := by nlinarith [hδi i, (hr i).2.1]
          simpa [dist_comm] using (le_of_lt hfinal)
        have hloc := (hlocal i).2 x hxhalf y hyhalf
        have hcoeffNN : (C i * B : ℝ≥0) ≤ Csum * B :=
          mul_le_mul_of_nonneg_right (hCi i) (by positivity)
        have hcoeff : (↑(C i * B) : ENNReal) ≤ ↑(Csum * B) := by
          exact_mod_cast hcoeffNN
        have hCglobal : Csum ≤ Cglobal := by
          rw [hCglobalFormula]
          have hpow : 0 < dNN ^ (α : ℝ) := by
            exact NNReal.rpow_pos hdNN
          have hfactor : (1 : ℝ≥0) ≤ 1 + 2 / (dNN ^ (α : ℝ)) := by
            exact le_add_of_nonneg_right (by positivity)
          calc
            Csum = Csum * 1 := by simp
            _ ≤ Csum * (1 + 2 / (dNN ^ (α : ℝ))) := by
              exact mul_le_mul_of_nonneg_left hfactor (bot_le)
        have hcoeffGlobal : (↑(Csum * B) : ENNReal) ≤ ↑(Cglobal * B) := by
          exact_mod_cast (mul_le_mul_of_nonneg_right hCglobal (by positivity))
        calc
          edist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤
              ↑(C i * B) * edist x y ^ (α : ℝ) := hloc
          _ ≤ ↑(Cglobal * B) * edist x y ^ (α : ℝ) :=
              mul_le_mul_of_nonneg_right (hcoeff.trans hcoeffGlobal) (by positivity)
      · have hδdist : (dNN : ENNReal) ≤ edist x y := by
          rw [edist_dist]
          have hreal : δ ≤ dist x y := le_of_not_gt hnear
          calc
            (dNN : ENNReal) = ENNReal.ofReal δ := by
              simp [dNN, ENNReal.ofReal, Real.toNNReal_of_nonneg hδ.le]
            _ ≤ ENNReal.ofReal (dist x y) := ENNReal.ofReal_le_ofReal hreal
        have hpowle : (dNN : ENNReal) ^ (α : ℝ) ≤ edist x y ^ (α : ℝ) :=
          ENNReal.rpow_le_rpow hδdist (by exact_mod_cast hα.le)
        have hpowpos : 0 < dNN ^ (α : ℝ) := NNReal.rpow_pos hdNN
        have hscale : 2 * Csum ≤ Cglobal * dNN ^ (α : ℝ) := by
          rw [hCglobalFormula]
          have hmul : 2 ≤ (1 + 2 / (dNN ^ (α : ℝ))) * dNN ^ (α : ℝ) := by
            have hcancel : (2 / (dNN ^ (α : ℝ))) * dNN ^ (α : ℝ) = 2 :=
              div_mul_cancel₀ 2 hpowpos.ne'
            calc
              2 = (2 / (dNN ^ (α : ℝ))) * dNN ^ (α : ℝ) := hcancel.symm
              _ ≤ (1 + 2 / (dNN ^ (α : ℝ))) * dNN ^ (α : ℝ) := by
                apply mul_le_mul_of_nonneg_right
                · exact le_add_of_nonneg_left (by positivity)
                · exact le_of_lt hpowpos
          calc
            2 * Csum ≤ ((1 + 2 / (dNN ^ (α : ℝ))) * dNN ^ (α : ℝ)) * Csum :=
              mul_le_mul_of_nonneg_right hmul (by positivity)
            _ = Csum * (1 + 2 / (dNN ^ (α : ℝ))) * dNN ^ (α : ℝ) := by ring
        have hscaleB : 2 * Csum * B ≤ (Cglobal * B) * dNN ^ (α : ℝ) := by
          calc
            2 * Csum * B = (2 * Csum) * B := by ring
            _ ≤ (Cglobal * dNN ^ (α : ℝ)) * B :=
              mul_le_mul_of_nonneg_right hscale (by positivity)
            _ = (Cglobal * B) * dNN ^ (α : ℝ) := by ring
        have hpowcast : (↑(dNN ^ (α : ℝ)) : ENNReal) =
            (dNN : ENNReal) ^ (α : ℝ) := ENNReal.coe_rpow_of_nonneg _ hα.le
        have hcoeffFar : (↑(2 * Csum * B) : ENNReal) ≤
            ↑(Cglobal * B) * (dNN : ENNReal) ^ (α : ℝ) := by
          rw [← hpowcast, ← ENNReal.coe_mul]
          exact_mod_cast hscaleB
        have hupperReal : dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤
            2 * (Csum : ℝ) * B := by
          rw [dist_eq_norm]
          calc
            ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ ≤
                ‖iteratedFDeriv ℝ 2 u x‖ + ‖iteratedFDeriv ℝ 2 u y‖ := norm_sub_le _ _
            _ ≤ Csum * B + Csum * B := add_le_add (hnorm x hx 2 le_rfl) (hnorm y hy 2 le_rfl)
            _ = 2 * (Csum : ℝ) * B := by ring
        have hupperNN : Real.toNNReal
            (dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y)) ≤ 2 * Csum * B := by
          apply Real.toNNReal_le_iff_le_coe.mpr
          simpa [mul_assoc] using hupperReal
        have hupper : edist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤
            ↑(2 * Csum * B) := by
          rw [edist_dist, ENNReal.ofReal]
          exact_mod_cast hupperNN
        calc
          edist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤ ↑(2 * Csum * B) := hupper
          _ ≤ ↑(Cglobal * B) * (dNN : ENNReal) ^ (α : ℝ) := hcoeffFar
          _ ≤ ↑(Cglobal * B) * edist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_left hpowle (by positivity)
    refine ⟨?_, hholder⟩
    intro j hj x hx
    have hVne : V ≠ ∅ := by
      intro hV
      subst V
      simp at hx
    have hCglobalFormula : Cglobal = Csum * (1 + 2 / (dNN ^ (α : ℝ))) := by
      simp [Cglobal, hVne]
    have hCglobal : Csum ≤ Cglobal := by
      rw [hCglobalFormula]
      have hfactor : (1 : ℝ≥0) ≤ 1 + 2 / (dNN ^ (α : ℝ)) :=
        le_add_of_nonneg_right (by positivity)
      calc
        Csum = Csum * 1 := by simp
        _ ≤ Csum * (1 + 2 / (dNN ^ (α : ℝ))) :=
          mul_le_mul_of_nonneg_left hfactor (bot_le)
    have hbound : Csum * B ≤ Cglobal * B :=
      mul_le_mul_of_nonneg_right hCglobal (by positivity)
    exact (hnorm x hx j hj).trans (by exact_mod_cast hbound)

/-- Smooth coefficients and a smooth potential make the complex elliptic operator smooth, without
using any regularity conclusion from the Schauder provider. -/
private theorem complexEllipticOp_contDiffOn_of_smooth {n : ℕ}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ} {U : Set (EuclideanSpace ℂ (Fin n))}
    (hU : IsOpen U) (hA : ∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A z j l) U)
    (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (complexEllipticOp A u) U := by
  have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) U := by
    exact hu.fderiv_of_isOpen hU (WithTop.coe_le_coe.mpr le_top)
  have hD₂u : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ u)) U := by
    exact hDu.fderiv_of_isOpen hU (WithTop.coe_le_coe.mpr le_top)
  have hD₂eval (v w : EuclideanSpace ℂ (Fin n)) :
      ContDiffOn ℝ ∞ (fun z ↦ fderiv ℝ (fderiv ℝ u) z v w) U := by
    have hv : ContDiffOn ℝ ∞ (fun _ : EuclideanSpace ℂ (Fin n) ↦ v) U := contDiffOn_const
    have hw : ContDiffOn ℝ ∞ (fun _ : EuclideanSpace ℂ (Fin n) ↦ w) U := contDiffOn_const
    exact (hD₂u.clm_apply hv).clm_apply hw
  have hEntry (j l : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ complexHessian u z j l) U := by
    have hFormula : ContDiffOn ℝ ∞ (fun z ↦
        ((fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1) (EuclideanSpace.single l 1) : ℂ) +
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
            (Complex.I • EuclideanSpace.single l 1) +
          Complex.I * (fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single j 1)
            (Complex.I • EuclideanSpace.single l 1) -
          fderiv ℝ (fderiv ℝ u) z (Complex.I • EuclideanSpace.single j 1)
            (EuclideanSpace.single l 1))) / 4) U := by
      simp only [← Complex.ofRealCLM_apply]
      fun_prop
    apply hFormula.congr
    intro z hz
    rw [complexHessian_apply
      (((hu z hz).contDiffAt (hU.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top))]
  have hSum : ContDiffOn ℝ ∞ (fun z ↦
      ∑ i, ∑ j, Complex.reCLM (A z i j * complexHessian u z j i)) U := by
    fun_prop
  have hOp : ContDiffOn ℝ ∞
      (fun z ↦ RCLike.re ((A z * complexHessian u z).trace)) U := by
    change ContDiffOn ℝ ∞
      (fun z ↦ Complex.reCLM ((A z * complexHessian u z).trace)) U
    apply hSum.congr
    intro z hz
    simp [Matrix.mul_apply, Matrix.trace, Complex.reCLM_apply]
  change ContDiffOn ℝ ∞
    (fun z ↦ RCLike.re ((A z * complexHessian u z).trace)) U
  exact hOp

/-- Data for regularizing the `k = 0` equation without assuming the provider theorem. The
coefficient and two-jet converge locally uniformly, while the ellipticity and Hölder/source bounds
are allowed a vanishing slack. -/
private def BaseSchauderApproximationData {n : ℕ}
    (α lam K K₀ K₁ : ℝ≥0) (U : Set (EuclideanSpace ℂ (Fin n)))
    (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n) → ℝ) : Prop :=
  ∃ (ε : ℕ → ℝ≥0)
    (Aseq : ℕ → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (useq : ℕ → EuclideanSpace ℂ (Fin n) → ℝ),
    Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    (∀ m, ε m ≤ 1) ∧
    (∀ m j l, ContDiffOn ℝ ∞ (fun z ↦ Aseq m z j l) U) ∧
    (∀ m, ContDiffOn ℝ ∞ (useq m) U) ∧
    (∀ m, IsUniformlyEllipticOn (Aseq m) (lam / 2) U) ∧
    (∀ m j l, HolderBoundOn 0 α (K + 1) U fun z ↦ Aseq m z j l) ∧
    (∀ m, HolderBoundOn 0 α (K₁ + ε m) U
      (complexEllipticOp (Aseq m) (useq m))) ∧
    (∀ m z, z ∈ U → |useq m z| ≤ K₀ + ε m) ∧
    (∀ j l, TendstoLocallyUniformlyOn (fun m z ↦ Aseq m z j l)
      (fun z ↦ A z j l) Filter.atTop U) ∧
    (∀ j ≤ 2, TendstoLocallyUniformlyOn
      (fun m z ↦ iteratedFDeriv ℝ j (useq m) z)
      (fun z ↦ iteratedFDeriv ℝ j u z) Filter.atTop U)

/-- Diagonalize already-global row families over an increasing exhaustion whose interiors cover U.
This assembles local-uniform convergence only: it does not construct the global row families or
supply their ellipticity, Hölder, or value estimates. -/
private theorem tendstoLocallyUniformlyOn_diagonal_of_exhaustion
    {E F : Type*} [TopologicalSpace E] [PseudoMetricSpace F]
    {U : Set E} (Q : ℕ → Set E)
    (hQmono : ∀ j, Q j ⊆ Q (j + 1))
    (hcover : ∀ x ∈ U, ∃ j, x ∈ interior (Q j))
    {rows : ℕ → ℕ → E → F} {f : E → F}
    (hrows : ∀ j, TendstoUniformlyOn (fun k x ↦ rows j k x) f
      Filter.atTop (Q j)) :
    ∃ k : ℕ → ℕ,
      TendstoLocallyUniformlyOn (fun j x ↦ rows j (k j) x) f Filter.atTop U := by
  classical
  have hstage (j : ℕ) :
      ∃ N : ℕ, ∀ m, N ≤ m → ∀ x ∈ Q j,
        dist (f x) (rows j m x) < (1 : ℝ) / ((j : ℝ) + 1) := by
    have hpos : (0 : ℝ) < (1 : ℝ) / ((j : ℝ) + 1) := by positivity
    have hev : ∀ᶠ m : ℕ in Filter.atTop, ∀ x ∈ Q j,
        dist (f x) (rows j m x) < (1 : ℝ) / ((j : ℝ) + 1) :=
      (Metric.tendstoUniformlyOn_iff.mp (hrows j)) _ hpos
    rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
    exact ⟨N, fun m hm x hx ↦ hN m hm x hx⟩
  let k : ℕ → ℕ := fun j ↦ Classical.choose (hstage j)
  have hk (j : ℕ) (x : E) (hx : x ∈ Q j) :
      dist (f x) (rows j (k j) x) < (1 : ℝ) / ((j : ℝ) + 1) :=
    Classical.choose_spec (hstage j) (k j) le_rfl x hx
  have hQsub : ∀ a b, a ≤ b → Q a ⊆ Q b := by
    intro a b hab
    induction b with
    | zero =>
        have ha : a = 0 := by omega
        subst a
        exact Subset.rfl
    | succ b ih =>
        by_cases hab' : a ≤ b
        · exact (ih hab').trans (hQmono b)
        · have ha : a = b + 1 := by omega
          subst a
          exact Subset.rfl
  refine ⟨k, ?_⟩
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  obtain ⟨j₀, hxj₀⟩ := hcover x hx
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  let J : ℕ := max j₀ N
  have hj₀ : j₀ ≤ J := Nat.le_max_left _ _
  have hNle : N ≤ J := Nat.le_max_right _ _
  have hInvJ : (1 / ε : ℝ) < (J : ℝ) := by
    exact lt_of_lt_of_le hN (by exact_mod_cast hNle)
  have hMul : (1 : ℝ) < (J : ℝ) * ε := (div_lt_iff₀ hε).mp hInvJ
  have hSmall : (1 : ℝ) / ((J : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith
  let t : Set E := interior (Q j₀) ∩ U
  refine ⟨t, ?_, ?_⟩
  · have hNhd : interior (Q j₀) ∈ nhds x := isOpen_interior.mem_nhds hxj₀
    change t ∈ nhds x ⊓ Filter.principal U
    exact Filter.inter_mem_inf hNhd (Filter.mem_principal_self U)
  · have hev : ∀ᶠ m : ℕ in Filter.atTop, J ≤ m :=
      Filter.eventually_atTop.2 ⟨J, fun _ hm ↦ hm⟩
    filter_upwards [hev] with m hm y hy
    have hyQ₀ : y ∈ Q j₀ := interior_subset hy.1
    have hyQm : y ∈ Q m := hQsub j₀ m (le_trans hj₀ hm) hyQ₀
    have hrecip :
        (1 : ℝ) / ((m : ℝ) + 1) ≤ (1 : ℝ) / ((J : ℝ) + 1) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hcast : (J : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith
    exact (hk m y hyQm).trans_le hrecip |>.trans hSmall

section BaseSchauderJetLimit
open Filter
open scoped uniformity Filter Topology

variable {ι : Type*} {l : Filter ι} {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedSpace 𝕜 E] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : ι → E → G}
  {g : E → G} {f' : ι → E → E →L[𝕜] G} {g' : E → E →L[𝕜] G} {x : E}

private theorem local_difference_quotients_converge_uniformly
    {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 E] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : ι → E → G}
    {g : E → G} {f' : ι → E → E →L[𝕜] G} {g' : E → E →L[𝕜] G} {x : E}
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y : E in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) :
    TendstoUniformlyOnFilter (fun n : ι => fun y : E => (‖y - x‖⁻¹ : 𝕜) • (f n y - f n x))
      (fun y : E => (‖y - x‖⁻¹ : 𝕜) • (g y - g x)) l (𝓝 x) := by
  let A : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  refine
    UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto ?_
      ((hfg.and (eventually_const.mpr hfg.self_of_nhds)).mono fun y hy =>
        (hy.1.sub hy.2).const_smul _)
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero]
  rw [Metric.tendstoUniformlyOnFilter_iff]
  have hfg' := hf'.uniformCauchySeqOnFilter
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hfg'
  rw [Metric.tendstoUniformlyOnFilter_iff] at hfg'
  intro ε hε
  obtain ⟨q, hqpos, hqε⟩ := exists_pos_rat_lt hε
  specialize hfg' (q : ℝ) (by simp [hqpos])
  have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hfg'.and this)
  obtain ⟨r, hr, hr'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
  rw [eventually_prod_iff]
  refine
    ⟨_, b, (· ∈ Metric.ball x r),
      eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
  simp only [Pi.zero_apply, dist_zero_left]
  rw [norm_neg_add, ← smul_sub, norm_smul, norm_inv, RCLike.norm_coe_norm]
  refine lt_of_le_of_lt ?_ hqε
  by_cases hyz' : x = y; · simp [hyz', hqpos.le]
  have hyz : 0 < ‖y - x‖ := by rw [norm_pos_iff]; intro hy'; exact hyz' (eq_of_sub_eq_zero hy').symm
  rw [inv_mul_le_iff₀ hyz, mul_comm, sub_sub_sub_comm]
  simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e
  refine
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
      (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit at `x`.

In words the assumptions mean the following:
  * `hf'`: The `f'` converge "uniformly at" `x` to `g'`. This does not mean that the `f' n` even
    converge away from `x`!
  * `hf`: For all `(y, n)` with `y` sufficiently close to `x` and `n` sufficiently large, `f' n` is
    the derivative of `f n`
  * `hfg`: The `f n` converge pointwise to `g` on a neighborhood of `x` -/

private theorem local_hasFDerivAt_of_tendstoUniformlyOnFilter [NeBot l]
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : HasFDerivAt g (g' x) x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  -- The proof strategy follows several steps:
  --   1. The quantifiers in the definition of the derivative are
  --      `∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`. We will introduce a quantifier in the middle:
  --      `∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x)` which will allow us to introduce the
  --      `f(') n`
  --   2. The order of the quantifiers `hfg` are opposite to what we need. We will be able to swap
  --      the quantifiers using the uniform convergence assumption
  rw [hasFDerivAt_iff_tendsto]
  -- Introduce extra quantifier via curried filters
  suffices
    Tendsto (fun y : ι × E => ‖y.2 - x‖⁻¹ * ‖g y.2 - g x - (g' x) (y.2 - x)‖)
      (l.curry (𝓝 x)) (𝓝 0) by
    rw [Metric.tendsto_nhds] at this ⊢
    intro ε hε
    specialize this ε hε
    rw [eventually_curry_iff] at this
    simp only at this
    exact (eventually_const.mp this).mono (by simp only [imp_self, forall_const])
  -- With the new quantifier in hand, we can perform the famous `ε/3` proof. Specifically,
  -- we will break up the limit (the difference functions minus the derivative go to 0) into 3:
  --   * The difference functions of the `f n` converge *uniformly* to the difference functions
  --     of the `g n`
  --   * The `f' n` are the derivatives of the `f n`
  --   * The `f' n` converge to `g'` at `x`
  conv =>
    congr
    ext
    rw [← abs_norm, ← abs_inv, ← @RCLike.norm_ofReal 𝕜 _ _, RCLike.ofReal_inv, ← norm_smul]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have :
    (fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (g' x) (a.2 - x))) =
      ((fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (g a.2 - g x - (f a.1 a.2 - f a.1 x))) +
          fun a : ι × E =>
          (‖a.2 - x‖⁻¹ : 𝕜) • (f a.1 a.2 - f a.1 x - ((f' a.1 x) a.2 - (f' a.1 x) x))) +
        fun a : ι × E => (‖a.2 - x‖⁻¹ : 𝕜) • (f' a.1 x - g' x) (a.2 - x) := by
    ext; simp only [Pi.add_apply]; rw [← smul_add, ← smul_add]; congr
    simp only [map_sub, sub_add_sub_cancel, FunLike.coe_sub, Pi.sub_apply]
    abel
  simp_rw [this]
  have : 𝓝 (0 : G) = 𝓝 (0 + 0 + 0) := by simp only [add_zero]
  rw [this]
  refine Tendsto.add (Tendsto.add ?_ ?_) ?_
  · have := local_difference_quotients_converge_uniformly hf' hf hfg
    rw [Metric.tendstoUniformlyOnFilter_iff] at this
    rw [Metric.tendsto_nhds]
    intro ε hε
    apply ((this ε hε).filter_mono curry_le_prod).mono
    intro n hn
    rw [dist_eq_norm] at hn ⊢
    convert! hn using 2
    module
  · -- (Almost) the definition of the derivatives
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_curry_iff]
    refine hf.curry.mono fun n hn => ?_
    have := hn.self_of_nhds
    rw [hasFDerivAt_iff_tendsto, Metric.tendsto_nhds] at this
    refine (this ε hε).mono fun y hy => ?_
    rw [dist_eq_norm] at hy ⊢
    simp only [sub_zero, map_sub, norm_mul, norm_inv, norm_norm] at hy ⊢
    rw [norm_smul, norm_inv, RCLike.norm_coe_norm]
    exact hy
  · -- hfg' after specializing to `x` and applying the definition of the operator norm
    refine Tendsto.mono_left ?_ curry_le_prod
    have h1 : Tendsto (fun n : ι × E => g' n.2 - f' n.1 n.2) (l ×ˢ 𝓝 x) (𝓝 0) := by
      rw [Metric.tendstoUniformlyOnFilter_iff] at hf'
      exact Metric.tendsto_nhds.mpr fun ε hε => by simpa [dist_eq_norm] using hf' ε hε
    have h2 : Tendsto (fun n : ι => g' x - f' n x) l (𝓝 0) := by
      rw [Metric.tendsto_nhds] at h1 ⊢
      exact fun ε hε => (h1 ε hε).curry.mono fun n hn => hn.self_of_nhds
    refine squeeze_zero_norm ?_
      (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_fst.comp (h2.prodMap tendsto_id)))
    intro n
    simp_rw [norm_smul, norm_inv, RCLike.norm_coe_norm]
    by_cases hx : x = n.2; · simp [hx]
    have hnx : 0 < ‖n.2 - x‖ := by
      rw [norm_pos_iff]; intro hx'; exact hx (eq_of_sub_eq_zero hx').symm
    rw [inv_mul_le_iff₀ hnx, mul_comm]
    simp only [Function.comp_apply, Prod.map_apply']
    rw [norm_sub_rev]
    exact (f' n.1 x - g' x).le_opNorm (n.2 - x)

private theorem local_hasFDerivAt_of_tendstoLocallyUniformlyOn [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn f' g' l s) (hf : ∀ n, ∀ x ∈ s, HasFDerivAt (f n) (f' n x) x)
    (hfg : ∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) :
    HasFDerivAt g (g' x) x := by
  have h1 : s ∈ 𝓝 x := hs.mem_nhds hx
  have h3 : Set.univ ×ˢ s ∈ l ×ˢ 𝓝 x := by simp only [h1, prod_mem_prod_iff, univ_mem, and_self_iff]
  have h4 : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_of_mem h3 fun ⟨n, z⟩ ⟨_, hz⟩ => hf n z hz
  refine local_hasFDerivAt_of_tendstoUniformlyOnFilter ?_ h4 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

/-- Uniform limits of the values and first two jets of smooth approximants on a closed ball have
first and second jets equal to those of the limiting `C²` function on the inner open ball. This
local identification is the derivative-limit step needed after diagonal compactness; it does not
construct approximation families on all of `U`. -/

private theorem identify_extracted_jets_on_inner_open_ball
    {n : ℕ} (center : EuclideanSpace ℂ (Fin n)) {ρ R : ℝ} (hρR : ρ < R)
    {vseq : ℕ → EuclideanSpace ℂ (Fin n) → ℝ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    {ψ : ℕ → ℕ}
    {g₀ : Metric.closedBall center ρ → ℝ}
    {g₁ : Metric.closedBall center ρ →
      (EuclideanSpace ℂ (Fin n)) [×1]→L[ℝ] ℝ}
    {g₂ : Metric.closedBall center ρ →
      (EuclideanSpace ℂ (Fin n)) [×2]→L[ℝ] ℝ}
    (hSmooth : ∀ m, ContDiffOn ℝ 2 (vseq (ψ m)) (Metric.ball center R))
    (hu : ContDiffOn ℝ 2 u (Metric.ball center R))
    (hvalues : ∀ x : Metric.closedBall center ρ, g₀ x = u (x : EuclideanSpace ℂ (Fin n)))
    (h₀ : TendstoUniformly
      (fun m (x : Metric.closedBall center ρ) => vseq (ψ m) (x : EuclideanSpace ℂ (Fin n)))
      g₀ atTop)
    (h₁ : TendstoUniformly
      (fun m (x : Metric.closedBall center ρ) =>
        iteratedFDeriv ℝ 1 (vseq (ψ m)) (x : EuclideanSpace ℂ (Fin n))) g₁ atTop)
    (h₂ : TendstoUniformly
      (fun m (x : Metric.closedBall center ρ) =>
        iteratedFDeriv ℝ 2 (vseq (ψ m)) (x : EuclideanSpace ℂ (Fin n))) g₂ atTop) :
    (∀ x (hx : x ∈ Metric.ball center ρ),
      ContDiffAt ℝ 2 u x ∧
      g₁ ⟨x, Metric.ball_subset_closedBall hx⟩ = iteratedFDeriv ℝ 1 u x ∧
      g₂ ⟨x, Metric.ball_subset_closedBall hx⟩ = iteratedFDeriv ℝ 2 u x) ∧
    TendstoUniformlyOn (fun m x => vseq (ψ m) x) u atTop (Metric.ball center ρ) ∧
    TendstoUniformlyOn (fun m x => iteratedFDeriv ℝ 1 (vseq (ψ m)) x)
      (iteratedFDeriv ℝ 1 u) atTop (Metric.ball center ρ) ∧
    TendstoUniformlyOn (fun m x => iteratedFDeriv ℝ 2 (vseq (ψ m)) x)
      (iteratedFDeriv ℝ 2 u) atTop (Metric.ball center ρ) := by
  classical
  let E := EuclideanSpace ℂ (Fin n)
  let K := Metric.closedBall center ρ
  let curry₁ := continuousMultilinearCurryFin1 ℝ E ℝ
  let G₁ : E → E →L[ℝ] ℝ := fun y =>
    if hy : y ∈ K then curry₁ (g₁ ⟨y, hy⟩) else 0
  have hcurry₁lip : LipschitzWith 1 curry₁ := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [curry₁.dist_map]
    simp
  have h₁curry : TendstoUniformly
      (fun m (y : K) => curry₁ (iteratedFDeriv ℝ 1 (vseq (ψ m)) (y : E)))
      (fun y => curry₁ (g₁ y)) atTop :=
    hcurry₁lip.uniformContinuous.comp_tendstoUniformly h₁
  have h₁on : TendstoUniformlyOn
      (fun m y => curry₁ (iteratedFDeriv ℝ 1 (vseq (ψ m)) y)) G₁ atTop K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have htarget : (fun y : K => G₁ (y : E)) = fun y => curry₁ (g₁ y) := by
      funext y
      simp only [G₁, dite_eq_left y.property]
      rfl
    change TendstoUniformly _ (fun y : K => G₁ (y : E)) atTop
    rw [htarget]
    exact h₁curry
  have h₁loc : TendstoLocallyUniformlyOn
      (fun m y => curry₁ (iteratedFDeriv ℝ 1 (vseq (ψ m)) y)) G₁ atTop
      (Metric.ball center ρ) :=
    h₁on.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
  have hvaluePoint : ∀ y ∈ Metric.ball center ρ,
      Tendsto (fun m => vseq (ψ m) y) atTop (𝓝 (u y)) := by
    intro y hy
    let yK : K := ⟨y, Metric.ball_subset_closedBall hy⟩
    simpa [hvalues yK] using h₀.tendsto_at yK
  have hder₁ : ∀ m y, y ∈ Metric.ball center ρ →
      HasFDerivAt (vseq (ψ m))
        (curry₁ (iteratedFDeriv ℝ 1 (vseq (ψ m)) y)) y := by
    intro m y hy
    have hyR : y ∈ Metric.ball center R := Metric.ball_subset_ball hρR.le hy
    have hAt : ContDiffAt ℝ 2 (vseq (ψ m)) y :=
      (hSmooth m).contDiffAt (Metric.isOpen_ball.mem_nhds hyR)
    have hhas := (hAt.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivAt
    have hEq : fderiv ℝ (vseq (ψ m)) y =
        continuousMultilinearCurryFin1 ℝ E ℝ
          (iteratedFDeriv ℝ 1 (vseq (ψ m)) y) := by
      ext v
      rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
      rfl
    rw [hEq] at hhas
    exact hhas
  have hfirst : ∀ x : E, ∀ hx : x ∈ Metric.ball center ρ,
      g₁ ⟨x, Metric.ball_subset_closedBall hx⟩ = iteratedFDeriv ℝ 1 u x := by
    intro x hx
    have hhas := local_hasFDerivAt_of_tendstoLocallyUniformlyOn
      Metric.isOpen_ball h₁loc hder₁ hvaluePoint hx
    have hxK : x ∈ K := Metric.ball_subset_closedBall hx
    have hhas' : fderiv ℝ u x = curry₁ (g₁ ⟨x, hxK⟩) := by
      simpa only [G₁, dite_eq_left hxK] using hhas.fderiv
    have hformula : fderiv ℝ u x =
        continuousMultilinearCurryFin1 ℝ E ℝ (iteratedFDeriv ℝ 1 u x) := by
      ext v
      rw [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
      rfl
    apply curry₁.injective
    calc
      curry₁ (g₁ ⟨x, Metric.ball_subset_closedBall hx⟩) = fderiv ℝ u x := hhas'.symm
      _ = curry₁ (iteratedFDeriv ℝ 1 u x) := hformula
  let curry₂ := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ
  let G₂ : E → E →L[ℝ] (E [×1]→L[ℝ] ℝ) := fun y =>
    if hy : y ∈ K then curry₂ (g₂ ⟨y, hy⟩) else 0
  have hcurry₂lip : LipschitzWith 1 curry₂ := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    rw [curry₂.dist_map]
    simp
  have h₂curry : TendstoUniformly
      (fun m (y : K) => curry₂ (iteratedFDeriv ℝ 2 (vseq (ψ m)) (y : E)))
      (fun y => curry₂ (g₂ y)) atTop :=
    hcurry₂lip.uniformContinuous.comp_tendstoUniformly h₂
  have h₂on : TendstoUniformlyOn
      (fun m y => curry₂ (iteratedFDeriv ℝ 2 (vseq (ψ m)) y)) G₂ atTop K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    have htarget : (fun y : K => G₂ (y : E)) = fun y => curry₂ (g₂ y) := by
      funext y
      simp only [G₂, dite_eq_left y.property]
      rfl
    change TendstoUniformly _ (fun y : K => G₂ (y : E)) atTop
    rw [htarget]
    exact h₂curry
  have h₂loc : TendstoLocallyUniformlyOn
      (fun m y => curry₂ (iteratedFDeriv ℝ 2 (vseq (ψ m)) y)) G₂ atTop
      (Metric.ball center ρ) :=
    h₂on.tendstoLocallyUniformlyOn.mono Metric.ball_subset_closedBall
  have hfirstPoint : ∀ y ∈ Metric.ball center ρ,
      Tendsto (fun m => iteratedFDeriv ℝ 1 (vseq (ψ m)) y) atTop
        (𝓝 (iteratedFDeriv ℝ 1 u y)) := by
    intro y hy
    let yK : K := ⟨y, Metric.ball_subset_closedBall hy⟩
    have ht := h₁.tendsto_at yK
    rw [hfirst y hy] at ht
    simpa [yK] using ht
  have hder₂ : ∀ m y, y ∈ Metric.ball center ρ →
      HasFDerivAt (iteratedFDeriv ℝ 1 (vseq (ψ m)))
        (curry₂ (iteratedFDeriv ℝ 2 (vseq (ψ m)) y)) y := by
    intro m y hy
    have hyR : y ∈ Metric.ball center R := Metric.ball_subset_ball hρR.le hy
    have hAt : ContDiffAt ℝ 2 (vseq (ψ m)) y :=
      (hSmooth m).contDiffAt (Metric.isOpen_ball.mem_nhds hyR)
    have hdiff := hAt.differentiableAt_iteratedFDeriv (by norm_num : (↑(1 : ℕ) : ℕ∞ω) < 2)
    have hhas := hdiff.hasFDerivAt
    have hfd := congrFun
      (fderiv_iteratedFDeriv (𝕜 := ℝ) (f := vseq (ψ m)) (n := 1)) y
    rw [hfd] at hhas
    exact hhas
  have hsecond : ∀ x : E, ∀ hx : x ∈ Metric.ball center ρ,
      g₂ ⟨x, Metric.ball_subset_closedBall hx⟩ = iteratedFDeriv ℝ 2 u x := by
    intro x hx
    have hhas := local_hasFDerivAt_of_tendstoLocallyUniformlyOn
      Metric.isOpen_ball h₂loc hder₂ hfirstPoint hx
    have hxK : x ∈ K := Metric.ball_subset_closedBall hx
    have hhas' : fderiv ℝ (iteratedFDeriv ℝ 1 u) x = curry₂ (g₂ ⟨x, hxK⟩) := by
      simpa only [G₂, dite_eq_left hxK] using hhas.fderiv
    have hformula : fderiv ℝ (iteratedFDeriv ℝ 1 u) x =
        curry₂ (iteratedFDeriv ℝ 2 u x) := by
      have h := congrFun (fderiv_iteratedFDeriv (𝕜 := ℝ) (f := u) (n := 1)) x
      simpa [curry₂, Function.comp_apply] using h
    apply curry₂.injective
    calc
      curry₂ (g₂ ⟨x, Metric.ball_subset_closedBall hx⟩) =
          fderiv ℝ (iteratedFDeriv ℝ 1 u) x := hhas'.symm
      _ = curry₂ (iteratedFDeriv ℝ 2 u x) := hformula
  have hpoint : ∀ x (hx : x ∈ Metric.ball center ρ),
      ContDiffAt ℝ 2 u x ∧
        g₁ ⟨x, Metric.ball_subset_closedBall hx⟩ = iteratedFDeriv ℝ 1 u x ∧
        g₂ ⟨x, Metric.ball_subset_closedBall hx⟩ = iteratedFDeriv ℝ 2 u x := by
    intro x hx
    have hAt : ContDiffAt ℝ 2 u x :=
      hu.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρR.le hx))
    exact ⟨hAt, hfirst x hx, hsecond x hx⟩
  have h₀ball : TendstoUniformlyOn (fun m x => vseq (ψ m) x) u atTop
      (Metric.ball center ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp h₀) ε hε] with m hm
    intro x hx
    let xK : K := ⟨x, Metric.ball_subset_closedBall hx⟩
    have h := hm xK
    simpa [hvalues xK] using h
  have h₁ball : TendstoUniformlyOn
      (fun m x => iteratedFDeriv ℝ 1 (vseq (ψ m)) x) (iteratedFDeriv ℝ 1 u)
      atTop (Metric.ball center ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp h₁) ε hε] with m hm
    intro x hx
    let xK : K := ⟨x, Metric.ball_subset_closedBall hx⟩
    have h := hm xK
    rw [hfirst x hx] at h
    simpa [xK] using h
  have h₂ball : TendstoUniformlyOn
      (fun m x => iteratedFDeriv ℝ 2 (vseq (ψ m)) x) (iteratedFDeriv ℝ 2 u)
      atTop (Metric.ball center ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp h₂) ε hε] with m hm
    intro x hx
    let xK : K := ⟨x, Metric.ball_subset_closedBall hx⟩
    have h := hm xK
    rw [hsecond x hx] at h
    simpa [xK] using h
  exact ⟨hpoint, h₀ball, h₁ball, h₂ball⟩

end BaseSchauderJetLimit

/-- Decompose a change in the complex elliptic operator into a coefficient error and a Hessian
error. This is the algebraic residual identity used when comparing mollified coefficients and
mollified second jets. -/
private theorem complexEllipticOp_residual_decomposition {n : ℕ}
    (A B : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n) → ℝ) (z : EuclideanSpace ℂ (Fin n)) :
    complexEllipticOp A u z - complexEllipticOp B v z =
      RCLike.re (((A z - B z) * complexHessian u z).trace) +
        RCLike.re ((B z * (complexHessian u z - complexHessian v z)).trace) := by
  change Complex.re ((A z * complexHessian u z).trace) -
      Complex.re ((B z * complexHessian v z).trace) =
    Complex.re (((A z - B z) * complexHessian u z).trace) +
      Complex.re ((B z * (complexHessian u z - complexHessian v z)).trace)
  have hmat : A z * complexHessian u z - B z * complexHessian v z =
      (A z - B z) * complexHessian u z +
        B z * (complexHessian u z - complexHessian v z) := by noncomm_ring
  calc
    Complex.re ((A z * complexHessian u z).trace) -
        Complex.re ((B z * complexHessian v z).trace) =
        Complex.re ((A z * complexHessian u z).trace -
          (B z * complexHessian v z).trace) := by rw [← Complex.sub_re]
    _ = Complex.re ((A z * complexHessian u z -
        B z * complexHessian v z).trace) := by rw [← Matrix.trace_sub]
    _ = Complex.re (((A z - B z) * complexHessian u z +
        B z * (complexHessian u z - complexHessian v z)).trace) := by rw [hmat]
    _ = Complex.re (((A z - B z) * complexHessian u z).trace) +
        Complex.re ((B z * (complexHessian u z - complexHessian v z)).trace) := by
          rw [Matrix.trace_add, Complex.add_re]

/-- Near/far interpolation turns a supremum bound at scale `ε` and a Lipschitz bound at that
scale into a uniform `C^α` modulus. For mollifier commutators, `C ε^α` is supplied by the product
of the coefficient Hölder seminorm and the local modulus of continuity of the Hessian. -/
private theorem holder_distance_of_sup_lipschitz
    {E : Type*} [PseudoMetricSpace E] {f : E → ℝ} {α ε C : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1) (hε : 0 < ε) (hC : 0 ≤ C)
    (hSup : ∀ x, |f x| ≤ C * ε ^ α)
    (hLip : ∀ x y, |f x - f y| ≤ C * dist x y / ε ^ (1 - α)) :
    ∀ x y, |f x - f y| ≤ 2 * C * dist x y ^ α := by
  intro x y
  let d := dist x y
  by_cases hnear : d ≤ ε
  · by_cases hd : d = 0
    · have hzero : |f x - f y| = 0 := by
        have hle : |f x - f y| ≤ 0 := by simpa [d, hd] using hLip x y
        exact le_antisymm hle (abs_nonneg _)
      rw [hzero]
      positivity
    · have hdpos : 0 < d := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
      have hpow : d ^ (1 - α) ≤ ε ^ (1 - α) :=
        Real.rpow_le_rpow dist_nonneg hnear (by linarith)
      have hd_eq : d = d ^ α * d ^ (1 - α) := by
        calc
          d = d ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = d ^ (α + (1 - α)) := by congr 1; ring
          _ = d ^ α * d ^ (1 - α) := by rw [Real.rpow_add hdpos]
      have hscale : d / ε ^ (1 - α) ≤ d ^ α := by
        rw [div_le_iff₀ (Real.rpow_pos_of_pos hε _)]
        calc
          d = d ^ α * d ^ (1 - α) := hd_eq
          _ ≤ d ^ α * ε ^ (1 - α) :=
            mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg dist_nonneg _)
      have hmain := hLip x y
      change |f x - f y| ≤ C * d / ε ^ (1 - α) at hmain
      calc
        |f x - f y| ≤ C * d / ε ^ (1 - α) := hmain
        _ ≤ C * d ^ α := by
          calc
            C * d / ε ^ (1 - α) = C * (d / ε ^ (1 - α)) := by ring
            _ ≤ C * d ^ α := mul_le_mul_of_nonneg_left hscale hC
        _ ≤ 2 * C * d ^ α := by
          have hn : 0 ≤ C * d ^ α := mul_nonneg hC (Real.rpow_nonneg dist_nonneg _)
          linarith
  · have hfar : ε ≤ d := le_of_not_ge hnear
    have hpow : ε ^ α ≤ d ^ α := Real.rpow_le_rpow (le_of_lt hε) hfar hα₀.le
    have habs : |f x - f y| ≤ |f x| + |f y| := by
      calc
        |f x - f y| = |f x + -f y| := by congr 1
        _ ≤ |f x| + |-f y| := abs_add_le _ _
        _ = |f x| + |f y| := by simp
    calc
      |f x - f y| ≤ |f x| + |f y| := habs
      _ ≤ C * ε ^ α + C * ε ^ α := add_le_add (hSup x) (hSup y)
      _ = 2 * C * ε ^ α := by ring
      _ ≤ 2 * C * d ^ α := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- A function on a subsingleton domain has the order-two Hölder bound whenever its values
are bounded. All positive-order derivatives vanish, and the top-order Hölder condition is
vacuous on a subsingleton set. -/
private theorem holderBoundOn_two_of_subsingleton_domain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    {α K₀ K₁ : ℝ≥0} {s : Set E} {f : E → ℝ}
    (hbound : ∀ z ∈ s, |f z| ≤ K₀) :
    HolderBoundOn 2 α (K₁ + K₀) s f := by
  have hf : f = fun _ : E => f 0 := funext fun z => by
    congr 1
    exact Subsingleton.elim z 0
  refine ⟨?_, ?_⟩
  · intro j hj z hz
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with hj' | hj' | hj'
    · subst j
      have hb : ‖iteratedFDeriv ℝ 0 f z‖ ≤ (K₀ : ℝ) := by
        simpa [iteratedFDeriv_zero_eq_comp, Real.norm_eq_abs] using hbound z hz
      have hsum : K₀ ≤ K₁ + K₀ := by
        exact le_add_of_nonneg_left (show 0 ≤ K₁ from zero_le)
      exact_mod_cast hb.trans (by exact_mod_cast hsum)
    · subst j
      have hderiv : iteratedFDeriv ℝ 1 f = 0 := by
        rw [hf]
        exact iteratedFDeriv_const_of_ne (by norm_num) _
      rw [hderiv]
      simpa using (show (0 : ℝ) ≤ (K₁ + K₀ : ℝ) by positivity)
    · subst j
      have hderiv : iteratedFDeriv ℝ 2 f = 0 := by
        rw [hf]
        exact iteratedFDeriv_const_of_ne (by norm_num) _
      rw [hderiv]
      simpa using (show (0 : ℝ) ≤ (K₁ + K₀ : ℝ) by positivity)
  · have hs : s.Subsingleton := fun x hx y hy => Subsingleton.elim x y
    exact hs.holderOnWith (K₁ + K₀) α (iteratedFDeriv ℝ 2 f)

/-- The positive-dimensional local ball estimate is the only analytic input left in the smooth-data
base slice. Its constant is independent of the coefficient, potential, and source bounds. -/
private theorem smoothInteriorSchauderBallEstimate (n : ℕ) (hn : 0 < n) :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
      ∀ (lam K : ℝ≥0), 0 < lam →
        ∀ c : EuclideanSpace ℂ (Fin n), ∀ R S : ℝ, 0 < R → R < S →
          ∃ C : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
            (u : EuclideanSpace ℂ (Fin n) → ℝ),
            (∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A z j l) (Metric.ball c S)) →
            ContDiffOn ℝ ∞ u (Metric.ball c S) →
            IsUniformlyEllipticOn A lam (Metric.ball c S) →
            (∀ j l, HolderBoundOn 0 α K (Metric.ball c S) fun z ↦ A z j l) →
            ∀ K₀ K₁ : ℝ≥0,
              ContDiffOn ℝ 0 (complexEllipticOp A u) (Metric.ball c S) →
              HolderBoundOn 0 α K₁ (Metric.ball c S) (complexEllipticOp A u) →
              (∀ z ∈ Metric.ball c S, |u z| ≤ K₀) →
              HolderBoundOn 2 α (C * (K₁ + K₀))
                (Metric.closedBall c (R / 2)) u := by
  exact CalabiYau.Schauder.smoothInteriorSchauderBallEstimate n hn

/-- The non-circular smooth-data `k = 0` Schauder estimate (the S2 input to the base slice). -/
private theorem smoothInteriorSchauderBaseEstimate (n : ℕ) :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
      ∀ (lam K : ℝ≥0), 0 < lam →
        ∀ U V : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → IsCompact (closure V) →
          closure V ⊆ U →
          ∃ C : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
            (u : EuclideanSpace ℂ (Fin n) → ℝ),
            (∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A z j l) U) → ContDiffOn ℝ ∞ u U →
            IsUniformlyEllipticOn A lam U →
            (∀ j l, HolderBoundOn 0 α K U fun z ↦ A z j l) →
            ∀ K₀ K₁ : ℝ≥0, ContDiffOn ℝ 0 (complexEllipticOp A u) U →
              HolderBoundOn 0 α K₁ U (complexEllipticOp A u) →
              (∀ z ∈ U, |u z| ≤ K₀) →
              HolderBoundOn 2 α (C * (K₁ + K₀)) V u := by
  intro α hα₀ hα₁ lam hlam K U V hU hV hVU
  by_cases hn : n = 0
  · subst n
    refine ⟨1, ?_⟩
    intro A u hA hu hEll hAH K₀ K₁ hL₀ hLH hBound
    have hLocal : HolderBoundOn 2 α (K₁ + K₀) V u := by
      apply holderBoundOn_two_of_subsingleton_domain
      intro z hz
      exact hBound z (hVU (subset_closure hz))
    simpa only [one_mul] using hLocal
  · classical
    obtain ⟨N, c, r, R, S, hr, hpatchSubset, hcover⟩ :=
      exists_baseSchauderFinitePatchCover hU hV hVU
    have hRpos (i : Fin N) : 0 < R i := by
      linarith [(hr i).1, (hr i).2.1]
    let Cpatch : Fin N → ℝ≥0 := fun i =>
      Classical.choose (smoothInteriorSchauderBallEstimate n (Nat.pos_of_ne_zero hn)
        α hα₀ hα₁ lam hlam K (c i) (R i) (S i) (hRpos i) (hr i).2.2)
    have hPatch (i : Fin N) := Classical.choose_spec
      (smoothInteriorSchauderBallEstimate n (Nat.pos_of_ne_zero hn)
        α hα₀ hα₁ lam hlam K (c i) (R i) (S i) (hRpos i) (hr i).2.2)
    have hUball (i : Fin N) : Metric.ball (c i) (S i) ⊆ U := by
      intro z hz
      exact hpatchSubset i (Metric.ball_subset_closedBall hz)
    obtain ⟨Cglobal, hGlobal⟩ :=
      holderBoundOn_two_of_finiteQuarterCover hα₀ N c r R S hr hcover Cpatch
    refine ⟨Cglobal, ?_⟩
    intro A u hA hu hEll hAH K₀ K₁ hL₀ hLH hBound
    have hlocal (i : Fin N) :
        HolderBoundOn 2 α (Cpatch i * (K₁ + K₀))
          (Metric.closedBall (c i) (R i / 2)) u := by
      have h := hPatch i A u
        (fun j l => (hA j l).mono (hUball i))
        (hu.mono (hUball i))
        (fun z hz => hEll z (hUball i hz))
        (fun j l => (hAH j l).mono_set (hUball i))
        K₀ K₁ (hL₀.mono (hUball i)) (hLH.mono_set (hUball i))
        (fun z hz => hBound z (hUball i hz))
      simpa [Cpatch] using h
    exact hGlobal (K₁ + K₀) u hlocal

/- The legacy all-U datum and its proved conditional consumers are retained above and below.
Its unproved constructor is deliberately retired: the public theorem now constructs fixed-radius
local data on compactly buffered patches. This does not assert the old all-U existence claim. -/

open Filter

private noncomputable def complexHessianFromSecondJet {n : ℕ}
    (D : (EuclideanSpace ℂ (Fin n)) [×2]→L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ := fun j k =>
      ((D ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ) +
        D ![Complex.I • EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] +
        Complex.I * (D ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1] -
          D ![Complex.I • EuclideanSpace.single j 1, EuclideanSpace.single k 1])) / 4

private theorem complexHessian_eq_fromSecondJet {n : ℕ}
    {v : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hv : ContDiffAt ℝ 2 v z) :
    complexHessian v z = complexHessianFromSecondJet (iteratedFDeriv ℝ 2 v z) := by
  ext j k
  rw [complexHessian_apply hv]
  simp [complexHessianFromSecondJet, iteratedFDeriv_two_apply]

private theorem continuous_complexHessianFromSecondJet {n : ℕ} :
    Continuous (complexHessianFromSecondJet (n := n)) := by
  fun_prop [complexHessianFromSecondJet]

private theorem complexHessian_tendsto_of_secondJet
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {vseq : ι → EuclideanSpace ℂ (Fin n) → ℝ}
    {v : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hseq : ∀ m, ContDiffAt ℝ 2 (vseq m) z)
    (hv : ContDiffAt ℝ 2 v z)
    (hjet : Tendsto (fun m => iteratedFDeriv ℝ 2 (vseq m) z) l
      (𝓝 (iteratedFDeriv ℝ 2 v z))) :
    Tendsto (fun m => complexHessian (vseq m) z) l (𝓝 (complexHessian v z)) := by
  have h := (continuous_complexHessianFromSecondJet (n := n)).continuousAt.tendsto.comp hjet
  have hseqEq (m) := complexHessian_eq_fromSecondJet (hseq m)
  have hvEq := complexHessian_eq_fromSecondJet hv
  have h' : Tendsto (fun m => complexHessianFromSecondJet (iteratedFDeriv ℝ 2 (vseq m) z)) l
      (𝓝 (complexHessianFromSecondJet (iteratedFDeriv ℝ 2 v z))) := by
    convert h using 1
    rfl
  have h'' : Tendsto (fun m => complexHessian (vseq m) z) l
      (𝓝 (complexHessianFromSecondJet (iteratedFDeriv ℝ 2 v z))) := by
    exact h'.congr' (Filter.Eventually.of_forall fun m => (hseqEq m).symm)
  simpa only [hvEq] using h''

private theorem complexTraceOperator_tendsto_of_matrix_tendsto
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {Aseq Hseq : ι → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {A H : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    (z : EuclideanSpace ℂ (Fin n))
    (hA : Tendsto (fun m => Aseq m z) l (𝓝 (A z)))
    (hH : Tendsto (fun m => Hseq m z) l (𝓝 (H z))) :
    Tendsto (fun m => Complex.re ((Aseq m z * Hseq m z).trace)) l
      (𝓝 (Complex.re ((A z * H z).trace))) := by
  let Φ : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ → ℝ :=
    fun p => Complex.re ((p.1 * p.2).trace)
  have hΦ : Continuous Φ := by fun_prop
  have hp : Tendsto (fun m => (Aseq m z, Hseq m z)) l (𝓝 (A z, H z)) :=
    hA.prodMk_nhds hH
  have := hΦ.continuousAt.tendsto.comp hp
  simpa [Φ, Function.comp_def] using this

private theorem complexEllipticOp_tendsto_of_entrywise_coeff_and_secondJet
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {Aseq : ι → EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {vseq : ι → EuclideanSpace ℂ (Fin n) → ℝ}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {v : EuclideanSpace ℂ (Fin n) → ℝ} {z : EuclideanSpace ℂ (Fin n)}
    (hA : ∀ j k, Tendsto (fun m => Aseq m z j k) l (𝓝 (A z j k)))
    (hseq : ∀ m, ContDiffAt ℝ 2 (vseq m) z)
    (hv : ContDiffAt ℝ 2 v z)
    (hjet : Tendsto (fun m => iteratedFDeriv ℝ 2 (vseq m) z) l
      (𝓝 (iteratedFDeriv ℝ 2 v z))) :
    Tendsto (fun m => complexEllipticOp (Aseq m) (vseq m) z) l
      (𝓝 (complexEllipticOp A v z)) := by
  have hAmat : Tendsto (fun m => Aseq m z) l (𝓝 (A z)) := by
    exact tendsto_pi_nhds.mpr fun j => tendsto_pi_nhds.mpr fun k => hA j k
  have hH := complexHessian_tendsto_of_secondJet hseq hv hjet
  have hTrace := complexTraceOperator_tendsto_of_matrix_tendsto z hAmat hH
  simpa [complexEllipticOp] using hTrace

private theorem iteratedFDeriv_zero_tendsto_of_tendsto
    {ι : Type*} {l : Filter ι} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {fseq : ι → E → ℝ} {f : E → ℝ} {z : E}
    (h : Tendsto (fun m => fseq m z) l (𝓝 (f z))) :
    Tendsto (fun m => iteratedFDeriv ℝ 0 (fseq m) z) l
      (𝓝 (iteratedFDeriv ℝ 0 f z)) := by
  let ψ := (continuousMultilinearCurryFin0 ℝ E ℝ).symm
  have hψ : Continuous ψ := by fun_prop
  have h' : Tendsto (fun m => ψ (fseq m z)) l (𝓝 (ψ (f z))) :=
    hψ.continuousAt.tendsto.comp h
  have hseqEq : (fun m => iteratedFDeriv ℝ 0 (fseq m) z) =
      (fun m => ψ (fseq m z)) := by
    funext m
    simp [iteratedFDeriv_zero_eq_comp, ψ]
  have hEq : iteratedFDeriv ℝ 0 f z = ψ (f z) := by
    simp [iteratedFDeriv_zero_eq_comp, ψ]
  simpa only [hseqEq, hEq] using h'

private theorem holderOnWith_of_pointwise_limit_varying_bound
    {X F : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace F]
    {α B : ℝ≥0} {Bseq : ℕ → ℝ≥0} {fseq : ℕ → X → F} {f : X → F} {s : Set X}
    (hconv : ∀ x ∈ s, Tendsto (fun m => fseq m x) Filter.atTop (𝓝 (f x)))
    (hHolder : ∀ m, HolderOnWith (Bseq m) α (fseq m) s)
    (hBlim : Filter.Tendsto Bseq Filter.atTop (𝓝 B)) :
    HolderOnWith B α f s := by
  intro x hx y hy
  have hxlim := hconv x hx
  have hylim := hconv y hy
  have hleft : Filter.Tendsto (fun m => edist (fseq m x) (fseq m y)) Filter.atTop
      (𝓝 (edist (f x) (f y))) := hxlim.edist hylim
  have hcoe : Continuous (fun b : NNReal => (b : ENNReal)) := by fun_prop
  have hcoef : Filter.Tendsto (fun m => (Bseq m : ENNReal)) Filter.atTop
      (𝓝 (B : ENNReal)) := hcoe.continuousAt.tendsto.comp hBlim
  have hright : Filter.Tendsto
      (fun m => (Bseq m : ENNReal) * edist x y ^ (α : ℝ)) Filter.atTop
      (𝓝 ((B : ENNReal) * edist x y ^ (α : ℝ))) :=
    ENNReal.Tendsto.mul_const hcoef
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg
        (show 0 ≤ (α : ℝ) from NNReal.coe_nonneg α) (edist_ne_top x y)))
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.Eventually.of_forall fun m => hHolder m x hx y hy

/-- A varying Hölder constant passes to the limit together with locally uniform convergence. -/
private theorem holderOnWith_of_localUniform_limit_varying_bound
    {X F : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace F]
    {α B : ℝ≥0} {Bseq : ℕ → ℝ≥0} {fseq : ℕ → X → F} {f : X → F} {s : Set X}
    (hconv : TendstoLocallyUniformlyOn fseq f Filter.atTop s)
    (hHolder : ∀ m, HolderOnWith (Bseq m) α (fseq m) s)
    (hBlim : Filter.Tendsto Bseq Filter.atTop (nhds B)) :
    HolderOnWith B α f s := by
  intro x hx y hy
  have hxlim : Filter.Tendsto (fun m => fseq m x) Filter.atTop (𝓝 (f x)) :=
    hconv.tendsto_at hx
  have hylim : Filter.Tendsto (fun m => fseq m y) Filter.atTop (𝓝 (f y)) :=
    hconv.tendsto_at hy
  have hleft : Filter.Tendsto (fun m => edist (fseq m x) (fseq m y)) Filter.atTop
      (𝓝 (edist (f x) (f y))) := hxlim.edist hylim
  have hcoe : Continuous (fun b : NNReal => (b : ENNReal)) := by fun_prop
  have hcoef : Filter.Tendsto (fun m => (Bseq m : ENNReal)) Filter.atTop
      (𝓝 (B : ENNReal)) := hcoe.continuousAt.tendsto.comp hBlim
  have hright : Filter.Tendsto
      (fun m => (Bseq m : ENNReal) * edist x y ^ (α : ℝ)) Filter.atTop
      (𝓝 ((B : ENNReal) * edist x y ^ (α : ℝ))) :=
    ENNReal.Tendsto.mul_const hcoef
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg
        (show 0 ≤ (α : ℝ) from NNReal.coe_nonneg α) (edist_ne_top x y)))
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.Eventually.of_forall fun m => hHolder m x hx y hy

/-- Pass a smooth-data estimate through the explicit local approximation and limit data. -/
private theorem baseSchauderLimit_of_smoothEstimate {n : ℕ}
    {α lam K K₀ K₁ C : ℝ≥0} {U V : Set (EuclideanSpace ℂ (Fin n))}
    {A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ}
    {u : EuclideanSpace ℂ (Fin n) → ℝ}
    (hU : IsOpen U) (hVU : closure V ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hApprox : BaseSchauderApproximationData α lam K K₀ K₁ U A u)
    (hSmooth : ∀ (A' : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
      (u' : EuclideanSpace ℂ (Fin n) → ℝ),
      (∀ j l, ContDiffOn ℝ ∞ (fun z ↦ A' z j l) U) → ContDiffOn ℝ ∞ u' U →
      IsUniformlyEllipticOn A' (lam / 2) U →
      (∀ j l, HolderBoundOn 0 α (K + 1) U fun z ↦ A' z j l) →
      ∀ K₀' K₁' : ℝ≥0, ContDiffOn ℝ 0 (complexEllipticOp A' u') U →
        HolderBoundOn 0 α K₁' U (complexEllipticOp A' u') →
        (∀ z ∈ U, |u' z| ≤ K₀') →
        HolderBoundOn 2 α (C * (K₁' + K₀')) V u') :
    HolderOnWith K₁ α (iteratedFDeriv ℝ 0 (complexEllipticOp A u)) U ∧
      HolderBoundOn 2 α (C * (K₁ + K₀)) V u := by
  rcases hApprox with ⟨ε, Aseq, useq, hε, hεle, hAsmooth, husmooth, hEll, hAH,
    hLH, hBound, hAconv, hDconv⟩
  let Bseq : ℕ → ℝ≥0 := fun m => C * ((K₁ + ε m) + (K₀ + ε m))
  let B : ℝ≥0 := C * (K₁ + K₀)
  have hBlim : Filter.Tendsto Bseq Filter.atTop (nhds B) := by
    have hcont : Continuous (fun e : ℝ≥0 => C * ((K₁ + e) + (K₀ + e))) := by fun_prop
    have h := hcont.continuousAt.tendsto.comp hε
    simpa [Bseq, B, Function.comp_def] using h
  let sourceSeq : ℕ → EuclideanSpace ℂ (Fin n) → ℝ := fun m z =>
    complexEllipticOp (Aseq m) (useq m) z
  have hSourceConv (z : EuclideanSpace ℂ (Fin n)) (hz : z ∈ U) :
      Filter.Tendsto (fun m => sourceSeq m z) Filter.atTop
        (𝓝 (complexEllipticOp A u z)) := by
    apply complexEllipticOp_tendsto_of_entrywise_coeff_and_secondJet
    · intro j l
      exact (hAconv j l).tendsto_at hz
    · intro m
      exact ((husmooth m).contDiffAt (hU.mem_nhds hz)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    · exact (hu z hz).contDiffAt (hU.mem_nhds hz)
    · exact (hDconv 2 (by omega)).tendsto_at hz
  let sourceBoundSeq : ℕ → ℝ≥0 := fun m => K₁ + ε m
  have hSourceBoundLim : Filter.Tendsto sourceBoundSeq Filter.atTop (nhds K₁) := by
    have hcont : Continuous (fun e : ℝ≥0 => K₁ + e) := by fun_prop
    have h := hcont.continuousAt.tendsto.comp hε
    simpa [sourceBoundSeq, Function.comp_def] using h
  have hSourceHolder : HolderOnWith K₁ α
      (iteratedFDeriv ℝ 0 (complexEllipticOp A u)) U := by
    apply holderOnWith_of_pointwise_limit_varying_bound
      (fun z hz => iteratedFDeriv_zero_tendsto_of_tendsto (hSourceConv z hz))
      (fun m => (hLH m).2) hSourceBoundLim
  have hEst (m : ℕ) :
      HolderBoundOn 2 α (Bseq m) V (useq m) := by
    dsimp [Bseq]
    have hLOpSmooth : ContDiffOn ℝ ∞ (complexEllipticOp (Aseq m) (useq m)) U :=
      complexEllipticOp_contDiffOn_of_smooth hU (hAsmooth m) (husmooth m)
    exact hSmooth (Aseq m) (useq m) (hAsmooth m) (husmooth m) (hEll m)
      (hAH m) (K₀ + ε m) (K₁ + ε m)
      (hLOpSmooth.of_le (WithTop.coe_le_coe.mpr le_top)) (hLH m) (hBound m)
  have hNorm : ∀ j ≤ 2, ∀ z ∈ V,
      ‖iteratedFDeriv ℝ j u z‖ ≤ B := by
    intro j hj z hz
    have hPoint := (hDconv j hj).tendsto_at (hVU (subset_closure hz))
    have hNormTendsto : Filter.Tendsto
        (fun m => ‖iteratedFDeriv ℝ j (useq m) z‖) Filter.atTop
        (𝓝 ‖iteratedFDeriv ℝ j u z‖) := hPoint.norm
    have hBReal : Filter.Tendsto (fun m => (Bseq m : ℝ)) Filter.atTop (𝓝 (B : ℝ)) := by
      have hcoe : Continuous (fun b : ℝ≥0 => (b : ℝ)) := continuous_subtype_val
      exact hcoe.continuousAt.tendsto.comp hBlim
    apply le_of_tendsto_of_tendsto hNormTendsto hBReal
    exact Filter.Eventually.of_forall fun m => (hEst m).1 j hj z hz
  refine ⟨hSourceHolder, ?_⟩
  refine ⟨hNorm, ?_⟩
  have hHolder : ∀ m, HolderOnWith (Bseq m) α
      (iteratedFDeriv ℝ 2 (useq m)) V := fun m => (hEst m).2
  have hD2 : TendstoLocallyUniformlyOn
      (fun m z => iteratedFDeriv ℝ 2 (useq m) z)
      (fun z => iteratedFDeriv ℝ 2 u z) Filter.atTop V :=
    (hDconv 2 (by omega)).mono (subset_closure.trans hVU)
  exact holderOnWith_of_localUniform_limit_varying_bound hD2 hHolder hBlim

/-- The exact `k = 0` slice of `InteriorSchauderEstimate`: for continuous coefficients and a
continuous complex elliptic operator, the `C²` solution has the interior `C^{2,α}` estimate. -/
theorem interiorSchauderBaseRegularity (n : ℕ) :
    ∀ (α : ℝ≥0), 0 < α → α < 1 →
      ∀ (lam K : ℝ≥0), 0 < lam →
        ∀ U V : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → IsCompact (closure V) →
          closure V ⊆ U →
          ∃ C : ℝ≥0, ∀ (A : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ)
            (u : EuclideanSpace ℂ (Fin n) → ℝ),
            (∀ j l, ContDiffOn ℝ 0 (fun z ↦ A z j l) U) → ContDiffOn ℝ 2 u U →
            IsUniformlyEllipticOn A lam U →
            (∀ j l, HolderBoundOn 0 α K U fun z ↦ A z j l) →
            ∀ K₀ K₁ : ℝ≥0, ContDiffOn ℝ 0 (complexEllipticOp A u) U →
              HolderBoundOn 0 α K₁ U (complexEllipticOp A u) →
              (∀ z ∈ U, |u z| ≤ K₀) →
              ContDiffOn ℝ 2 u U ∧ HolderBoundOn 2 α (C * (K₁ + K₀)) V u := by
  intro α hα₀ hα₁ lamb K hlam U V hU hV hVU
  by_cases hn : n = 0
  · subst n
    refine ⟨1, ?_⟩
    intro A u hA₀ hu hEll hAH K₀ K₁ hL₀ hLH hBound
    refine ⟨hu, ?_⟩
    have hLocal : HolderBoundOn 2 α (K₁ + K₀) V u := by
      apply holderBoundOn_two_of_subsingleton_domain
      intro z hz
      exact hBound z (hVU (subset_closure hz))
    simpa only [one_mul] using hLocal
  · classical
    obtain ⟨N, c, r, R, S, hr, hpatchSubset, hcover⟩ :=
      exists_baseSchauderFinitePatchCover hU hV hVU
    have hRpos (i : Fin N) : 0 < R i := by
      linarith [(hr i).1, (hr i).2.1]
    let Cpatch : Fin N → ℝ≥0 := fun i ↦ Classical.choose
      (CalabiYau.Schauder.localSchauderApproximationEstimate (Nat.pos_of_ne_zero hn)
        α lamb K hα₀ hα₁ hlam (R i) (S i) (hRpos i) (hr i).2.2)
    have hPatch (i : Fin N) := Classical.choose_spec
      (CalabiYau.Schauder.localSchauderApproximationEstimate (Nat.pos_of_ne_zero hn)
        α lamb K hα₀ hα₁ hlam (R i) (S i) (hRpos i) (hr i).2.2)
    obtain ⟨Cglobal, hGlobal⟩ :=
      holderBoundOn_two_of_finiteQuarterCover hα₀ N c r R S hr hcover Cpatch
    refine ⟨Cglobal, ?_⟩
    intro A u hA₀ hu hEll hAH K₀ K₁ hL₀ hLH hBound
    refine ⟨hu, hGlobal (K₁ + K₀) u ?_⟩
    intro i
    have hApprox := CalabiYau.Schauder.exists_localSchauderApproximationData
      hα₀ hα₁ hU (hRpos i) (hr i).2.2 (hpatchSubset i)
      hA₀ hu hEll hAH hL₀ hLH hBound
    exact hPatch i (c i) A u K₀ K₁ hApprox
