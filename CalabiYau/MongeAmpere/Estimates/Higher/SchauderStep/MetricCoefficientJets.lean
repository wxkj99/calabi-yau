module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Analysis.Elliptic.Schauder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.BufferedInterpolation
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.CompactHolder
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep.ComplexHessianJets

/-!
# Uniform lower jets of the perturbed chart metric

A uniform potential bound on an outer compact buffer controls the complex Hessian and hence
all coefficient jets on the inner domain. The buffer converts bounds of the next derivative
into a COMMON Hölder estimate for every lower jet even across nearby components of the inner
set. Positivity of the perturbed metric gives invertibility throughout the chart target.

Source: Székelyhidi, *An Introduction to Extremal Kähler Metrics*, §2.3, Theorem 2.8,
p. 28; Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, §6.2.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder MatrixOrder

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]

private theorem perturbed_metric_coefficient_smooth_unit
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ω₀.SolvesMongeAmpere p.1 p.2)
    {x : M} : ∀ p ∈ S,
      (∀ i j, ContDiffOn ℝ ∞ (fun z ↦
        (ω₀.metricInChart x z + complexHessian
          (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) i j)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) ∧
      (∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
        IsUnit (ω₀.metricInChart x z + complexHessian
          (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)) := by
  intro p hp
  rcases hS p hp with ⟨hpot, -⟩
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  have hpotOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.2 Set.univ :=
    contMDiffOn_univ.mpr hpot.contMDiff
  have hcoord : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
      ∞ (p.2 ∘ e.symm) e.target := by
    exact hpotOn.comp (contMDiffOn_extChartAt_symm x) (by intro u hu; simp)
  have hcoord' : ContDiffOn ℝ ∞ (p.2 ∘ e.symm) e.target := hcoord.contDiffOn
  have hhess := contDiffOn_complexHessian_entries_of_contDiffOn hopen (p.2 ∘ e.symm) hcoord'
  constructor
  · intro i j
    exact (ω₀.contDiffOn_metricInChart x i j).add (hhess i j)
  · intro z hz
    have hpos : (ω₀.metricInChart x z + complexHessian (p.2 ∘ e.symm) z).PosDef := by
      simpa [e, ω₀.metricInChart_perturb hpot x hz] using
        (ω₀.perturb p.2 hpot).posDef_metricInChart x hz
    exact Matrix.PosDef.isUnit hpos

set_option maxHeartbeats 1000000 in
private theorem exists_uniform_perturbed_metric_coefficient_holder_on
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ω₀.SolvesMongeAmpere p.1 p.2)
    {x : M} {α : ℝ≥0} (hα₁ : α < 1)
    {r : ℕ} (hr : 2 ≤ r) {Cφ : ℝ≥0}
    {L : Set (EuclideanSpace ℂ (Fin n))}
    (hLcompact : IsCompact L)
    (hLtarget : L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hCurrentOuter : ∀ p ∈ S,
      HolderBoundOn r α Cφ L
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)) :
    ∃ C : ℝ≥0, ∀ p ∈ S, ∀ i j,
      HolderBoundOn (r - 2) α C L (fun z ↦
        (ω₀.metricInChart x z + complexHessian
          (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) i j) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  have hαle : α ≤ 1 := by exact_mod_cast hα₁.le
  let G : EuclideanSpace ℂ (Fin n) → Matrix (Fin n) (Fin n) ℂ := fun z => ω₀.metricInChart x z
  have hGsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun z => G z i j) e.target := by
    intro i j
    exact ω₀.contDiffOn_metricInChart x i j
  obtain ⟨Cg, hG⟩ := CompactSmoothHolder.exists_holderBoundOn_matrix_entries_of_contDiffOn_compact
    (k := r - 2) G hopen hLcompact hLtarget hαle hGsmooth
  have hφsmooth : ∀ p ∈ S, ContDiffOn ℝ ∞ (p.2 ∘ e.symm) e.target := by
    intro p hp
    rcases hS p hp with ⟨hpot, -⟩
    have hpotOn : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.2 Set.univ :=
      contMDiffOn_univ.mpr hpot.contMDiff
    have hcoord : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
        ∞ (p.2 ∘ e.symm) e.target := by
      exact hpotOn.comp (contMDiffOn_extChartAt_symm x) (by intro z hz; simp)
    exact hcoord.contDiffOn
  have hHfamily := exists_uniform_holderBoundOn_complexHessian_family_of_succ_succ
    (P := (M → ℝ) × (M → ℝ)) (n := n) (r := r) (W := e.target) (K := L)
    (α := α) (C := Cφ) S (fun p => p.2 ∘ e.symm) hopen hLtarget hr hφsmooth hCurrentOuter
  obtain ⟨Ch, hH⟩ := hHfamily
  refine ⟨Cg + Ch, ?_⟩
  intro p hp i j
  let g : EuclideanSpace ℂ (Fin n) → ℂ := fun z => G z i j
  let h : EuclideanSpace ℂ (Fin n) → ℂ := fun z => complexHessian (p.2 ∘ e.symm) z i j
  have hgHolder := hG i j
  have hhHolder := hH p hp i j
  have hgSmooth : ContDiffOn ℝ ∞ g e.target := by
    simpa [g, G] using hGsmooth i j
  have hhSmooth : ContDiffOn ℝ ∞ h e.target := by
    exact (contDiffOn_complexHessian_entries_of_contDiffOn hopen (p.2 ∘ e.symm)
      (hφsmooth p hp)) i j
  have hgAt : ∀ z ∈ L, ContDiffAt ℝ (r - 2) g z := by
    intro z hz
    have htop : ((r - 2 : ℕ) : ℕ∞ω) ≤ ∞ := by
      exact WithTop.coe_le_coe.mpr (show ((r - 2 : ℕ) : ℕ∞) ≤ ⊤ from le_top)
    exact (hgSmooth.contDiffAt (hopen.mem_nhds (hLtarget hz))).of_le htop
  have hhAt : ∀ z ∈ L, ContDiffAt ℝ (r - 2) h z := by
    intro z hz
    have htop : ((r - 2 : ℕ) : ℕ∞ω) ≤ ∞ := by
      exact WithTop.coe_le_coe.mpr (show ((r - 2 : ℕ) : ℕ∞) ≤ ⊤ from le_top)
    exact (hhSmooth.contDiffAt (hopen.mem_nhds (hLtarget hz))).of_le htop
  refine ⟨?_, ?_⟩
  · intro m hm z hz
    have hm' : (m : ℕ∞ω) ≤ ((r - 2 : ℕ) : ℕ∞ω) := by
      exact_mod_cast (show (m : ℕ∞) ≤ ((r - 2 : ℕ) : ℕ∞) from Nat.cast_le.mpr hm)
    have hgz := (hgAt z hz).of_le hm'
    have hhz := (hhAt z hz).of_le hm'
    have hadd := iteratedFDeriv_add_apply hgz hhz
    have hfun : (fun z => (ω₀.metricInChart x z +
        complexHessian (p.2 ∘ e.symm) z) i j) = g + h := by
      funext z
      simp [g, h, G]
    rw [hfun, hadd]
    calc
      ‖iteratedFDeriv ℝ m g z + iteratedFDeriv ℝ m h z‖ ≤
          ‖iteratedFDeriv ℝ m g z‖ + ‖iteratedFDeriv ℝ m h z‖ := norm_add_le _ _
      _ ≤ (Cg : ℝ) + Ch := add_le_add (hgHolder.1 m hm z hz) (hhHolder.1 m hm z hz)
  · have hgh : HolderWith Cg α (fun z : L => iteratedFDeriv ℝ (r - 2) g z) :=
      hgHolder.2.holderWith
    have hhh : HolderWith Ch α (fun z : L => iteratedFDeriv ℝ (r - 2) h z) :=
      hhHolder.2.holderWith
    have hsum := hgh.add hhh
    intro z hz w hw
    have haddz := iteratedFDeriv_add_apply (hgAt z hz) (hhAt z hz)
    have haddw := iteratedFDeriv_add_apply (hgAt w hw) (hhAt w hw)
    have hfun : (fun z => (ω₀.metricInChart x z +
        complexHessian (p.2 ∘ e.symm) z) i j) = g + h := by
      funext z
      simp [g, h, G]
    rw [hfun]
    change edist (iteratedFDeriv ℝ (r - 2) (g + h) z)
      (iteratedFDeriv ℝ (r - 2) (g + h) w) ≤ _
    rw [haddz, haddw]
    exact hsum ⟨z, hz⟩ ⟨w, hw⟩

set_option maxHeartbeats 1000000 in
private theorem exists_uniform_perturbed_metric_coefficient_lower_holder_on
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ω₀.SolvesMongeAmpere p.1 p.2)
    {x : M} {α : ℝ≥0} (hα₁ : α < 1)
    {r : ℕ} (hr : 2 ≤ r) {Cφ : ℝ≥0}
    {U L : Set (EuclideanSpace ℂ (Fin n))} {k : ℕ}
    (hLcompact : IsCompact L)
    (hBuffer : closure U ⊆ interior L)
    (hLtarget : L ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hk : k + 1 ≤ r - 2)
    (hCurrentOuter : ∀ p ∈ S,
      HolderBoundOn r α Cφ L
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)) :
    ∃ C : ℝ≥0, ∀ p ∈ S, ∀ i j,
      HolderBoundOn k α C U (fun z ↦
        (ω₀.metricInChart x z + complexHessian
          (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) i j) := by
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hopen : IsOpen e.target := isOpen_extChartAt_target x
  obtain ⟨Cout, hOuter⟩ := exists_uniform_perturbed_metric_coefficient_holder_on
    ω₀ S hS hα₁ hr hLcompact hLtarget hCurrentOuter
  let P := {p : (M → ℝ) × (M → ℝ) // p ∈ S} × (Fin n × Fin n)
  let T : Set P := Set.univ
  let A : P → EuclideanSpace ℂ (Fin n) → ℂ := fun q z =>
    (ω₀.metricInChart x z + complexHessian (q.1.1.2 ∘ e.symm) z) q.2.1 q.2.2
  have hAsmooth : ∀ q ∈ T, ContDiffOn ℝ ∞ (A q) e.target := by
    intro q hq
    have hqS : q.1.1 ∈ S := q.1.2
    have hcoeff := (perturbed_metric_coefficient_smooth_unit ω₀ S hS (x := x) q.1.1 hqS).1
    have hentry := hcoeff q.2.1 q.2.2
    simpa [A, e] using hentry
  have hAbound : ∀ q ∈ T, ∀ j ≤ k + 1, ∀ z ∈ L, ‖iteratedFDeriv ℝ j (A q) z‖ ≤ Cout := by
    intro q hq j hj z hz
    have hqS : q.1.1 ∈ S := q.1.2
    have hcoef := hOuter q.1.1 hqS q.2.1 q.2.2
    have hj' : j ≤ r - 2 := by omega
    have hbound := hcoef.1 j hj' z hz
    simpa [A, e] using hbound
  obtain ⟨Cinner, hInner⟩ := exists_uniform_holderBoundOn_family_of_buffered_derivative_bounds
    T A hopen hLcompact hBuffer hLtarget hα₁ hAsmooth hAbound
  refine ⟨Cinner, ?_⟩
  intro p hp i j
  have hq : (⟨⟨p, hp⟩, (i, j)⟩ : P) ∈ T := Set.mem_univ _
  simpa [A, T, P, e] using hInner _ hq

/-- The outer `C^{r,α}` potential bound supplies one bound for every matrix entry and every
lower-order Hölder jet of the perturbed chart metric, uniformly in the solution family. -/
theorem exists_uniform_perturbed_metric_coefficient_jets
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ω₀.SolvesMongeAmpere p.1 p.2)
    {x : M} {α : ℝ≥0} (hα₁ : α < 1)
    {r : ℕ} (hr : 2 ≤ r) {Cφ : ℝ≥0}
    {U L : Set (EuclideanSpace ℂ (Fin n))}
    (hLcompact : IsCompact L)
    (hBuffer : closure U ⊆ interior L)
    (hLtarget : L ⊆
      (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target)
    (hCurrentOuter : ∀ p ∈ S,
      HolderBoundOn r α Cφ L
        (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm)) :
    ∃ CA : ℝ≥0, ∀ p ∈ S,
      (∀ i j, ContDiffOn ℝ ∞ (fun z ↦
        (ω₀.metricInChart x z + complexHessian
          (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) i j)
        (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target) ∧
      (∀ z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).target,
        IsUnit (ω₀.metricInChart x z + complexHessian
          (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z)) ∧
      (∀ i j,
        (∀ m ≤ r - 2, ∀ z ∈ U, ‖iteratedFDeriv ℝ m (fun z ↦
          (ω₀.metricInChart x z + complexHessian
            (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) i j) z‖ ≤ CA) ∧
        (∀ m < r - 2, HolderOnWith CA α (iteratedFDeriv ℝ m (fun z ↦
          (ω₀.metricInChart x z + complexHessian
            (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) i j)) U) ∧
        HolderOnWith CA α (iteratedFDeriv ℝ (r - 2) (fun z ↦
          (ω₀.metricInChart x z + complexHessian
            (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x).symm) z) i j)) U) := by
  classical
  let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
  have hUL : U ⊆ L := fun z hz => interior_subset (hBuffer (subset_closure hz))
  obtain ⟨Cout, hOuter⟩ := exists_uniform_perturbed_metric_coefficient_holder_on
    ω₀ S hS hα₁ hr hLcompact hLtarget hCurrentOuter
  let Ck : ℕ → ℝ≥0 := fun k => if hk : k < r - 2 then
    Classical.choose (exists_uniform_perturbed_metric_coefficient_lower_holder_on ω₀ S hS hα₁ hr
      hLcompact hBuffer hLtarget (Nat.succ_le_of_lt hk) hCurrentOuter) else 0
  have hCk (k : ℕ) (hk : k < r - 2) :
      ∀ p ∈ S, ∀ i j, HolderBoundOn k α (Ck k) U (fun z ↦
        (ω₀.metricInChart x z + complexHessian
          (p.2 ∘ e.symm) z) i j) := by
    dsimp [Ck]
    rw [dif_pos hk]
    exact Classical.choose_spec (exists_uniform_perturbed_metric_coefficient_lower_holder_on
      ω₀ S hS hα₁ hr hLcompact hBuffer hLtarget
      (Nat.succ_le_of_lt hk) hCurrentOuter)
  let Cinner : ℝ≥0 := (Finset.range (r - 2)).sup Ck
  let CA : ℝ≥0 := max Cout Cinner
  have hCout : Cout ≤ CA := le_max_left _ _
  have hCinner : Cinner ≤ CA := le_max_right _ _
  refine ⟨CA, ?_⟩
  intro p hp
  obtain ⟨hsmooth, hunit⟩ := perturbed_metric_coefficient_smooth_unit ω₀ S hS (x := x) p hp
  refine ⟨hsmooth, hunit, ?_⟩
  intro i j
  have htop := (hOuter p hp i j).mono_set hUL
  refine ⟨?_, ?_⟩
  · intro m hm z hz
    exact (htop.1 m hm z hz).trans (by exact_mod_cast hCout)
  · refine ⟨?_, ?_⟩
    · intro m hm
      have hmem : m ∈ Finset.range (r - 2) := Finset.mem_range.mpr hm
      have hkbound : Ck m ≤ Cinner := Finset.le_sup hmem
      have hlower := hCk m hm p hp i j
      exact hlower.2.mono_const (le_trans hkbound hCinner)
    · exact htop.2.mono_const hCout

end KahlerForm

end
