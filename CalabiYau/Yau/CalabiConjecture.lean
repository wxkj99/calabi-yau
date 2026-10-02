module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Geometry.Kahler.Ricci
public import CalabiYau.Geometry.Complex.DDBar.Basic
import CalabiYau.MongeAmpere.Uniqueness

/-!
# The Calabi conjecture

Let `(M, ω₀)` be a compact connected Kähler manifold.

* **Potential form (T2).** If `ρ - Ric(ω₀) = i∂∂̄F` with `F` smooth, there is a unique Kähler
  form `ω₀ + i∂∂̄φ` with Ricci form `ρ`.
* **Cohomological form (T3).** If `ρ` is a smooth real `(1,1)`-form with `[ρ] = 2π c₁(M)`, there
  is a unique Kähler form in the class `[ω₀]` with Ricci form `ρ`.

Existence is derived here from the solvability of the complex Monge–Ampère equation
(`KahlerForm.MongeAmpereSolvable`, proved in `CalabiYau.MongeAmpere.Existence` from the global
analytic inputs), and, for T3, from the `∂∂̄`-lemma (`SatisfiesDDBarLemma`, track H); both are
explicit hypotheses. Uniqueness needs neither.

## Proofs

T2, existence: choose `c` with `∫ e^{c - F} ω₀ⁿ = ∫ ω₀ⁿ` and solve `MA(φ) = e^{c - F}`. By
`ricciForm_perturb`, `Ric(ω_φ) = Ric(ω₀) - i∂∂̄(c - F) = ρ`.

T2, uniqueness: if `Ric(ω_φ) = Ric(ω_ψ)` then `i∂∂̄ log (ω_ψⁿ/ω_φⁿ) = 0`
(`ricciForm_eq_sub_mddbar`),
so `ω_ψⁿ = e^c ω_φⁿ` (`eq_const_of_mddbar_eq_zero`), `c = 0` by `integral_mongeAmpere`, and
`ψ - φ` is constant by Calabi's theorem (`eq_add_const_of_mongeAmpere_eq`).

T3: by `representsFirstChernClass_iff`, `ρ - Ric(ω₀)` is exact and `(1,1)`, hence `= i∂∂̄F` by
the `∂∂̄`-lemma; apply T2. Kähler forms cohomologous to `ω₀` are `ω₀ + i∂∂̄φ`
(`exists_perturb_eq_of_isExact`), which reduces uniqueness to T2.
-/

@[expose] public section

open scoped Manifold ContDiff

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

/-- **Calabi's uniqueness theorem**: in a Kähler class, a Kähler form is determined by its Ricci
form. -/
theorem perturb_eq_of_ricciForm_eq {ω₀ : KahlerForm n M} {φ ψ : M → ℝ} (hφ : ω₀.IsPotential φ)
    (hψ : ω₀.IsPotential ψ) (h : (ω₀.perturb φ hφ).ricciForm = (ω₀.perturb ψ hψ).ricciForm) :
    ω₀.perturb φ hφ = ω₀.perturb ψ hψ := by
  by_cases hM : IsEmpty M
  · ext x
    exact isEmptyElim (hM.false x)
  · let : Nonempty M := not_isEmpty_iff.mp hM
    let : MeasurableSpace M := borel M
    let : BorelSpace M := ⟨rfl⟩
    apply (KahlerForm.perturb_eq_perturb_iff hφ hψ).2
    let ωφ := ω₀.perturb φ hφ
    let ωψ := ω₀.perturb ψ hψ
    let u : M → ℝ := fun x ↦ ψ x - φ x
    have hsum : φ + u = ψ := by
      funext x
      simp [u]
    have hu : ωφ.IsPotential u := by
      apply (KahlerForm.isPotential_perturb_iff hφ).2
      exact hsum ▸ hψ
    have hpert : ωφ.perturb u hu = ωψ := by
      simpa only [hsum] using KahlerForm.perturb_perturb hφ hu
    have hlogzero : mddbar n (fun x ↦ Real.log (ContinuousAlternatingMap.relDet (ωφ x) (ωψ x))) = 0 := by
      have hdiff := KahlerForm.ricciForm_sub_ricciForm ωφ ωψ
      rw [h] at hdiff
      simpa [ωφ, ωψ] using hdiff.symm
    obtain ⟨c, hc⟩ := eq_const_of_mddbar_eq_zero
      (KahlerForm.contMDiff_log_relDet ωφ ωψ) hlogzero
    have hratio : ∀ x, ωφ.mongeAmpere u x = Real.exp c := by
      intro x
      rw [KahlerForm.mongeAmpere_eq_relDet_perturb hu x, hpert]
      calc
        ContinuousAlternatingMap.relDet (ωφ x) (ωψ x) =
            Real.exp (Real.log (ContinuousAlternatingMap.relDet (ωφ x) (ωψ x))) := by
              symm
              exact Real.exp_log (ContinuousAlternatingMap.relDet_pos (ωφ.isPositive x) (ωψ.isPositive x))
        _ = Real.exp c := by rw [hc x]
    have hma : ω₀.mongeAmpere ψ = fun x ↦ ω₀.mongeAmpere φ x * Real.exp c := by
      funext x
      rw [← hsum, KahlerForm.mongeAmpere_add hφ hu.1 x, hratio x]
    have hvol : (Real.exp c) * ω₀.volume.real Set.univ = ω₀.volume.real Set.univ := by
      calc
        Real.exp c * ω₀.volume.real Set.univ =
            ∫ x, ω₀.mongeAmpere φ x * Real.exp c ∂ω₀.volume := by
              rw [MeasureTheory.integral_mul_const, KahlerForm.integral_mongeAmpere hφ]
              ring
        _ = ∫ x, ω₀.mongeAmpere ψ x ∂ω₀.volume := by rw [← hma]
        _ = ω₀.volume.real Set.univ := KahlerForm.integral_mongeAmpere hψ
    have hc' : c = 0 := by
      have hv : ω₀.volume.real Set.univ ≠ 0 := by
        have hμ : ω₀.volume Set.univ ≠ 0 :=
          isOpen_univ.measure_ne_zero ω₀.volume Set.univ_nonempty
        exact (ENNReal.toReal_pos hμ (MeasureTheory.measure_ne_top ω₀.volume Set.univ)).ne'
      have he : Real.exp c = 1 := by
        apply mul_right_cancel₀ hv
        simpa [one_mul] using hvol
      exact Real.exp_injective (by simpa using he)
    have hmaeq : ω₀.mongeAmpere φ = ω₀.mongeAmpere ψ := by
      rw [hma, hc']
      simp
    obtain ⟨d, hd⟩ := KahlerForm.eq_add_const_of_mongeAmpere_eq hφ hψ hmaeq
    exact ⟨d, hd⟩

/-- Uniqueness in the cohomological form, under the `∂∂̄`-lemma. -/
theorem eq_of_ricciForm_eq_of_isExact (hdd : SatisfiesDDBarLemma n M) {ω₁ ω₂ : KahlerForm n M}
    (hc : (ω₂.toFormField - ω₁.toFormField).IsExact) (h : ω₁.ricciForm = ω₂.ricciForm) :
    ω₁ = ω₂ := by
  obtain ⟨φ, hφ, hpert⟩ := KahlerForm.exists_perturb_eq_of_isExact hdd ω₁ ω₂ hc
  have hric : (ω₁.perturb 0 KahlerForm.isPotential_zero).ricciForm =
      (ω₁.perturb φ hφ).ricciForm := by
    rw [KahlerForm.perturb_zero, hpert]
    exact h
  calc
    ω₁ = ω₁.perturb 0 KahlerForm.isPotential_zero := KahlerForm.perturb_zero.symm
    _ = ω₁.perturb φ hφ := KahlerForm.perturb_eq_of_ricciForm_eq
      KahlerForm.isPotential_zero hφ hric
    _ = ω₂ := hpert

variable [MeasurableSpace M] [BorelSpace M]

omit [ConnectedSpace M] in
/-- **The Calabi conjecture, potential form**, from the solvability of the Monge–Ampère
equation. -/
theorem exists_ricciForm_eq_of_sub_eq_mddbar (ω₀ : KahlerForm n M)
    (hMA : ω₀.MongeAmpereSolvable) {ρ : FormField (EuclideanSpace ℂ (Fin n)) M 2} {F : M → ℝ}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F)
    (hρ : ρ - ω₀.ricciForm = mddbar n F) :
    ∃ (φ : M → ℝ) (hφ : ω₀.IsPotential φ), (ω₀.perturb φ hφ).ricciForm = ρ := by
  by_cases hM : IsEmpty M
  · refine ⟨0, ω₀.isPotential_zero, ?_⟩
    ext x
    exact isEmptyElim (hM.false x)
  · let : Nonempty M := not_isEmpty_iff.mp hM
    let I : ℝ := ∫ x, Real.exp (-F x) ∂ω₀.volume
    let v : ℝ := ω₀.volume.real Set.univ
    let c : ℝ := Real.log (v / I)
    have hvol : 0 < v := by
      dsimp [v]
      apply ENNReal.toReal_pos
      · exact isOpen_univ.measure_ne_zero ω₀.volume Set.univ_nonempty
      · exact MeasureTheory.measure_ne_top ω₀.volume Set.univ
    have hcont : Continuous (fun x ↦ Real.exp (-F x)) :=
      Real.continuous_exp.comp (hF.continuous.neg)
    have hInt : MeasureTheory.Integrable (fun x ↦ Real.exp (-F x)) ω₀.volume := by
      exact MeasureTheory.integrableOn_univ.mp
        (hcont.continuousOn.integrableOn_compact isCompact_univ)
    have hI : 0 < I := by
      dsimp [I]
      apply MeasureTheory.integral_pos_of_integrable_nonneg_nonzero hcont hInt
      · intro x
        positivity
      · exact (Real.exp_pos (-F (Classical.choice (inferInstance : Nonempty M)))).ne'
    have hnorm : ∫ x, Real.exp (c - F x) ∂ω₀.volume = ω₀.volume.real Set.univ := by
      calc
        ∫ x, Real.exp (c - F x) ∂ω₀.volume =
            Real.exp c * ∫ x, Real.exp (-F x) ∂ω₀.volume := by
              have hfun : (fun x ↦ Real.exp (c - F x)) =
                  fun x ↦ Real.exp c * Real.exp (-F x) := by
                funext x
                rw [show c - F x = c + -F x by ring, Real.exp_add]
              rw [hfun]
              rw [MeasureTheory.integral_const_mul]
        _ = v := by
          dsimp [c, I]
          rw [Real.exp_log (div_pos hvol hI)]
          exact div_mul_cancel₀ _ hI.ne'
        _ = ω₀.volume.real Set.univ := rfl
    have hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (fun x ↦ c - F x) := by
      simpa using (contMDiff_const.sub hF)
    obtain ⟨φ, hsol⟩ := hMA (fun x ↦ c - F x) hG hnorm
    refine ⟨φ, hsol.1, ?_⟩
    rw [KahlerForm.ricciForm_perturb]
    have hlog : (fun x ↦ Real.log (ContinuousAlternatingMap.relDet (ω₀ x)
        (ω₀ x + mddbar n φ x))) = fun x ↦ c - F x := by
      funext x
      change Real.log (ω₀.mongeAmpere φ x) = c - F x
      rw [hsol.2 x, Real.log_exp]
    rw [hlog]
    rw [show mddbar n (fun x ↦ c - F x) = -mddbar n F by
      change mddbar n ((fun _ : M ↦ c) - F) = -mddbar n F
      simpa using (mddbar_sub (n := n) contMDiff_const hF)]
    have hρ' : ρ = ω₀.ricciForm + mddbar n F := by
      calc
        ρ = (ρ - ω₀.ricciForm) + ω₀.ricciForm := (sub_add_cancel _ _).symm
        _ = mddbar n F + ω₀.ricciForm := by rw [hρ]
        _ = ω₀.ricciForm + mddbar n F := add_comm _ _
    rw [hρ']
    simp [sub_eq_add_neg, add_comm]

omit [ConnectedSpace M] in
/-- **The Calabi conjecture, cohomological form**, from the solvability of the Monge–Ampère
equation and the `∂∂̄`-lemma. -/
theorem exists_ricciForm_eq_of_representsFirstChernClass (ω₀ : KahlerForm n M)
    (hMA : ω₀.MongeAmpereSolvable) (hdd : SatisfiesDDBarLemma n M)
    {ρ : FormField (EuclideanSpace ℂ (Fin n)) M 2} (hρs : ρ.IsSmooth) (hρ : ρ.IsOneOne)
    (hc : ((2 * Real.pi)⁻¹ • ρ).RepresentsFirstChernClass) :
    ∃ ω₁ : KahlerForm n M, (ω₁.toFormField - ω₀.toFormField).IsExact ∧ ω₁.ricciForm = ρ := by
  have hscaled : ((2 * Real.pi)⁻¹ • ρ - (2 * Real.pi)⁻¹ • ω₀.ricciForm).IsExact :=
    (FormField.representsFirstChernClass_iff ω₀).mp hc
  have hexact : (ρ - ω₀.ricciForm).IsExact := by
    have hscaled' : ((2 * Real.pi)⁻¹ • (ρ - ω₀.ricciForm)).IsExact := by
      rw [smul_sub]
      exact hscaled
    have hmul := hscaled'.smul (2 * Real.pi)
    have hp : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    simpa only [smul_smul, mul_inv_cancel₀ hp, one_smul] using hmul
  have hsmooth : (ρ - ω₀.ricciForm).IsSmooth := hρs.sub ω₀.isSmooth_ricciForm
  have hone : (ρ - ω₀.ricciForm).IsOneOne := fun x ↦
    (hρ x).sub (ω₀.isOneOne_ricciForm x)
  obtain ⟨F, hF, hddbar⟩ := hdd (ρ - ω₀.ricciForm) hsmooth hone hexact
  obtain ⟨φ, hφ, hric⟩ := exists_ricciForm_eq_of_sub_eq_mddbar ω₀ hMA hF hddbar
  exact ⟨ω₀.perturb φ hφ, KahlerForm.isExact_perturb_sub hφ, hric⟩

end KahlerForm
