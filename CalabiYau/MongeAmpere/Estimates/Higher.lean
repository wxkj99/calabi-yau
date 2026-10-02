module

public import CalabiYau.MongeAmpere.Operator
public import CalabiYau.Analysis.Elliptic.Schauder
import CalabiYau.MongeAmpere.Estimates.Higher.InitialBounds
import CalabiYau.MongeAmpere.Estimates.Higher.SchauderStep
import CalabiYau.MongeAmpere.Estimates.Higher.LinearizedMongeAmpere

/-!
# Higher-order estimates (Schauder bootstrap)

Let `S` be a family of solutions `(G, φ)` of `(ω₀ + i∂∂̄φ)ⁿ = e^G ω₀ⁿ` such that the `G`s are
bounded in every `C^k`, the `φ`s are uniformly bounded, `tr_ω₀ ω_φ ≤ Λ`, and the complex
Hessians `i∂∂̄φ` are uniformly bounded in `C¹` in every chart (the outputs of the `C⁰`, `C²` and
`C³` estimates). Then the `φ`s are bounded in every `C^k`.

The only analytic input is the interior Schauder estimate for the operators
`L_A u = re tr (A (u_{jk̄}))` on domains of `ℂⁿ` (`InteriorSchauderEstimate`), taken as an explicit
hypothesis.

## Proof sketch (Yau 1978, §4; Székelyhidi, Prop. 3.11 and §3.3; Gilbarg–Trudinger, Lemma 17.16)

Work in a chart, on compact subsets of the target. The `C¹` bound on `φ_{jk̄}` makes the
Euclidean Laplacian `4 ∑ φ_{jj̄}` bounded in `C^{0,α}`; Schauder with `A = 1`
(`isUniformlyEllipticOn_one`) bounds `φ` in `C^{2,α}`. Differentiating
`log det(g + φ_{jk̄}) = G + log det g` in a real direction `∂_ℓ` gives
`L_A (∂_ℓ φ) = ∂_ℓ G + ∂_ℓ log det g - re tr (A ∂_ℓ g)` with `A = (g + φ_{jk̄})⁻¹`, uniformly
elliptic by the `C²` bounds (`isNonneg_sub_smul_of_relTrace_le_of_le_relDet`) and bounded in
`C^{0,α}`. Schauder bounds `∂_ℓ φ` in `C^{2,α}`, i.e. `φ` in `C^{3,α}`, which improves `A` to
`C^{1,α}`; induct on `k`.
-/

@[expose] public section

open scoped Manifold ContDiff NNReal ComplexOrder
open ContinuousAlternatingMap

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [T2Space M] [CompactSpace M]

private theorem contDiffOn_complexHessian_entries_of_contDiffOn
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
    ∀ j k, ContDiffOn ℝ ∞ (fun z ↦ complexHessian f z j k) U := by
  have hddbar : ContDiffOn ℝ ∞ (ddbar f) U := ContDiffOn.ddbar hU hf
  intro j k
  let f₁ : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
    ddbar f z ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]
  let f₂ : EuclideanSpace ℂ (Fin n) → ℝ := fun z ↦
    ddbar f z ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]
  have hf₁ : ContDiffOn ℝ ∞ f₁ U := by
    dsimp [f₁]
    exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
      ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1]).contDiff).comp_contDiffOn
        hddbar
  have hf₂ : ContDiffOn ℝ ∞ f₂ U := by
    dsimp [f₂]
    exact ((ContinuousAlternatingMap.apply ℝ (EuclideanSpace ℂ (Fin n)) ℝ
      ![EuclideanSpace.single j 1, EuclideanSpace.single k 1]).contDiff).comp_contDiffOn hddbar
  have hf₁c : ContDiffOn ℝ ∞ (fun z ↦ (f₁ z : ℂ)) U := by
    convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₁ using 1
    ext z
    simp [Complex.ofRealCLM_apply]
  have hf₂c : ContDiffOn ℝ ∞ (fun z ↦ (f₂ z : ℂ)) U := by
    convert Complex.ofRealCLM.contDiff.comp_contDiffOn hf₂ using 1
    ext z
    simp [Complex.ofRealCLM_apply]
  have hIprod : ContDiffOn ℝ ∞ (fun z ↦ Complex.I * (f₂ z : ℂ)) U :=
    contDiffOn_const.mul hf₂c
  have hformula : ContDiffOn ℝ ∞
      (fun z ↦ ((f₁ z : ℂ) - Complex.I * (f₂ z : ℂ)) / 2) U :=
    (hf₁c.sub hIprod).div_const (2 : ℂ)
  apply hformula.congr
  intro z hz
  change (ddbar f z).coeffMatrix j k = _
  simp [ContinuousAlternatingMap.coeffMatrix, f₁, f₂]

private theorem contDiffOn_matrixDet_of_contDiffOn_entries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {G : E → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U) :
    ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U := by
  simp only [Matrix.det_apply]
  fun_prop

private theorem contDiffOn_matrixInverse_entries_of_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {G : E → Matrix (Fin n) (Fin n) ℂ}
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ G z i j) U)
    (hdet : ∀ z ∈ U, (G z).det ≠ 0) :
    ∀ i j, ContDiffOn ℝ ∞ (fun z ↦ (G z)⁻¹ i j) U := by
  have hdetfun : ContDiffOn ℝ ∞ (fun z ↦ (G z).det) U :=
    contDiffOn_matrixDet_of_contDiffOn_entries hG
  have hinvdet : ContDiffOn ℝ ∞ (fun z ↦ ((G z).det)⁻¹) U :=
    hdetfun.inv hdet
  have hadj (i j : Fin n) :
      ContDiffOn ℝ ∞ (fun z ↦ (G z).adjugate i j) U := by
    have hUpdate (a b : Fin n) : ContDiffOn ℝ ∞
        (fun z ↦ (G z).updateRow j (Pi.single i 1) a b) U := by
      by_cases ha : a = j
      · subst a
        by_cases hb : b = i
        · subst b
          simp [Matrix.updateRow_apply]
          exact contDiffOn_const
        · simp [Matrix.updateRow_apply, hb]
          exact contDiffOn_const
      · simp [Matrix.updateRow_apply, ha]
        exact hG a b
    have hdetUpdate := contDiffOn_matrixDet_of_contDiffOn_entries hUpdate
    apply hdetUpdate.congr
    intro z hz
    exact Matrix.adjugate_apply (G z) i j
  intro i j
  have hEq : (fun z ↦ (G z)⁻¹ i j) =
      fun z ↦ ((G z).det)⁻¹ * (G z).adjugate i j := by
    funext z
    rw [Matrix.inv_def]
    simp [Matrix.smul_apply, Ring.inverse_eq_inv]
  rw [hEq]
  exact (hinvdet.mul (hadj i j))

omit [T2Space M] [CompactSpace M] in

private theorem segment_dist_left_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y z : E} (hz : z ∈ segment ℝ x y) : dist x z ≤ dist x y := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  have hvec : x - ((1 - t) • x + t • y) = t • (x - y) := by module
  rw [dist_eq_norm, hvec, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) ht.2

private theorem exists_pos_segment_radius
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ δ → segment ℝ x y ⊆ U := by
  have hdisj : Disjoint K Uᶜ := by
    rw [Set.disjoint_left]
    intro z hzK hzC
    exact hzC (hKU hzK)
  obtain ⟨δ, hδ, hfar⟩ := Metric.exists_pos_forall_lt_edist hK hU.isClosed_compl hdisj
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy z hz
  by_contra hzU
  have hzC : z ∈ Uᶜ := hzU
  have hfar' := hfar x hx z hzC
  have hnear : edist x z ≤ (δ : ENNReal) := by
    rw [edist_dist, ENNReal.ofReal_le_coe]
    exact (segment_dist_left_le hz).trans hxy
  exact (not_lt_of_ge hnear) hfar'

omit [T2Space M] [CompactSpace M] in
/-- **Higher-order estimates.** Uniform `C⁰`, `C²` and `C³` bounds on a family of solutions, with
right-hand sides bounded in every `C^k`, give uniform `C^k` bounds for every `k`. -/
theorem holderBoundedInCharts_of_solvesMongeAmpere (hSch : InteriorSchauderEstimate n)
    (ω₀ : KahlerForm n M) (S : Set ((M → ℝ) × (M → ℝ)))
    (hS : ∀ p ∈ S, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
      ω₀.SolvesMongeAmpere p.1 p.2)
    (hG : ∀ k, HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) k 0 (Prod.fst '' S))
    {K Λ : ℝ} (hφ : ∀ p ∈ S, ∀ x, |p.2 x| ≤ K)
    (hΛ : ∀ p ∈ S, ∀ x, relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ Λ)
    (hC3 : ∀ (x₀ : M) (K' : Set (EuclideanSpace ℂ (Fin n))), IsCompact K' →
      K' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).target →
      ∃ C : ℝ, ∀ p ∈ S, ∀ z ∈ K',
        ‖fderiv ℝ (ddbar (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₀).symm)) z‖ ≤ C)
    (k : ℕ) : HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) k 0 (Prod.snd '' S) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hE : Subsingleton (EuclideanSpace ℂ (Fin 0)) := by infer_instance
    by_cases hM : IsEmpty M
    · intro x
      exact isEmptyElim (hM.false x)
    · by_cases hSempty : S = ∅
      · intro x K' hK hKt
        refine ⟨0, ?_⟩
        intro f hf
        simp [hSempty] at hf
      · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
        have hMne : Nonempty M := not_isEmpty_iff.mp hM
        obtain ⟨p, hp⟩ := hSne
        obtain ⟨x₀⟩ := hMne
        have hKnonneg : 0 ≤ K := (abs_nonneg (p.2 x₀)).trans (hφ p hp x₀)
        let C : ℝ≥0 := ⟨2 * K, by positivity⟩
        have hC : (C : ℝ) = 2 * K := by rfl
        intro x K' hK hKt
        let χ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin 0)) x
        refine ⟨C, ?_⟩
        intro f hf
        rcases (Set.mem_image Prod.snd S f).mp hf with ⟨p, hp, rfl⟩
        have hval (z : EuclideanSpace ℂ (Fin 0)) : |p.2 (χ.symm z)| ≤ K := hφ p hp (χ.symm z)
        refine ⟨?_, ?_⟩
        · intro j hj z hz
          by_cases hj0 : j = 0
          · subst j
            calc
              ‖iteratedFDeriv ℝ 0 (p.2 ∘ χ.symm) z‖ = |p.2 (χ.symm z)| := by simp
              _ ≤ K := hval z
              _ ≤ (C : ℝ) := by rw [hC]; nlinarith [hKnonneg]
          · have hconst : p.2 ∘ χ.symm = fun _ : EuclideanSpace ℂ (Fin 0) =>
                p.2 (χ.symm 0) := by
              funext y
              exact congrArg p.2 (congrArg χ.symm (hE.elim y 0))
            have hderiv : iteratedFDeriv ℝ j (p.2 ∘ χ.symm) = 0 := by
              rw [hconst]
              exact iteratedFDeriv_const_of_ne hj0 _
            change ‖iteratedFDeriv ℝ j (p.2 ∘ χ.symm) z‖ ≤ (C : ℝ)
            rw [hderiv]
            simp
        · change ∀ z ∈ K', ∀ w ∈ K',
            edist (iteratedFDeriv ℝ k (p.2 ∘ χ.symm) z)
              (iteratedFDeriv ℝ k (p.2 ∘ χ.symm) w) ≤
              (C : ENNReal) * edist z w ^ (0 : ℝ)
          intro z hz w hw
          by_cases hk0 : k = 0
          · subst k
            let a := p.2 (χ.symm z)
            let b := p.2 (χ.symm w)
            have ha : |a| ≤ K := by simpa [a] using hval z
            have hb : |b| ≤ K := by simpa [b] using hval w
            have ha' : -K ≤ a ∧ a ≤ K := abs_le.mp ha
            have hb' : -K ≤ b ∧ b ≤ K := abs_le.mp hb
            have hab : |a - b| ≤ 2 * K := by
              rw [abs_le]
              constructor
              · linarith [ha'.1, hb'.2]
              · linarith [ha'.2, hb'.1]
            calc
              edist (iteratedFDeriv ℝ 0 (p.2 ∘ χ.symm) z)
                  (iteratedFDeriv ℝ 0 (p.2 ∘ χ.symm) w) = edist a b := by
                    let L := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin 0)) ℝ
                    rw [iteratedFDeriv_zero_eq_comp]
                    change edist (L.symm (p.2 (χ.symm z))) (L.symm (p.2 (χ.symm w))) = _
                    rw [L.symm.edist_map]
              _ = ENNReal.ofReal |a - b| := by simp [edist_dist, Real.dist_eq]
              _ ≤ (C : ENNReal) := by
                rw [ENNReal.ofReal_le_coe]
                rw [hC]
                exact hab
              _ = (C : ENNReal) * edist z w ^ (0 : ℝ) := by simp
          · have hconst : p.2 ∘ χ.symm = fun _ : EuclideanSpace ℂ (Fin 0) =>
                p.2 (χ.symm 0) := by
              funext y
              exact congrArg p.2 (congrArg χ.symm (hE.elim y 0))
            have hderiv : iteratedFDeriv ℝ k (p.2 ∘ χ.symm) = 0 := by
              rw [hconst]
              exact iteratedFDeriv_const_of_ne hk0 _
            simp [hderiv]
  · by_cases hk : k = 0
    · subst k
      by_cases hM : IsEmpty M
      · intro x
        exact isEmptyElim (hM.false x)
      · by_cases hSempty : S = ∅
        · intro x K' hK hKt
          refine ⟨0, ?_⟩
          intro f hf
          simp [hSempty] at hf
        · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
          have hMne : Nonempty M := not_isEmpty_iff.mp hM
          obtain ⟨p, hp⟩ := hSne
          obtain ⟨x₀⟩ := hMne
          have hKnonneg : 0 ≤ K := (abs_nonneg (p.2 x₀)).trans (hφ p hp x₀)
          let C : ℝ≥0 := ⟨2 * K, by positivity⟩
          have hC : (C : ℝ) = 2 * K := by rfl
          intro x K' hK hKt
          let χ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
          refine ⟨C, ?_⟩
          intro f hf
          rcases (Set.mem_image Prod.snd S f).mp hf with ⟨p, hp, rfl⟩
          have hval (z : EuclideanSpace ℂ (Fin n)) : |p.2 (χ.symm z)| ≤ K := hφ p hp (χ.symm z)
          refine ⟨?_, ?_⟩
          · intro j hj z hz
            have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
            subst j
            calc
              ‖iteratedFDeriv ℝ 0 (p.2 ∘ χ.symm) z‖ = |p.2 (χ.symm z)| := by simp
              _ ≤ K := hval z
              _ ≤ (C : ℝ) := by rw [hC]; nlinarith [hKnonneg]
          · change ∀ z ∈ K', ∀ w ∈ K',
              edist (iteratedFDeriv ℝ 0 (p.2 ∘ χ.symm) z)
                (iteratedFDeriv ℝ 0 (p.2 ∘ χ.symm) w) ≤
                (C : ENNReal) * edist z w ^ (0 : ℝ)
            intro z hz w hw
            let a := p.2 (χ.symm z)
            let b := p.2 (χ.symm w)
            have ha : |a| ≤ K := by simpa [a] using hval z
            have hb : |b| ≤ K := by simpa [b] using hval w
            have ha' : -K ≤ a ∧ a ≤ K := abs_le.mp ha
            have hb' : -K ≤ b ∧ b ≤ K := abs_le.mp hb
            have hab : |a - b| ≤ 2 * K := by
              rw [abs_le]
              constructor
              · linarith [ha'.1, hb'.2]
              · linarith [ha'.2, hb'.1]
            calc
              edist (iteratedFDeriv ℝ 0 (p.2 ∘ χ.symm) z)
                  (iteratedFDeriv ℝ 0 (p.2 ∘ χ.symm) w) = edist a b := by
                    let L := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
                    rw [iteratedFDeriv_zero_eq_comp]
                    change edist (L.symm (p.2 (χ.symm z))) (L.symm (p.2 (χ.symm w))) = _
                    rw [L.symm.edist_map]
              _ = ENNReal.ofReal |a - b| := by simp [edist_dist, Real.dist_eq]
              _ ≤ (C : ENNReal) := by
                rw [ENNReal.ofReal_le_coe]
                rw [hC]
                exact hab
              _ = (C : ENNReal) * edist z w ^ (0 : ℝ) := by simp
    · by_cases hM : IsEmpty M
      · intro x
        exact isEmptyElim (hM.false x)
      · by_cases hSempty : S = ∅
        · intro x K' hK hKt
          refine ⟨0, ?_⟩
          intro f hf
          simp [hSempty] at hf
        ·
          intro x K' hK hKt
          let e := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
          have hderivBounds :
              ∃ C : ℝ≥0, ∀ p ∈ S, ∀ j ≤ k, ∀ z ∈ K',
                ‖iteratedFDeriv ℝ j (p.2 ∘ e.symm) z‖ ≤ C := by
            let α : ℝ≥0 := (1 / 2 : ℝ≥0)
            have hα₀ : 0 < α := by norm_num [α]
            have hα₁ : α < 1 := by norm_num [α]
            have hBase := exists_uniform_chart_holder_bound_two hSch ω₀ S hS hG hφ hΛ hC3
              α hα₀ hα₁ x K' hK hKt
            have hAll : ∀ m : ℕ, ∀ K'' : Set (EuclideanSpace ℂ (Fin n)),
                IsCompact K'' → K'' ⊆ e.target →
                  ∃ C : ℝ≥0, ∀ p ∈ S,
                    HolderBoundOn (m + 2) α C K'' (p.2 ∘ e.symm) := by
              intro m
              induction m with
              | zero =>
                  intro K'' hK'' hK''t
                  exact exists_uniform_chart_holder_bound_two hSch ω₀ S hS hG hφ hΛ hC3
                    α hα₀ hα₁ x K'' hK'' hK''t
              | succ m ih =>
                  intro K'' hK'' hK''t
                  exact exists_uniform_chart_holder_bound_succ hSch ω₀ S hS hG hφ hΛ x α
                    hα₀ hα₁ (m + 2) (by omega) ih K'' hK'' hK''t
            by_cases hk2 : k ≤ 2
            · rcases hBase with ⟨C, hC⟩
              refine ⟨C, ?_⟩
              intro p hp j hj z hz
              exact (hC p hp).1 j (by omega) z hz
            · rcases hAll (k - 2) K' hK hKt with ⟨C, hC⟩
              refine ⟨C, ?_⟩
              intro p hp j hj z hz
              exact (hC p hp).1 j (by omega) z hz
          have hHolderBoundOn (f : EuclideanSpace ℂ (Fin n) → ℝ) (C : ℝ≥0)
              (hf : ∀ j ≤ k, ∀ z ∈ K', ‖iteratedFDeriv ℝ j f z‖ ≤ C) :
              HolderBoundOn k 0 (2 * C) K' f := by
            refine ⟨?_, ?_⟩
            · intro j hj z hz
              change ‖iteratedFDeriv ℝ j f z‖ ≤ (2 * C : ℝ)
              calc
                ‖iteratedFDeriv ℝ j f z‖ ≤ (C : ℝ) := hf j hj z hz
                _ ≤ 2 * (C : ℝ) := by nlinarith [NNReal.coe_nonneg C]
            · intro z hz w hw
              change edist (iteratedFDeriv ℝ k f z) (iteratedFDeriv ℝ k f w) ≤ _
              calc
                edist (iteratedFDeriv ℝ k f z) (iteratedFDeriv ℝ k f w) =
                    ENNReal.ofReal (dist (iteratedFDeriv ℝ k f z)
                      (iteratedFDeriv ℝ k f w)) := by rw [edist_dist]
                _ ≤ ENNReal.ofReal (‖iteratedFDeriv ℝ k f z‖ +
                    ‖iteratedFDeriv ℝ k f w‖) :=
                      ENNReal.ofReal_le_ofReal (dist_le_norm_add_norm _ _)
                _ ≤ ((2 * C : ℝ≥0) : ENNReal) := by
                  rw [ENNReal.ofReal_le_coe]
                  have hz' := hf k le_rfl z hz
                  have hw' := hf k le_rfl w hw
                  have hC2 : (↑(2 * C : ℝ≥0) : ℝ) = 2 * (C : ℝ) := by
                    simp [NNReal.coe_mul]
                  nlinarith
                _ = (2 * C : ENNReal) * edist z w ^ (0 : ℝ) := by simp
          obtain ⟨C, hC⟩ := hderivBounds
          refine ⟨2 * C, ?_⟩
          intro f hf
          rcases (Set.mem_image Prod.snd S f).mp hf with ⟨p, hp, rfl⟩
          exact hHolderBoundOn (p.2 ∘ e.symm) C (fun j hj z hz ↦ hC p hp j hj z hz)

end KahlerForm
