module

public import CalabiYau.MongeAmpere.Continuity.Basic
public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.Analysis.Elliptic.Schauder
import CalabiYau.MongeAmpere.Estimates.C0
import CalabiYau.MongeAmpere.Estimates.C2
import CalabiYau.MongeAmpere.Estimates.C3
import CalabiYau.MongeAmpere.Estimates.Higher

/-!
# Closedness of the continuity set

The set of `t ∈ [0, 1]` for which `(ω₀ + i∂∂̄φₜ)ⁿ = e^{tF + cₜ} ω₀ⁿ` has a smooth solution is
closed.

## Proof sketch (Yau 1978; Székelyhidi, Lemma 3.5 and §3.4)

Let `tₖ → t` with solutions `φₖ`, normalized by `φₖ(x₀) = 0` (`SolvesMongeAmpere.add_const`). The
right-hand sides `Gₖ = tₖ F + c_{tₖ}` are bounded in every `C^k` (`continuous_pathConstant`,
`HolderBoundedInCharts.singleton`). Then:

1. `C⁰` (`exists_osc_le_of_solvesMongeAmpere`, using `hκ, hS, hP`) bounds `osc φₖ`, hence `|φₖ|`;
2. `C²` (`exists_relTrace_le_of_solvesMongeAmpere`) bounds `tr_ω₀ ω_{φₖ}` (note
   `Δ_ω₀ Gₖ = tₖ Δ_ω₀ F` is bounded);
3. `C³` (`exists_fderiv_ddbar_le_of_solvesMongeAmpere`) bounds `i∂∂̄φₖ` in `C¹`;
4. `Estimates/Higher` (using `hSch`) bounds `φₖ` in every `C^k`.

By Arzelà–Ascoli in `C^∞` (`exists_subseq_tendsto_of_holderBoundedInCharts`) a subsequence
converges with all derivatives to a smooth `φ`; passing to the limit in `mongeAmpere_eq_inChart`
gives `MA(φ) = e^{tF + c_t} > 0`, and positivity of `ω₀ + i∂∂̄φ` follows from
`ω₀ + i∂∂̄φₖ ≥ c ω₀` with `c` uniform (step 2 and the equation).
-/

@[expose] public section

open scoped Manifold ContDiff Topology ComplexOrder MatrixOrder
open Set Filter

namespace KahlerForm

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

/-- **Closedness.** The continuity set is closed. -/
theorem isClosed_continuitySet (hSch : InteriorSchauderEstimate n) (ω₀ : KahlerForm n M)
    {κ C_S C_P : ℝ} (hκ : 1 < κ) (hS : ω₀.SobolevInequality κ C_S)
    (hP : ω₀.PoincareInequality C_P) {F : M → ℝ}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ F) :
    IsClosed (ω₀.continuitySet F) := by
  classical
  by_cases hM : IsEmpty M
  · have hset : ω₀.continuitySet F = Icc (0 : ℝ) 1 := by
      ext t
      constructor
      · exact fun h ↦ h.1
      · intro ht
        refine ⟨ht, 0, ?_⟩
        refine ⟨ω₀.isPotential_zero, ?_⟩
        intro x
        exact isEmptyElim (hM.false x)
    rw [hset]
    exact isClosed_Icc
  · apply SequentialSpace.isClosed_of_seq
    intro seq t hseq hlim
    have htIcc : t ∈ Icc (0 : ℝ) 1 :=
      isClosed_Icc.isSeqClosed (fun i ↦ (hseq i).1) hlim
    refine ⟨htIcc, ?_⟩
    by_cases htmem : ∃ i, seq i = t
    · obtain ⟨i, hi⟩ := htmem
      rcases hseq i with ⟨_, φ, hφ⟩
      exact ⟨φ, by simpa [hi] using hφ⟩
    · let : Nonempty M := not_isEmpty_iff.mp hM
      let φraw : ℕ → M → ℝ := fun i ↦ Classical.choose (hseq i).2
      have hraw (i : ℕ) :
          ω₀.SolvesMongeAmpere (fun x ↦ seq i * F x + ω₀.pathConstant F (seq i)) (φraw i) :=
        Classical.choose_spec (hseq i).2
      let G : ℕ → M → ℝ := fun i x ↦ seq i * F x + ω₀.pathConstant F (seq i)
      have hG_smooth (i : ℕ) :
          ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (G i) := by
        apply ((contMDiff_const.mul hF).add
          (contMDiff_const (c := ω₀.pathConstant F (seq i)))).congr
        intro x
        rfl
      have hF_cont : Continuous F := hF.continuous
      obtain ⟨K_F, hK_F⟩ : ∃ K_F : ℝ, ∀ x, ‖F x‖ ≤ K_F := by
        obtain ⟨K_F, hK_F⟩ :=
          (isCompact_univ : IsCompact (Set.univ : Set M)).exists_bound_of_continuousOn
            (f := F) (s := Set.univ) hF_cont.continuousOn
        exact ⟨K_F, fun x ↦ hK_F x (Set.mem_univ x)⟩
      have hK_F_nonneg : 0 ≤ K_F := by
        obtain ⟨x⟩ := ‹Nonempty M›
        exact le_trans (norm_nonneg (F x)) (hK_F x)
      have hc_cont : Continuous (ω₀.pathConstant F) := ω₀.continuous_pathConstant hF
      obtain ⟨K_c, hK_c⟩ :
          ∃ K_c : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ‖ω₀.pathConstant F t‖ ≤ K_c :=
        isCompact_Icc.exists_bound_of_continuousOn (f := ω₀.pathConstant F)
          (s := Icc (0 : ℝ) 1) hc_cont.continuousOn
      have hK_c_nonneg : 0 ≤ K_c := by
        have h0 := hK_c 0 (by simp)
        exact le_trans (norm_nonneg _) h0
      have hseq_abs (i : ℕ) : |seq i| ≤ 1 := by
        have hi := (hseq i).1
        rw [abs_of_nonneg hi.1]
        exact hi.2
      have hG_bound (i : ℕ) (x : M) : |G i x| ≤ K_F + K_c := by
        have hFx : |F x| ≤ K_F := by simpa [Real.norm_eq_abs] using hK_F x
        have hcx : |ω₀.pathConstant F (seq i)| ≤ K_c := by
          simpa [Real.norm_eq_abs] using hK_c (seq i) (hseq i).1
        calc
          |G i x| ≤ |seq i * F x| + |ω₀.pathConstant F (seq i)| := abs_add_le _ _
          _ ≤ K_F + K_c := by
            gcongr
            · rw [abs_mul]
              calc
                |seq i| * |F x| ≤ 1 * |F x| :=
                  mul_le_mul_of_nonneg_right (hseq_abs i) (abs_nonneg _)
                _ ≤ 1 * K_F := mul_le_mul_of_nonneg_left hFx (by norm_num)
                _ = K_F := by rw [one_mul]
      let x₀ : M := Classical.choice ‹Nonempty M›
      let φnorm : ℕ → M → ℝ := fun i x ↦ φraw i x - φraw i x₀
      have hnorm (i : ℕ) :
          ω₀.SolvesMongeAmpere (G i) (φnorm i) := by
        simpa [φnorm, G, sub_eq_add_neg] using (hraw i).add_const (-φraw i x₀)
      obtain ⟨C₀, hC₀⟩ :=
        exists_osc_le_of_solvesMongeAmpere ω₀ hκ hS hP (K_F + K_c)
      have hosc (i : ℕ) (x y : M) : φnorm i x - φnorm i y ≤ C₀ :=
        hC₀ (G i) (φnorm i) (hG_smooth i) (hG_bound i) (hnorm i) x y
      have hnorm_x₀ (i : ℕ) : φnorm i x₀ = 0 := by simp [φnorm]
      have hφ_abs (i : ℕ) (x : M) : |φnorm i x| ≤ C₀ := by
        rw [abs_le]
        constructor
        · have h := hosc i x₀ x
          rw [hnorm_x₀ i] at h
          linarith
        · have h := hosc i x x₀
          rw [hnorm_x₀ i] at h
          linarith
      have hLap_smooth :
          ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (ω₀.laplacian F) :=
        ω₀.contMDiff_laplacian hF
      obtain ⟨K_L, hK_L⟩ : ∃ K_L : ℝ, ∀ x, ‖ω₀.laplacian F x‖ ≤ K_L := by
        obtain ⟨K_L, hK_L⟩ :=
          (isCompact_univ : IsCompact (Set.univ : Set M)).exists_bound_of_continuousOn
            (f := ω₀.laplacian F) (s := Set.univ) hLap_smooth.continuous.continuousOn
        exact ⟨K_L, fun x ↦ hK_L x (Set.mem_univ x)⟩
      have hK_L_nonneg : 0 ≤ K_L := by
        exact le_trans (norm_nonneg (ω₀.laplacian F x₀)) (hK_L x₀)
      have hLap_abs (x : M) : |ω₀.laplacian F x| ≤ K_L := by
        simpa [Real.norm_eq_abs] using hK_L x
      have hLap_formula (i : ℕ) :
          ω₀.laplacian (G i) = (seq i) • ω₀.laplacian F := by
        funext x
        calc
          ω₀.laplacian (G i) x =
              ω₀.laplacian (fun y ↦ (seq i) • F y + ω₀.pathConstant F (seq i)) x := rfl
          _ = ω₀.laplacian (fun y ↦ (seq i) • F y) x := by
            rw [ω₀.laplacian_add_const]
          _ = ω₀.laplacian ((seq i) • F) x := by
            congr 1
          _ = ((seq i) • ω₀.laplacian F) x := by
            exact congrArg (fun g ↦ g x) (ω₀.laplacian_smul hF (seq i))
      have hG_lap_abs (i : ℕ) (x : M) : |ω₀.laplacian (G i) x| ≤ K_L := by
        rw [hLap_formula]
        change |seq i * ω₀.laplacian F x| ≤ K_L
        rw [abs_mul]
        calc
          |seq i| * |ω₀.laplacian F x| ≤ 1 * |ω₀.laplacian F x| :=
            mul_le_mul_of_nonneg_right (hseq_abs i) (abs_nonneg _)
          _ ≤ 1 * K_L := mul_le_mul_of_nonneg_left (hLap_abs x) (by norm_num)
          _ = K_L := by rw [one_mul]
      have hC₀_nonneg : 0 ≤ C₀ := by
        have h := hosc 0 x₀ x₀
        simpa using h
      let K₂ : ℝ := max (K_F + K_c) (max K_L C₀)
      have hG_bound₂ (i : ℕ) (x : M) : |G i x| ≤ K₂ :=
        (hG_bound i x).trans (le_max_left _ _)
      have hG_lap_lower (i : ℕ) (x : M) : -K₂ ≤ ω₀.laplacian (G i) x := by
        have hle : K_L ≤ K₂ := le_trans (le_max_left _ _) (le_max_right _ _)
        exact (abs_le.mp ((hG_lap_abs i x).trans hle)).1
      have hosc₂ (i : ℕ) : ∀ x y, φnorm i x - φnorm i y ≤ K₂ := by
        intro x y
        exact (hosc i x y).trans (le_trans (le_max_right _ _) (le_max_right _ _))
      obtain ⟨C₂, hC₂⟩ := exists_relTrace_le_of_solvesMongeAmpere ω₀ K₂
      have hTrace (i : ℕ) (x : M) :
          ContinuousAlternatingMap.relTrace (ω₀ x) (ω₀ x + mddbar n (φnorm i) x) ≤ C₂ := by
        exact (hC₂ (G i) (φnorm i) (hG_smooth i) (hG_bound₂ i)
          (hG_lap_lower i) (hosc₂ i) (hnorm i) x).1
      have hG_holder :
          ∀ k, HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) k 0 (Set.range G) := by
        intro k x K hK hKt
        let χ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
        obtain ⟨C_F, hC_F⟩ :=
          (HolderBoundedInCharts.singleton (k := k) (α := 0) hF (by norm_num)) x K hK hKt
        have hF_chart : HolderBoundOn k 0 C_F K (F ∘ χ.symm) := by
          exact hC_F F (by simp)
        let C : NNReal := ⟨2 * ((C_F : ℝ) + K_F + K_c), by positivity⟩
        have hC_real : (C : ℝ) = 2 * ((C_F : ℝ) + K_F + K_c) := rfl
        have hC_F_nonneg : 0 ≤ (C_F : ℝ) := by positivity
        have hF_on : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
            ∞ F Set.univ := hF.contMDiffOn
        have hsymm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ χ.symm χ.target :=
          contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x
        have hF_md : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
            ∞ (F ∘ χ.symm) χ.target :=
          hF_on.comp hsymm (fun _ _ ↦ Set.mem_univ _)
        have hF_chart_smooth : ContDiffOn ℝ ∞ (F ∘ χ.symm) χ.target := hF_md.contDiffOn
        have htarget_open : IsOpen χ.target :=
          isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x
        refine ⟨C, ?_⟩
        intro g hg
        rcases hg with ⟨i, rfl⟩
        let f : EuclideanSpace ℂ (Fin n) → ℝ := F ∘ χ.symm
        let g : EuclideanSpace ℂ (Fin n) → ℝ := G i ∘ χ.symm
        have hg_eq : g = fun z ↦ seq i • f z + ω₀.pathConstant F (seq i) := by
          funext z
          simp [g, f, G, smul_eq_mul]
        have hG_on : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
            ∞ (G i) Set.univ := (hG_smooth i).contMDiffOn
        have hg_md : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
            ∞ g χ.target := by
          simpa [g] using hG_on.comp hsymm (fun _ _ ↦ Set.mem_univ _)
        have hg_chart_smooth : ContDiffOn ℝ ∞ g χ.target := hg_md.contDiffOn
        have hderivPos {j : ℕ} (hj : j ≠ 0) {z : EuclideanSpace ℂ (Fin n)}
            (hz : z ∈ χ.target) :
            iteratedFDeriv ℝ j g z = seq i • iteratedFDeriv ℝ j f z := by
          have hfInf := hF_chart_smooth.contDiffAt (htarget_open.mem_nhds hz)
          have hf : ContDiffAt ℝ j f z :=
            hfInf.of_le (show (↑j : ℕ∞ω) ≤ ∞ from by
              exact_mod_cast (le_top : (j : WithTop ℕ) ≤ ⊤))
          have hgInf := hg_chart_smooth.contDiffAt (htarget_open.mem_nhds hz)
          have hg' : ContDiffAt ℝ j g z :=
            hgInf.of_le (show (↑j : ℕ∞ω) ≤ ∞ from by
              exact_mod_cast (le_top : (j : WithTop ℕ) ≤ ⊤))
          rw [hg_eq]
          change iteratedFDeriv ℝ j ((fun y ↦ seq i • f y) +
            fun _ ↦ ω₀.pathConstant F (seq i)) z = _
          rw [iteratedFDeriv_add_apply (ContDiffAt.const_smul (seq i) hf)
            contDiffAt_const]
          have hmul : (fun y ↦ seq i • f y) = (seq i) • f := by
            ext y
            rfl
          rw [hmul]
          rw [iteratedFDeriv_const_smul_apply hf, iteratedFDeriv_const_of_ne hj]
          simp
        have hval (z : EuclideanSpace ℂ (Fin n)) : |g z| ≤ K_F + K_c := by
          simpa [g] using hG_bound i (χ.symm z)
        refine ⟨?_, ?_⟩
        · intro j hj z hz
          by_cases hj0 : j = 0
          · subst j
            calc
              ‖iteratedFDeriv ℝ 0 g z‖ = |g z| := by simp
              _ ≤ K_F + K_c := hval z
              _ ≤ (C : ℝ) := by rw [hC_real]; nlinarith [hC_F_nonneg, hK_F_nonneg, hK_c_nonneg]
          · rw [hderivPos hj0 (hKt hz), norm_smul, Real.norm_eq_abs]
            calc
              |seq i| * ‖iteratedFDeriv ℝ j f z‖ ≤ 1 * ‖iteratedFDeriv ℝ j f z‖ :=
                mul_le_mul_of_nonneg_right (hseq_abs i) (norm_nonneg _)
              _ ≤ 1 * C_F := mul_le_mul_of_nonneg_left (hF_chart.1 j hj z hz) (by norm_num)
              _ = (C_F : ℝ) := by rw [one_mul]
              _ ≤ (C : ℝ) := by rw [hC_real]; nlinarith [hC_F_nonneg, hK_F_nonneg, hK_c_nonneg]
        · by_cases hk0 : k = 0
          · subst k
            change HolderOnWith C 0 (iteratedFDeriv ℝ 0 g) K
            intro z hz w hw
            have hab : |g z - g w| ≤ 2 * (K_F + K_c) := by
              have hz' : - (K_F + K_c) ≤ g z ∧ g z ≤ K_F + K_c := abs_le.mp (hval z)
              have hw' : - (K_F + K_c) ≤ g w ∧ g w ≤ K_F + K_c := abs_le.mp (hval w)
              rw [abs_le]
              constructor <;> nlinarith
            calc
              edist (iteratedFDeriv ℝ 0 g z) (iteratedFDeriv ℝ 0 g w) =
                  edist (g z) (g w) := by
                    let L := continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℂ (Fin n)) ℝ
                    rw [iteratedFDeriv_zero_eq_comp]
                    change edist (L.symm (g z)) (L.symm (g w)) = _
                    rw [L.symm.edist_map]
              _ = ENNReal.ofReal |g z - g w| := by simp [edist_dist, Real.dist_eq]
              _ ≤ (C : ENNReal) := by
                rw [ENNReal.ofReal_le_coe]
                rw [hC_real]
                nlinarith [hab, hC_F_nonneg, hK_F_nonneg, hK_c_nonneg]
              _ = (C : ENNReal) * edist z w ^ (0 : ℝ) := by simp
          · have hF_holder_dom : HolderWith (C_F * ‖seq i‖₊) 0
                (seq i • K.domRestrict (iteratedFDeriv ℝ k f)) :=
              HolderWith.smul (seq i) hF_chart.2.holderWith
            have htnorm : ‖seq i‖₊ ≤ 1 := by
              exact_mod_cast hseq_abs i
            have hcoef : C_F * ‖seq i‖₊ ≤ C := by
              calc
                C_F * ‖seq i‖₊ ≤ C_F * 1 := by gcongr
                _ = C_F := by simp
                _ ≤ C := by
                  have hreal : (C_F : ℝ) ≤ (C : ℝ) := by
                    rw [hC_real]
                    nlinarith [hC_F_nonneg, hK_F_nonneg, hK_c_nonneg]
                  exact_mod_cast hreal
            have hF_holder_dom' : HolderWith C 0
                (seq i • K.domRestrict (iteratedFDeriv ℝ k f)) :=
              hF_holder_dom.mono hcoef
            change HolderOnWith C 0 (iteratedFDeriv ℝ k g) K
            intro z hz w hw
            rw [hderivPos (by omega) (hKt hz), hderivPos (by omega) (hKt hw)]
            simpa [Set.domRestrict] using hF_holder_dom' ⟨z, hz⟩ ⟨w, hw⟩
      let S : Set ((M → ℝ) × (M → ℝ)) := Set.range fun i ↦ (G i, φnorm i)
      have hS_solutions : ∀ p ∈ S,
          ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ p.1 ∧
            ω₀.SolvesMongeAmpere p.1 p.2 := by
        rintro ⟨g, φ⟩ ⟨i, heq⟩
        cases heq
        exact ⟨hG_smooth i, hnorm i⟩
      have hfirst : Prod.fst '' S = Set.range G := by
        ext g
        constructor
        · rintro ⟨p, ⟨i, heq⟩, rfl⟩
          cases heq
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨(G i, φnorm i), ⟨i, rfl⟩, rfl⟩
      have hG_bounded (k : ℕ) :
          HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) k 0 (Prod.fst '' S) := by
        rw [hfirst]
        exact hG_holder k
      have hΛ : ∀ p ∈ S, ∀ x,
          ContinuousAlternatingMap.relTrace (ω₀ x) (ω₀ x + mddbar n p.2 x) ≤ C₂ := by
        rintro ⟨g, φ⟩ ⟨i, heq⟩ x
        cases heq
        exact hTrace i x
      have hC3 : ∀ (x₁ : M) (K' : Set (EuclideanSpace ℂ (Fin n))), IsCompact K' →
          K' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).target →
          ∃ C : ℝ, ∀ p ∈ S, ∀ z ∈ K',
            ‖fderiv ℝ (ddbar (p.2 ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).symm)) z‖ ≤ C := by
        intro x₁ K' hK' hKt'
        exact exists_fderiv_ddbar_le_of_solvesMongeAmpere ω₀ S hS_solutions
          (hG_bounded 3) hΛ x₁ K' hK' hKt'
      have hHigher (k : ℕ) :
          HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) k 0 (Prod.snd '' S) := by
        exact holderBoundedInCharts_of_solvesMongeAmpere hSch ω₀ S hS_solutions
          hG_bounded (K := C₀) (Λ := C₂)
          (by
            intro p hp x
            rcases hp with ⟨i, heq⟩
            cases heq
            exact hφ_abs i x) hΛ hC3 k
      have hφ_smooth (i : ℕ) :
          ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ (φnorm i) :=
        (hnorm i).1.1
      have hφ_bounds (k : ℕ) :
          HolderBoundedInCharts (EuclideanSpace ℂ (Fin n)) k 0 (Set.range φnorm) := by
        have hsnd : Prod.snd '' S = Set.range φnorm := by
          ext φ
          constructor
          · rintro ⟨p, ⟨i, heq⟩, rfl⟩
            cases heq
            exact ⟨i, rfl⟩
          · rintro ⟨i, rfl⟩
            exact ⟨(G i, φnorm i), ⟨i, rfl⟩, rfl⟩
        rw [← hsnd]
        exact hHigher k
      obtain ⟨φlim, σ, hσ, hφlim_smooth, hconv⟩ :=
        exists_subseq_tendsto_of_holderBoundedInCharts (f := φnorm) hφ_smooth hφ_bounds
      let Gt : M → ℝ := fun x ↦ t * F x + ω₀.pathConstant F t
      have htime : Tendsto (fun m ↦ seq (σ m)) atTop (𝓝 t) :=
        hlim.comp hσ.tendsto_atTop
      have hG_tendsto (x : M) : Tendsto (fun m ↦ G (σ m) x) atTop (𝓝 (Gt x)) := by
        have hcont : Continuous (fun s : ℝ ↦ s * F x + ω₀.pathConstant F s) :=
          (continuous_id.mul continuous_const).add hc_cont
        exact hcont.continuousAt.tendsto.comp htime
      have hsecond_tendsto (x₁ : M) (z : EuclideanSpace ℂ (Fin n))
          (hz : z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).target) :
          Tendsto
            (fun m ↦ iteratedFDeriv ℝ 2
              (φnorm (σ m) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).symm) z)
            atTop
            (𝓝 (iteratedFDeriv ℝ 2
              (φlim ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).symm) z)) :=
        (hconv 2 x₁).tendsto_at hz
      have hcomplexHessian_tendsto (x₁ : M) :
          Tendsto
            (fun m ↦ complexHessian
              (φnorm (σ m) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).symm)
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ x₁))
            atTop
            (𝓝 (complexHessian (φlim ∘
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁).symm)
              (extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁ x₁))) := by
        let χ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x₁
        let z₀ := χ x₁
        have hz₀ : z₀ ∈ χ.target := by
          exact χ.map_source (by simp [χ])
        change Tendsto
          (fun m ↦ complexHessian (φnorm (σ m) ∘ χ.symm) z₀)
          atTop (𝓝 (complexHessian (φlim ∘ χ.symm) z₀))
        have hD : Tendsto
            (fun m ↦ iteratedFDeriv ℝ 2 (φnorm (σ m) ∘ χ.symm) z₀) atTop
            (𝓝 (iteratedFDeriv ℝ 2 (φlim ∘ χ.symm) z₀)) := by
          simpa [χ, z₀] using hsecond_tendsto x₁ z₀ hz₀
        let H : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ EuclideanSpace ℂ (Fin n)) ℝ →
            Matrix (Fin n) (Fin n) ℂ := fun D ↦ fun j k ↦
              ((D ![EuclideanSpace.single j 1, EuclideanSpace.single k 1] : ℝ) +
                D ![Complex.I • EuclideanSpace.single j 1,
                  Complex.I • EuclideanSpace.single k 1] +
                Complex.I * (D ![EuclideanSpace.single j 1,
                    Complex.I • EuclideanSpace.single k 1] -
                  D ![Complex.I • EuclideanSpace.single j 1,
                    EuclideanSpace.single k 1])) / 4
        have hHcont : Continuous H := by
          apply continuous_pi
          intro j
          apply continuous_pi
          intro k
          dsimp [H]
          fun_prop
        have hH : Tendsto (fun m ↦ H (iteratedFDeriv ℝ 2
            (φnorm (σ m) ∘ χ.symm) z₀)) atTop
            (𝓝 (H (iteratedFDeriv ℝ 2 (φlim ∘ χ.symm) z₀))) :=
          hHcont.continuousAt.tendsto.comp hD
        have hf (m : ℕ) : ContDiffAt ℝ 2 (φnorm (σ m) ∘ χ.symm) z₀ := by
          have hm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞
              (φnorm (σ m)) Set.univ := (hφ_smooth (σ m)).contMDiffOn
          have hχ : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
              𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ χ.symm χ.target :=
            contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₁
          have hh : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
              ∞ (φnorm (σ m) ∘ χ.symm) χ.target := by
            exact hm.comp hχ (fun _ _ ↦ Set.mem_univ _)
          have hcd : ContDiffOn ℝ ∞ (φnorm (σ m) ∘ χ.symm) χ.target := hh.contDiffOn
          have hopen : IsOpen χ.target :=
            isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₁
          exact (hcd.contDiffAt (hopen.mem_nhds hz₀)).of_le (by
            exact WithTop.coe_le_coe.mpr (le_top : (2 : WithTop ℕ) ≤ ⊤))
        have hflim : ContDiffAt ℝ 2 (φlim ∘ χ.symm) z₀ := by
          have hm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ φlim Set.univ :=
            hφlim_smooth.contMDiffOn
          have hχ : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
              𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ χ.symm χ.target :=
            contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₁
          have hh : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ)
              ∞ (φlim ∘ χ.symm) χ.target := by
            exact hm.comp hχ (fun _ _ ↦ Set.mem_univ _)
          have hcd : ContDiffOn ℝ ∞ (φlim ∘ χ.symm) χ.target := hh.contDiffOn
          have hopen : IsOpen χ.target :=
            isOpen_extChartAt_target (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) x₁
          exact (hcd.contDiffAt (hopen.mem_nhds hz₀)).of_le (by
            exact WithTop.coe_le_coe.mpr (le_top : (2 : WithTop ℕ) ≤ ⊤))
        have hformula (u : EuclideanSpace ℂ (Fin n) → ℝ)
            (hu : ContDiffAt ℝ 2 u z₀) :
            complexHessian u z₀ = H (iteratedFDeriv ℝ 2 u z₀) := by
          ext j k
          simp only [H]
          rw [complexHessian_apply hu j k]
          rw [iteratedFDeriv_two_apply (𝕜 := ℝ) u z₀
                ![EuclideanSpace.single j 1, EuclideanSpace.single k 1],
              iteratedFDeriv_two_apply (𝕜 := ℝ) u z₀
                ![Complex.I • EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1],
              iteratedFDeriv_two_apply (𝕜 := ℝ) u z₀
                ![EuclideanSpace.single j 1, Complex.I • EuclideanSpace.single k 1],
              iteratedFDeriv_two_apply (𝕜 := ℝ) u z₀
                ![Complex.I • EuclideanSpace.single j 1, EuclideanSpace.single k 1]]
          rfl
        have hformula_seq :
            (fun m ↦ complexHessian (φnorm (σ m) ∘ χ.symm) z₀) =
              (fun m ↦ H (iteratedFDeriv ℝ 2 (φnorm (σ m) ∘ χ.symm) z₀)) := by
          funext m
          exact hformula _ (hf m)
        have hformula_lim : complexHessian (φlim ∘ χ.symm) z₀ =
            H (iteratedFDeriv ℝ 2 (φlim ∘ χ.symm) z₀) := hformula _ hflim
        rw [hformula_seq, hformula_lim]
        exact hH
      have hMA_eq (x : M) : ω₀.mongeAmpere φlim x = Real.exp (Gt x) := by
        let χ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
        let z₀ := χ x
        have hχ : x ∈ (chartAt (EuclideanSpace ℂ (Fin n)) x).source := by simp
        have hχtarget : z₀ ∈ χ.target := by
          exact χ.map_source (by simp [χ])
        have hHess := hcomplexHessian_tendsto x
        let g₀ : Matrix (Fin n) (Fin n) ℂ := ω₀.metricInChart x z₀
        have hmat : Tendsto
            (fun m ↦ g₀ + complexHessian
              (φnorm (σ m) ∘ χ.symm) z₀) atTop
            (𝓝 (g₀ + complexHessian (φlim ∘ χ.symm) z₀)) :=
          tendsto_const_nhds.add hHess
        have hdet_fun : Continuous (fun A : Matrix (Fin n) (Fin n) ℂ ↦ A.det) :=
          continuous_id.matrix_det
        have hdet : Tendsto
            (fun m ↦ (g₀ + complexHessian (φnorm (σ m) ∘ χ.symm) z₀).det) atTop
            (𝓝 (g₀ + complexHessian (φlim ∘ χ.symm) z₀).det) :=
          (hdet_fun.continuousAt.tendsto).comp hmat
        have hdet_re : Tendsto
            (fun m ↦ RCLike.re (g₀ + complexHessian
              (φnorm (σ m) ∘ χ.symm) z₀).det) atTop
            (𝓝 (RCLike.re (g₀ + complexHessian (φlim ∘ χ.symm) z₀).det)) :=
          (RCLike.continuous_re.continuousAt.tendsto).comp hdet
        let d : ℝ := RCLike.re (ω₀.metricInChart x z₀).det
        have hratio : Tendsto
            (fun m ↦ RCLike.re (g₀ + complexHessian
              (φnorm (σ m) ∘ χ.symm) z₀).det / d) atTop
            (𝓝 (RCLike.re (g₀ + complexHessian (φlim ∘ χ.symm) z₀).det / d)) :=
          ((continuous_id.div_const d).continuousAt.tendsto).comp hdet_re
        have hformula_m (m : ℕ) :
            ω₀.mongeAmpere (φnorm (σ m)) x =
              RCLike.re (g₀ + complexHessian
                (φnorm (σ m) ∘ χ.symm) z₀).det / d := by
          simpa [χ, z₀, g₀, d] using
            ω₀.mongeAmpere_eq_inChart (hφ_smooth (σ m)) x (y := x) (by simp)
        have hformula_lim :
            ω₀.mongeAmpere φlim x =
              RCLike.re (g₀ + complexHessian (φlim ∘ χ.symm) z₀).det / d := by
          simpa [χ, z₀, g₀, d] using
            ω₀.mongeAmpere_eq_inChart hφlim_smooth x (y := x) (by simp)
        have hleft : Tendsto (fun m ↦ ω₀.mongeAmpere (φnorm (σ m)) x) atTop
            (𝓝 (RCLike.re (g₀ + complexHessian (φlim ∘ χ.symm) z₀).det / d)) :=
          Tendsto.congr (fun m ↦ (hformula_m m).symm) hratio
        have hright : Tendsto (fun m ↦ Real.exp (G (σ m) x)) atTop
            (𝓝 (Real.exp (Gt x))) :=
          (Real.continuous_exp.continuousAt.tendsto.comp (hG_tendsto x))
        have hsame : ∀ m, ω₀.mongeAmpere (φnorm (σ m)) x = Real.exp (G (σ m) x) :=
          fun m ↦ (hnorm (σ m)).2 x
        have hlim_eq := tendsto_nhds_unique hleft (hright.congr fun m ↦ (hsame m).symm)
        calc
          ω₀.mongeAmpere φlim x =
              RCLike.re (g₀ + complexHessian (φlim ∘ χ.symm) z₀).det / d := hformula_lim
          _ = Real.exp (Gt x) := hlim_eq
      have hMA : ∀ x, ω₀.mongeAmpere φlim x = Real.exp (Gt x) := hMA_eq
      refine ⟨φlim, ?_⟩
      refine ⟨⟨hφlim_smooth, ?_⟩, hMA⟩
      have hφlim_oneOne (x : M) :
          (ω₀ x + mddbar n φlim x).IsOneOne := by
        exact (ω₀.isOneOne x).add (isOneOne_mddbar hφlim_smooth x)
      have hpositive_limit (x : M) : (ω₀ x + mddbar n φlim x).IsPositive := by
        let χ := extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x
        let z₀ := χ x
        have hz₀ : z₀ ∈ χ.target := by
          exact χ.map_source (by simp [χ])
        have hcoeff (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
            𝓘(ℝ) ∞ f) (m : ℕ) :
            (ω₀ x + mddbar n f x).coeffMatrix =
              ω₀.metricInChart x z₀ + complexHessian (f ∘ χ.symm) z₀ := by
          change ((ω₀.toFormField + mddbar n f) x).coeffMatrix = _
          have hcenter : z₀ = extChartAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x x := rfl
          rw [← FormField.chartRep_self (ω₀.toFormField + mddbar n f) x]
          rw [hcenter]
          change ((ω₀.toFormField.chartRep x z₀ +
            (mddbar n f).chartRep x z₀).coeffMatrix) = _
          rw [ContinuousAlternatingMap.coeffMatrix_add]
          have hω : (ω₀.toFormField.chartRep x z₀).coeffMatrix =
              ω₀.metricInChart x z₀ := rfl
          rw [hω, chartRep_mddbar hf x hz₀]
          rfl
        have hmat : Tendsto
            (fun m ↦ (ω₀ x + mddbar n (φnorm (σ m)) x).coeffMatrix) atTop
            (𝓝 (ω₀ x + mddbar n φlim x).coeffMatrix) := by
          have hsum : Tendsto
              (fun m ↦ ω₀.metricInChart x z₀ +
                complexHessian (φnorm (σ m) ∘ χ.symm) z₀) atTop
              (𝓝 (ω₀.metricInChart x z₀ + complexHessian (φlim ∘ χ.symm) z₀)) := by
            exact tendsto_const_nhds.add (hcomplexHessian_tendsto x)
          have hm (m : ℕ) := hcoeff (φnorm (σ m)) (hφ_smooth (σ m)) m
          have hlim := hcoeff φlim hφlim_smooth 0
          have hseq : (fun m ↦ (ω₀ x + mddbar n (φnorm (σ m)) x).coeffMatrix) =
              (fun m ↦ ω₀.metricInChart x z₀ +
                complexHessian (φnorm (σ m) ∘ χ.symm) z₀) := by
            funext m
            exact hm m
          have htarget :
              (ω₀ x + mddbar n φlim x).coeffMatrix =
                ω₀.metricInChart x z₀ + complexHessian (φlim ∘ χ.symm) z₀ := hlim
          rw [hseq, htarget]
          exact hsum
        have hαlim_nonneg : (ω₀ x + mddbar n φlim x).IsNonneg := by
          refine ⟨hφlim_oneOne x, ?_⟩
          intro v
          let q : Matrix (Fin n) (Fin n) ℂ → ℝ := fun A ↦
            2 * (∑ j, ∑ k, A j k * v j * star (v k)).re
          have hqcont : Continuous q := by
            dsimp [q]
            fun_prop
          have hq : Tendsto
              (fun m ↦ q ((ω₀ x + mddbar n (φnorm (σ m)) x).coeffMatrix))
              atTop (𝓝 (q ((ω₀ x + mddbar n φlim x).coeffMatrix))) :=
            (hqcont.continuousAt.tendsto).comp hmat
          have hnonneg (m : ℕ) :
              0 ≤ q ((ω₀ x + mddbar n (φnorm (σ m)) x).coeffMatrix) := by
            have hmpos := (hnorm (σ m)).1.2 x
            have hqEq : (ω₀ x + mddbar n (φnorm (σ m)) x) ![v, Complex.I • v] =
                q ((ω₀ x + mddbar n (φnorm (σ m)) x).coeffMatrix) := by
              simpa [q] using hmpos.1.apply_I_smul v
            rw [← hqEq]
            exact hmpos.isNonneg.2 v
          have hmem : q ((ω₀ x + mddbar n φlim x).coeffMatrix) ∈ Ici 0 :=
            isClosed_Ici.mem_of_tendsto hq (Filter.Eventually.of_forall hnonneg)
          have hEval : (ω₀ x + mddbar n φlim x) ![v, Complex.I • v] =
              q ((ω₀ x + mddbar n φlim x).coeffMatrix) := by
            simpa [q] using (hφlim_oneOne x).apply_I_smul v
          have hqnonneg : 0 ≤ q ((ω₀ x + mddbar n φlim x).coeffMatrix) := hmem
          rw [hEval]
          exact hqnonneg
        have hdet_eq : ContinuousAlternatingMap.relDet (ω₀ x)
            (ω₀ x + mddbar n φlim x) = Real.exp (Gt x) := by
          simpa [mongeAmpere] using hMA_eq x
        have hdet_pos : 0 <
            ContinuousAlternatingMap.relDet (ω₀ x) (ω₀ x + mddbar n φlim x) := by
          rw [hdet_eq]
          exact Real.exp_pos _
        have hωdet_pos : 0 < RCLike.re (ω₀ x).coeffMatrix.det := by
          exact (RCLike.pos_iff.mp
            ((ContinuousAlternatingMap.isPositive_iff.mp (ω₀.isPositive x)).2.det_pos)).1
        have hαdet_pos : 0 < RCLike.re (ω₀ x + mddbar n φlim x).coeffMatrix.det := by
          change 0 < RCLike.re (ω₀ x + mddbar n φlim x).coeffMatrix.det /
            RCLike.re (ω₀ x).coeffMatrix.det at hdet_pos
          exact (div_pos_iff_of_pos_right hωdet_pos).mp hdet_pos
        have hαdet_ne : (ω₀ x + mddbar n φlim x).coeffMatrix.det ≠ 0 := by
          intro hzero
          have hreal : RCLike.re ((ω₀ x + mddbar n φlim x).coeffMatrix.det) = 0 := by
            rw [hzero]
            simp
          linarith
        have hαdet_unit : IsUnit (ω₀ x + mddbar n φlim x).coeffMatrix.det :=
          isUnit_iff_ne_zero.mpr hαdet_ne
        have hαmatrix_unit : IsUnit (ω₀ x + mddbar n φlim x).coeffMatrix :=
          (Matrix.isUnit_iff_isUnit_det
            (A := (ω₀ x + mddbar n φlim x).coeffMatrix)).mpr hαdet_unit
        have hαmatrix_posSemidef : (ω₀ x + mddbar n φlim x).coeffMatrix.PosSemidef :=
          (ContinuousAlternatingMap.isNonneg_iff.mp hαlim_nonneg).2
        have hαmatrix_posDef : (ω₀ x + mddbar n φlim x).coeffMatrix.PosDef :=
          hαmatrix_posSemidef.posDef_iff_isUnit.mpr hαmatrix_unit
        exact (ContinuousAlternatingMap.isPositive_iff).mpr
          ⟨hφlim_oneOne x, hαmatrix_posDef⟩
      exact hpositive_limit

end KahlerForm
