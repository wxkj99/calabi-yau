module

public import CalabiYau.Geometry.Kahler.Sobolev
public import CalabiYau.Analysis.Sobolev.Manifold.Embedding.Intrinsic
public import CalabiYau.Geometry.Riemannian.Volume.Invariance

/-!
# Sobolev inequality transfer in real dimension greater than two

Transfer the extracted real Riemannian Sobolev inequality to the Kähler convention. The volume and
pointwise gradient identities are explicit hypotheses so this transfer can be proved before the
Kähler-to-Riemannian bridge is available. The source theorem uses the canonical Borel measurable
space, as does the extracted Riemannian volume API.
-/

@[expose] public section

open scoped Manifold ContDiff
open MeasureTheory
open CalabiYau CalabiYau.Riemannian

namespace KahlerForm

section CanonicalBorel

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω M]
  [T2Space M] [CompactSpace M] [SigmaCompactSpace M]

local instance instMeasurableSpaceAboveTwo : MeasurableSpace M := borel M
local instance instBorelSpaceAboveTwo : BorelSpace M := ⟨rfl⟩

/-- On a Kähler manifold of complex dimension at least two, transfer the real Riemannian Sobolev
inequality to the canonical-Borel Kähler volume and gradient conventions. -/
theorem sobolevInequality_of_sobolev_two_integral
    (ω₀ : KahlerForm n M)
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) M)
    (hn : 2 ≤ n)
    (hvol : ω₀.volume = CalabiYau.RiemannianVolume.riemannianVolumeMeasure
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g)
    (hgrad : ∀ f : M → ℝ,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ) ∞ f →
      ∀ x, g.inner x (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x)
          (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x) =
        2 * ω₀.gradNormSq f x) :
    ∃ C : ℝ, 0 ≤ C ∧
      ω₀.SobolevInequality ((n : ℝ) / ((n : ℝ) - 1)) (4 * C ^ 2) := by
  have hdimReal :
      (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) = 2 * (n : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
    norm_num
  have hdim : 2 < (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) := by
    rw [hdimReal]
    have hnNat : 2 < 2 * n := by omega
    exact_mod_cast hnNat
  obtain ⟨C, hC, hSob⟩ :=
    Sobolev.sobolev_two_integral
      (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (M := M) g hdim
  have hnreal : 1 < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hden : (n : ℝ) - 1 ≠ 0 := by linarith
  have hden' : 2 * (n : ℝ) - 2 ≠ 0 := by linarith
  have hexp :
      (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) * 2 /
          ((Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) : ℝ) - 2) =
        2 * ((n : ℝ) / ((n : ℝ) - 1)) := by
    rw [hdimReal]
    field_simp [hden, hden']
  rw [hexp] at hSob
  refine ⟨C, hC, ?_⟩
  intro f hf
  let μ := ω₀.volume
  let κ : ℝ := (n : ℝ) / ((n : ℝ) - 1)
  have hκpos : 0 < κ := by
    dsimp [κ]
    positivity
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hfmeas : AEStronglyMeasurable f μ := hf.continuous.aestronglyMeasurable
  have hLp :
      lpNorm f (ENNReal.ofReal (2 * κ)) μ =
        (∫ x, |f x| ^ (2 * κ) ∂μ) ^ ((2 * κ)⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top hfmeas]
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * κ)]
    simp only [Real.norm_eq_abs]
  have hIntNonneg : 0 ≤ ∫ x, |f x| ^ (2 * κ) ∂μ :=
    integral_nonneg fun x => by positivity
  have hpowexp : κ⁻¹ = (2 * κ)⁻¹ * 2 := by
    field_simp [hκpos.ne']
  have hLeft :
      (∫ x, |f x| ^ (2 * κ) ∂μ) ^ κ⁻¹ =
        lpNorm f (ENNReal.ofReal (2 * κ)) μ ^ 2 := by
    rw [hLp, hpowexp, Real.rpow_mul hIntNonneg]
    exact Real.rpow_natCast _ 2
  have hSob := hSob hf
  rw [← hvol] at hSob
  have hSob' :
      lpNorm f (ENNReal.ofReal (2 * κ)) μ ^ 2 ≤
        2 * C ^ 2 * ((∫ x, f x ^ 2 ∂μ) +
          ∫ x, g.inner x (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x)
              (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x) ∂μ) := by
    simpa only [μ, κ] using hSob
  have henergy :
      (∫ x, g.inner x (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x)
          (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x) ∂μ) =
        2 * ∫ x, ω₀.gradNormSq f x ∂μ := by
    calc
      _ = ∫ x, 2 * ω₀.gradNormSq f x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (hgrad f hf)
      _ = 2 * ∫ x, ω₀.gradNormSq f x ∂μ := by rw [integral_const_mul]
  have hgradCont : Continuous (ω₀.gradNormSq f) :=
    (ω₀.contMDiff_gradNormSq hf).continuous
  have hgradInt : Integrable (ω₀.gradNormSq f) μ :=
    hgradCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfSqInt : Integrable (fun x => f x ^ 2) μ :=
    (hf.continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum :
      (∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂μ) =
        (∫ x, ω₀.gradNormSq f x ∂μ) + ∫ x, f x ^ 2 ∂μ := by
    rw [integral_add hgradInt hfSqInt]
  have hA : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (f x)
  have hB : 0 ≤ ∫ x, ω₀.gradNormSq f x ∂μ :=
    integral_nonneg fun x => ω₀.gradNormSq_nonneg f x
  rw [hLeft]
  calc
    lpNorm f (ENNReal.ofReal (2 * κ)) μ ^ 2 ≤
        2 * C ^ 2 * ((∫ x, f x ^ 2 ∂μ) + 2 * ∫ x, ω₀.gradNormSq f x ∂μ) := by
          calc
            _ ≤ 2 * C ^ 2 * ((∫ x, f x ^ 2 ∂μ) +
                ∫ x, g.inner x (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x)
                    (gradFun (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) g f x) ∂μ) := hSob'
            _ = _ := by rw [henergy]
    _ ≤ 4 * C ^ 2 * (∫ x, (ω₀.gradNormSq f x + f x ^ 2) ∂μ) := by
      rw [hsum]
      nlinarith [sq_nonneg C]

end CanonicalBorel

end KahlerForm
