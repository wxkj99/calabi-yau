-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Holder/Localization.lean
-- Locally modified.
module
public import CalabiYau.Mathlib.Analysis.Holder.Scaling
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

noncomputable section

open Set
open scoped ENNReal NNReal

namespace CalabiYau.Schauder

variable {X V F : Type*} [MetricSpace X]
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem eContDiffHolderGaugeOn_congr {s : Set V} {f g : V → F}
    {k : Nat} (hfg : ∀ j ≤ k,
      Set.EqOn (iteratedFDeriv Real j f) (iteratedFDeriv Real j g) s)
    (alpha : NNReal) :
    eContDiffHolderGaugeOn k alpha s f =
      eContDiffHolderGaugeOn k alpha s g := by
  unfold eContDiffHolderGaugeOn
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    exact eSupNormOn_congr
      (hfg j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  · exact eHolderSeminormOn_congr (hfg k le_rfl) alpha

def holderBallOscillationConst (R : Real) (alpha K : NNReal) : NNReal :=
  K * (Real.toNNReal R) ^ (alpha : Real)

omit [NormedSpace Real F] [NormedAddCommGroup V] [NormedSpace Real V] in
theorem norm_sub_le_holderBallOscillationConst_of_mem_ball
    {center x : X} {R : Real} (hR : 0 < R)
    {alpha K : NNReal} {f : X → F}
    (hf : HolderWith K alpha ((Metric.ball center R).domRestrict f))
    (hx : x ∈ Metric.ball center R) :
    ‖f center - f x‖ ≤ holderBallOscillationConst R alpha K := by
  have hcenter : center ∈ Metric.ball center R := by
    simpa only [Metric.mem_ball, dist_self] using hR
  have hraw := hf.dist_le
    (⟨center, hcenter⟩ : Metric.ball center R)
    (⟨x, hx⟩ : Metric.ball center R)
  have hdist : dist center x ≤ R := by
    simpa only [dist_comm] using (Metric.mem_ball.mp hx).le
  have hrpow : dist center x ^ (alpha : Real) ≤ R ^ (alpha : Real) :=
    Real.rpow_le_rpow (dist_nonneg) hdist alpha.coe_nonneg
  calc
    ‖f center - f x‖ = dist (f center) (f x) := (dist_eq_norm _ _).symm
    _ ≤ (K : Real) * dist center x ^ (alpha : Real) := by
      simpa only [Set.domRestrict_apply, Subtype.dist_eq] using hraw
    _ ≤ (K : Real) * R ^ (alpha : Real) :=
      mul_le_mul_of_nonneg_left hrpow K.coe_nonneg
    _ = holderBallOscillationConst R alpha K := by
      simp only [holderBallOscillationConst, NNReal.coe_mul, NNReal.coe_rpow,
        Real.coe_toNNReal R hR.le]

theorem holderWith_smul_of_norm_le
    {X₀ : Type*} [PseudoEMetricSpace X₀]
    {alpha C D M N : NNReal} {f : X₀ → Real} {g : X₀ → F}
    (hf : HolderWith C alpha f) (hg : HolderWith D alpha g)
    (hfnorm : ∀ x, ‖f x‖ ≤ M) (hgnorm : ∀ x, ‖g x‖ ≤ N) :
    HolderWith (M * D + N * C) alpha (f • g) := by
  intro x y
  have hleft : edist (f x • g x) (f x • g y) ≤
      (M : ENNReal) * edist (g x) (g y) := by
    refine (edist_smul_le (f x) (g x) (g y)).trans ?_
    rw [ENNReal.smul_def]
    have hnorm : (↑‖f x‖₊ : ENNReal) ≤ (M : ENNReal) := by
      exact_mod_cast hfnorm x
    exact _root_.mul_le_mul_left hnorm _
  have hright : edist (f x • g y) (f y • g y) ≤
      edist (f x) (f y) * (N : ENNReal) := by
    rw [edist_dist, edist_dist]
    have hreal : dist (f x • g y) (f y • g y) ≤
        dist (f x) (f y) * (N : Real) :=
      (dist_pair_smul (f x) (f y) (g y)).trans
        (mul_le_mul_of_nonneg_left
          (by simpa only [dist_zero_right] using hgnorm y) dist_nonneg)
    calc
      ENNReal.ofReal (dist (f x • g y) (f y • g y)) ≤
          ENNReal.ofReal (dist (f x) (f y) * (N : Real)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (dist (f x) (f y)) * (N : ENNReal) := by
        rw [ENNReal.ofReal_mul (dist_nonneg : 0 ≤ dist (f x) (f y))]
        congr 1
        exact ENNReal.ofReal_coe_nnreal
  calc
    edist (f x • g x) (f y • g y) ≤
        edist (f x • g x) (f x • g y) +
          edist (f x • g y) (f y • g y) := edist_triangle _ _ _
    _ ≤ (M : ENNReal) * edist (g x) (g y) +
        edist (f x) (f y) * (N : ENNReal) := add_le_add hleft hright
    _ ≤ (M : ENNReal) * ((D : ENNReal) * edist x y ^ (alpha : Real)) +
        ((C : ENNReal) * edist x y ^ (alpha : Real)) * (N : ENNReal) := by
      gcongr
      · exact hg x y
      · exact hf x y
    _ = ((M * D + N * C : NNReal) : ENNReal) *
        edist x y ^ (alpha : Real) := by
      push_cast
      ring

theorem holderWith_congr
    {X₀ Y₀ : Type*} [PseudoEMetricSpace X₀] [PseudoEMetricSpace Y₀]
    {alpha C : NNReal} {f g : X₀ → Y₀}
    (hf : HolderWith C alpha f) (hfg : ∀ x, f x = g x) :
    HolderWith C alpha g := by
  have h : f = g := funext hfg
  exact h ▸ hf

theorem holderWith_add
    {X₀ Y₀ : Type*} [PseudoEMetricSpace X₀] [SeminormedAddCommGroup Y₀]
    {alpha C D : NNReal} {f g : X₀ → Y₀}
    (hf : HolderWith C alpha f) (hg : HolderWith D alpha g) :
    HolderWith (C + D) alpha (f + g) := by
  intro x y
  simp only [Pi.add_apply, ENNReal.coe_add]
  grw [edist_add_add_le, hf x y, hg x y]
  rw [add_mul]

def cutoffExtension (chi : X → Real) (f0 : F) (f : X → F) : X → F :=
  fun x ↦ f0 + chi x • (f x - f0)

omit [MetricSpace X] in
@[simp]
theorem cutoffExtension_apply
    (chi : X → Real) (f0 : F) (f : X → F) (x : X) :
    cutoffExtension chi f0 f x = f0 + chi x • (f x - f0) :=
  rfl

theorem holderWith_comp_continuousLinearMap_of_norm_le_one
    {X₀ A B : Type*} [PseudoEMetricSpace X₀]
    [NormedAddCommGroup A] [NormedSpace Real A]
    [NormedAddCommGroup B] [NormedSpace Real B]
    {alpha K : NNReal} {f : X₀ → A}
    (L : A →L[Real] B) (hL : ‖L‖ ≤ 1)
    (hf : HolderWith K alpha f) :
    HolderWith K alpha (fun x ↦ L (f x)) := by
  have hraw := L.lipschitz.holderWith.comp hf
  have hraw' : HolderWith (‖L‖₊ * K) alpha (fun x ↦ L (f x)) := by
    change HolderWith (‖L‖₊ * K) alpha (⇑L ∘ f)
    simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using hraw
  have hnorm : ‖L‖₊ * K ≤ K := by
    apply mul_le_of_le_one_left zero_le
    exact_mod_cast hL
  exact hraw'.mono hnorm

omit [NormedSpace Real F] in
theorem holderWith_finset_sum
    {X₀ I : Type*} [PseudoEMetricSpace X₀]
    {alpha : NNReal} {K : I → NNReal} {f : I → X₀ → F}
    (s : Finset I) (h : ∀ i ∈ s, HolderWith (K i) alpha (f i)) :
    HolderWith (∑ i ∈ s, K i) alpha (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change HolderWith 0 alpha (0 : X₀ → F)
      exact HolderWith.zero
  | @insert i s hi ih =>
      have hi' := h i (Finset.mem_insert_self i s)
      have hs' := ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
      rw [Finset.sum_insert hi]
      have hfun : (fun x => ∑ j ∈ insert i s, f j x) =
          f i + fun x => ∑ j ∈ s, f j x := by
        funext x
        rw [Finset.sum_insert hi, Pi.add_apply]
      rw [hfun]
      exact holderWith_add hi' hs'

theorem holderWith_of_hasFDerivAt_of_norm_le
    {A : Type*} [NormedAddCommGroup A] [NormedSpace Real A]
    {f : V → A} {df : V → V →L[Real] A}
    {alpha M N : NNReal}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (hf : ∀ x, HasFDerivAt f (df x) x)
    (hfnorm : ∀ x, ‖f x‖ ≤ M)
    (hdfnorm : ∀ x, ‖df x‖ ≤ N) :
    HolderWith (max (2 * M) N) alpha f := by
  have hlip : LipschitzWith N f := by
    apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · exact fun x ↦ (hf x).differentiableAt
    · intro x
      rw [(hf x).fderiv]
      exact_mod_cast hdfnorm x
  have hzero : HolderWith (2 * M) 0 f :=
    holderWith_zero_of_norm_le hfnorm
  exact hzero.of_le_of_le hlip.holderWith halpha0 halpha1

end CalabiYau.Schauder

end
