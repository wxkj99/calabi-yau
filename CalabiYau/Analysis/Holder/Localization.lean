-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Holder/Localization.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Holder.Scaling
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


noncomputable section

open Set
open scoped ENNReal NNReal

namespace CalabiYau.Schauder

variable {X V F : Type*} [MetricSpace X]
  [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem ball_parabolicPoint_eq_parabolicCylinder
    {Y : Type*} [PseudoMetricSpace Y]
    (t0 R : Real) (hR : 0 ≤ R) (x0 : Y) :
    Metric.ball (parabolicPoint t0 x0) R =
      parabolicCylinder (Set.Ioo (t0 - R ^ 2) (t0 + R ^ 2))
        (Metric.ball x0 R) := by
  ext p
  rw [Metric.mem_ball]
  change dist p (parabolicPoint t0 x0) < R ↔
    (t0 - R ^ 2 < p.time ∧ p.time < t0 + R ^ 2) ∧
      dist p.space x0 < R
  rw [← parabolicPoint_time_space p, dist_parabolicPoint]
  simp only [parabolicPoint_time, parabolicPoint_space]
  constructor
  · intro hp
    have hmax := max_lt_iff.mp hp
    have htimeRoot : Real.sqrt |p.time - t0| < R := by
      simpa only [Real.sqrt_eq_rpow] using hmax.1
    have htimeSq :=
      (sq_lt_sq₀ (Real.sqrt_nonneg |p.time - t0|) hR).mpr htimeRoot
    rw [Real.sq_sqrt (abs_nonneg _)] at htimeSq
    have htime := abs_lt.mp htimeSq
    exact ⟨⟨by linarith, by linarith⟩, hmax.2⟩
  · rintro ⟨htime, hspace⟩
    have htimeAbs : |p.time - t0| < R ^ 2 := by
      rw [abs_lt]
      constructor <;> linarith
    have htimeSq : (Real.sqrt |p.time - t0|) ^ 2 < R ^ 2 := by
      rw [Real.sq_sqrt (abs_nonneg _)]
      exact htimeAbs
    have htimeRoot :=
      (sq_lt_sq₀ (Real.sqrt_nonneg |p.time - t0|) hR).mp htimeSq
    apply max_lt_iff.mpr
    exact ⟨by simpa only [Real.sqrt_eq_rpow] using htimeRoot, hspace⟩

omit [NormedSpace Real V] in
theorem parabolicRescaleTimeInterval_subset_of_ball_subset
    {J : Set Real} {Omega : Set V} {p : ParabolicPoint V}
    (r : NNReal) (hr : 0 < r) (R : Real) (hR1 : R < 1)
    (hball : Metric.ball p r ⊆ parabolicCylinder J Omega) :
    parabolicRescaleTimeInterval r p R ⊆ J := by
  intro t ht
  have hrReal : 0 < (r : Real) := NNReal.coe_pos.mpr hr
  have hpoint : parabolicPoint t p.space ∈ Metric.ball p r := by
    rw [← parabolicPoint_time_space p,
      ball_parabolicPoint_eq_parabolicCylinder p.time r r.coe_nonneg p.space]
    refine ⟨?_, Metric.mem_ball_self hrReal⟩
    change p.time - (r : Real) ^ 2 < t ∧
      t < p.time + (r : Real) ^ 2
    rw [parabolicRescaleTimeInterval] at ht
    have hscaleLt : (r : Real) ^ 2 * R < (r : Real) ^ 2 :=
      by simpa only [mul_one] using
        mul_lt_mul_of_pos_left hR1 (pow_pos hrReal 2)
    constructor <;> linarith [ht.1, ht.2]
  exact (hball hpoint).1

theorem eParabolicC2HolderGaugeOn_ball_le_of_timeTranslate
    (tau R : Real) (hR : 0 ≤ R) (x0 : V) (alpha C : NNReal)
    (u : Real → V → F)
    (hspace : ∀ p ∈ Metric.ball (parabolicPoint 0 x0) R,
      ContDiff Real 2 (u p.time))
    (h : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Set.Ioo (-R ^ 2 - tau) (R ^ 2 - tau))
        (Metric.ball x0 R))
      (parabolicRescaleAt 1 (parabolicPoint tau 0) u) ≤ C) :
    eParabolicC2HolderGaugeOn alpha
        (Metric.ball (parabolicPoint 0 x0) R) u ≤
      parabolicC2HolderRescaleConst 1 alpha C := by
  have hspace' : ∀ p ∈ parabolicCylinder
      (Set.Ioo (-R ^ 2 - tau + tau) (R ^ 2 - tau + tau))
      (Metric.ball x0 R), ContDiff Real 2 (u p.time) := by
    intro p hp
    apply hspace p
    rw [ball_parabolicPoint_eq_parabolicCylinder 0 R hR x0]
    simpa only [zero_sub, zero_add,
      show -R ^ 2 - tau + tau = -R ^ 2 by ring,
      show R ^ 2 - tau + tau = R ^ 2 by ring] using hp
  rw [ball_parabolicPoint_eq_parabolicCylinder 0 R hR x0]
  have hresult :=
    eParabolicC2HolderGaugeOn_parabolicCylinder_Ioo_le_of_timeTranslate
      tau (-R ^ 2 - tau) (R ^ 2 - tau) (Metric.ball x0 R)
        alpha C u hspace' h
  rw [show -R ^ 2 - tau + tau = -R ^ 2 by ring,
    show R ^ 2 - tau + tau = R ^ 2 by ring] at hresult
  simpa only [zero_sub, zero_add] using hresult

theorem eParabolicC2HolderGaugeOn_centered_ball_le_of_parabolicCylinder
    {t₀ t₁ r : Real} (hr : 0 ≤ r) (htime : t₁ - t₀ = 2 * r ^ 2)
    (center : V) (alpha C : NNReal)
    (u : Real → BoundedContinuousFunction V F)
    (du : Real → BoundedContinuousFunction V (V →L[Real] F))
    (d2u : Real → BoundedContinuousFunction V (V →L[Real] V →L[Real] F))
    (hu : ∀ s ∈ Set.Ioo t₀ t₁, ∀ x,
      HasFDerivAt (u s : V → F) (du s x) x)
    (hdu : ∀ s ∈ Set.Ioo t₀ t₁, ∀ x,
      HasFDerivAt (du s : V → V →L[Real] F) (d2u s x) x)
    (h : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Set.Ioo t₀ t₁) (Metric.ball center r))
      (fun t x ↦ u t x) ≤ C) :
    eParabolicC2HolderGaugeOn alpha
        (Metric.ball (parabolicPoint 0 center) r)
        (fun t x ↦ u ((t₀ + t₁) / 2 + t) x) ≤
      parabolicC2HolderRescaleConst 1 alpha C := by
  let midpoint : Real := (t₀ + t₁) / 2
  let v : Real → V → F := fun t x ↦ u (midpoint + t) x
  let tau : Real := -midpoint
  have hspace : ∀ p ∈ Metric.ball (parabolicPoint 0 center) r,
      ContDiff Real 2 (v p.time) := by
    intro p hp
    have hpCylinder : p ∈ parabolicCylinder
        (Set.Ioo (-r ^ 2) (r ^ 2)) (Metric.ball center r) := by
      rw [ball_parabolicPoint_eq_parabolicCylinder 0 r hr center] at hp
      simpa only [zero_sub, zero_add] using hp
    have hs : midpoint + p.time ∈ Set.Ioo t₀ t₁ := by
      dsimp only [midpoint]
      constructor <;> nlinarith [htime, hpCylinder.1.1, hpCylinder.1.2]
    exact contDiff_two_of_hasFDerivAt (u (midpoint + p.time))
      (du (midpoint + p.time)) (d2u (midpoint + p.time))
      (hu (midpoint + p.time) hs) (hdu (midpoint + p.time) hs)
  have htranslate : parabolicRescaleAt 1 (parabolicPoint tau 0) v =
      fun t x ↦ u t x := by
    funext t x
    change u (midpoint + (tau + 1 ^ 2 * t)) (0 + (1 : Real) • x) = u t x
    rw [one_pow, one_mul, one_smul, zero_add]
    congr 2
    dsimp only [tau]
    ring
  have hleft : -r ^ 2 - tau = t₀ := by
    dsimp only [tau, midpoint]
    nlinarith [htime]
  have hright : r ^ 2 - tau = t₁ := by
    dsimp only [tau, midpoint]
    nlinarith [htime]
  have hsource : eParabolicC2HolderGaugeOn alpha
      (parabolicCylinder (Set.Ioo (-r ^ 2 - tau) (r ^ 2 - tau))
        (Metric.ball center r))
      (parabolicRescaleAt 1 (parabolicPoint tau 0) v) ≤ C := by
    rw [hleft, hright, htranslate]
    exact h
  have hresult := eParabolicC2HolderGaugeOn_ball_le_of_timeTranslate
    tau r hr center alpha C v hspace hsource
  simpa only [v, midpoint] using hresult

def parabolicInteriorRadius
    (a t₀ t₁ b r R : Real) : Real :=
  min (Real.sqrt (t₀ - a))
    (min (Real.sqrt (b - t₁)) (R - r)) / 2

theorem parabolicInteriorRadius_pos
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b) (hrR : r < R) :
    0 < parabolicInteriorRadius a t₀ t₁ b r R := by
  unfold parabolicInteriorRadius
  apply div_pos
  · exact lt_min (Real.sqrt_pos.2 (sub_pos.2 hat₀))
      (lt_min (Real.sqrt_pos.2 (sub_pos.2 ht₁b)) (sub_pos.2 hrR))
  · norm_num

theorem ball_parabolicInteriorRadius_subset_parabolicCylinder
    {a t₀ t₁ b r R : Real}
    (hat₀ : a < t₀) (ht₁b : t₁ < b)
    (hrR : r < R) {center : X} {p : ParabolicPoint X}
    (hp : p ∈ parabolicCylinder (Set.Icc t₀ t₁)
      (Metric.closedBall center r)) :
    Metric.ball p (parabolicInteriorRadius a t₀ t₁ b r R) ⊆
      parabolicCylinder (Set.Icc a b) (Metric.closedBall center R) := by
  let delta := parabolicInteriorRadius a t₀ t₁ b r R
  have hdelta : 0 < delta := parabolicInteriorRadius_pos hat₀ ht₁b hrR
  have hdleft : delta ≤ Real.sqrt (t₀ - a) / 2 := by
    dsimp only [delta, parabolicInteriorRadius]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hdright : delta ≤ Real.sqrt (b - t₁) / 2 := by
    dsimp only [delta, parabolicInteriorRadius]
    exact div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hdspace : delta ≤ (R - r) / 2 := by
    dsimp only [delta, parabolicInteriorRadius]
    exact div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  have hdleftSq : delta ^ 2 ≤ t₀ - a := by
    have hsqrtSq : (Real.sqrt (t₀ - a)) ^ 2 = t₀ - a :=
      Real.sq_sqrt (sub_nonneg.2 hat₀.le)
    nlinarith [sq_nonneg (Real.sqrt (t₀ - a) / 2 - delta)]
  have hdrightSq : delta ^ 2 ≤ b - t₁ := by
    have hsqrtSq : (Real.sqrt (b - t₁)) ^ 2 = b - t₁ :=
      Real.sq_sqrt (sub_nonneg.2 ht₁b.le)
    nlinarith [sq_nonneg (Real.sqrt (b - t₁) / 2 - delta)]
  intro q hq
  have hqdist : dist q p < delta := by
    simpa only [delta] using Metric.mem_ball.mp hq
  have hqdistMax :
      max (|q.time - p.time| ^ (1 / 2 : Real))
          (dist q.space p.space) < delta := by
    calc
      max (|q.time - p.time| ^ (1 / 2 : Real))
          (dist q.space p.space) = dist q p := by
        rw [← parabolicPoint_time_space q, ← parabolicPoint_time_space p,
          dist_parabolicPoint]
        rfl
      _ < delta := hqdist
  have htimeSqrt : Real.sqrt |q.time - p.time| < delta := by
    rw [Real.sqrt_eq_rpow]
    exact (le_max_left _ _).trans_lt hqdistMax
  have htimeAbs : |q.time - p.time| < delta ^ 2 := by
    have hsqrtSq : (Real.sqrt |q.time - p.time|) ^ 2 =
        |q.time - p.time| := Real.sq_sqrt (abs_nonneg _)
    nlinarith [Real.sqrt_nonneg |q.time - p.time|]
  have htimeBounds := abs_lt.mp htimeAbs
  have hqa : a ≤ q.time := by
    linarith [hp.1.1]
  have hqb : q.time ≤ b := by
    linarith [hp.1.2]
  have hspaceDist : dist q.space p.space < delta :=
    (le_max_right _ _).trans_lt hqdistMax
  have hqcenter : dist q.space center ≤ R := by
    calc
      dist q.space center ≤ dist q.space p.space + dist p.space center :=
        dist_triangle _ _ _
      _ ≤ delta + r := add_le_add hspaceDist.le
        (Metric.mem_closedBall.mp hp.2)
      _ ≤ R := by linarith
  exact ⟨⟨hqa, hqb⟩, Metric.mem_closedBall.mpr hqcenter⟩

theorem exists_finite_ball_cover_of_isCompact
    {K : Set X} (hK : IsCompact K) (radius : K → Real)
    (hradius : ∀ x, 0 < radius x) :
    ∃ s : Finset K, K ⊆ ⋃ x ∈ s, Metric.ball x.1 (radius x) := by
  let U : K → Set X := fun x ↦ Metric.ball x.1 (radius x)
  have hcover : K ⊆ ⋃ x, U x := by
    intro x hx
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩, Metric.mem_ball_self (hradius ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U
    (fun _ ↦ Metric.isOpen_ball) hcover
  exact ⟨s, hs⟩

theorem exists_finite_buffered_ball_cover_of_isCompact
    {K : Set X} (hK : IsCompact K) (radius : K → Real)
    (hradius : ∀ x, 0 < radius x) (theta : NNReal) (htheta : 0 < theta) :
    ∃ s : Finset K, ∃ delta : NNReal, 0 < delta ∧
      (∀ x ∈ s, (delta : Real) ≤ (theta : Real) * radius x) ∧
      K ⊆ ⋃ x ∈ s, Metric.ball x.1 ((theta : Real) * radius x) := by
  have hscaledRadius : ∀ x, 0 < (theta : Real) * radius x := by
    intro x
    exact mul_pos (NNReal.coe_pos.mpr htheta) (hradius x)
  obtain ⟨s, hs⟩ := exists_finite_ball_cover_of_isCompact hK
    (fun x ↦ (theta : Real) * radius x) hscaledRadius
  let deltaReal : Real := if h : s.Nonempty then
      s.inf' h (fun x ↦ (theta : Real) * radius x) else 1
  have hdeltaReal : 0 < deltaReal := by
    rw [show deltaReal = if h : s.Nonempty then
        s.inf' h (fun x ↦ (theta : Real) * radius x) else 1 by rfl]
    split
    · next h =>
        rw [Finset.lt_inf'_iff]
        exact fun x _ ↦ hscaledRadius x
    · exact one_pos
  let delta : NNReal := ⟨deltaReal, hdeltaReal.le⟩
  have hdelta : 0 < delta := by exact_mod_cast hdeltaReal
  have hdeltaLe : ∀ x ∈ s,
      (delta : Real) ≤ (theta : Real) * radius x := by
    intro x hx
    dsimp only [delta]
    change deltaReal ≤ (theta : Real) * radius x
    rw [show deltaReal = if h : s.Nonempty then
        s.inf' h (fun y ↦ (theta : Real) * radius y) else 1 by rfl]
    split
    · next h => exact Finset.inf'_le _ hx
    · next h => exact (h ⟨x, hx⟩).elim
  exact ⟨s, delta, hdelta, hdeltaLe, hs⟩

omit [NormedSpace Real V] [NormedSpace Real F] in
theorem holderWith_parabolicCylinder_Icc_of_time_support
    {a b S T : Real} (ha : 0 < a) (haT : a ≤ T) (hbT : b < T)
    (hTS : T ≤ S)
    {alpha K : NNReal} (f : ParabolicPoint V → F)
    (hsupport : ∀ p, p.time ∈ Set.Icc (0 : Real) S →
      p.time ∉ Set.Ioo a b → f p = 0)
    (hlocal : HolderWith K alpha
      ((parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ).domRestrict f)) :
    HolderWith K alpha
      ((parabolicCylinder (Set.Icc (0 : Real) S) Set.univ).domRestrict f) := by
  let Q := parabolicCylinder (Set.Icc (0 : Real) S) (Set.univ : Set V)
  let U := parabolicCylinder (Set.Ioc (0 : Real) T) (Set.univ : Set V)
  let project : Q → U := fun p ↦
    ⟨parabolicPoint
      ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) p.1.space,
      ⟨⟨ha.trans_le (Set.projIcc a T haT p.1.time).2.1,
        (Set.projIcc a T haT p.1.time).2.2⟩, Set.mem_univ p.1.space⟩⟩
  have hproject : LipschitzWith 1 project := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (project p).1 (project q).1 ≤ (1 : Real) * dist p.1 q.1
    rw [one_mul]
    dsimp only [project]
    rw [dist_parabolicPoint, ← parabolicPoint_time_space p.1,
      ← parabolicPoint_time_space q.1, dist_parabolicPoint]
    apply max_le_max
    · exact Real.rpow_le_rpow
        (abs_nonneg _)
        (Set.abs_projIcc_sub_projIcc haT)
        (by norm_num)
    · exact le_rfl
  have hprojectValue : ∀ p : Q, f (project p).1 = f p.1 := by
    intro p
    have hprojectMem : (project p).1.time ∈ Set.Icc (0 : Real) S := by
      exact ⟨le_trans (le_of_lt ha)
          (Set.projIcc a T haT p.1.time).2.1,
        (Set.projIcc a T haT p.1.time).2.2.trans hTS⟩
    by_cases hp : p.1.time ∈ Set.Icc a T
    · have hproj := Set.projIcc_of_mem haT hp
      change f (parabolicPoint
        ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) p.1.space) =
          f p.1
      rw [show ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) =
        p.1.time from congrArg Subtype.val hproj, parabolicPoint_time_space]
    · by_cases hpa : p.1.time < a
      · have hproj := Set.projIcc_of_le_left haT hpa.le
        have hprojectTime : (project p).1.time = a := by
          change ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) = a
          exact congrArg Subtype.val hproj
        rw [hsupport p.1 p.2.1 (fun hmem ↦ (not_lt_of_ge hpa.le) hmem.1),
          hsupport (project p).1 hprojectMem (fun hmem ↦
            (lt_irrefl a) (hprojectTime ▸ hmem.1))]
      · have hpT : T < p.1.time := by
          by_contra hnot
          exact hp ⟨le_of_not_gt hpa, le_of_not_gt hnot⟩
        have hproj := Set.projIcc_of_right_le haT hpT.le
        have hprojectTime : (project p).1.time = T := by
          change ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) = T
          exact congrArg Subtype.val hproj
        rw [hsupport p.1 p.2.1 (fun hmem ↦
            (not_lt_of_ge (hbT.le.trans hpT.le)) hmem.2),
          hsupport (project p).1 hprojectMem (fun hmem ↦
            (not_lt_of_ge hbT.le) (hprojectTime ▸ hmem.2))]
  have hcomp := hlocal.comp hproject.holderWith
  have hfun :
      ((parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ).domRestrict f) ∘
          project = Q.domRestrict f := by
    funext p
    exact hprojectValue p
  rw [hfun] at hcomp
  simpa only [Q, NNReal.one_rpow, mul_one] using hcomp

omit [NormedAddCommGroup V] [NormedSpace Real V] [NormedSpace Real F] in
theorem eSupNormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
    {a b S T : Real} (ha : 0 < a) (haT : a ≤ T) (hbT : b < T)
    (hTS : T ≤ S)
    (f : ParabolicPoint V → F)
    (hsupport : ∀ p, p.time ∈ Set.Icc (0 : Real) S →
      p.time ∉ Set.Ioo a b → f p = 0) :
    eSupNormOn (parabolicCylinder (Set.Icc (0 : Real) S) Set.univ) f ≤
      eSupNormOn (parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ) f := by
  let Q := parabolicCylinder (Set.Icc (0 : Real) S) (Set.univ : Set V)
  let U := parabolicCylinder (Set.Ioc (0 : Real) T) (Set.univ : Set V)
  let project : Q → U := fun p ↦
    ⟨parabolicPoint
      ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) p.1.space,
      ⟨⟨ha.trans_le (Set.projIcc a T haT p.1.time).2.1,
        (Set.projIcc a T haT p.1.time).2.2⟩, Set.mem_univ p.1.space⟩⟩
  have hprojectValue : ∀ p : Q, f (project p).1 = f p.1 := by
    intro p
    have hprojectMem : (project p).1.time ∈ Set.Icc (0 : Real) S := by
      exact ⟨le_trans (le_of_lt ha)
          (Set.projIcc a T haT p.1.time).2.1,
        (Set.projIcc a T haT p.1.time).2.2.trans hTS⟩
    by_cases hp : p.1.time ∈ Set.Icc a T
    · have hproj := Set.projIcc_of_mem haT hp
      change f (parabolicPoint
        ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) p.1.space) =
          f p.1
      rw [show ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) =
        p.1.time from congrArg Subtype.val hproj, parabolicPoint_time_space]
    · by_cases hpa : p.1.time < a
      · have hproj := Set.projIcc_of_le_left haT hpa.le
        have hprojectTime : (project p).1.time = a := by
          change ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) = a
          exact congrArg Subtype.val hproj
        rw [hsupport p.1 p.2.1 (fun hmem ↦ (not_lt_of_ge hpa.le) hmem.1),
          hsupport (project p).1 hprojectMem (fun hmem ↦
            (lt_irrefl a) (hprojectTime ▸ hmem.1))]
      · have hpT : T < p.1.time := by
          by_contra hnot
          exact hp ⟨le_of_not_gt hpa, le_of_not_gt hnot⟩
        have hproj := Set.projIcc_of_right_le haT hpT.le
        have hprojectTime : (project p).1.time = T := by
          change ((Set.projIcc a T haT p.1.time : Set.Icc a T) : Real) = T
          exact congrArg Subtype.val hproj
        rw [hsupport p.1 p.2.1 (fun hmem ↦
            (not_lt_of_ge (hbT.le.trans hpT.le)) hmem.2),
          hsupport (project p).1 hprojectMem (fun hmem ↦
            (not_lt_of_ge hbT.le) (hprojectTime ▸ hmem.2))]
  rw [eSupNormOn_le]
  intro p hp
  rw [← hprojectValue ⟨p, hp⟩]
  exact norm_le_eSupNormOn U f (project ⟨p, hp⟩).1 (project ⟨p, hp⟩).2

omit [NormedSpace Real V] [NormedSpace Real F] in
theorem eHolderSeminormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
    {a b S T : Real} (ha : 0 < a) (haT : a ≤ T) (hbT : b < T)
    (hTS : T ≤ S)
    (alpha : NNReal) (f : ParabolicPoint V → F)
    (hsupport : ∀ p, p.time ∈ Set.Icc (0 : Real) S →
      p.time ∉ Set.Ioo a b → f p = 0) :
    eHolderSeminormOn alpha
        (parabolicCylinder (Set.Icc (0 : Real) S) Set.univ) f ≤
      eHolderSeminormOn alpha
        (parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ) f := by
  unfold eHolderSeminormOn eHolderNorm
  apply le_iInf
  intro C
  apply le_iInf
  intro hC
  exact HolderWith.eHolderNorm_le
    (holderWith_parabolicCylinder_Icc_of_time_support
      ha haT hbT hTS f hsupport hC)

theorem eParabolicC2HolderGaugeOn_Icc_le_Ioc_of_time_support
    {a b S T : Real} (ha : 0 < a) (haT : a ≤ T) (hbT : b < T)
    (hTS : T ≤ S)
    (alpha : NNReal) (u : Real → V → F)
    (hspatialSupport : ∀ j < 3, ∀ p,
      p.time ∈ Set.Icc (0 : Real) S →
        p.time ∉ Set.Ioo a b → parabolicSpatialJet j u p = 0)
    (htimeSupport : ∀ p,
      p.time ∈ Set.Icc (0 : Real) S →
        p.time ∉ Set.Ioo a b → parabolicTimeDerivative u p = 0) :
    eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Set.Icc (0 : Real) S) Set.univ) u ≤
      eParabolicC2HolderGaugeOn alpha
        (parabolicCylinder (Set.Ioc (0 : Real) T) Set.univ) u := by
  unfold eParabolicC2HolderGaugeOn
  gcongr with j hj
  · exact eSupNormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
      ha haT hbT hTS _ (hspatialSupport j (Finset.mem_range.mp hj))
  · exact eSupNormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
      ha haT hbT hTS _ htimeSupport
  · exact eHolderSeminormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
      ha haT hbT hTS alpha _ (hspatialSupport 2 (by norm_num))
  · exact eHolderSeminormOn_parabolicCylinder_Icc_le_Ioc_of_time_support
      ha haT hbT hTS alpha _ htimeSupport

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

theorem eParabolicC2HolderGaugeOn_congr
    {Q : Set (ParabolicPoint V)} {u v : Real → V → F}
    (hspatial : ∀ j ≤ 2,
      Set.EqOn (parabolicSpatialJet j u) (parabolicSpatialJet j v) Q)
    (htime : Set.EqOn (parabolicTimeDerivative u)
      (parabolicTimeDerivative v) Q)
    (alpha : NNReal) :
    eParabolicC2HolderGaugeOn alpha Q u =
      eParabolicC2HolderGaugeOn alpha Q v := by
  have hsum :
      (∑ j ∈ Finset.range 3,
        eSupNormOn Q (parabolicSpatialJet j u)) =
      ∑ j ∈ Finset.range 3,
        eSupNormOn Q (parabolicSpatialJet j v) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact eSupNormOn_congr
      (hspatial j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  have hsupTime : eSupNormOn Q (parabolicTimeDerivative u) =
      eSupNormOn Q (parabolicTimeDerivative v) :=
    eSupNormOn_congr htime
  have hholderSpatial :
      eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) =
        eHolderSeminormOn alpha Q (parabolicSpatialJet 2 v) :=
    eHolderSeminormOn_congr (hspatial 2 le_rfl) alpha
  have hholderTime :
      eHolderSeminormOn alpha Q (parabolicTimeDerivative u) =
        eHolderSeminormOn alpha Q (parabolicTimeDerivative v) :=
    eHolderSeminormOn_congr htime alpha
  unfold eParabolicC2HolderGaugeOn
  rw [hsum, hsupTime, hholderSpatial, hholderTime]

theorem eParabolicC2HolderGaugeWithLowerJetsOn_congr
    {Q : Set (ParabolicPoint V)} {u v : Real → V → F}
    (hvalue : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ v p.time p.space) Q)
    (hspatial : ∀ j ≤ 2,
      Set.EqOn (parabolicSpatialJet j u) (parabolicSpatialJet j v) Q)
    (htime : Set.EqOn (parabolicTimeDerivative u)
      (parabolicTimeDerivative v) Q)
    (alpha : NNReal) :
    eParabolicC2HolderGaugeWithLowerJetsOn alpha Q u =
      eParabolicC2HolderGaugeWithLowerJetsOn alpha Q v := by
  unfold eParabolicC2HolderGaugeWithLowerJetsOn
  rw [eParabolicC2HolderGaugeOn_congr hspatial htime alpha,
    eHolderSeminormOn_congr hvalue alpha,
    eHolderSeminormOn_congr (hspatial 1 (by norm_num)) alpha]

theorem isParabolicC2On_congr_of_eqOn_open
    {Q U : Set (ParabolicPoint V)} (hU : IsOpen U) (hQU : Q ⊆ U)
    {u v : Real → V → F}
    (huv : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ v p.time p.space) U)
    (hu : IsParabolicC2On Q u) :
    IsParabolicC2On Q v := by
  constructor
  · intro p hp
    have hmap : ContinuousAt
        (fun x ↦ parabolicPoint p.time x) p.space := by
      unfold parabolicPoint
      exact (continuous_const.prodMk continuous_id).continuousAt
    have heq : u p.time =ᶠ[nhds p.space] v p.time := by
      filter_upwards [hmap (hU.mem_nhds (hQU hp))] with x hx
      exact huv hx
    exact (hu.1 p hp).congr_of_eventuallyEq heq.symm
  · intro p hp
    have hmap : ContinuousAt
        (fun t ↦ parabolicPoint t p.space) p.time := by
      unfold parabolicPoint
      exact (Metric.Snowflaking.continuous_toSnowflaking.prodMk
        continuous_const).continuousAt
    have heq : (fun t ↦ u t p.space) =ᶠ[nhds p.time]
        fun t ↦ v t p.space := by
      filter_upwards [hmap (hU.mem_nhds (hQU hp))] with t ht
      exact huv ht
    exact heq.differentiableAt_iff.mp (hu.2 p hp)

theorem eParabolicC2HolderGaugeOn_congr_of_eqOn_open
    {Q U : Set (ParabolicPoint V)} (hU : IsOpen U) (hQU : Q ⊆ U)
    {u v : Real → V → F}
    (huv : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ v p.time p.space) U)
    (alpha : NNReal) :
    eParabolicC2HolderGaugeOn alpha Q u =
      eParabolicC2HolderGaugeOn alpha Q v := by
  apply eParabolicC2HolderGaugeOn_congr
  · intro j _hj p hp
    have hmap : ContinuousAt
        (fun x ↦ parabolicPoint p.time x) p.space := by
      unfold parabolicPoint
      exact (continuous_const.prodMk continuous_id).continuousAt
    have heq : u p.time =ᶠ[nhds p.space] v p.time := by
      filter_upwards [hmap (hU.mem_nhds (hQU hp))] with x hx
      exact huv hx
    unfold parabolicSpatialJet
    exact (Filter.EventuallyEq.iteratedFDeriv Real heq j).eq_of_nhds
  · intro p hp
    have hmap : ContinuousAt
        (fun t ↦ parabolicPoint t p.space) p.time := by
      unfold parabolicPoint
      exact (Metric.Snowflaking.continuous_toSnowflaking.prodMk
        continuous_const).continuousAt
    have heq : (fun t ↦ u t p.space) =ᶠ[nhds p.time]
        fun t ↦ v t p.space := by
      filter_upwards [hmap (hU.mem_nhds (hQU hp))] with t ht
      exact huv ht
    unfold parabolicTimeDerivative
    rw [heq.fderiv_eq]

theorem eParabolicC2HolderGaugeWithLowerJetsOn_congr_of_eqOn_open
    {Q U : Set (ParabolicPoint V)} (hU : IsOpen U) (hQU : Q ⊆ U)
    {u v : Real → V → F}
    (huv : Set.EqOn (fun p ↦ u p.time p.space)
      (fun p ↦ v p.time p.space) U)
    (alpha : NNReal) :
    eParabolicC2HolderGaugeWithLowerJetsOn alpha Q u =
      eParabolicC2HolderGaugeWithLowerJetsOn alpha Q v := by
  unfold eParabolicC2HolderGaugeWithLowerJetsOn
  rw [eParabolicC2HolderGaugeOn_congr_of_eqOn_open hU hQU huv alpha,
    eHolderSeminormOn_congr (huv.mono hQU) alpha]
  congr 1
  apply eHolderSeminormOn_congr
  intro p hp
  have hmap : ContinuousAt
      (fun x ↦ parabolicPoint p.time x) p.space := by
    unfold parabolicPoint
    exact (continuous_const.prodMk continuous_id).continuousAt
  have heq : u p.time =ᶠ[nhds p.space] v p.time := by
    filter_upwards [hmap (hU.mem_nhds (hQU hp))] with x hx
    exact huv hx
  unfold parabolicSpatialJet
  exact (Filter.EventuallyEq.iteratedFDeriv Real heq 1).eq_of_nhds

theorem eContDiffHolderGaugeOn_congr_of_eqOn_open
    {s U : Set V} (hU : IsOpen U) (hsU : s ⊆ U)
    {f g : V → F} (hfg : Set.EqOn f g U)
    (k : Nat) (alpha : NNReal) :
    eContDiffHolderGaugeOn k alpha s f =
      eContDiffHolderGaugeOn k alpha s g := by
  apply eContDiffHolderGaugeOn_congr
  intro j hj x hx
  have heq : f =ᶠ[nhds x] g :=
    Filter.mem_of_superset (hU.mem_nhds (hsU hx)) hfg
  exact (Filter.EventuallyEq.iteratedFDeriv Real heq j).eq_of_nhds

def holderBallOscillationConst (R : Real) (alpha K : NNReal) : NNReal :=
  K * (Real.toNNReal R) ^ (alpha : Real)

def bufferedBallHolderConst
    (alpha C B delta : NNReal) : NNReal :=
  C + 2 * B / delta ^ (alpha : Real)

omit [NormedSpace Real F] [NormedAddCommGroup V] [NormedSpace Real V] in
theorem holderWith_restrict_of_buffered_ball_cover
    {ι : Type*} {K : Set X} {alpha C B delta : NNReal}
    (hdelta : 0 < delta) (center : ι → X) (radius : ι → Real)
    (hbuffer : ∀ i, (delta : Real) ≤ radius i / 2)
    (hcover : ∀ x ∈ K, ∃ i, x ∈ Metric.ball (center i) (radius i / 2))
    {f : X → F}
    (hlocal : ∀ i, HolderWith C alpha
      ((Metric.ball (center i) (radius i)).domRestrict f))
    (hbound : ∀ x ∈ K, ‖f x‖ ≤ B) :
    HolderWith (bufferedBallHolderConst alpha C B delta) alpha
      (K.domRestrict f) := by
  intro x y
  rw [edist_dist, edist_dist]
  have hreal : dist (f x.1) (f y.1) ≤
      (bufferedBallHolderConst alpha C B delta : Real) *
        dist x.1 y.1 ^ (alpha : Real) := by
    obtain ⟨i, hxi⟩ := hcover x.1 x.2
    have hrhalf_pos : 0 < radius i / 2 :=
      lt_of_lt_of_le (by exact_mod_cast hdelta) (hbuffer i)
    have hradius_pos : 0 < radius i := by linarith
    have hxfull : x.1 ∈ Metric.ball (center i) (radius i) := by
      rw [Metric.mem_ball] at hxi ⊢
      exact hxi.trans (half_lt_self hradius_pos)
    by_cases hxy : dist x.1 y.1 < radius i / 2
    · have hyfull : y.1 ∈ Metric.ball (center i) (radius i) := by
        rw [Metric.mem_ball] at hxi ⊢
        calc
          dist y.1 (center i) ≤ dist y.1 x.1 + dist x.1 (center i) :=
            dist_triangle _ _ _
          _ = dist x.1 y.1 + dist x.1 (center i) := by rw [dist_comm y.1 x.1]
          _ < radius i / 2 + radius i / 2 := add_lt_add hxy hxi
          _ = radius i := by ring
      exact (hlocal i).dist_le ⟨x.1, hxfull⟩ ⟨y.1, hyfull⟩ |>.trans
        (mul_le_mul_of_nonneg_right
          (by
            exact_mod_cast
              (show C ≤ bufferedBallHolderConst alpha C B delta by
                exact le_add_of_nonneg_right (zero_le)))
          (Real.rpow_nonneg (dist_nonneg) _))
    · have hdelta_dist : (delta : Real) ≤ dist x.1 y.1 :=
        (hbuffer i).trans (le_of_not_gt hxy)
      have hdelta_pow_pos : 0 < (delta : Real) ^ (alpha : Real) :=
        Real.rpow_pos_of_pos (by exact_mod_cast hdelta) _
      have hrpow : (delta : Real) ^ (alpha : Real) ≤
          dist x.1 y.1 ^ (alpha : Real) :=
        Real.rpow_le_rpow delta.coe_nonneg hdelta_dist alpha.coe_nonneg
      have hdist_f : dist (f x.1) (f y.1) ≤ 2 * (B : Real) := by
        rw [dist_eq_norm]
        exact (norm_sub_le (f x.1) (f y.1)).trans
          ((add_le_add (hbound x.1 x.2) (hbound y.1 y.2)).trans_eq (by ring))
      calc
        dist (f x.1) (f y.1) ≤ 2 * (B : Real) := hdist_f
        _ = (2 * (B : Real) / (delta : Real) ^ (alpha : Real)) *
            (delta : Real) ^ (alpha : Real) := by
              rw [div_mul_cancel₀ _ hdelta_pow_pos.ne']
        _ ≤ (2 * (B : Real) / (delta : Real) ^ (alpha : Real)) *
            dist x.1 y.1 ^ (alpha : Real) :=
              mul_le_mul_of_nonneg_left hrpow (by positivity)
        _ ≤ (bufferedBallHolderConst alpha C B delta : Real) *
            dist x.1 y.1 ^ (alpha : Real) := by
              apply mul_le_mul_of_nonneg_right _
                (Real.rpow_nonneg (dist_nonneg) _)
              simp only [bufferedBallHolderConst, NNReal.coe_add,
                NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat,
                NNReal.coe_rpow]
              exact le_add_of_nonneg_left C.coe_nonneg
  calc
    ENNReal.ofReal (dist (f x.1) (f y.1)) ≤
        ENNReal.ofReal
          ((bufferedBallHolderConst alpha C B delta : Real) *
            dist x.1 y.1 ^ (alpha : Real)) := ENNReal.ofReal_le_ofReal hreal
    _ = (bufferedBallHolderConst alpha C B delta : ENNReal) *
        ENNReal.ofReal (dist x.1 y.1) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_mul (by positivity :
          (0 : Real) ≤ bufferedBallHolderConst alpha C B delta)]
      congr 1
      · exact ENNReal.ofReal_coe_nnreal
      · rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]
    _ = (bufferedBallHolderConst alpha C B delta : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [Subtype.dist_eq]

omit [NormedSpace Real F] [NormedAddCommGroup V] [NormedSpace Real V] in
theorem holderWith_restrict_of_finite_buffered_ball_cover
    {K : Set X} {alpha C B delta : NNReal}
    (hdelta : 0 < delta) (s : Finset X) (radius : X → Real)
    (hbuffer : ∀ x ∈ s, (delta : Real) ≤ radius x / 2)
    (hcover : K ⊆ ⋃ x ∈ s, Metric.ball x (radius x / 2))
    {f : X → F}
    (hlocal : ∀ x ∈ s, HolderWith C alpha
      ((Metric.ball x (radius x)).domRestrict f))
    (hbound : ∀ x ∈ K, ‖f x‖ ≤ B) :
    HolderWith (bufferedBallHolderConst alpha C B delta) alpha
      (K.domRestrict f) := by
  apply holderWith_restrict_of_buffered_ball_cover hdelta
    (fun x : ↥s ↦ x.1) (fun x : ↥s ↦ radius x.1)
  · intro x
    exact hbuffer x.1 x.2
  · intro x hx
    rcases Set.mem_iUnion₂.mp (hcover hx) with ⟨y, hy, hxy⟩
    exact ⟨⟨y, hy⟩, hxy⟩
  · intro x
    exact hlocal x.1 x.2
  · exact hbound

def bufferedParabolicC2HolderGaugeConst
    (alpha C delta : NNReal) : NNReal :=
  4 * C + 2 * bufferedBallHolderConst alpha C C delta

theorem eParabolicC2HolderGaugeOn_le_of_buffered_ball_cover
    {ι : Type*} {Q : Set (ParabolicPoint V)} {alpha C delta : NNReal}
    (hdelta : 0 < delta) (center : ι → ParabolicPoint V)
    (radius : ι → Real)
    (hbuffer : ∀ i, (delta : Real) ≤ radius i / 2)
    (hcover : ∀ q ∈ Q, ∃ i, q ∈ Metric.ball (center i) (radius i / 2))
    (u : Real → V → F)
    (hlocal : ∀ i,
      eParabolicC2HolderGaugeOn alpha
        (Metric.ball (center i) (radius i)) u ≤ C) :
    eParabolicC2HolderGaugeOn alpha Q u ≤
      bufferedParabolicC2HolderGaugeConst alpha C delta := by
  have hhalfFull : ∀ i,
      Metric.ball (center i) (radius i / 2) ⊆
        Metric.ball (center i) (radius i) := by
    intro i q hq
    rw [Metric.mem_ball] at hq ⊢
    have hrhalf_pos : 0 < radius i / 2 :=
      lt_of_lt_of_le (by exact_mod_cast hdelta) (hbuffer i)
    exact hq.trans (half_lt_self (by linarith))
  have hspatialNorm : ∀ j < 3, ∀ q ∈ Q,
      ‖parabolicSpatialJet j u q‖ ≤ C := by
    intro j hj q hq
    obtain ⟨i, hqi⟩ := hcover q hq
    exact parabolicSpatialJet_norm_le (hlocal i)
      (Nat.le_of_lt_succ hj) (hhalfFull i hqi)
  have htimeNorm : ∀ q ∈ Q, ‖parabolicTimeDerivative u q‖ ≤ C := by
    intro q hq
    obtain ⟨i, hqi⟩ := hcover q hq
    exact parabolicTimeDerivative_norm_le (hlocal i) (hhalfFull i hqi)
  have hspatialHolderLocal : ∀ i, HolderWith C alpha
      ((Metric.ball (center i) (radius i)).domRestrict
        (parabolicSpatialJet 2 u)) := by
    intro i
    exact parabolicSpatialJet_holderWith_restrict (hlocal i)
  have htimeHolderLocal : ∀ i, HolderWith C alpha
      ((Metric.ball (center i) (radius i)).domRestrict
        (parabolicTimeDerivative u)) := by
    intro i
    exact parabolicTimeDerivative_holderWith_restrict (hlocal i)
  have hspatialHolder := holderWith_restrict_of_buffered_ball_cover
    hdelta center radius hbuffer hcover hspatialHolderLocal
      (hspatialNorm 2 (by norm_num))
  have htimeHolder := holderWith_restrict_of_buffered_ball_cover
    hdelta center radius hbuffer hcover htimeHolderLocal htimeNorm
  have hspatialSup : ∀ j < 3,
      eSupNormOn Q (parabolicSpatialJet j u) ≤ C := by
    intro j hj
    rw [eSupNormOn_le]
    intro q hq
    exact ENNReal.ofReal_le_coe.mpr (hspatialNorm j hj q hq)
  have htimeSup : eSupNormOn Q (parabolicTimeDerivative u) ≤ C := by
    rw [eSupNormOn_le]
    intro q hq
    exact ENNReal.ofReal_le_coe.mpr (htimeNorm q hq)
  have hspatialSeminorm :
      eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) ≤
        bufferedBallHolderConst alpha C C delta :=
    hspatialHolder.eHolderNorm_le
  have htimeSeminorm :
      eHolderSeminormOn alpha Q (parabolicTimeDerivative u) ≤
        bufferedBallHolderConst alpha C C delta :=
    htimeHolder.eHolderNorm_le
  unfold eParabolicC2HolderGaugeOn bufferedParabolicC2HolderGaugeConst
  calc
    (∑ j ∈ Finset.range 3,
        eSupNormOn Q (parabolicSpatialJet j u)) +
        eSupNormOn Q (parabolicTimeDerivative u) +
        eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) +
        eHolderSeminormOn alpha Q (parabolicTimeDerivative u) ≤
      (∑ _j ∈ Finset.range 3, (C : ENNReal)) + C +
        bufferedBallHolderConst alpha C C delta +
        bufferedBallHolderConst alpha C C delta := by
          gcongr with j hj
          exact hspatialSup j (Finset.mem_range.mp hj)
    _ = (4 * C + 2 * bufferedBallHolderConst alpha C C delta : NNReal) := by
      simp only [Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, Nat.cast_ofNat, ENNReal.coe_add, ENNReal.coe_mul,
        ENNReal.coe_ofNat]
      ring

theorem eParabolicC2HolderGaugeOn_le_of_finite_buffered_ball_cover
    {Q : Set (ParabolicPoint V)} {alpha C delta : NNReal}
    (hdelta : 0 < delta) (s : Finset (ParabolicPoint V))
    (radius : ParabolicPoint V → Real)
    (hbuffer : ∀ p ∈ s, (delta : Real) ≤ radius p / 2)
    (hcover : Q ⊆ ⋃ p ∈ s, Metric.ball p (radius p / 2))
    (u : Real → V → F)
    (hlocal : ∀ p ∈ s,
      eParabolicC2HolderGaugeOn alpha (Metric.ball p (radius p)) u ≤ C) :
    eParabolicC2HolderGaugeOn alpha Q u ≤
      bufferedParabolicC2HolderGaugeConst alpha C delta := by
  apply eParabolicC2HolderGaugeOn_le_of_buffered_ball_cover hdelta
    (fun p : ↥s ↦ p.1) (fun p : ↥s ↦ radius p.1)
  · intro p
    exact hbuffer p.1 p.2
  · intro q hq
    rcases Set.mem_iUnion₂.mp (hcover hq) with ⟨p, hp, hqp⟩
    exact ⟨⟨p, hp⟩, hqp⟩
  · intro p
    exact hlocal p.1 p.2

theorem eParabolicC2HolderGaugeOn_le_of_finite_buffered_ball_cover_sum
    {ι : Type*} {Q : Set (ParabolicPoint V)} {alpha delta : NNReal}
    (hdelta : 0 < delta) (s : Finset ι)
    (center : ι → ParabolicPoint V) (radius : ι → Real)
    (hbuffer : ∀ i ∈ s, (delta : Real) ≤ radius i / 2)
    (hcover : Q ⊆ ⋃ i ∈ s, Metric.ball (center i) (radius i / 2))
    (u : Real → V → F) (localBound : ι → NNReal)
    (hlocal : ∀ i ∈ s,
      eParabolicC2HolderGaugeOn alpha
        (Metric.ball (center i) (radius i)) u ≤ localBound i) :
    eParabolicC2HolderGaugeOn alpha Q u ≤
      bufferedParabolicC2HolderGaugeConst alpha
        (∑ i ∈ s, localBound i) delta := by
  apply eParabolicC2HolderGaugeOn_le_of_buffered_ball_cover hdelta
    (fun i : ↥s ↦ center i.1) (fun i : ↥s ↦ radius i.1)
  · intro i
    exact hbuffer i.1 i.2
  · intro q hq
    rcases Set.mem_iUnion₂.mp (hcover hq) with ⟨i, hi, hqi⟩
    exact ⟨⟨i, hi⟩, hqi⟩
  · intro i
    apply (hlocal i.1 i.2).trans
    exact_mod_cast Finset.single_le_sum
      (fun j _ ↦ zero_le) i.2

theorem eParabolicC2HolderGaugeOn_le_of_finite_buffered_scaledBall_rescaleAt
    {ι : Type*} {Q : Set (ParabolicPoint V)} {alpha delta : NNReal}
    (hdelta : 0 < delta) (s : Finset ι)
    (center : ι → ParabolicPoint V) (scale : ι → NNReal)
    (innerRadius : ι → Real)
    (hscale : ∀ i ∈ s, 0 < scale i)
    (hbuffer : ∀ i ∈ s,
      (delta : Real) ≤ ((scale i : Real) * innerRadius i) / 2)
    (hcover : Q ⊆ ⋃ i ∈ s,
      Metric.ball (center i) (((scale i : Real) * innerRadius i) / 2))
    (u : Real → V → F)
    (hspace : ∀ i ∈ s, ∀ p ∈ Metric.ball (center i)
      ((scale i : Real) * innerRadius i), ContDiff Real 2 (u p.time))
    (localBound : ι → NNReal)
    (hlocal : ∀ i ∈ s,
      eParabolicC2HolderGaugeOn alpha
        (Metric.ball (parabolicPoint 0 0) (innerRadius i))
        (parabolicRescaleAt (scale i) (center i) u) ≤ localBound i) :
    eParabolicC2HolderGaugeOn alpha Q u ≤
      bufferedParabolicC2HolderGaugeConst alpha
        (∑ i ∈ s,
          parabolicC2HolderRescaleConst (scale i)⁻¹ alpha (localBound i))
        delta := by
  apply eParabolicC2HolderGaugeOn_le_of_finite_buffered_ball_cover_sum
    hdelta s center (fun i ↦ (scale i : Real) * innerRadius i)
      hbuffer hcover u
    (fun i ↦ parabolicC2HolderRescaleConst
      (scale i)⁻¹ alpha (localBound i))
  intro i hi
  exact eParabolicC2HolderGaugeOn_scaledBall_le_of_rescaleAt
    (scale i) alpha (localBound i) (hscale i hi) (center i) (innerRadius i)
      u (hspace i hi) (hlocal i hi)

theorem eParabolicC2HolderGaugeOn_le_of_finite_buffered_rescaleAt
    {ι : Type*} {Q : Set (ParabolicPoint V)} {alpha delta : NNReal}
    (hdelta : 0 < delta) (s : Finset ι)
    (center : ι → ParabolicPoint V) (radius : ι → NNReal)
    (hradius : ∀ i ∈ s, 0 < radius i)
    (hbuffer : ∀ i ∈ s, (delta : Real) ≤ (radius i : Real) / 2)
    (hcover : Q ⊆ ⋃ i ∈ s,
      Metric.ball (center i) ((radius i : Real) / 2))
    (u : Real → V → F) (hspace : ∀ t, ContDiff Real 2 (u t))
    (localBound : ι → NNReal)
    (hlocal : ∀ i ∈ s,
      eParabolicC2HolderGaugeOn alpha
        (Metric.ball (parabolicPoint 0 0) 1)
        (parabolicRescaleAt (radius i) (center i) u) ≤ localBound i) :
    eParabolicC2HolderGaugeOn alpha Q u ≤
      bufferedParabolicC2HolderGaugeConst alpha
        (∑ i ∈ s,
          parabolicC2HolderRescaleConst (radius i)⁻¹ alpha (localBound i))
        delta := by
  have hbuffer' : ∀ i ∈ s,
      (delta : Real) ≤ ((radius i : Real) * 1) / 2 := by
    simpa only [mul_one] using hbuffer
  have hcover' : Q ⊆ ⋃ i ∈ s,
      Metric.ball (center i) (((radius i : Real) * 1) / 2) := by
    simpa only [mul_one] using hcover
  simpa only [mul_one] using
    eParabolicC2HolderGaugeOn_le_of_finite_buffered_scaledBall_rescaleAt
      hdelta s center radius (fun _ ↦ 1) hradius hbuffer' hcover'
        u (fun _ _ p _ ↦ hspace p.time) localBound hlocal

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

theorem holderWith_smul_of_eq_zero_outside
    {Q U : Set X} {alpha Kchi Ku Mchi Mu : NNReal}
    (chi : X → Real) (u : X → F)
    (hchi : HolderWith Kchi alpha (Q.domRestrict chi))
    (hu : HolderWith Ku alpha ((Q ∩ U).domRestrict u))
    (hchiNorm : ∀ x, x ∈ Q → x ∈ U → ‖chi x‖ ≤ Mchi)
    (huNorm : ∀ x, x ∈ Q → x ∈ U → ‖u x‖ ≤ Mu)
    (hchiZero : ∀ x, x ∈ Q → x ∉ U → chi x = 0) :
    HolderWith (Mchi * Ku + Mu * Kchi) alpha
      (Q.domRestrict (fun x ↦ chi x • u x)) := by
  intro x y
  rw [edist_dist, edist_dist]
  have hreal : dist (chi x.1 • u x.1) (chi y.1 • u y.1) ≤
      ((Mchi * Ku + Mu * Kchi : NNReal) : Real) *
        dist x y ^ (alpha : Real) := by
    by_cases hxU : x.1 ∈ U
    · by_cases hyU : y.1 ∈ U
      · rw [dist_eq_norm]
        calc
          ‖chi x.1 • u x.1 - chi y.1 • u y.1‖ =
              ‖chi x.1 • (u x.1 - u y.1) +
                (chi x.1 - chi y.1) • u y.1‖ := by
            congr 1
            module
          _ ≤ ‖chi x.1 • (u x.1 - u y.1)‖ +
              ‖(chi x.1 - chi y.1) • u y.1‖ := norm_add_le _ _
          _ ≤ (Mchi : Real) * ((Ku : Real) * dist x y ^ (alpha : Real)) +
              ((Kchi : Real) * dist x y ^ (alpha : Real)) * (Mu : Real) := by
            rw [norm_smul, norm_smul]
            gcongr
            · simpa only [Real.norm_eq_abs] using hchiNorm x.1 x.2 hxU
            · have h := hu.dist_le
                (⟨x.1, ⟨x.2, hxU⟩⟩ : (Q ∩ U : Set X))
                (⟨y.1, ⟨y.2, hyU⟩⟩ : (Q ∩ U : Set X))
              simpa only [Set.domRestrict_apply, Subtype.dist_eq, dist_eq_norm] using h
            · change |chi x.1 - chi y.1| ≤
                (Kchi : Real) * dist x y ^ (alpha : Real)
              simpa only [Set.domRestrict_apply, Real.dist_eq, Subtype.dist_eq] using
                hchi.dist_le x y
            · exact huNorm y.1 y.2 hyU
          _ = ((Mchi * Ku + Mu * Kchi : NNReal) : Real) *
              dist x y ^ (alpha : Real) := by
            push_cast
            ring
      · rw [hchiZero y.1 y.2 hyU, zero_smul, dist_zero_right, norm_smul]
        calc
          ‖chi x.1‖ * ‖u x.1‖ ≤
              ((Kchi : Real) * dist x y ^ (alpha : Real)) * (Mu : Real) := by
            gcongr
            · have hc := hchi.dist_le x y
              simpa only [Set.domRestrict_apply, Real.dist_eq,
                hchiZero y.1 y.2 hyU, sub_zero, Real.norm_eq_abs,
                Subtype.dist_eq] using hc
            · exact huNorm x.1 x.2 hxU
          _ ≤ ((Mchi * Ku + Mu * Kchi : NNReal) : Real) *
              dist x y ^ (alpha : Real) := by
            push_cast
            rw [show (Kchi : Real) * dist x y ^ (alpha : Real) * Mu =
              (Mu * Kchi) * dist x y ^ (alpha : Real) by ring, add_mul]
            exact le_add_of_nonneg_left
              (mul_nonneg (mul_nonneg Mchi.coe_nonneg Ku.coe_nonneg)
                (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist x y) _))
    · rw [hchiZero x.1 x.2 hxU, zero_smul]
      by_cases hyU : y.1 ∈ U
      · rw [dist_zero_left, norm_smul]
        calc
          ‖chi y.1‖ * ‖u y.1‖ ≤
              ((Kchi : Real) * dist x y ^ (alpha : Real)) * (Mu : Real) := by
            gcongr
            · have hc := hchi.dist_le x y
              simpa only [Set.domRestrict_apply, Real.dist_eq,
                hchiZero x.1 x.2 hxU, zero_sub, norm_neg,
                Real.norm_eq_abs, abs_neg, Subtype.dist_eq] using hc
            · exact huNorm y.1 y.2 hyU
          _ ≤ ((Mchi * Ku + Mu * Kchi : NNReal) : Real) *
              dist x y ^ (alpha : Real) := by
            push_cast
            rw [show (Kchi : Real) * dist x y ^ (alpha : Real) * Mu =
              (Mu * Kchi) * dist x y ^ (alpha : Real) by ring, add_mul]
            exact le_add_of_nonneg_left
              (mul_nonneg (mul_nonneg Mchi.coe_nonneg Ku.coe_nonneg)
                (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist x y) _))
      · rw [hchiZero y.1 y.2 hyU, zero_smul, dist_self]
        positivity
  calc
    ENNReal.ofReal (dist (chi x.1 • u x.1) (chi y.1 • u y.1)) ≤
        ENNReal.ofReal (((Mchi * Ku + Mu * Kchi : NNReal) : Real) *
          dist x y ^ (alpha : Real)) := ENNReal.ofReal_le_ofReal hreal
    _ = ((Mchi * Ku + Mu * Kchi : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y ^ (alpha : Real)) := by
      rw [ENNReal.ofReal_mul (by positivity :
        (0 : Real) ≤ ((Mchi * Ku + Mu * Kchi : NNReal) : Real))]
      congr 1
      exact ENNReal.ofReal_coe_nnreal
    _ = ((Mchi * Ku + Mu * Kchi : NNReal) : ENNReal) *
        ENNReal.ofReal (dist x y) ^ (alpha : Real) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) alpha.coe_nonneg]

omit [MetricSpace X] in
theorem norm_smul_le_of_eq_zero_outside
    {Q U : Set X} {Mchi Mu : NNReal}
    (chi : X → Real) (u : X → F)
    (hchiNorm : ∀ x, x ∈ Q → x ∈ U → ‖chi x‖ ≤ Mchi)
    (huNorm : ∀ x, x ∈ Q → x ∈ U → ‖u x‖ ≤ Mu)
    (hchiZero : ∀ x, x ∈ Q → x ∉ U → chi x = 0) :
    ∀ x, x ∈ Q → ‖chi x • u x‖ ≤ Mchi * Mu := by
  intro x hxQ
  by_cases hxU : x ∈ U
  · rw [norm_smul]
    exact mul_le_mul (hchiNorm x hxQ hxU) (huNorm x hxQ hxU)
      (norm_nonneg _) Mchi.coe_nonneg
  · rw [hchiZero x hxQ hxU, zero_smul, norm_zero]
    positivity

def cutoffExtension (chi : X → Real) (f0 : F) (f : X → F) : X → F :=
  fun x ↦ f0 + chi x • (f x - f0)

omit [MetricSpace X] in
@[simp]
theorem cutoffExtension_apply
    (chi : X → Real) (f0 : F) (f : X → F) (x : X) :
    cutoffExtension chi f0 f x = f0 + chi x • (f x - f0) :=
  rfl

omit [MetricSpace X] in
theorem cutoffExtension_eq_of_eq_one
    (chi : X → Real) (f0 : F) (f : X → F) {x : X}
    (hx : chi x = 1) : cutoffExtension chi f0 f x = f x := by
  rw [cutoffExtension_apply, hx, one_smul, add_sub_cancel]

omit [MetricSpace X] in
theorem cutoffExtension_eq_of_eq_zero
    (chi : X → Real) (f0 : F) (f : X → F) {x : X}
    (hx : chi x = 0) : cutoffExtension chi f0 f x = f0 := by
  rw [cutoffExtension_apply, hx, zero_smul, add_zero]

theorem cutoffExtension_holderWith
    {Q U : Set X} {alpha Kchi Kf Mchi Mf : NNReal}
    (chi : X → Real) (f0 : F) (f : X → F)
    (hchi : HolderWith Kchi alpha (Q.domRestrict chi))
    (hf : HolderWith Kf alpha ((Q ∩ U).domRestrict f))
    (hchiNorm : ∀ x, x ∈ Q → x ∈ U → ‖chi x‖ ≤ Mchi)
    (hfNorm : ∀ x, x ∈ Q → x ∈ U → ‖f x‖ ≤ Mf)
    (hchiZero : ∀ x, x ∈ Q → x ∉ U → chi x = 0) :
    HolderWith (Mchi * Kf + (Mf + ‖f0‖₊) * Kchi) alpha
      (Q.domRestrict (cutoffExtension chi f0 f)) := by
  have hdiff : HolderWith Kf alpha
      ((Q ∩ U).domRestrict (fun x ↦ f x - f0)) := by
    intro x y
    simpa only [Set.domRestrict_apply, edist_dist, dist_eq_norm,
      sub_sub_sub_cancel_right] using hf x y
  have hdiffNorm : ∀ x, x ∈ Q → x ∈ U →
      ‖f x - f0‖ ≤ Mf + ‖f0‖₊ := by
    intro x hxQ hxU
    exact (norm_sub_le _ _).trans (add_le_add (hfNorm x hxQ hxU) le_rfl)
  have hproduct := holderWith_smul_of_eq_zero_outside
    (Mu := Mf + ‖f0‖₊)
    chi (fun x ↦ f x - f0) hchi hdiff hchiNorm hdiffNorm hchiZero
  intro x y
  simpa only [cutoffExtension, Set.domRestrict_apply, edist_dist,
    dist_eq_norm, add_sub_add_left_eq_sub] using hproduct x y

omit [MetricSpace X] in
theorem norm_cutoffExtension_le
    {Q U : Set X} {Mchi Mf : NNReal}
    (chi : X → Real) (f0 : F) (f : X → F)
    (hchiNorm : ∀ x, x ∈ Q → x ∈ U → ‖chi x‖ ≤ Mchi)
    (hfNorm : ∀ x, x ∈ Q → x ∈ U → ‖f x‖ ≤ Mf)
    (hchiZero : ∀ x, x ∈ Q → x ∉ U → chi x = 0) :
    ∀ x, x ∈ Q →
      ‖cutoffExtension chi f0 f x‖ ≤
        ‖f0‖₊ + Mchi * (Mf + ‖f0‖₊) := by
  have hdiffNorm : ∀ x, x ∈ Q → x ∈ U →
      ‖f x - f0‖ ≤ Mf + ‖f0‖₊ := by
    intro x hxQ hxU
    exact (norm_sub_le _ _).trans (add_le_add (hfNorm x hxQ hxU) le_rfl)
  have hproduct := norm_smul_le_of_eq_zero_outside
    (Mu := Mf + ‖f0‖₊)
    chi (fun x ↦ f x - f0) hchiNorm hdiffNorm hchiZero
  intro x hxQ
  rw [cutoffExtension_apply]
  exact (norm_add_le _ _).trans
    (add_le_add le_rfl (by simpa using hproduct x hxQ))

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

theorem eHolderSeminormOn_smul_le
    {s : Set X} {alpha C D M N : NNReal}
    {f : X → Real} {g : X → F}
    (hf : HolderWith C alpha (s.domRestrict f))
    (hg : HolderWith D alpha (s.domRestrict g))
    (hfnorm : ∀ x ∈ s, ‖f x‖ ≤ M)
    (hgnorm : ∀ x ∈ s, ‖g x‖ ≤ N) :
    eHolderSeminormOn alpha s (f • g) ≤ M * D + N * C := by
  apply HolderWith.eHolderNorm_le
  have hproduct := holderWith_smul_of_norm_le hf hg
    (fun x ↦ hfnorm x x.2) (fun x ↦ hgnorm x x.2)
  change HolderWith (M * D + N * C) alpha
    (s.domRestrict f • s.domRestrict g)
  exact hproduct

end CalabiYau.Schauder

end
