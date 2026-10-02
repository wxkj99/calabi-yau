-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Holder/Space.lean
-- Locally modified.
module
public import CalabiYau.Analysis.Holder.Basic

@[expose] public section


noncomputable section

open Set
open scoped NNReal

namespace CalabiYau.Schauder

section GaugeAlgebra

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
  [NormedSpace Real F]

omit [MetricSpace X] in
theorem eSupNormOn_smul (s : Set X) (f : X → F) (c : Real) :
    eSupNormOn s (c • f) = (‖c‖₊ : ENNReal) * eSupNormOn s f := by
  unfold eSupNormOn
  simp_rw [Pi.smul_apply, norm_smul, ENNReal.ofReal_mul (norm_nonneg c),
    ofReal_norm, enorm_eq_nnnorm]
  rw [ENNReal.mul_iSup]

theorem eHolderSeminormOn_smul
    (alpha : NNReal) (s : Set X) (f : X → F) (c : Real) :
    eHolderSeminormOn alpha s (c • f) =
      (‖c‖₊ : ENNReal) * eHolderSeminormOn alpha s f := by
  unfold eHolderSeminormOn
  change eHolderNorm alpha (c • s.domRestrict f) = _
  exact eHolderNorm_smul c

end GaugeAlgebra

section BoundedHolder

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]

def eHolderGauge (alpha : NNReal) (f : X → F) : ENNReal :=
  eSupNormOn Set.univ f + eHolderNorm alpha f

theorem eHolderGauge_add_le (alpha : NNReal) (f g : X → F) :
    eHolderGauge alpha (f + g) ≤
      eHolderGauge alpha f + eHolderGauge alpha g := by
  unfold eHolderGauge
  exact (add_le_add (eSupNormOn_add_le Set.univ f g)
    eHolderNorm_add_le).trans_eq (by
      simp only [add_assoc, add_left_comm])

theorem eHolderGauge_smul [NormedSpace Real F]
    (alpha : NNReal) (f : X → F) (c : Real) :
    eHolderGauge alpha (c • f) =
      (‖c‖₊ : ENNReal) * eHolderGauge alpha f := by
  unfold eHolderGauge
  rw [eSupNormOn_smul, eHolderNorm_smul, mul_add]

@[simp]
theorem eHolderGauge_zero (alpha : NNReal) :
    eHolderGauge alpha (0 : X → F) = 0 := by
  simp [eHolderGauge, eSupNormOn]

def IsBoundedHolder (alpha : NNReal) (f : X → F) : Prop :=
  eHolderGauge alpha f ≠ ⊤

namespace IsBoundedHolder

theorem memHolder {alpha : NNReal} {f : X → F}
    (hf : IsBoundedHolder alpha f) :
    MemHolder alpha f := by
  rw [← eHolderNorm_lt_top]
  exact lt_of_le_of_lt (le_add_left le_rfl)
    (lt_top_iff_ne_top.mpr hf)

theorem zero (alpha : NNReal) :
    IsBoundedHolder alpha (0 : X → F) := by
  simp [IsBoundedHolder]

theorem add {alpha : NNReal} {f g : X → F}
    (hf : IsBoundedHolder alpha f) (hg : IsBoundedHolder alpha g) :
    IsBoundedHolder alpha (f + g) := by
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
    (eHolderGauge_add_le alpha f g)

variable [NormedSpace Real F]

theorem smul {alpha : NNReal} {f : X → F}
    (hf : IsBoundedHolder alpha f) (c : Real) :
    IsBoundedHolder alpha (c • f) := by
  rw [IsBoundedHolder, eHolderGauge_smul]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hf

theorem neg {alpha : NNReal} {f : X → F}
    (hf : IsBoundedHolder alpha f) :
    IsBoundedHolder alpha (-f) := by
  simpa only [neg_one_smul] using hf.smul (-1)

theorem sub {alpha : NNReal} {f g : X → F}
    (hf : IsBoundedHolder alpha f) (hg : IsBoundedHolder alpha g) :
    IsBoundedHolder alpha (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end IsBoundedHolder

variable [NormedSpace Real F]

def boundedHolderSubmodule (alpha : NNReal) : Submodule Real (X → F) where
  carrier := {f | IsBoundedHolder alpha f}
  zero_mem' := IsBoundedHolder.zero alpha
  add_mem' := IsBoundedHolder.add
  smul_mem' := fun c _ hf ↦ hf.smul c

@[simp]
theorem mem_boundedHolderSubmodule {alpha : NNReal} {f : X → F} :
    f ∈ boundedHolderSubmodule alpha ↔ IsBoundedHolder alpha f :=
  Iff.rfl

end BoundedHolder

section Elliptic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem eContDiffHolderGaugeOn_smul
    (k : Nat) (alpha : NNReal) (s : Set V) (f : V → F) (c : Real)
    (hf : ∀ x ∈ s, ContDiffAt Real k f x) :
    eContDiffHolderGaugeOn k alpha s (c • f) =
      (‖c‖₊ : ENNReal) * eContDiffHolderGaugeOn k alpha s f := by
  have hjet : ∀ j ≤ k, Set.EqOn
      (iteratedFDeriv Real j (c • f))
      (c • iteratedFDeriv Real j f) s := by
    intro j hj x hx
    exact iteratedFDeriv_const_smul_apply
      ((hf x hx).of_le (by exact_mod_cast hj))
  unfold eContDiffHolderGaugeOn
  calc
    (∑ j ∈ Finset.range (k + 1),
        eSupNormOn s (iteratedFDeriv Real j (c • f))) +
        eHolderSeminormOn alpha s (iteratedFDeriv Real k (c • f)) =
      (∑ j ∈ Finset.range (k + 1),
        eSupNormOn s (c • iteratedFDeriv Real j f)) +
        eHolderSeminormOn alpha s (c • iteratedFDeriv Real k f) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        exact eSupNormOn_congr
          (hjet j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      · exact eHolderSeminormOn_congr (hjet k le_rfl) alpha
    _ = (‖c‖₊ : ENNReal) *
        ((∑ j ∈ Finset.range (k + 1),
          eSupNormOn s (iteratedFDeriv Real j f)) +
          eHolderSeminormOn alpha s (iteratedFDeriv Real k f)) := by
      simp_rw [eSupNormOn_smul, eHolderSeminormOn_smul]
      rw [← Finset.mul_sum, ← mul_add]

@[simp]
theorem eContDiffHolderGaugeOn_zero
    (k : Nat) (alpha : NNReal) (s : Set V) :
    eContDiffHolderGaugeOn k alpha s (0 : V → F) = 0 := by
  have h := eContDiffHolderGaugeOn_smul k alpha s (0 : V → F) 0
    (fun _ _ ↦ contDiffAt_const)
  simpa using h

namespace IsContDiffHolderOn

theorem zero (k : Nat) (alpha : NNReal) (s : Set V) :
    IsContDiffHolderOn k alpha s (0 : V → F) := by
  constructor
  · intro x _
    exact contDiffAt_const
  · have hjet :
        s.domRestrict (iteratedFDeriv Real k (0 : V → F)) = 0 := by
      funext x
      rw [iteratedFDeriv_zero]
      rfl
    rw [hjet]
    exact memHolder_zero

theorem add {k : Nat} {alpha : NNReal} {s : Set V} {f g : V → F}
    (hf : IsContDiffHolderOn k alpha s f)
    (hg : IsContDiffHolderOn k alpha s g) :
    IsContDiffHolderOn k alpha s (f + g) := by
  constructor
  · intro x hx
    exact (hf.1 x hx).add (hg.1 x hx)
  · have hjet :
        s.domRestrict (iteratedFDeriv Real k (f + g)) =
          s.domRestrict (iteratedFDeriv Real k f) +
            s.domRestrict (iteratedFDeriv Real k g) := by
      funext x
      exact iteratedFDeriv_add_apply (hf.1 x x.2) (hg.1 x x.2)
    rw [hjet]
    exact hf.2.add hg.2

theorem smul {k : Nat} {alpha : NNReal} {s : Set V} {f : V → F}
    (hf : IsContDiffHolderOn k alpha s f) (c : Real) :
    IsContDiffHolderOn k alpha s (c • f) := by
  constructor
  · intro x hx
    change ContDiffAt Real k (fun y => c • f y) x
    exact (hf.1 x hx).const_smul c
  · have hjet :
        s.domRestrict (iteratedFDeriv Real k (c • f)) =
          c • s.domRestrict (iteratedFDeriv Real k f) := by
      funext x
      exact iteratedFDeriv_const_smul_apply (hf.1 x x.2)
    rw [hjet]
    exact hf.2.smul

theorem neg {k : Nat} {alpha : NNReal} {s : Set V} {f : V → F}
    (hf : IsContDiffHolderOn k alpha s f) :
    IsContDiffHolderOn k alpha s (-f) := by
  simpa only [neg_one_smul] using hf.smul (-1)

theorem sub {k : Nat} {alpha : NNReal} {s : Set V} {f g : V → F}
    (hf : IsContDiffHolderOn k alpha s f)
    (hg : IsContDiffHolderOn k alpha s g) :
    IsContDiffHolderOn k alpha s (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end IsContDiffHolderOn

def contDiffHolderOnSubmodule (k : Nat) (alpha : NNReal) (s : Set V) :
    Submodule Real (V → F) where
  carrier := {f | IsContDiffHolderOn k alpha s f}
  zero_mem' := IsContDiffHolderOn.zero k alpha s
  add_mem' := IsContDiffHolderOn.add
  smul_mem' := fun c _ hf ↦ hf.smul c

@[simp]
theorem mem_contDiffHolderOnSubmodule {k : Nat} {alpha : NNReal}
    {s : Set V} {f : V → F} :
    f ∈ contDiffHolderOnSubmodule k alpha s ↔
      IsContDiffHolderOn k alpha s f :=
  Iff.rfl

def IsBoundedContDiffHolderOn (k : Nat) (alpha : NNReal)
    (s : Set V) (f : V → F) : Prop :=
  IsContDiffHolderOn k alpha s f ∧
    eContDiffHolderGaugeOn k alpha s f ≠ ⊤

namespace IsBoundedContDiffHolderOn

theorem zero (k : Nat) (alpha : NNReal) (s : Set V) :
    IsBoundedContDiffHolderOn k alpha s (0 : V → F) := by
  exact ⟨IsContDiffHolderOn.zero k alpha s, by simp⟩

theorem add {k : Nat} {alpha : NNReal} {s : Set V} {f g : V → F}
    (hf : IsBoundedContDiffHolderOn k alpha s f)
    (hg : IsBoundedContDiffHolderOn k alpha s g) :
    IsBoundedContDiffHolderOn k alpha s (f + g) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf.2, hg.2⟩)
    (eContDiffHolderGaugeOn_add_le k alpha s f g hf.1.1 hg.1.1)

theorem smul {k : Nat} {alpha : NNReal} {s : Set V} {f : V → F}
    (hf : IsBoundedContDiffHolderOn k alpha s f) (c : Real) :
    IsBoundedContDiffHolderOn k alpha s (c • f) := by
  refine ⟨hf.1.smul c, ?_⟩
  rw [eContDiffHolderGaugeOn_smul k alpha s f c hf.1.1]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hf.2

theorem neg {k : Nat} {alpha : NNReal} {s : Set V} {f : V → F}
    (hf : IsBoundedContDiffHolderOn k alpha s f) :
    IsBoundedContDiffHolderOn k alpha s (-f) := by
  simpa only [neg_one_smul] using hf.smul (-1)

theorem sub {k : Nat} {alpha : NNReal} {s : Set V} {f g : V → F}
    (hf : IsBoundedContDiffHolderOn k alpha s f)
    (hg : IsBoundedContDiffHolderOn k alpha s g) :
    IsBoundedContDiffHolderOn k alpha s (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end IsBoundedContDiffHolderOn

def boundedContDiffHolderOnSubmodule
    (k : Nat) (alpha : NNReal) (s : Set V) : Submodule Real (V → F) where
  carrier := {f | IsBoundedContDiffHolderOn k alpha s f}
  zero_mem' := IsBoundedContDiffHolderOn.zero k alpha s
  add_mem' := IsBoundedContDiffHolderOn.add
  smul_mem' := fun c _ hf ↦ hf.smul c

@[simp]
theorem mem_boundedContDiffHolderOnSubmodule
    {k : Nat} {alpha : NNReal} {s : Set V} {f : V → F} :
    f ∈ boundedContDiffHolderOnSubmodule k alpha s ↔
      IsBoundedContDiffHolderOn k alpha s f :=
  Iff.rfl

end Elliptic

section Parabolic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

theorem parabolicSpatialJet_const_smul
    (j : Nat) (u : Real → V → F) (p : ParabolicPoint V) (c : Real)
    (hu : ContDiffAt Real j (u p.time) p.space) :
    parabolicSpatialJet j (c • u) p = c • parabolicSpatialJet j u p := by
  unfold parabolicSpatialJet
  exact iteratedFDeriv_const_smul_apply hu

omit [NormedAddCommGroup V] [NormedSpace Real V] in
theorem parabolicTimeDerivative_const_smul
    (u : Real → V → F) (p : ParabolicPoint V) (c : Real)
    (hu : DifferentiableAt Real (fun t ↦ u t p.space) p.time) :
    parabolicTimeDerivative (c • u) p =
      c • parabolicTimeDerivative u p := by
  unfold parabolicTimeDerivative
  change (fderiv Real (c • fun t ↦ u t p.space) p.time) 1 = _
  rw [fderiv_const_smul hu c]
  exact smul_apply _ _ _

theorem eParabolicC2HolderGaugeOn_smul
    (alpha : NNReal) (Q : Set (ParabolicPoint V))
    (u : Real → V → F) (c : Real) (hu : IsParabolicC2On Q u) :
    eParabolicC2HolderGaugeOn alpha Q (c • u) =
      (‖c‖₊ : ENNReal) * eParabolicC2HolderGaugeOn alpha Q u := by
  have hspatial : ∀ j ≤ 2, Set.EqOn
      (parabolicSpatialJet j (c • u))
      (c • parabolicSpatialJet j u) Q := by
    intro j hj p hp
    exact parabolicSpatialJet_const_smul j u p c
      ((hu.1 p hp).of_le (by exact_mod_cast hj))
  have htime : Set.EqOn
      (parabolicTimeDerivative (c • u))
      (c • parabolicTimeDerivative u) Q := by
    intro p hp
    exact parabolicTimeDerivative_const_smul u p c (hu.2 p hp)
  have hsum :
      (∑ j ∈ Finset.range 3,
        eSupNormOn Q (parabolicSpatialJet j (c • u))) =
      ∑ j ∈ Finset.range 3,
        eSupNormOn Q (c • parabolicSpatialJet j u) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact eSupNormOn_congr
      (hspatial j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
  have hsupTime :
      eSupNormOn Q (parabolicTimeDerivative (c • u)) =
        eSupNormOn Q (c • parabolicTimeDerivative u) :=
    eSupNormOn_congr htime
  have hholderSpatial :
      eHolderSeminormOn alpha Q (parabolicSpatialJet 2 (c • u)) =
        eHolderSeminormOn alpha Q (c • parabolicSpatialJet 2 u) :=
    eHolderSeminormOn_congr (hspatial 2 le_rfl) alpha
  have hholderTime :
      eHolderSeminormOn alpha Q (parabolicTimeDerivative (c • u)) =
        eHolderSeminormOn alpha Q (c • parabolicTimeDerivative u) :=
    eHolderSeminormOn_congr htime alpha
  unfold eParabolicC2HolderGaugeOn
  calc
    (∑ j ∈ Finset.range 3,
        eSupNormOn Q (parabolicSpatialJet j (c • u))) +
        eSupNormOn Q (parabolicTimeDerivative (c • u)) +
        eHolderSeminormOn alpha Q (parabolicSpatialJet 2 (c • u)) +
        eHolderSeminormOn alpha Q (parabolicTimeDerivative (c • u)) =
      (∑ j ∈ Finset.range 3,
        eSupNormOn Q (c • parabolicSpatialJet j u)) +
        eSupNormOn Q (c • parabolicTimeDerivative u) +
        eHolderSeminormOn alpha Q (c • parabolicSpatialJet 2 u) +
        eHolderSeminormOn alpha Q (c • parabolicTimeDerivative u) := by
      rw [hsum, hsupTime, hholderSpatial, hholderTime]
    _ = (‖c‖₊ : ENNReal) *
        ((∑ j ∈ Finset.range 3,
          eSupNormOn Q (parabolicSpatialJet j u)) +
          eSupNormOn Q (parabolicTimeDerivative u) +
          eHolderSeminormOn alpha Q (parabolicSpatialJet 2 u) +
          eHolderSeminormOn alpha Q (parabolicTimeDerivative u)) := by
      simp_rw [eSupNormOn_smul, eHolderSeminormOn_smul]
      rw [← Finset.mul_sum]
      ring

@[simp]
theorem eParabolicC2HolderGaugeOn_zero
    (alpha : NNReal) (Q : Set (ParabolicPoint V)) :
    eParabolicC2HolderGaugeOn alpha Q (0 : Real → V → F) = 0 := by
  have hreg : IsParabolicC2On Q (0 : Real → V → F) := by
    constructor
    · intro p _
      exact contDiffAt_const
    · intro p _
      exact differentiableAt_const _
  have h := eParabolicC2HolderGaugeOn_smul alpha Q
    (0 : Real → V → F) 0 hreg
  simpa using h

namespace IsParabolicC2On

theorem zero (Q : Set (ParabolicPoint V)) :
    IsParabolicC2On Q (0 : Real → V → F) := by
  constructor
  · intro p _
    exact contDiffAt_const
  · intro p _
    exact differentiableAt_const _

theorem add {Q : Set (ParabolicPoint V)} {u v : Real → V → F}
    (hu : IsParabolicC2On Q u) (hv : IsParabolicC2On Q v) :
    IsParabolicC2On Q (u + v) := by
  constructor
  · intro p hp
    exact (hu.1 p hp).add (hv.1 p hp)
  · intro p hp
    exact (hu.2 p hp).add (hv.2 p hp)

theorem smul {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (hu : IsParabolicC2On Q u) (c : Real) :
    IsParabolicC2On Q (c • u) := by
  constructor
  · intro p hp
    change ContDiffAt Real 2 (fun y => c • u p.time y) p.space
    exact (hu.1 p hp).const_smul c
  · intro p hp
    change DifferentiableAt Real (fun t => c • u t p.space) p.time
    exact (hu.2 p hp).const_smul c

theorem neg {Q : Set (ParabolicPoint V)} {u : Real → V → F}
    (hu : IsParabolicC2On Q u) :
    IsParabolicC2On Q (-u) := by
  simpa only [neg_one_smul] using hu.smul (-1)

theorem sub {Q : Set (ParabolicPoint V)} {u v : Real → V → F}
    (hu : IsParabolicC2On Q u) (hv : IsParabolicC2On Q v) :
    IsParabolicC2On Q (u - v) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

end IsParabolicC2On

namespace IsParabolicC2HolderOn

theorem zero (alpha : NNReal) (Q : Set (ParabolicPoint V)) :
    IsParabolicC2HolderOn alpha Q (0 : Real → V → F) := by
  refine ⟨IsParabolicC2On.zero Q, ?_, ?_⟩
  · have hjet :
        Q.domRestrict (parabolicSpatialJet 2 (0 : Real → V → F)) = 0 := by
      funext p
      unfold parabolicSpatialJet
      change iteratedFDeriv Real 2 (0 : V → F) p.1.space = 0
      rw [iteratedFDeriv_zero]
      rfl
    rw [hjet]
    exact memHolder_zero
  · have htime :
        Q.domRestrict (parabolicTimeDerivative (0 : Real → V → F)) = 0 := by
      funext p
      unfold parabolicTimeDerivative
      change (fderiv Real (0 : Real → F) p.1.time) 1 = 0
      rw [fderiv_zero]
      rfl
    rw [htime]
    exact memHolder_zero

theorem add {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u v : Real → V → F}
    (hu : IsParabolicC2HolderOn alpha Q u)
    (hv : IsParabolicC2HolderOn alpha Q v) :
    IsParabolicC2HolderOn alpha Q (u + v) := by
  refine ⟨hu.1.add hv.1, ?_, ?_⟩
  · have hjet :
        Q.domRestrict (parabolicSpatialJet 2 (u + v)) =
          Q.domRestrict (parabolicSpatialJet 2 u) +
            Q.domRestrict (parabolicSpatialJet 2 v) := by
      funext p
      exact parabolicSpatialJet_add 2 u v p (hu.1.1 p p.2) (hv.1.1 p p.2)
    rw [hjet]
    exact hu.2.1.add hv.2.1
  · have htime :
        Q.domRestrict (parabolicTimeDerivative (u + v)) =
          Q.domRestrict (parabolicTimeDerivative u) +
            Q.domRestrict (parabolicTimeDerivative v) := by
      funext p
      exact parabolicTimeDerivative_add u v p (hu.1.2 p p.2) (hv.1.2 p p.2)
    rw [htime]
    exact hu.2.2.add hv.2.2

theorem smul {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u : Real → V → F}
    (hu : IsParabolicC2HolderOn alpha Q u) (c : Real) :
    IsParabolicC2HolderOn alpha Q (c • u) := by
  refine ⟨hu.1.smul c, ?_, ?_⟩
  · have hjet :
        Q.domRestrict (parabolicSpatialJet 2 (c • u)) =
          c • Q.domRestrict (parabolicSpatialJet 2 u) := by
      funext p
      exact parabolicSpatialJet_const_smul 2 u p c (hu.1.1 p p.2)
    rw [hjet]
    exact hu.2.1.smul
  · have htime :
        Q.domRestrict (parabolicTimeDerivative (c • u)) =
          c • Q.domRestrict (parabolicTimeDerivative u) := by
      funext p
      exact parabolicTimeDerivative_const_smul u p c (hu.1.2 p p.2)
    rw [htime]
    exact hu.2.2.smul

theorem neg {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u : Real → V → F}
    (hu : IsParabolicC2HolderOn alpha Q u) :
    IsParabolicC2HolderOn alpha Q (-u) := by
  simpa only [neg_one_smul] using hu.smul (-1)

theorem sub {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u v : Real → V → F}
    (hu : IsParabolicC2HolderOn alpha Q u)
    (hv : IsParabolicC2HolderOn alpha Q v) :
    IsParabolicC2HolderOn alpha Q (u - v) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

end IsParabolicC2HolderOn

def parabolicC2HolderOnSubmodule (alpha : NNReal)
    (Q : Set (ParabolicPoint V)) : Submodule Real (Real → V → F) where
  carrier := {u | IsParabolicC2HolderOn alpha Q u}
  zero_mem' := IsParabolicC2HolderOn.zero alpha Q
  add_mem' := IsParabolicC2HolderOn.add
  smul_mem' := fun c _ hu ↦ hu.smul c

@[simp]
theorem mem_parabolicC2HolderOnSubmodule {alpha : NNReal}
    {Q : Set (ParabolicPoint V)} {u : Real → V → F} :
    u ∈ parabolicC2HolderOnSubmodule alpha Q ↔
      IsParabolicC2HolderOn alpha Q u :=
  Iff.rfl

def IsBoundedParabolicC2HolderOn (alpha : NNReal)
    (Q : Set (ParabolicPoint V)) (u : Real → V → F) : Prop :=
  IsParabolicC2HolderOn alpha Q u ∧
    eParabolicC2HolderGaugeOn alpha Q u ≠ ⊤

namespace IsBoundedParabolicC2HolderOn

theorem of_isParabolicC2On_of_gauge_ne_top
    {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u : Real → V → F}
    (hu : IsParabolicC2On Q u)
    (hfinite : eParabolicC2HolderGaugeOn alpha Q u ≠ ⊤) :
    IsBoundedParabolicC2HolderOn alpha Q u := by
  have hspatialFinite : eHolderSeminormOn alpha Q
      (parabolicSpatialJet 2 u) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite
      (parabolicSpatialHolderSeminorm_le alpha Q u)
  have htimeFinite : eHolderSeminormOn alpha Q
      (parabolicTimeDerivative u) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite
      (parabolicTimeHolderSeminorm_le alpha Q u)
  have hspatial : MemHolder alpha
      (Q.domRestrict (parabolicSpatialJet 2 u)) := by
    rw [← eHolderNorm_lt_top]
    exact lt_top_iff_ne_top.mpr hspatialFinite
  have htime : MemHolder alpha
      (Q.domRestrict (parabolicTimeDerivative u)) := by
    rw [← eHolderNorm_lt_top]
    exact lt_top_iff_ne_top.mpr htimeFinite
  exact ⟨⟨hu, hspatial, htime⟩, hfinite⟩

theorem mono
    {alpha : NNReal} {Q R : Set (ParabolicPoint V)} (hQR : Q ⊆ R)
    {u : Real → V → F}
    (hu : IsBoundedParabolicC2HolderOn alpha R u) :
    IsBoundedParabolicC2HolderOn alpha Q u := by
  have huQ : IsParabolicC2On Q u :=
    ⟨fun p hp ↦ hu.1.1.1 p (hQR hp),
      fun p hp ↦ hu.1.1.2 p (hQR hp)⟩
  have hfinite : eParabolicC2HolderGaugeOn alpha Q u ≠ ⊤ :=
    ne_top_of_le_ne_top hu.2
      (eParabolicC2HolderGaugeOn_mono hQR alpha u)
  exact of_isParabolicC2On_of_gauge_ne_top huQ hfinite

theorem zero (alpha : NNReal) (Q : Set (ParabolicPoint V)) :
    IsBoundedParabolicC2HolderOn alpha Q (0 : Real → V → F) := by
  exact ⟨IsParabolicC2HolderOn.zero alpha Q, by simp⟩

theorem add {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u v : Real → V → F}
    (hu : IsBoundedParabolicC2HolderOn alpha Q u)
    (hv : IsBoundedParabolicC2HolderOn alpha Q v) :
    IsBoundedParabolicC2HolderOn alpha Q (u + v) := by
  refine ⟨hu.1.add hv.1, ?_⟩
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hu.2, hv.2⟩)
    (eParabolicC2HolderGaugeOn_add_le alpha Q u v hu.1.1 hv.1.1)

theorem smul {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u : Real → V → F}
    (hu : IsBoundedParabolicC2HolderOn alpha Q u) (c : Real) :
    IsBoundedParabolicC2HolderOn alpha Q (c • u) := by
  refine ⟨hu.1.smul c, ?_⟩
  rw [eParabolicC2HolderGaugeOn_smul alpha Q u c hu.1.1]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hu.2

theorem neg {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u : Real → V → F}
    (hu : IsBoundedParabolicC2HolderOn alpha Q u) :
    IsBoundedParabolicC2HolderOn alpha Q (-u) := by
  simpa only [neg_one_smul] using hu.smul (-1)

theorem sub {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u v : Real → V → F}
    (hu : IsBoundedParabolicC2HolderOn alpha Q u)
    (hv : IsBoundedParabolicC2HolderOn alpha Q v) :
    IsBoundedParabolicC2HolderOn alpha Q (u - v) := by
  simpa only [sub_eq_add_neg] using hu.add hv.neg

end IsBoundedParabolicC2HolderOn

def boundedParabolicC2HolderOnSubmodule (alpha : NNReal)
    (Q : Set (ParabolicPoint V)) : Submodule Real (Real → V → F) where
  carrier := {u | IsBoundedParabolicC2HolderOn alpha Q u}
  zero_mem' := IsBoundedParabolicC2HolderOn.zero alpha Q
  add_mem' := IsBoundedParabolicC2HolderOn.add
  smul_mem' := fun c _ hu ↦ hu.smul c

@[simp]
theorem mem_boundedParabolicC2HolderOnSubmodule
    {alpha : NNReal} {Q : Set (ParabolicPoint V)}
    {u : Real → V → F} :
    u ∈ boundedParabolicC2HolderOnSubmodule alpha Q ↔
      IsBoundedParabolicC2HolderOn alpha Q u :=
  Iff.rfl

end Parabolic

end CalabiYau.Schauder
