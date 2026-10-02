-- Extracted from https://github.com/qinz1yang/differential-geometry.git @ 7a48598d35109aa99d1cc678e2724c213cdf4ff3: DifferentialGeometry/Analysis/Schauder/Holder/NormedSpace.lean
-- Locally modified.
module
public import CalabiYau.Mathlib.Analysis.Holder.Space

@[expose] public section

-- and its private helpers occur in public declarations.

noncomputable section

open Set
open scoped BigOperators NNReal

namespace CalabiYau.Schauder

section BoundedHolder

variable {X F : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace Real F]

def BoundedHolderSpace (alpha : NNReal) : Type _ :=
  ↑(boundedHolderSubmodule (X := X) (F := F) alpha)

instance (alpha : NNReal) :
    AddCommGroup (BoundedHolderSpace (X := X) (F := F) alpha) :=
  inferInstanceAs (AddCommGroup
    ↑(boundedHolderSubmodule (X := X) (F := F) alpha))

instance (alpha : NNReal) :
    Module Real (BoundedHolderSpace (X := X) (F := F) alpha) :=
  inferInstanceAs (Module Real
    ↑(boundedHolderSubmodule (X := X) (F := F) alpha))

def boundedHolderSpaceFun {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) : X → F :=
  f.1

instance {alpha : NNReal} :
    CoeFun (BoundedHolderSpace (X := X) (F := F) alpha)
      (fun _ ↦ X → F) where
  coe := boundedHolderSpaceFun

@[simp]
theorem boundedHolderSpace_zero_apply {alpha : NNReal} (x : X) :
    (0 : BoundedHolderSpace (X := X) (F := F) alpha) x = 0 :=
  rfl

@[simp]
theorem boundedHolderSpace_add_apply {alpha : NNReal}
    (f g : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    (f + g) x = f x + g x :=
  rfl

@[simp]
theorem boundedHolderSpace_neg_apply {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    (-f) x = -f x :=
  rfl

@[simp]
theorem boundedHolderSpace_sub_apply {alpha : NNReal}
    (f g : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    (f - g) x = f x - g x :=
  rfl

@[simp]
theorem boundedHolderSpace_sum_apply {ι : Type*} {alpha : NNReal}
    (s : Finset ι)
    (f : ι → BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

@[ext]
theorem boundedHolderSpace_ext {alpha : NNReal}
    {f g : BoundedHolderSpace (X := X) (F := F) alpha}
    (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  funext x
  exact h x

instance (alpha : NNReal) :
    Norm (BoundedHolderSpace (X := X) (F := F) alpha) where
  norm f := (eHolderGauge alpha f).toReal

theorem boundedHolderSpace_normedSpaceCore (alpha : NNReal) :
    NormedSpace.Core Real
      (BoundedHolderSpace (X := X) (F := F) alpha) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c f := by
    change (eHolderGauge alpha (c • boundedHolderSpaceFun f)).toReal =
      ‖c‖ * (eHolderGauge alpha (boundedHolderSpaceFun f)).toReal
    rw [eHolderGauge_smul, ENNReal.toReal_mul]
    rfl
  norm_triangle f g := by
    change (eHolderGauge alpha
      (boundedHolderSpaceFun f + boundedHolderSpaceFun g)).toReal ≤
        (eHolderGauge alpha (boundedHolderSpaceFun f)).toReal +
          (eHolderGauge alpha (boundedHolderSpaceFun g)).toReal
    have hle := eHolderGauge_add_le alpha
      (boundedHolderSpaceFun f) (boundedHolderSpaceFun g)
    have hfinite : eHolderGauge alpha (boundedHolderSpaceFun f) +
        eHolderGauge alpha (boundedHolderSpaceFun g) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨f.2, g.2⟩
    have hreal := ENNReal.toReal_mono hfinite hle
    exact hreal.trans_eq (ENNReal.toReal_add f.2 g.2)
  norm_eq_zero_iff f := by
    constructor
    · intro hnorm
      have hgauge : eHolderGauge alpha (boundedHolderSpaceFun f) = 0 :=
        (ENNReal.toReal_eq_zero_iff _).mp hnorm |>.resolve_right f.2
      apply Subtype.ext
      funext x
      apply norm_eq_zero.mp
      have hx := norm_le_eSupNormOn Set.univ
        (boundedHolderSpaceFun f) x (Set.mem_univ x)
      have hsup : eSupNormOn Set.univ (boundedHolderSpaceFun f) ≤
          eHolderGauge alpha (boundedHolderSpaceFun f) := by
        unfold eHolderGauge
        exact le_add_right le_rfl
      have hzero : ENNReal.ofReal ‖boundedHolderSpaceFun f x‖ = 0 := by
        exact nonpos_iff_eq_zero.mp (by simpa only [hgauge] using hx.trans hsup)
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp hzero) (norm_nonneg _)
    · intro hf
      rw [hf]
      change (eHolderGauge alpha (0 : X → F)).toReal = 0
      simp

instance (alpha : NNReal) :
    NormedAddCommGroup
      (BoundedHolderSpace (X := X) (F := F) alpha) :=
  NormedAddCommGroup.ofCore
    (boundedHolderSpace_normedSpaceCore (X := X) (F := F) alpha)

instance (alpha : NNReal) :
    NormedSpace Real
      (BoundedHolderSpace (X := X) (F := F) alpha) :=
  NormedSpace.ofCore
    (boundedHolderSpace_normedSpaceCore (X := X) (F := F) alpha)

theorem norm_boundedHolderSpace_eq {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    ‖f‖ = (eHolderGauge alpha (boundedHolderSpaceFun f)).toReal :=
  rfl

theorem eHolderGauge_eq_ofReal_norm {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    eHolderGauge alpha (boundedHolderSpaceFun f) = ENNReal.ofReal ‖f‖ := by
  rw [norm_boundedHolderSpace_eq]
  exact (ENNReal.ofReal_toReal f.2).symm

theorem norm_boundedHolderSpace_apply_le {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) (x : X) :
    ‖f x‖ ≤ ‖f‖ := by
  have hx := norm_le_eSupNormOn Set.univ
    (boundedHolderSpaceFun f) x (Set.mem_univ x)
  have hsup : eSupNormOn Set.univ (boundedHolderSpaceFun f) ≤
      eHolderGauge alpha (boundedHolderSpaceFun f) := by
    unfold eHolderGauge
    exact le_add_right le_rfl
  have hreal := ENNReal.toReal_mono f.2 (hx.trans hsup)
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  change ‖boundedHolderSpaceFun f x‖ ≤
    (eHolderGauge alpha (boundedHolderSpaceFun f)).toReal at hreal
  rw [norm_boundedHolderSpace_eq]
  exact hreal

theorem boundedHolderSpace_holderWith {alpha : NNReal}
    (f : BoundedHolderSpace (X := X) (F := F) alpha) :
    HolderWith ‖f‖₊ alpha (boundedHolderSpaceFun f) := by
  have hle : (nnHolderNorm alpha (boundedHolderSpaceFun f) : ENNReal) ≤
      (‖f‖₊ : ENNReal) := by
    calc
      (nnHolderNorm alpha (boundedHolderSpaceFun f) : ENNReal) ≤
          eHolderNorm alpha (boundedHolderSpaceFun f) :=
        coe_nnHolderNorm_le_eHolderNorm
      _ ≤ eHolderGauge alpha (boundedHolderSpaceFun f) := by
        unfold eHolderGauge
        exact le_add_left le_rfl
      _ = (‖f‖₊ : ENNReal) := by
        rw [eHolderGauge_eq_ofReal_norm]
        simp only [ofReal_norm, enorm_eq_nnnorm]
  exact f.2.memHolder.holderWith.mono (ENNReal.coe_le_coe.mp hle)

end BoundedHolder

section ParabolicHolder

variable {V F : Type*} [MetricSpace V]
  [NormedAddCommGroup F] [NormedSpace Real F]

abbrev ParabolicHolderSpace (alpha : NNReal) : Type _ :=
  BoundedHolderSpace (X := ParabolicPoint V) (F := F) alpha

end ParabolicHolder

section Elliptic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def ContDiffHolderSpace (k : Nat) (alpha : NNReal) : Type _ :=
  ↑(boundedContDiffHolderOnSubmodule (V := V) (F := F)
    k alpha Set.univ)

instance (k : Nat) (alpha : NNReal) :
    AddCommGroup (ContDiffHolderSpace (V := V) (F := F) k alpha) :=
  inferInstanceAs (AddCommGroup
    ↑(boundedContDiffHolderOnSubmodule (V := V) (F := F)
      k alpha Set.univ))

instance (k : Nat) (alpha : NNReal) :
    Module Real (ContDiffHolderSpace (V := V) (F := F) k alpha) :=
  inferInstanceAs (Module Real
    ↑(boundedContDiffHolderOnSubmodule (V := V) (F := F)
      k alpha Set.univ))

def contDiffHolderSpaceFun {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) : V → F :=
  f.1

instance {k : Nat} {alpha : NNReal} :
    CoeFun (ContDiffHolderSpace (V := V) (F := F) k alpha)
      (fun _ ↦ V → F) where
  coe := contDiffHolderSpaceFun

@[simp]
theorem contDiffHolderSpace_zero_apply {k : Nat} {alpha : NNReal} (x : V) :
    (0 : ContDiffHolderSpace (V := V) (F := F) k alpha) x = 0 :=
  rfl

@[simp]
theorem contDiffHolderSpace_add_apply {k : Nat} {alpha : NNReal}
    (f g : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    (f + g) x = f x + g x :=
  rfl

@[simp]
theorem contDiffHolderSpace_neg_apply {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    (-f) x = -f x :=
  rfl

@[simp]
theorem contDiffHolderSpace_sub_apply {k : Nat} {alpha : NNReal}
    (f g : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    (f - g) x = f x - g x :=
  rfl

@[simp]
theorem contDiffHolderSpace_sum_apply {ι : Type*} {k : Nat} {alpha : NNReal}
    (s : Finset ι)
    (f : ι → ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

@[ext]
theorem contDiffHolderSpace_ext {k : Nat} {alpha : NNReal}
    {f g : ContDiffHolderSpace (V := V) (F := F) k alpha}
    (h : ∀ x, f x = g x) : f = g := by
  apply Subtype.ext
  funext x
  exact h x

instance (k : Nat) (alpha : NNReal) :
    Norm (ContDiffHolderSpace (V := V) (F := F) k alpha) where
  norm f := (eContDiffHolderGaugeOn k alpha Set.univ f).toReal

theorem contDiffHolderSpace_normedSpaceCore (k : Nat) (alpha : NNReal) :
    NormedSpace.Core Real
      (ContDiffHolderSpace (V := V) (F := F) k alpha) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c f := by
    change (eContDiffHolderGaugeOn k alpha Set.univ
      (c • contDiffHolderSpaceFun f)).toReal =
        ‖c‖ * (eContDiffHolderGaugeOn k alpha Set.univ
          (contDiffHolderSpaceFun f)).toReal
    rw [eContDiffHolderGaugeOn_smul k alpha Set.univ
      (contDiffHolderSpaceFun f) c f.2.1.1, ENNReal.toReal_mul]
    rfl
  norm_triangle f g := by
    change (eContDiffHolderGaugeOn k alpha Set.univ
      (contDiffHolderSpaceFun f + contDiffHolderSpaceFun g)).toReal ≤
        (eContDiffHolderGaugeOn k alpha Set.univ
          (contDiffHolderSpaceFun f)).toReal +
        (eContDiffHolderGaugeOn k alpha Set.univ
          (contDiffHolderSpaceFun g)).toReal
    have hle := eContDiffHolderGaugeOn_add_le k alpha Set.univ
      (contDiffHolderSpaceFun f) (contDiffHolderSpaceFun g)
      f.2.1.1 g.2.1.1
    have hfinite :
        eContDiffHolderGaugeOn k alpha Set.univ (contDiffHolderSpaceFun f) +
          eContDiffHolderGaugeOn k alpha Set.univ (contDiffHolderSpaceFun g) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨f.2.2, g.2.2⟩
    have hreal := ENNReal.toReal_mono hfinite hle
    exact hreal.trans_eq (ENNReal.toReal_add f.2.2 g.2.2)
  norm_eq_zero_iff f := by
    constructor
    · intro hnorm
      have hgauge :
          eContDiffHolderGaugeOn k alpha Set.univ
            (contDiffHolderSpaceFun f) = 0 :=
        (ENNReal.toReal_eq_zero_iff _).mp hnorm |>.resolve_right f.2.2
      apply Subtype.ext
      funext x
      apply norm_eq_zero.mp
      have hx := spatialJet_le_eContDiffHolderGaugeOn k alpha Set.univ
        (contDiffHolderSpaceFun f) (j := 0) (Nat.zero_le k) x (Set.mem_univ x)
      rw [hgauge] at hx
      have hzero :
          ‖iteratedFDeriv Real 0 (contDiffHolderSpaceFun f) x‖ = 0 := by
        apply le_antisymm
        · exact ENNReal.ofReal_eq_zero.mp (nonpos_iff_eq_zero.mp hx)
        · exact norm_nonneg _
      change ‖contDiffHolderSpaceFun f x‖ = 0
      simpa only [norm_iteratedFDeriv_zero] using hzero
    · intro hf
      rw [hf]
      change (eContDiffHolderGaugeOn k alpha Set.univ (0 : V → F)).toReal = 0
      simp

instance (k : Nat) (alpha : NNReal) :
    NormedAddCommGroup
      (ContDiffHolderSpace (V := V) (F := F) k alpha) :=
  NormedAddCommGroup.ofCore
    (contDiffHolderSpace_normedSpaceCore (V := V) (F := F) k alpha)

instance (k : Nat) (alpha : NNReal) :
    NormedSpace Real
      (ContDiffHolderSpace (V := V) (F := F) k alpha) :=
  NormedSpace.ofCore
    (contDiffHolderSpace_normedSpaceCore (V := V) (F := F) k alpha)

theorem norm_contDiffHolderSpace_eq {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) :
    ‖f‖ = (eContDiffHolderGaugeOn k alpha Set.univ
      (contDiffHolderSpaceFun f)).toReal :=
  rfl

theorem contDiffHolderSpace_iteratedFDeriv_norm_le
    {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha)
    {j : Nat} (hj : j ≤ k) (x : V) :
    ‖iteratedFDeriv Real j (contDiffHolderSpaceFun f) x‖ ≤ ‖f‖ := by
  have hle := spatialJet_le_eContDiffHolderGaugeOn k alpha Set.univ
    (contDiffHolderSpaceFun f) (j := j) hj x (Set.mem_univ x)
  have hreal := ENNReal.toReal_mono f.2.2 hle
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  change ‖iteratedFDeriv Real j (contDiffHolderSpaceFun f) x‖ ≤
    (eContDiffHolderGaugeOn k alpha Set.univ (contDiffHolderSpaceFun f)).toReal at hreal
  rw [norm_contDiffHolderSpace_eq]
  exact hreal

theorem norm_contDiffHolderSpace_apply_le {k : Nat} {alpha : NNReal}
    (f : ContDiffHolderSpace (V := V) (F := F) k alpha) (x : V) :
    ‖f x‖ ≤ ‖f‖ := by
  simpa only [norm_iteratedFDeriv_zero] using
    contDiffHolderSpace_iteratedFDeriv_norm_le f (Nat.zero_le k) x

end Elliptic

section Parabolic

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [NormedAddCommGroup F] [NormedSpace Real F]

def ParabolicC2HolderSpace (alpha : NNReal) : Type _ :=
  ↑(boundedParabolicC2HolderOnSubmodule (V := V) (F := F)
    alpha Set.univ)

instance (alpha : NNReal) :
    AddCommGroup (ParabolicC2HolderSpace (V := V) (F := F) alpha) :=
  inferInstanceAs (AddCommGroup
    ↑(boundedParabolicC2HolderOnSubmodule (V := V) (F := F)
      alpha Set.univ))

instance (alpha : NNReal) :
    Module Real (ParabolicC2HolderSpace (V := V) (F := F) alpha) :=
  inferInstanceAs (Module Real
    ↑(boundedParabolicC2HolderOnSubmodule (V := V) (F := F)
      alpha Set.univ))

def parabolicC2HolderSpaceFun {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    Real → V → F :=
  u.1

instance {alpha : NNReal} :
    CoeFun (ParabolicC2HolderSpace (V := V) (F := F) alpha)
      (fun _ ↦ Real → V → F) where
  coe := parabolicC2HolderSpaceFun

@[simp]
theorem parabolicC2HolderSpace_zero_apply {alpha : NNReal}
    (t : Real) (x : V) :
    (0 : ParabolicC2HolderSpace (V := V) (F := F) alpha) t x = 0 :=
  rfl

@[simp]
theorem parabolicC2HolderSpace_add_apply {alpha : NNReal}
    (u v : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (t : Real) (x : V) :
    (u + v) t x = u t x + v t x :=
  rfl

@[simp]
theorem parabolicC2HolderSpace_neg_apply {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (t : Real) (x : V) :
    (-u) t x = -u t x :=
  rfl

@[simp]
theorem parabolicC2HolderSpace_sub_apply {alpha : NNReal}
    (u v : ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (t : Real) (x : V) :
    (u - v) t x = u t x - v t x :=
  rfl

@[simp]
theorem parabolicC2HolderSpace_sum_apply
    {ι : Type*} {alpha : NNReal} (s : Finset ι)
    (u : ι → ParabolicC2HolderSpace (V := V) (F := F) alpha)
    (t : Real) (x : V) :
    (∑ i ∈ s, u i) t x = ∑ i ∈ s, u i t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

@[ext]
theorem parabolicC2HolderSpace_ext {alpha : NNReal}
    {u v : ParabolicC2HolderSpace (V := V) (F := F) alpha}
    (h : ∀ t x, u t x = v t x) : u = v := by
  apply Subtype.ext
  funext t x
  exact h t x

instance (alpha : NNReal) :
    Norm (ParabolicC2HolderSpace (V := V) (F := F) alpha) where
  norm u := (eParabolicC2HolderGaugeOn alpha Set.univ u).toReal

theorem parabolicC2HolderSpace_normedSpaceCore (alpha : NNReal) :
    NormedSpace.Core Real
      (ParabolicC2HolderSpace (V := V) (F := F) alpha) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c u := by
    change (eParabolicC2HolderGaugeOn alpha Set.univ
      (c • parabolicC2HolderSpaceFun u)).toReal =
        ‖c‖ * (eParabolicC2HolderGaugeOn alpha Set.univ
          (parabolicC2HolderSpaceFun u)).toReal
    rw [eParabolicC2HolderGaugeOn_smul alpha Set.univ
      (parabolicC2HolderSpaceFun u) c u.2.1.1, ENNReal.toReal_mul]
    rfl
  norm_triangle u v := by
    change (eParabolicC2HolderGaugeOn alpha Set.univ
      (parabolicC2HolderSpaceFun u + parabolicC2HolderSpaceFun v)).toReal ≤
        (eParabolicC2HolderGaugeOn alpha Set.univ
          (parabolicC2HolderSpaceFun u)).toReal +
        (eParabolicC2HolderGaugeOn alpha Set.univ
          (parabolicC2HolderSpaceFun v)).toReal
    have hle := eParabolicC2HolderGaugeOn_add_le alpha Set.univ
      (parabolicC2HolderSpaceFun u) (parabolicC2HolderSpaceFun v)
      u.2.1.1 v.2.1.1
    have hfinite :
        eParabolicC2HolderGaugeOn alpha Set.univ (parabolicC2HolderSpaceFun u) +
          eParabolicC2HolderGaugeOn alpha Set.univ
            (parabolicC2HolderSpaceFun v) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨u.2.2, v.2.2⟩
    have hreal := ENNReal.toReal_mono hfinite hle
    exact hreal.trans_eq (ENNReal.toReal_add u.2.2 v.2.2)
  norm_eq_zero_iff u := by
    constructor
    · intro hnorm
      have hgauge :
          eParabolicC2HolderGaugeOn alpha Set.univ
            (parabolicC2HolderSpaceFun u) = 0 :=
        (ENNReal.toReal_eq_zero_iff _).mp hnorm |>.resolve_right u.2.2
      apply Subtype.ext
      funext t x
      apply norm_eq_zero.mp
      have hjet := parabolicSpatialJet_le alpha Set.univ
        (parabolicC2HolderSpaceFun u) (j := 0) (by omega)
        (parabolicPoint t x) (Set.mem_univ _)
      rw [hgauge] at hjet
      have hzero :
          ‖parabolicSpatialJet 0 (parabolicC2HolderSpaceFun u)
            (parabolicPoint t x)‖ = 0 := by
        apply le_antisymm
        · exact ENNReal.ofReal_eq_zero.mp (nonpos_iff_eq_zero.mp hjet)
        · exact norm_nonneg _
      change ‖parabolicC2HolderSpaceFun u t x‖ = 0
      simpa only [parabolicSpatialJet, parabolicPoint_time,
        parabolicPoint_space, norm_iteratedFDeriv_zero] using hzero
    · intro hu
      rw [hu]
      change (eParabolicC2HolderGaugeOn alpha Set.univ
        (0 : Real → V → F)).toReal = 0
      simp

instance (alpha : NNReal) :
    NormedAddCommGroup
      (ParabolicC2HolderSpace (V := V) (F := F) alpha) :=
  NormedAddCommGroup.ofCore
    (parabolicC2HolderSpace_normedSpaceCore (V := V) (F := F) alpha)

instance (alpha : NNReal) :
    NormedSpace Real
      (ParabolicC2HolderSpace (V := V) (F := F) alpha) :=
  NormedSpace.ofCore
    (parabolicC2HolderSpace_normedSpaceCore (V := V) (F := F) alpha)

theorem norm_parabolicC2HolderSpace_eq {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    ‖u‖ = (eParabolicC2HolderGaugeOn alpha Set.univ
      (parabolicC2HolderSpaceFun u)).toReal :=
  rfl

theorem eParabolicC2HolderGaugeOn_eq_ofReal_norm {alpha : NNReal}
    (u : ParabolicC2HolderSpace (V := V) (F := F) alpha) :
    eParabolicC2HolderGaugeOn alpha Set.univ
      (parabolicC2HolderSpaceFun u) = ENNReal.ofReal ‖u‖ := by
  rw [norm_parabolicC2HolderSpace_eq]
  exact (ENNReal.ofReal_toReal u.2.2).symm

end Parabolic

end CalabiYau.Schauder
