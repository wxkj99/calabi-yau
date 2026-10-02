module

public import CalabiYau.Mathlib.Analysis.Holder.Basic

@[expose] public section

open Filter
open scoped NNReal Topology

namespace CalabiYau.Schauder

/-- A uniform Holder estimate and uniform pointwise bound pass to a locally uniform limit.
This packages the seminorm and zeroth-order parts of a common `C^{2,α}` estimate on a
compact target; compactness is needed by applications to obtain the local uniform convergence,
not by this limit argument itself. -/
theorem holderOnWith_and_norm_le_of_tendstoLocallyUniformlyOn
    {X F ι : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {l : Filter ι} [NeBot l]
    {C α : NNReal} {B : ℝ} {f : ι → X → F} {g : X → F} {s : Set X}
    (hHolder : ∀ i, HolderOnWith C α (f i) s)
    (hBound : ∀ i x, x ∈ s → ‖f i x‖ ≤ B)
    (hLimit : TendstoLocallyUniformlyOn f g l s) :
    HolderOnWith C α g s ∧ ∀ x ∈ s, ‖g x‖ ≤ B := by
  refine ⟨TendstoLocallyUniformlyOn.holderOnWith hLimit (Eventually.of_forall hHolder), ?_⟩
  intro x hx
  have hnorm : Tendsto (fun i => ‖f i x‖) l (𝓝 ‖g x‖) :=
    (hLimit.tendsto_at hx).norm
  exact le_of_tendsto hnorm (Eventually.of_forall fun i => hBound i x hx)

end CalabiYau.Schauder
