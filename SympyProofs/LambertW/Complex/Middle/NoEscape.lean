import SympyProofs.LambertW.Complex.Middle.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Bounds excluding escape to infinity on finite time intervals

A differentiable lift of a bounded-speed path staying away from zero remains
bounded. The comparison argument only uses derivative bounds at large lifted
values, so the lift may enter and leave the radius-two disk.
-/

namespace LambertW.Complex

open Set Filter Topology

/-- A derivative bound outside a disk yields a linear norm bound everywhere.
The extra `1` gives a strict comparison barrier. -/
theorem norm_le_of_large_deriv_bound {F F' : ℝ → ℂ} {a b C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ t ∈ Icc a b, HasDerivAt F (F' t) t)
    (hbound : ∀ t ∈ Ico a b, 2 ≤ ‖F t‖ → ‖F' t‖ ≤ C) :
    ∀ t ∈ Icc a b, ‖F t‖ ≤ max 2 ‖F a‖ + (C + 1) * (t - a) := by
  let B : ℝ → ℝ := fun t => max 2 ‖F a‖ + (C + 1) * (t - a)
  have hB (t : ℝ) : HasDerivAt B (C + 1) t := by
    convert (((hasDerivAt_id t).sub_const a).const_mul (C + 1)).const_add (max 2 ‖F a‖) using 1 <;> simp [B]
  apply image_norm_le_of_norm_deriv_right_lt_deriv_boundary
    (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hF t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (show ‖F a‖ ≤ B a by simp [B]) hB
  intro t ht he
  have hlarge : 2 ≤ ‖F t‖ := by
    rw [he]
    dsimp [B]
    have hp : 0 ≤ (C + 1) * (t - a) := mul_nonneg (by linarith) (sub_nonneg.mpr ht.1)
    exact (le_max_left _ _).trans (le_add_of_nonneg_right hp)
  exact (hbound t ht hlarge).trans_lt (by linarith)

/-- A bounded-speed input staying away from zero gives a uniform bound for
its lift on a closed interval, even across visits to the radius-two disk. -/
theorem norm_path_lift_le {F γ F' γ' : ℝ → ℂ} {a b δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (F' t) t)
    (hγ : ∀ t ∈ Ico a b, HasDerivAt γ (γ' t) t)
    (hi : ∀ t ∈ Ico a b, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s)
    (haway : ∀ t ∈ Ico a b, δ ≤ ‖γ t‖)
    (hspeed : ∀ t ∈ Ico a b, ‖γ' t‖ ≤ M) :
    ∀ t ∈ Icc a b,
      ‖F t‖ ≤ max 2 ‖F a‖ + ((2 / δ) * M + 1) * (t - a) := by
  apply norm_le_of_large_deriv_bound (mul_nonneg (by positivity) hM) hF
  intro t ht hlarge
  exact (norm_path_lift_derivative_le (hF t (Ico_subset_Icc_self ht))
    (hγ t ht) (hi t ht) hδ (haway t ht) hlarge).trans
    (mul_le_mul_of_nonneg_left (hspeed t ht) (by positivity))

/-- In particular, a lift on a half-open finite interval remains bounded up to
its missing endpoint. No finite endpoint limit is assumed. -/
theorem norm_path_lift_le_on_Ico {F γ F' γ' : ℝ → ℂ} {a b δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hF : ∀ t ∈ Ico a b, HasDerivAt F (F' t) t)
    (hγ : ∀ t ∈ Ico a b, HasDerivAt γ (γ' t) t)
    (hi : ∀ t ∈ Ico a b, ∀ᶠ s in 𝓝 t, mulExp (F s) = γ s)
    (haway : ∀ t ∈ Ico a b, δ ≤ ‖γ t‖)
    (hspeed : ∀ t ∈ Ico a b, ‖γ' t‖ ≤ M) :
    ∀ t ∈ Ico a b,
      ‖F t‖ ≤ max 2 ‖F a‖ + ((2 / δ) * M + 1) * (b - a) := by
  intro t ht
  have hsub : Icc a t ⊆ Ico a b := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hsub' : Ico a t ⊆ Ico a b := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hh := norm_path_lift_le hδ hM (fun s hs => hF s (hsub hs))
    (fun s hs => hγ s (hsub' hs)) (fun s hs => hi s (hsub' hs))
    (fun s hs => haway s (hsub' hs)) (fun s hs => hspeed s (hsub' hs)) t ⟨ht.1, le_rfl⟩
  apply hh.trans
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)

end LambertW.Complex
