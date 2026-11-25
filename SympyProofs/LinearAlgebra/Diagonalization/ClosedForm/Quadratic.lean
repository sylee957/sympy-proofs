module

public import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Tactic

/-! # The two principal-radical roots of a monic quadratic -/

@[expose] public section

namespace SympyProofs.Diagonalization

noncomputable def quadraticLabels (b c : ℂ) : Fin 2 → ℂ :=
  let s := (b ^ 2 - 4 * c).sqrt
  ![(-b + s) / 2, (-b - s) / 2]

theorem quadraticLabels_factor (b c x : ℂ) :
    (x - quadraticLabels b c 0) * (x - quadraticLabels b c 1) = x ^ 2 + b * x + c := by
  have hs : (b ^ 2 - 4 * c).sqrt ^ 2 = b ^ 2 - 4 * c := Complex.cpow_nat_inv_pow _ (by decide)
  simp [quadraticLabels]
  linear_combination -hs / 4

noncomputable def quadraticRoots (b c : ℂ) : List ℂ := List.ofFn (quadraticLabels b c)

theorem mem_quadraticRoots (b c x : ℂ) :
    x ∈ quadraticRoots b c ↔ x ^ 2 + b * x + c = 0 := by
  rw [← quadraticLabels_factor, mul_eq_zero]
  simp only [sub_eq_zero]
  simp [quadraticRoots]

end SympyProofs.Diagonalization
