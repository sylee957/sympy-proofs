module

public import SympyProofs.Calculus.Antiderivative.Proof.Logarithmic.Saturation
public import SympyProofs.Calculus.Antiderivative.Extension.LogPart

/-! Reconstruct saturated logarithmic derivatives from a finite set of rational residues. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Logarithmic

open Polynomial
open scoped Polynomial
open Extension.Residue

variable {F : Type*} [Field F] [CharZero F]
local notation "ι" => algebraMap F[X] (RatFunc F)

/-- A proper fraction with only normal simple poles and rational residues is saturated,
provided that the derivative's linear velocity gives a saturated constant at infinity. -/
theorem saturated_of_residues (δ : Derivation ℤ F[X] F[X])
    (D : Model.Der (RatFunc F)) (compat : ∀ p, D (ι p) = ι (δ p))
    (tw : F) (hw : Saturated D (RatFunc.C tw))
    (lead : ∀ p : F[X], p.Monic → (δ p - C ((p.natDegree : F) * tw) * p).degree < p.degree)
    (A S : F[X]) (hs : Squarefree S) (proper : A.degree < S.degree)
    (normal : ∀ p : F[X], Prime p → p ∣ S → ¬ p ∣ δ p)
    (qs : Finset ℚ) (cover : ∀ p : F[X], Prime p → p ∣ S →
      ∃ q ∈ qs, p ∣ A - C (q : F) * δ S) : Saturated D (ι A / ι S) := by
  classical
  let xs := qs.image (fun q : ℚ => (q : F))
  have res (p : F[X]) (hp : Prime p) (hd : p ∣ S) : ∃ x ∈ xs, p ∣ A - C x * δ S := by
    obtain ⟨r, hr, h⟩ := cover p hp hd
    exact ⟨_, Finset.mem_image_of_mem _ hr, h⟩
  have sum := degree_sum_of_residues δ hs normal xs res
  rw [logPart_identity δ tw lead hs normal proper xs sum, sub_eq_add_neg]
  apply Saturated.add
  · apply saturated_sum
    intro x hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
    have gn := (mgcd_monic (a := A - C (q : F) * δ S) hs.ne_zero).ne_zero
    have h := (saturated_log D (RatFunc.algebraMap_ne_zero gn)).rat_mul q
    change Saturated D (RatFunc.C (q : F) * (ι (δ (resGcd δ A S q)) / _))
    rw [← compat, map_ratCast]
    exact h
  · apply Saturated.neg
    rw [Finset.sum_mul, map_sum]
    apply saturated_sum
    intro x hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
    let d := (resGcd δ A S (q : F)).natDegree
    have h := hw.rat_mul ((d : ℚ) * q)
    change Saturated D (RatFunc.C (((d : F) * q) * tw))
    simpa only [map_mul, map_natCast, map_ratCast, Rat.cast_mul, Rat.cast_natCast] using h

end SympyProofs.Calculus.Antiderivative.Logarithmic
