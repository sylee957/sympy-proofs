module

public import SympyProofs.Calculus.Antiderivative.Algebra.Gaussian
public import SympyProofs.Calculus.Antiderivative.Spec.IntegerRelations
public import SympyProofs.Calculus.Antiderivative.Proof.Rat

/-! Coordinate proofs for the integer relations and natural root bounds over ℚ(i). -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.WithI

variable {F : Type} [Field F] [DecidableEq F]
variable [Fact (∀ x : F, x ^ 2 ≠ -1 + 0 * x)]
local notation "G" => WithI F

omit [DecidableEq F] in
private theorem coordinates (qs : List ℚ) (xs : List G) :
    (rationalCombination qs xs).re = rationalCombination qs (xs.map QuadraticAlgebra.re) ∧
    (rationalCombination qs xs).im = rationalCombination qs (xs.map QuadraticAlgebra.im) := by
  induction qs generalizing xs with
  | nil => simp [rationalCombination]
  | cons a qs ih =>
    cases xs with
    | nil => simp [rationalCombination]
    | cons b xs =>
      have ⟨h1,h2⟩ := ih xs
      change ((QuadraticAlgebra.C (a : F) * b + rationalCombination qs xs).re = _ ∧
        (QuadraticAlgebra.C (a : F) * b + rationalCombination qs xs).im = _)
      change (QuadraticAlgebra.C (a : F) * b + rationalCombination qs xs).re =
          (a : F) * b.re + rationalCombination qs (xs.map QuadraticAlgebra.re) ∧
        (QuadraticAlgebra.C (a : F) * b + rationalCombination qs xs).im =
          (a : F) * b.im + rationalCombination qs (xs.map QuadraticAlgebra.im)
      simp [h1, h2]

/-- Simultaneous rational relations on the two coordinates characterize zero in ℚ(i). -/
instance [IntegerRelations F] [LawfulIntegerRelations F] : LawfulIntegerRelations G where
  width xs r hr := by
    rcases List.mem_append.mp hr with h | h
    · simpa using LawfulIntegerRelations.width (xs.map QuadraticAlgebra.re) r h
    · simpa using LawfulIntegerRelations.width (xs.map QuadraticAlgebra.im) r h
  kernel xs q := by
    obtain ⟨hr,hi⟩ := coordinates q xs
    change (∀ r ∈ IntegerRelations.rows (xs.map QuadraticAlgebra.re) ++
      IntegerRelations.rows (xs.map QuadraticAlgebra.im), _) ↔ _
    rw [List.forall_mem_append, LawfulIntegerRelations.kernel, LawfulIntegerRelations.kernel,
      ← hr, ← hi]
    exact ⟨fun h => QuadraticAlgebra.ext h.1 h.2, fun h => by simp [h]⟩

omit [DecidableEq F] in
private theorem eval_coordinates (cs : List G) (m : ℕ) :
    (Poly.Raw.eval (m : G) cs).re = Poly.Raw.eval (m : F) (cs.map QuadraticAlgebra.re) ∧
    (Poly.Raw.eval (m : G) cs).im = Poly.Raw.eval (m : F) (cs.map QuadraticAlgebra.im) := by
  induction cs with
  | nil => simp [Poly.Raw.eval]
  | cons a cs ih =>
    simp [Poly.Raw.eval, ih.1, ih.2]

private theorem eval_map_coord (p : Poly G) (m : ℕ) (h : p.eval (m : G) = 0) :
    (p.map QuadraticAlgebra.re).eval (m : F) = 0 ∧
    (p.map QuadraticAlgebra.im).eval (m : F) = 0 := by
  have he := eval_coordinates p.coeffs m
  rw [← Poly.eval_eq_eval_coeffs, h] at he
  have evalMap (f : G → F) : (p.map f).eval (m : F) =
      Poly.Raw.eval (m : F) (p.coeffs.map f) := by
    rw [Poly.eval_eq_eval_coeffs, Poly.coeffs_map]
    exact Poly.Raw.eval_congr _ (Poly.Raw.rel_trim _)
  rw [evalMap, evalMap]
  exact ⟨he.1.symm, he.2.symm⟩

/-- Rational projections bound natural numbers and roots in the G rationals. -/
instance [NatBound F] [LawfulNatBound F] : LawfulNatBound G where
  natBound_spec z m hz := by
    subst z
    apply LawfulNatBound.natBound_spec (m : F) m rfl
  natRootBound_spec p m hp hroot := by
    obtain ⟨hr, hi⟩ := eval_map_coord p m hroot
    change m ≤ NatBound.natRootBound (if p.map QuadraticAlgebra.re = 0 then
      p.map QuadraticAlgebra.im else p.map QuadraticAlgebra.re)
    split
    next h =>
      apply LawfulNatBound.natRootBound_spec _ m _ hi
      intro hi
      apply hp
      apply Poly.ext
      intro j
      have hre := congrArg (fun q : Poly F => q.coeff j) h
      have him := congrArg (fun q : Poly F => q.coeff j) hi
      rw [Poly.coeff_map QuadraticAlgebra.re (by rfl), Poly.coeff_zero] at hre
      rw [Poly.coeff_map QuadraticAlgebra.im (by rfl), Poly.coeff_zero] at him
      rw [Poly.coeff_zero]
      exact QuadraticAlgebra.ext hre him
    next h => exact LawfulNatBound.natRootBound_spec _ m h hr

end SympyProofs.Calculus.Antiderivative.WithI
