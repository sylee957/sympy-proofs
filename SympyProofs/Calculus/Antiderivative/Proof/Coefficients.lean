module

public import SympyProofs.Calculus.Antiderivative.Program.Coefficients
public import SympyProofs.Calculus.Antiderivative.Spec.Level
public import SympyProofs.Calculus.Antiderivative.Spec.Split
import Mathlib.Tactic.Ring

/-! Clearing the denominators and testing every generator coefficient preserves all constant
linear relations after extension of the coefficient field. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

/-- Interpret a polynomial in the field below the current generator. -/
noncomputable abbrev Model.coefficientPolynomial (p : Poly (K R n)) : Polynomial (M k n) :=
  (Poly.equiv p).map (val k)

/-- Combine univariate polynomials with arbitrary model constant coefficients. -/
noncomputable def Model.polynomialCombination : List k → List (Poly (K R n)) → Polynomial (M k n)
  | c :: cs, p :: ps => Polynomial.C (Model.C k n c) * Model.coefficientPolynomial k p +
      Model.polynomialCombination cs ps
  | _, _ => 0

/-- Multiplying every input by one polynomial multiplies the combination by it. -/
theorem Model.polynomialCombination_mul (cs : List k) (ps : List (Poly (K R n)))
    (b : Poly (K R n)) :
    Model.polynomialCombination k cs (ps.map (· * b)) =
      Model.polynomialCombination k cs ps * Model.coefficientPolynomial k b := by
  induction cs generalizing ps with
  | nil => simp [Model.polynomialCombination]
  | cons c cs ih =>
    cases ps with
    | nil => simp [Model.polynomialCombination]
    | cons p ps =>
      simp [Model.polynomialCombination, ih, Model.coefficientPolynomial, add_mul, mul_assoc]

/-- A coefficient of a polynomial combination is the combination of the coefficients. -/
theorem Model.polynomialCombination_coeff (cs : List k) (ps : List (Poly (K R n))) (i : ℕ) :
    (Model.polynomialCombination k cs ps).coeff i =
      Model.linearCombination k cs (ps.map (·.coeff i)) := by
  induction cs generalizing ps with
  | nil => simp [Model.polynomialCombination, Model.linearCombination]
  | cons c cs ih => cases ps <;> simp [Model.polynomialCombination, Model.linearCombination, ih]

/-- Coefficients above all the input lengths vanish. -/
theorem Model.polynomialCombination_coeff_high (cs : List k) (ps : List (Poly (K R n))) (i : ℕ)
    (h : ∀ p ∈ ps, p.coeffs.length ≤ i) : (Model.polynomialCombination k cs ps).coeff i = 0 := by
  induction cs generalizing ps with
  | nil => simp [Model.polynomialCombination]
  | cons c cs ih =>
    cases ps with
    | nil => simp [Model.polynomialCombination]
    | cons p ps =>
      have hz : p.coeff i = 0 := by
        rw [← Poly.ofList_coeffs p, Poly.coeff_ofList]
        exact Poly.Raw.coeff_eq_zero_of_length_le (h p List.mem_cons_self)
      simp [Model.polynomialCombination, hz, ih ps (fun a ha => h a (List.mem_cons_of_mem _ ha))]

/-- The coefficient slices test whether the entire polynomial combination vanishes. -/
theorem Model.polynomialCombination_eq_zero (cs : List k) (ps : List (Poly (K R n))) :
    (∀ row ∈ coefficientSlices ps, Model.linearCombination k cs row = 0) ↔
      Model.polynomialCombination k cs ps = 0 := by
  simp only [coefficientSlices, List.mem_map, List.mem_range, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, ← Model.polynomialCombination_coeff]
  constructor
  · intro h
    ext i
    by_cases hi : i < (ps.map fun p => p.coeffs.length).max?.getD 0
    · simpa using h i hi
    · apply (Model.polynomialCombination_coeff_high k cs ps i _).trans (coeff_zero i).symm
      exact fun p hp => le_trans (List.le_max?_getD_of_mem (List.mem_map_of_mem
        (f := fun z : Poly (K R n) => z.coeffs.length) hp))
        (Nat.le_of_not_lt hi)
  · intro h
    simp [h]

/-- A model scalar includes as a constant rational function over the preceding field. -/
theorem Model.stepEquiv_scalar (c : k) : Model.stepEquiv k n (Model.C k (n + 1) c) =
    RatFunc.C (Model.C k n c) := by
  rw [← Model.stepEquiv_include]
  congr 1
  simp [Model.C]

/-- The shared denominator is nonzero and clears every constant combination of the inputs. -/
theorem commonDen_spec (ws : List (K R (n + 1))) :
    let (ps, d) := commonDen ws
    d ≠ 0 ∧ ∀ cs : List k, Model.stepEquiv k n (Model.linearCombination k cs ws) *
      algebraMap (Polynomial (M k n)) _ (Model.coefficientPolynomial k d) =
      algebraMap (Polynomial (M k n)) _ (Model.polynomialCombination k cs ps) := by
  induction ws with
  | nil =>
    exact ⟨one_ne_zero, fun cs => by
      cases cs <;> simp [Model.linearCombination, Model.polynomialCombination]⟩
  | cons x xs ih =>
    generalize hx : x.split = ab
    obtain ⟨a,b⟩ := ab
    generalize hd : commonDen xs = pd
    obtain ⟨ps,d⟩ := pd
    rw [hd] at ih
    dsimp only at ih
    have hn := Prod.mk.inj (val_split k x)
    rw [hx] at hn
    dsimp only at hn
    have hb : b ≠ 0 := by
      intro h
      have := hn.2
      rw [h, map_zero, Polynomial.map_zero] at this
      exact (Model.stepEquiv k n (val k x)).denom_ne_zero this.symm
    have he : Model.stepEquiv k n (val k x) *
        algebraMap (Polynomial (M k n)) _ (Model.coefficientPolynomial k b) =
          algebraMap (Polynomial (M k n)) _ (Model.coefficientPolynomial k a) := by
      rw [Model.coefficientPolynomial, Model.coefficientPolynomial, hn.1, hn.2]
      exact (div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))).mp
        (RatFunc.num_div_denom _) |>.symm
    rw [commonDen, hx, hd]
    refine ⟨mul_ne_zero hb ih.1, ?_⟩
    intro cs
    cases cs with
    | nil => simp [Model.linearCombination, Model.polynomialCombination]
    | cons c cs =>
      simp only [Model.linearCombination, map_add, map_mul, Model.stepEquiv_scalar,
        Model.polynomialCombination, Model.polynomialCombination_mul,
        Model.coefficientPolynomial, Polynomial.map_mul, RatFunc.algebraMap_C]
      linear_combination RatFunc.C (Model.C k n c) *
        algebraMap (Polynomial (M k n)) _ (Model.coefficientPolynomial k d) * he +
        algebraMap (Polynomial (M k n)) _ (Model.coefficientPolynomial k b) * ih.2 cs

/-- Clearing denominators retains one numerator for every input. -/
theorem length_commonDen (ws : List (K R (n + 1))) :
    (commonDen ws).1.length = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [commonDen, ih]

/-- Each coefficient equation has one entry for each of the original field elements. -/
theorem length_rowsOf : ∀ {n : ℕ} (ws : List (K R n)) {row}, row ∈ rowsOf ws →
    row.length = ws.length
  | 0, ws, row, h => congrArg List.length (List.mem_singleton.mp h)
  | n + 1, ws, row, h => by
    obtain ⟨slice, hs, hr⟩ := List.mem_flatMap.mp h
    rw [length_rowsOf slice hr]
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs
    rw [List.length_map, length_commonDen]

/-- The computed rows define exactly the vanishing combinations over every model field. -/
theorem rowsOf_spec : ∀ {n : ℕ} (ws : List (K R n)) (cs : List k),
    (∀ row ∈ rowsOf ws, Model.rowHolds k row cs) ↔ Model.linearCombination k cs ws = 0
  | 0, ws, cs => by simp [rowsOf, Model.rowHolds]
  | n + 1, ws, cs => by
    simp only [rowsOf, List.mem_flatMap, forall_exists_index, and_imp, forall_comm (α := List _),
      rowsOf_spec, Model.polynomialCombination_eq_zero]
    obtain ⟨hd,he⟩ := commonDen_spec k ws
    have hn : algebraMap (Polynomial (M k n)) (RatFunc (M k n))
        (Model.coefficientPolynomial k (commonDen ws).2) ≠ 0 :=
      RatFunc.algebraMap_ne_zero
        ((Polynomial.map_ne_zero_iff (val_injective (R := R) (n := n) k)).mpr
        (fun hz => hd (Poly.equiv.injective (hz.trans (map_zero _).symm))))
    rw [← (map_eq_zero_iff _ (RatFunc.algebraMap_injective _)), ← he, mul_eq_zero, or_iff_left hn,
      EmbeddingLike.map_eq_zero_iff]

end SympyProofs.Calculus.Antiderivative
