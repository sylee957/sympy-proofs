module

public import SympyProofs.Calculus.Risch.Program.Residue
public import SympyProofs.Calculus.Risch.Proof.Resultant
public import SympyProofs.Calculus.Risch.Algebra.HermiteLemmas
import Mathlib.Tactic.Ring

/-! The constant roots of a polynomial over the field of a tower. The coefficients of the
polynomial are put over one denominator, and the coefficients of each monomial in the
generators form a polynomial with rational coefficients, a slice. Because the generators are
algebraically independent over the constants, a constant is a root of the polynomial exactly
when it is a root of every slice, that is, of their greatest common divisor. `constRoots`
returns the squarefree part of that divisor: a squarefree polynomial with rational
coefficients whose roots in the constant field are the constant roots of the polynomial. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Residue

open Polynomial MPoly Linear

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

/-! ### Slices -/

/-- The list `x, x c, x c², …` of length `m`. -/
private def pows (c x : k) : ℕ → List k
  | 0 => []
  | m + 1 => x :: pows c (c * x) m

private theorem linComb_pows (c : k) : ∀ (R : Poly n) (m : ℕ) (x : k), R.length ≤ m →
    linComb (pows c x m) R = constHom k n x * (Poly.model k R).eval (constHom k n c)
  | [], m, x, _ => by rw [linComb_nil_right, Poly.model_nil, eval_zero, mul_zero]
  | a :: R, 0, x, h => by simp at h
  | a :: R, m + 1, x, h => by
    rw [pows, linComb_cons, linComb_pows c R m (c * x) (by simpa using h), Poly.model_cons,
      eval_add, eval_mul, eval_C, eval_X, map_mul]
    ring

private theorem dotK_pows (c : k) : ∀ (qs : List ℚ) (m : ℕ) (x : k), qs.length ≤ m →
    dotK qs (pows c x m) = x * (Poly.model k (qs.map Term.const : Poly 0)).eval c
  | [], m, x, _ => by simp [dotK, Poly.model_nil]
  | q :: qs, 0, x, h => by simp at h
  | q :: qs, m + 1, x, h => by
    have ih := dotK_pows c qs m (c * x) (by simpa using h)
    change (q : k) * x + dotK qs (pows c (c * x) m) = _
    rw [ih, List.map_cons, Poly.model_cons, eval_add, eval_mul, eval_C, eval_X,
      Term.value_const]
    change _ = x * ((q : k) + c * _)
    ring

private theorem length_numerators : ∀ as : List (Term n), (numerators as).1.length = as.length
  | [] => rfl
  | a :: as => by simp [numerators, length_numerators as]

/-- A constant is a root of a polynomial over the field of a tower exactly when it is a root
of every rational slice of the numerators of its coefficients. -/
theorem isRoot_iff_slices {R : Poly n} (hR : Poly.Defined k R) (c : k) :
    (Poly.model k R).IsRoot (constHom k n c) ↔
      ∀ μ ∈ monomials (numerators R).1,
        (Poly.model k
          (((numerators R).1.map fun w => Term.const (MPoly.coeff μ w)) : Poly 0)).IsRoot c := by
  have key := rowsOf_spec hR (pows c 1 R.length)
  rw [linComb_pows c R R.length 1 le_rfl, map_one, one_mul] at key
  rw [IsRoot.def, ← key]
  constructor
  · intro h μ hμ
    have := h _ (List.mem_map.mpr ⟨μ, hμ, rfl⟩)
    rw [dotK_pows c _ _ 1 (by simp [length_numerators]), one_mul, List.map_map] at this
    exact this
  · intro h row hrow
    obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hrow
    rw [dotK_pows c _ _ 1 (by simp [length_numerators]), one_mul, List.map_map]
    exact h μ hμ

/-! ### The greatest common divisor of a list -/

/-- Folding the greatest common divisor over a list of polynomials gives a common divisor of
the starting polynomial and of the list that vanishes at their common roots. -/
theorem foldGcd_spec : ∀ (ss : List (Poly n)) {g : Poly n}, Poly.Defined k g →
    (∀ s ∈ ss, Poly.Defined k s) →
    Poly.Defined k (ss.foldl (fun g s => Poly.trim (Poly.norm (Poly.gcd g s).1)) g) ∧
      Poly.model k (ss.foldl (fun g s => Poly.trim (Poly.norm (Poly.gcd g s).1)) g) ∣
        Poly.model k g ∧
      (∀ s ∈ ss, Poly.model k (ss.foldl (fun g s => Poly.trim (Poly.norm (Poly.gcd g s).1)) g) ∣
        Poly.model k s) ∧
      ∀ x : K k n, (Poly.model k g).IsRoot x → (∀ s ∈ ss, (Poly.model k s).IsRoot x) →
        (Poly.model k
          (ss.foldl (fun g s => Poly.trim (Poly.norm (Poly.gcd g s).1)) g)).IsRoot x
  | [], g, hg, _ => ⟨hg, dvd_rfl, by simp, fun _ h _ => h⟩
  | s :: ss, g, hg, hs => by
    have ds := hs s List.mem_cons_self
    obtain ⟨dg, -, -, bez, ga, gb⟩ := Poly.gcd_spec hg ds
    obtain ⟨mt, dt, -, -⟩ := Poly.trim_spec (Poly.defined_norm dg)
    rw [Poly.model_norm dg] at mt
    obtain ⟨d, dvg, dvs, root⟩ :=
      foldGcd_spec ss dt fun e he => hs e (List.mem_cons_of_mem _ he)
    rw [mt] at dvg root
    refine ⟨d, dvg.trans ga, fun e he => ?_, fun x hx hall => ?_⟩
    · rcases List.mem_cons.mp he with rfl | he
      · exact dvg.trans gb
      · exact dvs e he
    · refine root x ?_ fun e he => hall e (List.mem_cons_of_mem _ he)
      have hsx := hall s List.mem_cons_self
      rw [IsRoot.def] at hx hsx ⊢
      rw [← bez, eval_add, eval_mul, eval_mul, hx, hsx, mul_zero, mul_zero, add_zero]

/-! ### The squarefree part -/

/-- The quotient of a nonzero polynomial by a greatest common divisor with its derivative is
defined, not zero and squarefree; it divides the polynomial and has the same prime
factors. -/
theorem squarefreePart_spec {g : Poly n} (hg : Poly.Defined k g) (nz : Poly.model k g ≠ 0) :
    Poly.Normal k (Poly.trim (Poly.norm
        (Poly.quot g (Poly.trim (Poly.norm (Poly.gcd g (Poly.formalD g)).1))))) ∧
    Poly.Defined k (Poly.trim (Poly.norm
        (Poly.quot g (Poly.trim (Poly.norm (Poly.gcd g (Poly.formalD g)).1))))) ∧
      Poly.model k (Poly.trim (Poly.norm
        (Poly.quot g (Poly.trim (Poly.norm (Poly.gcd g (Poly.formalD g)).1))))) ≠ 0 ∧
      Squarefree (Poly.model k (Poly.trim (Poly.norm
        (Poly.quot g (Poly.trim (Poly.norm (Poly.gcd g (Poly.formalD g)).1)))))) ∧
      Poly.model k (Poly.trim (Poly.norm
        (Poly.quot g (Poly.trim (Poly.norm (Poly.gcd g (Poly.formalD g)).1))))) ∣
        Poly.model k g ∧
      ∀ p : (K k n)[X], Prime p → p ∣ Poly.model k g →
        p ∣ Poly.model k (Poly.trim (Poly.norm
          (Poly.quot g (Poly.trim (Poly.norm (Poly.gcd g (Poly.formalD g)).1))))) := by
  obtain ⟨dG, -, -, bez, ga, gb⟩ := Poly.gcd_spec hg (Poly.defined_formalD hg)
  rw [Poly.model_formalD] at bez gb
  obtain ⟨mt, dt, nrm, -⟩ := Poly.trim_spec (Poly.defined_norm dG)
  rw [Poly.model_norm dG] at mt
  have G0 : Poly.model k (Poly.gcd g (Poly.formalD g)).1 ≠ 0 := fun z =>
    nz (zero_dvd_iff.mp (z ▸ ga))
  have nG : Poly.Normal k (Poly.trim (Poly.norm (Poly.gcd g (Poly.formalD g)).1)) :=
    nrm.resolve_left fun h => G0 (by rw [← mt, h, Poly.model_nil])
  have hq := Poly.quot_of_dvd hg dt nG (by rw [mt]; exact ga)
  rw [mt] at hq
  have dq := (Poly.rem_spec hg dt nG).2.1
  obtain ⟨mr, dr, nr, -⟩ := Poly.trim_spec (Poly.defined_norm dq)
  rw [Poly.model_norm dq] at mr
  rw [mr]
  refine ⟨nr.resolve_left fun h => nz (by rw [hq, ← mr, h, Poly.model_nil, mul_zero]),
    dr, fun z => nz (by rw [hq, z, mul_zero]), Hermite.squarefree_of_gcd nz hq bez,
    Dvd.intro_left _ hq.symm, fun p hp h => Hermite.prime_dvd_of_gcd nz hq gb hp h⟩

/-! ### The constant roots -/

/-- `constRoots R` is a squarefree polynomial with rational coefficients, written without
vanishing leading coefficient, whose roots in the constant field are the constants that are
roots of `R`. -/
theorem constRoots_spec {R : Poly n} (hR : Poly.Defined k R) (nz : Poly.model k R ≠ 0) :
    Poly.Defined k (constRoots R) ∧ Poly.Normal k (constRoots R) ∧
      Squarefree (Poly.model k (constRoots R)) ∧
      ∀ c : k, (Poly.model k (constRoots R)).IsRoot c ↔
        (Poly.model k R).IsRoot (constHom k n c) := by
  have dsl : ∀ s ∈ (monomials (numerators R).1).map
      (fun μ => (numerators R).1.map fun w => (Term.const (MPoly.coeff μ w) : Term 0)),
      Poly.Defined k s := by
    intro s hs e he
    obtain ⟨μ, -, rfl⟩ := List.mem_map.mp hs
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp he
    trivial
  obtain ⟨dg, -, gs, groot⟩ := foldGcd_spec (k := k) _ Poly.defined_nil dsl
  have g0 : Poly.model k (((monomials (numerators R).1).map
      (fun μ => (numerators R).1.map fun w => (Term.const (MPoly.coeff μ w) : Term 0))).foldl
        (fun g s => Poly.trim (Poly.norm (Poly.gcd g s).1)) []) ≠ 0 := by
    intro z
    apply nz
    apply eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun q : ℚ => constHom k n (q : k))
      ((constHom k n).injective.comp Rat.cast_injective) fun q => ?_
    apply (isRoot_iff_slices hR _).mpr
    intro μ hμ
    have := gs _ (List.mem_map.mpr ⟨μ, hμ, rfl⟩)
    rw [z, zero_dvd_iff] at this
    rw [this, IsRoot.def, eval_zero]
  obtain ⟨nr, dr, -, sq, rg, rp⟩ := squarefreePart_spec dg g0
  refine ⟨dr, nr, sq, fun c => ?_⟩
  rw [isRoot_iff_slices hR c]
  constructor
  · intro h μ hμ
    exact (IsRoot.dvd h rg).dvd (gs _ (List.mem_map.mpr ⟨μ, hμ, rfl⟩))
  · intro h
    have gr := groot c (by rw [Poly.model_nil, IsRoot.def, eval_zero]) fun s hs => by
      obtain ⟨μ, hμ, rfl⟩ := List.mem_map.mp hs
      exact h μ hμ
    exact dvd_iff_isRoot.mp (rp _ (prime_X_sub_C c) (dvd_iff_isRoot.mpr gr))

/-! ### Lifting to the field of the tower -/

/-- The value of a constant of depth zero, as a constant of depth `n`. -/
theorem value_const_evalRat (e : Term 0) :
    Term.value k (Term.const e.evalRat : Term n) = constHom k n (Term.value k e) := by
  rw [Term.value_const, ← Term.value_evalRat, constHom_ratCast]

/-- A polynomial of depth zero, with its coefficients as constants of depth `n`, denotes the
image of the polynomial under the embedding of the constants. -/
theorem model_lift (p : Poly 0) :
    Poly.model k (p.map fun c => (Term.const c.evalRat : Term n)) =
      (Poly.model k p).map (constHom k n) := by
  induction p with
  | nil => rw [List.map_nil, Poly.model_nil, Poly.model_nil, Polynomial.map_zero]
  | cons c p ih =>
    rw [List.map_cons, Poly.model_cons, Poly.model_cons, ih, value_const_evalRat,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]

/-- A polynomial of depth zero, with its coefficients as constants of depth `n`, is
defined. -/
theorem defined_lift (p : Poly 0) :
    Poly.Defined k (p.map fun c => (Term.const c.evalRat : Term n)) := by
  intro e he
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp he
  trivial

end SympyProofs.Calculus.Risch.Residue
