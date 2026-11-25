module

public import SympyProofs.Calculus.Risch.Program.Poly
public import SympyProofs.Calculus.Risch.Spec.Field
public import SympyProofs.Calculus.Risch.Spec.Poly
public import SympyProofs.Calculus.Risch.Proof.Normal
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The specification of the polynomial programs. A coefficient list over the terms of depth
`n` denotes a polynomial over the field `K k n`. Each program is specified by the polynomial
its result denotes: the arithmetic, division with remainder, the extended Euclidean
algorithm and reduction to lowest terms. `Term.norm` keeps the value of every term that is
defined, over every constant field of characteristic zero. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

namespace Coeff

/-- The value of a negation is the negative of the value. -/
theorem value_neg (a : Term n) : Term.value k (neg a) = -Term.value k a := by
  fun_cases neg a <;> simp [Term.value, Term.eval]

/-- The value of a sum is the sum of the values. -/
theorem value_add (a b : Term n) :
    Term.value k (add a b) = Term.value k a + Term.value k b := by
  fun_cases add a b <;> simp_all [Term.value, Term.eval]

/-- The value of a product is the product of the values. -/
theorem value_mul (a b : Term n) :
    Term.value k (mul a b) = Term.value k a * Term.value k b := by
  fun_cases mul a b <;> simp_all [Term.value, Term.eval]

/-- The value of a quotient is the quotient of the values. -/
theorem value_div (a b : Term n) :
    Term.value k (div a b) = Term.value k a / Term.value k b := by
  fun_cases div a b <;> simp_all [Term.value, Term.eval]

/-- The negation of a defined term is defined. -/
theorem inDomain_neg {a : Term n} (ha : Term.InDomain k a) : Term.InDomain k (neg a) := by
  fun_cases neg a <;> first | exact trivial | exact ha

/-- The sum of defined terms is defined. -/
theorem inDomain_add {a b : Term n} (ha : Term.InDomain k a) (hb : Term.InDomain k b) :
    Term.InDomain k (add a b) := by
  fun_cases add a b <;> first | exact trivial | exact ha | exact hb | exact ⟨ha, hb⟩

/-- The product of defined terms is defined. -/
theorem inDomain_mul {a b : Term n} (ha : Term.InDomain k a) (hb : Term.InDomain k b) :
    Term.InDomain k (mul a b) := by
  fun_cases mul a b <;> first | exact trivial | exact ha | exact hb | exact ⟨ha, hb⟩

/-- The quotient of defined terms is defined when the divisor does not vanish. -/
theorem inDomain_div {a b : Term n} (ha : Term.InDomain k a) (hb : Term.InDomain k b)
    (nz : Term.value k b ≠ 0) : Term.InDomain k (div a b) := by
  fun_cases div a b <;> first | exact ha | exact ⟨ha, hb, nz⟩

end Coeff

namespace Poly

/-- Every written coefficient is defined in the field of depth `n`. -/
def Defined (k : Type) [Field k] [CharZero k] (p : Poly n) : Prop :=
  ∀ c ∈ p, Term.InDomain k c

theorem model_nil : model k ([] : Poly n) = 0 := rfl

theorem model_cons (c : Term n) (cs : Poly n) :
    model k (c :: cs) = C (Term.value k c) + X * model k cs := rfl

theorem defined_nil : Defined k ([] : Poly n) := fun _ h => by cases h

theorem defined_cons {c : Term n} {p : Poly n} :
    Defined k (c :: p) ↔ Term.InDomain k c ∧ Defined k p := by
  simp [Defined]

theorem value_zero : Term.value k (.const 0 : Term n) = 0 := by
  rw [Term.value_const, Rat.cast_zero]

/-! ### Arithmetic -/

/-- The sum of two coefficient lists denotes the sum. -/
@[simp] theorem model_add (p q : Poly n) : model k (add p q) = model k p + model k q := by
  induction p generalizing q with
  | nil => simp [add, model]
  | cons a p ih =>
    cases q with
    | nil => simp [add, model]
    | cons b q =>
      rw [add, model_cons, model_cons, model_cons, ih, Coeff.value_add, C_add]
      ring

/-- The negation of a coefficient list denotes the negative. -/
@[simp] theorem model_neg (p : Poly n) : model k (neg p) = -model k p := by
  induction p with
  | nil => simp [neg, model]
  | cons c p ih =>
    rw [neg] at ih
    rw [neg, List.map_cons, model_cons, model_cons, ih, Coeff.value_neg, C_neg]
    ring

/-- Multiplying every coefficient by a term multiplies the polynomial by its value. -/
@[simp] theorem model_scale (c : Term n) (p : Poly n) :
    model k (scale c p) = C (Term.value k c) * model k p := by
  induction p with
  | nil => simp [scale, model]
  | cons a p ih =>
    rw [scale] at ih
    rw [scale, List.map_cons, model_cons, model_cons, ih, Coeff.value_mul, C_mul]
    ring

/-- The difference of two coefficient lists denotes the difference. -/
@[simp] theorem model_sub (p q : Poly n) : model k (sub p q) = model k p - model k q := by
  rw [sub, model_add, model_neg, sub_eq_add_neg]

/-- The product of two coefficient lists denotes the product. -/
@[simp] theorem model_mul (p q : Poly n) : model k (mul p q) = model k p * model k q := by
  induction p with
  | nil => simp [mul, model]
  | cons a p ih =>
    rw [mul, model_add, model_scale, model_cons, model_cons, ih, value_zero, C_0]
    ring

/-- The sum of defined coefficient lists is defined. -/
theorem defined_add {p q : Poly n} (hp : Defined k p) (hq : Defined k q) :
    Defined k (add p q) := by
  induction p generalizing q with
  | nil => simpa [add] using hq
  | cons a p ih =>
    cases q with
    | nil => simpa [add] using hp
    | cons b q =>
      rw [add]
      exact defined_cons.mpr ⟨Coeff.inDomain_add (defined_cons.mp hp).1 (defined_cons.mp hq).1,
        ih (defined_cons.mp hp).2 (defined_cons.mp hq).2⟩

/-- The negation of a defined coefficient list is defined. -/
theorem defined_neg {p : Poly n} (hp : Defined k p) : Defined k (neg p) := by
  rintro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact Coeff.inDomain_neg (hp d hd)

/-- A defined multiple of a defined coefficient list is defined. -/
theorem defined_scale {c : Term n} {p : Poly n} (hc : Term.InDomain k c) (hp : Defined k p) :
    Defined k (scale c p) := by
  intro e he
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
  exact Coeff.inDomain_mul hc (hp y hy)

/-- The difference of defined coefficient lists is defined. -/
theorem defined_sub {p q : Poly n} (hp : Defined k p) (hq : Defined k q) :
    Defined k (sub p q) :=
  defined_add hp (defined_neg hq)

/-- The product of defined coefficient lists is defined. -/
theorem defined_mul {p q : Poly n} (hp : Defined k p) (hq : Defined k q) :
    Defined k (mul p q) := by
  induction p with
  | nil => exact defined_nil
  | cons a p ih =>
    rw [mul]
    exact defined_add (defined_scale (defined_cons.mp hp).1 hq)
      (defined_cons.mpr ⟨trivial, ih (defined_cons.mp hp).2⟩)

/-- Appending a coefficient list shifts it by the length of the first. -/
theorem model_append (p q : Poly n) :
    model k (p ++ q) = model k p + X ^ p.length * model k q := by
  induction p with
  | nil => simp [model]
  | cons c p ih =>
    simp only [List.cons_append, model_cons, ih, List.length_cons, pow_succ]
    ring

/-- A list of zeros denotes zero. -/
theorem model_replicate_zero (j : ℕ) :
    model k (List.replicate j (.const 0 : Term n)) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, model_cons, ih, value_zero]; simp

theorem defined_replicate_zero (j : ℕ) :
    Defined k (List.replicate j (.const 0 : Term n)) := by
  intro c hc
  rw [List.eq_of_mem_replicate hc]
  trivial

theorem defined_append {p q : Poly n} (hp : Defined k p) (hq : Defined k q) :
    Defined k (p ++ q) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hp c h
  · exact hq c h

/-- The monomial `h θʲ` denotes `h Xʲ`. -/
theorem model_mono (j : ℕ) (h : Term n) : model k (mono j h) = C (Term.value k h) * X ^ j := by
  rw [mono, model_append, model_replicate_zero, List.length_replicate, model_cons, model_nil]
  ring

theorem defined_mono (j : ℕ) {h : Term n} (hh : Term.InDomain k h) : Defined k (mono j h) :=
  defined_append (defined_replicate_zero j) fun e he => by
    rw [List.mem_singleton.mp he]
    exact hh

theorem defined_dropLast {p : Poly n} (hp : Defined k p) : Defined k p.dropLast :=
  fun c hc => hp c (List.dropLast_subset p hc)

theorem defined_tail {p : Poly n} (hp : Defined k p) : Defined k p.tail :=
  fun c hc => hp c (List.mem_of_mem_tail hc)

/-! ### Coefficients -/

/-- The coefficients of the polynomial are the values of the written coefficients. -/
theorem coeff_model (p : Poly n) (i : ℕ) :
    (model k p).coeff i = (p[i]?.map (Term.value k)).getD 0 := by
  induction p generalizing i with
  | nil => simp [model]
  | cons c cs ih =>
    cases i with
    | zero => simp [model]
    | succ i => simp [model, ih]

/-- The coefficients beyond the written ones vanish. -/
theorem coeff_model_of_length_le {p : Poly n} {i : ℕ} (h : p.length ≤ i) :
    (model k p).coeff i = 0 := by simp [coeff_model, List.getElem?_eq_none h]

/-- The coefficient read from the list denotes the coefficient of the polynomial. -/
theorem value_coeff (p : Poly n) (i : ℕ) :
    Term.value k (coeff p i) = (model k p).coeff i := by
  rw [coeff_model, coeff, List.getD_eq_getElem?_getD]
  cases p[i]? <;> simp [value_zero]

theorem defined_coeff {p : Poly n} (hp : Defined k p) (i : ℕ) :
    Term.InDomain k (coeff p i) := by
  rw [coeff, List.getD_eq_getElem?_getD]
  cases h : p[i]? with
  | none => trivial
  | some c => exact hp c (List.mem_of_getElem? h)

/-- A coefficient list of length `l` denotes a polynomial of degree below `l`. -/
theorem natDegree_model_le (p : Poly n) : (model k p).natDegree ≤ p.length - 1 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hi => coeff_model_of_length_le (by omega)

/-- The coefficients of a list given by a function on an initial segment. -/
theorem coeff_model_map_range (f : ℕ → Term n) (N i : ℕ) :
    (model k ((List.range N).map f)).coeff i = if i < N then Term.value k (f i) else 0 := by
  rw [coeff_model]
  split
  · rename_i h
    simp [h]
  · rename_i h
    rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt h)]
    rfl

/-- The formal derivative of a coefficient list denotes the derivative. -/
theorem model_formalD (p : Poly n) : model k (formalD p) = derivative (model k p) := by
  ext i
  rw [formalD, coeff_model_map_range, coeff_derivative]
  split
  · rw [Coeff.value_mul, value_coeff, Term.value_const]
    push_cast
    ring
  · rw [coeff_model_of_length_le (by omega : p.length ≤ i + 1), zero_mul]

theorem defined_formalD {p : Poly n} (hp : Defined k p) : Defined k (formalD p) := by
  intro c hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
  exact Coeff.inDomain_mul trivial (defined_coeff hp (i + 1))

/-- Dividing every coefficient by a term divides the polynomial by its value. -/
theorem model_map_div (p : Poly n) (e : Term n) :
    model k (p.map fun c => .div c e) = C (Term.value k e)⁻¹ * model k p := by
  induction p with
  | nil => simp [model]
  | cons c cs ih =>
    rw [List.map_cons, model_cons, ih, model_cons]
    change C (Term.value k c / Term.value k e) + _ = _
    rw [div_eq_mul_inv, C_mul]
    ring

theorem defined_map_div {p : Poly n} {e : Term n} (hp : Defined k p)
    (he : Term.InDomain k e) (nz : Term.value k e ≠ 0) :
    Defined k (p.map fun c => .div c e) := by
  intro c hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  exact ⟨hp a ha, he, nz⟩

/-! ### Terms one level up -/

/-- A coefficient list of depth `n`, read at depth `n + 1`, denotes the same polynomial with
its coefficients embedded in the larger field. -/
theorem model_map_weaken (p : Poly n) :
    model k (p.map Term.weaken) = (model k p).map (RatFunc.C : K k n →+* K k (n + 1)) := by
  induction p with
  | nil => simp [model_nil]
  | cons c cs ih =>
    rw [List.map_cons, model_cons, model_cons, ih, Term.value_weaken]
    simp

/-- The term of a coefficient list denotes its polynomial, as a rational function. -/
theorem value_toTerm (p : Poly n) :
    Term.value k (toTerm p) = algebraMap (K k n)[X] (RatFunc (K k n)) (model k p) := by
  induction p with
  | nil => simp [model, toTerm, Term.value, Term.eval]
  | cons c cs ih =>
    rw [toTerm, Coeff.value_add, Coeff.value_mul, Term.value_weaken, ih]
    simp [model, Term.value, Term.eval, gens, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

/-- The term of a defined coefficient list is defined. -/
theorem inDomain_toTerm {p : Poly n} (hp : Defined k p) : Term.InDomain k (toTerm p) := by
  induction p with
  | nil => trivial
  | cons a as ih =>
    exact Coeff.inDomain_add ((Term.inDomain_weaken a).mpr (defined_cons.mp hp).1)
      (Coeff.inDomain_mul trivial (ih (defined_cons.mp hp).2))

/-- The numerator and denominator of a term have defined coefficients. -/
theorem ofTerm_defined (f : Term (n + 1)) :
    Defined k (ofTerm f).1 ∧ Defined k (ofTerm f).2 := by
  induction f with
  | const => simp [Defined, ofTerm, Term.InDomain, Term.Defined]
  | gen i =>
    induction i using Fin.lastCases <;> simp [Defined, ofTerm, Term.InDomain, Term.Defined]
  | neg f ih => exact ⟨defined_neg ih.1, ih.2⟩
  | add _ _ h j =>
    exact ⟨defined_add (defined_mul h.1 j.2) (defined_mul j.1 h.2), defined_mul h.2 j.2⟩
  | sub _ _ h j =>
    exact ⟨defined_sub (defined_mul h.1 j.2) (defined_mul j.1 h.2), defined_mul h.2 j.2⟩
  | mul _ _ h j => exact ⟨defined_mul h.1 j.1, defined_mul h.2 j.2⟩
  | div _ _ h j => exact ⟨defined_mul h.1 j.2, defined_mul h.2 j.1⟩

/-- A defined term is the quotient of its numerator by its denominator, and the denominator
does not vanish. -/
theorem ofTerm_spec (f : Term (n + 1)) (hf : Term.InDomain k f) :
    algebraMap (K k n)[X] (RatFunc (K k n)) (model k (ofTerm f).1) =
        Term.value k f * algebraMap (K k n)[X] (RatFunc (K k n)) (model k (ofTerm f).2) ∧
      algebraMap (K k n)[X] (RatFunc (K k n)) (model k (ofTerm f).2) ≠ 0 := by
  induction f with
  | const q => simp [ofTerm, model, Term.value, Term.eval, RatFunc.algebraMap_C]
  | gen i =>
    induction i using Fin.lastCases <;>
      simp [ofTerm, model, Term.value, Term.eval, gens, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X]
  | neg f ih =>
    obtain ⟨he, hn⟩ := ih hf
    simpa [ofTerm, he, Term.value, Term.eval] using hn
  | add f g ih jh | sub f g ih jh | mul f g ih jh =>
    obtain ⟨he, hn⟩ := ih hf.1
    obtain ⟨ge, gn⟩ := jh hf.2
    simp only [ofTerm, model_add, model_sub, model_mul, map_sub, map_mul, map_add, he, ge]
    exact ⟨by simp only [Term.value, Term.eval]; ring, mul_ne_zero hn gn⟩
  | div f g ih jh =>
    obtain ⟨he, hn⟩ := ih hf.1
    obtain ⟨ge, gn⟩ := jh hf.2.1
    have nz : Term.value k g ≠ 0 := hf.2.2
    simp only [ofTerm, model_mul, map_mul, he, ge]
    refine ⟨?_, mul_ne_zero hn (mul_ne_zero nz gn)⟩
    change _ = Term.value k f / Term.value k g * _
    field_simp [nz]

/-! ### The highest written coefficient -/

/-- The highest written coefficient denotes the coefficient of that degree. -/
theorem value_lead (p : Poly n) :
    Term.value k (lead p) = (model k p).coeff (p.length - 1) := by
  rw [coeff_model, lead]
  rcases List.eq_nil_or_concat p with rfl | ⟨q, c, rfl⟩
  · simp [value_zero]
  · simp

theorem defined_lead {p : Poly n} (hp : Defined k p) : Term.InDomain k (lead p) := by
  rw [lead]
  rcases List.eq_nil_or_concat p with rfl | ⟨q, c, rfl⟩
  · trivial
  · simpa using hp c (by simp)

theorem lead_cons (c : Term n) {p : Poly n} (hp : p ≠ []) : lead (c :: p) = lead p := by
  cases p with
  | nil => exact (hp rfl).elim
  | cons y q => simp only [lead, List.getLastD_cons]

/-- The highest written coefficient does not vanish. -/
def Normal (k : Type) [Field k] [CharZero k] (p : Poly n) : Prop := Term.value k (lead p) ≠ 0

theorem Normal.ne_nil {p : Poly n} (h : Normal k p) : p ≠ [] := by
  rintro rfl
  exact h value_zero

theorem Normal.model_ne_zero {p : Poly n} (h : Normal k p) : model k p ≠ 0 := by
  intro z
  apply h
  rw [value_lead, z, coeff_zero]

/-- The degree of a normal coefficient list is one less than its length. -/
theorem Normal.natDegree {p : Poly n} (h : Normal k p) :
    (model k p).natDegree = p.length - 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_model_le p
  · rw [← value_lead]
    exact h

/-- The leading coefficient of a normal coefficient list is the value of the highest written
coefficient. -/
theorem Normal.leadingCoeff {p : Poly n} (h : Normal k p) :
    (model k p).leadingCoeff = Term.value k (lead p) := by
  rw [Polynomial.leadingCoeff, h.natDegree, value_lead]

/-- Trimming keeps the polynomial, and the result is empty or normal. -/
theorem trim_spec : ∀ {p : Poly n}, Defined k p →
    model k (trim p) = model k p ∧ Defined k (trim p) ∧ (trim p = [] ∨ Normal k (trim p)) ∧
      (trim p).length ≤ p.length := by
  intro p
  induction p with
  | nil => intro _; exact ⟨rfl, defined_nil, Or.inl rfl, le_rfl⟩
  | cons c cs ih =>
    intro hp
    have hc : Term.InDomain k c := hp c List.mem_cons_self
    obtain ⟨m, d, nrm, len⟩ := ih fun e he' => hp e (List.mem_cons_of_mem _ he')
    rw [trim]
    by_cases he : (trim cs).isEmpty
    · have e : trim cs = [] := List.isEmpty_iff.mp he
      have z : model k cs = 0 := by rw [← m, e, model_nil]
      rw [ite_eq_left he]
      by_cases hz : c.isZero
      · rw [ite_eq_left hz]
        refine ⟨?_, defined_nil, Or.inl rfl, by simp⟩
        rw [model_cons, z, (Term.isZero_iff hc).mp hz]
        simp [model_nil]
      · rw [ite_eq_right hz]
        refine ⟨by rw [model_cons, model_cons, z, model_nil], fun e he' => ?_, Or.inr ?_,
          by simp⟩
        · rw [List.mem_singleton.mp he']
          exact hc
        · exact fun v => hz ((Term.isZero_iff hc).mpr v)
    · rw [ite_eq_right he]
      have ne : trim cs ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
      refine ⟨by rw [model_cons, model_cons, m], fun e he' => ?_, Or.inr ?_, by simpa using len⟩
      · rcases List.mem_cons.mp he' with rfl | he'
        · exact hc
        · exact d e he'
      · have := nrm.resolve_left ne
        rw [Normal, lead_cons c ne]
        exact this

/-- Trimming leaves nothing exactly when the polynomial is zero. -/
theorem trim_eq_nil_iff {p : Poly n} (hp : Defined k p) : trim p = [] ↔ model k p = 0 := by
  obtain ⟨m, -, nrm, -⟩ := trim_spec hp
  constructor
  · intro e
    rw [← m, e, model_nil]
  · intro z
    rcases nrm with e | h
    · exact e
    · exact (h.model_ne_zero (m.trans z)).elim

/-- A shorter coefficient list has smaller degree than a normal one. -/
theorem degree_model_lt {p d : Poly n} (nd : Normal k d) (h : p.length < d.length) :
    (model k p).degree < (model k d).degree := by
  rw [degree_eq_natDegree nd.model_ne_zero, nd.natDegree]
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro m hm
  exact coeff_model_of_length_le (by omega)

end Poly

/-- A simplifier of terms: it keeps a defined term defined and does not change its value. -/
def Sound (k : Type) [Field k] [CharZero k] (ν : Term n → Term n) : Prop :=
  ∀ e, Term.InDomain k e → Term.InDomain k (ν e) ∧ Term.value k (ν e) = Term.value k e

namespace Poly

variable {ν : Term n → Term n}

/-- Simplifying every coefficient keeps a defined coefficient list defined. -/
theorem defined_map_sound (hν : Sound k ν) {p : Poly n} (hp : Defined k p) :
    Defined k (p.map ν) := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  exact (hν e (hp e he)).1

/-- Simplifying every coefficient of a defined coefficient list keeps the polynomial. -/
theorem model_map_sound (hν : Sound k ν) : ∀ {p : Poly n}, Defined k p →
    model k (p.map ν) = model k p
  | [], _ => rfl
  | c :: p, h => by
    rw [List.map_cons, model_cons, model_cons, (hν c (h c List.mem_cons_self)).2,
      model_map_sound hν fun e he => h e (List.mem_cons_of_mem _ he)]

/-! ### Division with remainder -/

theorem length_add (p q : Poly n) : (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]

theorem model_subShift (p : Poly n) (c : Term n) (j : ℕ) (d : Poly n) :
    model k (subShift p c j d) = model k p - C (Term.value k c) * X ^ j * model k d := by
  rw [subShift, model_sub, model_append, model_replicate_zero, model_scale,
    List.length_replicate]
  ring

theorem defined_subShift {p d : Poly n} {c : Term n} (hp : Defined k p)
    (hc : Term.InDomain k c) (hd : Defined k d) (j : ℕ) : Defined k (subShift p c j d) :=
  defined_sub hp (defined_append (defined_replicate_zero j) (defined_scale hc hd))

theorem length_subShift (p : Poly n) (c : Term n) (j : ℕ) (d : Poly n) :
    (subShift p c j d).length = max p.length (j + d.length) := by
  simp [subShift, sub, neg, scale, length_add]

/-- Dropping a vanishing highest written coefficient keeps the polynomial. -/
theorem model_dropLast {p : Poly n} (h : (model k p).coeff (p.length - 1) = 0) :
    model k p.dropLast = model k p := by
  ext i
  rw [coeff_model, coeff_model, List.getElem?_dropLast]
  by_cases hi : i < p.length - 1
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi]
    by_cases hl : i < p.length
    · have e : i = p.length - 1 := by omega
      rw [e, ← coeff_model, h]
      simp
    · rw [List.getElem?_eq_none (by omega)]

/-- Long division by a normal coefficient list: the quotient and remainder satisfy the
division identity, and the remainder is shorter than the divisor once the fuel suffices. -/
theorem divModWith_spec (hν : Sound k ν) {d : Poly n} (hd : Defined k d) (nd : Normal k d) :
    ∀ (fuel : ℕ) {p : Poly n}, Defined k p →
      model k p = model k d * model k (divModWith ν d fuel p).1 +
          model k (divModWith ν d fuel p).2 ∧
        Defined k (divModWith ν d fuel p).1 ∧ Defined k (divModWith ν d fuel p).2 ∧
        ((divModWith ν d fuel p).2.length < d.length ∨
          (divModWith ν d fuel p).2.length + fuel ≤ p.length) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p hp
    exact ⟨by simp [divModWith, model_nil], by simpa [divModWith] using defined_nil, hp,
      Or.inr (by simp [divModWith])⟩
  | succ fuel ih =>
    intro p hp
    rw [divModWith]
    by_cases hlt : p.length < d.length
    · rw [ite_eq_left (Nat.blt_eq.mpr hlt)]
      exact ⟨by simp [model_nil], defined_nil, hp, Or.inl hlt⟩
    · rw [ite_eq_right (fun h => hlt (Nat.blt_eq.mp h))]
      dsimp only
      have dpos : 0 < d.length := List.length_pos_iff.mpr nd.ne_nil
      have hc0 : Term.InDomain k (Term.div (lead p) (lead d)) :=
        ⟨defined_lead hp, defined_lead hd, nd⟩
      have vc : Term.value k (ν (Term.div (lead p) (lead d))) =
          Term.value k (lead p) / Term.value k (lead d) := (hν _ hc0).2
      obtain ⟨c, hcdef⟩ : ∃ c, c = ν (Term.div (lead p) (lead d)) := ⟨_, rfl⟩
      have hc : Term.InDomain k c := hcdef ▸ (hν _ hc0).1
      rw [← hcdef] at vc ⊢
      have hs := defined_subShift hp hc hd (p.length - d.length)
      have len : ((subShift p c (p.length - d.length) d).map ν).length = p.length := by
        rw [List.length_map, length_subShift]
        omega
      have top : (model k ((subShift p c (p.length - d.length) d).map ν)).coeff
          (((subShift p c (p.length - d.length) d).map ν).length - 1) = 0 := by
        rw [len, model_map_sound hν hs, model_subShift, coeff_sub, mul_assoc, coeff_C_mul,
          show p.length - 1 = (d.length - 1) + (p.length - d.length) by omega, coeff_X_pow_mul,
          ← show p.length - 1 = (d.length - 1) + (p.length - d.length) by omega, ← value_lead,
          ← value_lead, vc, div_mul_cancel₀ _ nd, sub_self]
      obtain ⟨eq, dq, dr, bound⟩ := ih (defined_dropLast (defined_map_sound hν hs))
      rw [model_dropLast top, model_map_sound hν hs, model_subShift] at eq
      refine ⟨?_, defined_add dq (defined_mono _ hc), dr, ?_⟩
      · rw [model_add, model_mono]
        linear_combination eq
      · rcases bound with b | b
        · exact Or.inl b
        · right
          rw [List.length_dropLast, len] at b
          omega

/-- Division by a normal coefficient list: the division identity holds and the remainder is
shorter than the divisor. -/
theorem remWith_spec (hν : Sound k ν) {p d : Poly n} (hp : Defined k p) (hd : Defined k d)
    (nd : Normal k d) :
    model k p = model k d * model k (quotWith ν p d) + model k (remWith ν p d) ∧
      Defined k (quotWith ν p d) ∧ Defined k (remWith ν p d) ∧
      (remWith ν p d).length < d.length := by
  obtain ⟨eq, dq, dr, bound⟩ := divModWith_spec hν hd nd p.length hp
  refine ⟨eq, dq, dr, ?_⟩
  rcases bound with b | b
  · exact b
  · have dpos : 0 < d.length := List.length_pos_iff.mpr nd.ne_nil
    change (remWith ν p d).length + p.length ≤ p.length at b
    omega

/-- Exact division returns the quotient. -/
theorem quotWith_of_dvd (hν : Sound k ν) {p d : Poly n} (hp : Defined k p)
    (hd : Defined k d) (nd : Normal k d) (dvd : model k d ∣ model k p) :
    model k p = model k d * model k (quotWith ν p d) := by
  obtain ⟨eq, -, -, small⟩ := remWith_spec hν hp hd nd
  have rdvd : model k d ∣ model k (remWith ν p d) := by
    have : model k (remWith ν p d) = model k p - model k d * model k (quotWith ν p d) := by
      rw [eq]; ring
    rw [this]
    exact dvd_sub dvd (dvd_mul_right _ _)
  have rz : model k (remWith ν p d) = 0 := by
    by_contra hne
    have le := natDegree_le_of_dvd rdvd hne
    rw [nd.natDegree] at le
    have up : (model k (remWith ν p d)).natDegree < (remWith ν p d).length := by
      by_contra hge
      exact hne (leadingCoeff_eq_zero.mp (coeff_model_of_length_le (by omega)))
    omega
  rw [eq, rz, add_zero]

/-! ### Greatest common divisors -/

/-- Dividing every coefficient by a term with nonzero value and simplifying keeps a defined
coefficient list defined. -/
theorem defined_map_sound_div (hν : Sound k ν) {p : Poly n} {e : Term n} (hp : Defined k p)
    (he : Term.InDomain k e) (nz : Term.value k e ≠ 0) :
    Defined k (p.map fun a => ν (.div a e)) := by
  have := defined_map_sound hν (defined_map_div hp he nz)
  rwa [List.map_map] at this

/-- Dividing every coefficient by a term with nonzero value and simplifying divides the
polynomial by the value. -/
theorem model_map_sound_div (hν : Sound k ν) {p : Poly n} {e : Term n} (hp : Defined k p)
    (he : Term.InDomain k e) (nz : Term.value k e ≠ 0) :
    model k (p.map fun a => ν (.div a e)) = C (Term.value k e)⁻¹ * model k p := by
  have := model_map_sound hν (defined_map_div hp he nz)
  rwa [List.map_map, model_map_div] at this

/-- Dividing a normal coefficient list by its highest coefficient keeps it defined and
divides the polynomial by that coefficient. -/
theorem monicWith_spec (hν : Sound k ν) {p : Poly n} (hp : Defined k p) (np : Normal k p) :
    Defined k (monicWith ν p) ∧ (monicWith ν p).length = p.length ∧
      model k (monicWith ν p) = C (Term.value k (lead p))⁻¹ * model k p :=
  ⟨defined_map_sound_div hν hp (defined_lead hp) np, List.length_map _,
    model_map_sound_div hν hp (defined_lead hp) np⟩

/-- The extended Euclidean algorithm returns a common divisor with its cofactors, once the
fuel is at least the trimmed length of the second argument. -/
theorem xgcdWith_spec (hν : Sound k ν) : ∀ (fuel : ℕ) {a b : Poly n}, Defined k a →
    Defined k b → (trim b).length ≤ fuel →
    Defined k (xgcdWith ν fuel a b).1 ∧ Defined k (xgcdWith ν fuel a b).2.1 ∧
      Defined k (xgcdWith ν fuel a b).2.2 ∧
      model k (xgcdWith ν fuel a b).2.1 * model k a +
          model k (xgcdWith ν fuel a b).2.2 * model k b =
        model k (xgcdWith ν fuel a b).1 ∧
      model k (xgcdWith ν fuel a b).1 ∣ model k a ∧
      model k (xgcdWith ν fuel a b).1 ∣ model k b := by
  intro fuel
  have one : Defined k ([.const 1] : Poly n) := fun e he' => by
    rw [List.mem_singleton.mp he']
    trivial
  have mone : model k ([.const 1] : Poly n) = 1 := by
    simp [model_cons, model_nil, Term.value_const]
  induction fuel with
  | zero =>
    intro a b ha hb hl
    have bz : model k b = 0 :=
      (trim_eq_nil_iff hb).mp (List.length_eq_zero_iff.mp (Nat.le_zero.mp hl))
    exact ⟨ha, one, defined_nil, by simp [xgcdWith, mone, model_nil], dvd_rfl,
      bz ▸ dvd_zero _⟩
  | succ fuel ih =>
    intro a b ha hb hl
    obtain ⟨mt, dt, nrm, -⟩ := trim_spec hb
    rw [xgcdWith]
    by_cases he : (trim b).isEmpty
    · rw [ite_eq_left he]
      have bz : model k b = 0 := (trim_eq_nil_iff hb).mp (List.isEmpty_iff.mp he)
      exact ⟨ha, one, defined_nil, by simp [mone, model_nil], dvd_rfl, bz ▸ dvd_zero _⟩
    · rw [ite_eq_right he]
      dsimp only
      have nb : Normal k (trim b) := nrm.resolve_left fun h => he (List.isEmpty_iff.mpr h)
      obtain ⟨eq, dq, dr, small⟩ := remWith_spec hν ha dt nb
      simp only [remWith, quotWith] at eq dq dr small
      generalize divModWith ν (trim b) a.length a = qr at eq dq dr small ⊢
      obtain ⟨rt, drt, nrt, lrt⟩ := trim_spec dr
      rw [mt] at eq
      by_cases re : (trim qr.2).isEmpty
      · rw [ite_eq_left re]
        have rz : model k qr.2 = 0 := (trim_eq_nil_iff dr).mp (List.isEmpty_iff.mp re)
        refine ⟨dt, defined_nil, one, by rw [model_nil, mone, mt]; ring, ?_, by rw [mt]⟩
        rw [eq, rz, add_zero, mt]
        exact dvd_mul_right _ _
      · rw [ite_eq_right re]
        have nr : Normal k (trim qr.2) := nrt.resolve_left fun h => re (List.isEmpty_iff.mpr h)
        obtain ⟨dm, lm, mm⟩ := monicWith_spec hν drt nr
        obtain ⟨dg, du, dv, bez, ga, gb⟩ := ih dt dm (by
          have := (trim_spec dm).2.2.2
          omega)
        generalize xgcdWith ν fuel (trim b) (monicWith ν (trim qr.2)) = s
          at dg du dv bez ga gb ⊢
        have du' := defined_map_sound_div hν dv (defined_lead drt) nr
        have mu := model_map_sound_div hν dv (defined_lead drt) nr
        have dco := defined_sub du (defined_mul du' dq)
        have u : IsUnit (C (Term.value k (lead (trim qr.2)))⁻¹) :=
          isUnit_C.mpr (inv_ne_zero nr).isUnit
        rw [mm, rt] at bez gb
        rw [mt] at bez ga
        refine ⟨dg, du', defined_map_sound hν dco, ?_, ?_, ga⟩
        · rw [model_map_sound hν dco, model_sub, model_mul, mu]
          linear_combination (C (Term.value k (lead (trim qr.2)))⁻¹ * model k s.2.2) * eq + bez
        · rw [eq]
          exact dvd_add (dvd_mul_of_dvd_left ga _) (u.dvd_mul_left.mp gb)

/-- The greatest common divisor program returns a common divisor `g` of `a` and `b` and
cofactors with `u a + v b = g`. -/
theorem gcdWith_spec (hν : Sound k ν) {a b : Poly n} (ha : Defined k a) (hb : Defined k b) :
    Defined k (gcdWith ν a b).1 ∧ Defined k (gcdWith ν a b).2.1 ∧
      Defined k (gcdWith ν a b).2.2 ∧
      model k (gcdWith ν a b).2.1 * model k a + model k (gcdWith ν a b).2.2 * model k b =
        model k (gcdWith ν a b).1 ∧
      model k (gcdWith ν a b).1 ∣ model k a ∧ model k (gcdWith ν a b).1 ∣ model k b :=
  xgcdWith_spec hν _ ha hb (by
    have := (trim_spec hb).2.2.2
    omega)

/-- The Euclidean algorithm returns a common divisor of `a` and `b` that every common divisor
divides, once the fuel is at least the trimmed length of `b`. -/
theorem euclidWith_spec (hν : Sound k ν) : ∀ (fuel : ℕ) {a b : Poly n}, Defined k a →
    Defined k b → (trim b).length ≤ fuel →
    Defined k (euclidWith ν fuel a b) ∧ model k (euclidWith ν fuel a b) ∣ model k a ∧
      model k (euclidWith ν fuel a b) ∣ model k b ∧
      ∀ h, h ∣ model k a → h ∣ model k b → h ∣ model k (euclidWith ν fuel a b) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b ha hb hl
    have bz : model k b = 0 :=
      (trim_eq_nil_iff hb).mp (List.length_eq_zero_iff.mp (Nat.le_zero.mp hl))
    exact ⟨ha, dvd_rfl, bz ▸ dvd_zero _, fun _ h _ => h⟩
  | succ fuel ih =>
    intro a b ha hb hl
    obtain ⟨mt, dt, nrm, -⟩ := trim_spec hb
    rw [euclidWith]
    by_cases he : (trim b).isEmpty
    · rw [ite_eq_left he]
      have bz : model k b = 0 := (trim_eq_nil_iff hb).mp (List.isEmpty_iff.mp he)
      exact ⟨ha, dvd_rfl, bz ▸ dvd_zero _, fun _ h _ => h⟩
    · rw [ite_eq_right he]
      dsimp only
      have nb : Normal k (trim b) := nrm.resolve_left fun h => he (List.isEmpty_iff.mpr h)
      obtain ⟨eq, -, dr, small⟩ := remWith_spec hν ha dt nb
      generalize remWith ν a (trim b) = r at eq dr small ⊢
      generalize quotWith ν a (trim b) = q at eq
      obtain ⟨rt, drt, nrt, lrt⟩ := trim_spec dr
      rw [mt] at eq
      by_cases re : (trim r).isEmpty
      · rw [ite_eq_left re]
        have rz : model k r = 0 := (trim_eq_nil_iff dr).mp (List.isEmpty_iff.mp re)
        refine ⟨dt, ?_, by rw [mt], fun h _ hb' => by rw [mt]; exact hb'⟩
        rw [eq, rz, add_zero, mt]
        exact dvd_mul_right _ _
      · rw [ite_eq_right re]
        have nr : Normal k (trim r) := nrt.resolve_left fun h => re (List.isEmpty_iff.mpr h)
        obtain ⟨dm, lm, mm⟩ := monicWith_spec hν drt nr
        obtain ⟨dg, ga, gb, gmax⟩ := ih dt dm (by
          have := (trim_spec dm).2.2.2
          omega)
        have u : IsUnit (C (Term.value k (lead (trim r)))⁻¹) :=
          isUnit_C.mpr (inv_ne_zero nr).isUnit
        rw [mm, rt] at gb
        rw [mt] at ga
        refine ⟨dg, ?_, ga, fun h ha' hb' => gmax h (by rw [mt]; exact hb') ?_⟩
        · rw [eq]
          exact dvd_add (dvd_mul_of_dvd_left ga _) (u.dvd_mul_left.mp gb)
        · rw [mm, rt, show model k r = model k a - model k b * model k q by rw [eq]; ring]
          exact dvd_mul_of_dvd_right (dvd_sub ha' (dvd_mul_of_dvd_left hb' _)) _

/-- Lowest terms: the same quotient, with coprime numerator and denominator. -/
theorem reduceWith_spec (hν : Sound k ν) {a b : Poly n} (ha : Defined k a) (hb : Defined k b)
    (bn : model k b ≠ 0) :
    Defined k (reduceWith ν a b).1 ∧ Defined k (reduceWith ν a b).2 ∧
      model k (reduceWith ν a b).2 ≠ 0 ∧
      IsCoprime (model k (reduceWith ν a b).1) (model k (reduceWith ν a b).2) ∧
      model k a * model k (reduceWith ν a b).2 = model k (reduceWith ν a b).1 * model k b := by
  obtain ⟨G, hG⟩ : ∃ G, G = euclidWith ν (b.length + 1) a b := ⟨_, rfl⟩
  have e : reduceWith ν a b = (quotWith ν a (trim G), quotWith ν b (trim G)) := by
    subst hG
    rfl
  obtain ⟨dg, ga, gb, gmax⟩ := euclidWith_spec hν (b.length + 1) ha hb (by
    have := (trim_spec hb).2.2.2
    omega)
  rw [← hG] at dg ga gb gmax
  rw [e]
  obtain ⟨mt, dt, nrm, -⟩ := trim_spec dg
  have gn : model k G ≠ 0 := fun z => bn (zero_dvd_iff.mp (z ▸ gb))
  have ng : Normal k (trim G) := nrm.resolve_left fun h => gn ((trim_eq_nil_iff dg).mp h)
  have qa := quotWith_of_dvd hν ha dt ng (mt ▸ ga)
  have qb := quotWith_of_dvd hν hb dt ng (mt ▸ gb)
  rw [mt] at qa qb
  refine ⟨(remWith_spec hν ha dt ng).2.1, (remWith_spec hν hb dt ng).2.1, ?_, ?_, ?_⟩
  · intro z
    apply bn
    rw [qb, z, mul_zero]
  · apply IsRelPrime.isCoprime
    intro d da db
    have h1 : model k G * d ∣ model k a := by
      rw [qa]
      exact mul_dvd_mul_left _ da
    have h2 : model k G * d ∣ model k b := by
      rw [qb]
      exact mul_dvd_mul_left _ db
    apply isUnit_of_dvd_one
    exact (mul_dvd_mul_iff_left gn).mp (by rw [mul_one]; exact gmax _ h1 h2)
  · apply mul_left_cancel₀ gn
    linear_combination
      (model k G * model k (quotWith ν b (trim G))) * qa -
      (model k G * model k (quotWith ν a (trim G))) * qb

end Poly

namespace Term

/-- The rational number computed for a term without generators is its value. -/
theorem value_evalRat (e : Term 0) : ((e.evalRat : ℚ) : k) = value k e := by
  induction e with
  | const q => rfl
  | gen i => exact i.elim0
  | neg a ih =>
    change ((-a.evalRat : ℚ) : k) = -value k a
    rw [Rat.cast_neg, ih]
  | add a b ha hb =>
    change ((a.evalRat + b.evalRat : ℚ) : k) = value k a + value k b
    rw [Rat.cast_add, ha, hb]
  | sub a b ha hb =>
    change ((a.evalRat - b.evalRat : ℚ) : k) = value k a - value k b
    rw [Rat.cast_sub, ha, hb]
  | mul a b ha hb =>
    change ((a.evalRat * b.evalRat : ℚ) : k) = value k a * value k b
    rw [Rat.cast_mul, ha, hb]
  | div a b ha hb =>
    change ((a.evalRat / b.evalRat : ℚ) : k) = value k a / value k b
    rw [Rat.cast_div, ha, hb]

/-- Lowest terms keep a defined term defined and do not change its value. -/
theorem norm_sound : ∀ (n : ℕ), Sound k (norm (n := n))
  | 0 => fun e _ => ⟨trivial, value_evalRat e⟩
  | n + 1 => by
    intro e he
    have hν : Sound k (norm (n := n)) := norm_sound n
    obtain ⟨fe, fn⟩ := Poly.ofTerm_spec e he
    obtain ⟨dp, dq⟩ := Poly.ofTerm_defined (k := k) e
    have qn : Poly.model k (Poly.ofTerm e).2 ≠ 0 := fun z => fn (by rw [z, map_zero])
    obtain ⟨dN, dB, nB, -, ratio⟩ := Poly.reduceWith_spec hν dp dq qn
    obtain ⟨mt, dt, nrm, -⟩ := Poly.trim_spec dB
    have nd : Poly.Normal k (Poly.trim (Poly.reduceWith norm (Poly.ofTerm e).1
        (Poly.ofTerm e).2).2) :=
      nrm.resolve_left fun h => nB ((Poly.trim_eq_nil_iff dB).mp h)
    have hc := Poly.defined_lead dt
    have cn : value k (Poly.lead (Poly.trim (Poly.reduceWith norm (Poly.ofTerm e).1
        (Poly.ofTerm e).2).2)) ≠ 0 := nd
    have nB' := RatFunc.algebraMap_ne_zero nB
    have ci : algebraMap (K k n)[X] (RatFunc (K k n)) (C (value k (Poly.lead (Poly.trim
        (Poly.reduceWith norm (Poly.ofTerm e).1 (Poly.ofTerm e).2).2)))⁻¹) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (C_ne_zero.mpr (inv_ne_zero cn))
    have vN := Poly.model_map_sound_div hν dN hc cn
    have vD := Poly.model_map_sound_div hν dt hc cn
    rw [mt] at vD
    rw [norm]
    refine ⟨Coeff.inDomain_div (Poly.inDomain_toTerm (Poly.defined_map_sound_div hν dN hc cn))
      (Poly.inDomain_toTerm (Poly.defined_map_sound_div hν dt hc cn)) ?_, ?_⟩
    · rw [Poly.value_toTerm, vD, map_mul]
      exact mul_ne_zero ci nB'
    · rw [Coeff.value_div, Poly.value_toTerm, Poly.value_toTerm, vN, vD, map_mul, map_mul,
        mul_div_mul_left _ _ ci, div_eq_iff nB']
      have r' := congrArg (algebraMap (K k n)[X] (RatFunc (K k n))) ratio
      simp only [map_mul] at r'
      rw [fe] at r'
      apply mul_right_cancel₀ fn
      linear_combination -r'

end Term

namespace Poly

/-! ### The programs with the fixed simplifier -/

theorem defined_norm {p : Poly n} (hp : Defined k p) : Defined k (norm p) :=
  defined_map_sound (Term.norm_sound n) hp

theorem model_norm {p : Poly n} (hp : Defined k p) : model k (norm p) = model k p :=
  model_map_sound (Term.norm_sound n) hp

/-- Division by a normal coefficient list: the division identity holds and the remainder is
shorter than the divisor. -/
theorem rem_spec {p d : Poly n} (hp : Defined k p) (hd : Defined k d) (nd : Normal k d) :
    model k p = model k d * model k (quot p d) + model k (rem p d) ∧
      Defined k (quot p d) ∧ Defined k (rem p d) ∧ (rem p d).length < d.length :=
  remWith_spec (Term.norm_sound n) hp hd nd

/-- Exact division returns the quotient. -/
theorem quot_of_dvd {p d : Poly n} (hp : Defined k p) (hd : Defined k d) (nd : Normal k d)
    (dvd : model k d ∣ model k p) : model k p = model k d * model k (quot p d) :=
  quotWith_of_dvd (Term.norm_sound n) hp hd nd dvd

/-- The greatest common divisor program returns a common divisor `g` of `a` and `b` and
cofactors with `u a + v b = g`. -/
theorem gcd_spec {a b : Poly n} (ha : Defined k a) (hb : Defined k b) :
    Defined k (gcd a b).1 ∧ Defined k (gcd a b).2.1 ∧ Defined k (gcd a b).2.2 ∧
      model k (gcd a b).2.1 * model k a + model k (gcd a b).2.2 * model k b =
        model k (gcd a b).1 ∧
      model k (gcd a b).1 ∣ model k a ∧ model k (gcd a b).1 ∣ model k b :=
  gcdWith_spec (Term.norm_sound n) ha hb

/-- Lowest terms: the same quotient, with coprime numerator and denominator. -/
theorem reduce_spec {a b : Poly n} (ha : Defined k a) (hb : Defined k b)
    (bn : model k b ≠ 0) :
    Defined k (reduce a b).1 ∧ Defined k (reduce a b).2 ∧ model k (reduce a b).2 ≠ 0 ∧
      IsCoprime (model k (reduce a b).1) (model k (reduce a b).2) ∧
      model k a * model k (reduce a b).2 = model k (reduce a b).1 * model k b :=
  reduceWith_spec (Term.norm_sound n) ha hb bn

end Poly

end SympyProofs.Calculus.Risch
