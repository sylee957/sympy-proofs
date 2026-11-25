module

public import SympyProofs.Calculus.Risch.Program.Term
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Data.Fin.Tuple.Basic

/-! The field presented by a tower of depth `n` over a constant field `k` is the field of
rational functions `k(θ₀, …, θₙ₋₁)`, built one generator at a time. A term denotes an
element of it. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

/-- A field of characteristic zero together with its instances. -/
structure Ground where
  carrier : Type
  [field : Field carrier]
  [charZero : CharZero carrier]

attribute [instance] Ground.field Ground.charZero

noncomputable abbrev ground (k : Type) [Field k] [CharZero k] (n : ℕ) : Ground :=
  Nat.rec ⟨k⟩ (fun _ F => ⟨RatFunc F.carrier⟩) n

/-- The field of rational functions in `n` generators over `k`. -/
abbrev K (k : Type) [Field k] [CharZero k] (n : ℕ) : Type := (ground k n).carrier

variable (k : Type) [Field k] [CharZero k]

/-- The generators as elements of the field of depth `n`. -/
noncomputable def gens : (n : ℕ) → Fin n → K k n
  | 0 => Fin.elim0
  | n + 1 => Fin.lastCases RatFunc.X fun i => RatFunc.C (gens n i)

/-- The constants as elements of the field of depth `n`. -/
noncomputable def constHom : (n : ℕ) → k →+* K k n
  | 0 => RingHom.id k
  | n + 1 => (RatFunc.C : K k n →+* RatFunc (K k n)).comp (constHom n)

namespace Term

variable {n : ℕ}

/-- The value of a term in a field, given values for the generators. -/
def eval {F : Type*} [Field F] (g : Fin n → F) : Term n → F
  | .const q => (q : F)
  | .gen i => g i
  | .neg a => -(a.eval g)
  | .add a b => a.eval g + b.eval g
  | .sub a b => a.eval g - b.eval g
  | .mul a b => a.eval g * b.eval g
  | .div a b => a.eval g / b.eval g

/-- No quotient in the term has a vanishing denominator. -/
def Defined {F : Type*} [Field F] (g : Fin n → F) : Term n → Prop
  | .const _ | .gen _ => True
  | .neg a => a.Defined g
  | .add a b | .sub a b | .mul a b => a.Defined g ∧ b.Defined g
  | .div a b => a.Defined g ∧ b.Defined g ∧ b.eval g ≠ 0

/-- The element of the field of depth `n` that a term denotes. -/
noncomputable def value (e : Term n) : K k n := e.eval (gens k n)

/-- The term is defined in the field of depth `n`: no denominator in it vanishes. -/
def InDomain (e : Term n) : Prop := e.Defined (gens k n)

variable {k}

@[simp] theorem eval_weaken {F : Type*} [Field F] (g : Fin n → F) (top : F) (e : Term n) :
    e.weaken.eval (Fin.lastCases top g) = e.eval g := by
  induction e <;> simp [weaken, eval, *]

@[simp] theorem defined_weaken {F : Type*} [Field F] (g : Fin n → F) (top : F) (e : Term n) :
    e.weaken.Defined (Fin.lastCases top g) ↔ e.Defined g := by
  induction e <;> simp [weaken, Defined, *]

/-- A term denotes the same element one level up. -/
@[simp] theorem value_weaken (e : Term n) : value k e.weaken = RatFunc.C (value k e) := by
  induction e with
  | const q => simp [value, weaken, eval]
  | gen i => simp [value, weaken, eval, gens]
  | neg a ih => simpa [value, weaken, eval] using congrArg Neg.neg ih
  | add a b ha hb => simpa [value, weaken, eval] using congrArg₂ (· + ·) ha hb
  | sub a b ha hb => simpa [value, weaken, eval] using congrArg₂ (· - ·) ha hb
  | mul a b ha hb => simpa [value, weaken, eval] using congrArg₂ (· * ·) ha hb
  | div a b ha hb => simpa [value, weaken, eval] using congrArg₂ (· / ·) ha hb

/-- A term is defined one level up exactly when it is defined. -/
@[simp] theorem inDomain_weaken (e : Term n) : InDomain k e.weaken ↔ InDomain k e := by
  induction e with
  | const | gen => exact Iff.rfl
  | neg a h => exact h
  | add a b ha hb | sub a b ha hb | mul a b ha hb => exact and_congr ha hb
  | div a b ha hb =>
    change InDomain k a.weaken ∧ InDomain k b.weaken ∧ value k b.weaken ≠ 0 ↔
      InDomain k a ∧ InDomain k b ∧ value k b ≠ 0
    simp [ha, hb]

end Term

variable {k} {n : ℕ}

theorem constHom_succ (c : k) : constHom k (n + 1) c = RatFunc.C (constHom k n c) := rfl

theorem constHom_ratCast (q : ℚ) : constHom k n (q : k) = (q : K k n) := map_ratCast _ q

/-- A combination of the values of terms with constant coefficients. -/
noncomputable def linComb (cs : List k) (as : List (Term n)) : K k n :=
  (List.zipWith (fun (c : k) (a : Term n) => constHom k n c * Term.value k a) cs as).sum

theorem linComb_cons (c : k) (cs : List k) (a : Term n) (as : List (Term n)) :
    linComb (c :: cs) (a :: as) = constHom k n c * Term.value k a + linComb cs as := by
  simp [linComb]

theorem linComb_nil_left (as : List (Term n)) : linComb ([] : List k) as = 0 := by
  simp [linComb]

theorem linComb_nil_right (cs : List k) : linComb cs ([] : List (Term n)) = 0 := by
  simp [linComb]

theorem linComb_append {p q : List k} {as bs : List (Term n)} (h : p.length = as.length) :
    linComb (p ++ q) (as ++ bs) = linComb p as + linComb q bs := by
  simp [linComb, List.zipWith_append h]

end SympyProofs.Calculus.Risch
