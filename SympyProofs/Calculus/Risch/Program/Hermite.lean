module

public import SympyProofs.Calculus.Risch.Program.Deriv

/-! Hermite reduction for a fraction `A / D` whose denominator has only normal prime
factors. The denominator is written `Ds * Dm` with `Ds` its squarefree part. Each step
subtracts the derivative of `B / Dm` and replaces `Dm` by its greatest common divisor with
its derivative, until `Dm` is a constant. Only greatest common divisors are used.

At an exponential step the generator is not a normal prime, so the power of the generator
in the denominator is split off first by a partial fraction. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {n : Nat}

namespace Hermite

open Poly

/-- Divide every coefficient by a term. -/
def scaleInv (c : Term n) (p : Poly n) : Poly n := p.map fun x => .div x c

/-- One step: the numerator `B` of the exact part, the new numerator, and the new `Dm`. -/
def step (t : Tower (n + 1)) (Ds A Dm : Poly n) : Poly n × Poly n × Poly n :=
  let Dm2 := trim (norm (gcd Dm (formalD Dm)).1)
  let Dms := trim (norm (quot Dm Dm2))
  let K := quot Ds Dms
  let E := neg (quot (mul Ds (der t Dm)) Dm)
  let bz := gcd E Dms
  let c := coeff bz.1 0
  let B := norm (scaleInv c (mul A bz.2.1))
  let Cq := scaleInv c (mul A bz.2.2)
  (B, norm (sub Cq (mul (der t B) K)), Dm2)

/-- Repeat the step until the repeated part is constant. -/
def loop (t : Tower (n + 1)) (Ds : Poly n) :
    Nat → Term (n + 1) → Poly n → Poly n → Term (n + 1) × Poly n × Poly n
  | 0, g, A, Dm => (g, A, Dm)
  | fuel + 1, g, A, Dm =>
    if Nat.ble Dm.length 1 then (g, A, Dm)
    else loop t Ds fuel (.add g (.div (toTerm (step t Ds A Dm).1) (toTerm Dm)))
      (step t Ds A Dm).2.1 (step t Ds A Dm).2.2

/-- Hermite reduction of `A / D`: an exact part, and a numerator over the squarefree part
of `D`. -/
def hermite (t : Tower (n + 1)) (A D : Poly n) : Term (n + 1) × Poly n × Poly n :=
  let Dm := trim (norm (gcd D (formalD D)).1)
  let Ds := trim (norm (quot D Dm))
  let out := loop t Ds Dm.length (.const 0) A Dm
  (out.1, norm (scaleInv (coeff out.2.2 0) out.2.1), Ds)

/-- The number of vanishing coefficients of lowest degree. -/
def lowZeros : Poly n → Nat
  | [] => 0
  | c :: cs => if c.isZero then lowZeros cs + 1 else 0

/-- The order of the pole at the generator that is split off: none at a primitive step,
where the generator is a normal prime. -/
def order : Tower (n + 1) → Poly n → Nat
  | .prim _ _, _ => 0
  | .exp _ _, D => lowZeros D

/-- The data of the reduction of a term `f`: the order `k` at the generator, an exact part
`g`, a fraction `Ar / Dr` in lowest terms with squarefree denominator, and a numerator `L1`
over the `k`-th power of the generator, with
`f = g′ + Ar / Dr + L1 / θᵏ`. -/
structure Reduced (n : Nat) where
  k : Nat
  g : Term (n + 1)
  Ar : Poly n
  Dr : Poly n
  L1 : Poly n

def reduceTerm (t : Tower (n + 1)) (f : Term (n + 1)) : Reduced n :=
  let fr := ofTerm f
  let D := trim (norm fr.2)
  let k := order t D
  let Dn := trim (D.drop k)
  let bz := gcd (mono k (.const 1)) Dn
  let c := coeff bz.1 0
  let hm := hermite t (norm (scaleInv c (mul fr.1 bz.2.1))) Dn
  let rd := reduce hm.2.1 hm.2.2
  ⟨k, hm.1, norm rd.1, trim (norm rd.2), norm (scaleInv c (mul fr.1 bz.2.2))⟩

end Hermite

end SympyProofs.Calculus.Risch
