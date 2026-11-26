# Antiderivative

A verified elementary integrator for towers of primitive, exponential and tangent generators.
The same `integrate` call handles all three and returns an answer in the original
coordinates and coefficient field. This is a rewrite of the earlier verified Risch algorithm
in `Calculus/Risch`, which was removed once this development proved the same theorems and
verified more of the benchmark. Its mathematics is reused in `Extension/`; its programs are
not.

The implementation and its verified milestones are tracked in [Plan and status](#plan-and-status).

## The idea

A field element is an element of a type that is a `Field`, not a term to be normalized. The
field of a tower with `n` generators over a ring `R` of constants is one type,

```lean
K R n      -- fractions of polynomials in n variables over R
```

Its elements are single fractions of two sparse polynomials in all the generators at once,
with coefficients in `R`. All coefficient arithmetic is arithmetic of `R`: for `R = ℤ`,
integers. This is the representation that made the earlier implementation fast, given a
`Field` instance instead of a normalizer.

The algorithm of one step works with polynomials in the newest generator over the field
below, `Poly (K R n)`, and is written for an arbitrary field. An element of `K R (n + 1)` is
split into such polynomials on the way in and joined on the way out.

## Principles

1. **Mathlib's classes are the interface.** Programs are written over `Field`, `CommRing`,
   `IsDomain`, `EuclideanDomain`, `NormalizedGCDMonoid`, `Algebra`, `DecidableEq`, `Div`.
2. **Override by instance, never by hook.** There is no class whose purpose is to let one
   type replace a default algorithm, and no interface kept for a second implementation that
   does not exist. A faster operation is the operation of a type with its own lawful
   instance, as `Rat.add` is to `Field ℚ`.
3. **The solver is total.** Recursion is structural or on fuel. At each level, the
   polynomial routines receive the derivative and the primitive or exponential step data.
4. **Arithmetic data carries no proofs.** A polynomial is a list and a fraction is a pair.
   A vector of fixed length is a list and an index below `n` is a number. The arithmetic types
   are quotients of these data, as `Multiset` is a quotient of `List`. Values carry only the
   data at run time, and the instances are lawful. Where Mathlib's interface asks for a
   bundled value it is given (a ring homomorphism, a unit).
5. **A class of our own carries data only.** Constant-field operations are `NatBound`,
   `IntegerRelations`, and `ConstantFactors`. Each has a separate class of laws that only
   theorems mention, as `LawfulBEq` is to `BEq`.
6. **Propositions live in `Proof/`.** A file of programs contains no theorem. The proof that
   an operation respects a quotient is next to the instance, not in the operation.
7. **A field element is always defined.** No theorem carries a hypothesis that denominators
   do not vanish.
8. **No type is defined by recursion.** `K R n` is one type former applied to a number. It is
   not built from `K R (n - 1)`, so its instances exist for all `n` at once and `simp`, `rw`
   and instance search treat it as any other type.
9. **Fractions are not nested.** A field element has one numerator and one denominator. A
   fraction whose coefficients are fractions makes every operation a greatest common divisor
   one level down, and Euclid's algorithm on top of that does not finish.
10. **One recursion, no special cases.** As in Risch (1969): the Main Theorem is a
    simultaneous induction on the tower of (a) elementary integration and (b) the parametric
    equation `y′ + f y = Σ cᵢ gᵢ`. Generality and completeness come before speed.

## Layers

| Directory | Contents | Imports |
| --- | --- | --- |
| `Algebra/` | the computable types `Poly R`, `MPoly n R`, `K R n`, with their Mathlib instances and the equivalences with Mathlib's `Polynomial`, `MvPolynomial`, `FractionRing` | Mathlib |
| `Program/` | tower arithmetic, integration, parametric solving, and admissibility | `Algebra/` |
| `Spec/` | the model of a tower, values, and what the theorems say | Mathlib, the above |
| `Extension/` | lemmas about `F[X]` and `RatFunc F` over an arbitrary differential field `F`: the quotient rule, logarithmic derivatives, Hermite reduction, simple poles and residues, poles of solutions, the constants of a primitive or exponential, and Liouville forms | Mathlib |
| `Proof/` | the specification of each program | all of the above |
| [../AntiderivativeFrontend/](../AntiderivativeFrontend/) | expression trees, tower construction, and proofs of the frontend decision criteria | native tower operations and their correctness proofs |

In `Algebra/`, each type has a file `Raw.lean` with the plain data and its operations and no
theorem, and a file `Basic.lean` with the quotient, the lifted operations, the proofs that
they respect the quotient, and the instances.

## Algebra

Namespace `SympyProofs.Calculus.Antiderivative`.

### `Poly R`: polynomials in one variable

```lean
abbrev Poly.Raw (R : Type) := List R          -- coefficients from degree zero
def Poly (R : Type) [Zero R] := Quotient …    -- lists with the same coefficients are equal
```

`CommRing (Poly R)` with `Poly.equiv : Poly R ≃+* R[X]`; over a field, `Div`, `Mod`,
`EuclideanDomain (Poly F)` and a monic `NormalizedGCDMonoid (Poly F)`. `Poly.map` takes any
function, so a derivation is mapped over the coefficients with no proof. This is the type the
step algorithm computes in. It was written and reviewed for an earlier attempt and is carried
over as it is.

### `MPoly n R`: polynomials in `n` variables

```lean
/-- A monomial: the exponent of each variable, from variable zero. Missing ones are zero. -/
abbrev Mono := List Nat

/-- Terms, each a monomial with its coefficient. A monomial may occur more than once. -/
abbrev MPoly.Raw (R : Type) := List (Mono × R)

/-- Two lists are the same polynomial in `n` variables when they have the same coefficient
at every monomial in the first `n` variables. Terms with a later variable count for
nothing. -/
def MPoly (n : ℕ) (R : Type) [AddCommMonoid R] := Quotient …
```

The number `n` is not in the data. It only says which terms count, so the inclusion
`MPoly n R → MPoly (n + 1) R` does nothing at run time beyond dropping terms that did not
count.

Operations on the plain lists (`MPoly/Raw.lean`): a normal form (terms sorted, equal
monomials merged, zeros dropped), sum, product, negation, partial derivative, the variable
`i`, constants, exact division (`some q` only when `q` times the divisor gives the dividend
back), and a common divisor of two polynomials. Operations return normal forms, for speed;
nothing relies on it.

Instances: `CommRing (MPoly n R)` for `[CommRing R] [DecidableEq R]`, `DecidableEq`,
`Algebra R (MPoly n R)`, `IsDomain` when `R` is, and
`MPoly.equiv : MPoly n R ≃+* MvPolynomial (Fin n) R`.

**The common divisor is not specified.** It is a function on plain lists: the primitive
Euclidean algorithm in the last variable, over the greatest common divisor of `R`. Nothing is
proved about it and no instance offers it, because the only place it is used checks its
answer by exact division (below). A faster one replaces it with no proof to redo.

### `K R n`: the field of a tower

```lean
/-- A numerator and a denominator. A vanishing denominator stands for zero. -/
structure K.Raw (R : Type) where
  num : MPoly.Raw R
  den : MPoly.Raw R

/-- Two pairs are the same element when they have the same value in the field of fractions
of the polynomials in `n` variables. -/
def K (R : Type) (n : ℕ) [CommRing R] [IsDomain R] := Quotient …
```

A sum or a product computes the common divisor of what it is about to cancel, divides both
by it exactly, and keeps the pair it had if either division fails. So the value never depends
on the common divisor being right.

Instances, for `[CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]`:
`Field (K R n)`, `DecidableEq` (by cross multiplication, at once when a numerator is zero or
the denominators agree), `Algebra (MPoly n R) (K R n)`, `IsFractionRing (MPoly n R) (K R n)`,
`CharZero` when `R` has it, and
`K.equiv : K R n ≃+* FractionRing (MvPolynomial (Fin n) R)`.

Functions between heights, all ring homomorphisms and none recursive:

| Function | What it is |
| --- | --- |
| `K.lift : K R n →+* K R (n + 1)` | an element of the field below |
| `K.gen : K R (n + 1)` | the newest generator |
| `K.ofConst : K R 0 →+* K R n` | a constant |
| `K.const? : K R n → Option (K R 0)` | the constant an element is, if it is one |
| `K.split : K R (n + 1) → Poly (K R n) × Poly (K R n)` | numerator and denominator as polynomials in the newest generator |
| `K.join : Poly (K R n) → Poly (K R n) → K R (n + 1)` | their quotient |
| `K.der : List (K R n) → K R n → K R n` | the derivation that sends generator `i` to the `i`th element of the list and the constants to zero: `Σ ∂f/∂xᵢ · vᵢ` |

### Constants

The ring `R` is a parameter. The field of constants of a tower is `K R 0`, the fractions of
`R`.

| `R` | Constants |
| --- | --- |
| `ℤ` | `ℚ` |
| a field `Γ` (a number field, `ℚ` itself) | `Γ` |
| the Gaussian integers | `ℚ(i)` |
| `Parameters m = K ℤ m` | `ℚ(γ₁, …, γ_m)` |

A field is a ring with a trivial greatest common divisor and exact division, so any field of
constants is used directly. A ring is allowed, and not only a field, for speed: over `ℤ` every
coefficient is an integer and the denominators are gathered in one polynomial. In the earlier
implementation, computing over `ℚ` with no integer ring lost 553 of 4,272 integrals on the
Hebisch suite.

### Effective operations on constants

```lean
/-- Bounds on natural numbers in a field of constants. -/
class NatBound (Γ : Type) [Zero Γ] where
  /-- An upper bound for the natural number the element is, if it is one. -/
  natBound : Γ → ℕ
  /-- An upper bound for the natural numbers that are roots of a nonzero polynomial. -/
  natRootBound : Poly Γ → ℕ
```

The degree of a solution at
a primitive step and the exponents at an exponential step are natural numbers determined by
equations over the constants. Its laws are in `Spec/NatBound.lean`:

```lean
class LawfulNatBound (Γ : Type) [Field Γ] [DecidableEq Γ] [NatBound Γ] : Prop where
  natBound_spec : ∀ (c : Γ) (m : ℕ), c = m → m ≤ NatBound.natBound c
  natRootBound_spec : ∀ (p : Poly Γ) (m : ℕ), p ≠ 0 → p.eval (m : Γ) = 0 →
    m ≤ NatBound.natRootBound p
```

The programs ask for `[NatBound (K R 0)]` and the theorems also for
`[LawfulNatBound (K R 0)]`. Instances: `K ℤ 0`, where `natBound` is exact and `natRootBound`
is Cauchy's estimate; and `K Γ 0` for a field `Γ` that has them.

The second interface, `IntegerRelations.rows : List Γ → List (List ℚ)`, gives rational
equations for the vectors `q` satisfying `Σ qᵢ cᵢ = 0`. Its law requires equivalence in both
directions and one column per input. At higher levels `logRelations` describes rational
combinations that become logarithmic derivatives after multiplication by a positive integer.
These rational equations recover the exceptional integer exponents in the degree bound,
including when an irrational constant multiplies a logarithmic derivative.

`ConstantFactors.factors` returns the monic irreducible factors of one nonzero univariate
polynomial over the ground constants. Their multiplicities and product are specified in
`Spec/Factor.lean`. Clearing denominators and Kronecker substitution reduce factorization
at positive height to this ground operation. Each irreducible normal denominator factor
contributes one rational residue variable, eliminated from the final rows.

## Towers

```lean
inductive Gen (F : Type)
  | prim (b : F)  -- θ′ = b
  | exp (u : F)   -- θ′ = u′ θ
  | tan (u : F)   -- θ′ = u′ (1 + θ²)

inductive Tower (R : Type) … : ℕ → Type
  | base : Tower R 0
  | step {n} (t : Tower R n) (g : Gen (K R n)) : Tower R (n + 1)
```

`Tower.gens t : List (K R n)` is the derivative of each generator, as an element of the field
of the whole tower, and the derivation of the tower is `K.der t.gens`. It is one formula for
every height, not a recursion through the fields.

## Programs

The frontend accepts a complete `Expr` through `e.toTower` or a series of operations
through `TowerBuilder`. Each operation can add a coefficient, adjoin a generator, or
remove a requirement by cancellation. A compatible operation continues from the preceding
tower. If its coefficient field or exponential scale changes, the builder reevaluates in
the new coordinates. Both entry points produce the same kind of tower and field element
for `Tower.integrate`.
[Expression-to-tower conversion](../AntiderivativeFrontend/ToTower.lean)

For example, an unsupported intermediate `log(pi)` can be kept in a script. Applying
`exp` recovers the positive argument, and subtracting `pi` gives an unconditional rational
zero. The builder retains denominator checks when the available identities cannot prove
the divisor nonzero.

```lean
import SympyProofs.Calculus.AntiderivativeFrontend.Status
open SympyProofs.Calculus.Antiderivative.Frontend

example : Bool := Id.run do
  let p := TowerBuilder.ofExpr .pi
  let lp := p.apply Expr.log
  let recovered := lp.apply Expr.exp
  let zero := recovered.combine Expr.sub p
  return !lp.domainBuilt && recovered.decisionStatus == .conditional [.pi] &&
    zero.decisionStatus.unconditionalDecision
```

`b.domainBuilt` tests whether the current operations yielded a tower and value.
`b.decisionStatus` also checks admissibility. Its Boolean projections describe what
can be decided for the resulting field element.

| Status | `domainBuilt` | `formalDecision` | `unconditionalDecision` |
| --- | --- | --- | --- |
| `incomplete reason` | false | false | false |
| `inadmissible` | true | false | false |
| `conditional parameters` | true | true | false |
| `ready` | true | true | true |

For example, `exp(x**2)` has status `ready` and the integrator returns
`nonelementary`. The status describes the applicability of the decision procedure.

`Input.formalDecisionSpec_of_formalDecision` proves soundness and completeness on the
constructed tower over the algebraic closure of its formal coefficients.
`Input.namedDecisionSpec_of_formalDecision` gives the specification for the named
complex values. In the conditional case it takes a proof of their joint independence.
Analytic interpretation of the source still requires a realization and regular branches.
[Decision tests](../AntiderivativeFrontend/Status.lean) · [Decision theorem](../AntiderivativeFrontend/Proof/Status.lean)

The constructors `.i` and `.pi` denote the imaginary unit and π. Rational inputs use ℚ,
and adjoining `I` uses ℚ(i) with the exact relation `I² = -1`. For rational exponential
arguments with common denominator D, one parameter represents exp(1/D) and integer powers
give the other exponentials. Logs of positive rationals use sums and differences of prime
logarithms. For example, log(8/9) uses 3 log(2) − 2 log(3). The frontend can also adjoin
exp(exp(q)) for nonzero rational q and log(log(p)) for prime p. It rewrites
log(2 log(2)) as log(2) + log(log(2)), so both spellings use the same coefficients.
An exponential whose argument is a rational linear combination of monomials
πᵏ exp(r) can add a coefficient for each distinct monomial. For example, exp(π/2)
and exp(2π) share the single parameter exp(π/2), and the second uses its fourth power.
When exp(x) and exp(x + π) occur together, the builder can use one differential
generator for exp(x) and the coefficient exp(π) for their ratio.
[Constant selection](../AntiderivativeFrontend/Constants.lean)

`Input.assumptions` lists the normalized real constants used as independent formal parameters.
An empty list requires no parameter specialization. For a nonempty list, the benchmark
reports the names and marks a successful derivative check as verified under assumptions.
`(-x+1)*ln(2)*exp(2-x)+2*x+6` is one such Hebisch input. Its primitive is
`x*(exp(2-x)*ln(2)+x+6)`, and the benchmark reports the single parameter `log(2)`.
`ConstantPlan.Independent` states the required joint algebraic independence over ℚ.
Given that proof, Lean constructs an embedding sending each parameter and the imaginary
unit to their intended values in ℂ. Inputs using π as a free coefficient currently carry
this condition. The integration proofs and executable derivative check start at the
constructed tower and its field element. An unmodeled constant function returns a reason.
[Specialization of named coefficients](../AntiderivativeFrontend/Proof/Constants.lean)

Check `t.admissible` once for the tower. On success, use `t.integrate f` and `t.solve b gs`
in the same coordinates and coefficient field. A negative integration decision on an
admissible tower excludes an elementary primitive.

```lean
import SympyProofs.Calculus.Antiderivative
import SympyProofs.Calculus.AntiderivativeFrontend.ToTower
open SympyProofs.Calculus.Antiderivative

example : Bool := Id.run do
  let e : Frontend.Expr := .add (.num 1) (.pow (.tan .var) (.num 2))
  let .ok (.rational t f) := e.toTower | return false
  unless t.admissible do return false
  let .elementary a := t.integrate f | return false
  let (ys, _) := t.solve 0 []  -- solutions of y′ = 0
  return a.differentiate t == some f && ys.any fun y => y != 0 && t.D y == 0
```

What the level of height `n` gives the level above is a record of functions: the two parts of
the Main Theorem and the linear relations of logarithmic derivatives.

```lean
structure Level (R : Type) (n : ℕ) … where
  integrate : K R n → Result R n                                   -- part (a)
  solve : K R n → List (K R n) → List (K R n) × List (List (K R 0))  -- part (b)
  elementaryBasis : List (K R n) → List (List (K R 0) × Answer R n)
  logRelations : List (K R n) → List (List ℚ)
```

In `Tower R n`, a generator can be primitive, exponential or tangent. The solver recurses
on the given tower. At a tangent step it uses an exponential coordinate so that the
polynomial velocity has degree at most one, as required by the degree bounds.

**The algorithm of a step** is the one of the earlier implementation: lowest terms, special
part, Hermite reduction, residues by a resultant over the constants with one more constant
adjoined, the polynomial part by part (b) one level down. It has two layers.

* `Program/Step/` works in `Poly F` for an arbitrary field `F` with a derivation given as a
  function `D : F → F` and the derivative of the generator `Dθ : Poly F`: lowest terms,
  squarefree factors, Hermite reduction, the resultant, the remainder sequences. It never
  mentions `K`.
* `Program/Level.lean` splits an element of `K R (n + 1)` into polynomials over `K R n`, runs
  those, calls the level below for what they ask about coefficients, and joins the result.

At a primitive step the last equation asks which combinations of the residual and `b`
have elementary primitives below. The coordinates and primitives in `elementaryBasis`
recover the undetermined constant coefficient of the new generator.

**Kinds of generator.** Hermite reduction, the residue criterion and the assembly of the
answer use only `Dθ`. What depends on the kind is kept in one file per kind
(`Program/Kind/Prim.lean`, `Program/Kind/Exp.lean`), behind these functions:

| Function | Primitive | Exponential |
| --- | --- | --- |
| the special polynomials | none | `θ` |
| integration of the part with special denominator and of the polynomial part | by `solve` one level down, degree by degree | by `solve`, one equation per power, negative powers included |
| in part (b): the bound on the special denominator | none | from `logRelations` |
| in part (b): the bound on the degree, and the equation of each coefficient | from `solve` one level down | from `logRelations` |
| admissibility of a new generator | `b` has no primitive below | no positive integer multiple of `u′` is a logarithmic derivative below |

## Extending

* **A field of constants** is a ring `R` with the Mathlib classes above, with `NatBound`, `IntegerRelations`,
  `ConstantFactors`, and their laws for `K R 0`.
* **A tangent** is the `.tan u` case of the public `Gen`, with `Dθ = u′ (θ² + 1)`.
  The recursion uses `θ = −i(z−1)/(z+1)` and `z = exp(2iu)`. The substitution applies
  to later generator arguments, integrands and differential equations. Its inverse expresses
  the primitive, its logarithms and the solution generators in the original variables.
  When −1 is a square in the constant field, a factor of `X² + 1` supplies the imaginary unit.
  Otherwise the calculation takes place over the quadratic constant extension and descends
  each answer to the original constants.
* **An algebraic generator** is not a variable: its field is a quotient of `Poly (K R n)`, not
  `K R (n + 1)`. It needs a second kind of step. Nothing here assumes it, and `Program/Step/`
  is reusable for it because it only knows `Poly F`.

## Specification

**The model.** For a field `k` of characteristic zero with
`[Algebra R k] [FaithfulSMul R k]`, the model of the field of height `n` is `M k n := FractionRing (MvPolynomial (Fin n) k)`, again one type former
applied to a number. `val : K R n →+* M k n` maps the coefficients. It is injective, and it
commutes with `K.lift`, `K.gen`, constants and `K.der`.

**One step in the model.** `M k (n + 1)` is the field of rational functions in one variable
over `M k n` (`MvPolynomial.finSuccEquiv` and fraction fields). Through that isomorphism,
`K.split` gives Mathlib's `RatFunc.num` and `RatFunc.denom`, and the derivation of the tower
is the extension of the derivation below by `Dθ`. This is proved once, and is where the lemmas
of `Extension/` apply: they are about `F[X]` and `RatFunc F` for an arbitrary differential
field `F`.

**The theorems** are those of the earlier implementation, with field elements in place of
terms. The work is one theorem per step,

```lean
theorem stepLevel_spec (t : Tower R n) (g : ReducedGen (K R n)) (L : Level R n)
    (ht : t.Admissible k) (hg : g.Admissible k t) (hL : L.Spec k t) :
    (stepLevel t.D g L).Spec k (t.step g)
```

for a primitive or exponential extension. The mixed-tower theorem combines this induction
with the change of tangent coordinates and descent. The public results are
`integrate_sound`, `integrate_complete` and `solve_spec`. Their hypotheses use
`t.Admissible k`, meaning that the kernel of the native derivative consists exactly of the
model constants. `t.admissible_iff k` proves that `t.admissible = true` is equivalent to
this hypothesis.
[Main proofs](Proof/Integrate.lean) · [Tower semantics](Spec/Integration.lean)

For every admissible tower `t` of height `n`, every algebraically closed model field `k`
of characteristic zero, and every `f : K R n`,

* **Soundness.** If `integrate t f = .elementary a`, the derivative of the value of `a` is
  `val k f`.
* **Completeness.** If `integrate t f = .nonelementary`, `val k f` has no elementary integral
  over `M k n`.
* **Part (b).** `solve` returns exactly the solutions.
* `integrate_iff_elementary` characterizes success by the existence of a Liouville form.
  `integrate_no_primitive` excludes a primitive in every elementary differential extension
  after a negative result. [Differential consequences](Proof/IntegrationConsequences.lean)
* `integrate_hasDerivAt` gives the complex derivative on regular branches.
  `integrate_no_function_in_extension` excludes analytic primitives on nonempty open sets
  with nonzero exponential coordinates and tangent coordinates different from `±i`.
  [Analytic consequences](Proof/Corollaries.lean)

## What was tried and is avoided

An earlier attempt, written and then discarded, found these by running into them.

* **Fields nested one in another**, `Frac (Poly (Frac (Poly Γ)))`. With three generators the
  derivative of a product of two small elements did not finish in 100 seconds: the remainders
  of Euclid's algorithm have coefficients that are fractions one level down, and they grow at
  each step.
* **A type defined by recursion on the height.** It needed a bundle of a type with its
  instances, and `simp` and `rw` could not see through it.
* **Instances that grow with the tower.** A field instance built from the instances one level
  down passed the size limit of instance search at two generators.
* **A zero in the type of a polynomial that is found by two routes.** The type `Poly R`
  mentions the zero of `R`. A small instance `Zero (F)` beside `Field F` makes matching need an
  instance search inside unification. A type gets its zero from one instance only.
* **Scalars from `ℚ`** on a field of fractions over a `ℚ`-algebra: two actions that are equal
  but not by definition, as for Mathlib's `FractionRing`. Constants are written with
  `algebraMap`.
* **The type `Derivation ℤ (RatFunc G) (RatFunc G)` written out**, which picks a `ℤ`-algebra
  that is equal to the usual one but not by definition. A derivation of a field `G` is written
  `Der G`, an abbreviation of `Derivation ℤ G G` for a variable `G`.
* **Proof fields in data, a class with its laws inside, a class for a second implementation,
  a class to override a default.** See the principles.

## Speed

The representation is the one of the earlier implementation: a quotient of two polynomials in
all the generators, cancelled by a common divisor that is checked and not trusted. Before the
algorithm was ported, a compiled program timed sums, products, inverses and derivatives in
`K ℤ n` for `n ≤ 3` against the same operations there, and checked that the outputs agree. In
one local run the largest time ratio was 1.79 (multiplication at height one). At height three
the ratios for addition, multiplication, inversion and differentiation were 0.88, 0.71, 0.002
and 0.16. The program was removed with the earlier implementation.

Equality of two field elements is a cross multiplication when the cheap cases do not answer.
The algorithm mostly compares with zero, which is a test on the numerator.

## Conventions

* Lean 4 with the module system: `module`, `public import`, `@[expose] public section`.
* No `sorry`, no `axiom`, no `native_decide`, no `set_option` (no linter silencing, no
  heartbeat limits), no `attribute [local irreducible]`.
* No warnings. An instance argument that a theorem does not use is removed with
  `omit … in` or by declaring the variable later.
* Lines of at most 100 characters.
* `Program/` files and `Raw.lean` files define data types and functions only: no theorem, no
  proposition in a type, no proof argument.
* Every definition and every main theorem has a docstring that says what it is, in plain
  words.
* Tests are small and fast: one case per run with a hard time limit. A small case that takes
  more than a second is profiled, not waited for.
* A module is built by name. The whole project is not built while others are working.

## Plan and status

| Stage | Contents | Status |
| --- | --- | --- |
| 1 | `Algebra/Poly`: carried over from the earlier attempt (the lists, the quotient, the ring, division and the greatest common divisor over a field) | Implemented and checked. |
| 2 | `Algebra/MPoly`: the lists of terms, the quotient, the ring, the equivalence with `MvPolynomial (Fin n) R`; exact division and the common divisor as plain functions | Implemented and checked. |
| 3 | `Algebra/K`: the pairs, the quotient, the field, the equivalence with `FractionRing`; `lift`, `gen`, `ofConst`, `const?`, `split`, `join`, `der`; `NatBound` for `K ℤ 0` | Implemented and checked, including constant recognition and the split/join laws. |
| 4 | the measurement of `K ℤ n` against the earlier implementation, compiled | Passed at all four heights; see [Speed](#speed). |
| 5 | `Program/Tower.lean`; `Spec/`: the model `M k n`, `val`, the step in the model | Implemented and checked, including transport of the derivation. |
| 6 | `Program/`: `Step/`, the two kinds, `Level`, `integrate`, `solve`, `admissible`; a benchmark driver | The public operations accept primitive, exponential and tangent generators and return answers in the original coordinates. |
| 7 | The simultaneous induction over primitive and exponential towers | Lean checks `stepLevel_spec`, `Tower.level_spec`, `Tower.admissible_iff`, `integrate_sound`, `integrate_complete` and `solve_spec`. |
| 8 | Analytic meaning over ℂ | Lean checks the derivative at a regular point and the converse on nonempty open sets, including elementary differential field extensions. |
| 9 | Parameter and Gaussian constants, mixed tangent towers | Verified parameter and quadratic constant operations, native tangent admissibility and poles, and integration and parametric solving with descent to the original coefficient field. |

Import `SympyProofs.Calculus.Antiderivative` for the public library. The joint theorem for all generator kinds is `Tower.operations_spec`.
[Integration proofs](Proof/Integrate.lean). The [differential consequences](Proof/IntegrationConsequences.lean)
cover the answer language and elementary field extensions. The [analytic results](Proof/Corollaries.lean)
give soundness and completeness for regular complex realizations. The executable
[differentiation theorem](Proof/Verify.lean) independently checks successful answers,
including logarithmic sums with repeated or nonmonic moduli.

`Parameters m` implements ℚ(γ₁,…,γₘ). `Gaussian` implements ℚ(i) with exact rational real
and imaginary coordinates and a specified embedding in ℂ. For either field, Lean checks
natural root bounds, rational relations, and factorization. For a computable field without i,
quadratic factorization uses one translate, a norm over the original field, and polynomial gcds.

Integration and parametric solving use the same tangent reduction for every supported
coefficient field. A returned primitive verifies with `a.differentiate t` using the original tower
velocities.
[Public operations](Program/Integrate.lean) · [Correctness](Proof/Integrate.lean)

Build the integrator with `lake build antiderivative-integral`. The benchmark tokenizes and
parses each input string into a `Frontend.Expr`. It prints candidate coefficients before
construction and the final specialization assumptions once the tower is built. Both
`log(x)` and `ln(x)` parse as `.log .var`. The JSON Lines record includes the domain
status and any final assumptions. A construction timeout retains the available candidates.
[Benchmark parser](../AntiderivativeBench/Parser.lean)

For example,
`.lake/build/bin/antiderivative-integral '1/(1+x**2)'` checks a logarithmic root sum by
differentiating it exactly. The frontend accepts rational expressions in `x` with integer
powers, exponentials, logarithms and tangents. For example,
`.lake/build/bin/antiderivative-integral '1+tan(x)**2'` checks a primitive on a rational
tangent tower. The `--contract tangent` case checks a Gaussian input containing all three
generator kinds.
The four level operations and answer differentiation use the new flat representation. The
suite gives parsing and integration one second each, and exact differentiation ten seconds.
Run a JSON Lines suite from the repository root with

```sh
python3 SympyProofs/Calculus/AntiderivativeBench/suite.py "$HEBISCH_FILE" --jobs 4
```

On the 10,335 Hebisch inputs with four workers and the time limits above, exact
differentiation verified 8,831 primitives. All 8,711 cases verified by the earlier
named-coefficient frontend still passed. Of the 120 additional verified cases, the
previous frontend classified 111 as out of scope and rejected the towers for the other 9.

| Outcome | Inputs |
| --- | ---: |
| Verified without a named-coefficient assumption | 4,501 |
| Verified under the reported independence assumption | 4,330 |
| Tower failed admissibility | 467 |
| Outside the frontend's supported expressions | 245 |
| Parsing or tower construction timed out | 75 |
| Integration or admissibility timed out | 684 |
| Exact differentiation timed out | 33 |

There were no wrong derivatives or process failures. Of the 245 out-of-scope inputs, 161
required a further constant logarithm model, 61 required a further constant exponential
model, and 23 used a fractional power. An archived run of the earlier implementation verified
4,272.
