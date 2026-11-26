# Risch

A verified decision procedure for elementary integration in towers of exponentials and
logarithms, following R. H. Risch, *The Problem of Integration in Finite Terms*
(Trans. AMS 139, 1969).

## What is proved

Let `k` be an algebraically closed field of characteristic zero, the constants. A tower
`t` of depth `n` presents the field `K k n = k(θ₀, …, θₙ₋₁)` with a derivation.

For every tower `t` with `admissible t = true` and every term `f` with `f.defined = true`:

* **Soundness** (`integrate_sound`). If `integrate t f = .elementary F`, then `F` is
  defined in the field and its derivative is `f`.
* **Completeness** (`integrate_complete`). If `integrate t f = .nonelementary`, then `f`
  has no elementary integral: there are no `v, uᵢ` in the field and constants `cᵢ` in `k`
  with `f = v′ + Σ cᵢ uᵢ′/uᵢ`. By Liouville's theorem this excludes a primitive in every
  elementary extension (`integrate_no_primitive`).
* **Input conditions are computed.** `admissible t` and `f.defined` are boolean programs. A
  tower that passes `admissible` is admissible over every constant field
  (`admissible_sound`), and `f.defined` holds exactly when no denominator of `f` vanishes
  (`Term.defined_iff`), so the caller supplies no proofs. `integrateChecked` runs both
  tests and then `integrate`.

The theorems are in `Proof/Integrate.lean`. They depend on no axioms beyond the three
standard ones of Lean and Mathlib. Apart from Mathlib, their statements use only the programs
and the definitions in `Spec/`, so reading a statement needs nothing from `Proof/` or
`Algebra/`.

The constants must be algebraically closed already for simple integrands. The integral of
`eˣ/(e²ˣ+1)` is `Σ c log(eˣ + 2c)` over the roots `c` of `4c² + 1`, that is
`(i/2) log(eˣ + i) - (i/2) log(eˣ - i)`, and with rational constants only it would have no
elementary integral in the sense above. The residues may be any algebraic numbers, and the
answer is a sum over the roots of a polynomial with rational coefficients.

## Scope

* Generators are *primitives* (`θ′ = b` with `b` in the field so far) and *exponentials*
  (`θ′ = u′θ`). The variable is the primitive of `1` over the constants, and `log u` is the
  primitive of `u′/u`, so a tower over `x` with `exp` and `log` nested in any way is covered.
* Integrands are rational expressions in the generators with rational coefficients.
* The programs treat any primitive generator, but `admissible` accepts a primitive above the
  first generator only when it is written as a logarithm. The uniqueness arguments at
  exponential steps, and the negative answers of `integrate`, rely on this.
* Out of scope: algebraic functions (`√x`, `√(log x)`), which need different methods, and
  rewriting a tower that is not admissible. A tower with a relation among its generators,
  such as `log x` with `log(x²)`, is rejected by `admissible`.

## Conventions

**Programs carry no propositions.** Every algorithm is a total function between plain data
types: `Term n`, `Tower n`, coefficient lists, rational numbers, `Bool`, `Option`. A program
takes no proof arguments and returns no proofs. Recursion is structural or on an explicit
fuel argument, so no termination proof is attached to a program.

**The grammar enforces what is syntactic.** Terms and towers are indexed by depth, and a
term of depth `n` refers to its generators through `Fin n`, so a reference to a generator
that does not exist cannot be written. What depends on the meaning of a term is not in the
grammar: that no denominator vanishes, and that a tower is admissible, are decided by
boolean programs.

**Propositions live in theorems.** Each program has a specification proved in a separate
file. Admissibility and definedness appear there as hypotheses.

**Programs do not import Mathlib.** Files under `Program/` depend only on the Lean core
library and on each other. They can be read, and run with `#eval`, as ordinary Lean code.

**One recursion, no special cases.** The constant field is depth zero and the variable is
the first generator, so rational functions are handled by the same code as every other
level. There are two kinds of step, primitive and exponential, and they share Hermite
reduction, the residue criterion and the assembly of the answer.

## Layout

| Directory | Contents | Imports |
| --- | --- | --- |
| `Program/` | data types and algorithms | Lean core only |
| `Spec/` | every definition the theorems are stated with: the field `K k n` and its derivation, the meaning of terms, coefficient lists and answers, Liouville forms and elementary extensions | Mathlib, `Program/` |
| `Algebra/` | lemmas about polynomials and rational functions over any field | Mathlib |
| `Proof/` | the specification of each program | all of the above |

## The algorithm

`integrate t f` is a recursion on the depth of `t`. At depth zero the field is the constant
field and only `0` has a primitive. At a tower step with newest generator `θ`:

1. **Lowest terms.** Write `f = N/D` with polynomials in `θ` over the preceding field.
2. **Special part.** At an exponential step, split off the power of `θ` in `D`. It joins
   the polynomial part, with negative exponents.
3. **Hermite reduction.** Subtract the derivative of a rational function so that the
   denominator that remains is squarefree. Only greatest common divisors are used.
4. **Residues.** For the remaining fraction `A/Dₛ`, the residues are the constant roots of
   the resultant of `A − z Dₛ′` and `Dₛ`, computed by the subresultant algorithm of Collins
   and Brown over the field one level up, where `z` is a generator. They are the roots of a
   polynomial `r(z)` with rational coefficients, found without factoring. The logarithm for a root `c` has argument
   `gcd(A − c Dₛ′, Dₛ)`, computed once with `c` symbolic, modulo `r`. An elementary integral
   exists only if these greatest common divisors account for all of `Dₛ`, which is a
   comparison of degrees.
5. **Polynomial part.** What is left is a polynomial in `θ`. Its coefficients satisfy
   differential equations in the preceding field, solved there by `solve`. The constant
   term is integrated by `integrate` one level down.

`solve t f gs` is part (b) of Risch's Main Theorem: all solutions `y` in the field, with
constants `cᵢ`, of `y′ + f y = Σ cᵢ gᵢ`, returned as a basis and a linear system over the
rationals. It is also a recursion on depth: a denominator for every solution from a bound
on integral residues, a bound on the degree of the numerator, and then one equation per
coefficient in the preceding field.

At an exponential step both bounds involve an integer `m` for which `g + m u′` is a
logarithmic derivative. It is found by linear algebra over the rationals (`relRows`), which
also decides whether a new exponential is admissible.

Coefficients are kept in lowest terms by `Term.norm`, which writes a term as a quotient of
two polynomials with integer coefficients in all the generators at once and cancels their
greatest common divisor. That divisor comes from the heuristic of Char, Geddes and Gonnet,
with a primitive Euclidean algorithm when it gives up, and is used only after exact division
by it has succeeded: nothing about it needs to be proved. Linear systems are solved by
elimination over the integers. Both avoid rational arithmetic, which in Lean computes a
greatest common divisor after every operation.

## Constants

Programs compute with rational numbers only. Part (b), admissibility, Hermite reduction
and the polynomial part are proved over an arbitrary constant field `k` of characteristic
zero. Algebraic closure is assumed for the residue step, in both directions: an answer is a
sum over the roots in `k` of a polynomial, and it is the integral only when all the roots
are there. Three facts make this work:

* a term with rational coefficients vanishes in `K k n` exactly when its normal form over
  the rationals is zero, whatever `k` is;
* a linear system with rational coefficients has a solution over `k` exactly when it has
  one over the rationals, so `solve` and the admissibility test do not depend on `k`;
* an algebraic number enters only as a residue, and is represented by the polynomial it is
  a root of. No arithmetic in an algebraic closure is performed.

## An example

`integrate Tower.x` applied to `1 / (x² + 1)` returns no rational part and one sum of
logarithms, with modulus `4 z² + 1` and argument `x + 2 z`:

    ∫ dx / (x² + 1) = Σ c log (x + 2 c),  the sum over the roots c of 4 c² + 1,

that is, `(i/2) log (x + i) - (i/2) log (x - i)`. The roots are never computed.

## Plan

Each stage ends with the project building and its theorems free of `sorry`.

1. **Foundations.** Terms, towers, the symbolic derivative; the field `K k n`, its
   derivation, and the theorem that the symbolic derivative computes it.
2. **Arithmetic.** Normal forms and the zero test; lowest terms of a term as a quotient of
   two polynomials with integer coefficients; polynomials in the newest generator as
   coefficient lists with division, greatest common divisor and reduction to lowest terms;
   linear algebra over the rationals.
3. **Part (b).** `solve` and `relRows` for both kinds of step, and `admissible`.
4. **Reduction and polynomial part.** Hermite reduction, and integration of a polynomial in
   the generator through its coefficients.
5. **Residues.** The residue criterion over an algebraically closed `k`, greatest common
   divisors modulo the residue polynomial, sums over its roots in the answer.
6. **Main theorems.** Soundness and completeness of `integrate`, and Liouville's theorem as
   the bridge from "no Liouville form in the field" to "no primitive in any elementary
   extension".
7. **Analytic meaning.** For `k = ℂ`, the answer as a function with the stated derivative
   near every regular point.

## Status

Stages 1 to 6 are complete: the programs run, the project builds, and no theorem uses
`sorry`. `integrate`, `integrateChecked`, `solve`, `relRows` and `admissible` agree with
the expected answers on the examples tried, including integrands with irrational residues.

| Stage | Programs | Proofs |
| --- | --- | --- |
| 1. Foundations | `Program/Term` | `Proof/Derivative` (`Tower.der_value`) |
| 2. Arithmetic | `Program/Normal`, `ZPoly`, `Poly`, `Linear`, `Constraints` | `Proof/Normal` (`Term.isZero_iff`, `Term.defined_iff`), `Proof/ZPoly` (`ZP.normFF_spec`), `Proof/Poly` (`Term.norm_sound`, division, gcd, lowest terms), `Proof/Linear` (`kernel_spec`), `Proof/Constraints` (`rowsOf_spec`) |
| 3. Part (b) | `Program/Deriv`, `Resultant`, `Rel`, `Solve`, `Admissible` | `Proof/Solve` (`admissible_sound`, `solve_spec`), with `Proof/Deriv`, `Constants`, `Pole`, `Subresultant`, `Resultant`, `SolvePoly`, `Rel`, `SolveBounds`, `SolveStep` |
| 4. Reduction and polynomial part | `Program/Hermite`, `PolyPart` | `Proof/Hermite` (`Hermite.reduceTerm_spec`), `Proof/LiouvilleForm`, `Proof/PolyPart` (`expPart_sound`, `expPart_complete`, `primPart_sound`, `primPart_complete`) |
| 5. Residues | `Program/Residue` | `Proof/ResidueCriterion` (`Tower.residue_necessary`), `Proof/ConstRoots` (`constRoots_spec`), `Proof/GcdMod` (`gcdMod_spec`), `Proof/RootSums`, `Algebra/LogPart` (`logPart_identity`), `Proof/Residue` (`logPart_sound`, `logPart_complete`) |
| 6. Main theorems | `Program/Answer`, `Integrate` | `Proof/Integrate` (`integrate_sound`, `integrate_complete`, `integrate_no_primitive`, `integrateChecked_sound`, `integrateChecked_complete`) |
| 7. Analytic meaning | | not started |
