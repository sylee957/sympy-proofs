module

public import SympyProofs.Sum.ModularShifts.Algorithm
public import SympyProofs.Sum.ModularShifts.Contracts
public import SympyProofs.Sum.ModularShifts.Correctness

/-!
# Modular shift enumeration over ℚ

Implements the centered-factor method of §6 of Gerhard, Giesbrecht, Storjohann,
and Zima, *Shiftless Decomposition and Polynomial-time Rational Summation* (2003):
https://cs.uwaterloo.ca/~astorjoh/p119-gerhard.pdf

`ModularShifts.shifts` immediately returns an empty array if either input has degree
zero. Otherwise it clears each input denominator once and takes the primitive
integer part. One derivative resultant per nonconstant integer input supplies the
excluded prime divisors, together with the integer leading coefficients. The prime
search uses only primality and integer divisibility tests. It chooses the lifting exponent using an
exact integer logarithm. `precision_spec` proves good reduction from the resultant
identity and proves the required modulus bound.

`ModularShifts.Backend` supplies integer resultants, finite-field factorization,
and Hensel lifting for integer polynomials. Resultant computation, reduction,
lifting, and exact verification share the prepared integer inputs.
`Backend.Valid` states their contracts,
including compatibility of the uniquely lifted factors under divisibility and
translation. Those arithmetic operations are not implemented here.

`ModularShifts.shifts` takes monic square-free inputs, computes and centers their
modular factors, recovers integer candidates, and performs exact gcd checks.
`ModularShifts.mem_shifts` proves both soundness and completeness with monicity
and square-freeness as proof preconditions; `nodup_shifts` proves uniqueness
without preconditions. The rational Cauchy bound includes inputs with zero constant
coefficient. The modulus is strictly greater than twice that bound, so negative
and positive shifts are reconstructed without ambiguity.

This module is independent of shiftless decomposition and works over rational
coefficients. Parameter-field specialization and norm reductions are not
implemented here.
-/
