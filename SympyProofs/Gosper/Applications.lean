module

public import SympyProofs.Gosper.Products

/-! # Polynomial certificates for the paper's explicit identities -/

@[expose] public section
noncomputable section

namespace Gosper

variable {K : Type*} [Field K]

def quadratic (b c d x : K) : K := b * x ^ 2 + c * x + d

def cubic (a b c d x : K) : K := a * x ^ 3 + b * x ^ 2 + c * x + d

/-- Equation (3a), also illustrating the boundary and denominator conditions. -/
theorem quadratic_product_sum (b c d e : K) (hde : e - d ≠ 0) (m : ℕ)
    (hv : ∀ j ∈ Finset.range m, quadratic b c e (j + 1 : K) ≠ 0) :
    ∑ n ∈ Finset.range m,
      productRatio (fun j => quadratic b c d (j : K))
        (fun j => quadratic b c e (j : K)) n / quadratic b c e (n + 1 : K) =
      (1 - productRatio (fun j => quadratic b c d (j : K))
        (fun j => quadratic b c e (j : K)) m) / (e - d) := by
  have h (x : K) : quadratic b c d x + (e - d) = quadratic b c e x := by
    dsimp [quadratic]; ring
  simpa only [h, Nat.cast_add, Nat.cast_one] using
    sum_product_offset (fun j => quadratic b c d (j : K)) (e - d) hde m
      (by simpa only [h, Nat.cast_add, Nat.cast_one] using hv)

/-- Equation (3b). -/
theorem cubic_product_sum (a b c d e : K) (hde : e - d ≠ 0) (m : ℕ)
    (hv : ∀ j ∈ Finset.range m, cubic a b c e (j + 1 : K) ≠ 0) :
    ∑ n ∈ Finset.range m,
      productRatio (fun j => cubic a b c d (j : K))
        (fun j => cubic a b c e (j : K)) n / cubic a b c e (n + 1 : K) =
      (1 - productRatio (fun j => cubic a b c d (j : K))
        (fun j => cubic a b c e (j : K)) m) / (e - d) := by
  have h (x : K) : cubic a b c d x + (e - d) = cubic a b c e x := by
    dsimp [cubic]; ring
  simpa only [h, Nat.cast_add, Nat.cast_one] using
    sum_product_offset (fun j => cubic a b c d (j : K)) (e - d) hde m
      (by simpa only [h, Nat.cast_add, Nat.cast_one] using hv)

def quadraticCertificate (b c d e x : K) : K :=
  (e - d) * (b * (2 * x + 3) + c + d - e) - 2 * b * quadratic b c e (x + 1)

def quadraticDenominator (b c d e : K) : K :=
  (e - d) * (b ^ 2 - c ^ 2 + d ^ 2 + e ^ 2 + 2 * b * d - 2 * d * e + 2 * e * b)

/-- The polynomial recurrence certifying equation (3c). -/
theorem quadratic_certificate (b c d e x : K) :
    quadratic b c d x * quadraticCertificate b c d e x -
      quadratic b c e (x + 1) * quadraticCertificate b c d e (x - 1) =
        quadraticDenominator b c d e := by
  unfold quadraticCertificate quadraticDenominator quadratic
  ring

/-- Equation (3c) in the equivalent certificate/boundary form. -/
theorem quadratic_second_product_sum (b c d e : K) (m : ℕ)
    (hD : quadraticDenominator b c d e ≠ 0)
    (hv : ∀ j ≤ m, quadratic b c e (j + 1 : K) ≠ 0) :
    ∑ n ∈ Finset.range m,
      productRatio (fun j => quadratic b c d (j : K))
        (fun j => quadratic b c e (j : K)) n /
        (quadratic b c e (n + 1 : K) * quadratic b c e (n + 2 : K)) =
      (quadraticCertificate b c d e (m : K) *
        productRatio (fun j => quadratic b c d (j : K))
          (fun j => quadratic b c e (j : K)) m / quadratic b c e (m + 1 : K) -
        quadraticCertificate b c d e 0 / quadratic b c e 1) / quadraticDenominator b c d e := by
  have hF (n : ℕ) (_ : n < m) :
      quadratic b c d ((n + 1 : ℕ) : K) * quadraticCertificate b c d e ((n + 1 : ℕ) : K) -
        quadratic b c e ((n + 2 : ℕ) : K) * quadraticCertificate b c d e (n : K) =
          quadraticDenominator b c d e := by
    convert quadratic_certificate b c d e ((n : K) + 1) using 1
    push_cast
    ring_nf
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero] using
    sum_product_certificate (fun j => quadratic b c d (j : K))
      (fun j => quadratic b c e (j : K)) (fun n => quadraticCertificate b c d e (n : K))
      _ hD m (by simpa only [Nat.cast_add, Nat.cast_one] using hv) hF

def cubicCertificate (a b c d e x : K) : K :=
  2 * (6 * a ^ 2 * x ^ 3 + 6 * a * (3 * a + b) * x ^ 2 +
    2 * (6 * a ^ 2 + 6 * a * b + b ^ 2) * x + 6 * a * (a + b + c + d) + b * (d - e))

def cubicDenominator (a b c d e : K) : K :=
  (e - d) * (2 * b * (e - d + c - 2 * a) - 9 * a * (e + d))

/-- The third factor of (14) makes the certificate of (15) satisfy (8). -/
theorem cubic_certificate (a b c d e x : K)
    (h : 3 * a * e - 3 * a * d - 6 * a * c + 2 * b ^ 2 - 6 * a ^ 2 = 0) :
    cubic a b c d x * cubicCertificate a b c d e x -
      cubic a b c e (x + 1) * cubicCertificate a b c d e (x - 1) =
        cubicDenominator a b c d e := by
  unfold cubic cubicCertificate cubicDenominator
  linear_combination
    (-4 * a * x ^ 3 + 4 * a * x + 2 * a - 2 * b * x ^ 2 + 2 * b * x + 2 * b +
      2 * c - d + 3 * e) * h

/-- Equation (15), in certificate/boundary form. -/
theorem cubic_second_product_sum (a b c d e : K) (m : ℕ)
    (h : 3 * a * e - 3 * a * d - 6 * a * c + 2 * b ^ 2 - 6 * a ^ 2 = 0)
    (hD : cubicDenominator a b c d e ≠ 0)
    (hv : ∀ j ≤ m, cubic a b c e (j + 1 : K) ≠ 0) :
    ∑ n ∈ Finset.range m,
      productRatio (fun j => cubic a b c d (j : K))
        (fun j => cubic a b c e (j : K)) n /
        (cubic a b c e (n + 1 : K) * cubic a b c e (n + 2 : K)) =
      (cubicCertificate a b c d e (m : K) *
        productRatio (fun j => cubic a b c d (j : K))
          (fun j => cubic a b c e (j : K)) m / cubic a b c e (m + 1 : K) -
        cubicCertificate a b c d e 0 / cubic a b c e 1) / cubicDenominator a b c d e := by
  have hF (n : ℕ) (_ : n < m) :
      cubic a b c d ((n + 1 : ℕ) : K) * cubicCertificate a b c d e ((n + 1 : ℕ) : K) -
        cubic a b c e ((n + 2 : ℕ) : K) * cubicCertificate a b c d e (n : K) =
          cubicDenominator a b c d e := by
    convert cubic_certificate a b c d e ((n : K) + 1) h using 1
    push_cast
    ring_nf
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero] using
    sum_product_certificate (fun j => cubic a b c d (j : K))
      (fun j => cubic a b c e (j : K)) (fun n => cubicCertificate a b c d e (n : K))
      _ hD m (by simpa only [Nat.cast_add, Nat.cast_one] using hv) hF

end Gosper
