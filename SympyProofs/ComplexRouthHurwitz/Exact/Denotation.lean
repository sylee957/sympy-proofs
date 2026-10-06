import SympyProofs.ComplexRouthHurwitz.FractionFree.Algebra
import SympyProofs.RouthHurwitz.Exact.Domain

/-! Coefficient arithmetic and its complex interpretation are separate.
A ring homomorphism transports the pseudo-remainder. Division is transported only
on exact products; no order or field structure on the coefficient ring is needed. -/
namespace RouthHurwitz.ComplexRouth.Exact

variable {A : Type*} [CommRing A]

/-- Pseudo-remainders commute with interpretation into a commutative ring. -/
theorem map_numerator {B : Type*} [CommRing B] (f : A →+* B) (u v : ℕ → A) (j : ℕ) :
    f (FractionFree.numerator u v j) =
      FractionFree.numerator (fun k => f (u k)) (fun k => f (v k)) j := by
  simp [FractionFree.numerator]

/-- The coefficient ring's conjugation supplies the complex initialization factor. -/
theorem map_conjugate_product [Star A] (f : A →+* ℂ)
    (hstar : ∀ b, f (star b) = star (f b)) (a b : A) :
    f (a * star b) = f a * star (f b) := by
  rw [map_mul, hstar]

end RouthHurwitz.ComplexRouth.Exact
