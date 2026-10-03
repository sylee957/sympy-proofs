import SympyProofs.RouthHurwitz.FractionFree.Determinants
import SympyProofs.RouthHurwitz.Table.Stability

/-! The determinant criterion connects unsigned algebra to strict stability. -/
namespace RouthHurwitz.FractionFree.Arithmetic
open Polynomial

private theorem linear_stable (u v : Row ℝ) (hu : 0 < u 0) :
    HurwitzStable (encodeRow 1 u + encodeRow 0 v) ↔ 0 < v 0 := by
  constructor
  · exact stable_pair_lower_pos 0 u v hu
  · intro hv z hz
    have he := congrArg Complex.re hz
    simp [encodeRow, Complex.mul_re] at he
    have hn : z.re < 0 := by nlinarith
    exact hn

/-- All leading Hurwitz minors are positive exactly when a row pair with
positive leading coefficient represents a strictly stable polynomial. -/
theorem stable_pair_iff_minors (d : ℕ) (u v : Row ℝ) (hu : 0 < u 0)
    (hsu : ∀ j, d+1 < 2*j → u j = 0) (hsv : ∀ j, d < 2*j → v j = 0) :
    HurwitzStable (encodeRow (d+1) u + encodeRow d v) ↔
      ∀ k, k ≤ d → 0 < (hMatrix u v (k+1) 0).det := by
  induction d generalizing u v with
  | zero =>
    rw [linear_stable u v hu]
    simp [hMatrix, hEntry, Matrix.det_unique]
  | succ d ih =>
    have hfirst : (hMatrix u v 1 0).det = v 0 := by simp [hMatrix, hEntry, Matrix.det_unique]
    have hreduce (hv : 0 < v 0) :
        HurwitzStable (encodeRow (d+2) u + encodeRow (d+1) v) ↔
          ∀ k, k ≤ d → 0 < (hMatrix v (next u v) (k+1) 0).det := by
      rw [stable_pair_reduce d u v hu hv hsv]
      have he : nextRow u v = next u v := by
        rw [nextRow_eq_sub u v (ne_of_gt hv)]; rfl
      rw [he]
      apply ih v (next u v) hv hsv
      intro j hj
      simp [next, hsu (j+1) (by omega), hsv (j+1) (by omega)]
    constructor
    · intro hs
      have hv := stable_pair_lower_pos (d+1) u v hu hs
      have hh := (hreduce hv).mp hs
      intro k hk
      cases k with
      | zero => simpa only [hfirst] using hv
      | succ k =>
        rw [det_step u v (ne_of_gt hv)]
        exact mul_pos hv (hh k (by omega))
    · intro hh
      have hv : 0 < v 0 := by simpa only [hfirst] using hh 0 (by omega)
      apply (hreduce hv).mpr
      intro k hk
      have hm := hh (k+1) (by omega)
      rw [det_step u v (ne_of_gt hv)] at hm
      exact (mul_pos_iff.mp hm).resolve_right (by intro h; linarith [h.1]) |>.2

/-- The symbolic Hurwitz minor uses the chosen degree, so specialization can
be handled without assuming the coefficient evaluation is injective. -/
def hurwitzMinor {A : Type*} [CommRing A] (p : Polynomial A) (n k : ℕ) : A :=
  (hMatrix (fun j => if 2*j ≤ n then p.coeff (n-2*j) else 0)
    (fun j => if 2*j+1 ≤ n then p.coeff (n-(2*j+1)) else 0) k 0).det

theorem hurwitzMinor_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (p : Polynomial A) (n k : ℕ) :
    hurwitzMinor (p.map f) n k = f (hurwitzMinor p n k) := by
  unfold hurwitzMinor
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hMatrix, hEntry, coeff_map]
  split_ifs <;> simp only [apply_ite, map_zero]
  all_goals split_ifs <;> rfl

/-- Fixed-degree Hurwitz criterion. The leading coefficient hypothesis also
ensures that this degree is the actual degree. -/
theorem hurwitzStable_iff_minors (p : Polynomial ℝ) (n : ℕ)
    (hd : p.natDegree = n) (hl : 0 < p.coeff n) :
    HurwitzStable p ↔ ∀ k, 1 ≤ k → k ≤ n → 0 < hurwitzMinor p n k := by
  cases n with
  | zero =>
    have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hd
    rw [he]
    constructor
    · intro _ k hk hk'; omega
    · intro _ z hz
      simp only [Polynomial.map_C, eval_C] at hz
      exact False.elim ((ne_of_gt hl) (Complex.ofReal_eq_zero.mp hz))
  | succ d =>
    let u := initialRow p.natDegree (descendingCoefficients p) 0
    let v := initialRow p.natDegree (descendingCoefficients p) 1
    have hp := initial_polynomials p (by omega)
    change encodeRow p.natDegree u + encodeRow (p.natDegree-1) v = p at hp
    rw [hd] at hp
    simp only [Nat.add_sub_cancel] at hp
    have hu : 0 < u 0 := by simpa [u, initialRow, descendingCoefficients, hd] using hl
    have hh := stable_pair_iff_minors d u v hu
      (by intro j hj; simp [u, initialRow, hd, show ¬ 2*j ≤ d+1 by omega])
      (by intro j hj; simp [v, initialRow, hd, show ¬ 2*j+1 ≤ d+1 by omega])
    rw [hp] at hh
    rw [hh]
    have he (k : ℕ) : (hMatrix u v k 0).det = hurwitzMinor p (d+1) k := by
      unfold hurwitzMinor
      congr 2 <;> funext j <;> simp [u, v, initialRow, descendingCoefficients, hd]
    simp_rw [he]
    constructor
    · intro h k hk hkn
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact h j (by omega)
    · intro h k hk
      exact h (k+1) (by omega) (by omega)

end RouthHurwitz.FractionFree.Arithmetic
