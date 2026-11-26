module

public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Rational
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Sqrt

/-! Completeness of the integer value search used in Kronecker interpolation. -/

public section

namespace SympyProofs.Calculus.Antiderivative.Factor

/-- Clearing the denominators uses a positive multiplier. -/
theorem denominator_pos (cs : List ℚ) : 0 < denominator cs := by
  induction cs with
  | nil => decide
  | cons a as ih => exact Nat.lcm_pos a.den_pos ih

/-- The common denominator is a multiple of every coefficient denominator. -/
theorem den_dvd_denominator {a : ℚ} {cs : List ℚ} (h : a ∈ cs) : a.den ∣ denominator cs := by
  induction cs with
  | nil => simp at h
  | cons b bs ih =>
    rcases List.mem_cons.mp h with rfl | hb
    · exact Nat.dvd_lcm_left _ _
    · exact (ih hb).trans (Nat.dvd_lcm_right _ _)

/-- The integral polynomial is precisely the positive integer multiple of the rational input. -/
theorem integral_eq (p : Poly ℚ) :
    (Poly.equiv (integral p)).map (Int.castRingHom ℚ) =
      Polynomial.C (denominator p.coeffs : ℚ) * Poly.equiv p := by
  let d := denominator p.coeffs
  have converted : (p.coeffs.map (fun a => ((a.num * (d / a.den : ℕ) : ℤ) : ℚ))) =
      p.coeffs.map (fun a => (d : ℚ) • a) := by
    apply List.map_congr_left
    intro a ha
    obtain ⟨k, hk⟩ := den_dvd_denominator ha
    change d = a.den * k at hk
    rw [hk, Nat.mul_div_cancel_left _ a.den_pos]
    push_cast
    rw [smul_eq_mul]
    have hr := a.num_div_den
    have he : (a.num : ℚ) = a * a.den :=
      (div_eq_iff (by exact_mod_cast a.den_nz)).mp hr
    rw [he]
    ring
  rw [integral, Poly.equiv_ofList, ← Poly.Raw.toPolynomial_listMap, List.map_map]
  change Poly.Raw.toPolynomial (p.coeffs.map (fun a => ((a.num * (d / a.den : ℕ) : ℤ) : ℚ))) = _
  rw [converted, Poly.Raw.toPolynomial_map_smul]
  rw [← Poly.equiv_ofList, Poly.ofList_coeffs, Polynomial.smul_eq_C_mul]

private theorem mem_pairedDivisors {u v : ℕ} (hu : 0 < u) (a : ℤ)
    (ha : a.natAbs = u * v) (hs : u ≤ a.natAbs.sqrt) :
    (u : ℤ) ∈ signedDivisors a ∧ -(u : ℤ) ∈ signedDivisors a ∧
      (v : ℤ) ∈ signedDivisors a ∧ -(v : ℤ) ∈ signedDivisors a := by
  have hmem : u - 1 ∈ List.range a.natAbs.sqrt := List.mem_range.mpr (by omega)
  have step : u - 1 + 1 = u := by omega
  have div : a.natAbs / u = v := by rw [ha, Nat.mul_div_cancel_left _ hu]
  have mod : a.natAbs % u = 0 := Nat.mod_eq_zero_of_dvd ⟨_, ha⟩
  have both (x : ℤ) (hx : x = u ∨ x = -↑u ∨ x = v ∨ x = -↑v) : x ∈ signedDivisors a := by
    apply List.mem_flatMap.mpr
    refine ⟨_, hmem, ?_⟩
    simp only [step, div, mod, ne_eq, not_true_eq_false, ite_false]
    split <;> simp_all
    tauto
  exact ⟨both _ (by simp), both _ (by simp), both _ (by simp), both _ (by simp)⟩

/-- Every signed divisor of a nonzero input occurs among the enumerated choices. -/
theorem mem_signedDivisors {u v : ℤ} (hv : v ≠ 0) (h : u ∣ v) : u ∈ signedDivisors v := by
  obtain ⟨w, hw⟩ := h
  have ha : v.natAbs = u.natAbs * w.natAbs := by rw [hw, Int.natAbs_mul]
  have hp : 0 < u.natAbs ∧ 0 < w.natAbs := by
    have hpos : 0 < v.natAbs := Int.natAbs_pos.mpr hv
    rw [ha] at hpos
    exact ⟨Nat.pos_of_ne_zero (fun h => by simp [h] at hpos),
      Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)⟩
  have both : (u.natAbs : ℤ) ∈ signedDivisors v ∧ -(u.natAbs : ℤ) ∈ signedDivisors v := by
    rcases Nat.le_sqrt_of_eq_mul ha with hu | hw'
    · have hd := mem_pairedDivisors hp.1 v ha hu
      exact ⟨hd.1, hd.2.1⟩
    · exact (mem_pairedDivisors hp.2 v (ha.trans (Nat.mul_comm _ _)) hw').2.2
  rcases Int.natAbs_eq u with e | e
  · exact e ▸ both.1
  · exact e ▸ both.2

/-- The executable basis agrees with the Lagrange basis on the consecutive integer nodes. -/
theorem equiv_basis (m i : ℕ) :
    Poly.equiv (basis m i) = Lagrange.basis (Finset.range (m + 1)) (fun j : ℕ => (j : ℚ)) i := by
  simp [basis, Lagrange.basis, Lagrange.basisDivisor]

/-- Consecutive values reconstruct any polynomial of degree at most m. -/
theorem reconstruct (p : Poly ℚ) {m : ℕ} (hd : p.natDegree ≤ m) :
    ((List.range (m + 1)).map fun (i : ℕ) => Poly.C (p.eval (i : ℚ)) * basis m i).sum = p := by
  apply Poly.equiv.injective
  rw [map_list_sum, List.map_map]
  have inj : Function.Injective (fun i : ℕ => (i : ℚ)) := Nat.cast_injective
  have deg : (Poly.equiv p).degree < ↑(Finset.range (m + 1)).card := by
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro i hi
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [Poly.natDegree_equiv]
    simp only [Finset.card_range] at hi
    omega
  rw [Lagrange.eq_interpolate inj.injOn deg, Lagrange.interpolate_apply]
  rw [← List.toFinset_range, List.sum_toFinset _ List.nodup_range]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  simp [equiv_basis, List.toFinset_range]

/-- Every successful interpolation passed the proper-divisor test. -/
theorem interpolateFactor_proper {p acc q : Poly ℚ} {nodes : List (Poly ℚ × List ℤ)}
    (h : interpolateFactor p acc nodes = some q) : proper p q := by
  induction nodes generalizing acc with
  | nil =>
    rw [interpolateFactor] at h
    split at h
    · cases h
      assumption
    · contradiction
  | cons t ts ih =>
    obtain ⟨b, vs⟩ := t
    obtain ⟨v, _, hv⟩ := List.exists_of_findSome?_eq_some h
    exact ih hv

/-- If the possible values include all values of a divisor, the interpolation search succeeds. -/
theorem interpolateFactor_isSome (p : Poly ℚ) (weight : ℕ → Poly ℚ) (choices : ℕ → List ℤ)
    (v : ℕ → ℤ) (indices : List ℕ) (acc : Poly ℚ) (hm : ∀ i ∈ indices, v i ∈ choices i)
    (hd : proper p (acc + (indices.map fun i => Poly.C (v i : ℚ) * weight i).sum)) :
    (interpolateFactor p acc (indices.map fun i => (weight i, choices i))).isSome := by
  induction indices generalizing acc with
  | nil => simpa [interpolateFactor] using hd
  | cons i is ih =>
    simp only [List.map_cons, interpolateFactor, List.findSome?_isSome_iff]
    refine ⟨v i, hm i List.mem_cons_self, ih _ (fun j hj => hm j (List.mem_cons_of_mem _ hj)) ?_⟩
    simpa [add_assoc] using hd

end SympyProofs.Calculus.Antiderivative.Factor
