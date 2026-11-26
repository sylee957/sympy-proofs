module

public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Tower
public import SympyProofs.Calculus.Antiderivative.Proof.Factor.Split
public import SympyProofs.Calculus.Antiderivative.Spec.Factor

/-! Product preservation and completeness of the subset-product search over the constants. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

namespace Factor

variable {C F : Type} [Field C] [Field F] [DecidableEq C] [DecidableEq F]

/-- Reading the low digits of a bounded exponent vector recovers it exactly.
The high quotient records the exponent of the main variable. -/
theorem digits_place {m bs : List ℕ} (bounded : List.Forall₂ (· < ·) m bs) (h : ℕ) :
    digits bs (placeDigits bs m h) = (m, h) := by
  induction bounded with
  | nil => rfl
  | @cons i b is bs hi _ ih =>
    have hb : 0 < b := by omega
    change digits (b :: bs) (i + b * placeDigits bs is h) = _
    simp [digits, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hi,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, ih]

/-- The mixed-radix encoding is injective among exponent vectors with the chosen bounds. -/
theorem encode_inj {a b bs : List ℕ} (ha : List.Forall₂ (· < ·) a bs)
    (hb : List.Forall₂ (· < ·) b bs) (he : encode bs a = encode bs b) : a = b := by
  have d := congrArg (digits bs) he
  rw [encode, encode, digits_place ha, digits_place hb] at d
  exact (Prod.mk.inj d).1

/-- Every proper divisor returned after reversing a substitution actually divides the input. -/
theorem subsetFactor_proper (decode : Poly C → Poly F) {p q : Poly F} (acc : Poly C)
    (fs : List (Poly C)) (h : subsetFactor decode p acc fs = some q) : proper p q := by
  induction fs generalizing acc with
  | nil =>
    rw [subsetFactor] at h
    split at h
    · cases h
      assumption
    · contradiction
  | cons b bs ih =>
    rw [subsetFactor] at h
    cases e : subsetFactor decode p acc bs with
    | none => exact ih _ (by simpa [e] using h)
    | some a =>
      simp [e] at h
      subst a
      exact ih _ e

private theorem isSome_orElse {α : Type} (a b : Option α) :
    (a.orElse (fun _ => b)).isSome = (a.isSome || b.isSome) := by
  cases a <;> rfl

/-- If a sublist gives a factor, the short-circuiting subset search finds one. -/
theorem subsetFactor_complete (decode : Poly C → Poly F) (p : Poly F) (acc : Poly C)
    {fs ss : List (Poly C)} (hs : ss.Sublist fs) (good : proper p (decode (acc * ss.prod))) :
    (subsetFactor decode p acc fs).isSome := by
  induction hs generalizing acc with
  | slnil => simpa [subsetFactor] using good
  | cons a hs ih =>
    simp only [subsetFactor, isSome_orElse, Bool.or_eq_true]
    exact Or.inl (ih _ good)
  | cons_cons a hs ih =>
    simp only [subsetFactor, isSome_orElse, Bool.or_eq_true]
    exact Or.inr (ih (acc * a) (by simpa [mul_assoc] using good))

/-- A monic divisor of a product of monic irreducibles is exactly a sublist product,
including the multiplicities of repeated factors. -/
theorem exists_sublist {fs : List (Poly C)} (hf : ∀ f ∈ fs, normalize f = f ∧ Irreducible f)
    {q : Poly C} (hn : normalize q = q) (hd : q ∣ fs.prod) :
    ∃ ss : List (Poly C), ss.Sublist fs ∧ ss.prod = q := by
  induction fs generalizing q with
  | nil =>
    have hu := normalize_eq_one.mpr (isUnit_iff_dvd_one.mpr hd)
    exact ⟨[], .refl _, hu.symm.trans hn⟩
  | cons b bs ih =>
    obtain ⟨hnB, hi⟩ := hf _ List.mem_cons_self
    have tail := fun f h => hf f (List.mem_cons_of_mem b h)
    rw [List.prod_cons] at hd
    by_cases hb : b ∣ q
    · obtain ⟨r, rfl⟩ := hb
      rw [normalize_mul, hnB] at hn
      obtain ⟨ss, hs, hp⟩ := ih tail (mul_left_cancel₀ hi.ne_zero hn)
        ((mul_dvd_mul_iff_left hi.ne_zero).mp hd)
      exact ⟨b :: ss, hs.cons_cons b, by simp [hp]⟩
    · have rel := (hi.isRelPrime_iff_not_dvd.mpr hb).symm
      obtain ⟨ss, hs, hp⟩ := ih tail hn (rel.dvd_of_dvd_mul_left hd)
      exact ⟨ss, hs.cons b, hp⟩

/-- The subset search over a lawful factorization finds a decoded divisor whenever one
monic divisor of the substituted polynomial decodes to a proper factor. -/
theorem subsetFactor_of_dvd [ConstantFactors C] [LawfulConstantFactors C]
    (decode : Poly C → Poly F) (p : Poly F) (f : Poly C) (hf : f ≠ 0)
    (d : Poly C) (hm : normalize d = d) (hd : d ∣ f) (good : proper p (decode d)) :
    (subsetFactor decode p 1 (ConstantFactors.factors f)).isSome := by
  have hu : IsUnit (Poly.C f.leadingCoeff) := by
    apply (isUnit_iff_dvd_one.mpr ?_)
    refine ⟨Poly.C f.leadingCoeff⁻¹, ?_⟩
    rw [← Poly.C_mul, mul_inv_cancel₀ (Poly.leadingCoeff_ne_zero hf), Poly.C_one]
  rw [← LawfulConstantFactors.product f hf] at hd
  obtain ⟨ss, hss, he⟩ := exists_sublist (fun b hb => by
    obtain ⟨hm, hi⟩ := LawfulConstantFactors.irreducible f hf b hb
    exact ⟨Poly.normalize_eq_self_iff.mpr (Or.inr ((Poly.leadingCoeff_equiv b).symm.trans hm)), hi⟩)
    hm (hu.dvd_mul_left.mp hd)
  exact subsetFactor_complete _ _ _ hss (by simpa [he] using good)

end Factor

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [ConstantFactors (K R 0)] [LawfulConstantFactors (K R 0)] {n : ℕ}

/-- Multiplying the factors over a function field recovers the input up to its leading scalar. -/
theorem factorTower_product (p : Poly (K R n)) (hp : p ≠ 0) :
    Poly.C p.leadingCoeff * (factorTower p).prod = p := by
  cases n with
  | zero => exact LawfulConstantFactors.product p hp
  | succ n =>
    rw [factorTower, Factor.split_prod _ _ _ hp, Poly.normalize_eq_C_mul, ← mul_assoc,
      ← Poly.C_mul, mul_inv_cancel₀ (Poly.leadingCoeff_ne_zero hp), Poly.C_one, one_mul]

/-- Every output factor is monic in the main variable. -/
theorem factorTower_monic (p : Poly (K R n)) (hp : p ≠ 0) (q : Poly (K R n))
    (hq : q ∈ factorTower p) : (Poly.equiv q).Monic := by
  cases n with
  | zero => exact (LawfulConstantFactors.irreducible p hp q hq).1
  | succ n => exact Factor.split_monic _ _ _ hq

end SympyProofs.Calculus.Antiderivative
