module

public import SympyProofs.Calculus.Antiderivative.Algebra.Factor.Split

/-! Soundness of recursive polynomial splitting, independently of the divisor search. -/

public section

namespace SympyProofs.Calculus.Antiderivative.Factor

variable {F : Type} [Field F] [DecidableEq F]

/-- A nonzero constant normalizes to one. -/
theorem normalize_of_degree_zero {p : Poly F} (hp : p ≠ 0) (hd : p.natDegree = 0) :
    normalize p = 1 := by
  apply Poly.equiv.injective
  rw [map_one]
  apply Polynomial.eq_one_of_monic_natDegree_zero
  · change (Poly.equiv (normalize p)).leadingCoeff = 1
    simp only [Poly.leadingCoeff_equiv, Poly.leadingCoeff_normalize, hp, ↓reduceIte]
  · simpa using hd

/-- The product of the returned factors is the input made monic. -/
theorem split_prod (find : Poly F → Option (Poly F)) (fuel : ℕ) (p : Poly F) (hp : p ≠ 0) :
    (split find fuel p).prod = normalize p := by
  induction fuel generalizing p with
  | zero =>
    by_cases hd : p.natDegree = 0 <;> simp [split, hd, normalize_of_degree_zero hp]
  | succ fuel ih =>
    rw [split]
    split
    · rename_i hd
      simp [normalize_of_degree_zero hp hd]
    split
    · simp
    split
    · simp
    rename_i b _
    dsimp only
    split
    · rename_i h
      have hne : b ≠ 0 ∧ p / b ≠ 0 := mul_ne_zero_iff.mp (fun e => hp (h.2.2.symm.trans e))
      rw [List.prod_append, ih _ hne.1, ih _ hne.2, ← normalize_mul, h.2.2]
    · simp

/-- Each returned polynomial is monic. -/
theorem split_monic (find : Poly F → Option (Poly F)) (fuel : ℕ) (p : Poly F)
    {a : Poly F} (ha : a ∈ split find fuel p) : (Poly.equiv a).Monic := by
  have leaf {q : Poly F} (hq : q.natDegree ≠ 0) (h : a ∈ [normalize q]) :
      (Poly.equiv a).Monic := by
    have hn : q ≠ 0 := fun e => hq (by simp [e])
    simp only [List.mem_singleton] at h
    change (Poly.equiv a).leadingCoeff = 1
    simp only [h, Poly.leadingCoeff_equiv, Poly.leadingCoeff_normalize, hn, ↓reduceIte]
  induction fuel generalizing p with
  | zero =>
    rw [split] at ha
    split at ha
    · simp at ha
    · exact leaf (by assumption) ha
  | succ fuel ih =>
    rw [split] at ha
    split at ha
    · simp at ha
    rename_i hp
    split at ha
    · exact leaf hp ha
    split at ha
    · exact leaf hp ha
    dsimp only at ha
    split at ha
    · exact (List.mem_append.mp ha).elim (fun h => ih _ h) (fun h => ih _ h)
    · exact leaf hp ha

/-- The executable test checks both strict degree inequalities and divisibility. -/
theorem proper_iff (p b : Poly F) :
    proper p b ↔ 0 < b.natDegree ∧ b.natDegree < p.natDegree ∧ b ∣ p := by
  simp [proper, EuclideanDomain.mod_eq_zero, and_assoc]

/-- The factors returned by a complete proper-divisor search are irreducible. -/
theorem split_irreducible (find : Poly F → Option (Poly F))
    (complete : ∀ p : Poly F, 2 ≤ p.natDegree → ¬Irreducible p →
      ∃ b, find p = some b ∧ proper p b)
    (fuel : ℕ) (p : Poly F) (enough : p.natDegree ≤ fuel)
    {a : Poly F} (ha : a ∈ split find fuel p) : Irreducible a := by
  have leaf {q : Poly F} (hq : Irreducible q) (h : a ∈ [normalize q]) : Irreducible a := by
    rw [List.mem_singleton.mp h]
    exact (normalize_associated q).irreducible_iff.mpr hq
  induction fuel generalizing p with
  | zero => simp [split, Nat.eq_zero_of_le_zero enough] at ha
  | succ fuel ih =>
    rw [split] at ha
    split at ha
    · simp at ha
    rename_i hd
    have hn : p ≠ 0 := fun h => hd (by simp [h])
    have hn' : Poly.equiv p ≠ 0 := (map_ne_zero_iff Poly.equiv Poly.equiv.injective).mpr hn
    have linear (h : p.natDegree = 1) : Irreducible p :=
      (MulEquiv.irreducible_iff (Poly.equiv (R := F))).mp (Polynomial.irreducible_of_degree_eq_one
        (by rw [Polynomial.degree_eq_natDegree hn', Poly.natDegree_equiv, h]; rfl))
    split at ha
    · exact leaf (linear (by assumption)) ha
    rename_i h1
    have hd' : 2 ≤ p.natDegree := by omega
    cases hfind : find p with
    | none =>
      simp only [hfind] at ha
      apply leaf _ ha
      by_contra h
      have ⟨_, he, _⟩ := complete p hd' h
      simp [hfind] at he
    | some b =>
      simp only [hfind] at ha
      have degrees (hm : b * (p / b) = p) : b.natDegree + (p / b).natDegree = p.natDegree := by
        have hp' := mul_ne_zero_iff.mp (fun hz => hn (hm.symm.trans hz))
        have d := Polynomial.natDegree_mul
          ((map_ne_zero_iff Poly.equiv Poly.equiv.injective).mpr hp'.1)
          ((map_ne_zero_iff Poly.equiv Poly.equiv.injective).mpr hp'.2)
        simpa only [← map_mul, hm, Poly.natDegree_equiv] using d.symm
      split at ha
      · rename_i h
        have d := degrees h.2.2
        exact (List.mem_append.mp ha).elim (ih _ (by omega)) (ih _ (by omega))
      · rename_i h
        apply leaf _ ha
        by_contra hnI
        obtain ⟨c, hc, hproper⟩ := complete p hd' hnI
        rw [hfind, Option.some.injEq] at hc
        subst c
        obtain ⟨hb, hlt, hdvd⟩ := (proper_iff _ _).mp hproper
        have hb0 : b ≠ 0 := fun e => by simp [e] at hb
        have hm := EuclideanDomain.mul_div_cancel' hb0 hdvd
        have _ := degrees hm
        exact h ⟨hb, by omega, hm⟩

end SympyProofs.Calculus.Antiderivative.Factor
