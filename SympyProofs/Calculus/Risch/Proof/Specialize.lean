module

public import SympyProofs.Calculus.Risch.Proof.Normal

/-! Specialization at a point. An element of the field `k(θ₀, …, θₙ₋₁)` that is a quotient
of polynomials whose denominator does not vanish at a point `p` has a value there, and an
identity between such elements holds for their values. The generators are algebraically
independent over `k`, so the value does not depend on the quotient chosen. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

variable (k) in
/-- Polynomials in the generators with coefficients in `k`, as elements of the field. -/
noncomputable def polyHom (n : ℕ) : MvPolynomial (Fin n) k →+* K k n :=
  MvPolynomial.eval₂Hom (constHom k n) (gens k n)

@[simp] theorem polyHom_C (c : k) : polyHom k n (MvPolynomial.C c) = constHom k n c := by
  simp [polyHom]

@[simp] theorem polyHom_X (i : Fin n) : polyHom k n (MvPolynomial.X i) = gens k n i := by
  simp [polyHom]

/-- One more generator: a polynomial becomes a polynomial in the new generator with
coefficients in the field below. -/
theorem polyHom_succ (n : ℕ) :
    polyHom k (n + 1) = (algebraMap (Polynomial (K k n)) (RatFunc (K k n))).comp
      ((Polynomial.mapRingHom (polyHom k n)).comp
        ((MvPolynomial.finSuccEquiv k n).toRingHom.comp
          (MvPolynomial.renameEquiv k (finRotate (n + 1))).toRingHom)) := by
  let v := polyHom k n
  let rot := MvPolynomial.renameEquiv k (finRotate (n + 1))
  let e := MvPolynomial.finSuccEquiv k n
  let ι := algebraMap (Polynomial (K k n)) (RatFunc (K k n))
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [polyHom, MvPolynomial.finSuccEquiv_apply, RatFunc.algebraMap_C]
    rfl
  · change ∀ i, polyHom k (n + 1) (MvPolynomial.X i) =
      ι (Polynomial.map v (e (rot (MvPolynomial.X i))))
    apply Fin.lastCases
    · rw [polyHom_X]
      simp only [rot, e, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
        finRotate_last, MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, ι,
        RatFunc.algebraMap_X]
      simp [gens]
    · intro j
      have hrot : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
      rw [polyHom_X]
      simp only [rot, e, ι, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, hrot,
        MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, RatFunc.algebraMap_C]
      simp [v, gens]

/-- The generators of a tower field are algebraically independent over the constants. -/
theorem polyHom_injective : ∀ n : ℕ, Function.Injective (polyHom k n)
  | 0 => by
    let e := MvPolynomial.isEmptyAlgEquiv k (Fin 0)
    have he : polyHom k 0 = e.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [e, constHom]
      · exact fun i => i.elim0
    rw [he]
    exact e.injective
  | n + 1 => by
    rw [polyHom_succ]
    exact (RatFunc.algebraMap_injective _).comp
      ((Polynomial.map_injective _ (polyHom_injective n)).comp
        ((MvPolynomial.finSuccEquiv k n).injective.comp
          (MvPolynomial.renameEquiv k (finRotate (n + 1))).injective))

/-- A polynomial in the generators below is the same element one level up. -/
theorem polyHom_rename_castSucc (P : MvPolynomial (Fin n) k) :
    polyHom k (n + 1) (MvPolynomial.rename Fin.castSucc P) = RatFunc.C (polyHom k n P) := by
  have : (polyHom k (n + 1)).comp (MvPolynomial.rename Fin.castSucc).toRingHom =
      (RatFunc.C : K k n →+* RatFunc (K k n)).comp (polyHom k n) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change polyHom k (n + 1) (MvPolynomial.rename Fin.castSucc (MvPolynomial.C c)) =
        RatFunc.C (polyHom k n (MvPolynomial.C c))
      rw [MvPolynomial.rename_C, polyHom_C, polyHom_C]
      rfl
    · intro i
      change polyHom k (n + 1) (MvPolynomial.rename Fin.castSucc (MvPolynomial.X i)) =
        RatFunc.C (polyHom k n (MvPolynomial.X i))
      rw [MvPolynomial.rename_X, polyHom_X, polyHom_X]
      simp [gens]
  exact congrArg (fun φ => φ P) this

/-- The element `x` of the field has the value `y p` at every point `p` of `S`: it is a
quotient of two polynomials whose denominator vanishes nowhere on `S`, and `y p` is the
quotient of their values at `p`. -/
def SpecializesOn (S : Set (Fin n → k)) (x : K k n) (y : (Fin n → k) → k) : Prop :=
  ∃ P Q : MvPolynomial (Fin n) k, x * polyHom k n Q = polyHom k n P ∧
    ∀ p ∈ S, MvPolynomial.eval p Q ≠ 0 ∧ y p * MvPolynomial.eval p Q = MvPolynomial.eval p P

namespace SpecializesOn

variable {S : Set (Fin n → k)} {x x' : K k n} {y y' : (Fin n → k) → k}

/-- The values on `S` are unique. -/
theorem unique (h : SpecializesOn S x y) (h' : SpecializesOn S x y') {p : Fin n → k}
    (hp : p ∈ S) : y p = y' p := by
  obtain ⟨P, Q, hx, hS⟩ := h
  obtain ⟨P', Q', hx', hS'⟩ := h'
  obtain ⟨q0, hy⟩ := hS p hp
  obtain ⟨q0', hy'⟩ := hS' p hp
  have e : P * Q' = P' * Q := polyHom_injective n (by
    rw [map_mul, map_mul, ← hx, ← hx']
    ring)
  have e' := congrArg (MvPolynomial.eval p) e
  rw [map_mul, map_mul, ← hy, ← hy'] at e'
  apply mul_right_cancel₀ (mul_ne_zero q0 q0')
  linear_combination e'

theorem mono {T : Set (Fin n → k)} (h : SpecializesOn S x y) (hT : T ⊆ S) :
    SpecializesOn T x y := by
  obtain ⟨P, Q, hx, hS⟩ := h
  exact ⟨P, Q, hx, fun p hp => hS p (hT hp)⟩

theorem congr (h : SpecializesOn S x y) (e : ∀ p ∈ S, y p = y' p) : SpecializesOn S x y' := by
  obtain ⟨P, Q, hx, hS⟩ := h
  exact ⟨P, Q, hx, fun p hp => ⟨(hS p hp).1, by rw [← e p hp]; exact (hS p hp).2⟩⟩

/-- An element with the value zero on a nonempty set is determined by a polynomial that
vanishes there. -/
theorem eq_zero_of_forall (h : SpecializesOn S x fun _ => 0) (ne : S.Nonempty)
    (inj : ∀ P : MvPolynomial (Fin n) k, (∀ p ∈ S, MvPolynomial.eval p P = 0) → P = 0) :
    x = 0 := by
  obtain ⟨P, Q, hx, hS⟩ := h
  have hP : P = 0 := inj P fun p hp => by rw [← (hS p hp).2, zero_mul]
  obtain ⟨p, hp⟩ := ne
  have hQ : polyHom k n Q ≠ 0 := fun z => (hS p hp).1 (by
    rw [polyHom_injective n (z.trans (map_zero _).symm), map_zero])
  rw [hP, map_zero] at hx
  exact (mul_eq_zero.mp hx).resolve_right hQ

theorem const (c : k) : SpecializesOn S (constHom k n c) fun _ => c :=
  ⟨MvPolynomial.C c, 1, by simp, fun _ _ => by simp⟩

theorem gen (i : Fin n) : SpecializesOn S (gens k n i) fun p => p i :=
  ⟨MvPolynomial.X i, 1, by simp, fun _ _ => by simp⟩

theorem zero : SpecializesOn S (0 : K k n) fun _ => 0 := by
  simpa using const (S := S) (n := n) (0 : k)

theorem natCast (m : ℕ) : SpecializesOn S ((m : ℕ) : K k n) fun _ => (m : k) := by
  simpa using const (S := S) (n := n) (m : k)

/-- A polynomial in the generators has its value at every point. -/
theorem poly (P : MvPolynomial (Fin n) k) :
    SpecializesOn S (polyHom k n P) fun p => MvPolynomial.eval p P :=
  ⟨P, 1, by simp, fun _ _ => by simp⟩

theorem neg (h : SpecializesOn S x y) : SpecializesOn S (-x) fun p => -y p := by
  obtain ⟨P, Q, hx, hS⟩ := h
  exact ⟨-P, Q, by rw [map_neg, ← hx]; ring, fun p hp =>
    ⟨(hS p hp).1, by rw [map_neg, ← (hS p hp).2]; ring⟩⟩

theorem add (h : SpecializesOn S x y) (h' : SpecializesOn S x' y') :
    SpecializesOn S (x + x') fun p => y p + y' p := by
  obtain ⟨P, Q, hx, hS⟩ := h
  obtain ⟨P', Q', hx', hS'⟩ := h'
  refine ⟨P * Q' + P' * Q, Q * Q', ?_, fun p hp => ⟨?_, ?_⟩⟩
  · simp only [map_add, map_mul, ← hx, ← hx']
    ring
  · rw [map_mul]
    exact mul_ne_zero (hS p hp).1 (hS' p hp).1
  · simp only [map_add, map_mul, ← (hS p hp).2, ← (hS' p hp).2]
    ring

theorem sub (h : SpecializesOn S x y) (h' : SpecializesOn S x' y') :
    SpecializesOn S (x - x') fun p => y p - y' p := by
  simpa [sub_eq_add_neg] using h.add h'.neg

theorem mul (h : SpecializesOn S x y) (h' : SpecializesOn S x' y') :
    SpecializesOn S (x * x') fun p => y p * y' p := by
  obtain ⟨P, Q, hx, hS⟩ := h
  obtain ⟨P', Q', hx', hS'⟩ := h'
  refine ⟨P * P', Q * Q', ?_, fun p hp => ⟨?_, ?_⟩⟩
  · simp only [map_mul, ← hx, ← hx']
    ring
  · rw [map_mul]
    exact mul_ne_zero (hS p hp).1 (hS' p hp).1
  · simp only [map_mul, ← (hS p hp).2, ← (hS' p hp).2]
    ring

theorem pow (h : SpecializesOn S x y) : ∀ e : ℕ, SpecializesOn S (x ^ e) fun p => y p ^ e
  | 0 => by simpa using const (S := S) (n := n) (1 : k)
  | e + 1 => by simpa only [pow_succ] using (pow h e).mul h

theorem div (h : SpecializesOn S x y) (h' : SpecializesOn S x' y')
    (nz : ∀ p ∈ S, y' p ≠ 0) : SpecializesOn S (x / x') fun p => y p / y' p := by
  obtain ⟨P, Q, hx, hS⟩ := h
  obtain ⟨P', Q', hx', hS'⟩ := h'
  have p0 : ∀ p ∈ S, MvPolynomial.eval p P' ≠ 0 := fun p hp => by
    rw [← (hS' p hp).2]
    exact mul_ne_zero (nz p hp) (hS' p hp).1
  by_cases x0 : x' = 0
  · -- then `S` is empty
    have empty : ∀ p ∈ S, False := fun p hp => by
      rw [x0, zero_mul] at hx'
      have : P' = 0 := polyHom_injective n (by rw [← hx', map_zero])
      exact p0 p hp (by rw [this, map_zero])
    exact ⟨0, 1, by simp [x0], fun p hp => (empty p hp).elim⟩
  · refine ⟨P * Q', Q * P', ?_, fun p hp => ⟨?_, ?_⟩⟩
    · simp only [map_mul, ← hx, ← hx']
      field_simp
    · rw [map_mul]
      exact mul_ne_zero (hS p hp).1 (p0 p hp)
    · have q0' := (hS' p hp).1
      have y0 := nz p hp
      simp only [map_mul, ← (hS p hp).2, ← (hS' p hp).2]
      field_simp

theorem sum {ι : Type*} (s : Finset ι) {x : ι → K k n} {y : ι → (Fin n → k) → k}
    (h : ∀ i ∈ s, SpecializesOn S (x i) (y i)) :
    SpecializesOn S (∑ i ∈ s, x i) fun p => ∑ i ∈ s, y i p := by
  induction s using Finset.cons_induction with
  | empty => simpa using zero (S := S)
  | cons i s hi ih =>
    simp only [Finset.sum_cons]
    exact (h i (Finset.mem_cons_self i s)).add
      (ih fun j hj => h j (Finset.mem_cons_of_mem hj))

theorem list_sum {α : Type*} {x : α → K k n} {y : α → (Fin n → k) → k} :
    ∀ l : List α, (∀ a ∈ l, SpecializesOn S (x a) (y a)) →
      SpecializesOn S (l.map x).sum fun p => (l.map fun a => y a p).sum
  | [], _ => by simpa using zero (S := S)
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add
      (list_sum l fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- A term evaluated at elements with values on `S` has the value of the term evaluated at
those values, where it is defined. -/
theorem eval {m : ℕ} {E : Fin m → K k n} {e' : (Fin n → k) → Fin m → k}
    (h : ∀ i, SpecializesOn S (E i) fun p => e' p i) :
    ∀ e : Term m, (∀ p ∈ S, e.Defined (e' p)) →
      SpecializesOn S (e.eval E) fun p => e.eval (e' p)
  | .const q, _ => by
    change SpecializesOn S (q : K k n) fun _ => (q : k)
    rw [← constHom_ratCast]
    exact const _
  | .gen i, _ => h i
  | .neg a, ha => (eval h a ha).neg
  | .add a b, hab => (eval h a fun p hp => (hab p hp).1).add (eval h b fun p hp => (hab p hp).2)
  | .sub a b, hab => (eval h a fun p hp => (hab p hp).1).sub (eval h b fun p hp => (hab p hp).2)
  | .mul a b, hab => (eval h a fun p hp => (hab p hp).1).mul (eval h b fun p hp => (hab p hp).2)
  | .div a b, hab =>
    (eval h a fun p hp => (hab p hp).1).div (eval h b fun p hp => (hab p hp).2.1)
      fun p hp => (hab p hp).2.2

/-- The value of a term at the generators. -/
theorem value (e : Term n) (he : ∀ p ∈ S, e.Defined p) :
    SpecializesOn S (Term.value k e) fun p => e.eval p :=
  eval (e' := fun p => p) gen e he

/-- An element of the field below has the same values one level up. -/
theorem lift {x : K k n} {y : (Fin n → k) → k} {S : Set (Fin n → k)}
    (h : SpecializesOn S x y) :
    SpecializesOn {p : Fin (n + 1) → k | (fun i => p i.castSucc) ∈ S}
      (RatFunc.C x : K k (n + 1)) fun p => y fun i => p i.castSucc := by
  obtain ⟨P, Q, hx, hS⟩ := h
  refine ⟨MvPolynomial.rename Fin.castSucc P, MvPolynomial.rename Fin.castSucc Q, ?_,
    fun p hp => ?_⟩
  · rw [polyHom_rename_castSucc, polyHom_rename_castSucc, ← hx, map_mul]
  · have := hS _ hp
    simpa only [MvPolynomial.eval_rename, Function.comp_def] using this

end SpecializesOn

end SympyProofs.Calculus.Risch
