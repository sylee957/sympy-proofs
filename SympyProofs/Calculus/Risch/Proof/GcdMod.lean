module

public import SympyProofs.Calculus.Risch.Proof.ResidueDefs
public import SympyProofs.Calculus.Risch.Proof.Hermite
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The specification of the Euclidean algorithm modulo a polynomial in the root variable
(Risch 1969, pp. 181–182). The coefficients of the polynomials in the generator are
polynomials in `z`, kept reduced modulo a modulus `m`, and every statement is about the
polynomials over the field obtained at a constant root `c` of `m`.

Reduction modulo `m` does not change the value at a root. `normalize` splits the modulus
into factors on each of which a polynomial is zero or has leading coefficient one at every
root. `bremMonic` is division with remainder by a polynomial with leading coefficient one.
`gcdMod` returns factors of the modulus that multiply to it, each with a greatest common
divisor valid at its roots. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Residue

open Polynomial

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

/-! ### Values at a constant -/

/-- The empty polynomial in the root variable has value zero. -/
theorem zeval_nil (c : k) : zeval k c ([] : Poly n) = 0 := by
  simp only [zeval, Poly.model_nil, eval_zero]

/-- The value of a product is the product of the values. -/
theorem zeval_mul (c : k) (p q : Poly n) :
    zeval k c (Poly.mul p q) = zeval k c p * zeval k c q := by
  simp only [zeval, Poly.model_mul, eval_mul]

/-- The value of a difference is the difference of the values. -/
theorem zeval_sub (c : k) (p q : Poly n) :
    zeval k c (Poly.sub p q) = zeval k c p - zeval k c q := by
  simp only [zeval, Poly.model_sub, eval_sub]

/-- The value of a negation is the negative of the value. -/
theorem zeval_neg (c : k) (p : Poly n) : zeval k c (Poly.neg p) = -zeval k c p := by
  simp only [zeval, Poly.model_neg, eval_neg]

/-- A root of a divisor is a root. -/
theorem IsRootOf.of_dvd {m m' : Poly n} {c : k} (h : IsRootOf k m' c)
    (d : Poly.model k m' ∣ Poly.model k m) : IsRootOf k m c :=
  Polynomial.IsRoot.dvd h d

/-- A modulus of length at most one is a nonzero constant and has no roots. -/
theorem not_isRootOf_of_length_le_one {m : Poly n} (nm : Poly.Normal k m) (h : m.length ≤ 1)
    (c : k) : ¬ IsRootOf k m c := by
  intro hc
  have d : (Poly.model k m).natDegree = 0 := by
    rw [nm.natDegree]
    omega
  have e := eq_C_of_natDegree_eq_zero d
  have hc' : (Poly.model k m).eval (constHom k n c) = 0 := hc
  rw [e, eval_C] at hc'
  apply nm.model_ne_zero
  rw [e, hc', C_0]

/-! ### Reduction modulo the modulus -/

/-- Reduction modulo a normal modulus `m`: the result differs from the polynomial by a
multiple of `m`, is defined, is empty or normal, and is shorter than `m`. -/
theorem zred_spec {m p : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    (hp : Poly.Defined k p) :
    Poly.model k p = Poly.model k m * Poly.model k (Poly.quot p m) + Poly.model k (zred m p) ∧
      Poly.Defined k (zred m p) ∧ (zred m p = [] ∨ Poly.Normal k (zred m p)) ∧
      (zred m p).length < m.length := by
  obtain ⟨eq, -, dr, small⟩ := Poly.rem_spec hp hm nm
  obtain ⟨mt, dt, nrm, len⟩ := Poly.trim_spec (Poly.defined_norm dr)
  rw [Poly.model_norm dr] at mt
  refine ⟨?_, dt, nrm, ?_⟩
  · rw [zred, mt]
    exact eq
  · have e : (Poly.norm (Poly.rem p m)).length = (Poly.rem p m).length := List.length_map _
    rw [zred]
    omega

/-- The reduction of a defined polynomial modulo a normal modulus is defined. -/
theorem defined_zred {m p : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    (hp : Poly.Defined k p) : Poly.Defined k (zred m p) :=
  (zred_spec hm nm hp).2.1

/-- The reduction modulo a normal modulus is shorter than the modulus. -/
theorem length_zred_lt {m p : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    (hp : Poly.Defined k p) : (zred m p).length < m.length :=
  (zred_spec hm nm hp).2.2.2

/-- The reduction is the empty list exactly when it denotes zero. -/
theorem zred_eq_nil_iff {m p : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    (hp : Poly.Defined k p) : zred m p = [] ↔ Poly.model k (zred m p) = 0 := by
  constructor
  · intro e
    rw [e, Poly.model_nil]
  · intro z
    rcases (zred_spec hm nm hp).2.2.1 with e | h
    · exact e
    · exact (h.model_ne_zero z).elim

/-- Reduction modulo `m` does not change the value at a root of `m`. -/
theorem zeval_zred {m p : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    (hp : Poly.Defined k p) {c : k} (hc : IsRootOf k m c) :
    zeval k c (zred m p) = zeval k c p := by
  obtain ⟨eq, -, -, -⟩ := zred_spec hm nm hp
  have hc' : (Poly.model k m).eval (constHom k n c) = 0 := hc
  have e := congrArg (eval (constHom k n c)) eq
  rw [eval_add, eval_mul, hc', zero_mul, zero_add] at e
  exact e.symm

/-! ### Polynomials in the generator at a constant -/

theorem bdefined_append {p q : BPoly n} (hp : BDefined k p) (hq : BDefined k q) :
    BDefined k (p ++ q) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact hp c h
  · exact hq c h

theorem bdefined_replicate_nil (j : ℕ) : BDefined k (List.replicate j ([] : Poly n)) := by
  intro c hc
  rw [List.eq_of_mem_replicate hc]
  exact Poly.defined_nil

theorem bdefined_dropLast {p : BPoly n} (hp : BDefined k p) : BDefined k p.dropLast :=
  fun c hc => hp c (List.dropLast_subset p hc)

/-- The highest written coefficient of a defined polynomial in the generator is defined. -/
theorem defined_getLastD {p : BPoly n} (hp : BDefined k p) :
    Poly.Defined k (p.getLastD []) := by
  rw [List.getLastD_eq_getLast?]
  cases h : p.getLast? with
  | none => exact Poly.defined_nil
  | some l =>
    rw [List.getLast?_eq_getElem?] at h
    exact hp l (List.mem_of_getElem? h)

/-- The coefficients of the polynomial at `c` are the values of the written coefficients. -/
theorem coeff_bmodel (c : k) (p : BPoly n) (i : ℕ) :
    (bmodel k c p).coeff i = (p[i]?.map (zeval k c)).getD 0 := by
  induction p generalizing i with
  | nil => simp [bmodel]
  | cons q qs ih =>
    cases i with
    | zero => simp [bmodel]
    | succ i => simp [bmodel, ih]

/-- The coefficients beyond the written ones vanish. -/
theorem coeff_bmodel_of_length_le (c : k) {p : BPoly n} {i : ℕ} (h : p.length ≤ i) :
    (bmodel k c p).coeff i = 0 := by simp [coeff_bmodel, List.getElem?_eq_none h]

/-- A list of `l` coefficients denotes a polynomial of degree below `l`. -/
theorem natDegree_bmodel_le (c : k) (p : BPoly n) : (bmodel k c p).natDegree ≤ p.length - 1 :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hi => coeff_bmodel_of_length_le c (by omega)

/-- The coefficient of highest written degree is the value of the last written coefficient. -/
theorem coeff_bmodel_last (c : k) (p : BPoly n) :
    (bmodel k c p).coeff (p.length - 1) = zeval k c (p.getLastD []) := by
  rw [coeff_bmodel, ← List.getLast?_eq_getElem?, List.getLastD_eq_getLast?]
  cases p.getLast? <;> simp [zeval_nil]

/-- Appending a list of coefficients shifts it by the length of the first. -/
theorem bmodel_append (c : k) (p q : BPoly n) :
    bmodel k c (p ++ q) = bmodel k c p + X ^ p.length * bmodel k c q := by
  induction p with
  | nil => simp [bmodel]
  | cons a p ih =>
    simp only [List.cons_append, bmodel_cons, ih, List.length_cons, pow_succ]
    ring

/-- A list of empty coefficients denotes zero. -/
theorem bmodel_replicate_nil (c : k) (j : ℕ) :
    bmodel k c (List.replicate j ([] : Poly n)) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, bmodel_cons, ih, zeval_nil, C_0, mul_zero, add_zero]

/-- Dropping a highest written coefficient that vanishes at `c` keeps the polynomial at
`c`. -/
theorem bmodel_dropLast {c : k} {p : BPoly n} (h : (bmodel k c p).coeff (p.length - 1) = 0) :
    bmodel k c p.dropLast = bmodel k c p := by
  ext i
  rw [coeff_bmodel, coeff_bmodel, List.getElem?_dropLast]
  by_cases hi : i < p.length - 1
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi]
    by_cases hl : i < p.length
    · have e : i = p.length - 1 := by omega
      rw [e, ← coeff_bmodel, h]
      simp
    · rw [List.getElem?_eq_none (by omega)]

/-- Multiplying every coefficient by `e` modulo `m` keeps the coefficients defined. -/
theorem bdefined_map_zmul {m e : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    (he : Poly.Defined k e) {p : BPoly n} (hp : BDefined k p) :
    BDefined k (p.map (zmul m e)) := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  exact defined_zred hm nm (Poly.defined_mul he (hp a ha))

/-- Multiplying every coefficient by `e` modulo `m` multiplies the polynomial at a root of
`m` by the value of `e`. -/
theorem bmodel_map_zmul {m e : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    (he : Poly.Defined k e) {p : BPoly n} (hp : BDefined k p) {c : k} (hc : IsRootOf k m c) :
    bmodel k c (p.map (zmul m e)) = C (zeval k c e) * bmodel k c p := by
  induction p with
  | nil => simp [bmodel]
  | cons a p ih =>
    rw [List.map_cons, bmodel_cons, bmodel_cons, ih (bdefined_cons.mp hp).2, zmul,
      zeval_zred hm nm (Poly.defined_mul he (bdefined_cons.mp hp).1) hc, zeval_mul, C_mul]
    ring

/-! ### Removing the vanishing coefficients -/

/-- Reducing every coefficient modulo `m` and removing the empty ones of highest degree
keeps the coefficients defined, does not lengthen the list, keeps the polynomial at every
root of `m`, and leaves a last coefficient that is not zero and is shorter than `m`. -/
theorem btrim_spec {m : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m) :
    ∀ {p : BPoly n}, BDefined k p →
      BDefined k (btrim m p) ∧ (btrim m p).length ≤ p.length ∧
        (∀ c : k, IsRootOf k m c → bmodel k c (btrim m p) = bmodel k c p) ∧
        ∀ l, (btrim m p).getLast? = some l →
          Poly.Defined k l ∧ Poly.model k l ≠ 0 ∧ l.length < m.length := by
  intro p
  induction p with
  | nil =>
    intro _
    exact ⟨bdefined_nil, le_rfl, fun _ _ => rfl, fun l h => by simp [btrim] at h⟩
  | cons a p ih =>
    intro hp
    have ha : Poly.Defined k a := (bdefined_cons.mp hp).1
    obtain ⟨d, len, mod, last⟩ := ih (bdefined_cons.mp hp).2
    obtain ⟨-, dz, nz, lz⟩ := zred_spec hm nm ha
    rw [btrim]
    by_cases he : (btrim m p).isEmpty
    · have e : btrim m p = [] := List.isEmpty_iff.mp he
      rw [ite_eq_left he]
      by_cases hz : (zred m a).isEmpty
      · have ez : zred m a = [] := List.isEmpty_iff.mp hz
        rw [ite_eq_left hz]
        refine ⟨bdefined_nil, by simp, fun c hc => ?_, fun l h => by simp at h⟩
        rw [bmodel_cons, ← mod c hc, e, ← zeval_zred hm nm ha hc, ez, zeval_nil, bmodel_nil,
          C_0, mul_zero, add_zero]
      · have ez : zred m a ≠ [] := fun h => hz (List.isEmpty_iff.mpr h)
        rw [ite_eq_right hz]
        refine ⟨?_, by simp, fun c hc => ?_, fun l h => ?_⟩
        · intro q hq
          rw [List.mem_singleton.mp hq]
          exact dz
        · rw [bmodel_cons, bmodel_cons, ← mod c hc, e, zeval_zred hm nm ha hc]
        · have el : zred m a = l := by simpa using h
          rw [← el]
          exact ⟨dz, (nz.resolve_left ez).model_ne_zero, lz⟩
    · rw [ite_eq_right he]
      have ne : btrim m p ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
      refine ⟨bdefined_cons.mpr ⟨dz, d⟩, by simpa using len, fun c hc => ?_, fun l h => ?_⟩
      · rw [bmodel_cons, bmodel_cons, mod c hc, zeval_zred hm nm ha hc]
      · obtain ⟨y, ys, e⟩ := List.exists_cons_of_ne_nil ne
        rw [e, List.getLast?_cons_cons, ← e] at h
        exact last l h

/-- Removing the vanishing coefficients keeps the coefficients defined. -/
theorem bdefined_btrim {m : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    {p : BPoly n} (hp : BDefined k p) : BDefined k (btrim m p) :=
  (btrim_spec hm nm hp).1

/-- Removing the vanishing coefficients does not lengthen the list. -/
theorem length_btrim_le {m : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    {p : BPoly n} (hp : BDefined k p) : (btrim m p).length ≤ p.length :=
  (btrim_spec hm nm hp).2.1

/-- Removing the coefficients that vanish modulo `m` keeps the polynomial at every root of
`m`. -/
theorem bmodel_btrim {m : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    {p : BPoly n} (hp : BDefined k p) {c : k} (hc : IsRootOf k m c) :
    bmodel k c (btrim m p) = bmodel k c p :=
  (btrim_spec hm nm hp).2.2.1 c hc

/-! ### Subtraction modulo the modulus -/

theorem bsub_nil_left (m : Poly n) (q : BPoly n) :
    bsub m [] q = q.map fun c => zred m (Poly.neg c) := by
  simp [bsub]

theorem bsub_nil_right (m : Poly n) (p : BPoly n) : bsub m p [] = p := by
  cases p <;> simp [bsub]

theorem bsub_cons_cons (m a b : Poly n) (p q : BPoly n) :
    bsub m (a :: p) (b :: q) = zred m (Poly.sub a b) :: bsub m p q := by
  simp [bsub]

/-- The difference has the length of the longer list. -/
theorem length_bsub (m : Poly n) (p q : BPoly n) :
    (bsub m p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [bsub_nil_left]
  | cons a p ih =>
    cases q with
    | nil => simp [bsub_nil_right]
    | cons b q => simp [bsub_cons_cons, ih]

/-- The difference of defined polynomials in the generator is defined. -/
theorem bdefined_bsub {m : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    {p q : BPoly n} (hp : BDefined k p) (hq : BDefined k q) : BDefined k (bsub m p q) := by
  induction p generalizing q with
  | nil =>
    rw [bsub_nil_left]
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    exact defined_zred hm nm (Poly.defined_neg (hq a ha))
  | cons a p ih =>
    cases q with
    | nil =>
      rw [bsub_nil_right]
      exact hp
    | cons b q =>
      rw [bsub_cons_cons]
      exact bdefined_cons.mpr ⟨defined_zred hm nm
        (Poly.defined_sub (bdefined_cons.mp hp).1 (bdefined_cons.mp hq).1),
        ih (bdefined_cons.mp hp).2 (bdefined_cons.mp hq).2⟩

/-- At a root of `m`, the difference modulo `m` denotes the difference. -/
theorem bmodel_bsub {m : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    {p q : BPoly n} (hp : BDefined k p) (hq : BDefined k q) {c : k} (hc : IsRootOf k m c) :
    bmodel k c (bsub m p q) = bmodel k c p - bmodel k c q := by
  induction p generalizing q with
  | nil =>
    rw [bsub_nil_left, bmodel_nil, zero_sub]
    induction q with
    | nil => simp [bmodel_nil]
    | cons b q ih =>
      rw [List.map_cons, bmodel_cons, bmodel_cons, ih (bdefined_cons.mp hq).2,
        zeval_zred hm nm (Poly.defined_neg (bdefined_cons.mp hq).1) hc, zeval_neg, C_neg]
      ring
  | cons a p ih =>
    cases q with
    | nil => rw [bsub_nil_right, bmodel_nil, sub_zero]
    | cons b q =>
      rw [bsub_cons_cons, bmodel_cons, bmodel_cons, bmodel_cons,
        ih (bdefined_cons.mp hp).2 (bdefined_cons.mp hq).2,
        zeval_zred hm nm (Poly.defined_sub (bdefined_cons.mp hp).1 (bdefined_cons.mp hq).1) hc,
        zeval_sub, C_sub]
      ring

/-! ### Pieces -/

/-- The modulus of a piece divides the modulus. -/
theorem PiecesOK.dvd {m : Poly n} {a b : BPoly n} {out : List (Poly n × BPoly n)}
    (h : PiecesOK k m a b out) {pc : Poly n × BPoly n} (hpc : pc ∈ out) :
    Poly.model k pc.1 ∣ Poly.model k m :=
  (List.dvd_prod (List.mem_map.mpr ⟨pc, hpc, rfl⟩)).trans h.prod.symm.dvd

/-- A single piece with the whole modulus, given the properties of its polynomial at every
root of the modulus. -/
theorem piecesOK_singleton {m : Poly n} {a b g : BPoly n} (hm : Poly.Defined k m)
    (nm : Poly.Normal k m) (hg : BDefined k g)
    (h : ∀ c : k, IsRootOf k m c →
      bmodel k c g ∣ bmodel k c a ∧ bmodel k c g ∣ bmodel k c b ∧
        (∃ u v : (K k n)[X], u * bmodel k c a + v * bmodel k c b = bmodel k c g) ∧
        (g = [] ∨ ((bmodel k c g).Monic ∧ (bmodel k c g).natDegree = g.length - 1))) :
    PiecesOK k m a b [(m, g)] := by
  refine ⟨fun pc hpc => ?_, fun pc hpc => ?_, ?_, fun pc hpc => ?_⟩
  · rw [List.mem_singleton.mp hpc]
    exact ⟨hm, hg⟩
  · rw [List.mem_singleton.mp hpc]
    exact nm
  · rw [List.map_singleton, List.prod_singleton]
  · rw [List.mem_singleton.mp hpc]
    exact h

/-- Pieces for `a′` and `b′` are pieces for `a` and `b` when, at every root of the modulus,
each pair is a combination of the other. -/
theorem PiecesOK.transfer {m : Poly n} {a b a' b' : BPoly n} {out : List (Poly n × BPoly n)}
    (h : PiecesOK k m a' b' out)
    (hab : ∀ c : k, IsRootOf k m c →
      (∃ x y : (K k n)[X], bmodel k c a' = x * bmodel k c a + y * bmodel k c b) ∧
      (∃ x y : (K k n)[X], bmodel k c b' = x * bmodel k c a + y * bmodel k c b) ∧
      (∃ x y : (K k n)[X], bmodel k c a = x * bmodel k c a' + y * bmodel k c b') ∧
      (∃ x y : (K k n)[X], bmodel k c b = x * bmodel k c a' + y * bmodel k c b')) :
    PiecesOK k m a b out := by
  refine ⟨h.defined, h.normal, h.prod, fun pc hpc c hc => ?_⟩
  obtain ⟨⟨x1, y1, e1⟩, ⟨x2, y2, e2⟩, ⟨x3, y3, e3⟩, ⟨x4, y4, e4⟩⟩ :=
    hab c (hc.of_dvd (h.dvd hpc))
  obtain ⟨ga, gb, ⟨u, v, bez⟩, shape⟩ := h.gcd pc hpc c hc
  refine ⟨?_, ?_, ⟨u * x1 + v * x2, u * y1 + v * y2, ?_⟩, shape⟩
  · rw [e3]
    exact dvd_add (dvd_mul_of_dvd_right ga _) (dvd_mul_of_dvd_right gb _)
  · rw [e4]
    exact dvd_add (dvd_mul_of_dvd_right ga _) (dvd_mul_of_dvd_right gb _)
  · linear_combination bez - u * e1 - v * e2

/-- Pieces for two moduli whose product is `m` are together pieces for `m`. -/
theorem PiecesOK.append {m m₁ m₂ : Poly n} {a b : BPoly n}
    {o₁ o₂ : List (Poly n × BPoly n)} (h₁ : PiecesOK k m₁ a b o₁) (h₂ : PiecesOK k m₂ a b o₂)
    (e : Poly.model k m = Poly.model k m₁ * Poly.model k m₂) : PiecesOK k m a b (o₁ ++ o₂) := by
  refine ⟨fun pc hpc => ?_, fun pc hpc => ?_, ?_, fun pc hpc => ?_⟩
  · rcases List.mem_append.mp hpc with h | h
    · exact h₁.defined pc h
    · exact h₂.defined pc h
  · rcases List.mem_append.mp hpc with h | h
    · exact h₁.normal pc h
    · exact h₂.normal pc h
  · rw [List.map_append, List.prod_append, e]
    exact h₁.prod.mul_mul h₂.prod
  · rcases List.mem_append.mp hpc with h | h
    · exact h₁.gcd pc h
    · exact h₂.gcd pc h

/-- Replacing every piece by pieces for its modulus gives pieces for the whole modulus. -/
theorem PiecesOK.flatMap {m : Poly n} {a b a' b' : BPoly n} {out : List (Poly n × BPoly n)}
    {f : Poly n × BPoly n → List (Poly n × BPoly n)} (h : PiecesOK k m a' b' out)
    (hf : ∀ pc ∈ out, PiecesOK k pc.1 a b (f pc)) : PiecesOK k m a b (out.flatMap f) := by
  refine ⟨fun pc hpc => ?_, fun pc hpc => ?_, ?_, fun pc hpc => ?_⟩
  · obtain ⟨p0, h0, hp⟩ := List.mem_flatMap.mp hpc
    exact (hf p0 h0).defined pc hp
  · obtain ⟨p0, h0, hp⟩ := List.mem_flatMap.mp hpc
    exact (hf p0 h0).normal pc hp
  · refine h.prod.trans ?_
    have step : ∀ l : List (Poly n × BPoly n),
        (∀ pc ∈ l, Associated (Poly.model k pc.1)
          ((f pc).map fun q => Poly.model k q.1).prod) →
        Associated (l.map fun pc => Poly.model k pc.1).prod
          ((l.flatMap f).map fun pc => Poly.model k pc.1).prod := by
      intro l
      induction l with
      | nil =>
        intro _
        exact Associated.refl _
      | cons x l ih =>
        intro hl
        rw [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
          List.prod_append]
        exact (hl x List.mem_cons_self).mul_mul
          (ih fun pc hpc => hl pc (List.mem_cons_of_mem _ hpc))
    exact step out fun pc hpc => (hf pc hpc).prod
  · obtain ⟨p0, h0, hp⟩ := List.mem_flatMap.mp hpc
    exact (hf p0 h0).gcd pc hp

/-! ### Splitting the modulus -/

theorem normalize_zero (m : Poly n) (p : BPoly n) : normalize 0 m p = [(m, btrim m p)] := by
  simp only [normalize]

theorem normalize_succ_none {fuel : ℕ} {m : Poly n} {p : BPoly n}
    (h : (btrim m p).getLast? = none) : normalize (fuel + 1) m p = [(m, [])] := by
  simp only [normalize, h]

theorem normalize_succ_some {fuel : ℕ} {m l : Poly n} {p : BPoly n}
    (h : (btrim m p).getLast? = some l) :
    normalize (fuel + 1) m p =
      if Nat.ble (Poly.trim (Poly.norm (Poly.gcd l m).1)).length 1 then
        [(m, (btrim m p).map (zmul m (zred m (Hermite.scaleInv
          (Poly.coeff (Poly.trim (Poly.norm (Poly.gcd l m).1)) 0) (Poly.gcd l m).2.1))))]
      else normalize fuel (Poly.trim (Poly.norm (Poly.gcd l m).1)) (btrim m p) ++
        normalize fuel
          (Poly.trim (Poly.norm (Poly.quot m (Poly.trim (Poly.norm (Poly.gcd l m).1)))))
          (btrim m p) := by
  simp only [normalize, h]

/-- `normalize` with the modulus as a variable of the induction on the fuel. -/
theorem normalize_aux : ∀ (fuel : ℕ) {m : Poly n} {p : BPoly n}, Poly.Defined k m →
    Poly.Normal k m → BDefined k p → m.length ≤ fuel + 1 →
    PiecesOK k m p [] (normalize fuel m p) ∧
      ∀ pc ∈ normalize fuel m p, pc.2.length ≤ p.length ∧
        ∀ c : k, IsRootOf k pc.1 c →
          ∃ w : K k n, w ≠ 0 ∧ bmodel k c pc.2 = C w * bmodel k c p := by
  intro fuel
  induction fuel with
  | zero =>
    intro m p hm nm hp hl
    obtain ⟨dp', lenp', -, -⟩ := btrim_spec hm nm hp
    have noroot := not_isRootOf_of_length_le_one nm hl
    rw [normalize_zero]
    refine ⟨piecesOK_singleton hm nm dp' fun c hc => (noroot c hc).elim, fun pc hpc => ?_⟩
    rw [List.mem_singleton.mp hpc]
    exact ⟨lenp', fun c hc => (noroot c hc).elim⟩
  | succ fuel ih =>
    intro m p hm nm hp hl
    obtain ⟨dp', lenp', modp', lastp'⟩ := btrim_spec hm nm hp
    cases hlast : (btrim m p).getLast? with
    | none =>
      have e : btrim m p = [] := List.getLast?_eq_none_iff.mp hlast
      have z : ∀ c : k, IsRootOf k m c → bmodel k c p = 0 := fun c hc => by
        rw [← modp' c hc, e, bmodel_nil]
      rw [normalize_succ_none hlast]
      refine ⟨piecesOK_singleton hm nm bdefined_nil fun c hc => ?_, fun pc hpc => ?_⟩
      · rw [bmodel_nil, z c hc]
        exact ⟨dvd_rfl, dvd_rfl, ⟨0, 0, by ring⟩, Or.inl rfl⟩
      · rw [List.mem_singleton.mp hpc]
        refine ⟨Nat.zero_le _, fun c hc => ⟨1, one_ne_zero, ?_⟩⟩
        rw [bmodel_nil, z c hc, mul_zero]
    | some l =>
      obtain ⟨dl, ml0, ll⟩ := lastp' l hlast
      rw [normalize_succ_some hlast]
      obtain ⟨dg, du, -, bez, gl, gm⟩ := Poly.gcd_spec dl hm
      obtain ⟨mt, dhh, nrm, -⟩ := Poly.trim_spec (Poly.defined_norm dg)
      rw [Poly.model_norm dg] at mt
      obtain ⟨hh, hhh⟩ : ∃ hh, hh = Poly.trim (Poly.norm (Poly.gcd l m).1) := ⟨_, rfl⟩
      rw [← hhh] at mt dhh nrm ⊢
      rw [← mt] at bez gl gm
      have nhh : Poly.Normal k hh := nrm.resolve_left fun e =>
        nm.model_ne_zero (zero_dvd_iff.mp (by rw [e, Poly.model_nil] at gm; exact gm))
      by_cases hle : hh.length ≤ 1
      · -- the last coefficient is invertible modulo `m`
        rw [ite_eq_left (Nat.ble_eq.mpr hle)]
        have d0 : (Poly.model k hh).natDegree = 0 := by
          rw [nhh.natDegree]
          omega
        have eC : Poly.model k hh = C (Term.value k (Poly.coeff hh 0)) := by
          rw [Poly.value_coeff]
          exact eq_C_of_natDegree_eq_zero d0
        have h0 : Term.value k (Poly.coeff hh 0) ≠ 0 := fun z =>
          nhh.model_ne_zero (by rw [eC, z, C_0])
        have dinv0 := Hermite.defined_scaleInv (Poly.defined_coeff dhh 0) h0 du
        obtain ⟨inv, hinv⟩ :
            ∃ inv, inv = zred m (Hermite.scaleInv (Poly.coeff hh 0) (Poly.gcd l m).2.1) :=
          ⟨_, rfl⟩
        rw [← hinv]
        have dinv : Poly.Defined k inv := hinv ▸ defined_zred hm nm dinv0
        have one : ∀ c : k, IsRootOf k m c → zeval k c inv * zeval k c l = 1 := by
          intro c hc
          have hc' : (Poly.model k m).eval (constHom k n c) = 0 := hc
          have e := congrArg (eval (constHom k n c)) bez
          rw [eval_add, eval_mul, eval_mul, hc', mul_zero, add_zero, eC, eval_C] at e
          rw [hinv, zeval_zred hm nm dinv0 hc]
          simp only [zeval]
          rw [Hermite.model_scaleInv, eval_mul, eval_C, mul_assoc, e]
          exact inv_mul_cancel₀ h0
        have wne : ∀ c : k, IsRootOf k m c → zeval k c inv ≠ 0 := fun c hc z => by
          have := one c hc
          rw [z, zero_mul] at this
          exact zero_ne_one this
        have key : ∀ c : k, IsRootOf k m c →
            bmodel k c ((btrim m p).map (zmul m inv)) = C (zeval k c inv) * bmodel k c p :=
          fun c hc => by rw [bmodel_map_zmul hm nm dinv dp' hc, modp' c hc]
        refine ⟨piecesOK_singleton hm nm (bdefined_map_zmul hm nm dinv dp') fun c hc =>
          ⟨?_, ?_, ?_, Or.inr ?_⟩, fun pc hpc => ?_⟩
        · rw [key c hc]
          exact Dvd.intro_left (C (zeval k c inv)⁻¹) (by
            rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ (wne c hc), C_1, one_mul])
        · rw [bmodel_nil]
          exact dvd_zero _
        · exact ⟨C (zeval k c inv), 0, by rw [key c hc, bmodel_nil]; ring⟩
        · have cf : (bmodel k c ((btrim m p).map (zmul m inv))).coeff
              (((btrim m p).map (zmul m inv)).length - 1) = 1 := by
            rw [bmodel_map_zmul hm nm dinv dp' hc, coeff_C_mul, List.length_map,
              coeff_bmodel_last, List.getLastD_eq_getLast?, hlast]
            exact one c hc
          have dle := natDegree_bmodel_le c ((btrim m p).map (zmul m inv))
          exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ dle cf,
            natDegree_eq_of_le_of_coeff_ne_zero dle (by rw [cf]; exact one_ne_zero)⟩
        · rw [List.mem_singleton.mp hpc]
          exact ⟨by simpa using lenp', fun c hc => ⟨_, wne c hc, key c hc⟩⟩
      · -- the modulus splits
        rw [ite_eq_right (fun h => hle (Nat.ble_eq.mp h))]
        have eq := Poly.quot_of_dvd hm dhh nhh gm
        have dq := (Poly.rem_spec hm dhh nhh).2.1
        obtain ⟨mt2, dm2, nrm2, -⟩ := Poly.trim_spec (Poly.defined_norm dq)
        rw [Poly.model_norm dq] at mt2
        obtain ⟨m2, hm2⟩ : ∃ m2, m2 = Poly.trim (Poly.norm (Poly.quot m hh)) := ⟨_, rfl⟩
        rw [← hm2] at mt2 dm2 nrm2 ⊢
        rw [← mt2] at eq
        have q0 : Poly.model k m2 ≠ 0 := fun z => nm.model_ne_zero (by rw [eq, z, mul_zero])
        have nm2 : Poly.Normal k m2 := nrm2.resolve_left fun e =>
          q0 (by rw [e, Poly.model_nil])
        have deg := congrArg natDegree eq
        rw [natDegree_mul nhh.model_ne_zero q0, nm.natDegree, nhh.natDegree, nm2.natDegree]
          at deg
        have m2pos : 0 < m2.length := List.length_pos_iff.mpr nm2.ne_nil
        have lpos : 0 < l.length :=
          List.length_pos_iff.mpr fun e => ml0 (by rw [e, Poly.model_nil])
        have dl' := natDegree_le_of_dvd gl ml0
        rw [nhh.natDegree] at dl'
        have ldeg := Poly.natDegree_model_le (k := k) l
        obtain ⟨ok1, rest1⟩ := ih dhh nhh dp' (by omega)
        obtain ⟨ok2, rest2⟩ := ih dm2 nm2 dp' (by omega)
        have okm : PiecesOK k m (btrim m p) []
            (normalize fuel hh (btrim m p) ++ normalize fuel m2 (btrim m p)) :=
          ok1.append ok2 eq
        refine ⟨okm.transfer fun c hc => ?_, fun pc hpc => ?_⟩
        · rw [modp' c hc]
          exact ⟨⟨1, 0, by ring⟩, ⟨0, 0, by rw [bmodel_nil]; ring⟩, ⟨1, 0, by ring⟩,
            ⟨0, 0, by rw [bmodel_nil]; ring⟩⟩
        · have hcm : ∀ c : k, IsRootOf k pc.1 c → IsRootOf k m c :=
            fun c hc => hc.of_dvd (okm.dvd hpc)
          have rest : pc.2.length ≤ (btrim m p).length ∧ ∀ c : k, IsRootOf k pc.1 c →
              ∃ w : K k n, w ≠ 0 ∧ bmodel k c pc.2 = C w * bmodel k c (btrim m p) := by
            rcases List.mem_append.mp hpc with h | h
            · exact rest1 pc h
            · exact rest2 pc h
          refine ⟨rest.1.trans lenp', fun c hc => ?_⟩
          obtain ⟨w, w0, e⟩ := rest.2 c hc
          exact ⟨w, w0, by rw [e, modp' c (hcm c hc)]⟩

/-- `normalize` splits a normal modulus `m` into pieces `(mⱼ, gⱼ)` whose moduli multiply to
`m` up to a unit. At every root `c` of `mⱼ` the polynomial `gⱼ(c)` is a nonzero constant
multiple of `p(c)`, and it is zero, with `gⱼ` the empty list, or has leading coefficient one
and degree one less than the length of `gⱼ`. No `gⱼ` is longer than `p`. -/
theorem normalize_spec {m : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    {p : BPoly n} (hp : BDefined k p) : ∀ fuel, m.length ≤ fuel + 1 →
    PiecesOK k m p [] (normalize fuel m p) ∧
      ∀ pc ∈ normalize fuel m p, pc.2.length ≤ p.length ∧
        ∀ c : k, IsRootOf k pc.1 c →
          ∃ w : K k n, w ≠ 0 ∧ bmodel k c pc.2 = C w * bmodel k c p :=
  fun fuel hl => normalize_aux fuel hm nm hp hl

/-! ### Division by a polynomial with leading coefficient one -/

/-- `bremMonic` returns a defined list shorter than the divisor `b`, once the fuel is at
least the number of coefficients to remove. At every root `c` of `m` at which `b(c)` has
leading coefficient one and the degree written, the result is a remainder of `a(c)` on
division by `b(c)`. -/
theorem bremMonic_spec {m : Poly n} (hm : Poly.Defined k m) (nm : Poly.Normal k m)
    {b : BPoly n} (hb : BDefined k b) (b0 : b ≠ []) :
    ∀ (fuel : ℕ) {a : BPoly n}, BDefined k a → a.length ≤ fuel + (b.length - 1) →
      BDefined k (bremMonic m b fuel a) ∧ (bremMonic m b fuel a).length < b.length ∧
        ∀ c : k, IsRootOf k m c → (bmodel k c b).Monic →
          (bmodel k c b).natDegree = b.length - 1 →
          ∃ q : (K k n)[X],
            bmodel k c a = q * bmodel k c b + bmodel k c (bremMonic m b fuel a) := by
  have bpos : 0 < b.length := List.length_pos_iff.mpr b0
  intro fuel
  induction fuel with
  | zero =>
    intro a ha hl
    rw [bremMonic]
    exact ⟨ha, by omega, fun c _ _ _ => ⟨0, by ring⟩⟩
  | succ fuel ih =>
    intro a ha hl
    rw [bremMonic]
    by_cases hlt : a.length < b.length
    · rw [ite_eq_left (Nat.blt_eq.mpr hlt)]
      exact ⟨ha, hlt, fun c _ _ _ => ⟨0, by ring⟩⟩
    · rw [ite_eq_right (fun h => hlt (Nat.blt_eq.mp h))]
      dsimp only
      obtain ⟨cc, hcc⟩ : ∃ cc, cc = a.getLastD [] := ⟨_, rfl⟩
      rw [← hcc]
      have dcc : Poly.Defined k cc := hcc ▸ defined_getLastD ha
      have dsh : BDefined k (List.replicate (a.length - b.length) [] ++ b.map (zmul m cc)) :=
        bdefined_append (bdefined_replicate_nil _) (bdefined_map_zmul hm nm dcc hb)
      have ds := bdefined_bsub hm nm ha dsh
      have len : (bsub m a
          (List.replicate (a.length - b.length) [] ++ b.map (zmul m cc))).length = a.length := by
        rw [length_bsub, List.length_append, List.length_replicate, List.length_map]
        omega
      obtain ⟨dr, small, div⟩ := ih (bdefined_dropLast ds) (by
        rw [List.length_dropLast, len]
        omega)
      refine ⟨dr, small, fun c hc mon deg => ?_⟩
      obtain ⟨q, hq⟩ := div c hc mon deg
      have val : bmodel k c (bsub m a
            (List.replicate (a.length - b.length) [] ++ b.map (zmul m cc))) =
          bmodel k c a - X ^ (a.length - b.length) * (C (zeval k c cc) * bmodel k c b) := by
        rw [bmodel_bsub hm nm ha dsh hc, bmodel_append, bmodel_replicate_nil,
          List.length_replicate, bmodel_map_zmul hm nm dcc hb hc, zero_add]
      have top : (bmodel k c (bsub m a
            (List.replicate (a.length - b.length) [] ++ b.map (zmul m cc)))).coeff
          ((bsub m a
            (List.replicate (a.length - b.length) [] ++ b.map (zmul m cc))).length - 1) = 0 := by
        rw [len, val, coeff_sub, coeff_bmodel_last, ← hcc,
          show a.length - 1 = (b.length - 1) + (a.length - b.length) by omega, coeff_X_pow_mul,
          coeff_C_mul, ← deg, mon.coeff_natDegree, mul_one, sub_self]
      rw [bmodel_dropLast top, val] at hq
      exact ⟨q + X ^ (a.length - b.length) * C (zeval k c cc), by linear_combination hq⟩

/-! ### The Euclidean algorithm -/

/-- The Euclidean algorithm modulo a normal modulus `m`, with fuel exceeding the length of
`b`, returns pieces `(mⱼ, gⱼ)` whose moduli multiply to `m` up to a unit. At every root `c`
of `mⱼ` the polynomial `gⱼ(c)` is a greatest common divisor of `a(c)` and `b(c)`: it divides
both and is a combination of them, and it is zero, with `gⱼ` the empty list, or has leading
coefficient one and degree one less than the length of `gⱼ`. -/
theorem gcdMod_spec : ∀ (fuel : ℕ) {m : Poly n} {a b : BPoly n}, Poly.Defined k m →
    Poly.Normal k m → BDefined k a → BDefined k b → b.length < fuel →
    PiecesOK k m a b (gcdMod fuel m a b) := by
  intro fuel
  induction fuel with
  | zero =>
    intro m a b _ _ _ _ h
    exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro m a b hm nm ha hb hl
    obtain ⟨ok, rest⟩ := normalize_aux m.length hm nm hb (Nat.le_succ _)
    rw [gcdMod]
    refine ok.flatMap fun pc hpc => ?_
    obtain ⟨dm, dg⟩ := ok.defined pc hpc
    have nmj := ok.normal pc hpc
    obtain ⟨len, scal⟩ := rest pc hpc
    change PiecesOK k pc.1 a b (if pc.2.isEmpty then _ else _)
    by_cases he : pc.2.isEmpty
    · -- `b` vanishes at the roots of this piece
      rw [ite_eq_left he]
      have e : pc.2 = [] := List.isEmpty_iff.mp he
      obtain ⟨ok2, -⟩ := normalize_aux pc.1.length dm nmj ha (Nat.le_succ _)
      refine ok2.transfer fun c hc => ?_
      obtain ⟨w, w0, hw⟩ := scal c hc
      rw [e, bmodel_nil] at hw
      have bz : bmodel k c b = 0 := by
        rcases mul_eq_zero.mp hw.symm with h | h
        · exact absurd (C_eq_zero.mp h) w0
        · exact h
      exact ⟨⟨1, 0, by ring⟩, ⟨0, 0, by rw [bmodel_nil]; ring⟩, ⟨1, 0, by ring⟩,
        ⟨0, 0, by rw [bz]; ring⟩⟩
    · -- `b` has leading coefficient one at the roots of this piece
      rw [ite_eq_right he]
      have ne : pc.2 ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
      obtain ⟨dr, small, div⟩ :=
        bremMonic_spec dm nmj dg ne a.length ha (Nat.le_add_right _ _)
      have ok2 := ih dm nmj dg dr (by omega)
      refine ok2.transfer fun c hc => ?_
      obtain ⟨w, w0, hw⟩ := scal c hc
      obtain ⟨-, -, -, shape⟩ := ok.gcd pc hpc c hc
      obtain ⟨mon, deg⟩ := shape.resolve_left ne
      obtain ⟨q, hq⟩ := div c hc mon deg
      refine ⟨⟨0, C w, by linear_combination hw⟩, ⟨1, -(q * C w), by
        linear_combination -hq - q * hw⟩, ⟨q, 1, by linear_combination hq⟩, ⟨C w⁻¹, 0, ?_⟩⟩
      rw [hw, zero_mul, add_zero, ← mul_assoc, ← C_mul, inv_mul_cancel₀ w0, C_1, one_mul]

/-! ### The moduli of the pieces are not constant -/

/-- When the modulus has at least two coefficients, so has the modulus of every piece
returned by `normalize`. -/
theorem normalize_length : ∀ (fuel : ℕ) {m : Poly n} {p : BPoly n}, Poly.Defined k m →
    Poly.Normal k m → BDefined k p → 2 ≤ m.length →
    ∀ pc ∈ normalize fuel m p, 2 ≤ pc.1.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro m p _ _ _ h2 pc hpc
    rw [normalize_zero] at hpc
    rw [List.mem_singleton.mp hpc]
    exact h2
  | succ fuel ih =>
    intro m p hm nm hp h2 pc hpc
    obtain ⟨dp', -, -, lastp'⟩ := btrim_spec hm nm hp
    cases hlast : (btrim m p).getLast? with
    | none =>
      rw [normalize_succ_none hlast] at hpc
      rw [List.mem_singleton.mp hpc]
      exact h2
    | some l =>
      obtain ⟨dl, ml0, ll⟩ := lastp' l hlast
      rw [normalize_succ_some hlast] at hpc
      obtain ⟨dg, -, -, -, gl, gm⟩ := Poly.gcd_spec dl hm
      obtain ⟨mt, dhh, nrm, -⟩ := Poly.trim_spec (Poly.defined_norm dg)
      rw [Poly.model_norm dg] at mt
      obtain ⟨hh, hhh⟩ : ∃ hh, hh = Poly.trim (Poly.norm (Poly.gcd l m).1) := ⟨_, rfl⟩
      rw [← hhh] at mt dhh nrm hpc
      rw [← mt] at gl gm
      have nhh : Poly.Normal k hh := nrm.resolve_left fun e =>
        nm.model_ne_zero (zero_dvd_iff.mp (by rw [e, Poly.model_nil] at gm; exact gm))
      by_cases hle : hh.length ≤ 1
      · rw [ite_eq_left (Nat.ble_eq.mpr hle)] at hpc
        rw [List.mem_singleton.mp hpc]
        exact h2
      · rw [ite_eq_right (fun h => hle (Nat.ble_eq.mp h))] at hpc
        have eq := Poly.quot_of_dvd hm dhh nhh gm
        have dq := (Poly.rem_spec hm dhh nhh).2.1
        obtain ⟨mt2, dm2, nrm2, -⟩ := Poly.trim_spec (Poly.defined_norm dq)
        rw [Poly.model_norm dq] at mt2
        obtain ⟨m2, hm2⟩ : ∃ m2, m2 = Poly.trim (Poly.norm (Poly.quot m hh)) := ⟨_, rfl⟩
        rw [← hm2] at mt2 dm2 nrm2 hpc
        rw [← mt2] at eq
        have q0 : Poly.model k m2 ≠ 0 := fun z => nm.model_ne_zero (by rw [eq, z, mul_zero])
        have nm2 : Poly.Normal k m2 := nrm2.resolve_left fun e =>
          q0 (by rw [e, Poly.model_nil])
        have deg := congrArg natDegree eq
        rw [natDegree_mul nhh.model_ne_zero q0, nm.natDegree, nhh.natDegree, nm2.natDegree]
          at deg
        have lpos : 0 < l.length :=
          List.length_pos_iff.mpr fun e => ml0 (by rw [e, Poly.model_nil])
        have dl' := natDegree_le_of_dvd gl ml0
        rw [nhh.natDegree] at dl'
        have ldeg := Poly.natDegree_model_le (k := k) l
        rcases List.mem_append.mp hpc with h | h
        · exact ih dhh nhh dp' (by omega) pc h
        · exact ih dm2 nm2 dp' (by omega) pc h

/-- When the modulus has at least two coefficients, so has the modulus of every piece
returned by the Euclidean algorithm. -/
theorem gcdMod_length : ∀ (fuel : ℕ) {m : Poly n} {a b : BPoly n}, Poly.Defined k m →
    Poly.Normal k m → BDefined k a → BDefined k b → 2 ≤ m.length →
    ∀ pc ∈ gcdMod fuel m a b, 2 ≤ pc.1.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro m a b _ _ _ _ h2 pc hpc
    rw [gcdMod] at hpc
    rw [List.mem_singleton.mp hpc]
    exact h2
  | succ fuel ih =>
    intro m a b hm nm ha hb h2 pc hpc
    obtain ⟨ok, -⟩ := normalize_aux m.length hm nm hb (Nat.le_succ _)
    rw [gcdMod] at hpc
    obtain ⟨p0, h0, hp⟩ := List.mem_flatMap.mp hpc
    obtain ⟨dm, dg⟩ := ok.defined p0 h0
    have nmj := ok.normal p0 h0
    have l2 := normalize_length m.length hm nm hb h2 p0 h0
    change pc ∈ (if p0.2.isEmpty then _ else _) at hp
    by_cases he : p0.2.isEmpty
    · rw [ite_eq_left he] at hp
      exact normalize_length _ dm nmj ha l2 pc hp
    · rw [ite_eq_right he] at hp
      have ne : p0.2 ≠ [] := fun h => he (List.isEmpty_iff.mpr h)
      obtain ⟨dr, -, -⟩ := bremMonic_spec dm nmj dg ne a.length ha (Nat.le_add_right _ _)
      exact ih dm nmj dg dr l2 pc hp

end SympyProofs.Calculus.Risch.Residue
