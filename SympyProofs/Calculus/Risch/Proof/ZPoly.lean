module

public import SympyProofs.Calculus.Risch.Program.ZPoly
public import SympyProofs.Calculus.Risch.Spec.Field
public import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The specification of fraction-free lowest terms. A polynomial with integer coefficients
has a value at any values of its variables in a field, and the arithmetic, exact division,
the fractions and `normFF` are specified by values. The greatest common divisors are not
specified at all: what they return is used only after exact division by it has succeeded,
so `normFF` keeps the value of every defined term whatever they return. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

namespace ZP

variable {F : Type*} [Field F]

/-! ### Values -/

/-- Horner's evaluation `c₀ + x (c₁ + x (…))` of a coefficient list. -/
def horner {α : Type*} (f : α → F) (x : F) : List α → F
  | [] => 0
  | c :: cs => f c + x * horner f x cs

/-- The value of a polynomial at values of its variables. -/
def eval : (n : ℕ) → (Fin n → F) → ZP n → F
  | 0, _, a => (toInt a : F)
  | n + 1, g, p => horner (eval n fun i => g i.castSucc) (g (Fin.last n)) (toList p)

@[simp] theorem toList_ofList {n : ℕ} (l : List (ZP n)) : toList (ofList l) = l := rfl

@[simp] theorem toInt_ofInt (a : ℤ) : toInt (ofInt a) = a := rfl

theorem eval_zero_level (g : Fin 0 → F) (a : ZP 0) : eval 0 g a = (toInt a : F) := rfl

theorem eval_succ {n : ℕ} (g : Fin (n + 1) → F) (p : ZP (n + 1)) :
    eval (n + 1) g p = horner (eval n fun i => g i.castSucc) (g (Fin.last n)) (toList p) :=
  rfl

/-! ### Coefficient lists -/

section Horner

variable {α : Type} (f : α → F) (x : F)

@[simp] theorem horner_nil : horner f x [] = 0 := rfl

@[simp] theorem horner_cons (c : α) (cs : List α) :
    horner f x (c :: cs) = f c + x * horner f x cs := rfl

theorem horner_addL {add : α → α → α} (h : ∀ a b, f (add a b) = f a + f b) :
    ∀ p q : List α, horner f x (addL add p q) = horner f x p + horner f x q
  | [], q => by simp [addL]
  | a :: p, [] => by simp [addL]
  | a :: p, b :: q => by
    rw [addL, horner_cons, horner_cons, horner_cons, h, horner_addL h p q]
    ring

theorem horner_trimL {z : α → Bool} (hz : ∀ a, z a = true → f a = 0) :
    ∀ l : List α, horner f x (trimL z l) = horner f x l
  | [] => rfl
  | a :: as => by
    have ih := horner_trimL hz as
    cases h : trimL z as with
    | nil =>
      rw [h, horner_nil] at ih
      by_cases hza : z a = true
      · simp [trimL, h, hza, ← ih, hz a hza]
      · simp [trimL, h, hza, ← ih]
    | cons b bs =>
      rw [h] at ih
      simp [trimL, h, ih]

theorem horner_map {β : Type} (h : β → α) :
    ∀ l : List β, horner f x (l.map h) = horner (fun b => f (h b)) x l
  | [] => rfl
  | b :: l => by simp [horner_map h l]

theorem horner_replicate_append {z : α} (hz : f z = 0) :
    ∀ (k : ℕ) (l : List α), horner f x (List.replicate k z ++ l) = x ^ k * horner f x l
  | 0, l => by simp
  | k + 1, l => by
    rw [List.replicate_succ, List.cons_append, horner_cons, hz,
      horner_replicate_append hz k l]
    ring

theorem horner_map_neg {neg : α → α} (h : ∀ a, f (neg a) = -f a) :
    ∀ l : List α, horner f x (l.map neg) = -horner f x l
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, horner_cons, h, horner_map_neg h l]
    ring

theorem horner_map_mul {mul : α → α → α} (h : ∀ a b, f (mul a b) = f a * f b) (a : α) :
    ∀ q : List α, horner f x (q.map (mul a)) = f a * horner f x q
  | [] => by simp
  | b :: q => by
    simp only [List.map_cons, horner_cons, h, horner_map_mul h a q]
    ring

theorem horner_mulL {z : α} {add mul : α → α → α} (hz : f z = 0)
    (hadd : ∀ a b, f (add a b) = f a + f b) (hmul : ∀ a b, f (mul a b) = f a * f b) :
    ∀ p q : List α, horner f x (mulL z add mul p q) = horner f x p * horner f x q
  | [], q => by simp [mulL]
  | a :: p, q => by
    rw [mulL, horner_addL f x hadd, horner_map_mul f x hmul, horner_cons, hz,
      horner_mulL hz hadd hmul p q, horner_cons]
    ring

end Horner

/-! ### Arithmetic -/

theorem eval_zero : ∀ (n : ℕ) (g : Fin n → F), eval n g (zero n) = 0
  | 0, _ => by simp [eval, zero]
  | _ + 1, _ => rfl

theorem eval_of_isZero : ∀ {n : ℕ} (g : Fin n → F) {p : ZP n}, isZero n p = true →
    eval n g p = 0
  | 0, _, a, h => by
    have : toInt a = 0 := by simpa [isZero] using h
    simp [eval, this]
  | _ + 1, _, p, h => by
    have : toList p = [] := List.isEmpty_iff.mp h
    rw [eval_succ, this, horner_nil]

theorem eval_add : ∀ (n : ℕ) (g : Fin n → F) (p q : ZP n),
    eval n g (add n p q) = eval n g p + eval n g q
  | 0, _, a, b => by simp [eval, add]
  | n + 1, g, p, q => by
    rw [eval_succ, eval_succ, eval_succ, add, toList_ofList,
      horner_trimL _ _ fun a h => eval_of_isZero _ h, horner_addL _ _ (eval_add n _)]

theorem eval_neg : ∀ (n : ℕ) (g : Fin n → F) (p : ZP n), eval n g (neg n p) = -eval n g p
  | 0, _, a => by simp [eval, neg]
  | n + 1, g, p => by
    rw [eval_succ, eval_succ, neg, toList_ofList, horner_map_neg _ _ (eval_neg n _)]

theorem eval_sub (n : ℕ) (g : Fin n → F) (p q : ZP n) :
    eval n g (sub n p q) = eval n g p - eval n g q := by
  rw [sub, eval_add, eval_neg, sub_eq_add_neg]

theorem eval_mul : ∀ (n : ℕ) (g : Fin n → F) (p q : ZP n),
    eval n g (mul n p q) = eval n g p * eval n g q
  | 0, _, a, b => by simp [eval, mul]
  | n + 1, g, p, q => by
    unfold mul
    split
    · rename_i h
      rw [eval_zero]
      simp only [Bool.or_eq_true, List.isEmpty_iff] at h
      rcases h with h | h <;> simp [eval_succ, h]
    · rw [eval_succ, toList_ofList, horner_trimL _ _ fun a h => eval_of_isZero _ h,
        horner_mulL _ _ (eval_zero n _) (eval_add n _) (eval_mul n _), eval_succ, eval_succ]

theorem eval_const : ∀ (n : ℕ) (g : Fin n → F) (a : ℤ), eval n g (const n a) = (a : F)
  | 0, _, _ => rfl
  | n + 1, g, a => by
    rw [eval_succ, const, toList_ofList]
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha, eval_const n]

theorem eval_one (n : ℕ) (g : Fin n → F) : eval n g (one n) = 1 := by
  rw [one, eval_const, Int.cast_one]

theorem eval_var : ∀ (n : ℕ) (g : Fin n → F) (i : Fin n), eval n g (var n i) = g i
  | 0, _, i => i.elim0
  | n + 1, g, i => by
    unfold var
    split
    · rename_i h
      have e : i = Fin.last n := Fin.ext h
      subst e
      simp [eval_succ, eval_zero, eval_one]
    · rw [eval_succ, toList_ofList, horner_cons, horner_nil, mul_zero, add_zero, eval_var n]
      rfl

theorem eq_of_beqL {α : Type} {e : α → α → Bool} (he : ∀ a b, e a b = true → a = b) :
    ∀ p q : List α, beqL e p q = true → p = q
  | [], [], _ => rfl
  | a :: p, b :: q, h => by
    simp only [beqL, Bool.and_eq_true] at h
    rw [he a b h.1, eq_of_beqL he p q h.2]
  | [], _ :: _, h => by simp [beqL] at h
  | _ :: _, [], h => by simp [beqL] at h

theorem eq_of_beq : ∀ (n : ℕ) {p q : ZP n}, beq n p q = true → p = q
  | 0, a, b, h => (beq_iff_eq.mp h : toInt a = toInt b)
  | n + 1, p, q, h => eq_of_beqL (fun _ _ => eq_of_beq n) (toList p) (toList q) h

theorem eval_of_isOne {n : ℕ} (g : Fin n → F) {p : ZP n} (h : isOne n p = true) :
    eval n g p = 1 := by
  rw [eq_of_beq n h, eval_one]

theorem leadInt_zero : ∀ n, leadInt n (zero n) = 0
  | 0 => rfl
  | n + 1 => leadInt_zero n

theorem eval_of_isConst : ∀ (n : ℕ) (g : Fin n → F) {p : ZP n}, isConst n p = true →
    eval n g p = (leadInt n p : F)
  | 0, _, _, _ => rfl
  | n + 1, g, p, h => by
    have lead_eq : leadInt (n + 1) p = leadInt n ((toList p).getLastD (zero n)) := rfl
    rw [lead_eq, eval_succ]
    rcases hp : toList p with _ | ⟨c, _ | ⟨c', cs⟩⟩
    · simp [leadInt_zero]
    · have hc : isConst n c = true := by simpa [isConst, hp] using h
      simp [eval_of_isConst n _ hc]
    · simp [isConst, hp] at h

/-! ### Exact division -/

theorem horner_subShift (n : ℕ) (g : Fin n → F) (x : F) (p : List (ZP n)) (c : ZP n)
    (k : ℕ) (q : List (ZP n)) :
    horner (eval n g) x (subShift n p c k q) =
      horner (eval n g) x p - x ^ k * (eval n g c * horner (eval n g) x q) := by
  rw [subShift, horner_trimL _ _ fun a h => eval_of_isZero g h, horner_addL _ _ (eval_add n g),
    horner_replicate_append _ _ (eval_zero n g), horner_map]
  have : horner (fun e => eval n g (neg n (mul n c e))) x q =
      -eval n g c * horner (eval n g) x q := by
    induction q with
    | nil => simp
    | cons e q ih =>
      rw [horner_cons, horner_cons, ih, eval_neg, eval_mul]
      ring
  rw [this]
  ring

theorem divLoop_spec (n : ℕ) (g : Fin n → F) (x : F) (dex : ZP n → ZP n → Option (ZP n))
    (dl : List (ZP n)) (ld : ZP n) :
    ∀ (fuel : ℕ) (p q : List (ZP n)), divLoop n dex dl ld fuel p = some q →
      horner (eval n g) x p = horner (eval n g) x q * horner (eval n g) x dl
  | 0, p, q, h => by simp [divLoop] at h
  | fuel + 1, p, q, h => by
    unfold divLoop at h
    split at h
    · rename_i hp
      cases h
      rw [List.isEmpty_iff.mp hp]
      simp
    · split at h
      · contradiction
      · split at h
        · contradiction
        · rename_i c _
          obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
          have ih := divLoop_spec n g x dex dl ld fuel _ q' hq'
          rw [horner_subShift] at ih
          rw [horner_trimL _ _ fun a h => eval_of_isZero g h, horner_addL _ _ (eval_add n g),
            horner_replicate_append _ _ (eval_zero n g), horner_cons, horner_nil]
          linear_combination ih

theorem eval_of_divExact : ∀ (n : ℕ) (g : Fin n → F) {p d q : ZP n},
    divExact? n p d = some q → eval n g p = eval n g q * eval n g d
  | 0, _, a, b, q, h => by
    unfold divExact? at h
    split at h
    · contradiction
    · split at h
      · rename_i ha
        cases h
        have hd : toInt b ∣ toInt a := Int.dvd_of_emod_eq_zero (by simpa using ha)
        show (toInt a : F) = ((toInt a / toInt b : ℤ) : F) * (toInt b : F)
        rw [← Int.cast_mul, Int.ediv_mul_cancel hd]
      · contradiction
  | n + 1, g, p, d, q, h => by
    unfold divExact? at h
    dsimp only at h
    split at h
    · contradiction
    · obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [eval_succ, eval_succ, eval_succ, toList_ofList]
      exact divLoop_spec n _ _ _ _ _ _ _ _ hq'

/-! ### Fractions -/

variable {n : ℕ} (g : Fin n → F)

/-- The value of a fraction. -/
def fval (f : Frac n) : F := eval n g f.1 / eval n g f.2

theorem fixFrac_spec {f : Frac n} (hf : eval n g f.2 ≠ 0) :
    eval n g (fixFrac n f).2 ≠ 0 ∧ fval g (fixFrac n f) = fval g f := by
  unfold fixFrac
  split
  · simp only [fval, eval_neg]
    exact ⟨neg_ne_zero.mpr hf, neg_div_neg_eq _ _⟩
  · exact ⟨hf, rfl⟩

theorem cancel_spec {a b : ZP n} (hb : eval n g b ≠ 0) :
    eval n g (cancel n a b).2 ≠ 0 ∧ fval g (cancel n a b) = eval n g a / eval n g b := by
  unfold cancel
  dsimp only
  split
  · rename_i ha
    simp [fval, eval_zero, eval_one, eval_of_isZero g ha]
  · split
    · exact ⟨hb, rfl⟩
    · split
      · exact fixFrac_spec g hb
      · split
        · rename_i a' b' ha' hb'
          have ea := eval_of_divExact n g ha'
          have eb := eval_of_divExact n g hb'
          have b0 : eval n g b' ≠ 0 := fun z => hb (by rw [eb, z, zero_mul])
          have g0 : eval n g (gcd n a b) ≠ 0 := fun z => hb (by rw [eb, z, mul_zero])
          obtain ⟨h1, h2⟩ := fixFrac_spec g (f := (a', b')) b0
          refine ⟨h1, ?_⟩
          rw [h2, fval, ea, eb, mul_div_mul_right _ _ g0]
        · exact fixFrac_spec g hb

theorem negF_spec {f : Frac n} (hf : eval n g f.2 ≠ 0) :
    eval n g (negF n f).2 ≠ 0 ∧ fval g (negF n f) = -fval g f := by
  refine ⟨hf, ?_⟩
  simp [negF, fval, eval_neg, neg_div]

theorem addF_spec {f f' : Frac n} (hf : eval n g f.2 ≠ 0) (hf' : eval n g f'.2 ≠ 0) :
    eval n g (addF n f f').2 ≠ 0 ∧ fval g (addF n f f') = fval g f + fval g f' := by
  obtain ⟨a, b⟩ := f
  obtain ⟨c, d⟩ := f'
  simp only at hf hf'
  simp only [fval]
  unfold addF
  dsimp only
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · rw [eval_of_isZero g h1, zero_div, zero_add]
    exact ⟨hf', rfl⟩
  · rw [eval_of_isZero g h2, zero_div, add_zero]
    exact ⟨hf, rfl⟩
  · simp only [Bool.and_eq_true] at h3
    rw [eval_add, eval_of_isOne g h3.1, eval_of_isOne g h3.2]
    exact ⟨one_ne_zero, by ring⟩
  · rw [eval_add, eval_mul, eval_of_isOne g h4]
    refine ⟨hf', ?_⟩
    field_simp
  · rw [eval_add, eval_mul, eval_of_isOne g h5]
    refine ⟨hf, ?_⟩
    field_simp
  · obtain rfl := eq_of_beq n h6
    obtain ⟨h1', h2'⟩ := cancel_spec g (a := add n a c) hf
    refine ⟨h1', ?_⟩
    rw [fval] at h2'
    rw [h2', eval_add, add_div]
  · rw [eval_add, eval_mul, eval_mul, eval_mul]
    refine ⟨mul_ne_zero hf hf', ?_⟩
    field_simp
  · split
    · rename_i b' d' hb' hd'
      have eb := eval_of_divExact n g hb'
      have ed := eval_of_divExact n g hd'
      have e0 : eval n g (gcd n b d) ≠ 0 := fun z => hf (by rw [eb, z, mul_zero])
      have b0 : eval n g b' ≠ 0 := fun z => hf (by rw [eb, z, zero_mul])
      have d0 : eval n g d' ≠ 0 := fun z => hf' (by rw [ed, z, zero_mul])
      have sum : eval n g a / eval n g b + eval n g c / eval n g d =
          eval n g (add n (mul n a d') (mul n c b')) / (eval n g b' * eval n g d) := by
        rw [eval_add, eval_mul, eval_mul, eb, ed]
        field_simp
      split_ifs with h8
      · rw [sum, eval_of_isZero g h8, zero_div, eval_zero, eval_one, zero_div]
        exact ⟨one_ne_zero, rfl⟩
      · split
        · rename_i t' d2 ht hd2
          have et := eval_of_divExact n g ht
          have ed2 := eval_of_divExact n g hd2
          have e20 : eval n g (gcd n (add n (mul n a d') (mul n c b')) (gcd n b d)) ≠ 0 :=
            fun z => hf' (by rw [ed2, z, mul_zero])
          have d20 : eval n g d2 ≠ 0 := fun z => hf' (by rw [ed2, z, zero_mul])
          obtain ⟨h1', h2'⟩ := fixFrac_spec g (f := (t', mul n b' d2))
            (by rw [eval_mul]; exact mul_ne_zero b0 d20)
          refine ⟨h1', ?_⟩
          rw [fval] at h2'
          rw [h2', sum, et, ed2]
          simp only [fval, eval_mul]
          field_simp
        · obtain ⟨h1', h2'⟩ := cancel_spec g (a := add n (mul n a d') (mul n c b'))
            (b := mul n b' d) (by rw [eval_mul]; exact mul_ne_zero b0 hf')
          refine ⟨h1', ?_⟩
          rw [fval] at h2'
          rw [h2', sum, eval_mul]
    · obtain ⟨h1', h2'⟩ := cancel_spec g (a := add n (mul n a d) (mul n c b))
        (b := mul n b d) (by rw [eval_mul]; exact mul_ne_zero hf hf')
      refine ⟨h1', ?_⟩
      rw [fval] at h2'
      rw [h2', eval_add, eval_mul, eval_mul, eval_mul]
      field_simp

theorem cancelPair_spec {a d : ZP n} (hd : eval n g d ≠ 0) :
    eval n g (cancelPair n a d).2 ≠ 0 ∧
      eval n g a * eval n g (cancelPair n a d).2 = eval n g (cancelPair n a d).1 * eval n g d := by
  unfold cancelPair
  dsimp only
  split
  · exact ⟨hd, by ring⟩
  · split
    · exact ⟨hd, by ring⟩
    · split
      · rename_i a' d' ha' hd'
        have ea := eval_of_divExact n g ha'
        have ed := eval_of_divExact n g hd'
        refine ⟨fun z => hd (by rw [ed, z, zero_mul]), ?_⟩
        simp only
        rw [ea, ed]
        ring
      · exact ⟨hd, by ring⟩

theorem mulF_spec {f f' : Frac n} (hf : eval n g f.2 ≠ 0) (hf' : eval n g f'.2 ≠ 0) :
    eval n g (mulF n f f').2 ≠ 0 ∧ fval g (mulF n f f') = fval g f * fval g f' := by
  obtain ⟨a, b⟩ := f
  obtain ⟨c, d⟩ := f'
  simp only at hf hf'
  simp only [fval]
  unfold mulF
  dsimp only
  split_ifs with h1 h2
  · simp only [Bool.or_eq_true] at h1
    rw [eval_zero, eval_one, zero_div]
    refine ⟨one_ne_zero, ?_⟩
    rcases h1 with h | h <;> simp [eval_of_isZero g h]
  · simp only [Bool.and_eq_true] at h2
    rw [eval_mul, eval_of_isOne g h2.1, eval_of_isOne g h2.2]
    exact ⟨one_ne_zero, by ring⟩
  · obtain ⟨ad0, ad⟩ := cancelPair_spec g (a := a) hf'
    obtain ⟨cb0, cb⟩ := cancelPair_spec g (a := c) hf
    obtain ⟨h1', h2'⟩ := fixFrac_spec g (f := (mul n (cancelPair n a d).1 (cancelPair n c b).1,
      mul n (cancelPair n c b).2 (cancelPair n a d).2))
      (by rw [eval_mul]; exact mul_ne_zero cb0 ad0)
    refine ⟨h1', ?_⟩
    rw [fval] at h2'
    rw [h2']
    simp only [fval, eval_mul]
    field_simp
    linear_combination -(eval n g c * eval n g (cancelPair n c b).2) * ad -
      (eval n g (cancelPair n a d).1 * eval n g d) * cb

theorem divF_spec {f f' : Frac n} (hf : eval n g f.2 ≠ 0) (hf' : eval n g f'.2 ≠ 0)
    (nz : fval g f' ≠ 0) :
    eval n g (divF n f f').2 ≠ 0 ∧ fval g (divF n f f') = fval g f / fval g f' := by
  unfold divF
  split
  · rename_i h
    exact absurd (by rw [fval, eval_of_isZero g h, zero_div]) nz
  · have n1 : eval n g f'.1 ≠ 0 := fun z => nz (by rw [fval, z, zero_div])
    obtain ⟨i1, i2⟩ := fixFrac_spec g (f := (f'.2, f'.1)) n1
    obtain ⟨m1, m2⟩ := mulF_spec g hf i1
    refine ⟨m1, ?_⟩
    rw [m2, i2]
    simp only [fval]
    field_simp

/-- A defined term is the quotient of the fraction it is turned into. -/
theorem toFrac_spec [CharZero F] :
    ∀ e : Term n, e.Defined g → eval n g (toFrac n e).2 ≠ 0 ∧ fval g (toFrac n e) = e.eval g
  | .const q, _ => by
    refine ⟨?_, ?_⟩
    · rw [toFrac, eval_const, Int.cast_natCast]
      exact Nat.cast_ne_zero.mpr q.den_nz
    · rw [toFrac, fval, eval_const, eval_const, Int.cast_natCast, Term.eval, Rat.cast_def]
  | .gen i, _ => by
    rw [toFrac, fval, eval_var, eval_one, div_one]
    exact ⟨one_ne_zero, rfl⟩
  | .neg a, ha => by
    obtain ⟨h1, h2⟩ := toFrac_spec a ha
    obtain ⟨n1, n2⟩ := negF_spec g h1
    exact ⟨n1, by rw [toFrac, n2, h2]; rfl⟩
  | .add a b, ⟨ha, hb⟩ => by
    obtain ⟨a1, a2⟩ := toFrac_spec a ha
    obtain ⟨b1, b2⟩ := toFrac_spec b hb
    obtain ⟨s1, s2⟩ := addF_spec g a1 b1
    exact ⟨s1, by rw [toFrac, s2, a2, b2]; rfl⟩
  | .sub a b, ⟨ha, hb⟩ => by
    obtain ⟨a1, a2⟩ := toFrac_spec a ha
    obtain ⟨b1, b2⟩ := toFrac_spec b hb
    obtain ⟨n1, n2⟩ := negF_spec g b1
    obtain ⟨s1, s2⟩ := addF_spec g a1 n1
    exact ⟨s1, by rw [toFrac, s2, n2, a2, b2, ← sub_eq_add_neg]; rfl⟩
  | .mul a b, ⟨ha, hb⟩ => by
    obtain ⟨a1, a2⟩ := toFrac_spec a ha
    obtain ⟨b1, b2⟩ := toFrac_spec b hb
    obtain ⟨m1, m2⟩ := mulF_spec g a1 b1
    exact ⟨m1, by rw [toFrac, m2, a2, b2]; rfl⟩
  | .div a b, ⟨ha, hb, nz⟩ => by
    obtain ⟨a1, a2⟩ := toFrac_spec a ha
    obtain ⟨b1, b2⟩ := toFrac_spec b hb
    obtain ⟨d1, d2⟩ := divF_spec g a1 b1 (by rw [b2]; exact nz)
    exact ⟨d1, by rw [toFrac, d2, a2, b2]; rfl⟩

/-! ### Back to terms -/

section Terms

variable {N : ℕ} (g : Fin N → F)

theorem eval_tadd (a b : Term N) : (tadd a b).eval g = a.eval g + b.eval g := by
  unfold tadd
  split
  · rename_i q
    split
    · rename_i h
      rw [beq_iff_eq.mp h]
      simp [Term.eval]
    · rfl
  · rfl

theorem defined_tadd {a b : Term N} (ha : a.Defined g) (hb : b.Defined g) :
    (tadd a b).Defined g := by
  unfold tadd
  split
  · split
    · exact hb
    · exact ⟨ha, hb⟩
  · exact ⟨ha, hb⟩

theorem eval_tmul (θ b : Term N) : (tmul θ b).eval g = θ.eval g * b.eval g := by
  unfold tmul
  split
  · rename_i q
    split
    · rename_i h
      rw [beq_iff_eq.mp h]
      simp [Term.eval]
    · rfl
  · rfl

theorem defined_tmul {θ b : Term N} (hθ : θ.Defined g) (hb : b.Defined g) :
    (tmul θ b).Defined g := by
  unfold tmul
  split
  · split
    · exact hθ
    · exact ⟨hθ, hb⟩
  · exact ⟨hθ, hb⟩

theorem hornerT_spec {α : Type} (θ : Term N) (f : α → Term N) (hθ : θ.Defined g)
    (hf : ∀ c, (f c).Defined g) :
    ∀ l : List α, (hornerT θ f l).Defined g ∧
      (hornerT θ f l).eval g = horner (fun c => (f c).eval g) (θ.eval g) l
  | [] => ⟨trivial, by simp [hornerT, Term.eval]⟩
  | c :: cs => by
    obtain ⟨d, e⟩ := hornerT_spec θ f hθ hf cs
    unfold hornerT
    split
    · rename_i h
      rw [List.isEmpty_iff.mp h]
      exact ⟨hf c, by simp⟩
    · exact ⟨defined_tadd g (hf c) (defined_tmul g hθ d), by
        rw [eval_tadd, eval_tmul, e, horner_cons]⟩

theorem ofZPAt_spec : ∀ (n : ℕ) (h : n ≤ N) (p : ZP n),
    (ofZPAt N n h p).Defined g ∧
      (ofZPAt N n h p).eval g = eval n (fun i => g ⟨i, lt_of_lt_of_le i.isLt h⟩) p
  | 0, _, a => ⟨trivial, by simp [ofZPAt, Term.eval, eval]⟩
  | n + 1, h, p => by
    have ih := ofZPAt_spec n (by omega)
    obtain ⟨d, e⟩ := hornerT_spec g (.gen ⟨n, by omega⟩) (ofZPAt N n (by omega)) trivial
      (fun c => (ih c).1) (toList p)
    refine ⟨d, ?_⟩
    rw [ofZPAt, e, eval_succ]
    congr 1
    funext c
    rw [(ih c).2]
    rfl

end Terms

/-- Lowest terms keep a defined term defined and do not change its value. -/
theorem normFF_spec [CharZero F] (e : Term n) (he : e.Defined g) :
    (normFF e).Defined g ∧ (normFF e).eval g = e.eval g := by
  obtain ⟨h2, hv⟩ := toFrac_spec g e he
  have back : ∀ p, (ofZP n p).Defined g ∧ (ofZP n p).eval g = eval n g p := fun p =>
    ofZPAt_spec g n le_rfl p
  rw [fval] at hv
  unfold normFF
  dsimp only
  split
  · rename_i hc2
    have e2 := eval_of_isConst n g hc2
    rw [e2] at h2 hv
    split
    · rename_i hc1
      rw [eval_of_isConst n g hc1] at hv
      refine ⟨trivial, ?_⟩
      rw [← hv, Term.eval, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
    · split
      · rename_i hd
        rw [beq_iff_eq.mp hd, Int.cast_one, div_one] at hv
        exact ⟨(back _).1, by rw [(back _).2, hv]⟩
      · refine ⟨⟨(back _).1, trivial, ?_⟩, ?_⟩
        · rw [Term.eval, Rat.cast_intCast]
          exact h2
        · rw [Term.eval, Term.eval, (back _).2, Rat.cast_intCast, hv]
  · exact ⟨⟨(back _).1, (back _).1, by rw [(back _).2]; exact h2⟩,
      by rw [Term.eval, (back _).2, (back _).2, hv]⟩

end ZP

end SympyProofs.Calculus.Risch
