module

public import SympyProofs.Calculus.Antiderivative.Algebra.MPoly.Semantics
import Mathlib.Data.List.Sort

/-! Uniqueness of the sorted list of terms. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.MPoly.Raw

variable {R : Type*} [AddCommMonoid R]

/-- Descending order of monomials in the canonical term list. -/
private abbrev Before (a b : Mono × R) := b.1.key < a.1.key

/-- A nonzero term with trimmed exponents within the available variables. -/
private def Good (n : ℕ) (x : Mono × R) : Prop :=
  x.1.trim = x.1 ∧ x.1.trim.length ≤ n ∧ x.2 ≠ 0

private theorem key_injective : Function.Injective Mono.key := by
  intro a b h
  exact congrArg (fun k : Lex (ℕ × Mono) => (ofLex k).2) h

private theorem lexLess_iff (d e : Mono) : Mono.lexLess d e = true ↔ d < e := by
  induction d generalizing e with
  | nil => cases e <;> simp [Mono.lexLess]
  | cons a as ih =>
    cases e with
    | nil => simp [Mono.lexLess]
    | cons b bs =>
      by_cases he : a = b <;> simp [Mono.lexLess, he, List.cons_lt_cons_iff, ih]

private theorem before_iff (e d : Mono) : e.before d = true ↔ d.key < e.key := by
  simp only [Mono.before,Mono.key,Prod.Lex.toLex_lt_toLex, beq_iff_eq]
  split_ifs with eq
  · simp [eq,lexLess_iff]
  · simp [eq]

private theorem insert_keys [DecidableEq R] (e : Mono) (c : R) (p : Raw R)
    (x : Mono × R) (hx : x ∈ insert e c p) : x.1 = e ∨ ∃ y ∈ p, y.1 = x.1 := by
  induction p with
  | nil =>
    by_cases hc : c = 0 <;> simp [insert, hc] at hx; simp [hx]
  | cons a p ih =>
    rcases a with ⟨d,b⟩
    unfold insert at hx
    split_ifs at hx with hc hd hsum ho
    all_goals simp only [List.mem_cons] at hx ⊢
    all_goals grind

private theorem insert_sorted [DecidableEq R] (e : Mono) (c : R) {p : Raw R}
    (hp : p.Pairwise Before) : (insert e c p).Pairwise Before := by
  induction p with
  | nil => by_cases hc : c = 0 <;> simp [insert, hc]
  | cons a p ih =>
    rcases a with ⟨d,b⟩
    obtain ⟨hfront, htail⟩ := List.pairwise_cons.mp hp
    have hnew := ih htail
    unfold insert
    split_ifs with hc hd hsum ho
    · exact hp
    · exact htail
    · subst d
      exact List.pairwise_cons.mpr ⟨hfront, htail⟩
    · have hde : d.key < e.key := (before_iff e d).mp ho
      refine List.pairwise_cons.mpr ⟨?_, hp⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hde
      · exact lt_trans (hfront x hx) hde
    · have hed : e.key < d.key :=
        lt_of_le_of_ne (le_of_not_gt (fun h => ho ((before_iff e d).mpr h)))
          (fun h => hd (key_injective h))
      refine List.pairwise_cons.mpr ⟨?_, hnew⟩
      intro x hx
      rcases insert_keys e c p x hx with h | ⟨y,hy,h⟩
      · simpa [Before, h] using hed
      · simpa [Before, h] using hfront y hy

private theorem insert_good [DecidableEq R] (n : ℕ) (e : Mono) (c : R)
    (he : e.trim = e) (hen : e.trim.length ≤ n) {p : Raw R}
    (hp : ∀ x ∈ p, Good n x) : ∀ x ∈ insert e c p, Good n x := by
  induction p with
  | nil =>
    by_cases hc : c = 0 <;> simp [insert, hc, Good, he, he ▸ hen]
  | cons a p ih =>
    rcases a with ⟨d,b⟩
    have htail : ∀ x ∈ p, Good n x := fun x hx => hp x (List.mem_cons_of_mem _ hx)
    have hhead := hp (d,b) List.mem_cons_self
    unfold insert
    split_ifs with hc hd hsum ho
    · exact hp
    · exact htail
    · exact List.forall_mem_cons.mpr ⟨⟨he, hen, hsum⟩, htail⟩
    · exact List.forall_mem_cons.mpr ⟨⟨he, hen, hc⟩, hp⟩
    · exact List.forall_mem_cons.mpr ⟨hhead, ih htail⟩

private theorem normalize_sorted [DecidableEq R] (n : ℕ) (p : Raw R) :
    (normalize n p).Pairwise Before := by
  induction p with
  | nil => simp [normalize]
  | cons a p ih =>
    rcases a with ⟨e,c⟩
    simp only [normalize]
    split <;> first | exact insert_sorted _ _ ih | exact ih

private theorem normalize_good [DecidableEq R] (n : ℕ) (p : Raw R) :
    ∀ x ∈ normalize n p, Good n x := by
  induction p with
  | nil => simp [normalize]
  | cons a p ih =>
    rcases a with ⟨e,c⟩
    simp only [normalize]
    split
    · rename_i h
      apply insert_good _ _ _ (Poly.Raw.trim_trim _)
      · simpa [Mono.trim] using h
      · exact ih
    · exact ih

private theorem value_absent (n : ℕ) (s : Fin n →₀ ℕ) {p : Raw R}
    (h : ∀ x ∈ p, x.1.exponents n ≠ s) : value n p s = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rcases a with ⟨d,b⟩
    have hhead := h (d,b) List.mem_cons_self
    have htail := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    by_cases hd : d.trim.length ≤ n <;>
      simp [value, term, hd, hhead, htail]

private theorem exponent_inj {n : ℕ} {x y : Mono × R} (hx : Good n x) (hy : Good n y)
    (h : x.1.exponents n = y.1.exponents n) : x.1 = y.1 := by
  simpa [hx.1, hy.1] using Mono.trim_eq_of_exponents_eq hx.2.1 hy.2.1 h

private theorem value_at_mem {n : ℕ} {p : Raw R} (hp : p.Pairwise Before)
    (hg : ∀ x ∈ p, Good n x) (x : Mono × R) (hx : x ∈ p) :
    value n p (x.1.exponents n) = x.2 := by
  induction p with
  | nil => simp at hx
  | cons a p ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hp
    have ga := hg a List.mem_cons_self
    have gt : ∀ x ∈ p, Good n x := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    rcases List.mem_cons.mp hx with rfl | hmem
    · have hz := value_absent n (x.1.exponents n) (p := p) fun y hy h => by
        have hlt : y.1.key < x.1.key := ha y hy
        exact lt_irrefl _ (exponent_inj (gt y hy) ga h ▸ hlt)
      rcases x with ⟨e,c⟩
      simp [value, term, ga.2.1, hz]
    · have hne : a.1.exponents n ≠ x.1.exponents n := fun h => by
        have hlt : x.1.key < a.1.key := ha x hmem
        exact lt_irrefl _ (exponent_inj ga (gt x hmem) h ▸ hlt)
      rcases a with ⟨d,b⟩
      simp [value, term, ga.2.1, hne, ih ht gt hmem]

private theorem mem_of_eq_value {n : ℕ} {p q : Raw R} (hp : p.Pairwise Before)
    (gp : ∀ x ∈ p, Good n x) (hq : q.Pairwise Before) (gq : ∀ x ∈ q, Good n x)
    (h : value n p = value n q) (x : Mono × R) (hx : x ∈ p) : x ∈ q := by
  have hval := value_at_mem hp gp x hx
  rw [h] at hval
  have hg := gp x hx
  have hex : ∃ y ∈ q, y.1.exponents n = x.1.exponents n := by
    by_contra! hnone
    exact hg.2.2 (hval.symm.trans (value_absent n _ hnone))
  obtain ⟨y,hy,he⟩ := hex
  have hyval := value_at_mem hq gq y hy
  rw [he, hval] at hyval
  exact Prod.ext (exponent_inj (gq y hy) hg he) hyval.symm ▸ hy

/-- A term in a normal form fits the height and records its original nonzero coefficient. -/
theorem coefficient_of_mem_normalize [DecidableEq R] (n : ℕ) (p : Raw R) (e : Mono) (c : R)
    (h : (e,c) ∈ normalize n p) :
    e.trim.length ≤ n ∧ c ≠ 0 ∧ value n p (e.exponents n) = c := by
  have hg := normalize_good n p (e,c) h
  refine ⟨hg.2.1, hg.2.2, ?_⟩
  simpa using value_at_mem (normalize_sorted n p) (normalize_good n p) (e,c) h

/-- Normal forms agree exactly when every coefficient agrees. -/
theorem normalize_eq_iff_value [DecidableEq R] (n : ℕ) (p q : Raw R) :
    normalize n p = normalize n q ↔ value n p = value n q := by
  constructor
  · intro h
    simpa using congrArg (value n) h
  · intro h
    have hv : value n (normalize n p) = value n (normalize n q) := by simpa
    let _ : Std.Antisymm (Before (R := R)) :=
      ⟨fun _ _ h₁ h₂ => False.elim (lt_asymm h₁ h₂)⟩
    let _ : Std.Irrefl (Before (R := R)) := ⟨fun _ => lt_irrefl _⟩
    exact (normalize_sorted n p).eq_of_mem_iff (normalize_sorted n q) fun x =>
      ⟨mem_of_eq_value (normalize_sorted n p) (normalize_good n p) (normalize_sorted n q)
        (normalize_good n q) hv x, mem_of_eq_value (normalize_sorted n q) (normalize_good n q)
        (normalize_sorted n p) (normalize_good n p) hv.symm x⟩

end SympyProofs.Calculus.Antiderivative.MPoly.Raw
