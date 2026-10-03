import Mathlib

/-! Hurwitz minors and exact delayed-pivot cancellation over coefficient rings.
The unsigned divisibility theorem uses an injective ring map into a field and
requires no order. Absolute-value normalization is handled separately. -/
open Matrix Finset
namespace RouthHurwitz.FractionFree.Arithmetic
variable {K : Type*} [Field K]

def hEntry {K : Type*} [Zero K] (u l : ℕ → K) (r c : ℕ) : K :=
  if r / 2 ≤ c then (if r % 2 = 0 then l else u) (c - r / 2) else 0

def hMatrix {K : Type*} [Zero K] (u l : ℕ → K) (m j : ℕ) : Matrix (Fin m) (Fin m) K :=
  fun r c => hEntry u l r.val (if c.val + 1 = m then c.val + j else c.val)

def elim (q : K) (m : ℕ) : Matrix (Fin m) (Fin m) K :=
  fun r c => if r = c then 1 else if r.val % 2 = 1 ∧ c.val + 1 = r.val then -q else 0

theorem elim_det (q : K) (m : ℕ) : (elim q m).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [elim]
  · intro i j hij
    have h : i.val < j.val := hij
    simp [elim, show i ≠ j by intro he; subst j; omega, show ¬ j.val + 1 = i.val by omega]

theorem elim_mul (q : K) (m : ℕ) (M : Matrix (Fin m) (Fin m) K) (r c : Fin m) :
    (elim q m * M) r c = M r c -
      if h : r.val % 2 = 1 then q * M ⟨r.val - 1, by omega⟩ c else 0 := by
  classical
  by_cases hr : r.val % 2 = 1
  · have hx : r.val - 1 < m := by omega
    have hne : (⟨r.val - 1, hx⟩ : Fin m) ≠ r := by intro h; have he := congrArg Fin.val h; dsimp only at he; omega
    rw [Matrix.mul_apply]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
    simp only [elim]
    rw [Finset.sum_eq_single ⟨r.val - 1, hx⟩]
    · simp [hne.symm, hr, show r.val - 1 + 1 = r.val by omega, sub_eq_add_neg]
    · intro b hb hbn
      have hbr : b ≠ r := by simpa using hb
      have hval : b.val + 1 ≠ r.val := by
        intro h
        apply hbn
        apply Fin.ext
        dsimp only
        omega
      simp [hbr.symm, hval]
    · intro h
      exact (h (by simp [hne])).elim
  · simp [Matrix.mul_apply, elim, hr]

def next (u l : ℕ → K) (j : ℕ) : K := u (j+1) - u 0 / l 0 * l (j+1)

theorem entry_succ (u l : ℕ → K) (hl : l 0 ≠ 0) (r c : ℕ) :
    hEntry u l (r+1) (c+1) -
      (if (r+1) % 2 = 1 then u 0 / l 0 * hEntry u l r (c+1) else 0) =
    hEntry l (next u l) r c := by
  by_cases hr : r % 2 = 0
  · have hm : (r+1) % 2 = 1 := by omega
    have hd : (r+1) / 2 = r / 2 := by omega
    simp only [hEntry, hr, hm, hd, if_pos, Nat.one_ne_zero, if_false]
    by_cases hc : r / 2 ≤ c
    · have hcs : r / 2 ≤ c+1 := by omega
      simp only [if_pos hc, if_pos hcs, next, show c+1-r/2 = c-r/2+1 by omega]
    · by_cases hcs : r / 2 ≤ c+1
      · have he : r/2 = c+1 := by omega
        simp [he, hl]
      · simp [hc, hcs]
  · have hm : (r+1) % 2 = 0 := by omega
    have hd : (r+1) / 2 = r / 2 + 1 := by omega
    simp only [hEntry, hr, hm, hd, if_pos, Nat.zero_ne_one, if_false, sub_zero,
      Nat.add_le_add_iff_right, Nat.add_sub_add_right]

theorem entry_zero (u l : ℕ → K) (hl : l 0 ≠ 0) (r : ℕ) :
    hEntry u l (r+1) 0 -
      (if (r+1) % 2 = 1 then u 0 / l 0 * hEntry u l r 0 else 0) = 0 := by
  by_cases hr : r = 0
  · subst r
    simp [hEntry, hl]
  · have h : ¬ (r+1)/2 ≤ 0 := by omega
    by_cases hpar : (r+1)%2 = 1
    · have h' : ¬ r/2 ≤ 0 := by omega
      simp [hEntry, h, h', hpar]
    · simp [hEntry, h, hpar]

theorem det_step (u l : ℕ → K) (hl : l 0 ≠ 0) (m j : ℕ) :
    (hMatrix u l (m+2) j).det = l 0 * (hMatrix l (next u l) (m+1) j).det := by
  let M := elim (u 0 / l 0) (m+2) * hMatrix u l (m+2) j
  have h00 : M 0 0 = l 0 := by
    simp [M, elim_mul, hMatrix, hEntry]
  have hz (r : Fin (m+1)) : M r.succ 0 = 0 := by
    dsimp only [M]
    rw [elim_mul]
    by_cases hr : (r.val + 1) % 2 = 1
    all_goals
      simpa [hMatrix, hr, show ¬ (1 : ℕ) = m+2 by omega] using entry_zero u l hl r.val
  have hsub : M.submatrix Fin.succ Fin.succ = hMatrix l (next u l) (m+1) j := by
    ext r c
    dsimp only [Matrix.submatrix, Matrix.of_apply, M]
    rw [elim_mul]
    have hcol : (if c.val+1+1 = m+2 then c.val+1+j else c.val+1) =
        (if c.val+1 = m+1 then c.val+j else c.val)+1 := by split_ifs <;> omega
    simpa only [hMatrix, dite_eq_ite, Fin.val_succ, Nat.add_sub_cancel, hcol] using
      entry_succ u l hl r.val (if c.val+1 = m+1 then c.val+j else c.val)
  have he : (hMatrix u l (m+2) j).det = M.det := by
    simp [M, Matrix.det_mul, elim_det]
  rw [he, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h00, hz, hsub]

def pair (u l : ℕ → K) : ℕ → (ℕ → K) × (ℕ → K)
  | 0 => (u, l)
  | k+1 => pair l (next u l) k

def weight (u l : ℕ → K) : ℕ → K
  | 0 => 1
  | k+1 => l 0 * weight l (next u l) k

def Regular (u l : ℕ → K) : ℕ → Prop
  | 0 => True
  | k+1 => l 0 ≠ 0 ∧ Regular l (next u l) k

theorem pair_step (u l : ℕ → K) (k : ℕ) :
    pair u l (k+1) = ((pair u l k).2, next (pair u l k).1 (pair u l k).2) := by
  induction k generalizing u l with
  | zero => rfl
  | succ k ih => exact ih l (next u l)

theorem weight_step (u l : ℕ → K) (k : ℕ) :
    weight u l (k+1) = weight u l k * (pair u l k).2 0 := by
  induction k generalizing u l with
  | zero => simp [weight, pair]
  | succ k ih =>
    change l 0 * weight l (next u l) (k+1) =
      (l 0 * weight l (next u l) k) * (pair l (next u l) k).2 0
    rw [ih]
    ring

theorem regular_step (u l : ℕ → K) (k : ℕ) :
    Regular u l (k+1) ↔ Regular u l k ∧ (pair u l k).2 0 ≠ 0 := by
  induction k generalizing u l with
  | zero => simp [Regular, pair]
  | succ k ih =>
    change (l 0 ≠ 0 ∧ Regular l (next u l) (k+1)) ↔
      (l 0 ≠ 0 ∧ Regular l (next u l) k) ∧ (pair l (next u l) k).2 0 ≠ 0
    rw [ih]
    tauto

theorem det_pair (u l : ℕ → K) (k j : ℕ) (hr : Regular u l k) :
    (hMatrix u l (k+1) j).det = weight u l k * (pair u l k).2 j := by
  induction k generalizing u l with
  | zero => simp [hMatrix, hEntry, Matrix.det_unique, weight, pair]
  | succ k ih =>
    rw [det_step u l hr.1, ih l (next u l) hr.2]
    simp [pair, weight, mul_assoc]

theorem weight_ne_zero (u l : ℕ → K) (k : ℕ) (hr : Regular u l k) :
    weight u l k ≠ 0 := by
  induction k generalizing u l with
  | zero => simp [weight]
  | succ k ih => exact mul_ne_zero hr.1 (ih _ _ hr.2)

/-- Every coefficient lies in the image of the coefficient-ring homomorphism. -/
def MappedRow {R : Type*} [CommRing R] (f : R →+* K) (u : ℕ → K) : Prop :=
  ∀ j, ∃ a : R, u j = f a

/-- Determinants commute with the coefficient-ring map. No field operations
or injectivity assumptions are needed in the coefficient ring. -/
theorem mapped_minor {R : Type*} [CommRing R] (f : R →+* K)
    (u l : ℕ → K) (hu : MappedRow f u) (hl : MappedRow f l) (m j : ℕ) :
    ∃ a : R, (hMatrix u l m j).det = f a := by
  choose a ha using hu
  choose b hb using hl
  refine ⟨(hMatrix a b m j).det, ?_⟩
  have hm : hMatrix u l m j = (hMatrix a b m j).map f := by
    ext r c
    change hEntry u l _ _ = f (hEntry a b _ _)
    simp only [hEntry]
    split_ifs <;> simp_all
  rw [hm]
  exact (f.map_det (hMatrix a b m j)).symm

/-- The unsigned regular Bareiss rows lie in the original coefficient ring. -/
theorem mapped_weighted_pair {R : Type*} [CommRing R] (f : R →+* K)
    (u l : ℕ → K) (hu : MappedRow f u) (hl : MappedRow f l)
    (k : ℕ) (hr : Regular u l k) :
    MappedRow f (fun j => weight u l k * (pair u l k).2 j) := by
  intro j
  obtain ⟨a, ha⟩ := mapped_minor f u l hu hl (k+1) j
  exact ⟨a, (det_pair u l k j hr).symm.trans ha⟩

/-- Exact delayed-pivot divisibility in the coefficient ring itself.
The current rows are related to the regular remainder pair by the two delayed
scales. This algebraic theorem needs no order on either ring or field. -/
theorem bareiss_divisor_dvd {R : Type*} [CommRing R] (f : R →+* K)
    (hf : Function.Injective f) (u l : ℕ → K)
    (hu : MappedRow f u) (hl : MappedRow f l) (k : ℕ) (hr : Regular u l (k+1))
    (upper lower : ℕ → R) (divisor : R)
    (hupper : ∀ j, f (upper j) = f divisor * (pair u l k).1 j)
    (hlower : ∀ j, f (lower j) = weight u l k * (pair u l k).2 j) (j : ℕ) :
    divisor ∣ lower 0 * upper (j+1) - upper 0 * lower (j+1) := by
  obtain ⟨q, hq⟩ := mapped_weighted_pair f u l hu hl (k+1) hr j
  refine ⟨q, hf ?_⟩
  dsimp only at hq
  rw [map_sub, map_mul, map_mul, map_mul, hupper, hupper, hlower, hlower, ← hq,
    weight_step, pair_step]
  dsimp only
  unfold next
  have hp := (regular_step u l k).mp hr |>.2
  field_simp

/-- Sign normalization only multiplies by a unit ±1 and preserves the image
of any coefficient ring, without requiring that homomorphism to preserve order. -/
theorem mapped_abs_weighted_pair [LinearOrder K] [IsStrictOrderedRing K]
    {R : Type*} [CommRing R] (f : R →+* K)
    (u l : ℕ → K) (hu : MappedRow f u) (hl : MappedRow f l)
    (k : ℕ) (hr : Regular u l k) :
    MappedRow f (fun j => |weight u l k| * (pair u l k).2 j) := by
  intro j
  obtain ⟨a, ha⟩ := mapped_weighted_pair f u l hu hl k hr j
  dsimp only at ha ⊢
  by_cases hw : weight u l k < 0
  · exact ⟨-a, by rw [abs_of_neg hw, neg_mul, ha, map_neg]⟩
  · exact ⟨a, by rwa [abs_of_nonneg (le_of_not_gt hw)]⟩

end RouthHurwitz.FractionFree.Arithmetic
