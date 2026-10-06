import Mathlib

/-! Subresultant minors for consecutive degree-one complex remainder steps.
The row order is lower, lower, upper, upper, repeated; eliminating the first
two columns swaps the two row families without a determinant sign change. -/
namespace RouthHurwitz.ComplexRouth.FractionFree.Arithmetic
open Matrix Finset
variable {K : Type*} [Field K]

def next (u v : ℕ → K) (j : ℕ) : K :=
  u (j+2) - u 0 / v 0 * v (j+2) - ((u 1-u 0/v 0*v 1)/v 0)*v (j+1)

def lower (r : ℕ) : Prop := r % 4 < 2
instance (r : ℕ) : Decidable (lower r) := inferInstanceAs (Decidable (r % 4 < 2))
def shift (r : ℕ) : ℕ := 2*(r/4)+r%2

def entry {R : Type*} [Zero R] (u v : ℕ → R) (r c : ℕ) : R :=
  if shift r ≤ c then (if lower r then v else u) (c-shift r) else 0

def minor {R : Type*} [Zero R] (u v : ℕ → R) (k j : ℕ) : Matrix (Fin (2*k+1)) (Fin (2*k+1)) R :=
  fun r c => entry u v r.val (if c.val = 2*k then c.val+j else c.val)

theorem det_shear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (S : Finset ι) (src : ι → ι) (a : ι → K)
    (hs : ∀ r ∈ S, src r ∉ S) :
    Matrix.det (fun r c => if r ∈ S then M r c + a r * M (src r) c else M r c) = M.det := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hi' := hs i (mem_insert_self _ _)
    have hsrc : src i ∉ S := fun h => hi' (mem_insert_of_mem h)
    have hne : i ≠ src i := by intro h; apply hi'; rw [← h]; exact mem_insert_self _ _
    have ih' := ih (fun r hr h => hs r (mem_insert_of_mem hr) (mem_insert_of_mem h))
    let B : Matrix ι ι K := fun r c => if r ∈ S then M r c + a r * M (src r) c else M r c
    have he : (fun r c => if r ∈ insert i S then M r c + a r * M (src r) c else M r c) =
        B.updateRow i (B i + a i • B (src i)) := by
      ext r c
      by_cases hri : r = i
      · subst r; simp [B, hi, hsrc, Matrix.updateRow, Function.update]
      · simp [Matrix.updateRow, Function.update, B, hri]
    rw [he, det_updateRow_add_smul_self B hne]
    exact ih'

private theorem shifted_remainder (u v : ℕ → K) (hv : v 0 ≠ 0) (s c : ℕ) :
    (if s ≤ c then u (c-s) else 0) - u 0/v 0*(if s ≤ c then v (c-s) else 0) -
      ((u 1-u 0/v 0*v 1)/v 0)*(if s+1 ≤ c then v (c-(s+1)) else 0) =
    if s+2 ≤ c then next u v (c-(s+2)) else 0 := by
  by_cases h : s+2 ≤ c
  · simp [h, show s ≤ c by omega, show s+1 ≤ c by omega, next,
      show c-(s+2)+2=c-s by omega, show c-(s+2)+1=c-(s+1) by omega]
  · by_cases h0 : s = c
    · subst c; simp [hv]
    · by_cases h1 : s+1 = c
      · subst c; simp [h, hv]
      · simp [show ¬ s ≤ c by omega, show ¬ s+1 ≤ c by omega, h]

def reducedEntry (u v : ℕ → K) (r c : ℕ) : K :=
  if lower r then entry u v r c
  else if shift r+2 ≤ c then next u v (c-(shift r+2)) else 0

private theorem entry_reduce (u v : ℕ → K) (hv : v 0 ≠ 0) (r c : ℕ) (hr : ¬ lower r) :
    entry u v r c - u 0/v 0*entry u v (r-2) c -
      ((u 1-u 0/v 0*v 1)/v 0)*entry u v (if r%4=2 then r-1 else r+1) c =
      reducedEntry u v r c := by
  have hl : lower (r-2) := by dsimp [lower] at *; omega
  have hl' : lower (if r%4=2 then r-1 else r+1) := by dsimp [lower] at *; split <;> omega
  have hs : shift (r-2) = shift r := by dsimp [shift, lower] at *; omega
  have hs' : shift (if r%4=2 then r-1 else r+1) = shift r+1 := by
    dsimp [shift, lower] at *; split <;> omega
  simpa only [entry, hr, hl, hl', ite_false, ite_true, hs, hs', reducedEntry] using
    shifted_remainder u v hv (shift r) c

private theorem reduced_entry_succ (u v : ℕ → K) (r c : ℕ) :
    reducedEntry u v (r+2) (c+2) = entry v (next u v) r c := by
  by_cases hr : lower r
  · have hnr : ¬ lower (r+2) := by dsimp [lower] at *; omega
    have hs : shift (r+2) = shift r := by dsimp [shift, lower] at *; omega
    simp [reducedEntry, entry, hr, hnr, hs]
  · have hl : lower (r+2) := by dsimp [lower] at *; omega
    have hs : shift (r+2) = shift r+2 := by dsimp [shift, lower] at *; omega
    simp [reducedEntry, entry, hr, hl, hs]

private theorem reduced_det (u v : ℕ → K) (hv : v 0 ≠ 0) (k j : ℕ) :
    Matrix.det (fun r c : Fin (2*k+3) => reducedEntry u v r.val
      (if c.val=2*k+2 then c.val+j else c.val)) =
    Matrix.det (fun r c : Fin (2*k+3) => entry u v r.val
      (if c.val=2*k+2 then c.val+j else c.val)) := by
  let M : Matrix (Fin (2*k+3)) (Fin (2*k+3)) K := fun r c =>
    entry u v r.val (if c.val=2*k+2 then c.val+j else c.val)
  let S := Finset.univ.filter (fun r : Fin (2*k+3) => ¬ lower r.val)
  let src : Fin (2*k+3) → Fin (2*k+3) := fun r => ⟨r.val-2, by omega⟩
  let src' : Fin (2*k+3) → Fin (2*k+3) := fun r =>
    if hr : lower r.val then r else
      ⟨if r.val%4=2 then r.val-1 else r.val+1, by dsimp [lower] at hr; split <;> omega⟩
  have hs (r) (hr : r ∈ S) : src r ∉ S := by
    simp only [S, mem_filter, mem_univ, true_and] at *
    dsimp [src, lower] at *; omega
  have hs' (r) (hr : r ∈ S) : src' r ∉ S := by
    simp only [S, mem_filter, mem_univ, true_and] at *
    simp only [src', dite_eq_right hr, Fin.val_mk]
    dsimp [lower] at *
    split_ifs <;> omega
  let B : Matrix (Fin (2*k+3)) (Fin (2*k+3)) K := fun r c =>
    if r ∈ S then M r c + (-u 0/v 0)*M (src r) c else M r c
  have hb : B.det = M.det := det_shear M S src (fun _ => -u 0/v 0) hs
  have hh := det_shear B S src' (fun _ => -((u 1-u 0/v 0*v 1)/v 0)) hs'
  have he : (fun r c => if r ∈ S then B r c + (-((u 1-u 0/v 0*v 1)/v 0))*B (src' r) c else B r c) =
      (fun r c : Fin (2*k+3) => reducedEntry u v r.val (if c.val=2*k+2 then c.val+j else c.val)) := by
    ext r c
    by_cases hr : r ∈ S
    · have hnr : ¬ lower r.val := (Finset.mem_filter.mp hr).2
      simp only [hr, ite_true, B, hs' r hr, ite_false]
      dsimp [M, src, src']
      rw [dite_eq_right hnr]
      simpa only [neg_div, neg_mul, sub_eq_add_neg] using entry_reduce u v hv r.val
        (if c.val=2*k+2 then c.val+j else c.val) hnr
    · have hl : lower r.val := by simpa [S] using hr
      simp [B, hr, M, reducedEntry, hl]
  rw [he] at hh
  exact hh.trans hb

/-- Removing two leading pivots gives the next subresultant minor. -/
theorem det_step (u v : ℕ → K) (hv : v 0 ≠ 0) (k j : ℕ) :
    (minor u v (k+1) j).det = v 0^2 * (minor v (next u v) k j).det := by
  let M : Matrix (Fin (2*k+3)) (Fin (2*k+3)) K := fun r c =>
    reducedEntry u v r.val (if c.val=2*k+2 then c.val+j else c.val)
  have he : (minor u v (k+1) j).det = M.det := by
    convert (reduced_det u v hv k j).symm using 1
    congr 1
  have h00 : M 0 0 = v 0 := by simp [M, reducedEntry, entry, lower, shift]
  have h10 : ∀ r : Fin (2*k+2), M r.succ 0 = 0 := by
    intro r
    simp only [M, Fin.val_succ, Fin.val_zero, show ¬ 0=2*k+2 by omega, ite_false]
    dsimp [reducedEntry, entry, lower, shift]
    split_ifs <;> simp_all only [ite_true, ite_false]
    all_goals
      split_ifs <;> simp_all only [ite_true, ite_false]
      omega
  let M' := M.submatrix Fin.succ Fin.succ
  have h11 : M' 0 0 = v 0 := by simp [M', M, Matrix.submatrix, reducedEntry, entry, lower, shift]
  have h21 : ∀ r : Fin (2*k+1), M' r.succ 0 = 0 := by
    intro r
    dsimp [M', M, Matrix.submatrix, reducedEntry, entry, lower, shift]
    split_ifs <;> simp_all only [ite_true, ite_false]
    all_goals
      split_ifs <;> simp_all only [ite_true, ite_false]
      omega
  have hsub : M'.submatrix Fin.succ Fin.succ = minor v (next u v) k j := by
    ext r c
    dsimp only [M', M, Matrix.submatrix, Matrix.of_apply, minor, Fin.val_succ]
    have hc : (if c.val+1+1=2*k+2 then c.val+1+1+j else c.val+1+1) =
        (if c.val=2*k then c.val+j else c.val)+2 := by split_ifs <;> omega
    rw [hc]
    exact reduced_entry_succ u v r.val (if c.val=2*k then c.val+j else c.val)
  rw [he, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [h00, h10, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
  change v 0 * M'.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h11, h21, hsub, pow_two, mul_assoc]

def pair (u l : ℕ → K) : ℕ → (ℕ → K) × (ℕ → K)
  | 0 => (u, l)
  | k+1 => pair l (next u l) k

def weight (u l : ℕ → K) : ℕ → K
  | 0 => 1
  | k+1 => l 0^2 * weight l (next u l) k

def Regular (u l : ℕ → K) : ℕ → Prop
  | 0 => True
  | k+1 => l 0 ≠ 0 ∧ Regular l (next u l) k

theorem pair_step (u l : ℕ → K) (k : ℕ) :
    pair u l (k+1) = ((pair u l k).2, next (pair u l k).1 (pair u l k).2) := by
  induction k generalizing u l with
  | zero => rfl
  | succ k ih => exact ih l (next u l)

theorem weight_step (u l : ℕ → K) (k : ℕ) :
    weight u l (k+1) = weight u l k * (pair u l k).2 0^2 := by
  induction k generalizing u l with
  | zero => simp [weight, pair]
  | succ k ih =>
    change l 0^2 * weight l (next u l) (k+1) =
      (l 0^2 * weight l (next u l) k) * (pair l (next u l) k).2 0^2
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
    (minor u l k j).det = weight u l k * (pair u l k).2 j := by
  induction k generalizing u l with
  | zero => simp [minor, entry, lower, shift, Matrix.det_unique, weight, pair]
  | succ k ih =>
    rw [det_step u l hr.1, ih l (next u l) hr.2]
    simp [pair, weight, mul_assoc]

theorem weight_ne_zero (u l : ℕ → K) (k : ℕ) (hr : Regular u l k) :
    weight u l k ≠ 0 := by
  induction k generalizing u l with
  | zero => simp [weight]
  | succ k ih => exact mul_ne_zero (pow_ne_zero 2 hr.1) (ih _ _ hr.2)

/-- Every coefficient lies in the image of the coefficient-ring homomorphism. -/
def MappedRow {R : Type*} [CommRing R] (f : R →+* K) (u : ℕ → K) : Prop :=
  ∀ j, ∃ a : R, u j = f a

/-- Determinants commute with the coefficient-ring map. No field operations
or injectivity assumptions are needed in the coefficient ring. -/
theorem mapped_minor {R : Type*} [CommRing R] (f : R →+* K)
    (u l : ℕ → K) (hu : MappedRow f u) (hl : MappedRow f l) (m j : ℕ) :
    ∃ a : R, (minor u l m j).det = f a := by
  choose a ha using hu
  choose b hb using hl
  refine ⟨(minor a b m j).det, ?_⟩
  have hm : minor u l m j = (minor a b m j).map f := by
    ext r c
    change entry u l _ _ = f (entry a b _ _)
    simp only [entry]
    split_ifs <;> simp_all
  rw [hm]
  exact (f.map_det (minor a b m j)).symm

/-- The unsigned regular Bareiss rows lie in the original coefficient ring. -/
theorem mapped_weighted_pair {R : Type*} [CommRing R] (f : R →+* K)
    (u l : ℕ → K) (hu : MappedRow f u) (hl : MappedRow f l)
    (k : ℕ) (hr : Regular u l k) :
    MappedRow f (fun j => weight u l k * (pair u l k).2 j) := by
  intro j
  obtain ⟨a, ha⟩ := mapped_minor f u l hu hl k j
  exact ⟨a, (det_pair u l k j hr).symm.trans ha⟩


end RouthHurwitz.ComplexRouth.FractionFree.Arithmetic
