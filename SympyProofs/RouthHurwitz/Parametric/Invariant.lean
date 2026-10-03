import SympyProofs.RouthHurwitz.Parametric.Basic
import SympyProofs.RouthHurwitz.FractionFree.Determinants

/-! Direct loop invariant for unsigned elimination and its specialization-safe certificate. -/
namespace RouthHurwitz.Parametric
open Exact FractionFree.Arithmetic
variable {A : Type*} [CommRing A] [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A]

namespace Proofs
abbrev Locals (A : Type*) (W : ℕ) :=
  Vector A (W+1) × Vector A (W+1) × List A × A × A × List (Vector A (W+1))

def start {W : ℕ} (first second : Vector A (W+1)) : Locals A W :=
  (first, second, [second[0]], 1, 1, [first, second])

def step {W : ℕ} (s : Locals A W) : Locals A W :=
  if s.2.1[0] ≠ 0 then
    let row := Vector.ofFn (fun j : Fin (W+1) =>
      if h : j.val+1 < W+1 then
        (s.2.1[0] * s.1[j.val+1] - s.1[0] * s.2.1[j.val+1]) / s.2.2.2.1
      else 0)
    (s.2.1, row, s.2.2.1 ++ [row[0]], s.2.2.2.2.1, s.2.1[0], s.2.2.2.2.2 ++ [row])
  else s

def extend {B : Type*} [Zero B] {W : ℕ} (r : Vector B (W+1)) (j : ℕ) : B :=
  if h : j < W+1 then r[j] else 0

@[simp] theorem extend_zero {B : Type*} [Zero B] {W : ℕ} (r : Vector B (W+1)) :
    extend r 0 = r[0] := rfl

/-- Ring-valued minor; it remains meaningful at every real specialization. -/
def minor {W : ℕ} (first second : Vector A (W+1)) (k : ℕ) : A :=
  (hMatrix (extend first) (extend second) (k+1) 0).det

omit [IsDomain A] [MulDivCancelClass A] in
/-- Expose both returned fields as the outcome of the inline loop. -/
theorem run_eq (p : Polynomial A) :
    run p = if p.natDegree = 0 then
      { rows := [initial p p.natDegree 0], positive := [p.leadingCoeff * p.leadingCoeff] }
    else
      let s := (List.range (p.natDegree-1)).foldl (fun s _ => step s)
        (start (initial p p.natDegree 0) (initial p p.natDegree 1))
      { rows := s.2.2.2.2.2, positive := p.leadingCoeff * p.leadingCoeff :: s.2.2.1 } := by
  simp only [run, ← apply_ite, List.forIn_pure_yield_eq_foldl]
  split_ifs <;> rfl

omit [IsDomain A] [MulDivCancelClass A] in
theorem run_positive_eq (p : Polynomial A) :
    (run p).positive = p.leadingCoeff * p.leadingCoeff ::
      (if p.natDegree = 0 then [] else
        ((List.range (p.natDegree-1)).foldl (fun s _ => step s)
          (start (initial p p.natDegree 0) (initial p p.natDegree 1))).2.2.1) := by
  rw [run_eq]
  split_ifs <;> rfl

omit [IsDomain A] [MulDivCancelClass A] in
private theorem loop_rows_pivots {W : ℕ} (first second : Vector A (W+1)) (k : ℕ) :
    let s := (List.range k).foldl (fun s _ => step s) (start first second)
    s.2.2.2.2.2.map (fun row => row[0]) = first[0] :: s.2.2.1 := by
  induction k with
  | zero => simp [start]
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize hs : (List.range k).foldl (fun s _ => step s) (start first second) = s at ih ⊢
    dsimp only at ih ⊢
    by_cases hl : s.2.1[0] ≠ 0
    · simp only [step, if_pos hl, List.map_append, List.map_cons, List.map_nil,
        ih, List.cons_append]
    · simpa only [step, if_neg hl] using ih

variable {K : Type*} [Field K] (f : A →+* K) (hf : Function.Injective f)

def seed {W : ℕ} (r : Vector A (W+1)) : ℕ → K := fun j => f (extend r j)

omit [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A] in
theorem mapped_seed {W : ℕ} (r : Vector A (W+1)) : MappedRow f (seed f r) :=
  fun j => ⟨extend r j, rfl⟩

omit [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A] in
theorem minor_map {W : ℕ} (first second : Vector A (W+1)) (k j : ℕ) :
    (hMatrix (seed f first) (seed f second) k j).det =
      f ((hMatrix (extend first) (extend second) k j).det) := by
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hMatrix, hEntry]
  split_ifs <;> simp only [seed, map_zero]

/-- The row scales are signed products of ordinary pivots, with no absolute values. -/
structure RegularState {W : ℕ} (first second : Vector A (W+1))
    (k : ℕ) (s : Locals A W) : Prop where
  regular : Regular (seed f first) (seed f second) k
  divisor_ne : s.2.2.2.1 ≠ 0
  upper : ∀ j, f (extend s.1 j) = f s.2.2.2.1 * (pair (seed f first) (seed f second) k).1 j
  lower : ∀ j, f (extend s.2.1 j) = weight (seed f first) (seed f second) k *
    (pair (seed f first) (seed f second) k).2 j
  delayed : f s.2.2.2.2.1 = weight (seed f first) (seed f second) k
  pivots : s.2.2.1 = (List.range (k+1)).map (minor first second)

include hf

omit [DecidableEq A] [Div A] [MulDivCancelClass A] hf in
theorem initial_regular {W : ℕ} (first second : Vector A (W+1)) :
    RegularState f first second 0 (start first second) := by
  refine ⟨trivial, one_ne_zero, ?_, ?_, ?_, ?_⟩
  · intro j; simp [start, seed, pair]
  · intro j; simp [start, seed, pair, weight]
  · simp [start, weight]
  · simp [start, minor, hMatrix, hEntry, Matrix.det_unique]

omit [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A] in
theorem RegularState.pivot_eq {W : ℕ} {first second : Vector A (W+1)}
    {k : ℕ} {s : Locals A W} (h : RegularState f first second k s) :
    s.2.1[0] = minor first second k := by
  apply hf
  have hm := det_pair (seed f first) (seed f second) k 0 h.regular
  rw [minor_map f] at hm
  exact (h.lower 0).trans hm.symm

omit [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A] in
/-- Every performed division is exact in the source ring. -/
theorem RegularState.divides {W : ℕ} {first second : Vector A (W+1)}
    {k : ℕ} {s : Locals A W} (h : RegularState f first second k s)
    (hl : s.2.1[0] ≠ 0) (j : ℕ) :
    s.2.2.2.1 ∣ s.2.1[0] * extend s.1 (j+1) - s.1[0] * extend s.2.1 (j+1) := by
  have hp : (pair (seed f first) (seed f second) k).2 0 ≠ 0 := by
    intro hz
    have he := h.lower 0
    rw [hz, mul_zero] at he
    exact hl (hf (he.trans (map_zero f).symm))
  exact bareiss_divisor_dvd f hf _ _ (mapped_seed f first) (mapped_seed f second) k
    ((regular_step _ _ k).mpr ⟨h.regular, hp⟩) (extend s.1) (extend s.2.1)
    s.2.2.2.1 h.upper h.lower j

omit [IsDomain A] in
theorem RegularState.advance {W : ℕ} {first second : Vector A (W+1)}
    {k : ℕ} {s : Locals A W} (h : RegularState f first second k s)
    (hl : s.2.1[0] ≠ 0) : RegularState f first second (k+1) (step s) := by
  let u := seed f first
  let v := seed f second
  let r := pair u v k
  have hp : r.2 0 ≠ 0 := by
    intro hz
    have he := h.lower 0
    change f s.2.1[0] = weight u v k * r.2 0 at he
    rw [hz, mul_zero] at he
    exact hl (hf (he.trans (map_zero f).symm))
  have hreg : Regular u v (k+1) := (regular_step u v k).mpr ⟨h.regular, hp⟩
  have hd : f s.2.2.2.1 ≠ 0 := fun hz => h.divisor_ne (hf (hz.trans (map_zero f).symm))
  have he : s.2.2.2.2.1 ≠ 0 := by
    intro hz
    have hh := h.delayed
    rw [hz, map_zero] at hh
    exact weight_ne_zero u v k h.regular hh.symm
  let row := Vector.ofFn (fun j : Fin (W+1) =>
    if hj : j.val+1 < W+1 then
      (s.2.1[0] * s.1[j.val+1] - s.1[0] * s.2.1[j.val+1]) / s.2.2.2.1
    else 0)
  have hrow (j : ℕ) : f (extend row j) = weight u v (k+1) * (pair u v (k+1)).2 j := by
    have hn : f (s.2.1[0] * extend s.1 (j+1) - s.1[0] * extend s.2.1 (j+1)) /
        f s.2.2.2.1 = weight u v (k+1) * (pair u v (k+1)).2 j := by
      rw [map_sub, map_mul, map_mul, ← extend_zero s.2.1, ← extend_zero s.1,
        h.lower, h.upper, h.upper, h.lower, weight_step, pair_step]
      dsimp only
      unfold next
      dsimp [u, v, r] at hp ⊢
      field_simp [hp, hd]
    rw [← hn]
    by_cases hj : j+1 < W+1
    · rw [show extend row j =
          (s.2.1[0] * extend s.1 (j+1) - s.1[0] * extend s.2.1 (j+1)) / s.2.2.2.1 by
        simp only [extend, row, Vector.getElem_ofFn, dif_pos hj, dif_pos (show j < W+1 by omega)]]
      exact map_quotient f hf _ _ h.divisor_ne (h.divides f hf hl j)
    · have hz : extend row j = 0 := by
        simp only [extend, row, Vector.getElem_ofFn]
        split_ifs <;> simp_all
      rw [hz]
      simp only [extend, dif_neg hj, mul_zero, sub_self, map_zero, zero_div]
  have hpivot : row[0] = minor first second (k+1) := by
    apply hf
    have hh := det_pair u v (k+1) 0 hreg
    rw [minor_map f] at hh
    exact (hrow 0).trans hh.symm
  rw [step, if_pos hl]
  change RegularState f first second (k+1)
    (s.2.1, row, s.2.2.1 ++ [row[0]], s.2.2.2.2.1, s.2.1[0], s.2.2.2.2.2 ++ [row])
  refine ⟨hreg, he, ?_, hrow, ?_, ?_⟩
  · intro j
    rw [h.lower, h.delayed, pair_step]
  · rw [← extend_zero s.2.1, h.lower, weight_step]
  · change s.2.2.1 ++ [row[0]] = _
    rw [h.pivots, hpivot, List.range_succ (n := k+1), List.map_append]
    rfl

/-- If elimination stopped, its certificate contains zero and a genuine
Hurwitz minor is zero. Otherwise the full regular invariant is retained. -/
def Inv {W : ℕ} (first second : Vector A (W+1)) (k : ℕ) (s : Locals A W) : Prop :=
  RegularState f first second k s ∨
    (s.2.1[0] = 0 ∧ 0 ∈ s.2.2.1 ∧ ∃ j, j ≤ k ∧ minor first second j = 0)

theorem loop_inv {W : ℕ} (first second : Vector A (W+1)) (k : ℕ) :
    Inv f first second k ((List.range k).foldl (fun s _ => step s) (start first second)) := by
  induction k with
  | zero => exact Or.inl (initial_regular f first second)
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rcases ih with h | ⟨hz, hmem, j, hj, he⟩
    · by_cases hl : ((List.range k).foldl (fun s _ => step s) (start first second)).2.1[0] = 0
      · right
        rw [step, if_neg (not_not.mpr hl)]
        refine ⟨hl, ?_, k, by omega, ?_⟩
        · rw [h.pivots]
          apply List.mem_map.mpr
          exact ⟨k, List.mem_range.mpr (by omega), (h.pivot_eq f hf).symm.trans hl⟩
        · exact (h.pivot_eq f hf).symm.trans hl
      · exact Or.inl (h.advance f hf hl)
    · right
      rw [step, if_neg (not_not.mpr hz)]
      exact ⟨hz, hmem, j, by omega, he⟩

/-- The certificate remains correct under every real specialization, including
noninjective ones at which a symbolic pivot vanishes. -/
theorem loop_positive_iff {W : ℕ} (first second : Vector A (W+1)) (steps : ℕ)
    (g : A →+* ℝ) :
    (∀ a ∈ ((List.range steps).foldl (fun s _ => step s) (start first second)).2.2.1, 0 < g a) ↔
      ∀ j, j ≤ steps → 0 < g (minor first second j) := by
  have hi := loop_inv f hf first second steps
  rcases hi with h | ⟨_, hz, j, hj, hm⟩
  · rw [h.pivots]
    constructor
    · intro hh j hj
      exact hh _ (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)
    · intro hh a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact hh j (by have := List.mem_range.mp hj; omega)
  · constructor
    · intro hh
      have := hh 0 hz
      simp at this
    · intro hh
      have := hh j hj
      simp [hm] at this

end Proofs
omit [IsDomain A] [MulDivCancelClass A] in
/-- The stability inequalities are precisely the first column of the returned table. -/
theorem run_positive_eq_firstColumn (p : Polynomial A) :
    (run p).positive = (run p).rows.map (fun row => row[0]'(Imperative.Bounds.width_pos _)) := by
  have hfirst : (initial p p.natDegree 0)[0]'(Imperative.Bounds.width_pos _) =
      p.leadingCoeff * p.leadingCoeff := by
    simp only [initial, Vector.getElem_ofFn, Nat.mul_zero, Nat.add_zero, Nat.zero_le,
      if_true, Nat.sub_zero, Polynomial.coeff_natDegree]
  rw [Proofs.run_eq]
  split_ifs with hn
  · simp only [List.map_cons, List.map_nil, hfirst]
  · have h := Proofs.loop_rows_pivots (initial p p.natDegree 0)
      (initial p p.natDegree 1) (p.natDegree-1)
    rw [← hfirst]
    exact h.symm

/-- Every division reached by `Parametric.run` has a nonzero exact divisor.
The bounded index selects an iteration of the actual inline loop; no order or
regularity assumption is imposed on the input polynomial. -/
theorem run_exact_division (p : Polynomial A) (k : Fin (p.natDegree-1)) :
    let s := (List.range k.val).foldl (fun s _ => Proofs.step s)
      (Proofs.start (initial p p.natDegree 0) (initial p p.natDegree 1))
    s.2.1[0] ≠ 0 → s.2.2.2.1 ≠ 0 ∧ ∀ j : ℕ,
      s.2.2.2.1 ∣ s.2.1[0] * Proofs.extend s.1 (j+1) - s.1[0] * Proofs.extend s.2.1 (j+1) := by
  intro s hl
  have hi := Proofs.loop_inv (algebraMap A (FractionRing A))
    (IsFractionRing.injective A (FractionRing A))
    (initial p p.natDegree 0) (initial p p.natDegree 1) k.val
  rcases hi with h | ⟨hz, _⟩
  · exact ⟨h.divisor_ne, h.divides _ (IsFractionRing.injective A (FractionRing A)) hl⟩
  · exact (hl hz).elim

end RouthHurwitz.Parametric
