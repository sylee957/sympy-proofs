import SympyProofs.RouthHurwitz.Parametric.Basic
import SympyProofs.RouthHurwitz.FractionFree.Determinants
import Std.Tactic.Do
import Std.WP
import SympyProofs.RouthHurwitz.FractionFree.Stability

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

variable {K : Type*} [Field K] (f : A →+* K) (hf : Function.Injective f)

def seed {W : ℕ} (r : Vector A (W+1)) : ℕ → K := fun j => f (extend r j)

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
  exact bareiss_divisor_dvd f hf _ _ (fun j => ⟨extend first j, rfl⟩) (fun j => ⟨extend second j, rfl⟩) k
    ((regular_step _ _ k).mpr ⟨h.regular, hp⟩) (extend s.1) (extend s.2.1)
    s.2.2.2.1 h.upper h.lower j

/-- If elimination stopped, its certificate contains zero and a genuine
Hurwitz minor is zero. Otherwise the full regular invariant is retained. -/
def Inv {W : ℕ} (first second : Vector A (W+1)) (k : ℕ) (s : Locals A W) : Prop :=
  RegularState f first second k s ∨
    (s.2.1[0] = 0 ∧ 0 ∈ s.2.2.1 ∧ ∃ j, j ≤ k ∧ minor first second j = 0)

omit [IsDomain A] in
theorem Inv.advance {W : ℕ} {first second : Vector A (W+1)} {k : ℕ}
    {s : Locals A W} (hi : Inv f first second k s) :
    Inv f first second (k+1) (step s) := by
  rcases hi with h | ⟨hz, hmem, j, hj, he⟩
  · by_cases hl : s.2.1[0] = 0
    · right
      rw [step, ite_eq_right (not_not.mpr hl)]
      have he : minor first second k = 0 := by
        apply hf
        have hm := det_pair (seed f first) (seed f second) k 0 h.regular
        rw [minor_map f] at hm
        exact hm.trans ((h.lower 0).symm.trans (by simp [hl]))
      refine ⟨hl, ?_, k, by omega, he⟩
      rw [h.pivots]
      exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), he⟩
    · left
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
            simp only [extend, row, Vector.getElem_ofFn, dite_eq_left hj, dite_eq_left (show j < W+1 by omega)]]
          exact map_quotient f hf _ _ h.divisor_ne (h.divides f hf hl j)
        · have hz : extend row j = 0 := by
            simp only [extend, row, Vector.getElem_ofFn]
            split_ifs <;> simp_all
          rw [hz]
          simp only [extend, dite_eq_right hj, mul_zero, sub_self, map_zero, zero_div]
      have hpivot : row[0] = minor first second (k+1) := by
        apply hf
        have hh := det_pair u v (k+1) 0 hreg
        rw [minor_map f] at hh
        exact (hrow 0).trans hh.symm
      rw [step, ite_eq_left hl]
      change RegularState f first second (k+1)
        (s.2.1, row, s.2.2.1 ++ [row[0]], s.2.2.2.2.1, s.2.1[0], s.2.2.2.2.2 ++ [row])
      refine ⟨hreg, he, ?_, hrow, ?_, ?_⟩
      · intro j
        rw [h.lower, h.delayed, pair_step]
      · rw [← extend_zero s.2.1, h.lower, weight_step]
      · change s.2.2.1 ++ [row[0]] = _
        rw [h.pivots, hpivot, List.range_succ (n := k+1), List.map_append]
        rfl
  · right
    rw [step, ite_eq_right (not_not.mpr hz)]
    exact ⟨hz, hmem, j, by omega, he⟩


end Proofs
open scoped Std.WP in
/-- Direct verification of the imperative certificate against the Hurwitz minors. -/
theorem run_certificate_iff (p : Polynomial A) (g : A →+* ℝ) :
    (run p).Holds g ↔ 0 < g (p.leadingCoeff * p.leadingCoeff) ∧
      ∀ j, j < p.natDegree →
        0 < g (Proofs.minor (initial p p.natDegree 0) (initial p p.natDegree 1) j) := by
  generalize h : run p = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ s => Proofs.Inv (algebraMap A (FractionRing A))
      (initial p p.natDegree 0) (initial p p.natDegree 1) pref.length s
  case vc1 => simp_all +zetaDelta [Result.Holds]
  case vc2 => exact Or.inl (Proofs.initial_regular _ _ _)
  case vc3 =>
    simp only [Result.Holds, List.mem_cons, forall_eq_or_imp]
    apply and_congr_right
    intro _
    rcases ‹Proofs.Inv _ _ _ _ _› with hs | ⟨_, hz, j, hj, hm⟩
    · have hpivots := hs.pivots
      dsimp only at hpivots
      rw [hpivots]
      simp only [List.length_range]
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
        have := hh j (by simp only [List.length_range] at hj; omega)
        simp [hm] at this
  case vc4 | vc5 =>
    have hi := (‹Proofs.Inv _ _ _ _ _›).advance _
      (IsFractionRing.injective A (FractionRing A))
    simp_all +zetaDelta [Proofs.step]

open scoped Std.WP in
omit [IsDomain A] [MulDivCancelClass A] in
/-- The stability inequalities are precisely the first column of the returned table. -/
theorem run_positive_eq_firstColumn (p : Polynomial A) :
    (run p).positive = (run p).rows.map (fun row => row[0]'(Imperative.Bounds.width_pos _)) := by
  have hfirst : (initial p p.natDegree 0)[0]'(Imperative.Bounds.width_pos _) =
      p.leadingCoeff * p.leadingCoeff := by
    simp only [initial, Vector.getElem_ofFn, Nat.mul_zero, Nat.add_zero, Nat.zero_le,
      ite_true, Nat.sub_zero, Polynomial.coeff_natDegree]
  generalize h : run p = result
  apply Std.WP.Id.of_run_eq_wp h
  vcgen invariants
  · fun _ _ ⟨_, _, pivots, _, _, rows⟩ =>
      rows.map (fun row => row[0]) = p.leadingCoeff * p.leadingCoeff :: pivots
  all_goals simp_all +zetaDelta only [List.map_append, List.map_cons, List.map_nil,
    List.cons_append]

/-- Every division reached by `Parametric.run` has a nonzero exact divisor.
The bounded index selects an iteration of the actual inline loop; no order or
regularity assumption is imposed on the input polynomial. -/
theorem run_exact_division (p : Polynomial A) (k : Fin (p.natDegree-1)) :
    let s := (List.range k.val).foldl (fun s _ => Proofs.step s)
      (Proofs.start (initial p p.natDegree 0) (initial p p.natDegree 1))
    s.2.1[0] ≠ 0 → s.2.2.2.1 ≠ 0 ∧ ∀ j : ℕ,
      s.2.2.2.1 ∣ s.2.1[0] * Proofs.extend s.1 (j+1) - s.1[0] * Proofs.extend s.2.1 (j+1) := by
  intro s hl
  have hi (steps : ℕ) : Proofs.Inv (algebraMap A (FractionRing A))
      (initial p p.natDegree 0) (initial p p.natDegree 1) steps
      ((List.range steps).foldl (fun s _ => Proofs.step s)
        (Proofs.start (initial p p.natDegree 0) (initial p p.natDegree 1))) := by
    induction steps with
    | zero => exact Or.inl (Proofs.initial_regular _ _ _)
    | succ steps ih =>
      simpa only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        using ih.advance _ (IsFractionRing.injective A (FractionRing A))
  rcases hi k.val with h | ⟨hz, _⟩
  · exact ⟨h.divisor_ne, h.divides _ (IsFractionRing.injective A (FractionRing A)) hl⟩
  · exact (hl hz).elim

end RouthHurwitz.Parametric

/-! Pointwise correctness of the generated polynomial inequalities. -/
namespace RouthHurwitz.Parametric
open Polynomial Exact FractionFree FractionFree.Arithmetic
variable {A : Type*} [CommRing A] [IsDomain A] [DecidableEq A] [Div A] [MulDivCancelClass A]

/-- The generated inequalities hold exactly when the leading coefficient survives
specialization and the resulting real polynomial is Hurwitz stable. -/
theorem run_correct (p : Polynomial A) (f : A →+* ℝ) :
    (run p).Holds f ↔ f p.leadingCoeff ≠ 0 ∧ HurwitzStable (p.map f) := by
  by_cases hl : f p.leadingCoeff = 0
  · simp [run_certificate_iff, map_mul, hl]
  rw [and_iff_right hl]
  have hd : (p.map f).natDegree = p.natDegree := natDegree_map_of_leadingCoeff_ne_zero f hl
  let q := C p.leadingCoeff * p
  have hqd : (q.map f).natDegree = p.natDegree := by
    simpa only [q, Polynomial.map_mul, Polynomial.map_C, natDegree_C_mul hl] using hd
  have hql : 0 < (q.map f).coeff p.natDegree := by
    simp only [q, Polynomial.map_mul, Polynomial.map_C, coeff_C_mul, coeff_map, coeff_natDegree]
    exact mul_self_pos.mpr hl
  have hscale : HurwitzStable (C (f p.leadingCoeff) * p.map f) ↔
      HurwitzStable (p.map f) := by
    simp only [HurwitzStable, Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C,
      mul_eq_zero, Complex.ofRealHom_eq_coe, Complex.ofReal_eq_zero, hl, false_or]
  rw [← hscale]
  rw [show C (f p.leadingCoeff) * p.map f = q.map f by simp [q]]
  rw [hurwitzStable_iff_minors _ p.natDegree hqd hql]
  rw [run_certificate_iff]
  have hsquare : 0 < f (p.leadingCoeff * p.leadingCoeff) := by
    simpa only [map_mul] using mul_self_pos.mpr hl
  rw [and_iff_right hsquare]
  have hminor (k : ℕ) :
      Proofs.minor (initial p p.natDegree 0) (initial p p.natDegree 1) k =
        hurwitzMinor q p.natDegree (k+1) := by
    have hext (parity j : ℕ) : Proofs.extend (initial p p.natDegree parity) j =
        if 2*j+parity ≤ p.natDegree then
          p.coeff p.natDegree * p.coeff (p.natDegree-(2*j+parity)) else 0 := by
      change (if h : j < p.natDegree/2+1 then (initial p p.natDegree parity)[j] else 0) = _
      by_cases hj : j < p.natDegree/2+1
      · simp only [dite_eq_left hj, initial, Vector.getElem_ofFn]
      · have hh : ¬ 2*j+parity ≤ p.natDegree := by omega
        simp only [dite_eq_right hj, ite_eq_right hh]
    unfold Proofs.minor hurwitzMinor
    congr 2 <;> funext j <;> simp only [hext, q, coeff_C_mul, coeff_natDegree, Nat.add_zero]
  simp_rw [hminor, hurwitzMinor_map]
  constructor
  · intro h k hk hkn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact h j (by omega)
  · intro h k hk
    exact h (k+1) (by omega) (by omega)

end RouthHurwitz.Parametric
