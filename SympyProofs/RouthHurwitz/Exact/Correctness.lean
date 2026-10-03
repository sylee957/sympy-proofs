import SympyProofs.RouthHurwitz.FractionFree.Correctness
import SympyProofs.RouthHurwitz.FractionFree.Integrality

/-! Transport the actual coefficient-domain loop to the verified real loop. -/
namespace RouthHurwitz.Exact
open Polynomial Imperative Imperative.Bounds
variable {A : Type*} [CommRing A] [LinearOrder A] [Div A] [MulDivCancelClass A] [IsStrictOrderedRing A]

namespace Proofs
variable (D : RealDomain A)

omit [Div A] [MulDivCancelClass A] [IsStrictOrderedRing A] in
@[simp] theorem embed_eq_zero (a : A) : D.embed a = 0 ↔ a = 0 := by
  rw [← map_zero D.embed, D.injective.eq_iff]

omit [Div A] [MulDivCancelClass A] [IsStrictOrderedRing A] in
theorem lt_zero_iff_embed (a : A) : a < 0 ↔ D.embed a < 0 := by
  simpa only [map_zero] using (D.strictMono.lt_iff_lt (a := a) (b := 0)).symm

omit [Div A] [MulDivCancelClass A] in
private theorem embed_abs (a : A) : D.embed |a| = |D.embed a| := by
  by_cases h : a < 0
  · rw [abs_of_neg h, map_neg, abs_of_neg ((lt_zero_iff_embed D a).mp h)]
  · rw [abs_of_nonneg (le_of_not_gt h),
      abs_of_nonneg (le_of_not_gt (fun hh => h ((lt_zero_iff_embed D a).mpr hh)))]

omit [Div A] [MulDivCancelClass A] [IsStrictOrderedRing A] in
private theorem repair_map {W : ℕ} (d : ℕ) (w : Fin (W+2))
    (u r : Vector A (W+1)) :
    repair d w (u.map D.embed) (r.map D.embed) =
      ((repair d w u r).1.map D.embed, (repair d w u r).2) := by
  have hscan : scan w (r.map D.embed) = scan w r := by simp [scan]
  simp only [repair, hscan, Vector.getElem_map, embed_eq_zero]
  split_ifs
  all_goals simp only [Id.run_pure, Prod.mk.injEq, and_true]
  · apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn, Vector.getElem_map]
    split_ifs <;> simp
  · apply Vector.ext
    intro j hj
    simp [Vector.getElem_ofFn]

omit [Div A] [MulDivCancelClass A] [IsStrictOrderedRing A] in
private theorem initial_map (p : Polynomial ℝ) (coeff : ℕ → A)
    (hc : ∀ j, D.embed (coeff j) = p.coeff j) (parity : ℕ) :
    (initialCoefficients p.natDegree coeff parity).map D.embed = Imperative.initial p parity := by
  apply Vector.ext
  intro j hj
  simp only [Imperative.initial, initialCoefficients, Vector.getElem_map, Vector.getElem_ofFn]
  split_ifs <;> simp [hc]

def mapLocals {n : ℕ} (s : Locals A n) : FractionFree.Proofs.Locals (K := ℝ) n :=
  (s.1.map D.embed, s.2.1.map D.embed, s.2.2.1.map (Vector.map D.embed),
    s.2.2.2.1, s.2.2.2.2.1, D.embed s.2.2.2.2.2.1, D.embed s.2.2.2.2.2.2)

omit [Div A] [MulDivCancelClass A] [IsStrictOrderedRing A] in
private theorem start_map (p : Polynomial ℝ) (coeff : ℕ → A)
    (hc : ∀ j, D.embed (coeff j) = p.coeff j) :
    mapLocals D (start p.natDegree coeff) = FractionFree.Proofs.initialLocals p := by
  have hu := initial_map D p coeff hc 0
  have hl := initial_map D p coeff hc 1
  have hr := repair_map D p.natDegree ⟨width p.natDegree, Nat.lt_succ_self _⟩
    (initialCoefficients p.natDegree coeff 0) (initialCoefficients p.natDegree coeff 1)
  dsimp only [width] at hu hl hr ⊢
  simp only [hu, hl] at hr
  simp only [start, mapLocals, FractionFree.Proofs.initialLocals_eq, Id.run_pure]
  dsimp only [width] at ⊢
  simp only [← hu, ← hl, repair_map, Vector.getElem_map, List.map_cons, List.map_nil,
    map_one, lt_zero_iff_embed D, map_mul]
  erw [Vector.getElem_map]
  rfl

private theorem step_map (n k : ℕ) (s : Locals A n)
    (hex : FractionFree.ExactDivision D.embed n k (mapLocals D s)) :
    mapLocals D (step n k s) = FractionFree.Proofs.step n k (mapLocals D s) := by
  obtain ⟨upper, lower, rows, count, deg, divisor, nextDivisor⟩ := s
  let w : Fin (width n+1) := ⟨activeWidth n (k+2), Nat.lt_succ_of_le (activeWidth_le n _)⟩
  let raw := Vector.ofFn (fun j : Fin (width n) =>
    if hj : j.val < w then
      ((if (lower[0]'(width_pos _)) < 0 then (-1 : A) else 1) *
        (lower[0]'(width_pos _) * upper[j.val+1]'(next_index_lt n k j.val hj) -
          upper[0]'(width_pos _) * lower[j.val+1]'(next_index_lt n k j.val hj))) / divisor
    else 0)
  let rawR := Vector.ofFn (fun j : Fin (width n) =>
    if hj : j.val < w then
      (if (lower.map D.embed)[0]'(width_pos _) < 0 then (-1 : ℝ) else 1) *
        ((lower.map D.embed)[0]'(width_pos _) * (upper.map D.embed)[j.val+1]'(next_index_lt n k j.val hj) -
          (upper.map D.embed)[0]'(width_pos _) * (lower.map D.embed)[j.val+1]'(next_index_lt n k j.val hj)) /
          D.embed divisor
    else 0)
  have hd : divisor ≠ 0 := by
    intro hz
    have hh := hex.1
    simp [mapLocals, hz] at hh
  have hraw : raw.map D.embed = rawR := by
    apply Vector.ext
    intro j hj
    simp only [raw, rawR, Vector.getElem_map, Vector.getElem_ofFn]
    by_cases ha : j < w
    · simp only [dif_pos ha]
      let numerator := (if (lower[0]'(width_pos _)) < 0 then (-1 : A) else 1) *
        (lower[0]'(width_pos _) * upper[j+1]'(next_index_lt n k j ha) -
          upper[0]'(width_pos _) * lower[j+1]'(next_index_lt n k j ha))
      have hn : FractionFree.cellNumerator n k (mapLocals D
          (upper, lower, rows, count, deg, divisor, nextDivisor)) ⟨j, ha⟩ = D.embed numerator := by
        by_cases hsign : D.embed (lower[0]'(width_pos n)) < 0 <;>
          simp [FractionFree.cellNumerator, mapLocals, numerator, lt_zero_iff_embed D, hsign]
      obtain ⟨q, hq⟩ := hex.2.2 ⟨j, ha⟩
      rw [hn] at hq
      have hdiv : divisor ∣ numerator := ⟨q, D.injective (by simpa [mapLocals] using hq)⟩
      have hm := map_quotient D.embed D.injective numerator divisor hd hdiv
      simpa [numerator, lt_zero_iff_embed D, apply_ite] using hm
    · simp only [dif_neg ha, map_zero]
  have hr := repair_map D (n+1-(k+2)) w lower raw
  dsimp only [width] at hr hraw ⊢
  rw [hraw] at hr
  simp only [step, mapLocals, FractionFree.Proofs.step]
  change ( (lower.map D.embed), (repair (n+1-(k+2)) w lower raw).1.map D.embed,
    (List.append rows [(repair (n+1-(k+2)) w lower raw).1]).map (Vector.map D.embed),
    count + (if (lower[0]'(width_pos n) * (repair (n+1-(k+2)) w lower raw).1[0]) < 0 then 1 else 0),
    deg || !(repair (n+1-(k+2)) w lower raw).2,
    D.embed (if raw[0]'(width_pos n) = 0 then 1 else nextDivisor),
    D.embed (if raw[0]'(width_pos n) = 0 then 1 else |lower[0]'(width_pos n)|)) =
    (lower.map D.embed, (repair (n+1-(k+2)) w (lower.map D.embed) rawR).1,
      List.append (rows.map (Vector.map D.embed)) [(repair (n+1-(k+2)) w (lower.map D.embed) rawR).1],
      count + (if (lower.map D.embed)[0]'(width_pos n) * (repair (n+1-(k+2)) w (lower.map D.embed) rawR).1[0] < 0 then 1 else 0),
      deg || !(repair (n+1-(k+2)) w (lower.map D.embed) rawR).2,
      (if rawR[0]'(width_pos n) = 0 then (1 : ℝ) else D.embed nextDivisor),
      (if rawR[0]'(width_pos n) = 0 then (1 : ℝ) else |(lower.map D.embed)[0]'(width_pos n)|))
  dsimp only [width] at w upper lower rows raw rawR hr hraw ⊢
  simp only [hr]
  simp only [← hraw, Vector.getElem_map, lt_zero_iff_embed D, map_mul]
  repeat' erw [Vector.getElem_map]
  by_cases hz : raw[0]'(Nat.zero_lt_succ (n/2)) = 0
  all_goals simp only [embed_eq_zero, hz, if_true, if_false,
    Prod.mk.injEq, true_and]
  all_goals repeat' first | erw [if_pos hz] | erw [if_neg hz]
  all_goals simp only [map_one, embed_abs]
  all_goals repeat' first | erw [List.map_append] | erw [List.map_cons] | erw [List.map_nil]
  all_goals simp only [true_and, and_true]
  all_goals repeat' constructor

private theorem loop_map (p : Polynomial ℝ) (coeff : ℕ → A)
    (hc : ∀ j, D.embed (coeff j) = p.coeff j) (k : ℕ) (hk : k+1 ≤ p.natDegree) :
    mapLocals D ((List.range k).foldl (fun s j => step p.natDegree j s)
      (start p.natDegree coeff)) =
      (List.range k).foldl (fun s j => FractionFree.Proofs.step p.natDegree j s)
        (FractionFree.Proofs.initialLocals p) := by
  induction k with
  | zero => exact start_map D p coeff hc
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have hi := ih (by omega)
    rw [step_map D _ _ _ (by
      rw [hi]
      exact FractionFree.run_exact_division D.embed p (fun j => ⟨coeff j, (hc j).symm⟩) k (by omega)), hi]

private theorem outcome_map (p : Polynomial A) :
    ((run p).signChanges, (run p).degenerate) =
      ((run (p.map D.embed)).signChanges, (run (p.map D.embed)).degenerate) := by
  have hd : (p.map D.embed).natDegree = p.natDegree := natDegree_map_eq_of_injective D.injective p
  have hc : ∀ j, D.embed (p.coeff j) = (p.map D.embed).coeff j :=
    fun j => (coeff_map _ _).symm
  by_cases hn : (p.map D.embed).natDegree = 0
  · simp only [run, ← hd, if_pos hn, Id.run_pure, coeff_map, embed_eq_zero]
  · have hi := loop_map D (p.map D.embed) p.coeff hc ((p.map D.embed).natDegree-1) (by omega)
    have hh := congrArg (fun s : FractionFree.Proofs.Locals (K := ℝ) (p.map D.embed).natDegree =>
      (s.2.2.2.1, s.2.2.2.2.1)) hi
    have he := congrArg (fun n =>
      let s := (List.range (n-1)).foldl (fun s j => step n j s) (start n p.coeff)
      (s.2.2.2.1, s.2.2.2.2.1)) hd.symm
    have hn' : p.natDegree ≠ 0 := by simpa only [hd] using hn
    simp only [run_eq, if_neg hn, if_neg hn']
    exact he.trans hh

end Proofs

/-- The domain-valued loop counts complex right-half-plane roots of the real
interpretation, including multiplicities and both exceptional repairs. -/
theorem run_signChanges_correct (D : RealDomain A) (p : Polynomial A) (hp : p ≠ 0) :
    (run p).signChanges =
      Polynomial.rightCount ((p.map D.embed).map Complex.ofRealHom) := by
  have h := congrArg Prod.fst (Proofs.outcome_map D p)
  exact h.trans (FractionFree.real_run_signChanges_correct _
    ((Polynomial.map_ne_zero_iff D.injective).mpr hp))

/-- Exact coefficient arithmetic decides strict stability through its specified
real embedding. No field division is performed by `run`. -/
theorem accepts_run_iff_hurwitzStable (D : RealDomain A) (p : Polynomial A) :
    accepts (run p) = true ↔ HurwitzStable (p.map D.embed) := by
  have h := Proofs.outcome_map D p
  have he : accepts (run p) = accepts (run (p.map D.embed)) := by
    unfold accepts
    rw [show (run p).signChanges = (run (p.map D.embed)).signChanges from congrArg Prod.fst h,
      show (run p).degenerate = (run (p.map D.embed)).degenerate from congrArg Prod.snd h]
  rw [he]
  exact FractionFree.accepts_real_run_iff_hurwitzStable _

end RouthHurwitz.Exact
