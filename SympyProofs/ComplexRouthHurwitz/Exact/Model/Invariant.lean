import SympyProofs.ComplexRouthHurwitz.Exact.Model.Initialization

/-! One-step Gaussian arithmetic lemmas for the compressed loop invariant.
These declarations are proof-only descriptions of row denotations. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian.Model.ProofsG
open Polynomial FractionFree FractionFree.Arithmetic
noncomputable section
open Classical
local notation "f" => GaussianInt.toComplex

abbrev Locals (N : ℕ) := Rows.Row N × Rows.Row N × List (Rows.Row N) × List ℤ × ℕ × Option Auxiliary × ℤ

def encode {N} (s : Locals N) : ProofsFF.Locals N :=
  (mapRow s.1, mapRow s.2.1, s.2.2.1.map mapRow, s.2.2.2.1.map (fun z : ℤ => (z:ℝ)),
    s.2.2.2.2.1, s.2.2.2.2.2.1, (s.2.2.2.2.2.2:ℝ))

def Valid (q : ℂ[X]) (m : ℕ) {N} (s : Locals N) : Prop :=
  ProofsFF.Valid q m (encode s) ∧ (m ≠ 0 → Segment f
    (descending (Coefficients.entry (mapRow s.1)) m)
    (descending (Coefficients.entry (mapRow s.2.1)) (m-1)) (s.2.2.2.2.2.2:ℂ))

def initial {N} (a : Rows.Row N) (n : ℕ) : Locals N :=
  let r := initialRows a n
  (r.upper,r.lower,[],[],0,none,initialDivisor a n)

def step (n k : ℕ) (s : Locals (n+1)) : Locals (n+1) :=
  let (u,v,rows,pivots,count,aux,D) := s
  let d := n-(k+1)
  let aux := if v = Rows.zero (n+1) ∧ aux.isNone then
    some { degree := d+1, rightBefore := count } else aux
  let D := if (Rows.entry v d).re = 0 then 1 else D
  let r := Rows.repair d u v
  let B := (Rows.entry r.lower d).re
  let count := count + if (Rows.entry r.upper (d+1)).re < 0 ↔ B < 0 then 0 else 1
  if d = 0 then
    (Rows.one (n+1),Rows.zero (n+1),rows ++ [r.upper,r.lower],pivots ++ [B],count,aux,B^2)
  else
    (r.lower,Model.nextLower d D r.upper r.lower,
      rows ++ [r.upper,r.lower],pivots ++ [B],count,aux,B^2)

private theorem cast_lt_zero (b : ℤ) : (b:ℝ) < 0 ↔ b < 0 := by exact_mod_cast (Iff.rfl : b<0 ↔ b<0)

/-- Once exact division is known, one integer step denotes one field step. -/
theorem encode_step (n k : ℕ) (s : Locals (n+1))
    (hn : let d := n-(k+1)
      let D := if (Rows.entry s.2.1 d).re=0 then 1 else s.2.2.2.2.2.2
      let r := Rows.repair d s.1 s.2.1
      d ≠ 0 → mapRow (Model.nextLower d D r.upper r.lower) =
        FractionFree.nextLower d (D:ℝ) (mapRow r.upper) (mapRow r.lower)) :
    encode (step n k s) = ProofsFF.step n k (encode s) := by
  obtain ⟨u,v,rows,pivots,count,aux,D⟩ := s
  dsimp only at hn
  by_cases hd : n-(k+1)=0
  all_goals
    simp only [step, ProofsFF.step, encode, ← map_repair, mapPair, map_entry,
      ← GaussianInt.intCast_re, mapRow_eq_zero, Int.cast_eq_zero, cast_lt_zero,
      hd, ite_true, ite_false, map_zero, map_one,
      List.map_append, List.map_cons, List.map_nil, Int.cast_pow]
  rw [hn hd]
  split_ifs <;> simp

theorem initial_valid (q : ℂ[X]) (n : ℕ) (a : Rows.Row (n+1))
    (hn : 0<n) (hd : q.natDegree=n) (hq : 0 < q.leadingCoeff.re)
    (ha : mapRow a = Coefficients.pack (n+1) q) : Valid q n (initial a n) := by
  constructor
  · have he : encode (initial a n) = ProofsFF.initial q n := by
      have h := map_initialRows a n
      rw [ha] at h
      have hu := congrArg Coefficients.Pair.upper h
      have hv := congrArg Coefficients.Pair.lower h
      simp only [mapPair] at hu hv
      simp only [initial, encode, ProofsFF.initial, List.map_nil, map_initialDivisor, ha, hu, hv]
    rw [he]
    exact ProofsFF.initial_valid q n hn hd hq
  · intro _
    have hz : (Rows.entry a n).re ≠ 0 := by
      have hh : ((Rows.entry a n).re:ℝ) = q.leadingCoeff.re := by
        rw [GaussianInt.intCast_re, ← map_entry, ha, Coefficients.entry_pack q (by omega), ← hd, coeff_natDegree]
      exact_mod_cast (hh.symm ▸ ne_of_gt hq : ((Rows.entry a n).re:ℝ) ≠ 0)
    exact initial_segment a hn (by omega) hz

/-- A repair starts a new ring-valued segment exactly when the divisor resets. -/
theorem repaired_segment {N d} (u v : Rows.Row N) (D : ℤ)
    (hs : Segment f (descending (Coefficients.entry (mapRow u)) (d+1))
      (descending (Coefficients.entry (mapRow v)) d) (D:ℂ)) :
    let r := Rows.repair d u v
    Segment f (descending (Coefficients.entry (mapRow r.upper)) (d+1))
      (descending (Coefficients.entry (mapRow r.lower)) d)
      ((if (Rows.entry v d).re=0 then 1 else D : ℤ):ℂ) := by
  by_cases hp : (Rows.entry v d).re=0
  · simp only [hp, ite_true, Int.cast_one]
    exact Segment.start (mapped_descending _ _) (mapped_descending _ _)
  · have hv : v ≠ Rows.zero N := by
      intro hz; subst v
      simp [Rows.entry, Rows.zero] at hp
    simpa only [Rows.repair, hp, hv, ite_false] using hs

/-- A reached step has a positive divisor and an integral next row;
its arithmetic segment is also ready to advance. -/
theorem step_ready (q : ℂ[X]) (n k : ℕ) (hk : k<n) (s : Locals (n+1))
    (h : Valid q (n-k) s) :
    let r := Rows.repair (n-(k+1)) s.1 s.2.1
    let E : ℤ := if (Rows.entry s.2.1 (n-(k+1))).re=0 then 1 else s.2.2.2.2.2.2
    (0:ℝ) < E ∧ (n-(k+1) ≠ 0 →

      MappedRow f (Coefficients.entry (FractionFree.nextLower (n-(k+1)) (E:ℝ) (mapRow r.upper) (mapRow r.lower))) ∧
      Segment f
        (descending (Coefficients.entry (mapRow r.lower)) (n-(k+1)))
        (descending (Coefficients.entry (FractionFree.nextLower (n-(k+1)) (E:ℝ) (mapRow r.upper) (mapRow r.lower))) (n-(k+1)-1))
        (((Rows.entry r.lower (n-(k+1))).re:ℂ)^2)) := by
  obtain ⟨u,v,rows,pivots,count,aux,D⟩ := s
  obtain ⟨hf,hs⟩ := h
  obtain ⟨hD,U,V,hu,hv,hi⟩ := hf
  dsimp only [encode] at hD hu hv hi
  have hm : 0<n-k := by omega
  have he : n-k = n-(k+1)+1 := by omega
  have hp : ComplexRouth.Pair (n-(k+1)) U V := by simpa only [he, Nat.add_sub_cancel] using hi.active hm
  have hN : n-(k+1)+1 < n+1 := by omega
  let r := Rows.repair (n-(k+1)) u v
  let E : ℤ := if (Rows.entry v (n-(k+1))).re=0 then 1 else D
  have hE : (0:ℝ) < E := by dsimp [E]; split_ifs <;> simp_all only [Int.cast_one, zero_lt_one]
  have hE0 : E ≠ 0 := by exact_mod_cast (ne_of_gt hE)
  have hmr := map_repair (n-(k+1)) u v
  rw [hu,hv,Coefficients.repair_pack _ U V hp hN] at hmr
  have hru : mapRow r.upper = Coefficients.pack (n+1) (ComplexRouth.repair (n-(k+1)) U V).upper :=
    congrArg Coefficients.Pair.upper hmr
  have hrv : mapRow r.lower = Coefficients.pack (n+1) (ComplexRouth.repair (n-(k+1)) U V).lower :=
    congrArg Coefficients.Pair.lower hmr
  have hr := hp.repair_correct
  have hrN : (ComplexRouth.repair (n-(k+1)) U V).lower.natDegree < n+1 :=
    hr.1.lower_bound.trans_lt (by omega)
  have hB : ((Rows.entry r.lower (n-(k+1))).re:ℝ) =
      ((ComplexRouth.repair (n-(k+1)) U V).lower.coeff (n-(k+1))).re := by
    rw [GaussianInt.intCast_re, ← map_entry, hrv, Coefficients.entry_pack _ hrN]
  have hrs := repaired_segment u v D (by simpa only [he, Nat.add_sub_cancel] using hs (by omega))
  change Segment f (descending (Coefficients.entry (mapRow r.upper)) (n-(k+1)+1))
    (descending (Coefficients.entry (mapRow r.lower)) (n-(k+1))) (E:ℂ) at hrs
  have hadv (hd : n-(k+1) ≠ 0) :
      MappedRow f (Coefficients.entry (FractionFree.nextLower (n-(k+1)) (E:ℝ) (mapRow r.upper) (mapRow r.lower))) ∧
      Segment f
        (descending (Coefficients.entry (mapRow r.lower)) (n-(k+1)))
        (descending (Coefficients.entry (FractionFree.nextLower (n-(k+1)) (E:ℝ) (mapRow r.upper) (mapRow r.lower))) (n-(k+1)-1))
        (((Rows.entry r.lower (n-(k+1))).re:ℂ)^2) := by
    rw [hru,hrv] at hrs ⊢
    have hbcast : ((Rows.entry r.lower (n-(k+1))).re:ℂ) =
        (((ComplexRouth.repair (n-(k+1)) U V).lower.coeff (n-(k+1))).re:ℂ) := by exact_mod_cast hB
    rw [hbcast]
    exact advance_vectors f _ _ hr.1 (by omega) hN hr.2.1 (E:ℝ) hE hrs
  exact ⟨hE,hadv⟩

/-- The simultaneous semantic and arithmetic invariant advances through every branch. -/
theorem step_valid (q : ℂ[X]) (n k : ℕ) (hk : k<n) (s : Locals (n+1))
    (h : Valid q (n-k) s) : Valid q (n-(k+1)) (step n k s) := by
  obtain ⟨u,v,rows,pivots,count,aux,D⟩ := s
  let r := Rows.repair (n-(k+1)) u v
  let E : ℤ := if (Rows.entry v (n-(k+1))).re=0 then 1 else D
  have hr := step_ready q n k hk (u,v,rows,pivots,count,aux,D) h
  have hE0 : E ≠ 0 := by exact_mod_cast (ne_of_gt hr.1)
  have hnext (hd : n-(k+1) ≠ 0) :
      mapRow (Model.nextLower (n-(k+1)) E r.upper r.lower) =
        FractionFree.nextLower (n-(k+1)) (E:ℝ) (mapRow r.upper) (mapRow r.lower) :=
    map_nextLower _ _ _ _ hE0 (hr.2 hd).1
  constructor
  · have hh := ProofsFF.step_valid q n k hk _ h.1
    rw [← encode_step n k (u,v,rows,pivots,count,aux,D) hnext] at hh
    exact hh
  · intro hd
    have hx := hnext hd
    dsimp only [r,E] at hx
    simp only [step, hd, ite_false, hx, Int.cast_pow]
    exact (hr.2 hd).2


end
end RouthHurwitz.ComplexRouth.Exact.Gaussian.Model.ProofsG
