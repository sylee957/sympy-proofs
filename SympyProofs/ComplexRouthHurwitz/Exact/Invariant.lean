import SympyProofs.ComplexRouthHurwitz.Exact.Initialization
import SympyProofs.ComplexRouthHurwitz.Exact.Model.Invariant

/-! The compressed loop simulates the Gaussian model at every reached iteration. -/
namespace RouthHurwitz.ComplexRouth.Exact.Gaussian
open Polynomial Model

namespace Proofs
noncomputable section
open Classical
abbrev Locals (N : ℕ) := Row N × Row N × List (Row N) × List ℤ × ℕ × Option Auxiliary × ℤ

def initial {N} (a : Rows.Row N) (n : ℕ) : Locals N :=
  let r := initialRows a n
  (r.upper,r.lower,[],[],0,none,initialDivisor a n)

def step (n k : ℕ) (s : Locals (n+1)) : Locals (n+1) :=
  let (u,v,rows,pivots,count,aux,D) := s
  let d := n-(k+1)
  let aux := if v=Vector.replicate (n+1) 0 ∧ aux.isNone then
    some { degree := d+1, rightBefore := count } else aux
  let D := if entry v d=0 then 1 else D
  let r := repair d u v
  let B := entry r.lower d
  let count := count + if entry r.upper (d+1)<0 ↔ B<0 then 0 else 1
  if d=0 then
    (Vector.ofFn (fun j => if j.val=0 then 1 else 0), Vector.replicate (n+1) 0,
      rows ++ [r.upper,r.lower],pivots ++ [B],count,aux,B^2)
  else
    (r.lower,nextLower d D r.upper r.lower,
      rows ++ [r.upper,r.lower],pivots ++ [B],count,aux,B^2)

def Related {N} (m : ℕ) (s : Locals N) (t : ProofsG.Locals N) : Prop :=
  decode m s.1=t.1 ∧ decode (m-1) s.2.1=t.2.1 ∧
  s.2.2.2.1=t.2.2.2.1 ∧ s.2.2.2.2.1=t.2.2.2.2.1 ∧
  s.2.2.2.2.2.1=t.2.2.2.2.2.1 ∧ s.2.2.2.2.2.2=t.2.2.2.2.2.2

/-- Symmetry in the existing loop invariant makes both row encodings lossless. -/
theorem valid_rows {N m} (q : ℂ[X]) (t : ProofsG.Locals N)
    (h : ProofsG.Valid q m t) (hm : 0 < m) :
    decode m (encode m t.1)=t.1 ∧ decode (m-1) (encode (m-1) t.2.1)=t.2.1 := by
  obtain ⟨hD,U,V,hu,hv,hi⟩ := h.1
  have hp := hi.active hm
  exact ⟨decode_encode_symmetric m t.1 U hu (by simpa only [show m-1+1=m by omega] using hp.upper_sym),
    decode_encode_symmetric (m-1) t.2.1 V hv hp.lower_sym⟩

theorem initial_related (q : ℂ[X]) (n : ℕ) (a : Rows.Row (n+1))
    (hn : 0 < n) (h : ProofsG.Valid q n (ProofsG.initial a n)) :
    Related n (initial a n) (ProofsG.initial a n) := by
  have hr := valid_rows q _ h hn
  have he := initialRows_spec a n hn
  simp only [Related, initial, ProofsG.initial]
  rw [he.1, he.2]
  simp only [and_true]
  exact ⟨hr.1, hr.2⟩

theorem repaired_rows (q : ℂ[X]) (n k : ℕ) (t : ProofsG.Locals (n+1))
    (hk : k < n) (h : ProofsG.Valid q (n-k) t) :
    let d := n-(k+1)
    let r := Rows.repair d t.1 t.2.1
    decode (d+1) (encode (d+1) r.upper)=r.upper ∧
      decode d (encode d r.lower)=r.lower := by
  obtain ⟨hD,U,V,hu,hv,hi⟩ := h.1
  have hp := hi.active (by omega : 0 < n-k)
  have he : n-k = n-(k+1)+1 := by omega
  rw [he, Nat.add_sub_cancel] at hp
  have hr := map_repair (n-(k+1)) t.1 t.2.1
  dsimp only [ProofsG.encode] at hu hv
  rw [hu,hv,Coefficients.repair_pack _ U V hp (by omega)] at hr
  have hru := congrArg Coefficients.Pair.upper hr
  have hrv := congrArg Coefficients.Pair.lower hr
  exact ⟨decode_encode_symmetric _ _ _ hru hp.repair_correct.1.upper_sym,
    decode_encode_symmetric _ _ _ hrv hp.repair_correct.1.lower_sym⟩

theorem step_related (q : ℂ[X]) (n k : ℕ) (s : Locals (n+1)) (t : ProofsG.Locals (n+1))
    (hk : k < n) (h : ProofsG.Valid q (n-k) t) (hs : Related (n-k) s t) :
    Related (n-(k+1)) (step n k s) (ProofsG.step n k t) := by
  obtain ⟨u,v,rows,pivots,count,aux,D⟩ := s
  obtain ⟨gu,gv,grows,gpivots,gcount,gaux,gD⟩ := t
  have hm : n-k = n-(k+1)+1 := by omega
  simp only [Related, hm, Nat.add_sub_cancel] at hs
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := hs
  let d := n-(k+1)
  let r := repair d u v
  let gr := Rows.repair d (decode (d+1) u) (decode d v)
  have hrs := repair_spec d u v
  have hr := repaired_rows q n k _ hk h
  have hu : decode (d+1) r.upper=gr.upper := by
    change decode (d+1) (repair d u v).upper=gr.upper
    rw [hrs.1]; exact hr.1
  have hv : decode d r.lower=gr.lower := by
    change decode d (repair d u v).lower=gr.lower
    rw [hrs.2]; exact hr.2
  have hA : (Rows.entry gr.upper (d+1)).re = entry r.upper (d+1) := by rw [← hu]; exact decode_pivot _ _
  have hB : (Rows.entry gr.lower d).re = entry r.lower d := by rw [← hv]; exact decode_pivot _ _
  have ready := ProofsG.step_ready q n k hk _ h
  let E := if entry v d=0 then 1 else D
  have hE : E ≠ 0 := by
    have hpos : (0:ℝ)<E := by simpa only [decode_pivot] using ready.1
    exact_mod_cast (ne_of_gt hpos)
  have hn (hd : d≠0) :
      decode (d-1) (nextLower d E r.upper r.lower) = Model.nextLower d E gr.upper gr.lower := by
    have hex (j : Fin (n+1)) : (E:GaussianInt) ∣ cellNumerator d gr.upper gr.lower j := by
      apply cell_divides _ _ _ _ hE
      simpa only [decode_pivot] using (ready.2 hd).1
    have hh := nextLower_encode d (by omega) E hE r.upper r.lower
      (by intro j; rw [hu,hv]; exact hex j)
    rw [hu,hv] at hh
    rw [hh]
    have hn := (valid_rows q _ (ProofsG.step_valid q n k hk _ h) (by omega : 0 < d)).2
    simpa only [ProofsG.step, show n-(k+1)≠0 from hd, ite_false, decode_pivot] using hn
  dsimp only [d, r, gr, E] at hu hv hA hB hn
  by_cases hd : n-(k+1)=0
  · simp only [Related, step, ProofsG.step, hd, ite_true, decode_eq_zero,
      decode_pivot]
    simp only [hd] at hA hB
    rw [hA,hB]
    simp only [and_true]
    apply Vector.ext; intro j hj
    by_cases hz : j=0
    · subst j; simp [decode, scalar, Rows.one]; rfl
    · simp [decode, scalar, Rows.one, hz]; rfl
  · simp only [Related, step, ProofsG.step, hd, ite_false, decode_eq_zero,
      decode_pivot, hA, hB]
    simp only [and_true]
    exact ⟨hv, hn hd⟩

/-- The actual integer locals admit Gaussian denotations satisfying the semantic
and subresultant invariants. No second runner or second loop is evaluated. -/
def Valid (q : ℂ[X]) (m : ℕ) {N} (s : Locals N) : Prop :=
  ∃ t : ProofsG.Locals N, ProofsG.Valid q m t ∧ Related m s t

theorem initial_valid (q : ℂ[X]) (n : ℕ) (a : Rows.Row (n+1))
    (hn : 0 < n) (hd : q.natDegree=n) (hq : 0 < q.leadingCoeff.re)
    (ha : mapRow a=Coefficients.pack (n+1) q) : Valid q n (initial a n) := by
  have h := ProofsG.initial_valid q n a hn hd hq ha
  exact ⟨ProofsG.initial a n, h, initial_related q n a hn h⟩

theorem step_valid (q : ℂ[X]) (n k : ℕ) (s : Locals (n+1))
    (hk : k < n) (h : Valid q (n-k) s) : Valid q (n-(k+1)) (step n k s) := by
  obtain ⟨t,ht,hs⟩ := h
  exact ⟨ProofsG.step n k t, ProofsG.step_valid q n k hk t ht,
    step_related q n k s t hk ht hs⟩

/-- The invariant holds at every prefix of the integer runner's imperative loop. -/
theorem loop_valid (q : ℂ[X]) (n : ℕ) (a : Rows.Row (n+1))
    (hn : 0 < n) (hd : q.natDegree=n) (hq : 0 < q.leadingCoeff.re)
    (ha : mapRow a=Coefficients.pack (n+1) q) (k : ℕ) (hk : k≤n) :
    Valid q (n-k) ((List.range k).foldl (fun s j => step n j s) (initial a n)) := by
  induction k with
  | zero => exact initial_valid q n a hn hd hq ha
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact step_valid q n k _ (by omega) (ih (by omega))

end
end Proofs


end RouthHurwitz.ComplexRouth.Exact.Gaussian
