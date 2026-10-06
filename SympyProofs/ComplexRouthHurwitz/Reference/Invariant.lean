import SympyProofs.ComplexRouthHurwitz.Table.Coefficients

/-! Count invariants of the actual direct complex counting loop. -/
namespace RouthHurwitz.ComplexRouth
open Polynomial
noncomputable section
open Classical
namespace Proofs

/-- Before the first zero row the axis count is preserved. Afterwards its
value is fixed by the recorded symmetric row and the original right count. -/
def AxisData (p q : ℂ[X]) (count : ℕ) (aux : Option Auxiliary) : Prop :=
  match (generalizing := false) aux with
  | none => axisCount p = axisCount q
  | some a => a.rightBefore ≤ count ∧
      axisCount p + 2*rightCount p = a.degree + 2*a.rightBefore

structure Inv (p : ℂ[X]) (m : ℕ) (u v : ℂ[X]) (count : ℕ) (aux : Option Auxiliary) : Prop where
  shape : if m = 0 then u = 1 ∧ v = 0 else Pair (m-1) u v
  right : rightCount p = count + rightCount (u+v)
  axis : AxisData p (u+v) count aux

theorem Inv.active {p u v : ℂ[X]} {m count : ℕ} {aux : Option Auxiliary}
    (h : Inv p m u v count aux) (hm : 0 < m) : Pair (m-1) u v := by
  simpa [show m ≠ 0 by omega] using h.shape

theorem Inv.repaired {p u v : ℂ[X]} {m count : ℕ} {aux : Option Auxiliary}
    (h : Inv p m u v count aux) (hm : 0 < m) :
    let r := repair (m-1) u v
    let a := if v = 0 ∧ aux.isNone then some { degree := m, rightBefore := count } else aux
    Inv p m r.upper r.lower count a := by
  have hp := h.active hm
  have hr := hp.repair_correct
  dsimp only
  refine ⟨by simpa [show m ≠ 0 by omega] using hr.1, ?_, ?_⟩
  · rw [hr.2.2.1]; exact h.right
  · cases aux with
    | some a => simpa [AxisData] using h.axis
    | none =>
      by_cases hv : v = 0
      · simp only [hv, true_and, Option.isNone_none, ite_true, AxisData]
        refine ⟨le_rfl, ?_⟩
        have hs := symmetric_counts u (m-1+1) hp.upper_sym
        have hd := hp.upper_degree
        have ha := h.axis
        have hc := h.right
        simp only [AxisData, hv, add_zero] at ha hc
        omega
      · simp only [hv, false_and, ite_false, AxisData]
        exact h.axis.trans (hr.2.2.2 hv).symm

theorem Inv.eliminate {p u v : ℂ[X]} {m count : ℕ} {aux : Option Auxiliary}
    (h : Inv p m u v count aux) (hm : 0 < m) (hv : (v.coeff (m-1)).re ≠ 0) :
    let d := m-1
    let a := C (((v.coeff d).re⁻¹ : ℝ) : ℂ)
    let nextU := if d = 0 then 1 else a*v
    let nextV := if d = 0 then 0 else a*remainder (d-1) u v
    Inv p d nextU nextV (count + if (u.coeff (d+1)).re < 0 ↔ (v.coeff d).re < 0 then 0 else 1) aux := by
  have hp := h.active hm
  dsimp only
  by_cases hd : m-1 = 0
  · simp only [hd, ite_true] at hv hp ⊢
    have hc := hp.terminal_counts hv
    refine ⟨by simp, ?_, ?_⟩
    · have hh := h.right
      rw [hc.1] at hh
      simpa [rightCount, regionCount] using hh
    · cases aux with
      | none =>
        have hh := h.axis
        change axisCount p = axisCount (u+v) at hh
        simpa [AxisData, axisCount, regionCount] using hh.trans hc.2
      | some a =>
        exact ⟨h.axis.1.trans (Nat.le_add_right _ _), h.axis.2⟩
  · have he : m-1 = (m-1-1)+1 := by omega
    have hp' : Pair ((m-1-1)+1) u v := by rwa [← he]
    have hv' : (v.coeff ((m-1-1)+1)).re ≠ 0 := by rwa [← he]
    have hn := hp'.count_advance hv'
    have hc := hp'.eliminate_counts hv'
    rw [← he] at hn hc
    simp only [show m-1-1+2=m-1+1 by omega] at hc
    simp only [ite_eq_right hd]
    refine ⟨by simpa [hd] using hn, ?_, ?_⟩
    · rw [← mul_add]
      have hh := h.right
      omega
    · rw [← mul_add]
      cases aux with
      | none => exact h.axis.trans hc.2
      | some a => exact ⟨h.axis.1.trans (Nat.le_add_right _ _), h.axis.2⟩

-- These tuples describe mutable locals only; they are not a second runner.
abbrev Locals := ℂ[X] × ℂ[X] × List ℂ[X] × List ℝ × ℕ × Option Auxiliary

def atLocals (p : ℂ[X]) (m : ℕ) (s : Locals) : Prop :=
  Inv p m s.1 s.2.1 s.2.2.2.2.1 s.2.2.2.2.2

def initial (q : ℂ[X]) (n : ℕ) : Locals :=
  let r := scan q n
  (r.upper,r.lower,[],[],0,none)

def step (n k : ℕ) (s : Locals) : Locals :=
  let (u,v,rows,pivots,count,aux) := s
  let d := n-(k+1)
  let aux := if v = 0 ∧ aux.isNone then some { degree := d+1, rightBefore := count } else aux
  let r := repair d u v
  let pivot := (r.lower.coeff d).re
  let count := count + if (r.upper.coeff (d+1)).re < 0 ↔ pivot < 0 then 0 else 1
  if d = 0 then (1,0,rows ++ [r.upper,r.lower],pivots ++ [pivot],count,aux)
  else
    let a := C ((pivot⁻¹ : ℝ) : ℂ)
    (a*r.lower,a*remainder (d-1) r.upper r.lower,
      rows ++ [r.upper,r.lower],pivots ++ [pivot],count,aux)

theorem step_inv (p : ℂ[X]) (n k : ℕ) (hk : k < n) (s : Locals)
    (h : atLocals p (n-k) s) : atLocals p (n-(k+1)) (step n k s) := by
  obtain ⟨u,v,rows,pivots,count,aux⟩ := s
  change Inv p (n-k) u v count aux at h
  have hm : 0 < n-k := by omega
  have hr := h.repaired hm
  have hv := (h.active hm).repair_correct.2.1
  have hn := hr.eliminate hm hv
  have he : n-k-1 = n-(k+1) := by omega
  have he' : n-k = n-(k+1)+1 := by omega
  simp only [he] at hn
  by_cases hd : n-(k+1) = 0
  · simpa only [atLocals, step, hd, ite_true, he'] using hn
  · simpa only [atLocals, step, hd, ite_false, he'] using hn

theorem initial_inv (p : ℂ[X]) (n : ℕ) (hn : 0 < n) (hd : p.natDegree = n) (hp : PositiveLeading p) :
    atLocals p n (initial p n) := by
  rw [initial, scan]
  have he : n-1+1=n := by omega
  have hi := initial_pair p (n-1) (by omega) hp
  rw [he] at hi
  exact ⟨by simpa [show n ≠ 0 by omega] using hi, by simp [parts_add], by simp [AxisData,parts_add]⟩

theorem loop_inv (p : ℂ[X]) (n : ℕ) (hn : 0 < n) (hd : p.natDegree = n) (hp : PositiveLeading p)
    (k : ℕ) (hk : k ≤ n) :
    atLocals p (n-k) ((List.range k).foldl (fun s j => step n j s) (initial p n)) := by
  induction k with
  | zero => simpa using initial_inv p n hn hd hp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact step_inv p n k (by omega) _ (ih (by omega))

theorem Inv.finish {p u v : ℂ[X]} {count : ℕ} {aux : Option Auxiliary}
    (h : Inv p 0 u v count aux) :
    count = rightCount p ∧
    axisTotal aux count = axisCount p := by
  have hs : u=1 ∧ v=0 := by simpa using h.shape
  have hc : count = rightCount p := by
    have hh := h.right
    simpa [hs.1, hs.2, rightCount, regionCount] using hh.symm
  refine ⟨hc, ?_⟩
  cases aux with
  | none => simpa [axisTotal, AxisData, hs.1, hs.2, axisCount, regionCount] using h.axis.symm
  | some a =>
    have ha := h.axis
    change a.rightBefore ≤ count ∧ axisCount p+2*rightCount p=a.degree+2*a.rightBefore at ha
    dsimp only [axisTotal, Option.elim]
    omega

/-- The same mutable locals, with each polynomial represented by a vector. -/
abbrev VectorLocals (N : ℕ) := Coefficients.Row N × Coefficients.Row N ×
  List (Coefficients.Row N) × List ℝ × ℕ × Option Auxiliary

def encode (N : ℕ) (s : Locals) : VectorLocals N :=
  (Coefficients.pack N s.1, Coefficients.pack N s.2.1,
    s.2.2.1.map (Coefficients.pack N),s.2.2.2.1,s.2.2.2.2.1,s.2.2.2.2.2)

/-- Proof expression for one iteration of `run`; no second runner is evaluated. -/
def vectorStep (n k : ℕ) (s : VectorLocals (n+1)) : VectorLocals (n+1) :=
  let (u,v,rows,pivots,count,aux) := s
  let d := n-(k+1)
  let aux := if v = Coefficients.zero (n+1) ∧ aux.isNone then
    some { degree := d+1, rightBefore := count } else aux
  let r := Coefficients.repair d u v
  let pivot := (Coefficients.entry r.lower d).re
  let count := count + if (Coefficients.entry r.upper (d+1)).re < 0 ↔ pivot < 0 then 0 else 1
  if d = 0 then
    (Coefficients.one (n+1),Coefficients.zero (n+1),rows ++ [r.upper,r.lower],pivots ++ [pivot],count,aux)
  else
    let a := ((pivot⁻¹ : ℝ) : ℂ)
    (Coefficients.scale a r.lower,Coefficients.scale a (Coefficients.remainder (d-1) r.upper r.lower),
      rows ++ [r.upper,r.lower],pivots ++ [pivot],count,aux)

theorem vectorStep_encode (p : ℂ[X]) (n k : ℕ) (hk : k < n) (s : Locals)
    (h : atLocals p (n-k) s) :
    vectorStep n k (encode (n+1) s) = encode (n+1) (step n k s) := by
  obtain ⟨u,v,rows,pivots,count,aux⟩ := s
  change Inv p (n-k) u v count aux at h
  have hp : Pair (n-(k+1)) u v := by
    have := h.active (by omega)
    convert this using 1
  have hv : v.natDegree < n+1 := hp.lower_bound.trans_lt (by omega)
  have hr := hp.repair_correct.1
  have hur : (repair (n-(k+1)) u v).upper.natDegree < n+1 := hr.upper_bound.trans_lt (by omega)
  have hvr : (repair (n-(k+1)) u v).lower.natDegree < n+1 := hr.lower_bound.trans_lt (by omega)
  simp only [vectorStep, encode, step, Coefficients.pack_eq_zero v hv,
    Coefficients.repair_pack (N := n+1) _ u v hp (by omega),
    Coefficients.entry_pack _ hvr, Coefficients.entry_pack _ hur]
  split <;> simp [Coefficients.remainder_pack _ _ _ hur hvr,
    Coefficients.scale_pack, List.map_append]

theorem vector_loop_eq (p : ℂ[X]) (n : ℕ) (hn : 0 < n) (hd : p.natDegree = n) (hp : PositiveLeading p)
    (k : ℕ) (hk : k ≤ n) :
    (List.range k).foldl (fun s j => vectorStep n j s) (encode (n+1) (initial p n)) =
      encode (n+1) ((List.range k).foldl (fun s j => step n j s) (initial p n)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih (by omega)]
    exact vectorStep_encode p n k (by omega) _ (loop_inv p n hn hd hp k (by omega))

end Proofs
end
end RouthHurwitz.ComplexRouth
