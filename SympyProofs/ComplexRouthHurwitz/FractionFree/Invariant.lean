import SympyProofs.ComplexRouthHurwitz.FractionFree.Basic
import SympyProofs.ComplexRouthHurwitz.FractionFree.Initialization

/-! Row scaling, positive divisors, and the fraction-free counting invariant. -/
namespace RouthHurwitz.ComplexRouth.FractionFree
open Polynomial
open scoped ComplexConjugate
noncomputable section
open Classical

theorem inv_rescale {p u v : ℂ[X]} {m count : ℕ} {aux : Option Auxiliary}
    (h : Proofs.Inv p m u v count aux) (hm : 0 < m)
    (a b : ℝ) (ha : a ≠ 0) (hb : 0 < b/a) :
    Proofs.Inv p m (C (a:ℂ)*u) (C (b:ℂ)*v) count aux := by
  have hp := h.active hm
  have hc := pair_rescale_counts hp a b ha hb
  refine ⟨?_, ?_, ?_⟩
  · simp only [show m ≠ 0 by omega, ite_false]
    refine ⟨hp.upper_sym.scale a, hp.lower_sym.scale b,
      (natDegree_C_mul_le _ _).trans hp.upper_bound,
      (natDegree_C_mul_le _ _).trans hp.lower_bound, ?_⟩
    simp only [coeff_C_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_ne_zero ha hp.upper_ne
  · rw [hc.1]; exact h.right
  · cases aux with
    | none => exact h.axis.trans hc.2.symm
    | some x => exact h.axis

theorem inv_ff_eliminate {p u v : ℂ[X]} {m count : ℕ} {aux : Option Auxiliary}
    (h : Proofs.Inv p m u v count aux) (hm : 1 < m)
    (hv : (v.coeff (m-1)).re ≠ 0) (D : ℝ) (hD : 0 < D) :
    let B := (v.coeff (m-1)).re
    Proofs.Inv p (m-1) v
      (C ((B^2/D : ℝ):ℂ)*ComplexRouth.remainder (m-1-1) u v)
      (count + if (u.coeff m).re < 0 ↔ B < 0 then 0 else 1) aux := by
  let B := (v.coeff (m-1)).re
  have hB : B ≠ 0 := hv
  have hi := h.eliminate (by omega) hv
  simp only [show m-1 ≠ 0 by omega, ite_false] at hi
  have hratio : 0 < B*(B^2/D)/B := by
    rw [mul_div_cancel_left₀ _ hB]
    exact div_pos (sq_pos_of_ne_zero hB) hD
  have hh := inv_rescale hi (by omega) B (B*(B^2/D)) hB hratio
  have h1 : B*B⁻¹ = 1 := mul_inv_cancel₀ hB
  have h2 : B*(B^2/D)*B⁻¹ = B^2/D := by field_simp
  dsimp only [B] at h1 h2 hh
  simp only [← mul_assoc, ← map_mul, ← Complex.ofReal_mul, h1, h2, Complex.ofReal_one,
    map_one, one_mul, show m-1+1=m by omega] at hh
  exact hh

theorem nextLower_pack {N : ℕ} {d : ℕ} (u v : ℂ[X]) (h : ComplexRouth.Pair d u v)
    (hd : 0 < d) (hN : d+1 < N) (hv : (v.coeff d).re ≠ 0) (D : ℝ) (hD : 0 < D) :
    nextLower d D (Coefficients.pack N u) (Coefficients.pack N v) =
      Coefficients.pack N (C (((v.coeff d).re^2/D : ℝ):ℂ)*
        ComplexRouth.remainder (d-1) u v) := by
  have huN : u.natDegree < N := h.upper_bound.trans_lt hN
  have hvN : v.natDegree < N := h.lower_bound.trans_lt (by omega)
  have hvC : v.coeff d = ((v.coeff d).re : ℂ) := by
    apply Complex.ext <;> simp [h.lower_sym.real_coeff]
  rw [← Coefficients.scale_pack, ← Coefficients.remainder_pack _ u v huN hvN]
  apply Vector.ext; intro j hj
  simp only [nextLower, Coefficients.scale, Coefficients.remainder, Fin.getElem_fin, Vector.getElem_ofFn,
    Coefficients.entry_pack u huN, Coefficients.entry_pack v hvN,
    show d-1+2=d+1 by omega, show d-1+1=d by omega]
  simp only [Coefficients.pack, Vector.getElem_ofFn]
  rw [hvC]
  simp only [Complex.ofReal_re]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hv, Complex.ofReal_ne_zero.mpr (ne_of_gt hD)]

namespace ProofsFF
abbrev Locals (N : ℕ) := Coefficients.Row N × Coefficients.Row N ×
  List (Coefficients.Row N) × List ℝ × ℕ × Option Auxiliary × ℝ

def Valid (p : ℂ[X]) (m : ℕ) {N : ℕ} (s : Locals N) : Prop :=
  0 < s.2.2.2.2.2.2 ∧ ∃ u v : ℂ[X],
    s.1 = Coefficients.pack N u ∧ s.2.1 = Coefficients.pack N v ∧
    Proofs.Inv p m u v s.2.2.2.2.1 s.2.2.2.2.2.1

def initial (q : ℂ[X]) (n : ℕ) : Locals (n+1) :=
  let r := initialRows (Coefficients.pack (n+1) q) n
  (r.upper,r.lower,[],[],0,none,initialDivisor (Coefficients.pack (n+1) q) n)

def step (n k : ℕ) (s : Locals (n+1)) : Locals (n+1) :=
  let (u,v,rows,pivots,count,aux,D) := s
  let d := n-(k+1)
  let aux := if v = Coefficients.zero (n+1) ∧ aux.isNone then
    some { degree := d+1, rightBefore := count } else aux
  let D := if (Coefficients.entry v d).re = 0 then 1 else D
  let r := Coefficients.repair d u v
  let B := (Coefficients.entry r.lower d).re
  let count := count + if (Coefficients.entry r.upper (d+1)).re < 0 ↔ B < 0 then 0 else 1
  if d = 0 then
    (Coefficients.one (n+1),Coefficients.zero (n+1),rows ++ [r.upper,r.lower],pivots ++ [B],count,aux,B^2)
  else
    (r.lower,nextLower d D r.upper r.lower,
      rows ++ [r.upper,r.lower],pivots ++ [B],count,aux,B^2)

theorem initial_valid (p : ℂ[X]) (n : ℕ) (hn : 0 < n) (hd : p.natDegree = n)
    (hp : 0 < p.leadingCoeff.re) : Valid p n (initial p n) := by
  rw [initial, initialRows_pack p n hd (by omega), initialDivisor_pack p n hd (by omega)]
  have he : n-1+1=n := by omega
  have hs := first_pair p (n-1) (by omega) hp
  have hc := first_counts p (n-1) (by omega) hp
  rw [he] at hs hc
  refine ⟨?_, upperPart p n, firstLower p n, rfl, rfl, ?_, ?_, ?_⟩
  · split_ifs <;> positivity
  · simpa [show n ≠ 0 by omega] using hs
  · simpa using hc.1.symm
  · exact hc.2.symm

theorem step_valid (p : ℂ[X]) (n k : ℕ) (hk : k < n) (s : Locals (n+1))
    (h : Valid p (n-k) s) : Valid p (n-(k+1)) (step n k s) := by
  obtain ⟨U,V,rows,pivots,count,aux,D⟩ := s
  obtain ⟨hD,u,v,hu,hv,h⟩ := h
  dsimp only at hu hv hD h
  subst U V
  have hm : 0 < n-k := by omega
  have he : n-k-1 = n-(k+1) := by omega
  have he' : n-k = n-(k+1)+1 := by omega
  have hp : ComplexRouth.Pair (n-(k+1)) u v := by simpa [he] using h.active hm
  have hvN : v.natDegree < n+1 := hp.lower_bound.trans_lt (by omega)
  have hr := hp.repair_correct
  have hurN : (ComplexRouth.repair (n-(k+1)) u v).upper.natDegree < n+1 :=
    hr.1.upper_bound.trans_lt (by omega)
  have hvrN : (ComplexRouth.repair (n-(k+1)) u v).lower.natDegree < n+1 :=
    hr.1.lower_bound.trans_lt (by omega)
  let E := if (v.coeff (n-(k+1))).re = 0 then 1 else D
  have hE : 0 < E := by dsimp [E]; split <;> positivity
  have hi := h.repaired hm
  simp only [he', Nat.add_sub_cancel] at hi
  have hB := hr.2.1
  simp only [step, Coefficients.pack_eq_zero v hvN,
    Coefficients.entry_pack v hvN, Coefficients.repair_pack (N := n+1) _ u v hp (by omega),
    Coefficients.entry_pack _ hvrN, Coefficients.entry_pack _ hurN]
  split
  · rename_i hd
    have hn := hi.eliminate (by omega) (by simpa [he,he'] using hB)
    simp only [Nat.add_sub_cancel, hd, ite_true] at hn
    refine ⟨sq_pos_of_ne_zero hB, 1, 0, ?_, ?_, ?_⟩
    · exact (Coefficients.pack_one _).symm
    · exact (Coefficients.pack_zero _).symm
    · simpa [he,he',hd] using hn
  · rename_i hd
    have hn := inv_ff_eliminate hi (by omega) (by simpa [he,he'] using hB) E hE
    simp only [Nat.add_sub_cancel] at hn
    have hpack := nextLower_pack _ _ hr.1 (by omega)
      (show n-(k+1)+1 < n+1 by omega) hB E hE
    dsimp only [E] at hpack
    simp only [hpack]
    refine ⟨sq_pos_of_ne_zero hB, _, _, rfl, rfl, ?_⟩
    exact hn

theorem loop_valid (p : ℂ[X]) (n : ℕ) (hn : 0 < n) (hd : p.natDegree = n)
    (hp : 0 < p.leadingCoeff.re) (k : ℕ) (hk : k ≤ n) :
    Valid p (n-k) ((List.range k).foldl (fun s j => step n j s) (initial p n)) := by
  induction k with
  | zero => simpa using initial_valid p n hn hd hp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact step_valid p n k (by omega) _ (ih (by omega))

theorem finish {p : ℂ[X]} {N : ℕ} {s : Locals N} (h : Valid p 0 s) :
    s.2.2.2.2.1 = rightCount p ∧ axisTotal s.2.2.2.2.2.1 s.2.2.2.2.1 = axisCount p := by
  obtain ⟨_,u,v,_,_,hi⟩ := h
  exact hi.finish
end ProofsFF


end
end RouthHurwitz.ComplexRouth.FractionFree
