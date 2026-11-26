module

public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Interpretation

/-! The descended root sums represent the sum of both signed interpretations. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric.Descent

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable [Fact (¬ IsSquare (-1 : K R 0))] {n : ℕ}
local notation "E" => WithI (K R 0)
variable (k : Type) [Field k] [CharZero k] [Algebra R k] [FaithfulSMul R k]

/-- The two descended moduli and their arguments are regular. Together they contribute
exactly the sum obtained from evaluating the original unit-weight sum in both models. -/
theorem pairedSums_spec (t : Tower R n) (s : RootSum E n) (hw : s.weight = 1)
    (P N : Interpretation E k n) (j : k) (hj : j^2 = -1) (H : Fits P j) (G : Fits N (-j))
    (hp : P.Regular s) (hn : N.Regular s) :
    (∀ r ∈ pairedSums s, r.Regular k) ∧
      ((pairedSums s).map (RootSum.deriv k t)).sum =
        P.derivative (t.modelD k) s + N.derivative (t.modelD k) s := by
  classical
  let I := Interpretation.standard (S := R) (n := n) k
  let f := Model.constantHom (R := R) k
  let Ck := Model.C k n
  let D := t.modelD k
  let e := Step.atRoot f
  let v := fun z => Step.atRoot (val (n := n) (R := R) k) (Ck z)
  let p := s.modulus.map (fun a => (project 0 a).re)
  let q := s.modulus.map (fun a => (project 0 a).im)
  let a := s.arg.map (fun u => (project n u).re)
  let b := s.arg.map (fun u => (project n u).im)
  let m := Step.modelPoly f
  let U : RootSum R n := ⟨(moduli p q).1,a^2+b^2,1⟩
  let V : RootSum R n := ⟨(moduli p q).2,(p.map K.ofConst)*a+(q.map K.ofConst)*b,1⟩
  have hList : pairedSums s = [U,V] := rfl
  have Pm : P.modulus s = m p + C j * m q := H.modulus s
  have Nm : N.modulus s = m p - C j * m q := by
    simpa only [map_neg,neg_mul,← sub_eq_add_neg] using G.modulus s
  have NZ : p^2 + q^2 ≠ 0 := by
    intro h
    have hx : C j ^ 2 = (-1 : k[X]) := by rw [← map_pow,hj,map_neg,map_one]
    apply (mul_ne_zero hp.1 hn.1)
    rw [Pm,Nm]
    have eq : (m p + C j * m q)*(m p - C j * m q) = m (p^2+q^2) := by
      rw [map_add,map_pow,map_pow]
      linear_combination -(m q)^2*hx
    rw [eq,h,map_zero]
  obtain ⟨nzU,nzV⟩ := moduli_ne_zero f NZ
  have posRoot (z : k) : (P.modulus s).IsRoot z ↔ e z p + j * e z q = 0 := by
    rw [Pm,IsRoot.def,eval_add,eval_mul,eval_C]; rfl
  have negRoot (z : k) : (N.modulus s).IsRoot z ↔ e z p - j * e z q = 0 := by
    rw [Nm,IsRoot.def,eval_sub,eval_mul,eval_C]; rfl
  have ur (z : k) : (I.modulus U).IsRoot z ↔
      (P.modulus s).IsRoot z ∧ (N.modulus s).IsRoot z := by
    rw [posRoot,negRoot]; exact common_roots f p q j hj z
  have vr (z : k) : (I.modulus V).IsRoot z ↔
      ((P.modulus s).IsRoot z ∨ (N.modulus s).IsRoot z) ∧
        ¬((P.modulus s).IsRoot z ∧ (N.modulus s).IsRoot z) := by
    rw [posRoot,negRoot]; exact exclusive_roots f p q NZ j hj z
  have pa (z : k) : P.argument s z = v z a + Ck j*v z b := H.argument s z
  have na (z : k) : N.argument s z = v z a - Ck j*v z b := by
    simpa only [map_neg,neg_mul,← sub_eq_add_neg] using G.argument s z
  have ua (z : k) : I.argument U z = (v z a)^2 + (v z b)^2 := by
    change v z (a^2+b^2) = _; rw [map_add,map_pow,map_pow]
  have va (z : k) : I.argument V z = Ck (e z p)*v z a + Ck (e z q)*v z b := by
    change v z ((p.map K.ofConst)*a+(q.map K.ofConst)*b) = _
    rw [map_add,map_mul,map_mul]
    rw [show v z (p.map K.ofConst) = _ from Residue.atRoot_ofConst k p z,
      show v z (q.map K.ofConst) = _ from Residue.atRoot_ofConst k q z]
  let ld := fun x : M k n => D x/x
  have hD (z : k) : D (Ck z) = 0 := Model.derivation_C k _ z
  have pu (z : k) (h₁ : (P.modulus s).IsRoot z) (h₂ : (N.modulus s).IsRoot z) :
      I.argument U z ≠ 0 ∧ ld (I.argument U z) = ld (P.argument s z)+ld (N.argument s z) := by
    rw [ua,pa,na]
    exact shared_log Ck D hj _ _ (pa z ▸ hp.2 _ h₁) (na z ▸ hn.2 _ h₂)
  have pv (z : k) (h₁ : (P.modulus s).IsRoot z) (h₂ : ¬(N.modulus s).IsRoot z) :
      I.argument V z ≠ 0 ∧ ld (I.argument V z) = ld (P.argument s z) := by
    rw [va,pa]
    exact exclusive_log Ck D hD hj _ _ ((posRoot _).mp h₁) (mt (negRoot _).mpr h₂)
      (pa z ▸ hp.2 _ h₁)
  have nv (z : k) (h₂ : (N.modulus s).IsRoot z) (h₁ : ¬(P.modulus s).IsRoot z) :
      I.argument V z ≠ 0 ∧ ld (I.argument V z) = ld (N.argument s z) := by
    rw [va,na]
    exact exclusive_log_neg Ck D hD hj _ _ ((negRoot _).mp h₂) (mt (posRoot _).mpr h₁)
      (na z ▸ hn.2 _ h₂)
  have regU : I.Regular U := ⟨nzU,fun z hz => (pu z ((ur z).mp hz).1 ((ur z).mp hz).2).1⟩
  have regV : I.Regular V := by
    refine ⟨nzV,fun z hz => ?_⟩
    obtain ⟨h₁,h₂⟩ := (vr z).mp hz
    rcases h₁ with h | h
    · exact (pv z h (fun hn => h₂ ⟨h,hn⟩)).1
    · exact (nv z h (fun hp => h₂ ⟨hp,h⟩)).1
  rw [hList]
  constructor
  · simpa using And.intro ((Interpretation.standard_regular k U).mp regU)
      ((Interpretation.standard_regular k V).mp regV)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    ← Interpretation.standard_derivative]
  change I.derivative D U + I.derivative D V = P.derivative D s + N.derivative D s
  simp only [Interpretation.derivative,show U.weight = 1 from rfl,show V.weight = 1 from rfl,
    hw,map_one,one_mul]
  apply sum_pair
  · intro z
    simpa only [Multiset.mem_toFinset,mem_roots regU.1,mem_roots hp.1,mem_roots hn.1] using ur z
  · intro z
    simpa only [Multiset.mem_toFinset,mem_roots regV.1,mem_roots hp.1,mem_roots hn.1] using vr z
  · intro z hz hw
    simp only [Multiset.mem_toFinset,mem_roots hp.1,mem_roots hn.1] at hz hw
    rw [show D (I.argument U z)/I.argument U z = _ from (pu z hz hw).2,mul_add]
  · intro z hz hw
    simp only [Multiset.mem_toFinset,mem_roots hp.1,mem_roots hn.1] at hz hw
    rw [show D (I.argument V z)/I.argument V z = _ from (pv z hz hw).2]
  · intro z hz hw
    simp only [Multiset.mem_toFinset,mem_roots hp.1,mem_roots hn.1] at hz hw
    rw [show D (I.argument V z)/I.argument V z = _ from (nv z hz hw).2]

end SympyProofs.Calculus.Antiderivative.Trigonometric.Descent
