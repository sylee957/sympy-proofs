module

public import SympyProofs.Calculus.Antiderivative.Program.Verify
public import SympyProofs.Calculus.Antiderivative.Proof.Verify.Trace
public import SympyProofs.Calculus.Antiderivative.Proof.Step.Residue
public import SympyProofs.Calculus.Antiderivative.Proof.PolynomialDerivation
public import SympyProofs.Calculus.Antiderivative.Spec.Level

/-! The computed squarefree residue modulus has the prescribed distinct roots, and the
logarithm argument is invertible modulo it whenever the root sum is regular. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.RootSum

open Polynomial

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [CharZero k] [IsAlgClosed k] [Algebra R k] [FaithfulSMul R k]
variable {n : ℕ}

/-- The squarefree part of the defining constant polynomial. -/
abbrev radical (s : RootSum R n) : Poly (K R 0) := (Step.squarefreeParts s.modulus).1

/-- The squarefree constant polynomial with coefficients included in the tower. -/
abbrev liftedRadical (s : RootSum R n) := s.radical.map (K.ofConst (n := n))

/-- The squarefree constant polynomial interpreted over the model scalars. -/
noncomputable abbrev constantRadical (s : RootSum R n) :=
  Step.modelPoly (Model.constantHom k) s.radical

omit [CharZero k] [IsAlgClosed k] in
theorem model_liftedRadical (s : RootSum R n) :
    Step.modelPoly (val k) s.liftedRadical = (s.constantRadical k).map (Model.C k n) := by
  simp only [liftedRadical,constantRadical,Step.modelPoly_apply,Poly.equiv_map,Polynomial.map_map]
  congr 1
  ext c
  exact (Model.C_constantHom k c).symm

omit [CharZero k] [IsAlgClosed k] in
theorem regular_modulus_ne_zero {s : RootSum R n} (h : s.Regular k) : s.modulus ≠ 0 := by
  intro e
  exact h.1 (by simp [modelModulus,e])

omit [CharZero k] [IsAlgClosed k] in
theorem squarefree_radical {s : RootSum R n} (h : s.Regular k) : Squarefree (s.constantRadical k) :=
  Step.squarefreePart_squarefree _ (regular_modulus_ne_zero k h)

omit [IsAlgClosed k] in
theorem radical_root (s : RootSum R n) (c : k) :
    (s.constantRadical k).IsRoot c ↔ (s.modelModulus k).IsRoot c :=
  Step.squarefreePart_roots _ s.modulus c

omit [IsAlgClosed k] in
theorem radical_roots [DecidableEq k] {s : RootSum R n} (h : s.Regular k) :
    (s.constantRadical k).roots.toFinset = (s.modelModulus k).roots.toFinset := by
  ext c
  simp only [Multiset.mem_toFinset,mem_roots (squarefree_radical k h).ne_zero,mem_roots h.1]
  exact radical_root k s c

omit [CharZero k] [IsAlgClosed k] in
theorem radical_degree {s : RootSum R n} :
    (s.constantRadical k).natDegree = s.liftedRadical.natDegree := by
  simp [constantRadical,liftedRadical,← Poly.natDegree_equiv,Poly.equiv_map]

theorem radical_coprime {s : RootSum R n} (h : s.Regular k) : IsCoprime s.arg s.liftedRadical := by
  classical
  let ev := Step.modelPoly (val (R := R) (n := n) k)
  have hd := squarefree_radical k h
  let P := s.constantRadical k
  let i := Model.C k n
  have hc : IsCoprime (ev s.arg) (ev s.liftedRadical) := by
    change IsCoprime _ (Step.modelPoly _ _)
    rw [model_liftedRadical, map_eq_nodal i hd]
    apply IsCoprime.mul_right
    · have hn : i P.leadingCoeff ≠ 0 := (map_ne_zero_iff i i.injective).mpr
        (leadingCoeff_ne_zero.mpr hd.ne_zero)
      exact ⟨0,C (i P.leadingCoeff)⁻¹,by rw [zero_mul,zero_add,← C_mul,inv_mul_cancel₀ hn,C_1]⟩
    · apply IsCoprime.prod_right
      intro z hz
      apply IsCoprime.symm
      apply (irreducible_X_sub_C _).coprime_iff_not_dvd.mpr
      rw [dvd_iff_isRoot]
      exact fun he => h.2 z ((radical_root k s z).mp ((mem_roots hd.ne_zero).mp
        (Multiset.mem_toFinset.mp hz))) (by
          simpa [ev,RootSum.argAt,Polynomial.IsRoot,eval_map] using he)
  have hc' : IsCoprime (Poly.equiv s.arg) (Poly.equiv s.liftedRadical) :=
    (Polynomial.isCoprime_map (val k)).mp hc
  simpa only [RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,RingEquiv.symm_apply_apply] using
    hc'.map Poly.equiv.symm.toRingHom

end SympyProofs.Calculus.Antiderivative.RootSum
