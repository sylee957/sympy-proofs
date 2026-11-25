module

public import SympyProofs.Calculus.Risch.Program.Resultant
public import SympyProofs.Calculus.Risch.Proof.Poly
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The specification of the subresultant program: it computes the resultant of two
polynomials over the field of depth `n`, with their degrees as the formal degrees. One step of
the loop replaces `(A, B)` by `(B, R / β)`, where `R` is the pseudo-remainder of `A` by `B`
and `β = g h^δ` does not vanish. Each part of the step changes the resultant by a known
factor: exchanging the arguments by a sign, multiplying `A` by `c` by `c^(deg B)`, subtracting
a multiple of `B` from `A` not at all, lowering the formal degree of `R` to its degree by a
power of the leading coefficient of `B`, and dividing `R` by `β` by `β^(-deg B)`. The loop
invariant collects these factors as powers of `g` and `h`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch

open Polynomial

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

namespace Resultant

/-- The value of `tpow x j` is the `j`-th power of the value of `x`. -/
theorem value_tpow (x : Term n) (j : ℕ) : Term.value k (tpow x j) = Term.value k x ^ j := by
  induction j with
  | zero => rw [tpow, Term.value_const, Rat.cast_one, pow_zero]
  | succ j ih => rw [tpow, Coeff.value_mul, ih, pow_succ']

/-- A power of a defined term is defined. -/
theorem inDomain_tpow {x : Term n} (hx : Term.InDomain k x) (j : ℕ) :
    Term.InDomain k (tpow x j) := by
  induction j with
  | zero => rw [tpow]; trivial
  | succ j ih => rw [tpow]; exact Coeff.inDomain_mul hx ih

/-- One pseudo-division step. If `c A = R + B Q` with `deg B = d`, `deg Q + d ≤ m` and
`deg R ≤ r ≤ m`, then `c^d Res_{m,d}(A, B) = (-1)^(m d) b^(m - r) Res_{d,r}(B, R)`, where `b`
is the coefficient of degree `d` of `B`. -/
theorem resultant_pseudo_step {F : Type*} [Field F] {A B Q R : F[X]} {m d r : ℕ} {c : F}
    (hB : B.natDegree = d) (hdiv : C c * A = R + B * Q) (hQ : Q.natDegree + d ≤ m)
    (hR : R.natDegree ≤ r) (hrm : r ≤ m) :
    c ^ d * resultant A B m d = (-1) ^ (m * d) * B.coeff d ^ (m - r) * resultant B R d r := by
  have h1 := resultant_C_mul_right B A d m c
  rw [hdiv, resultant_add_mul_right B R Q d m hQ hB.le] at h1
  have h2 := resultant_add_right_deg B R d r (m - r) hR
  rw [Nat.add_sub_of_le hrm] at h2
  rw [resultant_comm A B m d]
  linear_combination (-1 : F) ^ (m * d) * (h2 - h1)

/-- The value of the program's conditional negation is a sign times the value. -/
private theorem value_signed (j : ℕ) (r : Term n) :
    Term.value k (if j % 2 == 1 then Coeff.neg r else r) = (-1) ^ j * Term.value k r := by
  by_cases hj : j % 2 = 1
  · rw [ite_eq_left (beq_iff_eq.mpr hj), Coeff.value_neg, (Nat.odd_iff.mpr hj).neg_one_pow,
      neg_one_mul]
  · rw [ite_eq_right (fun e => hj (beq_iff_eq.mp e)), (Nat.even_iff.mpr (by omega)).neg_one_pow,
      one_mul]

/-- The program's conditional negation of a defined term is defined. -/
private theorem inDomain_signed (j : ℕ) {r : Term n} (hr : Term.InDomain k r) :
    Term.InDomain k (if j % 2 == 1 then Coeff.neg r else r) := by
  by_cases hj : (j % 2 == 1) = true
  · rw [ite_eq_left hj]
    exact Coeff.inDomain_neg hr
  · rw [ite_eq_right hj]
    exact hr

/-- The identity in the field behind one step of the loop, with `d = deg B`, `m = deg A`,
`δ = m - d`, `r = deg R < d`, `β = G H^δ` and `h' H^δ = H b^δ`. -/
private theorem step_identity {F : Type*} [Field F] {b G H h' v' σ RA RBR RBB' : F}
    {m d δ r : ℕ} (hb : b ≠ 0) (hh' : h' ≠ 0) (hrd : r < d) (hm : m = d + δ)
    (P : (b ^ (δ + 1)) ^ d * RA = σ * b ^ (m - r) * RBR)
    (S : RBR = (G * H ^ δ) ^ d * RBB')
    (I : v' * b ^ r * h' ^ d = RBB' * h')
    (E : h' * H ^ δ = H * b ^ δ) :
    σ * v' * G ^ d * H ^ m = RA * H := by
  obtain ⟨t, rfl⟩ : ∃ t, d = r + t + 1 := ⟨d - r - 1, by omega⟩
  subst hm
  rw [show r + t + 1 + δ - r = t + 1 + δ by omega] at P
  have E' : (h' * H ^ δ) ^ (r + t) = (H * b ^ δ) ^ (r + t) := by rw [E]
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero ((δ + 1) * (r + t + 1)) hb) hh')
  linear_combination (-h' * H) * P + (-h' * H * σ * b ^ (t + 1 + δ)) * S +
    (H * σ * b ^ (t + 1 + δ) * (G * H ^ δ) ^ (r + t + 1)) * I +
    (-σ * v' * G ^ (r + t + 1) * h' * H ^ (1 + δ) * b ^ (r + t + 1 + δ)) * E'

/-- The invariant of the subresultant loop. For defined coefficient lists `A` and `B` with
nonzero highest coefficients and `deg B ≤ deg A`, fuel at least the length of `B`, and defined
`g` and `h` with nonzero values, the loop returns a defined term `v` with
`v g^(deg B) h^(deg A) = Res(A, B) h`, that is `v = Res(A, B) g^(-deg B) h^(1 - deg A)`. The
degrees are the lengths of the coefficient lists minus one. -/
theorem subresLoop_spec : ∀ (fuel : ℕ) {A B : Poly n} {g h : Term n},
    Poly.Defined k A → Poly.Normal k A → Poly.Defined k B → Poly.Normal k B →
    B.length ≤ A.length → B.length ≤ fuel →
    Term.InDomain k g → Term.value k g ≠ 0 → Term.InDomain k h → Term.value k h ≠ 0 →
    Term.InDomain k (subresLoop fuel A B g h) ∧
      Term.value k (subresLoop fuel A B g h) * Term.value k g ^ (B.length - 1) *
          Term.value k h ^ (A.length - 1) =
        resultant (Poly.model k A) (Poly.model k B) * Term.value k h := by
  intro fuel
  induction fuel with
  | zero =>
    intro A B g h _ _ _ nB _ hf
    exact absurd (List.length_pos_iff.mpr nB.ne_nil) (by omega)
  | succ fuel ih =>
    intro A B g h dA nA dB nB hBA hf dg ng dh nh
    obtain ⟨m, hm⟩ : ∃ m, m = A.length - 1 := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, d = B.length - 1 := ⟨_, rfl⟩
    have degA : (Poly.model k A).natDegree = m := by rw [nA.natDegree, hm]
    have degB : (Poly.model k B).natDegree = d := by rw [nB.natDegree, hd]
    have vb : Term.value k (Poly.lead B) = (Poly.model k B).coeff d := by
      rw [Poly.value_lead, hd]
    have db : Term.InDomain k (Poly.lead B) := Poly.defined_lead dB
    have nb : Term.value k (Poly.lead B) ≠ 0 := nB
    rw [degA, degB, ← hm, ← hd]
    by_cases hd0 : d = 0
    · -- `B` is a constant `b`, and `Res(A, b) = b^(deg A)`.
      have hd1 : (B.length - 1 == 0) = true := beq_iff_eq.mpr (by omega)
      rw [subresLoop, ite_eq_left hd1, ← hm]
      subst hd0
      have din : Term.InDomain k (Coeff.div (Coeff.mul h (tpow (Poly.lead B) m)) (tpow h m)) :=
        Coeff.inDomain_div (Coeff.inDomain_mul dh (inDomain_tpow db m)) (inDomain_tpow dh m)
          (by rw [value_tpow]; exact pow_ne_zero m nh)
      obtain ⟨s1, s2⟩ := Term.norm_sound n _ din
      refine ⟨s1, ?_⟩
      rw [s2, Coeff.value_div, Coeff.value_mul, value_tpow, value_tpow, pow_zero, mul_one,
        resultant_zero_right_deg, ← vb, div_mul_cancel₀ _ (pow_ne_zero m nh), mul_comm]
    · have hd1 : ¬(B.length - 1 == 0) = true := fun e => hd0 (by rw [hd]; exact beq_iff_eq.mp e)
      obtain ⟨δ, hδ⟩ : ∃ δ, δ = m - d := ⟨_, rfl⟩
      have hmd : m = d + δ := by omega
      obtain ⟨c, hc⟩ : ∃ c, c = tpow (Poly.lead B) (δ + 1) := ⟨_, rfl⟩
      obtain ⟨P, hP⟩ : ∃ P, P = Poly.scale c A := ⟨_, rfl⟩
      obtain ⟨R, hR⟩ : ∃ R, R = Poly.trim (Poly.rem P B) := ⟨_, rfl⟩
      rw [subresLoop, ite_eq_right hd1]
      dsimp only
      rw [← hm, ← hd, ← hδ, ← hc, ← hP, ← hR]
      -- The pseudo-remainder.
      have vc : Term.value k c = Term.value k (Poly.lead B) ^ (δ + 1) := by rw [hc, value_tpow]
      have dc : Term.InDomain k c := hc ▸ inDomain_tpow db (δ + 1)
      have dP : Poly.Defined k P := hP ▸ Poly.defined_scale dc dA
      have mP : Poly.model k P = C (Term.value k c) * Poly.model k A := by
        rw [hP, Poly.model_scale]
      obtain ⟨div, -, drem, lrem⟩ := Poly.rem_spec dP dB nB
      obtain ⟨mR, dR, nR, lR⟩ := Poly.trim_spec drem
      rw [← hR] at mR dR nR lR
      have hdiv : C (Term.value k c) * Poly.model k A =
          Poly.model k R + Poly.model k B * Poly.model k (Poly.quot P B) := by
        rw [← mP, div, mR, add_comm]
      have cne : Term.value k c ≠ 0 := by rw [vc]; exact pow_ne_zero _ nb
      have hQ : (Poly.model k (Poly.quot P B)).natDegree + d ≤ m := by
        by_cases hQ0 : Poly.model k (Poly.quot P B) = 0
        · rw [hQ0, natDegree_zero]
          omega
        · have e : Poly.model k B * Poly.model k (Poly.quot P B) =
              C (Term.value k c) * Poly.model k A - Poly.model k R := by
            rw [hdiv]
            ring
          have le : (C (Term.value k c) * Poly.model k A - Poly.model k R).natDegree ≤ m := by
            refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
            · exact (natDegree_C_mul_le _ _).trans degA.le
            · exact (Poly.natDegree_model_le R).trans (by omega)
          rw [← e, natDegree_mul nB.model_ne_zero hQ0, degB] at le
          omega
      rcases nR with hR0 | nR'
      · -- The remainder vanishes, and so does the resultant.
        rw [hR0, ite_eq_left List.isEmpty_nil]
        refine ⟨trivial, ?_⟩
        have key := resultant_pseudo_step degB hdiv hQ
          (show (Poly.model k R).natDegree ≤ 0 by rw [hR0, Poly.model_nil, natDegree_zero])
          (Nat.zero_le m)
        rw [hR0, Poly.model_nil, resultant_zero_right_deg, coeff_zero, zero_pow hd0,
          mul_zero] at key
        have z : resultant (Poly.model k A) (Poly.model k B) m d = 0 :=
          (mul_eq_zero.mp key).resolve_left (pow_ne_zero d cne)
        rw [Poly.value_zero, z]
        ring
      · have Rne : R ≠ [] := nR'.ne_nil
        rw [ite_eq_right (fun e => Rne (List.isEmpty_iff.mp e))]
        obtain ⟨r, hr⟩ : ∃ r, r = R.length - 1 := ⟨_, rfl⟩
        have hrd : r < d := by
          have := List.length_pos_iff.mpr Rne
          omega
        have degR : (Poly.model k R).natDegree = r := by rw [nR'.natDegree, hr]
        obtain ⟨β, hβ⟩ : ∃ β, β = Coeff.mul g (tpow h δ) := ⟨_, rfl⟩
        obtain ⟨B', hB'⟩ : ∃ B', B' = Poly.norm (R.map fun c => Term.div c β) := ⟨_, rfl⟩
        obtain ⟨h', hh'⟩ : ∃ h', h' =
            Term.norm (Coeff.div (Coeff.mul h (tpow (Poly.lead B) δ)) (tpow h δ)) := ⟨_, rfl⟩
        rw [← hβ, ← hB', ← hh']
        obtain ⟨v', hv'⟩ : ∃ v', v' = subresLoop fuel B B' (Poly.lead B) h' := ⟨_, rfl⟩
        rw [← hv', value_signed]
        -- The divisor `β`.
        have vβ : Term.value k β = Term.value k g * Term.value k h ^ δ := by
          rw [hβ, Coeff.value_mul, value_tpow]
        have nβ : Term.value k β ≠ 0 := by
          rw [vβ]
          exact mul_ne_zero ng (pow_ne_zero δ nh)
        have dβ : Term.InDomain k β := hβ ▸ Coeff.inDomain_mul dg (inDomain_tpow dh δ)
        -- The next divisor `B' = R / β`.
        have dmap := Poly.defined_map_div dR dβ nβ
        have dB' : Poly.Defined k B' := hB' ▸ Poly.defined_norm dmap
        have mB' : Poly.model k B' = C (Term.value k β)⁻¹ * Poly.model k R := by
          rw [hB', Poly.model_norm dmap, Poly.model_map_div]
        have lB' : B'.length = R.length := by
          rw [hB', Poly.norm, List.length_map, List.length_map]
        have nB' : Poly.Normal k B' := by
          rw [Poly.Normal, Poly.value_lead, mB', coeff_C_mul, lB', ← Poly.value_lead]
          exact mul_ne_zero (inv_ne_zero nβ) nR'
        have degB' : (Poly.model k B').natDegree = r := by rw [nB'.natDegree, lB', hr]
        have mR' : Poly.model k R = C (Term.value k β) * Poly.model k B' := by
          rw [mB', ← mul_assoc, ← C_mul, mul_inv_cancel₀ nβ, C_1, one_mul]
        -- The next `h`.
        have din : Term.InDomain k (Coeff.div (Coeff.mul h (tpow (Poly.lead B) δ)) (tpow h δ)) :=
          Coeff.inDomain_div (Coeff.inDomain_mul dh (inDomain_tpow db δ)) (inDomain_tpow dh δ)
            (by rw [value_tpow]; exact pow_ne_zero δ nh)
        obtain ⟨dh', vh'⟩ := Term.norm_sound n _ din
        rw [← hh'] at dh' vh'
        rw [Coeff.value_div, Coeff.value_mul, value_tpow, value_tpow] at vh'
        have nh' : Term.value k h' ≠ 0 := by
          rw [vh']
          exact div_ne_zero (mul_ne_zero nh (pow_ne_zero δ nb)) (pow_ne_zero δ nh)
        have E : Term.value k h' * Term.value k h ^ δ =
            Term.value k h * Term.value k (Poly.lead B) ^ δ := by
          rw [vh', div_mul_cancel₀ _ (pow_ne_zero δ nh)]
        -- The recursive call.
        obtain ⟨dv', I⟩ := ih dB nB dB' nB' (by omega) (by omega) db nb dh' nh'
        rw [← hv'] at dv' I
        refine ⟨inDomain_signed _ dv', ?_⟩
        rw [lB', ← hr, ← hd, degB, degB'] at I
        have P := resultant_pseudo_step degB hdiv hQ degR.le (by omega)
        rw [← vb, vc] at P
        have S : resultant (Poly.model k B) (Poly.model k R) d r =
            (Term.value k g * Term.value k h ^ δ) ^ d *
              resultant (Poly.model k B) (Poly.model k B') d r := by
          rw [mR', resultant_C_mul_right, vβ]
        exact step_identity nb nh' hrd hmd P S I E

/-- The subresultant program computes the resultant: for defined coefficient lists `F` and
`G`, `subresultant F G` is defined and its value is `Res(F, G)`, with the degrees of `F` and
`G` as the formal degrees. -/
theorem subresultant_spec {F G : Poly n} (hF : Poly.Defined k F) (hG : Poly.Defined k G) :
    Term.InDomain k (subresultant F G) ∧
      Term.value k (subresultant F G) = resultant (Poly.model k F) (Poly.model k G) := by
  obtain ⟨F', hF'⟩ : ∃ F', F' = Poly.trim F := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G', G' = Poly.trim G := ⟨_, rfl⟩
  obtain ⟨mF, dF, nF, -⟩ := Poly.trim_spec hF
  obtain ⟨mG, dG, nG, -⟩ := Poly.trim_spec hG
  rw [← hF'] at mF dF nF
  rw [← hG'] at mG dG nG
  rw [subresultant]
  dsimp only
  rw [← hF', ← hG', ← mF, ← mG]
  have one : Term.value k (.const 1 : Term n) = 1 := by rw [Term.value_const, Rat.cast_one]
  rcases nF with hF0 | nF'
  · rw [hF0, ite_eq_left List.isEmpty_nil, Poly.model_nil, resultant_zero_left, natDegree_zero,
      pow_zero, mul_one]
    by_cases hl : G'.length ≤ 1
    · rw [ite_eq_left (Nat.ble_eq.mpr hl)]
      refine ⟨trivial, ?_⟩
      rw [one, Nat.le_zero.mp ((Poly.natDegree_model_le G').trans (by omega)), pow_zero]
    · rw [ite_eq_right (fun e => hl (Nat.ble_eq.mp e))]
      refine ⟨trivial, ?_⟩
      have nG' : Poly.Normal k G' := nG.resolve_left fun e => hl (by simp [e])
      rw [Poly.value_zero, nG'.natDegree, zero_pow (by omega)]
  · rw [ite_eq_right (fun e => nF'.ne_nil (List.isEmpty_iff.mp e))]
    rcases nG with hG0 | nG'
    · rw [hG0, ite_eq_left List.isEmpty_nil, Poly.model_nil, resultant_zero_right,
        natDegree_zero, pow_zero, mul_one, nF'.natDegree]
      by_cases hl : F'.length ≤ 1
      · rw [ite_eq_left (Nat.ble_eq.mpr hl)]
        exact ⟨trivial, by rw [one, show F'.length - 1 = 0 by omega, pow_zero]⟩
      · rw [ite_eq_right (fun e => hl (Nat.ble_eq.mp e))]
        exact ⟨trivial, by rw [Poly.value_zero, zero_pow (by omega)]⟩
    · rw [ite_eq_right (fun e => nG'.ne_nil (List.isEmpty_iff.mp e))]
      have d1 : Term.InDomain k (.const 1 : Term n) := trivial
      have n1 : Term.value k (.const 1 : Term n) ≠ 0 := by
        rw [one]
        exact one_ne_zero
      by_cases hle : G'.length ≤ F'.length
      · rw [ite_eq_left (Nat.ble_eq.mpr hle)]
        obtain ⟨dv, hv⟩ := subresLoop_spec G'.length dF nF' dG nG' hle le_rfl d1 n1 d1 n1
        refine ⟨dv, ?_⟩
        simpa only [one, one_pow, mul_one] using hv
      · rw [ite_eq_right (fun e => hle (Nat.ble_eq.mp e))]
        obtain ⟨dv, hv⟩ :=
          subresLoop_spec F'.length dG nG' dF nF' (by omega) le_rfl d1 n1 d1 n1
        refine ⟨inDomain_signed _ dv, ?_⟩
        simp only [one, one_pow, mul_one] at hv
        rw [value_signed, hv, resultant_comm (Poly.model k F'), nF'.natDegree, nG'.natDegree]

end Resultant

end SympyProofs.Calculus.Risch
