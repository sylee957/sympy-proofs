module

public import SympyProofs.Calculus.Risch.Program.Hermite
public import SympyProofs.Calculus.Risch.Algebra.HermiteLemmas
public import SympyProofs.Calculus.Risch.Proof.Pole
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The specification of Hermite reduction (Risch 1969, pp. 180–181), in the form that uses
greatest common divisors only. For a fraction `A / D` whose denominator has only normal prime
factors, `hermite` returns an exact part `g` and a numerator over the squarefree part `Ds` of
`D`, with `A / D = g′ + A′ / Ds`.

`reduceTerm` prepares an arbitrary element of the field of a tower step: it is written in
lowest terms, the power of the generator in the denominator is split off at an exponential
step, and Hermite reduction leaves a fraction in lowest terms with squarefree denominator
whose prime factors are normal. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Hermite

open Polynomial

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

noncomputable local instance intAlgebraHermite {F : Type*} [Field F] :
    Algebra ℤ (RatFunc F) := Ring.toIntAlgebra _

local notation "ι" => algebraMap (K k n)[X] (RatFunc (K k n))

/-- Dividing every coefficient by a term divides the polynomial by its value. -/
theorem model_scaleInv (c : Term n) (p : Poly n) :
    Poly.model k (scaleInv c p) = C (Term.value k c)⁻¹ * Poly.model k p :=
  Poly.model_map_div p c

/-- Dividing every coefficient of a defined coefficient list by a defined term with nonzero
value gives a defined coefficient list. -/
theorem defined_scaleInv {c : Term n} {p : Poly n} (hc : Term.InDomain k c)
    (nz : Term.value k c ≠ 0) (hp : Poly.Defined k p) : Poly.Defined k (scaleInv c p) :=
  Poly.defined_map_div hp hc nz

/-- A unit of the polynomial ring is its constant coefficient. -/
theorem unit_eq_C {F : Type*} [Field F] {g : F[X]} (hg : IsUnit g) :
    g = C (g.coeff 0) ∧ g.coeff 0 ≠ 0 := by
  obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hg
  rw [coeff_C_zero]
  exact ⟨rfl, hr.ne_zero⟩

/-- The standing assumptions on the squarefree part `Ds` of the denominator: it is a defined
coefficient list with nonvanishing highest coefficient, it is squarefree, and each of its
prime factors is normal for the derivation of the tower step. -/
structure Base (k : Type) [Field k] [CharZero k] (t : Tower (n+1)) (Ds : Poly n) : Prop where
  admissible : t.Admissible k
  defined : Poly.Defined k Ds
  normalForm : Poly.Normal k Ds
  squarefree : Squarefree (Poly.model k Ds)
  normal : ∀ p : (K k n)[X], Prime p → p ∣ Poly.model k Ds → ¬ p ∣ Tower.polyDer k t p

/-- The loop invariant on the repeated part `Dm` of the denominator: it is a defined
coefficient list with nonvanishing highest coefficient, and each of its prime factors
divides the squarefree part. -/
structure Inv (k : Type) [Field k] [CharZero k] (Ds Dm : Poly n) : Prop where
  defined : Poly.Defined k Dm
  normalForm : Poly.Normal k Dm
  radical : ∀ p : (K k n)[X], Prime p → p ∣ Poly.model k Dm → p ∣ Poly.model k Ds

/-- One step of Hermite reduction: for a repeated part `Dm` that is not constant, the step
returns a numerator `B`, a new numerator `A′` and a shorter repeated part `Dm′` with
`A / (Ds Dm) = (B / Dm)′ + A′ / (Ds Dm′)`, and the invariant is kept. -/
theorem step_spec {t : Tower (n+1)} {Ds A Dm : Poly n} (hb : Base k t Ds)
    (hA : Poly.Defined k A) (inv : Inv k Ds Dm) (big : 2 ≤ Dm.length) :
    Poly.Defined k (step t Ds A Dm).1 ∧ Poly.Defined k (step t Ds A Dm).2.1 ∧
      Inv k Ds (step t Ds A Dm).2.2 ∧ (step t Ds A Dm).2.2.length < Dm.length ∧
      ι (Poly.model k A) / ι (Poly.model k Ds * Poly.model k Dm) =
        t.der k (ι (Poly.model k (step t Ds A Dm).1) / ι (Poly.model k Dm)) +
          ι (Poly.model k (step t Ds A Dm).2.1) /
            ι (Poly.model k Ds * Poly.model k (step t Ds A Dm).2.2) := by
  obtain ⟨ht, dDs, nDs, hs, normal⟩ := hb
  obtain ⟨dDm, nDm, rad⟩ := inv
  have Dm0 : Poly.model k Dm ≠ 0 := nDm.model_ne_zero
  have Ds0 : Poly.model k Ds ≠ 0 := nDs.model_ne_zero
  -- the greatest common divisor of `Dm` and its derivative
  obtain ⟨dg, -, -, bez, gT, gD⟩ := Poly.gcd_spec dDm (Poly.defined_formalD dDm)
  rw [Poly.model_formalD] at bez gD
  obtain ⟨mG, dDm2, nrm2, -⟩ := Poly.trim_spec (Poly.defined_norm dg)
  obtain ⟨Dm2, hDm2⟩ :
      ∃ Dm2, Dm2 = Poly.trim (Poly.norm (Poly.gcd Dm (Poly.formalD Dm)).1) := ⟨_, rfl⟩
  rw [← hDm2] at mG dDm2 nrm2
  rw [Poly.model_norm dg] at mG
  rw [← mG] at bez gT gD
  have Dm20 : Poly.model k Dm2 ≠ 0 := fun z => Dm0 (zero_dvd_iff.mp (z ▸ gT))
  have nDm2 : Poly.Normal k Dm2 :=
    nrm2.resolve_left fun h => Dm20 (by rw [h, Poly.model_nil])
  -- its cofactor, the squarefree part of `Dm`
  have dq := (Poly.rem_spec dDm dDm2 nDm2).2.1
  have eDm := Poly.quot_of_dvd dDm dDm2 nDm2 gT
  obtain ⟨mS, dDms, nrmS, -⟩ := Poly.trim_spec (Poly.defined_norm dq)
  obtain ⟨Dms, hDms⟩ : ∃ Dms, Dms = Poly.trim (Poly.norm (Poly.quot Dm Dm2)) := ⟨_, rfl⟩
  rw [← hDms] at mS dDms nrmS
  rw [Poly.model_norm dq] at mS
  rw [← mS] at eDm
  have Dms0 : Poly.model k Dms ≠ 0 := fun z => Dm0 (by rw [eDm, z, mul_zero])
  have nDms : Poly.Normal k Dms :=
    nrmS.resolve_left fun h => Dms0 (by rw [h, Poly.model_nil])
  -- the cofactor of the squarefree part in `Ds`
  have dvdK := step_dvd_radical rad Dm0 eDm bez
  have dK := (Poly.rem_spec dDs dDms nDms).2.1
  have eK := Poly.quot_of_dvd dDs dDms nDms dvdK
  -- the polynomial `E`
  have dδ := Poly.defined_der ht dDm
  have dProd : Poly.Defined k (Poly.mul Ds (Poly.der t Dm)) := Poly.defined_mul dDs dδ
  have dvdE : Poly.model k Dm ∣ Poly.model k (Poly.mul Ds (Poly.der t Dm)) := by
    rw [Poly.model_mul, Poly.model_der]
    exact step_dvd (Tower.polyDer k t) rad Dm0
  have dQE := (Poly.rem_spec dProd dDm nDm).2.1
  have eQE := Poly.quot_of_dvd dProd dDm nDm dvdE
  rw [Poly.model_mul, Poly.model_der] at eQE
  obtain ⟨E, hE⟩ : ∃ E, E = Poly.neg (Poly.quot (Poly.mul Ds (Poly.der t Dm)) Dm) := ⟨_, rfl⟩
  have dE : Poly.Defined k E := hE ▸ Poly.defined_neg dQE
  have mE : Poly.model k E * Poly.model k Dm =
      -(Poly.model k Ds * Tower.polyDer k t (Poly.model k Dm)) := by
    rw [hE, Poly.model_neg, eQE]
    ring
  have cop := step_coprime (Tower.polyDer k t) hs normal rad Dm0 eDm mE
  -- the solution of `B E + C Dms = A`
  obtain ⟨dg0, da, db, bez0, g0E, g0S⟩ := Poly.gcd_spec dE dDms
  obtain ⟨bz, hbz⟩ : ∃ bz, bz = Poly.gcd E Dms := ⟨_, rfl⟩
  rw [← hbz] at dg0 da db bez0 g0E g0S
  obtain ⟨gC, c0⟩ := unit_eq_C (cop.isUnit_of_dvd' g0E g0S)
  obtain ⟨c, hc⟩ : ∃ c, c = Poly.coeff bz.1 0 := ⟨_, rfl⟩
  have dc : Term.InDomain k c := hc ▸ Poly.defined_coeff dg0 0
  have vc : Term.value k c = (Poly.model k bz.1).coeff 0 := by rw [hc, Poly.value_coeff]
  have cn : Term.value k c ≠ 0 := vc ▸ c0
  rw [← vc] at gC
  have dB0 : Poly.Defined k (scaleInv c (Poly.mul A bz.2.1)) :=
    defined_scaleInv dc cn (Poly.defined_mul hA da)
  obtain ⟨B, hB⟩ : ∃ B, B = Poly.norm (scaleInv c (Poly.mul A bz.2.1)) := ⟨_, rfl⟩
  have dB : Poly.Defined k B := hB ▸ Poly.defined_norm dB0
  have mB : Poly.model k B =
      C (Term.value k c)⁻¹ * (Poly.model k A * Poly.model k bz.2.1) := by
    rw [hB, Poly.model_norm dB0, model_scaleInv, Poly.model_mul]
  have dC : Poly.Defined k (scaleInv c (Poly.mul A bz.2.2)) :=
    defined_scaleInv dc cn (Poly.defined_mul hA db)
  have mC : Poly.model k (scaleInv c (Poly.mul A bz.2.2)) =
      C (Term.value k c)⁻¹ * (Poly.model k A * Poly.model k bz.2.2) := by
    rw [model_scaleInv, Poly.model_mul]
  have solve : Poly.model k B * Poly.model k E +
      Poly.model k (scaleInv c (Poly.mul A bz.2.2)) * Poly.model k Dms = Poly.model k A := by
    rw [mB, mC]
    have inv1 : C (Term.value k c)⁻¹ * Poly.model k bz.1 = 1 := by
      rw [gC, ← C_mul, inv_mul_cancel₀ cn, C_1]
    linear_combination C (Term.value k c)⁻¹ * Poly.model k A * bez0 + Poly.model k A * inv1
  have dNew : Poly.Defined k (Poly.sub (scaleInv c (Poly.mul A bz.2.2))
      (Poly.mul (Poly.der t B) (Poly.quot Ds Dms))) :=
    Poly.defined_sub dC (Poly.defined_mul (Poly.defined_der ht dB) dK)
  have run : step t Ds A Dm = (B, Poly.norm (Poly.sub (scaleInv c (Poly.mul A bz.2.2))
      (Poly.mul (Poly.der t B) (Poly.quot Ds Dms))), Dm2) := by
    rw [step, ← hDm2, ← hDms, ← hE, ← hbz, ← hc, ← hB]
  rw [run]
  dsimp only
  refine ⟨dB, Poly.defined_norm dNew, ⟨dDm2, nDm2, fun p hp h => rad p hp (h.trans gT)⟩, ?_, ?_⟩
  · have deg := step_degree (Dm := Poly.model k Dm) (G2 := Poly.model k Dm2)
      (by rw [nDm.natDegree]; omega) gD
    rw [nDm.natDegree, nDm2.natDegree] at deg
    have pos : 0 < Dm2.length := List.length_pos_iff.mpr nDm2.ne_nil
    omega
  · rw [Poly.model_norm dNew, Poly.model_sub, Poly.model_mul, Poly.model_der,
      Pole.der_div _ _ Dm0]
    exact step_identity (Tower.polyDer k t) Dm0 Ds0 eDm eK mE solve

/-- The loop of Hermite reduction: with enough fuel, it returns an exact part, a numerator
and a constant repeated part `Dm′` with
`A / (Ds Dm) + g′ = A′ / (Ds Dm′) + g′′`, where `g` is the exact part accumulated before and
`g′′` the one returned. -/
theorem loop_spec {t : Tower (n+1)} {Ds : Poly n} (hb : Base k t Ds) :
    ∀ (fuel : ℕ) {g : Term (n+1)} {A Dm : Poly n}, Term.InDomain k g → Poly.Defined k A →
      Inv k Ds Dm → Dm.length ≤ fuel + 1 →
      Term.InDomain k (loop t Ds fuel g A Dm).1 ∧ Poly.Defined k (loop t Ds fuel g A Dm).2.1 ∧
        Inv k Ds (loop t Ds fuel g A Dm).2.2 ∧ (loop t Ds fuel g A Dm).2.2.length ≤ 1 ∧
        ι (Poly.model k A) / ι (Poly.model k Ds * Poly.model k Dm) +
            t.der k (Term.value k g) =
          ι (Poly.model k (loop t Ds fuel g A Dm).2.1) /
            ι (Poly.model k Ds * Poly.model k (loop t Ds fuel g A Dm).2.2) +
              t.der k (Term.value k (loop t Ds fuel g A Dm).1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro g A Dm hg hA inv len
    exact ⟨hg, hA, inv, len, rfl⟩
  | succ fuel ih =>
    intro g A Dm hg hA inv len
    rw [loop]
    by_cases small : Dm.length ≤ 1
    · rw [ite_eq_left (Nat.ble_eq_true_of_le small)]
      exact ⟨hg, hA, inv, small, rfl⟩
    · rw [ite_eq_right fun h => small (Nat.le_of_ble_eq_true h)]
      obtain ⟨dB, dA', inv', lt, id⟩ := step_spec hb hA inv (by omega)
      have Dm0 : ι (Poly.model k Dm) ≠ 0 :=
        RatFunc.algebraMap_ne_zero inv.normalForm.model_ne_zero
      have hg' : Term.InDomain k
          (.add g (.div (Poly.toTerm (step t Ds A Dm).1) (Poly.toTerm Dm))) := by
        refine ⟨hg, Poly.inDomain_toTerm dB, Poly.inDomain_toTerm inv.defined, ?_⟩
        change Term.value k (Poly.toTerm Dm) ≠ 0
        rw [Poly.value_toTerm]
        exact Dm0
      obtain ⟨o1, o2, o3, o4, o5⟩ := ih hg' dA' inv' (by omega)
      refine ⟨o1, o2, o3, o4, ?_⟩
      rw [← o5, id]
      change _ = _ + t.der k (Term.value k g +
        Term.value k (Poly.toTerm _) / Term.value k (Poly.toTerm Dm))
      rw [Poly.value_toTerm, Poly.value_toTerm, map_add]
      ring

/-- Hermite reduction of `A / D`, for a denominator all of whose prime factors are normal:
the exact part `g` is defined, the denominator `Ds` returned is squarefree and divides `D`,
and `A / D = g′ + A′ / Ds`. -/
theorem hermite_spec {t : Tower (n+1)} (ht : t.Admissible k) {A D : Poly n}
    (hA : Poly.Defined k A) (hD : Poly.Defined k D) (nD : Poly.Normal k D)
    (normal : ∀ p : (K k n)[X], Prime p → p ∣ Poly.model k D → ¬ p ∣ Tower.polyDer k t p) :
    Term.InDomain k (hermite t A D).1 ∧ Poly.Defined k (hermite t A D).2.1 ∧
      Poly.Defined k (hermite t A D).2.2 ∧ Poly.Normal k (hermite t A D).2.2 ∧
      Squarefree (Poly.model k (hermite t A D).2.2) ∧
      Poly.model k (hermite t A D).2.2 ∣ Poly.model k D ∧
      ι (Poly.model k A) / ι (Poly.model k D) =
        t.der k (Term.value k (hermite t A D).1) +
          ι (Poly.model k (hermite t A D).2.1) / ι (Poly.model k (hermite t A D).2.2) := by
  have D0 : Poly.model k D ≠ 0 := nD.model_ne_zero
  obtain ⟨dg, -, -, bez, gT, gD⟩ := Poly.gcd_spec hD (Poly.defined_formalD hD)
  rw [Poly.model_formalD] at bez gD
  obtain ⟨mG, dDm, nrm, -⟩ := Poly.trim_spec (Poly.defined_norm dg)
  obtain ⟨Dm, hDm⟩ :
      ∃ Dm, Dm = Poly.trim (Poly.norm (Poly.gcd D (Poly.formalD D)).1) := ⟨_, rfl⟩
  rw [← hDm] at mG dDm nrm
  rw [Poly.model_norm dg] at mG
  rw [← mG] at bez gT gD
  have Dm0 : Poly.model k Dm ≠ 0 := fun z => D0 (zero_dvd_iff.mp (z ▸ gT))
  have nDm : Poly.Normal k Dm := nrm.resolve_left fun h => Dm0 (by rw [h, Poly.model_nil])
  have dq := (Poly.rem_spec hD dDm nDm).2.1
  have eD := Poly.quot_of_dvd hD dDm nDm gT
  obtain ⟨mS, dDs, nrmS, -⟩ := Poly.trim_spec (Poly.defined_norm dq)
  obtain ⟨Ds, hDs⟩ : ∃ Ds, Ds = Poly.trim (Poly.norm (Poly.quot D Dm)) := ⟨_, rfl⟩
  rw [← hDs] at mS dDs nrmS
  rw [Poly.model_norm dq] at mS
  rw [← mS] at eD
  have Ds0 : Poly.model k Ds ≠ 0 := fun z => D0 (by rw [eD, z, mul_zero])
  have nDs : Poly.Normal k Ds := nrmS.resolve_left fun h => Ds0 (by rw [h, Poly.model_nil])
  have dvdD : Poly.model k Ds ∣ Poly.model k D := ⟨Poly.model k Dm, by rw [eD]; ring⟩
  have hb : Base k t Ds := ⟨ht, dDs, nDs, squarefree_of_gcd D0 eD bez,
    fun p hp h => normal p hp (h.trans dvdD)⟩
  have inv : Inv k Ds Dm := ⟨dDm, nDm, fun p hp h =>
    prime_dvd_of_gcd D0 eD gD hp (h.trans gT)⟩
  obtain ⟨o1, o2, o3, o4, o5⟩ := loop_spec hb Dm.length
    (show Term.InDomain k (.const 0 : Term (n+1)) from trivial) hA inv (by omega)
  obtain ⟨out, hout⟩ : ∃ out, out = loop t Ds Dm.length (.const 0) A Dm := ⟨_, rfl⟩
  rw [← hout] at o1 o2 o3 o4 o5
  have run : hermite t A D =
      (out.1, Poly.norm (scaleInv (Poly.coeff out.2.2 0) out.2.1), Ds) := by
    rw [hermite, ← hDm, ← hDs, ← hout]
  rw [run]
  dsimp only
  -- the last repeated part is a nonzero constant
  have len1 : out.2.2.length = 1 := by
    have := List.length_pos_iff.mpr o3.normalForm.ne_nil
    omega
  have deg0 : (Poly.model k out.2.2).natDegree = 0 := by rw [o3.normalForm.natDegree, len1]
  have eC : Poly.model k out.2.2 = C (Term.value k (Poly.coeff out.2.2 0)) := by
    rw [Poly.value_coeff]
    exact eq_C_of_natDegree_eq_zero deg0
  have cn : Term.value k (Poly.coeff out.2.2 0) ≠ 0 := by
    intro z
    apply o3.normalForm.model_ne_zero
    rw [eC, z, C_0]
  have dc := Poly.defined_coeff o3.defined 0
  have dA' := defined_scaleInv dc cn o2
  refine ⟨o1, Poly.defined_norm dA', dDs, nDs, hb.squarefree, dvdD, ?_⟩
  have zero : t.der k (Term.value k (.const 0 : Term (n+1))) = 0 := by
    rw [Term.value_const, Rat.cast_zero, map_zero]
  rw [zero, add_zero] at o5
  rw [Poly.model_norm dA', model_scaleInv, eD, mul_comm (Poly.model k Dm) (Poly.model k Ds),
    o5, eC]
  have c' : ι (C (Term.value k (Poly.coeff out.2.2 0))) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (fun z => cn (C_eq_zero.mp z))
  have s' : ι (Poly.model k Ds) ≠ 0 := RatFunc.algebraMap_ne_zero Ds0
  rw [add_comm]
  congr 1
  simp only [map_mul]
  rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C] at *
  rw [map_inv₀]
  field_simp

/-- A coefficient list is the power of the generator counted by `lowZeros` times the rest,
and the rest has nonzero constant coefficient unless the polynomial is zero. -/
theorem lowZeros_spec : ∀ {D : Poly n}, Poly.Defined k D →
    Poly.model k D = X ^ lowZeros D * Poly.model k (D.drop (lowZeros D)) ∧
      (Poly.model k D ≠ 0 → (Poly.model k (D.drop (lowZeros D))).coeff 0 ≠ 0)
  | [], _ => by simp [lowZeros, Poly.model_nil]
  | c :: cs, h => by
    have hc := h c List.mem_cons_self
    rw [lowZeros]
    by_cases z : c.isZero = true
    · rw [ite_eq_left z]
      obtain ⟨e, nz⟩ := lowZeros_spec (D := cs) fun x hx => h x (List.mem_cons_of_mem _ hx)
      have vc := (Term.isZero_iff hc).mp z
      refine ⟨?_, fun hne => nz fun z' => hne ?_⟩
      · rw [List.drop_succ_cons, Poly.model_cons, vc, C_0, zero_add, pow_succ]
        conv_lhs => rw [e]
        ring
      · rw [Poly.model_cons, vc, z', C_0]
        ring
    · rw [ite_eq_right z]
      refine ⟨by simp, fun _ => ?_⟩
      rw [List.drop_zero, Poly.model_cons]
      simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero]
      exact fun v => z ((Term.isZero_iff hc).mpr v)

/-- The denominator is the power of the generator that is split off times a polynomial
coprime to that power, all of whose prime factors are normal. -/
theorem order_spec {t : Tower (n+1)} (ht : t.Admissible k) {D : Poly n}
    (hD : Poly.Defined k D) (nz : Poly.model k D ≠ 0) :
    Poly.model k D = X ^ order t D * Poly.model k (D.drop (order t D)) ∧
      IsCoprime (X ^ order t D : (K k n)[X]) (Poly.model k (D.drop (order t D))) ∧
      ∀ p : (K k n)[X], Prime p → p ∣ Poly.model k (D.drop (order t D)) →
        ¬ p ∣ Tower.polyDer k t p := by
  cases t with
  | prim low b =>
    refine ⟨by simp [order], by simpa [order] using isCoprime_one_left, ?_⟩
    intro p hp _
    exact Pole.prim_normal ht hp
  | exp low u =>
    obtain ⟨e, c0⟩ := lowZeros_spec hD
    have c0' := c0 nz
    have nX : ¬ X ∣ Poly.model k (D.drop (lowZeros D)) := fun h => c0' (X_dvd_iff.mp h)
    refine ⟨e, ((prime_X.irreducible.coprime_iff_not_dvd).mpr nX).pow_left, ?_⟩
    intro p hp hpd
    apply Pole.exp_normal ht hp
    intro h0
    exact nX ((X_dvd_iff.mpr h0).trans hpd)

/-- The specification of the reduction of a term `f`: the exact part `g` is defined, the
fraction `Ar / Dr` is in lowest terms, its denominator is squarefree with normal prime
factors none of which divides the power of the generator split off, and
`f = g′ + Ar / Dr + L1 / θᵏ`. -/
structure ReducedSpec (k : Type) [Field k] [CharZero k] (t : Tower (n+1)) (f : Term (n+1))
    (p : Reduced n) : Prop where
  dg : Term.InDomain k p.g
  dA : Poly.Defined k p.Ar
  dD : Poly.Defined k p.Dr
  nD : Poly.Normal k p.Dr
  squarefree : Squarefree (Poly.model k p.Dr)
  normal : ∀ q : (K k n)[X], Prime q → q ∣ Poly.model k p.Dr → ¬ q ∣ Tower.polyDer k t q
  cop : IsCoprime (Poly.model k p.Ar) (Poly.model k p.Dr)
  dL : Poly.Defined k p.L1
  away : ∀ q : (K k n)[X], Prime q → q ∣ Poly.model k p.Dr → ¬ q ∣ Polynomial.X ^ p.k
  value : Term.value k f = t.der k (Term.value k p.g) +
    algebraMap (K k n)[X] (RatFunc (K k n)) (Poly.model k p.Ar) /
      algebraMap (K k n)[X] (RatFunc (K k n)) (Poly.model k p.Dr) +
    algebraMap (K k n)[X] (RatFunc (K k n)) (Poly.model k p.L1) / RatFunc.X ^ p.k

/-- The reduction of a term defined in the field of an admissible tower step meets its
specification. -/
theorem reduceTerm_spec {t : Tower (n+1)} (ht : t.Admissible k) {f : Term (n+1)}
    (hf : Term.InDomain k f) : ReducedSpec k t f (reduceTerm t f) := by
  obtain ⟨fe, fn⟩ := Poly.ofTerm_spec f hf
  obtain ⟨dN, dq⟩ := Poly.ofTerm_defined (k := k) f
  have qn : Poly.model k (Poly.ofTerm f).2 ≠ 0 := fun z => fn (by rw [z, map_zero])
  -- the denominator
  obtain ⟨mD, dD, nrmD, -⟩ := Poly.trim_spec (Poly.defined_norm dq)
  obtain ⟨D, hD⟩ : ∃ D, D = Poly.trim (Poly.norm (Poly.ofTerm f).2) := ⟨_, rfl⟩
  rw [← hD] at mD dD nrmD
  rw [Poly.model_norm dq] at mD
  have D0 : Poly.model k D ≠ 0 := mD ▸ qn
  obtain ⟨eD, copX, normalDn⟩ := order_spec ht dD D0
  obtain ⟨j, hj⟩ : ∃ j, j = order t D := ⟨_, rfl⟩
  rw [← hj] at eD copX normalDn
  have dDrop : Poly.Defined k (D.drop j) := fun c hc => dD c (List.mem_of_mem_drop hc)
  obtain ⟨mDn, dDn, nrmDn, -⟩ := Poly.trim_spec dDrop
  obtain ⟨Dn, hDn⟩ : ∃ Dn, Dn = Poly.trim (D.drop j) := ⟨_, rfl⟩
  rw [← hDn] at mDn dDn nrmDn
  rw [← mDn] at eD copX normalDn
  have Dn0 : Poly.model k Dn ≠ 0 := fun z => D0 (by rw [eD, z, mul_zero])
  have nDn : Poly.Normal k Dn := nrmDn.resolve_left fun h => Dn0 (by rw [h, Poly.model_nil])
  -- the partial fraction at the generator
  have dX : Poly.Defined k (Poly.mono j (.const 1) : Poly n) := Poly.defined_mono j trivial
  have mX : Poly.model k (Poly.mono j (.const 1) : Poly n) = X ^ j := by
    rw [Poly.model_mono, Term.value_const, Rat.cast_one, C_1, one_mul]
  obtain ⟨dg0, da, db, bez0, g0X, g0D⟩ := Poly.gcd_spec dX dDn
  obtain ⟨bz, hbz⟩ : ∃ bz, bz = Poly.gcd (Poly.mono j (.const 1)) Dn := ⟨_, rfl⟩
  rw [← hbz] at dg0 da db bez0 g0X g0D
  rw [mX] at bez0 g0X
  obtain ⟨gC, c0⟩ := unit_eq_C (copX.isUnit_of_dvd' g0X g0D)
  obtain ⟨c, hc⟩ : ∃ c, c = Poly.coeff bz.1 0 := ⟨_, rfl⟩
  have dc : Term.InDomain k c := hc ▸ Poly.defined_coeff dg0 0
  have vc : Term.value k c = (Poly.model k bz.1).coeff 0 := by rw [hc, Poly.value_coeff]
  have cn : Term.value k c ≠ 0 := vc ▸ c0
  rw [← vc] at gC
  have dA0 : Poly.Defined k (scaleInv c (Poly.mul (Poly.ofTerm f).1 bz.2.1)) :=
    defined_scaleInv dc cn (Poly.defined_mul dN da)
  have dL0 : Poly.Defined k (scaleInv c (Poly.mul (Poly.ofTerm f).1 bz.2.2)) :=
    defined_scaleInv dc cn (Poly.defined_mul dN db)
  obtain ⟨A1, hA1⟩ :
      ∃ A1, A1 = Poly.norm (scaleInv c (Poly.mul (Poly.ofTerm f).1 bz.2.1)) := ⟨_, rfl⟩
  obtain ⟨L1, hL1⟩ :
      ∃ L1, L1 = Poly.norm (scaleInv c (Poly.mul (Poly.ofTerm f).1 bz.2.2)) := ⟨_, rfl⟩
  have dA1 : Poly.Defined k A1 := hA1 ▸ Poly.defined_norm dA0
  have dL1 : Poly.Defined k L1 := hL1 ▸ Poly.defined_norm dL0
  have mA1 : Poly.model k A1 =
      C (Term.value k c)⁻¹ * (Poly.model k (Poly.ofTerm f).1 * Poly.model k bz.2.1) := by
    rw [hA1, Poly.model_norm dA0, model_scaleInv, Poly.model_mul]
  have mL1 : Poly.model k L1 =
      C (Term.value k c)⁻¹ * (Poly.model k (Poly.ofTerm f).1 * Poly.model k bz.2.2) := by
    rw [hL1, Poly.model_norm dL0, model_scaleInv, Poly.model_mul]
  have split : Poly.model k A1 * X ^ j + Poly.model k L1 * Poly.model k Dn =
      Poly.model k (Poly.ofTerm f).1 := by
    rw [mA1, mL1]
    have inv1 : C (Term.value k c)⁻¹ * Poly.model k bz.1 = 1 := by
      rw [gC, ← C_mul, inv_mul_cancel₀ cn, C_1]
    linear_combination C (Term.value k c)⁻¹ * Poly.model k (Poly.ofTerm f).1 * bez0 +
      Poly.model k (Poly.ofTerm f).1 * inv1
  -- Hermite reduction and lowest terms
  obtain ⟨dg, dA2, dDs, nDs, sqf, dvdDs, idH⟩ := hermite_spec ht dA1 dDn nDn normalDn
  obtain ⟨hm, hhm⟩ : ∃ hm, hm = hermite t A1 Dn := ⟨_, rfl⟩
  rw [← hhm] at dg dA2 dDs nDs sqf dvdDs idH
  obtain ⟨dr1, dr2, r20, cop, cross⟩ := Poly.reduce_spec dA2 dDs nDs.model_ne_zero
  obtain ⟨rd, hrd⟩ : ∃ rd, rd = Poly.reduce hm.2.1 hm.2.2 := ⟨_, rfl⟩
  rw [← hrd] at dr1 dr2 r20 cop cross
  obtain ⟨mDr, dDr, nrmDr, -⟩ := Poly.trim_spec (Poly.defined_norm dr2)
  obtain ⟨Dr, hDr⟩ : ∃ Dr, Dr = Poly.trim (Poly.norm rd.2) := ⟨_, rfl⟩
  rw [← hDr] at mDr dDr nrmDr
  rw [Poly.model_norm dr2] at mDr
  have nDr : Poly.Normal k Dr :=
    nrmDr.resolve_left fun h => r20 (by rw [← mDr, h, Poly.model_nil])
  have dvdR : Poly.model k Dr ∣ Poly.model k hm.2.2 := by
    rw [mDr]
    exact cop.symm.dvd_of_dvd_mul_left ⟨Poly.model k hm.2.1, by linear_combination -cross⟩
  have run : reduceTerm t f = ⟨j, hm.1, Poly.norm rd.1, Dr, L1⟩ := by
    rw [reduceTerm, ← hD, ← hj, ← hDn, ← hbz, ← hc, ← hA1, ← hL1, ← hhm, ← hrd, ← hDr]
  rw [run]
  have Dr0 : ι (Poly.model k Dr) ≠ 0 := RatFunc.algebraMap_ne_zero nDr.model_ne_zero
  have Ds0 : ι (Poly.model k hm.2.2) ≠ 0 := RatFunc.algebraMap_ne_zero nDs.model_ne_zero
  have Dn0' : ι (Poly.model k Dn) ≠ 0 := RatFunc.algebraMap_ne_zero Dn0
  have Xj0 : (RatFunc.X : RatFunc (K k n)) ^ j ≠ 0 := pow_ne_zero j RatFunc.X_ne_zero
  refine
    { dg := dg, dA := Poly.defined_norm dr1, dD := dDr, nD := nDr,
      squarefree := Squarefree.squarefree_of_dvd dvdR sqf,
      normal := fun q hq h => normalDn q hq ((h.trans dvdR).trans dvdDs),
      cop := by rw [Poly.model_norm dr1, mDr]; exact cop, dL := dL1,
      away := fun q hq h hX =>
        hq.not_isUnit (copX.isUnit_of_dvd' hX ((h.trans dvdR).trans dvdDs)),
      value := ?_ }
  change _ = _ + ι (Poly.model k (Poly.norm rd.1)) / _ + _
  rw [Poly.model_norm dr1, mDr]
  have e1 : Term.value k f =
      ι (Poly.model k A1) / ι (Poly.model k Dn) + ι (Poly.model k L1) / RatFunc.X ^ j := by
    have fe' : Term.value k f = ι (Poly.model k (Poly.ofTerm f).1) / ι (Poly.model k D) := by
      rw [mD, fe, mul_div_assoc, div_self fn, mul_one]
    rw [fe', eD, ← split]
    simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X]
    field_simp
  have e2 : ι (Poly.model k hm.2.1) / ι (Poly.model k hm.2.2) =
      ι (Poly.model k rd.1) / ι (Poly.model k rd.2) := by
    have r20' : ι (Poly.model k rd.2) ≠ 0 := RatFunc.algebraMap_ne_zero r20
    rw [div_eq_div_iff Ds0 r20', ← map_mul, ← map_mul, cross]
  rw [e1, idH, e2]

/-- At a primitive step nothing is split off: the order at the generator is zero. -/
theorem reduceTerm_order (t : Tower n) (b : Term n) (f : Term (n+1)) :
    (reduceTerm (t.prim b) f).k = 0 := rfl

end SympyProofs.Calculus.Risch.Hermite
