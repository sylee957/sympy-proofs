module

public import SympyProofs.Calculus.Antiderivative.Algebra.K.Constants
public import SympyProofs.Calculus.Antiderivative.Algebra.K.Heights

/-! Recognize constant fractions by comparing coefficients at one denominator monomial. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

namespace MPoly.Raw

variable {R : Type} [CommRing R]

/-- Sum all coefficients whose trimmed exponent vector matches the given one. -/
def readTerm (e : Mono) : Raw R → R
  | [] => 0
  | (d,c) :: p => (if d.trim = e.trim then c else 0) + readTerm e p

/-- Reading a valid monomial gives its coefficient in the polynomial. -/
theorem readTerm_eq {n : ℕ} {e : Mono} (he : e.trim.length ≤ n) (p : Raw R) :
    readTerm e p = (toMvPolynomial n p).coeff (e.exponents n) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rcases a with ⟨d,c⟩
    rw [readTerm, ih, toMvPolynomial_cons, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    congr 1
    by_cases hde : d.trim = e.trim
    · have hex : d.exponents n = e.exponents n := by
        rw [← Mono.exponents_trim n d, hde, Mono.exponents_trim]
      simp [hde, he, hex]
    · by_cases hd : d.trim.length ≤ n
      · have hex : d.exponents n ≠ e.exponents n := fun h =>
          hde (Mono.trim_eq_of_exponents_eq hd he h)
        simp [hde, hd, MvPolynomial.coeff_monomial, hex]
      · simp [hde, hd]

end MPoly.Raw

namespace K

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable {n : ℕ}

/-- A candidate constant from any nonzero term of the denominator. -/
def Raw.constantCandidate (n : ℕ) (x : Raw R) : K R 0 :=
  match MPoly.Raw.normalize n x.den with
  | [] => 0
  | (e,c) :: _ => K.C (MPoly.Raw.readTerm e x.num) / K.C c

@[simp] theorem equiv_C (a : R) :
    equiv (C a : K R n) = algebraMap (MvPolynomial (Fin n) R) _ (MvPolynomial.C a) :=
  toFractionRing_C a

/-- Including a constant coefficient preserves its value. -/
@[simp] theorem ofConst_C (a : R) : ofConst (C a : K R 0) = (C a : K R n) := by
  apply toFractionRing_injective
  change Raw.value n ((Raw.C a).atHeight 0) = Raw.value n (Raw.C a)
  rw [Raw.value_atHeight (Nat.zero_le n), Raw.value_C, Raw.value_C, Model.includeVars_polynomial]
  simp

/-- Every height-zero fraction is a quotient of two constant coefficients. -/
theorem ofRaw_constants (x : Raw R) :
    (ofRaw x : K R 0) = C x.num.constantTerm / C x.den.constantTerm := by
  apply equiv.injective
  simp [Raw.value, Raw.polyValue, MPoly.Raw.toMvPolynomial_zero_vars, map_div₀]

/-- A quotient equal to a constant has that constant as its coefficient ratio. -/
theorem Raw.candidate_eq {x : Raw R} {c : K R 0} (h : (ofRaw x : K R n) = ofConst c) :
    x.constantCandidate n = c := by
  cases hd : MPoly.Raw.normalize n x.den with
  | nil =>
    have hzero : (MPoly.ofRaw x.den : MPoly n R) = 0 :=
      MPoly.normalize_eq_iff.mp (hd.trans rfl)
    have hx : (ofRaw x : K R n) = 0 := by rw [ofRaw_eq_div, hzero, map_zero, div_zero]
    have hc : c = 0 := ofConst.injective (h.symm.trans (hx.trans (map_zero ofConst).symm))
    simp [constantCandidate, hd, hc]
  | cons a p =>
    rcases a with ⟨e,b⟩
    have hm := MPoly.Raw.coefficient_of_mem_normalize n x.den e b
      (by rw [hd]; exact List.mem_cons_self)
    have he := hm.1
    have hb := hm.2.1
    have heq : (MPoly.Raw.toMvPolynomial n x.den).coeff (e.exponents n) = b := hm.2.2
    have hden : MPoly.Raw.toMvPolynomial n x.den ≠ 0 := by
      intro hz
      rw [hz] at heq
      exact hb heq.symm
    induction c using Quotient.inductionOn with
    | _ y =>
      change (ofRaw x : K R n) = ofConst (ofRaw y) at h
      change x.constantCandidate n = ofRaw y
      rw [ofRaw_constants y, map_div₀, ofConst_C, ofConst_C] at h
      simp only [ofRaw_constants y, constantCandidate, hd, MPoly.Raw.readTerm_eq he]
      by_cases hy : y.den.constantTerm = 0
      · have hz : MPoly.Raw.toMvPolynomial n x.num = 0 := by
          have hv := congrArg equiv h
          simp only [equiv_ofRaw, Raw.value, Raw.polyValue, map_div₀, equiv_C, hy,
            map_zero, div_zero, div_eq_zero_iff] at hv
          have hiff (z : MvPolynomial (Fin n) R) : algebraMap _ (M R n) z = 0 ↔ z = 0 :=
            map_eq_zero_iff (algebraMap (MvPolynomial (Fin n) R) (M R n))
              (IsFractionRing.injective _ _)
          exact (hiff _).mp (hv.resolve_right fun hz => hden ((hiff _).mp hz))
        simp [hz, hy, show (K.C (0 : R) : K R 0) = 0 by rfl]
      · let f := algebraMap (MvPolynomial (Fin n) R) (M R n)
        have hf : Function.Injective f := IsFractionRing.injective _ _
        have hd' : f (MPoly.Raw.toMvPolynomial n x.den) ≠ 0 := (map_ne_zero_iff f hf).mpr hden
        have hy' : f (MvPolynomial.C y.den.constantTerm) ≠ 0 :=
          (map_ne_zero_iff f hf).mpr ((map_ne_zero_iff _ (MvPolynomial.C_injective _ _)).mpr hy)
        have hv := congrArg equiv h
        rw [equiv_ofRaw, map_div₀, equiv_C, equiv_C] at hv
        have hp : MPoly.Raw.toMvPolynomial n x.num * MvPolynomial.C y.den.constantTerm =
            MvPolynomial.C y.num.constantTerm * MPoly.Raw.toMvPolynomial n x.den := by
          apply hf
          simpa only [map_mul, f, Raw.polyValue] using (div_eq_div_iff hd' hy').mp hv
        have hc := congrArg (fun z : MvPolynomial (Fin n) R => z.coeff (e.exponents n)) hp
        rw [mul_comm _ (MvPolynomial.C _), MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
          heq] at hc
        apply equiv.injective
        simp only [map_div₀, equiv_C]
        let g := (algebraMap (MvPolynomial (Fin 0) R) (M R 0)).comp MvPolynomial.C
        have hg := (IsFractionRing.injective (MvPolynomial (Fin 0) R) (M R 0)).comp
          (MvPolynomial.C_injective (Fin 0) R)
        change g _ / g b = g _ / g y.den.constantTerm
        apply (div_eq_div_iff ((map_ne_zero_iff g hg).mpr hb) ((map_ne_zero_iff g hg).mpr hy)).mpr
        rw [← map_mul, ← map_mul, mul_comm _ y.den.constantTerm, hc]

/-- Recognize a constant by verifying its coefficient ratio in the full field. -/
def Raw.recognize (n : ℕ) (x : Raw R) : Option (K R 0) :=
  let c := x.constantCandidate n
  if ofRaw x = (ofConst c : K R n) then some c else none

theorem Raw.recognize_eq_some (x : Raw R) (c : K R 0) :
    x.recognize n = some c ↔ (ofRaw x : K R n) = ofConst c := by
  by_cases h : (ofRaw x : K R n) = ofConst c
  · simp [recognize, x.candidate_eq h, h]
  · simp only [recognize]
    split
    · rename_i hg
      constructor
      · intro hs
        exact Option.some.inj hs ▸ hg
      · exact False.elim ∘ h
    · simp [h]

/-- Return the unique element of the constant field represented by this fraction, if any. -/
def const? (x : K R n) : Option (K R 0) :=
  Quotient.lift (s := Raw.setoid R n) (Raw.recognize n) (fun a b h => by
    have he : (ofRaw a : K R n) = ofRaw b := Quotient.sound h
    exact Option.ext fun c => by rw [Raw.recognize_eq_some, Raw.recognize_eq_some, he]) x

/-- Constant recognition succeeds exactly on the embedded copy of the constants. -/
theorem const?_eq_some (x : K R n) (c : K R 0) : const? x = some c ↔ x = ofConst c :=
  Quotient.inductionOn x fun a => Raw.recognize_eq_some a c

@[simp] theorem const?_ofConst (c : K R 0) : const? (ofConst c : K R n) = some c :=
  (const?_eq_some _ c).mpr rfl

end K

end SympyProofs.Calculus.Antiderivative
