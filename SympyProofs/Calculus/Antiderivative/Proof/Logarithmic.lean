module

public import SympyProofs.Calculus.Antiderivative.Spec.Logarithmic
public import SympyProofs.Calculus.Antiderivative.Proof.BaseLevel
import Mathlib.Tactic.FieldSimp

/-! Rational logarithmic relations at the base, and their use in exact admissibility and
in bounding every exponent in an admissible tower step. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] [NormalizedGCDMonoid R] [Div R]
variable (k : Type) [Field k] [Algebra R k] [FaithfulSMul R k] {n : ℕ}

@[simp] theorem satisfiesRows_iff (q : List ℚ) (rs : List (List ℚ)) :
    satisfiesRows q rs = true ↔ ∀ r ∈ rs, Linear.dot q r = 0 := by simp [satisfiesRows]

/-- The logarithmic derivative of any base-field element is zero. -/
theorem baseLevel_logRelations_spec [CharZero k] [IntegerRelations (K R 0)]
    [LawfulIntegerRelations (K R 0)] : (baseLevel R).LogRelationsSpec k .base := by
  intro w q _
  change (∀ r ∈ IntegerRelations.rows w, Linear.dot q r = 0) ↔ _
  rw [LawfulIntegerRelations.kernel]
  constructor
  · intro hz
    exact ⟨1, 1, Nat.one_pos, one_ne_zero, by simp [hz]⟩
  · rintro ⟨m,y,hm,_,h⟩
    have h' : (m : M k 0) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
    apply (val k).injective
    simpa [h', eq_comm] using h

/-- The single-column integer relation test decides precisely the exponential condition. -/
theorem Level.expOk_iff (t : Tower R n) (L : Level R n) (hs : L.LogRelationsSpec k t)
    (u : K R n) : L.expOk t.D u = true ↔ (ReducedGen.exp u).Admissible k t := by
  have h := hs [t.D u] [1] rfl
  simpa [Level.expOk, Bool.not_eq_true', ← Bool.not_eq_true, ReducedGen.Admissible,
    Tower.SaturatedLog,
    rationalCombination, satisfiesRows_iff] using not_congr h

private theorem dot_pair (a b : ℚ) (r : List ℚ) :
    Linear.dot [a,b] r = a * r.getD 0 0 + b * r.getD 1 0 := by
  cases r with
  | nil => simp [Linear.dot]
  | cons u us => cases us <;> simp [Linear.dot]

/-- The rational kernel bounds an integral second coordinate whenever it excludes the
vertical direction. -/
theorem le_exponentBound {rs : List (List ℚ)} {m : ℕ}
    (hm : ∀ r ∈ rs, Linear.dot [1, (m : ℚ)] r = 0)
    (hv : ¬ ∀ r ∈ rs, Linear.dot [0, 1] r = 0) : m ≤ exponentBound rs := by
  simp only [dot_pair, zero_mul, one_mul, zero_add] at hv
  unfold exponentBound
  generalize he : rs.find? (fun r => r.getD 1 0 != 0) = o
  cases o with
  | none => exact False.elim (hv (by simpa using List.find?_eq_none.mp he))
  | some r =>
    have hr := List.mem_of_find?_eq_some he
    have hd : r.getD 1 0 ≠ 0 := by simpa using List.find?_some he
    have heq := hm r hr
    rw [dot_pair, one_mul, add_eq_zero_iff_neg_eq] at heq
    have e : -(r.getD 0 0) / r.getD 1 0 = (m : ℚ) := (div_eq_iff hd).mpr heq
    change m ≤ Rational.natBound (-(r.getD 0 0) / r.getD 1 0)
    rw [e]
    simp [Rational.natBound]

/-- If an exponential is admissible, the degree bound includes all natural exponents
for which adding that multiple of its velocity gives a logarithmic derivative. -/
theorem Level.exponentBound_spec (t : Tower R n) (L : Level R n) (hs : L.LogRelationsSpec k t)
    (u g : K R n) (hu : (ReducedGen.exp u).Admissible k t) (m : ℕ)
    (hm : t.SaturatedLog k (val k (g + (m : K R n) * t.D u))) :
    m ≤ exponentBound (L.logRelations [g, t.D u]) := by
  apply le_exponentBound
  · apply (hs _ [1, (m : ℚ)] rfl).mpr
    simpa [rationalCombination] using hm
  · intro hv
    apply hu
    have hv' := (hs _ [0, 1] rfl).mp hv
    simpa [rationalCombination, Tower.SaturatedLog] using hv'

end SympyProofs.Calculus.Antiderivative
