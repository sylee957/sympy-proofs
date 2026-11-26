module

public import SympyProofs.Calculus.Antiderivative.Program.TrigonometricDescent.Polynomials
public import SympyProofs.Calculus.Antiderivative.Proof.Step.Residue

/-! The descended moduli partition the two conjugate sets of residue roots. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric.Descent

open Polynomial

variable {F k : Type} [Field F] [DecidableEq F] [Field k] [CharZero k]

private theorem shared_iff {a b j : k} (hj : j^2 = -1) :
    a = 0 ∧ b = 0 ↔ a + j*b = 0 ∧ a - j*b = 0 := by
  have h : j ≠ 0 := by rintro rfl; simp at hj
  constructor
  · rintro ⟨rfl,rfl⟩; simp
  · rintro ⟨h₁,h₂⟩
    have ha : a = 0 := by linear_combination (h₁+h₂)/2
    refine ⟨ha,? _⟩
    simpa [ha, h] using h₁

/-- The common modulus has the roots belonging to both embeddings. -/
theorem common_roots (f : F →+* k) (p q : Poly F) (j : k) (hj : j^2 = -1) (z : k) :
    let e := Step.atRoot f z
    e (moduli p q).1 = 0 ↔ e p + j*e q = 0 ∧ e p - j*e q = 0 :=
  (Step.map_gcd_eq_zero_iff _ p q).trans (shared_iff hj)

private theorem radical_root (f : F →+* k) (p q : Poly F) (j : k) (hj : j^2 = -1) (z : k) :
    let e := Step.atRoot f z
    e (Step.squarefreeParts (p^2 + q^2)).1 = 0 ↔ e p + j*e q = 0 ∨ e p - j*e q = 0 := by
  let e := Step.atRoot f z
  apply (Step.squarefreePart_roots f (p^2+q^2) z).trans
  change e (p^2+q^2) = 0 ↔ _
  rw [map_add, map_pow, map_pow, ← mul_eq_zero]
  have he : e p ^ 2 + e q ^ 2 = (e p+j*e q)*(e p-j*e q) := by
    linear_combination (e q)^2*hj
  exact he ▸ Iff.rfl

omit [CharZero k] in
private theorem model_ne_zero (f : F →+* k) {p : Poly F} (hp : p ≠ 0) :
    Step.modelPoly f p ≠ 0 :=
  (map_ne_zero_iff _ ((Polynomial.map_injective _ f.injective).comp Poly.equiv.injective)).mpr hp

omit [CharZero k] in
/-- For a nonzero norm both output moduli are nonzero. -/
theorem moduli_ne_zero (f : F →+* k) {p q : Poly F} (hn : p^2+q^2 ≠ 0) :
    Step.modelPoly f (moduli p q).1 ≠ 0 ∧ Step.modelPoly f (moduli p q).2 ≠ 0 := by
  let u := (Step.squarefreeParts (p^2+q^2)).1
  let g := gcd p q
  have hu : u ≠ 0 := by
    intro hu
    have hh := Step.squarefreeParts_mul hn
    change _ * u = _ at hh
    exact hn (by simpa [hu] using hh.symm)
  have hg : g ≠ 0 := by
    intro hg
    have hd := ((gcd_eq_zero_iff _ _).mp hg)
    simp [hd.1,hd.2] at hn
  have hf := EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_left hu (a := u) (b := g))
    (gcd_dvd_left u g)
  refine ⟨model_ne_zero f hg, model_ne_zero f ?_⟩
  change u / gcd u g ≠ 0
  intro hz
  exact hu (by simpa [hz] using hf.symm)

/-- The exclusive modulus has the roots belonging to precisely one embedding. -/
theorem exclusive_roots (f : F →+* k) (p q : Poly F) (hn : p^2+q^2 ≠ 0)
    (j : k) (hj : j^2 = -1) (z : k) :
    let e := Step.atRoot f z
    e (moduli p q).2 = 0 ↔ (e p + j*e q = 0 ∨ e p - j*e q = 0) ∧
      ¬(e p + j*e q = 0 ∧ e p - j*e q = 0) := by
  let e := Step.atRoot f z
  let u := (Step.squarefreeParts (p^2+q^2)).1
  let g := gcd p q
  let h := gcd u g
  let v := u / h
  have hs := Step.squarefreePart_squarefree f hn
  have hu : u ≠ 0 := by
    rintro hz
    exact hs.ne_zero (by change Step.modelPoly f u = 0; rw [hz,map_zero])
  have hh : h ≠ 0 := gcd_ne_zero_of_left hu
  have hf : h*v = u := EuclideanDomain.mul_div_cancel' hh (gcd_dvd_left u g)
  have rel := congrArg (Step.modelPoly f) hf
  rw [map_mul] at rel
  have hc := IsRelPrime.of_squarefree_mul (rel.symm ▸ hs)
  have non (h₁ : e h = 0) (h₂ : e v = 0) := (irreducible_X_sub_C z).not_isUnit
    (hc (dvd_iff_isRoot.mpr h₁) (dvd_iff_isRoot.mpr h₂))
  have prod : e u = e h * e v := by rw [← hf,map_mul]
  have both : e h = 0 ↔ e u = 0 ∧ e g = 0 := Step.map_gcd_eq_zero_iff _ _ _
  have allr : e u = 0 ↔ _ := radical_root f p q j hj z
  have common : e g = 0 ↔ _ := common_roots f p q j hj z
  change e v = 0 ↔ _
  rw [← allr, ← common]
  constructor
  · intro hv
    have hz : e u = 0 := by rw [prod,hv,mul_zero]
    exact ⟨hz,fun hg => non (both.mpr ⟨hz,hg⟩) hv⟩
  · rintro ⟨hz,hg⟩
    rw [prod,mul_eq_zero] at hz
    exact hz.resolve_left fun hh => hg (both.mp hh).2

end SympyProofs.Calculus.Antiderivative.Trigonometric.Descent
