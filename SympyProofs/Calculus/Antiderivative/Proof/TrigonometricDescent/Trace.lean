module

public import SympyProofs.Calculus.Antiderivative.Proof.TrigonometricDescent.Moduli
public import SympyProofs.Calculus.Antiderivative.Spec.Derivation

/-! Pairing the logarithmic contributions at common and exclusive residue roots. -/

@[expose] public section

namespace SympyProofs.Calculus.Antiderivative.Trigonometric.Descent

variable {k V : Type} [Field k] [Field V]
variable (C : k →+* V) (D : Model.Der V) (hC : ∀ x, D (C x) = 0)

private theorem ld_mul {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) :
    D (a*b)/(a*b) = D a/a + D b/b := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  field_simp
  ring

include hC in
private theorem ld_const {u : V} (hu : u ≠ 0) {a : k} (ha : a ≠ 0) :
    D (C a*u)/(C a*u) = D u/u := by
  rw [ld_mul D ((map_ne_zero_iff _ C.injective).mpr ha) hu,hC,zero_div,zero_add]

/-- At a common root, the product argument adds the two logarithmic derivatives. -/
theorem shared_log {j : k} (hj : j^2 = -1) (a b : V)
    (hp : a+C j*b ≠ 0) (hm : a-C j*b ≠ 0) :
    a^2+b^2 ≠ 0 ∧ D (a^2+b^2)/(a^2+b^2) =
      D (a+C j*b)/(a+C j*b) + D (a-C j*b)/(a-C j*b) := by
  have hj' : (C j)^2 = -1 := by rw [← map_pow,hj,map_neg,map_one]
  have H : a^2+b^2 = (a+C j*b)*(a-C j*b) := by linear_combination b^2*hj'
  rw [H]
  exact ⟨mul_ne_zero hp hm,ld_mul D hp hm⟩

private theorem exclusive_value {j p q : k} (hj : j^2 = -1)
    (hp : p+j*q = 0) (hm : p-j*q ≠ 0) (a b : V) :
    p ≠ 0 ∧ C p*a+C q*b = C p*(a+C j*b) := by
  have hn : p ≠ 0 := by rintro rfl; simp_all
  have eq : p*j = q := by linear_combination j*hp-q*hj
  exact ⟨hn,by rw [mul_add,← mul_assoc,← map_mul,eq]⟩

include hC in
/-- At an exclusive root, the descended argument differs from its contributing signed
argument by a nonzero scalar. -/
theorem exclusive_log {j p q : k} (hj : j^2 = -1) (a b : V)
    (hp : p+j*q = 0) (hm : p-j*q ≠ 0) (hn : a+C j*b ≠ 0) :
    C p*a+C q*b ≠ 0 ∧ D (C p*a+C q*b)/(C p*a+C q*b) = D (a+C j*b)/(a+C j*b) := by
  obtain ⟨h₁,h₂⟩ := exclusive_value C hj hp hm a b
  rw [h₂]
  exact ⟨mul_ne_zero ((map_ne_zero_iff _ C.injective).mpr h₁) hn,ld_const C D hC hn h₁⟩

include hC in
theorem exclusive_log_neg {j p q : k} (hj : j^2 = -1) (a b : V)
    (hm : p-j*q = 0) (hp : p+j*q ≠ 0) (hn : a-C j*b ≠ 0) :
    C p*a+C q*b ≠ 0 ∧ D (C p*a+C q*b)/(C p*a+C q*b) = D (a-C j*b)/(a-C j*b) := by
  simpa [sub_eq_add_neg] using exclusive_log C D hC (j := -j) (p := p) (q := q)
    (by simpa using hj) a b (by simpa [sub_eq_add_neg] using hm)
    (by simpa using hp) (by simpa [sub_eq_add_neg] using hn)

section Sums

variable {α W : Type} [DecidableEq α] [AddCommMonoid W]

private theorem sum_on_union {s u : Finset α} (hs : s ⊆ u) (f : α → W) :
    ∑ z ∈ s, f z = ∑ z ∈ u, if z ∈ s then f z else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext z
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨hs h,h⟩,And.right⟩

/-- A pair of finite sums is partitioned into the shared indices and the indices appearing
on precisely one side. -/
theorem sum_pair {p q shared single : Finset α}
    (h₁ : ∀ z, z ∈ shared ↔ z ∈ p ∧ z ∈ q)
    (h₂ : ∀ z, z ∈ single ↔ (z ∈ p ∨ z ∈ q) ∧ ¬ (z ∈ p ∧ z ∈ q))
    (a b c d : α → W) (hs : ∀ z ∈ p, z ∈ q → c z = a z+b z)
    (hp : ∀ z ∈ p, z ∉ q → d z = a z) (hm : ∀ z ∈ q, z ∉ p → d z = b z) :
    (∑ z ∈ shared, c z) + ∑ z ∈ single, d z = (∑ z ∈ p, a z) + ∑ z ∈ q, b z := by
  let u := p ∪ q
  have sc : shared ⊆ u := fun z hz => Finset.mem_union_left _ ((h₁ z).mp hz).1
  have sd : single ⊆ u := fun z hz => Finset.mem_union.mpr ((h₂ z).mp hz).1
  rw [sum_on_union sc,sum_on_union sd,
    sum_on_union (Finset.subset_union_left (s₁ := p) (s₂ := q)),
    sum_on_union (Finset.subset_union_right (s₁ := p) (s₂ := q)),← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hP : z ∈ p <;> by_cases hQ : z ∈ q <;> simp [h₁,h₂,hP,hQ,hs,hp,hm]

end Sums

end SympyProofs.Calculus.Antiderivative.Trigonometric.Descent
