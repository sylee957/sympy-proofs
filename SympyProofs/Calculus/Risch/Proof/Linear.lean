module

public import SympyProofs.Calculus.Risch.Program.Linear
public import SympyProofs.Calculus.Risch.Spec.Linear
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.List.GetD
import Mathlib.Data.Int.Cast.Field
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The specification of the linear algebra programs. The rows of a system are rational,
and the unknowns range over a field `k` of characteristic zero: the generators computed by
`kernel` span the solutions over `k`, `eliminate` removes one unknown, and `normalized`
finds a solution with first coordinate `1` exactly when one exists over `k`. -/

@[expose] public section

namespace SympyProofs.Calculus.Risch.Linear

variable {k : Type} [Field k] [CharZero k]

/-- A combination over `k` of rational vectors, coordinatewise. -/
def lsum (es : List k) (G : List (List ℚ)) (i : ℕ) : k :=
  (List.zipWith (fun (e : k) (g : List ℚ) => e * ((g.getD i 0 : ℚ) : k)) es G).sum

/-! ### Rows applied to vectors -/

theorem dotK_cast : ∀ (row x : List ℚ),
    dotK row (x.map fun (q : ℚ) => (q : k)) = ((dot row x : ℚ) : k)
  | [], x => by simp [dotK, dot]
  | a :: row, [] => by simp [dotK, dot]
  | a :: row, c :: x => by
    change (a : k) * (c : k) + dotK row (x.map fun (q : ℚ) => (q : k)) =
      ((a * c + dot row x : ℚ) : k)
    rw [dotK_cast row x]
    push_cast
    rfl

omit [CharZero k] in
theorem dotK_eq_sum : ∀ (x : List k) (row : List ℚ),
    dotK row x = ∑ i ∈ Finset.range x.length, ((row.getD i 0 : ℚ) : k) * x.getD i 0
  | [], row => by simp [dotK]
  | c :: x, [] => by simp [dotK]
  | c :: x, r :: row => by
    change (r : k) * c + dotK row x = _
    rw [dotK_eq_sum x row, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

omit [CharZero k] in
theorem dotK_append {r s : List ℚ} {c d : List k} (h : r.length = c.length) :
    dotK (r ++ s) (c ++ d) = dotK r c + dotK s d := by
  simp [dotK, List.zipWith_append h]

omit [CharZero k] in
theorem dotK_snoc (r : List ℚ) (α : List k) (c : k) :
    dotK r (α ++ [c]) = dotK r α + ((r.getD α.length 0 : ℚ) : k) * c := by
  rw [dotK_eq_sum, dotK_eq_sum, List.length_append, List.length_singleton,
    Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [List.getD_append _ _ _ _ (Finset.mem_range.mp hi)]
  · rw [List.getD_append_right _ _ _ _ le_rfl]
    simp

omit [CharZero k] in
theorem dotK_zero_row : ∀ (row : List ℚ) (p : List k), (∀ e ∈ row, e = 0) → dotK row p = 0
  | [], p, _ => by simp [dotK]
  | r :: row, [], _ => by simp [dotK]
  | r :: row, c :: p, h => by
    change (r : k) * c + dotK row p = 0
    rw [dotK_zero_row row p fun y hy => h y (List.mem_cons_of_mem _ hy),
      h r List.mem_cons_self]
    simp

omit [CharZero k] in
theorem getD_map_cast (g : List ℚ) (i : ℕ) :
    (g.map fun (q : ℚ) => (q : k)).getD i 0 = ((g.getD i 0 : ℚ) : k) := by
  by_cases hi : i < g.length
  · simp [List.getD, hi]
  · simp [List.getD, hi]

theorem getD_map_range (N : ℕ) (f : ℕ → ℚ) (i : ℕ) :
    ((List.range N).map f).getD i 0 = if i < N then f i else 0 := by
  by_cases hi : i < N
  · simp [List.getD, hi]
  · simp [List.getD, hi]

/-! ### Unit vectors -/

theorem length_unit : ∀ m i, (unit m i).length = m
  | 0, _ => rfl
  | m + 1, 0 => by simp [unit]
  | m + 1, i + 1 => by simp [unit, length_unit m i]

omit [CharZero k] in
theorem dotK_unit : ∀ (m i : ℕ) (v : List k), i < m → dotK (unit m i) v = v.getD i 0
  | 0, _, _, h => by omega
  | m + 1, 0, [], _ => by simp [unit, dotK]
  | m + 1, 0, c :: v, _ => by
    change ((1 : ℚ) : k) * c + dotK (List.replicate m 0) v = c
    rw [dotK_zero_row (List.replicate m 0) v fun e he => List.eq_of_mem_replicate he]
    simp
  | m + 1, i + 1, [], _ => by simp [unit, dotK]
  | m + 1, i + 1, c :: v, h => by
    change ((0 : ℚ) : k) * c + dotK (unit m i) v = v.getD i 0
    rw [dotK_unit m i v (by omega)]
    simp

theorem getD_unit : ∀ (m i j : ℕ), i < m → (unit m i).getD j 0 = if j = i then 1 else 0
  | 0, _, _, h => by omega
  | m + 1, 0, 0, _ => by simp [unit]
  | m + 1, 0, j + 1, _ => by
    simp only [unit, List.getD_cons_succ]
    by_cases hj : j < m
    · simp [List.getD, hj]
    · simp [List.getD, hj]
  | m + 1, i + 1, 0, _ => by simp [unit]
  | m + 1, i + 1, j + 1, h => by
    simp only [unit, List.getD_cons_succ, getD_unit m i j (by omega)]
    simp

/-! ### Vectors as functions -/

variable (k) in
/-- A rational vector as a function on indices with values in `k`, zero beyond its length. -/
def fn (v : List ℚ) : ℕ → k := fun i => ((v.getD i 0 : ℚ) : k)

/-- A vector over `k` as a function on indices, zero beyond its length. -/
def vec (x : List k) : ℕ → k := fun i => x.getD i 0

/-- The linear form of a row on the first `M` coordinates. -/
noncomputable def form (M : ℕ) (r : List ℚ) : (ℕ → k) →ₗ[k] k where
  toFun f := ∑ i ∈ Finset.range M, ((r.getD i 0 : ℚ) : k) * f i
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

omit [CharZero k] in
theorem dotK_eq_form {M : ℕ} (r : List ℚ) {x : List k} (hx : x.length = M) :
    dotK r x = form M r (vec x) := by
  rw [dotK_eq_sum, hx]
  rfl

theorem form_fn {M : ℕ} (r : List ℚ) {g : List ℚ} (hg : g.length = M) :
    form M r (fn k g) = ((dot r g : ℚ) : k) := by
  rw [← dotK_cast, dotK_eq_sum, List.length_map, hg]
  change ∑ i ∈ Finset.range M, ((r.getD i 0 : ℚ) : k) * ((g.getD i 0 : ℚ) : k) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [getD_map_cast]

/-! ### The span of the generators -/

variable (k) in
/-- The span over `k` of a list of rational vectors, as functions. -/
def span (G : List (List ℚ)) : Submodule k (ℕ → k) :=
  Submodule.span k (fn k '' {g | g ∈ G})

/-! ### Integer vectors -/

/-- An integer vector as a rational one. -/
def castV (g : List ℤ) : List ℚ := g.map fun (a : ℤ) => (a : ℚ)

theorem length_castV (g : List ℤ) : (castV g).length = g.length := List.length_map _

theorem getD_castV (g : List ℤ) (i : ℕ) : (castV g).getD i 0 = ((g.getD i 0 : ℤ) : ℚ) := by
  by_cases hi : i < g.length
  · simp [castV, List.getD, hi]
  · simp [castV, List.getD, hi]

theorem foldl_add_int (acc : ℤ) : ∀ l : List ℤ, l.foldl (· + ·) acc = acc + l.sum
  | [] => by simp
  | a :: l => by rw [List.foldl_cons, foldl_add_int (acc + a) l, List.sum_cons]; ring

theorem dotZ_cast : ∀ (r g : List ℤ), ((dotZ r g : ℤ) : ℚ) = dot (castV r) (castV g) := by
  intro r g
  rw [dotZ, foldl_add_int, zero_add]
  induction r generalizing g with
  | nil => simp [dot, castV]
  | cons a r ih =>
    cases g with
    | nil => simp [dot, castV]
    | cons b g =>
      have := ih g
      simp only [dot, castV, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at this ⊢
      push_cast at this ⊢
      rw [this]

theorem form_fn_castV {M : ℕ} (r : List ℤ) {g : List ℤ} (hg : g.length = M) :
    form M (castV r) (fn k (castV g)) = ((dotZ r g : ℤ) : k) := by
  rw [form_fn (castV r) (by rw [length_castV, hg]), ← dotZ_cast, Rat.cast_intCast]

theorem length_zipWith_comb {M : ℕ} {g w : List ℤ} (hg : g.length = M) (hw : w.length = M)
    (a b : ℤ) : (List.zipWith (fun x y => a * x - b * y) g w).length = M := by
  simp [hg, hw]

theorem fn_comb {M : ℕ} {g w : List ℤ} (hg : g.length = M) (hw : w.length = M) (a b : ℤ) :
    fn k (castV (List.zipWith (fun x y => a * x - b * y) g w)) =
      (a : k) • fn k (castV g) - (b : k) • fn k (castV w) := by
  funext i
  simp only [fn, getD_castV, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i < M
  · rw [List.getD_eq_getElem _ _ (by rw [length_zipWith_comb hg hw]; exact hi),
      List.getElem_zipWith, List.getD_eq_getElem _ _ (by omega),
      List.getD_eq_getElem _ _ (by omega)]
    push_cast
    ring
  · rw [List.getD_eq_default _ _ (by rw [length_zipWith_comb hg hw]; omega),
      List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    simp

/-- `smallZ` keeps the length and multiplies the vector by a nonzero rational. -/
theorem smallZ_spec (g : List ℤ) :
    (smallZ g).length = g.length ∧
      ∃ c : ℚ, c ≠ 0 ∧ ∀ i, (((smallZ g).getD i 0 : ℤ) : ℚ) = c * ((g.getD i 0 : ℤ) : ℚ) := by
  unfold smallZ
  dsimp only
  split_ifs with h1 h2 h3
  · exact ⟨rfl, 1, one_ne_zero, fun i => (one_mul _).symm⟩
  · exact ⟨rfl, 1, one_ne_zero, fun i => (one_mul _).symm⟩
  · refine ⟨List.length_map _, ((((g.foldl (fun acc a => Nat.gcd acc a.natAbs) 0 : ℕ) : ℤ) :
      ℚ))⁻¹, inv_ne_zero (Int.cast_ne_zero.mpr (by omega)), fun i => ?_⟩
    have dvd : ∀ a ∈ g, ((g.foldl (fun acc a => Nat.gcd acc a.natAbs) 0 : ℕ) : ℤ) ∣ a := by
      intro a ha
      have := List.all_eq_true.mp h3 a ha
      exact Int.dvd_of_emod_eq_zero (by simpa using this)
    by_cases hi : i < g.length
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi,
        Int.cast_div (dvd _ (List.getElem_mem hi)) (by rw [Int.cast_ne_zero]; omega)]
      ring
    · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
        List.getD_eq_default _ _ (by omega)]
      simp
  · exact ⟨rfl, 1, one_ne_zero, fun i => (one_mul _).symm⟩

theorem fn_smallZ (g : List ℤ) :
    ∃ c : k, c ≠ 0 ∧ fn k (castV (smallZ g)) = c • fn k (castV g) := by
  obtain ⟨-, c, c0, hc⟩ := smallZ_spec g
  refine ⟨(c : k), Rat.cast_ne_zero.mpr c0, ?_⟩
  funext i
  simp only [fn, getD_castV, Pi.smul_apply, smul_eq_mul, hc i, Rat.cast_mul]

/-- `intRow` keeps the length and multiplies the row by a nonzero rational. -/
theorem intRow_spec (r : List ℚ) :
    (intRow r).length = r.length ∧
      ∃ d : ℚ, d ≠ 0 ∧ ∀ i, (((intRow r).getD i 0 : ℤ) : ℚ) = d * r.getD i 0 := by
  unfold intRow
  split
  · rename_i h
    refine ⟨List.length_map _, 1, one_ne_zero, fun i => ?_⟩
    by_cases hi : i < r.length
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi, one_mul]
      have := List.all_eq_true.mp h _ (List.getElem_mem hi)
      exact (Rat.den_eq_one_iff _).mp (by simpa using this)
    · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
        List.getD_eq_default _ _ (by omega)]
      simp
  · have key : ∀ (l : List ℚ) (acc : ℕ), acc ≠ 0 →
        l.foldl (fun acc q => Nat.lcm acc q.den) acc ≠ 0 ∧
          ∀ q ∈ l, q.den ∣ l.foldl (fun acc q => Nat.lcm acc q.den) acc := by
      intro l
      induction l with
      | nil => intro acc h; exact ⟨h, by simp⟩
      | cons q l ih =>
        intro acc h
        obtain ⟨nz, dv⟩ := ih (Nat.lcm acc q.den) (Nat.lcm_ne_zero h q.den_nz)
        refine ⟨nz, fun q' hq' => ?_⟩
        rcases List.mem_cons.mp hq' with rfl | hq'
        · have mono : ∀ (l : List ℚ) (a : ℕ), a ∣ l.foldl (fun acc q => Nat.lcm acc q.den) a := by
            intro l
            induction l with
            | nil => intro a; simp
            | cons p l ih' =>
              intro a
              exact (Nat.dvd_lcm_left a p.den).trans (ih' _)
          exact (Nat.dvd_lcm_right acc q'.den).trans (mono l _)
        · exact dv q' hq'
    obtain ⟨nz, dv⟩ := key r 1 one_ne_zero
    refine ⟨List.length_map _, ((r.foldl (fun acc q => Nat.lcm acc q.den) 1 : ℕ) : ℚ),
      Nat.cast_ne_zero.mpr nz, fun i => ?_⟩
    by_cases hi : i < r.length
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi), List.getElem_map,
        List.getD_eq_getElem _ _ hi]
      have hd := dv _ (List.getElem_mem hi)
      rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hd (Nat.cast_ne_zero.mpr r[i].den_nz)]
      conv_rhs => rw [← Rat.num_div_den r[i]]
      ring
    · rw [List.getD_eq_default _ _ (by rw [List.length_map]; omega),
        List.getD_eq_default _ _ (by omega)]
      simp

theorem form_intRow {M : ℕ} (r : List ℚ) (f : ℕ → k) :
    form M (castV (intRow r)) f = 0 ↔ form M r f = 0 := by
  obtain ⟨-, d, d0, hd⟩ := intRow_spec r
  have : form M (castV (intRow r)) f = (d : k) * form M r f := by
    change ∑ i ∈ Finset.range M, (((castV (intRow r)).getD i 0 : ℚ) : k) * f i =
      (d : k) * ∑ i ∈ Finset.range M, ((r.getD i 0 : ℚ) : k) * f i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [getD_castV, hd i, Rat.cast_mul]
    ring
  rw [this, mul_eq_zero, or_iff_right (Rat.cast_ne_zero.mpr d0)]

/-- A step over the integers keeps the lengths, and cuts the span down to the solutions of
its equation. -/
theorem stepZ_spec {M : ℕ} (r : List ℤ) {G : List (List ℤ)} (hG : ∀ g ∈ G, g.length = M) :
    (∀ g ∈ stepZ r G, g.length = M) ∧
      span k ((stepZ r G).map castV) =
        span k (G.map castV) ⊓ LinearMap.ker (form (k := k) M (castV r)) := by
  rw [stepZ]
  cases hfind : G.find? (fun g => dotZ r g != 0) with
  | none =>
    refine ⟨hG, ?_⟩
    have all := List.find?_eq_none.mp hfind
    apply le_antisymm
    · refine le_inf le_rfl ?_
      apply Submodule.span_le.mpr
      rintro _ ⟨g', hg', rfl⟩
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      have zero : dotZ r g = 0 := by simpa using all g hg
      rw [SetLike.mem_coe, LinearMap.mem_ker, form_fn_castV r (hG g hg), zero, Int.cast_zero]
    · exact inf_le_left
  | some w =>
    have hw : w ∈ G := List.mem_of_find?_eq_some hfind
    have hc : dotZ r w ≠ 0 := by simpa using List.find?_some hfind
    have wl := hG w hw
    have cform : form M (castV r) (fn k (castV w)) ≠ 0 := by
      rw [form_fn_castV r wl]
      exact Int.cast_ne_zero.mpr hc
    refine ⟨?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [(smallZ_spec _).1, length_zipWith_comb (hG g' (List.mem_of_mem_erase hg')) wl]
    obtain ⟨T, hT⟩ : ∃ T : (ℕ → k) →ₗ[k] (ℕ → k), ∀ x,
        T x = form M (castV r) (fn k (castV w)) • x - form M (castV r) x • fn k (castV w) :=
      ⟨form M (castV r) (fn k (castV w)) • LinearMap.id -
        (form M (castV r)).smulRight (fn k (castV w)), fun x => by
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
            LinearMap.smulRight_apply]⟩
    have Tw : T (fn k (castV w)) = 0 := by rw [hT, sub_self]
    have Tker (y : ℕ → k) (hy : form M (castV r) y = 0) :
        T y = form M (castV r) (fn k (castV w)) • y := by
      rw [hT, hy, zero_smul, sub_zero]
    -- each new generator is a nonzero multiple of the image of an old one
    have each (g : List ℤ) (hg : g ∈ G.erase w) : ∃ c : k, c ≠ 0 ∧
        fn k (castV (smallZ (List.zipWith (fun a b => dotZ r w * a - dotZ r g * b) g w))) =
          c • T (fn k (castV g)) := by
      have gl := hG g (List.mem_of_mem_erase hg)
      obtain ⟨c, c0, hc⟩ := fn_smallZ (k := k)
        (List.zipWith (fun a b => dotZ r w * a - dotZ r g * b) g w)
      refine ⟨c, c0, ?_⟩
      rw [hc, fn_comb gl wl, hT, form_fn_castV r gl, form_fn_castV r wl]
    have S_eq : Submodule.span k (fn k '' {g | g ∈ ((G.erase w).map fun g =>
          smallZ (List.zipWith (fun a b => dotZ r w * a - dotZ r g * b) g w)).map castV}) =
        Submodule.span k (T '' (fn k '' {g | g ∈ (G.erase w).map castV})) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨v, hv, rfl⟩
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hu
        obtain ⟨c, -, hc⟩ := each g hg
        rw [SetLike.mem_coe, hc]
        exact Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨fn k (castV g), ⟨castV g, List.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩, rfl⟩)
      · apply Submodule.span_le.mpr
        rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hv
        obtain ⟨c, c0, hc⟩ := each g hg
        have : T (fn k (castV g)) = c⁻¹ • fn k (castV (smallZ
            (List.zipWith (fun a b => dotZ r w * a - dotZ r g * b) g w))) := by
          rw [hc, smul_smul, inv_mul_cancel₀ c0, one_smul]
        rw [SetLike.mem_coe, this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, List.mem_map.mpr
          ⟨_, List.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩, rfl⟩)
    have whole : fn k '' {g | g ∈ G.map castV} =
        insert (fn k (castV w)) (fn k '' {g | g ∈ (G.erase w).map castV}) := by
      have sets : {g | g ∈ G.map castV} = insert (castV w) {g | g ∈ (G.erase w).map castV} := by
        ext g
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff]
        rw [← List.mem_cons, ← List.map_cons, ((List.perm_cons_erase hw).map castV).mem_iff]
      rw [sets, Set.image_insert_eq]
    rw [span, S_eq, ← Submodule.map_span, span, whole]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have xin : x ∈ Submodule.span k (insert (fn k (castV w))
          (fn k '' {g | g ∈ (G.erase w).map castV})) :=
        Submodule.span_mono (Set.subset_insert _ _) hx
      refine ⟨?_, ?_⟩
      · rw [hT]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ xin)
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      · rw [SetLike.mem_coe, LinearMap.mem_ker, hT, map_sub, map_smul, map_smul, smul_eq_mul,
          smul_eq_mul, mul_comm, sub_self]
    · rintro y ⟨hy, hker⟩
      have mapped : T y ∈ Submodule.map T
          (Submodule.span k (insert (fn k (castV w))
            (fn k '' {g | g ∈ (G.erase w).map castV}))) := ⟨y, hy, rfl⟩
      rw [Submodule.map_span, Set.image_insert_eq, Tw, Submodule.span_insert_zero,
        ← Submodule.map_span, Tker y (LinearMap.mem_ker.mp hker)] at mapped
      have := Submodule.smul_mem _ (form M (castV r) (fn k (castV w)))⁻¹ mapped
      rwa [smul_smul, inv_mul_cancel₀ cform, one_smul] at this

theorem foldlZ_spec {M : ℕ} : ∀ (rows : List (List ℤ)) {G : List (List ℤ)},
    (∀ g ∈ G, g.length = M) →
    (∀ g ∈ rows.foldl (fun G r => stepZ r G) G, g.length = M) ∧
      ∀ f : ℕ → k, f ∈ span k ((rows.foldl (fun G r => stepZ r G) G).map castV) ↔
        f ∈ span k (G.map castV) ∧ ∀ r ∈ rows, form M (castV r) f = 0
  | [], G, hG => ⟨hG, fun f => by simp⟩
  | r :: rows, G, hG => by
    obtain ⟨len, eq⟩ := stepZ_spec (k := k) r hG
    obtain ⟨len', iff⟩ := foldlZ_spec rows len
    refine ⟨len', fun f => ?_⟩
    rw [List.foldl_cons, iff, eq, Submodule.mem_inf, LinearMap.mem_ker]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

theorem length_unitZ : ∀ m i, (unitZ m i).length = m
  | 0, _ => rfl
  | m + 1, 0 => by simp [unitZ]
  | m + 1, i + 1 => by simp [unitZ, length_unitZ m i]

theorem castV_unitZ : ∀ m i, castV (unitZ m i) = unit m i
  | 0, _ => rfl
  | m + 1, 0 => by simp [castV, unitZ, unit]
  | m + 1, i + 1 => by
    have := castV_unitZ m i
    simp only [castV] at this ⊢
    simp [unitZ, unit, this]

theorem length_of_mem_unitsZ {M : ℕ} : ∀ g ∈ (List.range M).map (unitZ M), g.length = M := by
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hg
  exact length_unitZ M i

theorem kernel_eq (rows : List (List ℚ)) (M : ℕ) :
    kernel rows M =
      ((rows.map intRow).foldl (fun G r => stepZ r G) ((List.range M).map (unitZ M))).map
        castV := rfl

/-- Every generator has the length of the system. -/
theorem length_of_mem_kernel (rows : List (List ℚ)) (M : ℕ) :
    ∀ g ∈ kernel rows M, g.length = M := by
  intro g hg
  rw [kernel_eq] at hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [length_castV]
  exact (foldlZ_spec (k := ℚ) (rows.map intRow) length_of_mem_unitsZ).1 g' hg'

/-- The span of the generators consists of the solutions, as functions. -/
theorem mem_span_kernel (rows : List (List ℚ)) (M : ℕ) (f : ℕ → k) :
    f ∈ span k (kernel rows M) ↔
      f ∈ span k ((List.range M).map (unit M)) ∧ ∀ r ∈ rows, form M r f = 0 := by
  rw [kernel_eq, (foldlZ_spec (k := k) (rows.map intRow) length_of_mem_unitsZ).2 f,
    List.map_map, show castV ∘ unitZ M = unit M from funext (castV_unitZ M)]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, form_intRow]

omit [CharZero k] in
theorem mem_span_unit {M : ℕ} {x : List k} (hx : x.length = M) :
    vec x ∈ span k ((List.range M).map (unit M)) := by
  have eq : vec x = ∑ i ∈ Finset.range M, x.getD i 0 • fn k (unit M i) := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, fn, vec]
    by_cases hj : j < M
    · rw [Finset.sum_eq_single j]
      · rw [getD_unit M j j hj]
        simp
      · intro i hi hne
        rw [getD_unit M i j (Finset.mem_range.mp hi), ite_eq_right (Ne.symm hne), Rat.cast_zero,
          mul_zero]
      · intro h
        exact (h (Finset.mem_range.mpr hj)).elim
    · rw [List.getD_eq_default _ _ (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      rw [getD_unit M i j (Finset.mem_range.mp hi),
        ite_eq_right (by have := Finset.mem_range.mp hi; omega), Rat.cast_zero, mul_zero]
  rw [eq]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨unit M i, List.mem_map.mpr ⟨i, List.mem_range.mpr
    (Finset.mem_range.mp hi), rfl⟩, rfl⟩

omit [CharZero k] in
theorem mem_span_iff : ∀ (G : List (List ℚ)) (f : ℕ → k),
    f ∈ span k G ↔ ∃ es : List k, es.length = G.length ∧ ∀ i, f i = lsum es G i
  | [], f => by
    have : span k [] = ⊥ := by simp [span]
    rw [this, Submodule.mem_bot]
    constructor
    · rintro rfl
      exact ⟨[], rfl, fun i => by simp [lsum]⟩
    · rintro ⟨es, -, h⟩
      funext i
      simpa [lsum] using h i
  | g :: G, f => by
    have split : span k (g :: G) = Submodule.span k {fn k g} ⊔ span k G := by
      rw [span, span, ← Submodule.span_union]
      congr 1
      ext h
      simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_cons, Set.singleton_union,
        Set.mem_insert_iff]
      constructor
      · rintro ⟨v, rfl | hv, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨v, hv, rfl⟩
      · rintro (rfl | ⟨v, hv, rfl⟩)
        · exact ⟨g, Or.inl rfl, rfl⟩
        · exact ⟨v, Or.inr hv, rfl⟩
    rw [split, Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      obtain ⟨es, el, eh⟩ := (mem_span_iff G b).mp hb
      refine ⟨c :: es, by simp [el], fun i => ?_⟩
      simp [lsum, fn, eh i]
    · rintro ⟨es, el, eh⟩
      cases es with
      | nil => simp at el
      | cons c es =>
        refine ⟨c • fn k g, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
          fun i => lsum es G i, (mem_span_iff G _).mpr ⟨es, by simpa using el, fun _ => rfl⟩, ?_⟩
        funext i
        simp [eh i, lsum, fn]

/-! ### The solution space -/

/-- The generators have the length of the system, and their combinations over `k` are
exactly the solutions over `k`. -/
theorem kernel_spec (rows : List (List ℚ)) (M : ℕ) :
    (∀ g ∈ kernel rows M, g.length = M) ∧
    ∀ x : List k, x.length = M → ((∀ row ∈ rows, dotK row x = 0) ↔
      ∃ es : List k, es.length = (kernel rows M).length ∧
        ∀ i, x.getD i 0 = lsum es (kernel rows M) i) := by
  refine ⟨length_of_mem_kernel rows M, fun x hx => ?_⟩
  change _ ↔ ∃ es : List k, es.length = (kernel rows M).length ∧
    ∀ i, vec x i = lsum es (kernel rows M) i
  rw [← mem_span_iff (kernel rows M) (vec x), mem_span_kernel]
  constructor
  · intro h
    exact ⟨mem_span_unit hx, fun r hr => by rw [← dotK_eq_form r hx]; exact h r hr⟩
  · rintro ⟨-, h⟩ r hr
    rw [dotK_eq_form r hx]
    exact h r hr

/-! ### Elimination of one unknown -/

theorem dotK_reduceRow {m : ℕ} (b c : ℚ) (r p : List ℚ) {α : List k} (hα : α.length = m) :
    dotK (reduceRow m b r c p) α = (b : k) * dotK r α - (c : k) * dotK p α := by
  rw [dotK_eq_sum, dotK_eq_sum, dotK_eq_sum, hα, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [reduceRow, getD_map_range, ite_eq_left (Finset.mem_range.mp hi)]
  push_cast
  ring

/-- The reduced system holds for the first `m` unknowns exactly when the original system
holds for some value of the unknown at position `m`. -/
theorem eliminate_spec {m : ℕ} (rows : List (List ℚ)) {α : List k} (hα : α.length = m) :
    (∀ r ∈ eliminate m rows, dotK r α = 0) ↔ ∃ c : k, ∀ r ∈ rows, dotK r (α ++ [c]) = 0 := by
  unfold eliminate
  cases h : rows.find? (fun r => r.getD m 0 != 0) with
  | none =>
    have all : ∀ r ∈ rows, r.getD m 0 = 0 := by
      intro r hr
      have := List.find?_eq_none.mp h r hr
      simpa using this
    constructor
    · intro H
      exact ⟨0, fun r hr => by
        rw [dotK_snoc, hα, all r hr, Rat.cast_zero, zero_mul, add_zero]
        exact H r hr⟩
    · rintro ⟨c, H⟩ r hr
      have := H r hr
      rwa [dotK_snoc, hα, all r hr, Rat.cast_zero, zero_mul, add_zero] at this
  | some p =>
    have pm : p ∈ rows := List.mem_of_find?_eq_some h
    have pb : p.getD m 0 ≠ 0 := by simpa using List.find?_some h
    have pk : ((p.getD m 0 : ℚ) : k) ≠ 0 := Rat.cast_ne_zero.mpr pb
    constructor
    · intro H
      refine ⟨-(dotK p α) / ((p.getD m 0 : ℚ) : k), fun r hr => ?_⟩
      have := H _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
      rw [dotK_reduceRow _ _ _ _ hα] at this
      rw [dotK_snoc, hα]
      field_simp
      linear_combination this
    · rintro ⟨c, H⟩ r' hr'
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
      rw [dotK_reduceRow _ _ _ _ hα]
      have e1 := H r hr
      have e2 := H p pm
      rw [dotK_snoc, hα] at e1 e2
      linear_combination ((p.getD m 0 : ℚ) : k) * e1 - ((r.getD m 0 : ℚ) : k) * e2

/-! ### A solution with first coordinate one -/

omit [CharZero k] in
theorem lsum_eq_zero {i : ℕ} : ∀ (es : List k) (G : List (List ℚ)),
    (∀ g ∈ G, g.getD i 0 = 0) → lsum es G i = 0
  | [], G, _ => by simp [lsum]
  | e :: es, [], _ => by simp [lsum]
  | e :: es, g :: G, h => by
    change e * ((g.getD i 0 : ℚ) : k) + lsum es G i = 0
    rw [lsum_eq_zero es G fun g hg => h g (List.mem_cons_of_mem _ hg), h g List.mem_cons_self]
    simp

/-- The vector returned by `normalized` is a rational solution with first coordinate `1`. -/
theorem normalized_sound {rows : List (List ℚ)} {M : ℕ} {x : List ℚ}
    (h : normalized rows M = some x) :
    x.length = M ∧ x.getD 0 0 = 1 ∧ ∀ row ∈ rows, dot row x = 0 := by
  unfold normalized at h
  cases hfind : (kernel rows M).find? (fun g => g.getD 0 0 != 0) with
  | none =>
    rw [hfind] at h
    cases h
  | some g =>
    rw [hfind] at h
    obtain rfl := Option.some.inj h
    have hg : g ∈ kernel rows M := List.mem_of_find?_eq_some hfind
    have g0 : g.getD 0 0 ≠ 0 := by simpa using List.find?_some hfind
    have xl : (g.map fun a => a / g.getD 0 0).length = M := by
      rw [List.length_map, length_of_mem_kernel rows M g hg]
    have scaled : fn ℚ (g.map fun a => a / g.getD 0 0) = (g.getD 0 0)⁻¹ • fn ℚ g := by
      funext i
      simp only [fn, Rat.cast_id, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i < g.length
      · simp [List.getD, hi, div_eq_inv_mul]
      · simp [List.getD, hi]
    refine ⟨xl, ?_, fun row hrow => ?_⟩
    · have := congrFun scaled 0
      simp only [fn, Rat.cast_id, Pi.smul_apply, smul_eq_mul] at this
      rw [this, inv_mul_cancel₀ g0]
    · have mem : fn ℚ (g.map fun a => a / g.getD 0 0) ∈ span ℚ (kernel rows M) := by
        rw [scaled]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hg, rfl⟩)
      have zero := ((mem_span_kernel rows M _).mp mem).2 row hrow
      rwa [form_fn row xl, Rat.cast_id] at zero

/-- If the system has a solution over `k` with first coordinate `1`, `normalized` finds a
rational one. -/
theorem normalized_complete {rows : List (List ℚ)} {M : ℕ}
    (h : ∃ x : List k, x.length = M ∧ x.getD 0 0 = 1 ∧ ∀ row ∈ rows, dotK row x = 0) :
    (normalized rows M).isSome := by
  obtain ⟨x, xl, x0, sol⟩ := h
  unfold normalized
  cases hfind : (kernel rows M).find? (fun g => g.getD 0 0 != 0) with
  | some g => rfl
  | none =>
    exfalso
    have all : ∀ g ∈ kernel rows M, g.getD 0 0 = 0 := by
      intro g hg
      have := List.find?_eq_none.mp hfind g hg
      simpa using this
    obtain ⟨es, -, comb⟩ := ((kernel_spec rows M).2 x xl).mp sol
    have := comb 0
    rw [x0, lsum_eq_zero es _ all] at this
    exact one_ne_zero this

end SympyProofs.Calculus.Risch.Linear
