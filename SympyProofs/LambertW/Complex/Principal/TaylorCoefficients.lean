import SympyProofs.LambertW.Complex.Principal.Taylor

/-!
# Closed Taylor coefficients of the principal Lambert W branch

The proof substitutes `z = w exp(w)` into the Taylor expansion and multiplies
by `(1+w) exp(-n w)`. Taking the coefficient of degree `n` annihilates all
terms except the desired one. No general inversion formula is assumed.
-/

namespace LambertW.Complex

open Set Filter Topology

private theorem jet_id_mul (n : ℕ) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    iteratedDeriv (n + 1) (fun z => z * f z) 0 =
      (n + 1 : ℂ) * iteratedDeriv n f 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  simp only [iteratedDeriv_fun_id_zero, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp

private theorem jet_pow_mul_zero {n k : ℕ} (hk : n < k) {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) : iteratedDeriv n (fun z => z ^ k * f z) 0 = 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i ≠ k := by have := Finset.mem_range.mp hi; omega
  simp only [iteratedDeriv_fun_pow_zero, hik, ite_false, Nat.cast_zero, mul_zero, zero_mul]

private theorem jet_weighted_exp (n k : ℕ) (hk : k ≠ n) :
    iteratedDeriv n (fun z : ℂ => z ^ k * (1 + z) * Complex.exp (((k : ℂ) - n) * z)) 0 = 0 := by
  let F : ℂ → ℂ := fun z => z ^ k * Complex.exp (((k : ℂ) - n) * z)
  have hF : AnalyticAt ℂ F 0 := by dsimp [F]; fun_prop
  have he : (fun z => ((k : ℂ) - n) * (z ^ k * (1 + z) * Complex.exp (((k : ℂ) - n) * z))) =
      fun z => deriv (fun w => w * F w) z - (n + 1 : ℂ) * F z := by
    funext z
    have hd := ((hasDerivAt_id z).pow (k + 1)).mul
      ((Complex.hasDerivAt_exp (((k : ℂ) - n) * z)).comp z
        ((hasDerivAt_id z).const_mul ((k : ℂ) - n)))
    have hh : (fun w => w * F w) = fun w => w ^ (k + 1) * Complex.exp (((k : ℂ) - n) * w) := by
      funext w; dsimp [F]; ring
    simp only [Pi.pow_apply, Function.comp_def, id_eq] at hd
    have hd' : HasDerivAt (fun w : ℂ => w ^ (k + 1) * Complex.exp (((k : ℂ) - n) * w))
        ((k + 1 : ℂ) * z ^ k * Complex.exp (((k : ℂ) - n) * z) +
          z ^ (k + 1) * (Complex.exp (((k : ℂ) - n) * z) * ((k : ℂ) - n))) z := by
      convert hd using 1 <;> simp [Pi.pow_def, Pi.mul_def, id_eq]
    rw [hh, hd'.deriv]
    dsimp [F]
    rw [pow_succ]
    ring
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv n f 0) he
  rw [iteratedDeriv_const_mul_field] at hd
  rw [iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_const_mul_field, ← iteratedDeriv_succ', jet_id_mul n hF] at hd
  have hc : (k : ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hk)
  exact (mul_eq_zero.mp (hd.trans (sub_self _))).resolve_left hc

private theorem jet_weighted_diagonal (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => z ^ n * (1 + z) * Complex.exp (((n : ℂ) - n) * z)) 0 = n.factorial := by
  have he : (fun z : ℂ => z ^ n * (1 + z) * Complex.exp (((n : ℂ) - n) * z)) =
      fun z => z ^ n + z ^ (n + 1) := by
    funext z; simp only [sub_self, zero_mul, Complex.exp_zero, mul_one]; ring
  rw [he, iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_fun_pow_zero]
  simp

private theorem jet_weighted_linear (n : ℕ) :
    iteratedDeriv (n + 1) (fun z : ℂ => z * (1 + z) * Complex.exp (-((n + 1 : ℕ) : ℂ) * z)) 0 =
      (-((n + 1 : ℕ) : ℂ)) ^ n := by
  have he : (fun z : ℂ => z * (1 + z) * Complex.exp (-((n + 1 : ℕ) : ℂ) * z)) =
      fun z => z * (Complex.exp (-((n + 1 : ℕ) : ℂ) * z) + z * Complex.exp (-((n + 1 : ℕ) : ℂ) * z)) := by
    funext z; ring
  rw [he, jet_id_mul n (by fun_prop), iteratedDeriv_fun_add (by fun_prop) (by fun_prop)]
  cases n with
  | zero => simp [iteratedDeriv_zero]
  | succ n =>
    rw [jet_id_mul n (by fun_prop)]
    simp only [iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero, mul_one]
    push_cast
    rw [pow_succ]
    ring

/-- Closed derivatives at the origin: `W^(n+1)(0) = (-(n+1))^n`. -/
theorem iteratedDeriv_principal_zero_closed (n : ℕ) :
    iteratedDeriv (n + 1) principal 0 = (-((n + 1 : ℕ) : ℂ)) ^ n := by
  let N := n + 1
  let c : ℕ → ℂ := fun k => iteratedDeriv k principal 0 / (k.factorial : ℂ)
  let weight : ℂ → ℂ := fun w => (1 + w) * Complex.exp (-(N : ℂ) * w)
  let term : ℕ → ℂ → ℂ := fun k w => w ^ k * (1 + w) * Complex.exp (((k : ℂ) - N) * w)
  obtain ⟨R, hR, hTaylor⟩ :=
    (analyticAt_principal zero_mem_principalDomain).exists_eventuallyEq_sum_add_pow_mul (N + 1)
  let S : ℂ → ℂ := fun w => Complex.exp w ^ (N + 1) * R (mulExp w) * weight w
  have hS : AnalyticAt ℂ S 0 := by
    have hRc : AnalyticAt ℂ (fun w => R (mulExp w)) 0 := by
      exact (show AnalyticAt ℂ R (mulExp 0) by simpa using hR).comp (analyticAt_mulExp 0)
    dsimp [S, weight]
    exact ((analyticAt_cexp.pow _).mul hRc).mul (by fun_prop)
  have hterm (k : ℕ) (w : ℂ) : mulExp w ^ k * weight w = term k w := by
    dsimp [mulExp, weight, term]
    rw [mul_pow, ← Complex.exp_nat_mul]
    have he : Complex.exp ((k : ℂ) * w) * Complex.exp (-(N : ℂ) * w) =
        Complex.exp (((k : ℂ) - N) * w) := by
      rw [← Complex.exp_add]; congr 1; ring
    calc
      _ = w ^ k * (1 + w) * (Complex.exp ((k : ℂ) * w) * Complex.exp (-(N : ℂ) * w)) := by ring
      _ = _ := by rw [he]
  have hsub : ∀ᶠ w in 𝓝 (0 : ℂ),
      w * weight w = (∑ k ∈ Finset.range (N + 1), c k * term k w) + w ^ (N + 1) * S w := by
    have ht := (show Tendsto mulExp (𝓝 (0 : ℂ)) (𝓝 0) by
      simpa using (analyticAt_mulExp 0).continuousAt.tendsto).eventually hTaylor
    filter_upwards [ht, isOpen_principalRange.mem_nhds zero_mem_principalRange] with w ht hw
    rw [principal_mulExp hw] at ht
    have h := congrArg (fun z : ℂ => z * weight w) ht
    simp only [add_mul, Finset.sum_mul, smul_eq_mul] at h
    rw [h]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      dsimp [c]
      rw [show (mulExp w ^ k / (k.factorial : ℂ) * iteratedDeriv k principal 0) * weight w =
          (iteratedDeriv k principal 0 / (k.factorial : ℂ)) * (mulExp w ^ k * weight w) by ring,
        hterm]
    · dsimp [S, mulExp]
      rw [mul_pow]
      ring
  have hd := Filter.EventuallyEq.iteratedDeriv_eq N hsub
  have ht (k : ℕ) : AnalyticAt ℂ (fun w => c k * term k w) 0 := by dsimp [term]; fun_prop
  have hsum : AnalyticAt ℂ (fun w => ∑ k ∈ Finset.range (N + 1), c k * term k w) 0 :=
    Finset.analyticAt_fun_sum _ (fun k _ => ht k)
  have hrem : AnalyticAt ℂ (fun w : ℂ => w ^ (N + 1) * S w) 0 :=
    (analyticAt_id.pow _).fun_mul hS
  rw [iteratedDeriv_fun_add (f := fun w => ∑ k ∈ Finset.range (N + 1), c k * term k w)
      (g := fun w => w ^ (N + 1) * S w) hsum.contDiffAt hrem.contDiffAt,
    jet_pow_mul_zero (Nat.lt_succ_self N) hS, add_zero,
    iteratedDeriv_fun_sum (fun k _ => (ht k).contDiffAt)] at hd
  simp only [iteratedDeriv_const_mul_field] at hd
  rw [Finset.sum_eq_single N] at hd
  · have hdiag := jet_weighted_diagonal N
    change iteratedDeriv N (term N) 0 = (N.factorial : ℂ) at hdiag
    rw [hdiag] at hd
    have hfact : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    dsimp [c] at hd
    rw [div_mul_cancel₀ _ hfact] at hd
    rw [← hd]
    simpa only [N, weight, mul_assoc] using jet_weighted_linear n
  · intro k hk hkn
    have hzero := jet_weighted_exp N k hkn
    change iteratedDeriv N (term k) 0 = 0 at hzero
    rw [hzero, mul_zero]
  · simp

/-- The classical convergent series `∑ (-(n+1))^n z^(n+1) / (n+1)!`. -/
theorem hasSum_principal_taylor_closed {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (-((n + 1 : ℕ) : ℂ)) ^ n / ((n + 1).factorial : ℂ) * z ^ (n + 1))
      (principal z) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_principal_taylor hz)
  simpa [iteratedDeriv_principal_zero_closed, iteratedDeriv_zero, div_eq_mul_inv, mul_comm,
    mul_left_comm, mul_assoc] using h

end LambertW.Complex
