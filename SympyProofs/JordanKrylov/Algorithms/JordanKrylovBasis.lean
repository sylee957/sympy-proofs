import SympyProofs.JordanKrylov.Algorithms.JordanKrylovElimination

/-! # Algorithm 2: Jordan–Krylov basis construction

`V ℓ` lists the input generators of rank `ℓ`. Lists provide a deterministic
choice order; the output is a finite set. Only layers `1, …, ℓbar` are processed.
The input contract from the paper is that these layers generate the full primary
kernel, `f` is monic irreducible, and `m` is its characteristic multiplicity.
These are correctness assumptions, not arguments needed by the computation.

The implementation uses pairs of vectors for stacked columns. Applying `A` to
both halves is multiplication by `diag(A,A)`; applying `f(A)` to only the lower
half is multiplication by `diag(I,f(A))`.
-/
namespace SympyProofs.JordanKrylov
open Polynomial Matrix

/-- Algorithm 2 in imperative form. The polynomial operations are supplied by
`PolynomialOperations K`. The definition is total even outside the input contract:
an empty top layer is skipped, and only strictly lower positive residual ranks
are queued. Correctness as a Jordan–Krylov basis requires a separate proof. -/
def computeJordanKrylovBasis (K : Type*) [Field K] [DecidableEq K]
    [PolynomialOperations K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X])
    (V : ℕ → List (Fin n → K)) (ℓbar m : ℕ) : Finset (Fin n → K) := Id.run do
  let F := PolynomialOperations.applyMatrix f A
  let d := f.natDegree
  let mut basis : ℕ → Finset (Fin n → K) := fun _ => ∅
  let mut pending : ℕ → List (PairedColumn K n) := fun _ => []
  -- Lines 2–4: form the paired generators of every positive rank.
  for ℓ in (List.range ℓbar).reverse.map Nat.succ do
    let mut layer := []
    for v in V ℓ do
      let mut top := v
      for _ in List.range (ℓ - 1) do
        top := F top
      layer := layer ++ [{ top := top, bottom := v }]
    pending := Function.update pending ℓ layer
  let mut D : Array (Fin n × PairedColumn K n) := #[]
  for ℓ in (List.range ℓbar).reverse.map Nat.succ do
    let mut layer := pending ℓ
    pending := Function.update pending ℓ []
    -- Lines 6–13: initialize from the first generator in the highest layer.
    if ℓ = ℓbar then
      if let v :: rest := layer then
        layer := rest
        basis := Function.update basis ℓ {v.bottom}
        if ℓ = m then
          return {v.bottom}
        let mut w := v
        for _ in List.range d do
          D := insertPairedColumn D w
          w := { top := A *ᵥ w.top, bottom := A *ᵥ w.bottom }
    -- Lines 14–24: each candidate is removed once. Residuals go to later layers.
    for v in layer do
      let r := reducePairedColumn D v
      if r.top ≠ 0 then
        basis := Function.update basis ℓ (insert r.bottom (basis ℓ))
        let mut w := r
        for _ in List.range d do
          D := insertPairedColumn D w
          w := { top := A *ᵥ w.top, bottom := A *ᵥ w.bottom }
      else if r.bottom ≠ 0 ∧ 1 < ℓ then
        -- Find the first power that kills the residual, bounded by ℓ - 1.
        let mut rank : ℕ := 0
        let mut terminal := r.bottom
        let mut w := r.bottom
        for j in List.range (ℓ - 1) do
          if rank = 0 then
            let next := F w
            if next = 0 then
              rank := j + 1
              terminal := w
            else
              w := next
        if 0 < rank then
          pending := Function.update pending rank
            (pending rank ++ [⟨terminal, r.bottom⟩])
    -- Lines 25–27: retain the top block, lower the rank of the bottom block.
    if 1 < ℓ then
      D := D.map (fun (i, w) => (i, ⟨w.top, F w.bottom⟩))
  let mut result := ∅
  for k in List.range ℓbar do
    result := result ∪ basis (k + 1)
  return result

end SympyProofs.JordanKrylov
