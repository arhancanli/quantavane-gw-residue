module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Definitions used by the proof

These are the four definitions of `Challenge.lean`, with the same imports and the same text, so
that the proof is about exactly the notions the statement uses (Comparator checks that the
declarations agree). See `Challenge.lean` for the mathematical account.
-/

namespace GwResidue

/-- `c` is a *good exact `r`-colouring of `[1, n]`* for rainbow 3-term and monochromatic `l`-term
arithmetic progressions: every colour `col : Fin r` occurs on `[1, n]`; no `x, x + d, x + 2d` in
`[1, n]` with `d ≥ 1` has three distinct colours; and no `x, x + d, …, x + (l - 1)d` in `[1, n]`
with `d ≥ 1` has all its terms of one colour. The colouring is a function on all of `ℕ`; its values
outside `[1, n]` play no role. -/
def IsGoodExactColouring (r l n : ℕ) (c : ℕ → Fin r) : Prop :=
  (∀ col : Fin r, ∃ x, 1 ≤ x ∧ x ≤ n ∧ c x = col) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ n →
    ¬ (c x ≠ c (x + d) ∧ c x ≠ c (x + 2 * d) ∧ c (x + d) ≠ c (x + 2 * d))) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x)

/-- `m` has the defining property of the Gallai–van der Waerden number `GW(r; 3, l)`
(Mao–Ozeki–Robertson–Wang, JCTA 2023, Def. 1.15): for every `n ≥ m`, every exact `r`-colouring of
`[1, n]` contains a rainbow 3-term AP or a monochromatic `l`-term AP, that is, no `[1, n]` with
`n ≥ m` has a good exact `r`-colouring. -/
def GWProperty (r l m : ℕ) : Prop :=
  ∀ n ≥ m, ∀ c : ℕ → Fin r, ¬ IsGoodExactColouring r l n c

/-- `GW(r; 3, l)`: the least `m` with `GWProperty r l m`. Lean's `sInf` of the empty set of natural
numbers is `0`; the Gallai–van der Waerden theorem says that the set is not empty, but it is not
formalised here, so `lt_GW` assumes that some `m` has the property. -/
noncomputable def GW (r l : ℕ) : ℕ := sInf {m | GWProperty r l m}

/-- The colouring of Theorem 1, with colours `Fin (s + 2)`. A point `x ≢ 1 (mod p)` gets the
residue colour `0` if `legendreSym p (x - 1) = 1` and `1` otherwise; the point `x = 1 + kp`
(`k < l`) of the zero class gets colour `2 + z k`. Points `x = 1 + kp` with `k ≥ l` lie outside
`[1, (l - 1)p + 1]`; they get a residue colour, which plays no role. -/
def gwColour (p : ℕ) [Fact p.Prime] (l s : ℕ) (z : Fin l → Fin s) (x : ℕ) : Fin (s + 2) :=
  if h : x % p = 1 ∧ (x - 1) / p < l then (z ⟨(x - 1) / p, h.2⟩).addNat 2
  else if legendreSym p ((x : ℤ) - 1) = 1 then 0 else 1

end GwResidue
