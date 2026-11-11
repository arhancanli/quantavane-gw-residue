module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Gallai–van der Waerden numbers from quadratic-residue colourings: the statement

This file is the statement of record. It imports only Mathlib, defines the four notions the
statements use, and states the results with `sorry`. `Solution.lean` proves every statement;
`comparator.json` names the compared theorems. The four definitions below must agree exactly with
the ones the proof uses (Comparator checks this), so they are spelled out here in full.

## Gallai–van der Waerden numbers

Write `[1, n] = {1, …, n}`. An *exact `r`-colouring* of `[1, n]` is a colouring of `[1, n]` with
`r` colours in which every colour occurs. An arithmetic progression (AP) always has common
difference `d ≥ 1`. A 3-term AP `x, x + d, x + 2d` is *rainbow* when its three terms have three
distinct colours, and an `l`-term AP `x, x + d, …, x + (l - 1)d` is *monochromatic* when all its
terms have the same colour. The Gallai–van der Waerden number `GW(r; 3, l)` of Mao, Ozeki, Robertson
and Wang (J. Combin. Theory Ser. A, 2023, Definition 1.15, case `k = 3`) is the least `m` such that,
for every `n ≥ m`, every exact `r`-colouring of `[1, n]` contains a rainbow 3-term AP or a
monochromatic `l`-term AP.

* `IsGoodExactColouring r l n c`: `c` is an exact `r`-colouring of `[1, n]` with no rainbow 3-term
  AP and no monochromatic `l`-term AP in `[1, n]`.
* `GWProperty r l m`: no `[1, n]` with `n ≥ m` has such a colouring. `GW(r; 3, l)` is the least `m`
  with this property.
* `GW r l`: that least `m`, as `sInf`.
* `gwColour p l s z`: the colouring of Theorem 1.

## Theorem 1

Let `l ≥ 4` and let `p > l` be a prime with `p ≡ 1 (mod 8)` such that no `l` consecutive integers
`a, a + 1, …, a + l - 1` in `[1, p - 1]` all have the same Legendre symbol modulo `p`. Let `s ≥ 2`
and let `z : {0, …, l - 1} → {0, …, s - 1}` be surjective with no rainbow 3-term AP. Put
`N = (l - 1)p + 1` and colour `x ∈ [1, N]` with the `s + 2` colours `0, 1, …, s + 1`:

* if `x ≢ 1 (mod p)`: colour `0` when the Legendre symbol `(x - 1 | p)` is `1`, colour `1`
  otherwise;
* if `x = 1 + kp` with `0 ≤ k ≤ l - 1`: colour `2 + z(k)`.

Then (a) all `s + 2` colours occur on `[1, N]`, (b) no 3-term AP in `[1, N]` is rainbow, and
(c) no `l`-term AP in `[1, N]` is monochromatic. Hence `[1, N]` has a good exact
`(s + 2)`-colouring, and `GW(s + 2; 3, l) > (l - 1)p + 1`.

The hypotheses can be met: `(l, p) = (4, 17)` satisfies them, and with `z = 0, 1, 1, 0`
(`s = 2`) or `z = 0, 1, 1, 2` (`s = 3`) Theorem 1 gives `GW(4; 3, 4) > 52` and `GW(5; 3, 4) > 52`.
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

/-- **Theorem 1.** Let `l ≥ 4` and let `p > l` be a prime with `p ≡ 1 (mod 8)` such that no `l`
consecutive integers `a, …, a + l - 1` with `1 ≤ a` and `a + l - 1 ≤ p - 1` all have the same
Legendre symbol modulo `p` (`hrun`). Let `s ≥ 2` and let `z : Fin l → Fin s` be surjective with no
rainbow 3-term AP `i < j < k`, `i + k = 2j` (`hz3`). Put `N = (l - 1)p + 1` and `c = gwColour p l s z`.
Then (a) every one of the `s + 2` colours occurs on `[1, N]`; (b) no `x, x + d, x + 2d` in `[1, N]`
with `d ≥ 1` has three distinct colours; (c) no `x, x + d, …, x + (l - 1)d` in `[1, N]` with
`d ≥ 1` has all its terms of one colour. -/
theorem theorem1 (l p s : ℕ) [Fact p.Prime] (hl : 4 ≤ l) (hp8 : p % 8 = 1) (hlp : l < p)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hs : 2 ≤ s) (z : Fin l → Fin s) (hz : Function.Surjective z)
    (hz3 : ∀ i j k : Fin l, i < j → j < k → (i : ℕ) + k = 2 * j →
      ¬ (z i ≠ z j ∧ z i ≠ z k ∧ z j ≠ z k)) :
    let N := (l - 1) * p + 1
    let c := gwColour p l s z
    (∀ col : Fin (s + 2), ∃ x, 1 ≤ x ∧ x ≤ N ∧ c x = col) ∧
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ N →
      ¬ (c x ≠ c (x + d) ∧ c x ≠ c (x + 2 * d) ∧ c (x + d) ≠ c (x + 2 * d))) ∧
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ N → ¬ ∀ j < l, c (x + j * d) = c x) := by
  sorry

/-- **Corollary** (existence form). Under the hypotheses of Theorem 1, `[1, (l - 1)p + 1]` has a
good exact `(s + 2)`-colouring: an exact colouring with no rainbow 3-term AP and no monochromatic
`l`-term AP. -/
theorem exists_goodExactColouring (l p s : ℕ) [Fact p.Prime] (hl : 4 ≤ l) (hp8 : p % 8 = 1)
    (hlp : l < p)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hs : 2 ≤ s) (z : Fin l → Fin s) (hz : Function.Surjective z)
    (hz3 : ∀ i j k : Fin l, i < j → j < k → (i : ℕ) + k = 2 * j →
      ¬ (z i ≠ z j ∧ z i ≠ z k ∧ z j ≠ z k)) :
    ∃ c : ℕ → Fin (s + 2), IsGoodExactColouring (s + 2) l ((l - 1) * p + 1) c := by
  sorry

/-- **Corollary** (Gallai–van der Waerden form): `GW(s + 2; 3, l) > (l - 1)p + 1`. Under the
hypotheses of Theorem 1, every `m` with the defining property of `GW(s + 2; 3, l)` exceeds
`(l - 1)p + 1`. This form needs no assumption that such an `m` exists. -/
theorem lt_of_gwProperty (l p s : ℕ) [Fact p.Prime] (hl : 4 ≤ l) (hp8 : p % 8 = 1)
    (hlp : l < p)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hs : 2 ≤ s) (z : Fin l → Fin s) (hz : Function.Surjective z)
    (hz3 : ∀ i j k : Fin l, i < j → j < k → (i : ℕ) + k = 2 * j →
      ¬ (z i ≠ z j ∧ z i ≠ z k ∧ z j ≠ z k))
    (m : ℕ) (hm : GWProperty (s + 2) l m) : (l - 1) * p + 1 < m := by
  sorry

/-- **Corollary** for the number itself: `(l - 1)p + 1 < GW (s + 2) l`, given that some `m` has
the property (`hex`, which is the Gallai–van der Waerden theorem and is not formalised here). -/
theorem lt_GW (l p s : ℕ) [Fact p.Prime] (hl : 4 ≤ l) (hp8 : p % 8 = 1) (hlp : l < p)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hs : 2 ≤ s) (z : Fin l → Fin s) (hz : Function.Surjective z)
    (hz3 : ∀ i j k : Fin l, i < j → j < k → (i : ℕ) + k = 2 * j →
      ¬ (z i ≠ z j ∧ z i ≠ z k ∧ z j ≠ z k))
    (hex : ∃ m, GWProperty (s + 2) l m) : (l - 1) * p + 1 < GW (s + 2) l := by
  sorry

/-- **Instance** `(l, p) = (4, 17)`, `s = 2`: `GW(4; 3, 4) > 52`. Every `m` with the defining
property of `GW(4; 3, 4)` exceeds `52 = 3 · 17 + 1`. This shows that the hypotheses of Theorem 1 can
be met. -/
theorem gw_r4_l4 (m : ℕ) (hm : GWProperty 4 4 m) : 52 < m := by
  sorry

/-- **Instance** `(l, p) = (4, 17)`, `s = 3`: `GW(5; 3, 4) > 52`. -/
theorem gw_r5_l4 (m : ℕ) (hm : GWProperty 5 4 m) : 52 < m := by
  sorry

end GwResidue
