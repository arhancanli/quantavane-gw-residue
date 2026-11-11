module

public import GwResidue

public section

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` (Comparator
checks this, together with the definitions the statements use, which come from `GwResidue.Defs`).
The proofs are in `GwResidue/Basic.lean`:

* `uses_all`, `no_rainbow`, `no_mono`: parts (a), (b), (c) of Theorem 1;
* `gwColour_isGood`: the three parts as `IsGoodExactColouring`;
* `lt_of_good`: a good exact colouring of `[1, n]` puts every GW threshold above `n`;
* `good_4_17_r4`, `good_4_17_r5`: Theorem 1 at `(l, p) = (4, 17)`, with the run hypothesis checked
  by `decide` through Euler's criterion (`hrun_of_euler`, `run_4_17`).
-/

namespace GwResidue

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
    (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ N → ¬ ∀ j < l, c (x + j * d) = c x) :=
  ⟨uses_all hl hp8 hlp hrun hz, fun x d hx hd hN => no_rainbow hl hp8 hz3 x d hx hd hN,
    fun x d hx hd hN => no_mono hl hrun hs hz x d hx hd hN⟩

theorem exists_goodExactColouring (l p s : ℕ) [Fact p.Prime] (hl : 4 ≤ l) (hp8 : p % 8 = 1)
    (hlp : l < p)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hs : 2 ≤ s) (z : Fin l → Fin s) (hz : Function.Surjective z)
    (hz3 : ∀ i j k : Fin l, i < j → j < k → (i : ℕ) + k = 2 * j →
      ¬ (z i ≠ z j ∧ z i ≠ z k ∧ z j ≠ z k)) :
    ∃ c : ℕ → Fin (s + 2), IsGoodExactColouring (s + 2) l ((l - 1) * p + 1) c :=
  ⟨_, gwColour_isGood l p s hl hp8 hlp hrun hs z hz hz3⟩

theorem lt_of_gwProperty (l p s : ℕ) [Fact p.Prime] (hl : 4 ≤ l) (hp8 : p % 8 = 1)
    (hlp : l < p)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hs : 2 ≤ s) (z : Fin l → Fin s) (hz : Function.Surjective z)
    (hz3 : ∀ i j k : Fin l, i < j → j < k → (i : ℕ) + k = 2 * j →
      ¬ (z i ≠ z j ∧ z i ≠ z k ∧ z j ≠ z k))
    (m : ℕ) (hm : GWProperty (s + 2) l m) : (l - 1) * p + 1 < m :=
  lt_of_good (gwColour_isGood l p s hl hp8 hlp hrun hs z hz hz3) hm

theorem lt_GW (l p s : ℕ) [Fact p.Prime] (hl : 4 ≤ l) (hp8 : p % 8 = 1) (hlp : l < p)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hs : 2 ≤ s) (z : Fin l → Fin s) (hz : Function.Surjective z)
    (hz3 : ∀ i j k : Fin l, i < j → j < k → (i : ℕ) + k = 2 * j →
      ¬ (z i ≠ z j ∧ z i ≠ z k ∧ z j ≠ z k))
    (hex : ∃ m, GWProperty (s + 2) l m) : (l - 1) * p + 1 < GW (s + 2) l :=
  lt_of_gwProperty l p s hl hp8 hlp hrun hs z hz hz3 _ (Nat.sInf_mem hex)

theorem gw_r4_l4 (m : ℕ) (hm : GWProperty 4 4 m) : 52 < m := lt_of_good good_4_17_r4 hm

theorem gw_r5_l4 (m : ℕ) (hm : GWProperty 5 4 m) : 52 < m := lt_of_good good_4_17_r5 hm

end GwResidue
