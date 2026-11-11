module

public import GwResidue.Defs
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

/-!
# Proof of Theorem 1

The lemmas behind `Solution.lean`: the colouring `gwColour` of `GwResidue.Defs` uses all `s + 2`
colours on `[1, N]` (`uses_all`), has no rainbow 3-term AP there (`no_rainbow`) and no
monochromatic `l`-term AP (`no_mono`), where `N = (l - 1)p + 1`. `gwColour_isGood` collects the
three parts. The section `Sanity` checks the run hypothesis for `(l, p) = (4, 17)` by `decide`
(kernel evaluation) and gives the good exact 4- and 5-colourings of `[1, 52]`.

This file is ported from Quantavane's `GwResidue/Basic.lean` (Lean v4.33.1, Mathlib v4.33.1, 11 Nov
2026) to Lean v4.35.0 and Lean's module system; the definitions moved to `GwResidue.Defs` and the
compared theorems to `Solution.lean`.
-/

namespace GwResidue

/-- A good exact colouring of `[1, n]` forces every GW threshold above `n`. -/
theorem lt_of_good {r l n : ℕ} {c : ℕ → Fin r} (hc : IsGoodExactColouring r l n c) {m : ℕ}
    (hm : GWProperty r l m) : n < m := by
  by_contra h
  exact hm n (not_lt.mp h) c hc

section Lemmas

variable {p : ℕ} [hp : Fact p.Prime] {l s : ℕ} {z : Fin l → Fin s}

theorem one_lt_p : 1 < p := hp.out.one_lt

theorem mod_eq_one_iff (y : ℕ) : y % p = 1 ↔ (y : ZMod p) = 1 := by
  have h := ZMod.natCast_eq_natCast_iff' y 1 p
  rw [Nat.cast_one, Nat.mod_eq_of_lt (one_lt_p (p := p))] at h
  exact h.symm

omit hp in
theorem eq_one_add_mul_of_mod {x : ℕ} (hx : x % p = 1) : x = 1 + p * (x / p) := by
  have := Nat.mod_add_div x p
  rw [hx] at this
  exact this.symm

theorem idx_lt {k : ℕ} (hl : 1 ≤ l) (h : 1 + p * k ≤ (l - 1) * p + 1) : k < l := by
  have hp1 : 1 < p := one_lt_p
  have h1 : p * k ≤ p * (l - 1) := by rw [Nat.mul_comm p (l - 1)]; omega
  have := Nat.le_of_mul_le_mul_left h1 (by omega : 0 < p)
  omega

/-- The legendre symbols of `-1`, `2`, `-2` are `1` when `p ≡ 1 (mod 8)`. -/
theorem legendreSym_small (hp8 : p % 8 = 1) :
    legendreSym p (-1) = 1 ∧ legendreSym p 2 = 1 ∧ legendreSym p (-2) = 1 := by
  have hp2 : p ≠ 2 := by omega
  have hm1 : legendreSym p (-1) = 1 := by
    rw [legendreSym.at_neg_one hp2]
    exact ZMod.χ₄_nat_one_mod_four (by omega)
  have h2 : legendreSym p 2 = 1 := by
    rw [legendreSym.at_two hp2, ZMod.χ₈_nat_eq_if_mod_eight]
    have : p % 2 = 1 := by omega
    simp [this, hp8]
  refine ⟨hm1, h2, ?_⟩
  rw [show (-2 : ℤ) = -1 * 2 by norm_num, legendreSym.mul, hm1, h2]
  norm_num

theorem two_ne_zero_zmod (hp8 : p % 8 = 1) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  have := one_lt_p (p := p)
  omega

/-- If `w ≡ 1 (mod p)` and `y = w + m d`, then `(y - 1 | p) = (m | p) (d | p)`. -/
theorem legendre_shift {y w d : ℕ} {m : ℤ} (hw : (w : ZMod p) = 1) (h : (y : ℤ) = w + m * d) :
    legendreSym p ((y : ℤ) - 1) = legendreSym p m * legendreSym p d := by
  rw [← legendreSym.mul]
  unfold legendreSym
  congr 1
  rw [h]
  push_cast
  rw [hw]
  ring

theorem gwColour_of_mod_ne {x : ℕ} (hx : x % p ≠ 1) :
    gwColour p l s z x =
      if legendreSym p ((x : ℤ) - 1) = 1 then 0 else 1 := by
  unfold gwColour
  rw [dite_eq_right (fun h => hx h.1)]

theorem gwColour_val_lt_two {x : ℕ} (hx : x % p ≠ 1) : (gwColour p l s z x : ℕ) < 2 := by
  rw [gwColour_of_mod_ne hx]
  split_ifs <;> simp

theorem gwColour_one_add_mul (k : ℕ) (hk : k < l) :
    gwColour p l s z (1 + p * k) = (z ⟨k, hk⟩).addNat 2 := by
  have hp1 : 1 < p := one_lt_p
  have h1 : (1 + p * k) % p = 1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp1]
  have h2 : (1 + p * k - 1) / p = k := by
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left k (by omega)]
  have hc : (1 + p * k) % p = 1 ∧ (1 + p * k - 1) / p < l := ⟨h1, by rw [h2]; exact hk⟩
  unfold gwColour
  rw [dite_eq_left hc]
  exact congrArg (fun i => (z i).addNat 2) (Fin.ext h2)

theorem addNat_two_inj {a b : Fin s} (h : a.addNat 2 = b.addNat 2) : a = b := by
  ext
  have := congrArg Fin.val h
  simpa using this

theorem not_rainbow_of_lt_two {n : ℕ} {a b c : Fin n} (ha : (a : ℕ) < 2) (hb : (b : ℕ) < 2)
    (hc : (c : ℕ) < 2) : ¬ (a ≠ b ∧ a ≠ c ∧ b ≠ c) := by
  rintro ⟨h1, h2, h3⟩
  rw [Ne, Fin.ext_iff] at h1 h2 h3
  omega

/-- Part (a): every one of the `s + 2` colours occurs on `[1, N]`. -/
theorem uses_all (hl : 4 ≤ l) (hp8 : p % 8 = 1) (hlp : l < p)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hz : Function.Surjective z) (col : Fin (s + 2)) :
    ∃ x, 1 ≤ x ∧ x ≤ (l - 1) * p + 1 ∧ gwColour p l s z x = col := by
  have hp1 : 1 < p := one_lt_p
  have hpN : p ≤ (l - 1) * p := Nat.le_mul_of_pos_left p (by omega)
  obtain ⟨c, hc⟩ := col
  rcases Nat.lt_or_ge c 2 with h2 | h2
  · interval_cases c
    · -- colour `0`: the point `2`, as `(1 | p) = 1`
      refine ⟨2, by omega, by omega, ?_⟩
      have h2p : 2 % p ≠ 1 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [gwColour_of_mod_ne h2p]
      norm_num [legendreSym.at_one]
    · -- colour `1`: the run hypothesis at `a = 1` gives a non-residue `1 + j ≤ l`
      obtain ⟨j, hj, hne⟩ := hrun 1 le_rfl (by omega)
      refine ⟨2 + j, by omega, by omega, ?_⟩
      have hm : (2 + j) % p ≠ 1 := by
        rcases Nat.lt_or_ge (2 + j) p with h | h
        · rw [Nat.mod_eq_of_lt h]; omega
        · rw [show 2 + j = p by omega, Nat.mod_self]; omega
      rw [gwColour_of_mod_ne hm, ite_eq_right]
      · exact Fin.ext (by simp)
      rw [show ((2 + j : ℕ) : ℤ) - 1 = ((1 + j : ℕ) : ℤ) by push_cast; ring]
      simpa [legendreSym.at_one] using hne
  · -- colour `c ≥ 2`: a point `1 + k p` with `z k = c - 2`
    obtain ⟨⟨k, hk⟩, hzk⟩ := hz ⟨c - 2, by omega⟩
    refine ⟨1 + p * k, by omega, ?_, ?_⟩
    · have : p * k ≤ (l - 1) * p := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right p (by omega)
      omega
    · rw [gwColour_one_add_mul k hk, hzk]
      exact Fin.ext (by simp only [Fin.val_addNat]; omega)

/-- Part (b): no rainbow 3-term AP in `[1, N]`. -/
theorem no_rainbow (hl : 4 ≤ l) (hp8 : p % 8 = 1)
    (hz3 : ∀ i j k : Fin l, i < j → j < k → (i : ℕ) + k = 2 * j →
      ¬ (z i ≠ z j ∧ z i ≠ z k ∧ z j ≠ z k))
    (x d : ℕ) (hx : 1 ≤ x) (hd : 1 ≤ d) (hN : x + 2 * d ≤ (l - 1) * p + 1) :
    ¬ (gwColour p l s z x ≠ gwColour p l s z (x + d) ∧
        gwColour p l s z x ≠ gwColour p l s z (x + 2 * d) ∧
        gwColour p l s z (x + d) ≠ gwColour p l s z (x + 2 * d)) := by
  intro hrb
  have hp1 : 1 < p := one_lt_p
  obtain ⟨hm1, h2, hm2⟩ := legendreSym_small (p := p) hp8
  by_cases hd0 : (d : ZMod p) = 0
  · -- `p ∣ d`: the three terms are congruent mod `p`
    obtain ⟨e, rfl⟩ := (ZMod.natCast_eq_zero_iff d p).mp hd0
    by_cases hxZ : x % p = 1
    · -- all three terms lie in the zero class: use that `z` has no rainbow 3-AP
      obtain ⟨k, rfl⟩ : ∃ k, x = 1 + p * k := ⟨x / p, eq_one_add_mul_of_mod hxZ⟩
      have he : 1 ≤ e := by
        rcases Nat.eq_zero_or_pos e with h | h
        · subst h; simp at hd
        · exact h
      have t1 : 1 + p * k + p * e = 1 + p * (k + e) := by ring
      have t2 : 1 + p * k + 2 * (p * e) = 1 + p * (k + 2 * e) := by ring
      have hk2 : k + 2 * e < l := idx_lt (by omega) (t2 ▸ hN)
      rw [t1, t2, gwColour_one_add_mul k (by omega), gwColour_one_add_mul (k + e) (by omega),
        gwColour_one_add_mul (k + 2 * e) hk2] at hrb
      apply hz3 ⟨k, by omega⟩ ⟨k + e, by omega⟩ ⟨k + 2 * e, hk2⟩ (Fin.mk_lt_mk.mpr (by omega))
        (Fin.mk_lt_mk.mpr (by omega)) (show k + (k + 2 * e) = 2 * (k + e) by omega)
      exact ⟨fun h => hrb.1 (by rw [h]), fun h => hrb.2.1 (by rw [h]),
        fun h => hrb.2.2 (by rw [h])⟩
    · -- no term lies in the zero class: only the two residue colours occur
      have n1 : (x + p * e) % p ≠ 1 := by rwa [Nat.add_mul_mod_self_left]
      have n2 : (x + 2 * (p * e)) % p ≠ 1 := by
        rwa [show x + 2 * (p * e) = x + p * (2 * e) by ring, Nat.add_mul_mod_self_left]
      exact not_rainbow_of_lt_two (gwColour_val_lt_two hxZ) (gwColour_val_lt_two n1)
        (gwColour_val_lt_two n2) hrb
  · -- `p ∤ d`: at most one term lies in the zero class
    have h2z : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp8
    by_cases hx0 : x % p = 1
    · -- `x` in the zero class: the others are `x + d`, `x + 2d`, with residues `d`, `2d`
      have hw := (mod_eq_one_iff x).mp hx0
      have n1 : (x + d) % p ≠ 1 := by
        rw [Ne, mod_eq_one_iff]; push_cast; rw [hw]; intro h
        exact hd0 (by linear_combination h)
      have n2 : (x + 2 * d) % p ≠ 1 := by
        rw [Ne, mod_eq_one_iff]; push_cast; rw [hw]; intro h
        exact mul_ne_zero h2z hd0 (by linear_combination h)
      apply hrb.2.2
      rw [gwColour_of_mod_ne n1, gwColour_of_mod_ne n2,
        legendre_shift (y := x + d) (w := x) (d := d) (m := 1) hw (by push_cast; ring),
        legendre_shift (y := x + 2 * d) (w := x) (d := d) (m := 2) hw (by push_cast; ring),
        legendreSym.at_one, h2]
    · by_cases hx1 : (x + d) % p = 1
      · -- `x + d` in the zero class: residues `-d`, `d`
        have hw := (mod_eq_one_iff (x + d)).mp hx1
        have n2 : (x + 2 * d) % p ≠ 1 := by
          rw [Ne, mod_eq_one_iff]; intro h
          apply hd0
          have hw' := hw
          push_cast at hw' h
          linear_combination h - hw'
        apply hrb.2.1
        rw [gwColour_of_mod_ne hx0, gwColour_of_mod_ne n2,
          legendre_shift (y := x) (w := x + d) (d := d) (m := -1) hw (by push_cast; ring),
          legendre_shift (y := x + 2 * d) (w := x + d) (d := d) (m := 1) hw (by push_cast; ring),
          legendreSym.at_one, hm1]
      · by_cases hx2 : (x + 2 * d) % p = 1
        · -- `x + 2d` in the zero class: residues `-2d`, `-d`
          have hw := (mod_eq_one_iff (x + 2 * d)).mp hx2
          apply hrb.1
          rw [gwColour_of_mod_ne hx0, gwColour_of_mod_ne hx1,
            legendre_shift (y := x) (w := x + 2 * d) (d := d) (m := -2) hw (by push_cast; ring),
            legendre_shift (y := x + d) (w := x + 2 * d) (d := d) (m := -1) hw
              (by push_cast; ring),
            hm1, hm2]
        · -- no term in the zero class
          exact not_rainbow_of_lt_two (gwColour_val_lt_two hx0) (gwColour_val_lt_two hx1)
            (gwColour_val_lt_two hx2) hrb

/-- Part (c): no monochromatic `l`-term AP in `[1, N]`. -/
theorem no_mono (hl : 4 ≤ l)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hs : 2 ≤ s) (hz : Function.Surjective z)
    (x d : ℕ) (hx : 1 ≤ x) (hd : 1 ≤ d) (hN : x + (l - 1) * d ≤ (l - 1) * p + 1) :
    ¬ ∀ j < l, gwColour p l s z (x + j * d) = gwColour p l s z x := by
  intro hall
  have hp1 : 1 < p := one_lt_p
  have hp0 : 0 < p := by omega
  -- every term lies in `[1, N]`
  have hterm : ∀ j < l, x + j * d ≤ (l - 1) * p + 1 := by
    intro j hj
    have : j * d ≤ (l - 1) * d := Nat.mul_le_mul_right d (by omega)
    omega
  -- a point of the zero class in `[1, N]` has colour `≥ 2`
  have hbig : ∀ y, y % p = 1 → y ≤ (l - 1) * p + 1 → 2 ≤ (gwColour p l s z y : ℕ) := by
    intro y hy hyN
    obtain ⟨k, hk⟩ : ∃ k, y = 1 + p * k := ⟨y / p, eq_one_add_mul_of_mod hy⟩
    subst hk
    rw [gwColour_one_add_mul k (idx_lt (by omega) hyN)]
    simp
  -- if `p ∣ d` then `d = p` and `x = 1`
  have hpd : (d : ZMod p) = 0 → d = p ∧ x = 1 := by
    intro h0
    obtain ⟨e, rfl⟩ := (ZMod.natCast_eq_zero_iff d p).mp h0
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at hd
      · exact h
    have h1 : (l - 1) * (p * e) ≤ (l - 1) * (p * 1) := by rw [Nat.mul_one]; omega
    have h2 : p * e ≤ p * 1 := Nat.le_of_mul_le_mul_left h1 (by omega)
    have h3 : e ≤ 1 := Nat.le_of_mul_le_mul_left h2 hp0
    have he1 : e = 1 := by omega
    subst he1
    rw [Nat.mul_one] at hN ⊢
    exact ⟨rfl, by omega⟩
  by_cases hxZ : x % p = 1
  · -- every term lies in the zero class, so `p ∣ d`, the AP is the zero class itself,
    -- coloured by `z`, which is not constant
    have hallZ : ∀ j < l, (x + j * d) % p = 1 := by
      intro j hj
      by_contra hne
      have h1 := gwColour_val_lt_two (l := l) (s := s) (z := z) hne
      rw [hall j hj] at h1
      have := hbig x hxZ (by omega)
      omega
    have hd0 : (d : ZMod p) = 0 := by
      have a1 := (mod_eq_one_iff _).mp (hallZ 1 (by omega))
      have a0 := (mod_eq_one_iff _).mp hxZ
      push_cast at a1
      linear_combination a1 - a0
    obtain ⟨hdp, hx1⟩ := hpd hd0
    subst hx1
    rw [hdp] at hall
    have h0 : gwColour p l s z 1 = (z ⟨0, by omega⟩).addNat 2 := by
      simpa using gwColour_one_add_mul (p := p) (z := z) 0 (by omega)
    have hc : ∀ i : Fin l, z i = z ⟨0, by omega⟩ := by
      intro i
      have h := hall i i.isLt
      rw [show 1 + (i : ℕ) * p = 1 + p * i by ring, gwColour_one_add_mul (i : ℕ) i.isLt, h0] at h
      exact addNat_two_inj h
    obtain ⟨i0, hi0⟩ := hz ⟨0, by omega⟩
    obtain ⟨i1, hi1⟩ := hz ⟨1, by omega⟩
    rw [hc i0] at hi0
    rw [hc i1, hi0] at hi1
    simp at hi1
  · -- no term lies in the zero class
    have hallN : ∀ j < l, (x + j * d) % p ≠ 1 := by
      intro j hj hZ
      have h1 := gwColour_val_lt_two (l := l) (s := s) (z := z) hxZ
      rw [← hall j hj] at h1
      have := hbig _ hZ (hterm j hj)
      omega
    by_cases hd0 : (d : ZMod p) = 0
    · obtain ⟨_, hx1⟩ := hpd hd0
      exact hxZ (by rw [hx1]; exact Nat.mod_eq_of_lt hp1)
    · -- write `x - 1 ≡ a d (mod p)`; the term `x + j d` has residue `(a + j) d`
      set A : ZMod p := ((x : ZMod p) - 1) / (d : ZMod p) with hA
      have hAd : A * d = (x : ZMod p) - 1 := div_mul_cancel₀ _ hd0
      have ha : ((A.val : ℕ) : ZMod p) = A := ZMod.natCast_zmod_val A
      set a := A.val with ha_def
      have hleg : ∀ j : ℕ, legendreSym p (((x + j * d : ℕ) : ℤ) - 1) =
          legendreSym p ((a + j : ℕ) : ℤ) * legendreSym p (d : ℤ) := by
        intro j
        rw [← legendreSym.mul]
        unfold legendreSym
        congr 1
        push_cast
        rw [ha]
        linear_combination -hAd
      have hnz : ∀ j < l, ((a + j : ℕ) : ZMod p) ≠ 0 := by
        intro j hj h0
        apply hallN j hj
        rw [mod_eq_one_iff]
        push_cast at h0 ⊢
        rw [ha] at h0
        linear_combination (d : ZMod p) * h0 - hAd
      have ha_lt : a < p := ZMod.val_lt A
      have ha1 : 1 ≤ a := by
        rcases Nat.eq_zero_or_pos a with h | h
        · exfalso; apply hnz 0 (by omega); rw [h]; simp
        · exact h
      -- `a, a+1, …, a+l-1` avoid `0 (mod p)`, so they lie in `[1, p-1]`
      have hal : a + (l - 1) ≤ p - 1 := by
        by_contra hcon
        apply hnz (p - a) (by omega)
        rw [show a + (p - a) = p by omega]
        exact ZMod.natCast_self p
      obtain ⟨j, hj, hne⟩ := hrun a ha1 hal
      have hc := hall j hj
      have hleg0 : legendreSym p ((x : ℤ) - 1) =
          legendreSym p (a : ℤ) * legendreSym p (d : ℤ) := by
        simpa using hleg 0
      rw [gwColour_of_mod_ne (hallN j hj), gwColour_of_mod_ne hxZ, hleg j, hleg0] at hc
      have hd' : ((d : ℤ) : ZMod p) ≠ 0 := by exact_mod_cast hd0
      have hj' : (((a + j : ℕ) : ℤ) : ZMod p) ≠ 0 := by exact_mod_cast hnz j hj
      have h0' : (((a : ℕ) : ℤ) : ZMod p) ≠ 0 := by
        have := hnz 0 (by omega)
        simp only [Nat.add_zero] at this
        exact_mod_cast this
      rcases legendreSym.eq_one_or_neg_one p hd' with e1 | e1 <;>
        rcases legendreSym.eq_one_or_neg_one p hj' with e2 | e2 <;>
        rcases legendreSym.eq_one_or_neg_one p h0' with e3 | e3 <;>
        · rw [e1, e2, e3] at hc
          rw [e2, e3] at hne
          simp at hc hne

end Lemmas

/-- Theorem 1 in the language of `IsGoodExactColouring`: the three parts `uses_all`, `no_rainbow`
and `no_mono`. -/
theorem gwColour_isGood (l p s : ℕ) [Fact p.Prime] (hl : 4 ≤ l) (hp8 : p % 8 = 1) (hlp : l < p)
    (hrun : ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ))
    (hs : 2 ≤ s) (z : Fin l → Fin s) (hz : Function.Surjective z)
    (hz3 : ∀ i j k : Fin l, i < j → j < k → (i : ℕ) + k = 2 * j →
      ¬ (z i ≠ z j ∧ z i ≠ z k ∧ z j ≠ z k)) :
    IsGoodExactColouring (s + 2) l ((l - 1) * p + 1) (gwColour p l s z) :=
  ⟨uses_all hl hp8 hlp hrun hz, fun x d hx hd hN => no_rainbow hl hp8 hz3 x d hx hd hN,
    fun x d hx hd hN => no_mono hl hrun hs hz x d hx hd hN⟩

/-! ## Sanity instance: `(l, p) = (4, 17)` -/

section Sanity

/-- Euler's criterion turns the run hypothesis into a finite computation on natural numbers. -/
theorem hrun_of_euler {p : ℕ} [Fact p.Prime] {l : ℕ}
    (h : ∀ a < p, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, ((a + j) ^ (p / 2) % p = 1 ↔ ¬ a ^ (p / 2) % p = 1)) :
    ∀ a : ℕ, 1 ≤ a → a + (l - 1) ≤ p - 1 →
      ∃ j < l, legendreSym p ((a + j : ℕ) : ℤ) ≠ legendreSym p (a : ℤ) := by
  have key : ∀ n : ℕ, 1 ≤ n → n < p → (legendreSym p (n : ℤ) = 1 ↔ n ^ (p / 2) % p = 1) := by
    intro n hn1 hnp
    have hn0 : (n : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [legendreSym.eq_one_iff' p hn0, ZMod.euler_criterion p hn0, mod_eq_one_iff]
    push_cast
    exact Iff.rfl
  intro a ha hal
  obtain ⟨j, hj, hiff⟩ := h a (by omega) ha hal
  refine ⟨j, hj, fun heq => ?_⟩
  have k1 := key (a + j) (by omega) (by omega)
  have k2 := key a ha (by omega)
  rw [heq] at k1
  tauto

instance fact_prime_17 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The run condition for `(l, p) = (4, 17)`, by `decide` (kernel evaluation). -/
theorem run_4_17 : ∀ a < 17, 1 ≤ a → a + (4 - 1) ≤ 17 - 1 →
    ∃ j < 4, ((a + j) ^ (17 / 2) % 17 = 1 ↔ ¬ a ^ (17 / 2) % 17 = 1) := by
  decide

/-- `l = 4, p = 17, s = 2`: a good exact 4-colouring of `[1, 52]`, so `GW(4; 3, 4) > 52`. -/
theorem good_4_17_r4 : IsGoodExactColouring 4 4 52 (gwColour 17 4 2 ![0, 1, 1, 0]) :=
  gwColour_isGood 4 17 2 (by norm_num) (by norm_num) (by norm_num) (hrun_of_euler run_4_17)
    (by norm_num) _ (by decide) (by decide)

/-- `l = 4, p = 17, s = 3`: a good exact 5-colouring of `[1, 52]`, so `GW(5; 3, 4) > 52`. -/
theorem good_4_17_r5 : IsGoodExactColouring 5 4 52 (gwColour 17 4 3 ![0, 1, 1, 2]) :=
  gwColour_isGood 4 17 3 (by norm_num) (by norm_num) (by norm_num) (hrun_of_euler run_4_17)
    (by norm_num) _ (by decide) (by decide)

end Sanity

end GwResidue
