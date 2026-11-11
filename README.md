# Gallai–van der Waerden numbers from quadratic-residue colourings

A Lean 4 proof, with Mathlib, of a lower-bound construction for the Gallai–van der Waerden numbers
`GW(r; 3, l)` of Mao, Ozeki, Robertson and Wang. It is laid out for registration on
[Palomar](https://palomar-registry.org): `Challenge.lean` states the results, `Solution.lean` proves
them, and `comparator.json` names the compared theorems. Submissions go through the form at
https://submit.palomar-registry.org/.

## The result

Write `[1, n] = {1, …, n}`. An exact `r`-colouring of `[1, n]` uses all `r` colours. A 3-term
arithmetic progression (AP) is rainbow when its terms have three distinct colours; an `l`-term AP is
monochromatic when its terms all have one colour; common differences are at least 1. Following
Mao, Ozeki, Robertson and Wang (MORW; J. Combin. Theory Ser. A 193 (2023) 105672, Definition 1.15),
`GW(r; 3, l)` is the least `m` such that for every `n ≥ m`, every exact `r`-colouring of `[1, n]`
contains a rainbow 3-term AP or a monochromatic `l`-term AP.

**Theorem 1.** Let `l ≥ 4` and let `p > l` be a prime with `p ≡ 1 (mod 8)` such that no `l`
consecutive integers in `[1, p - 1]` all have the same Legendre symbol modulo `p`. Let `s ≥ 2` and
let `z : {0, …, l - 1} → {0, …, s - 1}` be onto, with no rainbow 3-term AP. Put `N = (l - 1)p + 1`
and colour `x ∈ [1, N]`:

- if `x ≢ 1 (mod p)`: colour `0` when `(x - 1 | p) = 1`, colour `1` otherwise;
- if `x = 1 + kp` (`0 ≤ k ≤ l - 1`): colour `2 + z(k)`.

Then this is an exact `(s + 2)`-colouring of `[1, N]` with no rainbow 3-term AP and no
monochromatic `l`-term AP. Hence `GW(s + 2; 3, l) > (l - 1)p + 1`.

For `(l, p) = (4, 17)` the hypotheses hold, which gives `GW(4; 3, 4) > 52` and `GW(5; 3, 4) > 52`.

## What is compared (`comparator.json`)

All six theorems are stated in `Challenge.lean` (with `sorry`) and proved in `Solution.lean`.

| Lean name | What it says |
|---|---|
| `GwResidue.theorem1` | Theorem 1 as above, parts (a) all `s + 2` colours occur on `[1, N]`, (b) no rainbow 3-term AP in `[1, N]`, (c) no monochromatic `l`-term AP in `[1, N]`, for the colouring `gwColour p l s z`. |
| `GwResidue.exists_goodExactColouring` | Under the same hypotheses, `[1, (l - 1)p + 1]` has a good exact `(s + 2)`-colouring. |
| `GwResidue.lt_of_gwProperty` | Under the same hypotheses, every `m` with the defining property of `GW(s + 2; 3, l)` is greater than `(l - 1)p + 1`. |
| `GwResidue.lt_GW` | The same inequality for the number `GW (s + 2) l` itself, assuming some `m` has the property. |
| `GwResidue.gw_r4_l4` | Every `m` with the defining property of `GW(4; 3, 4)` is greater than 52. |
| `GwResidue.gw_r5_l4` | Every `m` with the defining property of `GW(5; 3, 4)` is greater than 52. |

`definition_names` is empty on purpose. The four definitions the statements use (below) are spelled
out in full in `Challenge.lean`; Comparator follows them from the theorem statements and requires
them to be identical in the Solution, which takes them from `GwResidue/Defs.lean`.

## Definitions, and how they match the paper

- `IsGoodExactColouring r l n c`: every colour `col : Fin r` occurs on `[1, n]`; no `x, x + d, x + 2d`
  in `[1, n]` with `d ≥ 1` has three distinct colours; no `x, x + d, …, x + (l - 1)d` in `[1, n]` with
  `d ≥ 1` is monochromatic. The colouring `c : ℕ → Fin r` is defined on all of `ℕ`; only its values on
  `[1, n]` matter.
- `GWProperty r l m`: for every `n ≥ m` and every `c`, `¬ IsGoodExactColouring r l n c`. This is the
  defining property in MORW Definition 1.15 (for every `n ≥ m`, not only `n = m`, since exactness does
  not pass to sub-intervals).
- `GW r l := sInf {m | GWProperty r l m}`. In Lean the infimum of the empty set of natural numbers is
  `0`. The Gallai–van der Waerden theorem (that some `m` has the property) is not formalised here, so
  `lt_GW` assumes it (`hex`). `lt_of_gwProperty`, `gw_r4_l4` and `gw_r5_l4` need no such assumption.
- `gwColour p l s z x`: the colouring of Theorem 1, with colours `Fin (s + 2)`. Points `1 + kp` with
  `k ≥ l` lie outside `[1, N]` and get a residue colour, which plays no role.

How the hypotheses are encoded in `theorem1`:

- `hrun`: for every `a ≥ 1` with `a + (l - 1) ≤ p - 1` there is `j < l` with
  `legendreSym p (a + j) ≠ legendreSym p a`, that is, no run of `l` equal Legendre symbols in
  `[1, p - 1]`.
- `hz3`: no `i < j < k` in `Fin l` with `i + k = 2j` gets three distinct colours under `z`.
- `hz` (onto) and `hs : 2 ≤ s` make `z` non-constant; "not constant" is not a separate hypothesis.
- `p ≡ 1 (mod 8)` is what part (b) needs (through `(-1 | p) = (2 | p) = 1`), and `l < p` is used in
  part (a); both are hypotheses of every general theorem.

## How the proof goes (`GwResidue/Basic.lean`)

- `legendreSym_small`: from `p ≡ 1 (mod 8)`, `(-1 | p) = (2 | p) = (-2 | p) = 1` (Mathlib's
  `legendreSym.at_neg_one`, `legendreSym.at_two`).
- `legendre_shift`: if `w ≡ 1 (mod p)` and `y = w + md`, then `(y - 1 | p) = (m | p)(d | p)`.
- `uses_all` (a): colour 0 at `x = 2`; colour 1 at `x = 2 + j`, where `1 + j` is the non-residue that
  `hrun` gives at `a = 1`; colour `2 + t` at `x = 1 + kp` with `z(k) = t`.
- `no_rainbow` (b): if `p | d` the three terms are all in the zero class (then `hz3` applies) or all
  outside it (two colours only). If `p ∤ d`, at most one term is in the zero class, and the other two
  have residues `(d, 2d)`, `(-d, d)` or `(-2d, -d)` modulo `p`, which have equal Legendre symbols
  because `(-1 | p) = (2 | p) = 1`.
- `no_mono` (c): a monochromatic AP with a colour `≥ 2` lies in the zero class, which forces `d = p`,
  `x = 1`, so the AP is the whole zero class, coloured by the non-constant `z`. Otherwise no term is in
  the zero class, `p ∤ d`, and with `x - 1 ≡ ad (mod p)` the colours are those of
  `(a + j | p)(d | p)` for `j < l`; the integers `a, …, a + l - 1` lie in `[1, p - 1]`, so `hrun` makes
  two colours differ.
- `gwColour_isGood` collects (a)–(c); `lt_of_good` turns a good exact colouring of `[1, n]` into
  `n < m` for every `m` with the GW property.
- The instance `(4, 17)`: `run_4_17` checks the run condition in Euler's form
  (`(a + j)^8 % 17 = 1 ↔ ¬ a^8 % 17 = 1`) by `decide`, which the kernel evaluates;
  `hrun_of_euler` turns it into `hrun` (Mathlib's `ZMod.euler_criterion`). The colourings
  `z = 0, 1, 1, 0` and `z = 0, 1, 1, 2` are checked onto and rainbow-free by `decide`.

No `sorry` outside `Challenge.lean`, no `native_decide`, no extra axioms:
`lake env lean scripts/CheckAxioms.lean` prints `[propext, Classical.choice, Quot.sound]` for each
compared theorem.

## Why it is of interest

Gallai–van der Waerden numbers were introduced by Mao, Ozeki, Robertson and Wang (2023) as the
arithmetic analogue of Gallai–Ramsey numbers, and published exact values exist only for `l = 3` (Si, 2026).
Theorem 1 turns any prime `p ≡ 1 (mod 8)` without `l` consecutive equal quadratic characters into an
explicit lower bound for every number of colours `r = s + 2` with `2 ≤ s ≤ s(l)`, where `s(l)` is the
largest number of colours of a rainbow-free colouring of `{0, …, l - 1}`. For `l = 4` the bound is
sharp: `p = 17` gives `GW(r; 3, 4) ≥ 53` for `r = 4, 5`, and SAT certificates (Quantavane, not part of
this submission) show `GW(4; 3, 4) = GW(5; 3, 4) = 53`. Primes found by a computer search (not
formalised here) give, for example, `GW(r; 3, 6) ≥ 967` (`p = 193`) and `GW(r; 3, 7) ≥ 3,704`
(`p = 617`) for `r = 4, 5`. The natural readers are researchers in Ramsey theory on the integers and
arithmetic combinatorics: van der Waerden numbers, rainbow (anti-van der Waerden) problems and
Gallai–Ramsey colourings.

## Provenance, literature and novelty

The construction and Theorem 1 were found on 11 November 2026 in Quantavane's research work and are
first presented here (an internal note of Quantavane has the same statement and proof). The
residue part of the colouring is the classical power-residue idea for van der Waerden lower bounds
(Rabung, Canad. Math. Bull. 22 (1979) 87–91; Rabung and Lotts, Electron. J. Combin. 19(2) (2012) #P35).
What is new here is the Gallai setting: the zero class `1 + kp` is an `l`-term AP that receives its own
rainbow-free colouring, and `(-1 | p) = (2 | p) = 1` is what keeps every 3-term AP through the zero
class from being rainbow.

Literature search (11 November 2026): MORW give definitions, `GW(r; 3, 3)` values and asymptotic
bounds, but no value for `l ≥ 4`; Y. Si (arXiv:2610.30711, October 2026) determines `GW(r; 3, 3)` for
every `r`; MathWorld's Gallai–van der Waerden page (updated 11 November 2026) lists only `l = 3`. We
found no earlier construction of this kind and no published value or bound of `GW(r; 3, l)` for
`l ≥ 4`. The search was limited (these sources and two web searches), so novelty is our reading, not
an established fact. Y. Si has told us of preliminary, unpublished computations of small values of
`GW(r; 3, 4)` (private communication, November 2026), which agree with `gw_r4_l4` and `gw_r5_l4`; we
claim no priority for those two numerical instances.

## Authorship and the role of AI

Author and maintainer: Arhan Canli (Quantavane), who takes responsibility for the result.

The construction, its informal proof and the Lean proof were produced by AI agents (Claude, by
Anthropic) working for Quantavane under Arhan Canli's direction: the coordinating agent found the
construction and wrote the informal proof, a second agent wrote the Lean proof (Lean v4.33.1), and the
coordinating agent rebuilt that proof from scratch, printed the elaborated statement with `#check` to compare it
with the informal statement, and printed its axioms. A third agent ported it to Lean v4.35.0 and the
module system for this repository. No mathematician outside Quantavane has reviewed the proof.

## Checking it

Lean `v4.35.0` (`lean-toolchain`) and Mathlib `v4.35.0`
(`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`).

```sh
lake exe cache get        # prebuilt Mathlib
lake build                # GwResidue, Challenge, Solution
lake env lean scripts/CheckAxioms.lean
lake comparator           # Linux with bubblewrap: compares Challenge and Solution and replays the proofs
```

`.github/workflows/palomar-preflight.yml` runs Palomar's own mechanical check
(`PalomarRegistry/PalomarSubmission`, pinned commit) on every push to `main`.

## Files

- `Challenge.lean`: the statement of record (Mathlib imports only, about 150 lines).
- `Solution.lean`: the six compared theorems with proofs.
- `GwResidue/Defs.lean`: the four definitions, identical to those in `Challenge.lean`.
- `GwResidue/Basic.lean`: the proof.
- `comparator.json`, `formalization.yaml`, `scripts/CheckAxioms.lean`.

## Licence

Apache-2.0 (`LICENSE`).
