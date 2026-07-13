# Central-Binomial-Lean

Lean 4 / Mathlib formalization of the deterministic proof in
"An AI-Derived Proof of Erdős Problem #728 via Higher-Power Carry
Compensation." You can read the paper at: [Paper link](https://omniscienceproject.com/papers/an-ai-derived-proof-of-erdos-problem-728-via-higher-power-carry-1hwQTOM4). A companion paper with a different method of proof to the same problem is also available at: [Companion Paper link](https://omniscienceproject.com/papers/a-deterministic-resolution-of-erdos-problem-728-via-small-prime-nQHYqk7S).

## Status: complete and kernel-verified

Erdős Problem #728 is **fully proved** in this development, unconditionally.
The paper-facing main theorem is

```
theorem erdos728Main_proved : erdos728Main
```

in `CentralBinomialLean/ParameterSupply.lean`, where `erdos728Main` (stated in
`CentralBinomialLean/Problem.lean`) unfolds to: for every `0 < C₁ < C₂` and
every `0 < ε < 1/2`, there are infinitely many triples `(a, b, n)` with
`ε·n ≤ a, b ≤ (1-ε)·n`, `a!·b! ∣ n!·(a+b-n)!`, and `C₁·log n < a+b-n < C₂·log n`.

- The project builds from source with **no `sorry`** in any Lean file.
- `#print axioms erdos728Main_proved` reports only the three standard
  foundational axioms — `[propext, Classical.choice, Quot.sound]` — i.e. no
  `sorryAx` and no project-specific axioms. The result is a genuine
  kernel-checked proof.

The final asymptotic step is closed unconditionally by
`shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt_of_pos`,
which discharges the counting budget from the standard sublinear growth of
`log x`, `√x · log x`, and `log² x` against the linear budget `x` — the
formal counterpart of the paper's "the cost is a vanishing fraction of
`log N`" argument.

See [Building and verifying](#building-and-verifying) below to reproduce both
checks.

## Component overview

The project builds with no `sorry` in Lean sources.

`CentralBinomialLean/Problem.lean` is the reviewer's entry point: it states
*only* the paper-facing problem — `erdos728Triple`, `erdos728UnboundedTriples`,
`erdos728Main` — together with the central divisibility predicates
`centralBinomialDivides` / `centralFactorialDivides` and the elementary bridge
between them. No proof machinery lives here.

`CentralBinomialLean/Carry.lean` contains:

- the carry predicates for `(A + k).choose k` and `(2 * A).choose A`;
- the `q > 2k` domination lemma from paper Lemma 5;
- the exact-congruence carry equality used in paper Lemma 6;
- the deficit and surplus residue predicates from Section 6, using integer-exact
  half-thresholds (`2 * r < p` and `q <= 2 * r`);
- the finite one-step lifting count:
  among the `p` lifts `u + lQ`, at most `p / 2 + 2` avoid the surplus interval;
- the iterated geometric lifting bound and the integer `p >= 8` version of the
  `3/4` decay factor from paper Lemma 7.

`CentralBinomialLean/Kummer.lean` connects those carry predicates to Mathlib's
Kummer/factorization theorem for binomial coefficients.

`CentralBinomialLean/SmallPrimes.lean` proves the small-prime congruence
mechanism. It includes a concrete finite modulus `Nat.lcmUpto (2 * k)` and
shows that congruence modulo this modulus gives carry-count domination for any
fixed positive base `p`.  It now also defines the paper-style base-restricted
modulus `baseRestrictedPrimePowerModulus k Y`, proves it is positive, proves it
contains every power `p^j <= 2k` for bases `p <= Y`, and derives the optimized
small-prime carry-count domination theorem from congruence modulo that modulus.
It also proves that every prime above the cutoff `Y` is coprime to this
base-restricted modulus, hence to every corresponding prime power `p^J`.

`CentralBinomialLean/LargePrimes.lean` proves the local large-prime
classification: deficit residues are exactly lower carries without central
carries, and surplus residues are exactly central carries without lower carries.
It also contains the finite compensation-count theorem and the medium-prime
carry-count domination wrapper: in the range `2 * k < p^2`, either no level-1
deficit occurs or a later surplus in the Kummer window compensates it.
It defines a semantic bad-residue set modulo `p^J` and proves that avoiding
that set implies the medium-prime good condition.
The semantic bad set is now proved to be contained in the recursively counted
geometric bad-residue tree, yielding the same `(p / 2) * p * (p / 2 + 2)^(J-2)`
bound and its `p >= 8` three-quarters form.
It also lifts these residue counts to interval counts in `[lo, hi)` and proves
finite-prime avoidance/carry-domination theorems from the summed geometric or
three-quarters estimates.  The same three-quarters estimate is now available
along arithmetic progressions `offset + scale * t`, assuming the progression
step is coprime to the relevant `p^J`.

`CentralBinomialLean/Reduction.lean` proves that carry-count domination for
every prime implies the specialized factorial divisibility
`A! * (A + k)! | (2A)! * k!`.

`CentralBinomialLean/Counting.lean` provides deterministic finite counting
infrastructure: if the total size of bad sets is smaller than the universe,
some element avoids every bad set.  It also proves residue-class counting
lemmas for initial segments, translated initial segments, and half-open
intervals `[lo, hi)`: a finite bad residue set `B` modulo `q` captures at most
`B.card * ((hi - lo) / q + 1)` elements of `[lo, hi)`.
It includes finite-family avoidance theorems for residue bad sets with
possibly different moduli, both on ordinary intervals and on arithmetic
progressions `offset + scale * t` when `scale` is coprime to each modulus.

`CentralBinomialLean/Global.lean` packages the verified components.  It defines
finite prime windows, small-prime windows, and medium-prime windows.  It
packages carry-count domination for the small-prime window using the
base-restricted modulus, for primes above `2k` using the `q > 2k` lemma, and
specializes the summed three-quarters bad-residue estimate to medium-prime
windows, including arithmetic-progressions versions.  It proves a
progression-level global endpoint: if a finite medium-prime set covers every
prime between the small cutoff and the automatic `p > 2k` range, and the summed
bad-residue estimate is smaller than the number of progression points, then
some `A = k + baseRestrictedPrimePowerModulus k Y * t` satisfies the central
factorial divisibility.  It also proves the shifted endpoint
`A = k + baseRestrictedPrimePowerModulus k Y * T +
baseRestrictedPrimePowerModulus k Y * y`, `y < N`, which is the paper-shaped
window needed for the final size and logarithmic constraints.  For medium
windows beginning at `Y + 1`, it now supplies the progression coprimality
hypothesis automatically from the cutoff.
It also proves the canonical medium-window cover, the square condition for
the exact cutoff `Y = Nat.sqrt (2 * k)`, and the concrete implication
`25 <= k -> 7 <= Nat.sqrt (2 * k)`.  It also proves a direct end-to-end
central-specialization theorem: if `A ≡ k (mod Nat.lcmUpto (2 * k))`, then
`Nat.choose (A + k) k | Nat.choose (2 * A) A`, hence
`A! * (A + k)! | (2A)! * k!`.  It also proves that for every lower bound `M`
there exists such an `A >= M`.

`CentralBinomialLean/Statement.lean` is the reduction bridge (7 declarations).
It defines the two bridge predicates `centralPairsForTriples` and the
asymptotic `centralLogWindowPairsAt lam`, and proves the central specialization
`a = A`, `b = A + k`, `n = 2A`: a sufficient supply of central pairs with the
right logarithmic inequalities implies unbounded Erdős #728 triples
(`erdos728Main_of_centralLogWindowPairsAt`).  It contains no counting machinery.

`CentralBinomialLean/ParameterSupply.lean` carries the asymptotic machinery and
the final theorem.  The central-pair supply is obtained through a tower of
`…ParameterSupplyAt` predicates and reductions: from
`progressionWindowParameterSupplyAt lam` to the `canonical`, `sqrt`, and
`largeK` specializations (cutoff `Y = Nat.sqrt (2 * k)`, `25 ≤ k`), then the
`shifted` variants (postconditions imposed on a later progression window), and
the split of the bad-residue sum into quotient and tail contributions.  The
chain bottoms out at the core predicate
`shiftedLargeKCoreCeilPowerTailDirectBudgetSubcriticalEndpointWindowParameterSupplyAt`,
discharged for every positive `lam` by the sublinear-growth argument
(`..._of_pos`).  Composing the chain gives the unconditional
`erdos728Main_proved : erdos728Main`.

`CentralBinomialLean/AlternativeRoutes.lean` collects several *alternative*
endpoint routes (the `Effective`, `Numeric`, and `Crude` supply variants and
their wrappers).  They are **not** on the path taken by `erdos728Main_proved`
and are kept separate so the main development stays focused.

## Building and verifying

Prerequisites: `elan`/`lake` with the toolchain pinned in `lean-toolchain`
(`leanprover/lean4:v4.30.0`) and the matching Mathlib (see `lakefile.lean` /
`lake-manifest.json`).

```sh
# Build the whole library (no sorry, no errors expected):
lake build

# Confirm the main theorem depends only on the standard axioms:
echo 'import CentralBinomialLean
open CentralBinomialLean.Erdos728
#print axioms erdos728Main_proved' > /tmp/axcheck.lean
lake env lean /tmp/axcheck.lean
# expected: depends on axioms: [propext, Classical.choice, Quot.sound]
```

The main result is `erdos728Main_proved` in
`CentralBinomialLean/ParameterSupply.lean`.  A reviewer can read the claim in
`CentralBinomialLean/Problem.lean` and the reduction in
`CentralBinomialLean/Statement.lean` without touching the machinery.

## License

Released under the Apache License 2.0; see [`LICENSE`](LICENSE).
