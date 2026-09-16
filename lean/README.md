# Liouville–Goldbach in Lean

This project fully formalizes the assertion that every even integer greater than two is a sum of two positive integers with Liouville value −1. The question was asked on [MathOverflow by the user Pablo in August 2018](https://mathoverflow.net/questions/307479/goldbachs-conjecture-for-the-liouville-function); [Mangerel's paper](https://arxiv.org/abs/2412.17199v1) attributes it to Shusterman. The proof follows the [polished mathematical note](PROOF.md): two commuting symmetries, a symmetric descent, and a small prime which is a quadratic residue.

The final declaration is `LiouvilleGoldbach.liouville_goldbach` in `LiouvilleGoldbach/Main.lean`:

```lean
theorem liouville_goldbach (N : ℕ) (hEven : Even N) (hN : 2 < N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
      ArithmeticFunction.liouville a = -1 ∧
      ArithmeticFunction.liouville b = -1
```

The function is mathlib's `ArithmeticFunction.liouville`, defined for positive `n` as `(-1) ^ cardFactors n`, with prime factors counted with multiplicity. There is no replacement or assumed model of the Liouville function.

## Files

| File | Contents |
|---|---|
| `LiouvilleGoldbach/Completion.lean` | Local inequalities, the upper-band identity, and odd completion. Also retains the earlier residue-case argument for reference. |
| `LiouvilleGoldbach/Commuting.lean` | Replaces the residue cases by a commuting square and disjoint defect supports; proves exact multiplication by 2 and 3. |
| `LiouvilleGoldbach/Descent.lean` | A uniform halving step for both residue classes in the descent. |
| `LiouvilleGoldbach/Coset.lean` | Short representatives for invariant sets and the new half-interval extension proof. |
| `LiouvilleGoldbach/Residue.lean` | A prime square below the half interval and the contradiction from odd multiplicativity. |
| `LiouvilleGoldbach/Extension.lean`, `LiouvilleGoldbach/Character.lean` | Earlier proofs and supporting utilities, retained for comparison. |
| `LiouvilleGoldbach/Reduction.lean` | Reduction from positive pairs at twice primes greater than three to all even integers. |
| `LiouvilleGoldbach/Main.lean` | Instantiation with the actual Liouville function and the final unconditional theorem. |
| `Audit.lean` | Prints the final statement and the axioms used by the principal results. |
| `RouteAudit.lean` | Checks the final theorem's project dependencies: the new ingredients occur and the replaced ingredients are absent. |

The formal proof avoids character classification: multiplicativity makes the function one on nonzero squares. The prime-square lemma also removes the separate deduction that the modulus is 3 modulo 8. The final scaling extracts two prime factors and uses the three explicit pairs at 8, 12, and 18.

## Reproduce

Install Lean through [the official Lean installation guide](https://lean-lang.org/install/). From this directory, run:

```text
lake update
lake exe cache get Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity Mathlib.Tactic
lake build
lake env lean Audit.lean
lake env lean RouteAudit.lean
```

The versions are pinned:

- Lean `v4.34.0-rc2`.
- mathlib commit `de2ef68216c6074f338c8e61890ee0a379ddfb9b`.

`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` record the toolchain and dependencies. The package contains source and dependency metadata; the library cache is downloaded separately.

## Verification results

The final theorem has only the hypotheses displayed above: `N` is even and `2 < N`. The completed audit reports exactly Lean's usual logical foundations:

```text
propext
Classical.choice
Quot.sound
```

These are propositional extensionality, choice, and quotient soundness. They are not assumptions about Liouville–Goldbach. There is no `sorryAx` or custom theorem axiom in the final dependency list. The project's Lean source contains no `sorry`, `admit`, `native_decide`, or `unsafe` declaration.

The actual results are saved in [the build log](verification-build.log), [the axiom audit](verification-axioms.log), and [the proof-route audit](verification-route.log). [The verification record](verification.json) includes the toolchain version, mathlib revision, and SHA-256 hashes of every project Lean source file. The build compiled the changed and new modules from source against the pinned dependencies.

Mangerel's result, GRH, class-number classification, and finite numerical verification are not hypotheses of this development.
