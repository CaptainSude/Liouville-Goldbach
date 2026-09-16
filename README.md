# A Goldbach theorem for the Liouville function

**[Read the paper](paper/liouville-goldbach.pdf)** · [LaTeX source](paper/liouville-goldbach.tex) · [Lean proof and verification](lean/README.md)

Every even integer greater than two is a sum of two positive integers, each with an odd number of prime factors counted with multiplicity. Equivalently, for every even $N>2$, there are $a,b\geq 1$ such that

$$N=a+b,\qquad \lambda(a)=\lambda(b)=-1.$$

The paper gives an elementary proof through two commuting symmetries, a descent, and quadratic reciprocity. The complete argument is formalized in Lean using mathlib's Liouville function.

The question was asked on [MathOverflow by the user Pablo in August 2018](https://mathoverflow.net/questions/307479/goldbachs-conjecture-for-the-liouville-function). [Mangerel's paper](https://arxiv.org/abs/2412.17199v1) attributes it to Shusterman. The paper discusses previous results and credits the ideas used in the proof, including Bloom's scaling observation and Mangerel's rigidity and commuting-defect arguments.

## Read and verify

| Contents | Location |
|---|---|
| Paper and editable source | [`paper/`](paper/) |
| Complete formal proof and build instructions | [`lean/`](lean/) |
| Final theorem | [`lean/LiouvilleGoldbach/Main.lean`](lean/LiouvilleGoldbach/Main.lean) |
| Short mathematical proof outline | [`lean/PROOF.md`](lean/PROOF.md) |
| Recorded local verification | [`lean/verification.json`](lean/verification.json) |
| Axiom audit | [`lean/verification-axioms.log`](lean/verification-axioms.log) |
| Proof-route audit | [`lean/verification-route.log`](lean/verification-route.log) |

The final declaration is `LiouvilleGoldbach.liouville_goldbach`:

```lean
theorem liouville_goldbach (N : ℕ) (hEven : Even N) (hN : 2 < N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧
      ArithmeticFunction.liouville a = -1 ∧
      ArithmeticFunction.liouville b = -1
```

The source is pinned to Lean `v4.34.0-rc2` and mathlib commit `de2ef68216c6074f338c8e61890ee0a379ddfb9b`. The recorded build, axiom audit, and proof-route audit passed. The final theorem uses only `propext`, `Classical.choice`, and `Quot.sound`; the audit contains no unfinished proof or additional mathematical axiom.

The included logs record local verification. After the verification workflow is installed, the **Actions** tab records a fresh build and both audits for each uploaded commit.
