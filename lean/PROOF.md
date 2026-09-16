# Liouville–Goldbach: a proof through two commuting symmetries

Let \(\lambda(n)=(-1)^{\Omega(n)}\), where prime factors are counted with multiplicity.

**Theorem.** Every even integer \(N>2\) is the sum of two positive integers on which \(\lambda\) is negative.

The proof turns a missing sum into a multiplicative structure. Its two main ingredients are a commuting-square argument, which makes two local symmetries exact, and a descent, which extends short multiplicativity to an entire prime field.

**1. A missing sum forces two exact symmetries.**

Fix a prime \(p>3\). Suppose that \(2p\) has no representation \(a+b\) with \(\lambda(a)=\lambda(b)=1\), and write \(f=\lambda\).

There is then no negative-negative pair summing to \(p\), since doubling it would give a positive-positive pair summing to \(2p\). These two exclusions, together with \(f(2n)=f(3n)=-f(n)\), give
\[
f(p-n)\ge-f(n),\qquad f(p+n)\le f(n)
\quad(0<n<p),
\tag{1}
\]
and
\[
f(p-2n)\ge f(n)\qquad(0<n<p/2).
\tag{2}
\]
Indeed, the second inequality in (1) follows by applying the two exclusions successively; (2) follows from \(2p=4n+2(p-2n)\). All inequalities compare the signs \(-1\) and \(1\).

For \(p/3<n<p/2\), put \(u=p-2n\) and \(v=3n-p\). The identities
\[
2p=4n+2u,\qquad 3n=p+v,\qquad p=3u+2v
\]
give a closed chain of inequalities:
\[
-f(n)\le f(v)\le-f(u)\le-f(n).
\]
Consequently
\[
f(n)=f(p-2n)=-f(3n-p)
\qquad(p/3<n<p/2).
\tag{3}
\]

Now extend the lower half of \(f\) oddly to \(\mathbb F_p\): set \(G(0)=0\), and, for the unique integer representative \(-p/2<t<p/2\) of a nonzero residue, set
\[
G(t)=\operatorname{sgn}(t)f(|t|).
\]
Thus \(G(1)=1\), \(G(-x)=-G(x)\), and \(G(n)=f(n)\) when \(0<n<p/2\).

Measure the failures of invariance under multiplication by \(-2\) and \(-3\):
\[
A(x)=G(-2x)-G(x),\qquad B(x)=G(-3x)-G(x).
\]
Both are odd. For positive central representatives, put
\[
Q=(p/4,p/3),\qquad M=(p/6,p/3).
\]
The local doubling and tripling identities, (1)–(3), give this simple picture:

| Positive representative \(n\) | \((0,p/6)\) | \((p/6,p/4)\) | \(Q=(p/4,p/3)\) | \((p/3,p/2)\) |
|---|---:|---:|---:|---:|
| \(A(n)\) | \(0\) | \(0\) | \(\ge0\) | \(0\) |
| \(B(n)\) | \(0\) | \(\ge0\) | \(A(n)\) | \(0\) |

Here is the calculation behind these assertions. On \(Q\),
\(A(n)=f(p-2n)-f(n)\ge0\); outside \(Q\), local doubling or (3) gives zero. On \(M\),
\(B(n)=f(p-3n)-f(n)\ge0\), by reflection applied to \(3n\); outside \(M\), local tripling or (3) gives zero. Finally, if \(n\in Q\), apply (3) to \(u=p-2n\):
\[
f(p-2n)=-f(2(p-3n))=f(p-3n),
\]
which proves \(A(n)=B(n)\). None of the interval endpoints is an integer, since \(p>3\) is prime.

The two multiplications commute, so their failures satisfy the single identity
\[
\boxed{A(-3x)+B(x)=B(-2x)+A(x).}
\tag{4}
\]
If \(p/6<n<p/4\), then \(A(n)=0\) and \(B(-2n)=0\), whereas the central representative of \(-3n\) is the positive integer \(p-3n\). Both terms on the left of (4) are therefore nonnegative and their sum is zero. Hence \(B(n)=0\). Together with the preceding assertions and oddness, this proves \(A=B\) everywhere.

It follows that \(G(2x)=G(3x)\), so both \(G\) and \(A\) are invariant under multiplication by \(2/3\). If \(A\) were nonzero, oddness would give \(A(n)>0\) for some positive central representative \(n\in Q\). The central representative \(m\) of \(2n/3\) also has \(A(m)>0\). It must be positive, by oddness and nonnegativity on positive representatives, and it must lie in \(Q\). But then
\[
3m\equiv2n\pmod p,\qquad 0<3m-2n<p,
\]
an impossibility. Thus \(A=B=0\), proving simultaneously
\[
\boxed{G(2x)=-G(x),\qquad G(3x)=-G(x).}
\tag{5}
\]

**2. Short multiplicativity extends to the whole field.**

We isolate the arithmetic reason this is possible.

**Short-representative lemma.** Let \(H\) be a proper subgroup of \(\mathbb F_p^\times\) containing \(-1,2,3\), and let \(q\) be the least positive integer whose residue is outside \(H\). Every multiplicative coset of \(H\) has a positive integer representative smaller than \(p/(2q)\).

**Proof.** The integer \(q\) is prime, since a factorization into smaller positive integers would put it in \(H\). Also \(5\le q<p/2\), because \(1,2,3\in H\), and every residue is represented up to sign below \(p/2\).

Take the smallest positive integer representative \(n\) of a coset. Negation gives \(n<p/2\); minimality and \(2\in H\) force \(n\) to be odd. If \(n=1\), the required bound is immediate. Otherwise \(1<n<p\), so \(n\nmid p\). Suppose that \(2qn\ge p\); equality is impossible.

If \(p<(2q-1)n\), choose an even integer \(a\) nearest to \(p/n\). Then
\[
2\le a\le2q-2,\qquad 0<|p-an|<n.
\]
The inequalities are strict because \(1<n<p\) and \(p\) is prime. Since \(a=2j\) with \(j<q\), its residue belongs to \(H\); hence \(|p-an|\) is a smaller representative of the same coset, a contradiction.

We are left with
\[
(2q-1)n<p<2qn.
\]
Choose the one of \(a=2q-1\) and \(a=2q+1\) that is divisible by \(3\). It has the form \(a=3j\) with \(0<j<q\), so again \(a\in H\). Now \(a,n,p\) are all odd, and
\[
0<|p-an|<2n.
\]
Therefore
\[
\boxed{\frac{|p-an|}{2}}
\]
is a positive integer smaller than \(n\), in the same coset. This is the final contradiction. \(\square\)

**Extension lemma.** Let \(F:\mathbb F_p^\times\to\{\pm1\}\) satisfy \(F(1)=1\). Suppose multiplication by \(-1,2,3\) is exact:
\[
F(cx)=F(c)F(x)\qquad(c=-1,2,3),
\]
and suppose
\[
F(ab)=F(a)F(b)\qquad(a,b\ge1,\ ab<p/2).
\]
Then \(F\) is multiplicative everywhere.

**Proof.** Let \(H\) consist of the residues \(c\) for which \(F(cx)=F(c)F(x)\) for every \(x\). Composition and inversion show that \(H\) is a subgroup. If it is proper, let \(q\) be its least missing positive integer. The function
\[
D(x)=\frac{F(qx)}{F(q)F(x)}
\]
is constant on each coset of \(H\). The short-representative lemma supplies in every coset an integer \(n<p/(2q)\); short multiplicativity gives \(D(n)=1\). Thus \(D=1\) everywhere, which says \(q\in H\), a contradiction. \(\square\)

Our completed function \(G\) satisfies the extension lemma: (5) supplies the exact multipliers, oddness supplies \(-1\), and complete multiplicativity of \(\lambda\) supplies short multiplicativity. Therefore \(G\) is multiplicative on \(\mathbb F_p^\times\).

**3. A small prime square gives the contradiction.**

We need only this elementary consequence of quadratic reciprocity:

**Small-prime lemma.** If \(p>3\) is prime and \(p\equiv3\pmod4\), some prime \(\ell<p/2\) is a square modulo \(p\).

**Proof.** Choose any prime divisor \(\ell\) of \(L=(p+1)/4>1\). Certainly \(\ell\le L<p/2\). If \(\ell=2\), then \(p\equiv7\pmod8\), so \(2\) is a square modulo \(p\). If \(\ell\) is odd, quadratic reciprocity gives
\[
\left(\frac{\ell}{p}\right)
=\left(\frac{-p}{\ell}\right)
=\left(\frac{1}{\ell}\right)=1,
\]
because \(p\equiv-1\pmod\ell\). \(\square\)

Since \(G\) is a multiplicative sign function, it equals \(1\) on every nonzero square. But \(G(-1)=-1\), so \(-1\) is not a square and \(p\equiv3\pmod4\). Take the prime \(\ell\) from the lemma. Agreement with \(\lambda\) below \(p/2\) gives the contradiction
\[
1=G(\ell)=\lambda(\ell)=-1.
\]
We have proved that every prime \(p>3\) admits
\[
2p=u+v,\qquad u,v>0,\qquad \lambda(u)=\lambda(v)=1.
\tag{6}
\]

**4. Two prime factors finish the proof.**

Write \(N=2m>2\). If \(\lambda(m)=-1\), use \(m+m\). Otherwise \(m\) has a positive even number of prime factors, counted with multiplicity. Extract two of them:
\[
m=rsc,\qquad r,s\text{ prime},\qquad \lambda(c)=1.
\]
If one, say \(r\), exceeds \(3\), multiply the positive-positive pair at \(2r\) from (6) by \(sc\), whose Liouville sign is negative. This gives the required negative-negative pair at \(N\).

Otherwise \(r,s\in\{2,3\}\), and \(2rs\) is one of \(8,12,18\). Multiply the corresponding identity
\[
8=3+5,\qquad 12=5+7,\qquad 18=7+11
\]
by \(c\). Its positive Liouville sign preserves the negative signs of both summands. \(\square\)

---

**Verification.** The full theorem, following this new route, has been verified in Lean. The [source and reproduction instructions](README.md) include the commuting argument, symmetric descent, invariant-set extension, and small-prime lemma. The [axiom audit](verification-axioms.log) reports only Lean's standard logical foundations. A separate [dependency audit](verification-route.log) checks that the final proof uses the new ingredients and does not depend on the replaced residue-case or extension proofs.

The argument uses the standard square criteria and quadratic reciprocity. This is a polished proof-development note; literature positioning and the paper remain separate work.
