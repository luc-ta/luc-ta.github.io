---
permalink: /commutative-quandles/
title: "Structure theory of commutative quandles"
sitemap: false
date: 2026-01-15
---

## Abstract

In this blogpost, we describe an equivalence of categories between medial Latin (resp. commutative) quandles and affine modules over the ring of integral Laurent polynomials (resp. dyadic rationals). As an application, we obtain structure theorems for finitely generated commutative quandles and finite cancellative midpoint algebras. This solves Questions 7.1 and 7.3 of Bardakov and Elhamdadi \[BE26\].

## 1. Introduction

_Commutative quandles_ and _cancellative midpoint algebras_ are two families of nonassociative algebraic structures appearing in topology. Although these structures originated independently of one another, they coincide in the finite case and turn out to be closely related to affine modules over the ring of dyadic rationals \\(k=\mathbb{Z}[\frac{1}{2}]\\). The purpose of this blogpost is to collect results describing these relationships. In particular, we show that the category of commutative quandles is equivalent to the category of affine modules over the dyadic rationals, and we deduce structure theorems for finitely generated commutative quandles and finite cancellative midpoint algebras. This solves two problems of Bardakov and Elhamdadi \[BE26\].

Joyce \[Jo82\] and Matveev \[Ma82\] independently introduced quandles in 1982 to develop complete invariants of knots. In particular, commutative quandles are important to the theory of certain nonassociative rings called _quandle rings_ \[BE26\]. 
Sigmon \[S70\] introduced cancellative midpoint algebras under the name "medial means" in 1970. Cancellative midpoint algebras allow for categorifications of certain aspects of convex analysis \[ES01, Fr08\], they have connections to (affine) modules over the dyadic rationals \[Ba24, Fr08\].

### 1.1. Definitions

First, we recall definitions coming from nonassociative algebra. Recall that a _magma_ is a set \\(X\\) equipped with a binary operation \\(\ast\colon X\to X\\) called _multiplication_. The cardinality of \\(X\\) is called its _order._ Given magmas \\( (X,\ast_X)\\) and \\( (Y,\ast_Y)\\), functions \\(f\colon X\to Y\\) are called _magma homomorphisms_ if \\(f(w\ast_X x)=f(w)\ast_Y f(x)\\) for all \\(w,x\in X\\). 

Let \\((X,\ast)\\) be a magma. For all \\(x\in X\\), define the _right multiplication_ map \\(R_x\colon X\to X\\) by \\(y\mapsto y\ast x\\), and define the _left multiplication map_ \\(L_x\colon X\to X\\) by \\(y\mapsto x\ast y\\).
* \\(X\\) is called _Latin_ or a _quasigroup_ if for all \\(x\in X\\), the multiplication maps \\(R_x\\) and \\(L_x\\) are permutations.
* \\(X\\) is called a _rack_ if for all \\(x\in X\\), the right multiplication map \\(R_x\\) is a magma automorphism. In particular, the multiplication \\(\ast\\) is right-distributive: \\[(x\ast y)\ast z=(x\ast z)\ast (y\ast z).\\]
* \\(X\\) is called _idempotent_ if \\(x\ast x=x\\) for all \\(x\in X\\).
* A _quandle_ is an idempotent rack.
* Note that the Cartesian product \\(X\times X\\) is a magma. We call \\(X\\) _medial_ if the multiplication \\(\ast\colon X\times X\to X\\) is a magma homomorphism; that is,\\[(w\ast x)\ast(y\ast z)=(w\ast y)\ast(x\ast z)\\] for all \\(w,x,y,z\in X\\). 
* \\(X\\) is called _commutative_ if \\(x\ast y=y\ast x\\) for all \\(x,y\in X\\).
* A _midpoint algebra_ is an idempotent medial commutative magma.
* \\(X\\) is called _cancellative_ if for all \\(x\in X\\), the left multiplication map \\(L_x\\) is injective.

The archetypal example of a quandle is the _conjugation quandle_ of a group \\(G\\), defined to be the pair \\(\mathrm{Conj}(G):=(G,\ast)\\) with \\[g\ast h:=hgh^{-1}.\\] Another important class of quandles are _core quandles_ of groups \\(G\\), defined to be \\(\mathrm{Core}(G):=(G,\ast)\\) with \\[g\ast h:=hg^{-1}h.\\] On the other hand, _Alexander quandles_ are important examples of medial quandles. Given an automorphism \\(\varphi\\) of an abelian group \\(A\\), the Alexander quandle \\(\mathrm{Alex}(A,\varphi)=(A,\ast)\\) is defined by \\[x\ast y:=\varphi(x)+(\mathrm{id}-\varphi)(y).\\] 

### 1.2. Preliminary results

Commutativity turns out to be a very strong condition for quandles. 
The following two lemmas are straightforward and left to the reader.

**Lemma 1.1.** 
* _Every Latin rack is an idempotent quasigroup and, in particular, a quandle._
* _Every commutative rack is Latin and, in particular, a quandle._

**Lemma 1.2** (cf. \[Ba24\])**.** 
* _Every commutative magma is medial._
* _Let \\( (X,\ast)\\) be a finite commutative magma. Then \\(X\\) is cancellative if and only if it is Latin._
* _Commutative quandles are the same as Latin midpoint algebras. In particular, finite commutative quandles are the same as finite cancellative midpoint algebras._

_Remark 1.3._ Infinite cancellative midpoint algebras are not necessarily quasigroups; in particular, Lemma 1.1 implies they are not necessarily quandles. See Remark 2.3 for a counterexample.

The following result requires a more involved argument. In \[BE26\], the authors start with a fixed element \\(x\in X\\) and show that \\(X-\\{x\\}\\) consists of \\(2n\\) elements \\(\\{y_1,\dots,y_n,z_1,\dots,z_n\\}\\) such that \\(z_i\ast y_i=x\\) for all \\(1\leq i\leq n\\).

**Lemma 1.4** (\[BE26, Prop. 5.2\])**.** _The order of every finite commutative quandle is odd._

The following solves part (2) of \[BE26, Question 7.1\]; we solve part (1) in Section 5.

**Proposition 1.5.** Let \\(G\\) be a group. Then: \
(1) \\(\mathrm{Conj}(G)\\) is commutative if and only if \\(G\\) is the trivial group. \
(2) \\(\mathrm{Core}(G)\\) is commutative if and only if the exponent of \\(G\\) is \\(\mathrm{exp}(G)=3\\).

_Proof._ (1): If \\(\mathrm{Conj}(G)\\) is commutative, then \\[g=g\ast e=e\ast g=e\\] for all \\(g\in G\\), so \\(G=\\{e\\}\\). The converse is trivial.

(2): If \\(\mathrm{Core}(G)\\) is commutative, then for all \\(g\in G\\), we have \\[g^2=e\ast g=g\ast e=g^{-1}\\] and, hence, \\(g^3=e\\). Conversely, suppose \\(\mathrm{exp}(G)=3\\). Then for all \\(g,h\in G\\), we have \\( (hg^{-1})^2 = (hg^{-1})^{-1} \\), so \\[ g\ast h= hg^{-1}h=(hg^{-1})^2 g = (hg^{-1})^{-1} g = gh^{-1}g=h\ast g, \\] as desired. QED.

## 2. Averaging quandles

Henceforth, \\(k:=\mathbb{Z}[\frac{1}{2}]\\) denotes the ring of dyadic rationals. All abelian groups are denoted additively.

In this section, we define a class of commutative quandles called _averaging quandles_. The quandles in parts (1) and (2) of \[BE26, Ex. 5.1\] are special classes of averaging quandles. Later, we show that every commutative quandle is isomorphic to an averaging quandle, and every finitely generated commutative quandle canonically decomposes as the Cartesian product of a free commutative averaging quandle and certain finite averaging quandles \\(C_{2n+1}\\).

**Definition 2.1.** Let \\(A\\) be a unital ring in which \\(2\\\) is invertible, and let \\(M\\) be a left \\(A\\)-module. Define a quandle operation on \\(M\\) by averaging: \\[x\ast y:=\frac{1}{2}(x+y).\\] Then \\( M_{\mathrm{avg}}:=(M,\ast) \\) is a commutative quandle called the _averaging quandle_ on \\(M\\). 

In particular, if \\(M=\mathbb{Z}/(2n+1)\mathbb{Z}\\) is the cyclic group of order \\(2n+1\\) with \\(n\geq 0\\), then we denote the averaging quandle by \\(C\_{2n+1}:=M\_{\mathrm{avg}}\\). Since \\(2^{-1}=n+1\\) in \\(M\\), this definition of \\(C_{2n+1}\\) coincides with the one from \[BE26\].

_Remark 2.2._ Averaging quandles are a special class of Alexander quandles. Indeed, if \\( M_{\mathrm{avg}}\\) is an averaging quandle and \\(\varphi\\) denotes multiplication by \\(1/2\\), then \\(M_{\mathrm{avg}}=\mathrm{Alex}(M,\varphi)\\). In general, though, Alexander quandles are not necessarily commutative.

_Remark 2.3._ Contrary to Example 5.1(3) and Question 7.3 of \[BE26\], the subset \\(X:=\\{n/2^k \mid n,k\in\mathbb{Z}_{\geq 0}\\}\subset k\\) is not a subquandle of \\(k\_{\mathrm{avg}}\\). Indeed, the right multiplication map \\( R_1\\) does not restrict to a permutation of \\(X\\).

## 3. Medial Latin quandles

We completely describe medial Latin quandles and commutative quandles. The following results were already shown in \[Ba24, JPSZ15\]; we provide new, much shorter proofs at the cost of appealing to the Bruck–Murdoch–Toyoda theorem.

Recall from Lemmas 1.1 and 1.2 that every commutative quandle is medial and Latin, and every Latin quandle is a quasigroup. These observations allow us to use the _Bruck–Murdoch–Toyoda theorem_, which states the following: For every medial quasigroup \\( (X,\ast)\\), there exists an abelian group \\(A\\), a fixed element \\(c\in A\\), and two commuting automorphisms \\(\varphi,\psi\\) of \\(A\\) such that \\(X\\) is isomorphic to the medial quasigroup \\( (A,\cdot)\\), where \\[a\cdot b := \varphi(a)+\psi(b)+c\\] for all \\(a,b\in A\\).

**Theorem 3.1** (\[JPSZ15, Ex. 2.2 and Cor. 3.4\])**.** _Every medial Latin quandle is isomorphic to an Alexander quandle \\(\mathrm{Alex}(A,\varphi)\\) such that \\(\mathrm{id}-\varphi\\) is a permutation of \\(A\\)._

_Proof._ By the above discussion, every medial Latin quandle is isomorphic to a quasigroup of the form \\( (A,\cdot)\\) described above. By assumption, \\( (A,\cdot)\\) is idempotent, so taking \\(a:=0\\) and \\(b:=0\\) above shows that \\(c=0\\). Therefore, idempotence forces \\(\varphi+\psi=\mathrm{id}\\). That is, \\[a\cdot b=\varphi(a)+(\mathrm{id}-\varphi)(b),\\] so \\( (A,\cdot)=\mathrm{Alex}(A,\varphi),\\) as desired. Finally, since \\( (A,\cdot)\\) is Latin, the left multiplication maps \\(L_a=\varphi(a)+\mathrm{id}-\varphi\\) are invertible. Since addition by \\(\varphi(a)\\) is invertible, it follows that \\(\mathrm{id}-\varphi\\) is also invertible. QED.

**Theorem 3.2** (\[Ba24\])**.** _Every commutative quandle is isomorphic to an averaging quandle._

_Proof._ By Theorem 3.1, every commutative quandle is isomorphic to an Alexander quandle \\( \mathrm{Alex}(A,\varphi) \\). Commutativity implies that \\[\varphi(a)=a\ast 0=0\ast a=a-\varphi(a)\\] for all \\(a\in A\\); that is, \\(2\varphi=\mathrm{id}\\). Since \\(\varphi\\) is invertible, it follows that multiplication by \\(2\\) is invertible. Hence, \\(A\\) is a \\(k\\)-module, and \\(\varphi\\) is multiplication by \\(1/2\\). QED.

_Remark 3.3._ The "converses" of Theorems 3.1 and 3.2 also hold. Precisely, every Alexander quandle \\(\mathrm{Alex}(A,\varphi)\\) is medial, and if \\(\mathrm{id}-\varphi\\) is invertible, then \\(\mathrm{Alex}(A,\varphi)\\) is also Latin. Moreover, every averaging quandle is commutative.

In light of Lemma 1.2, the construction of Bauer \[Ba24\] can be viewed as a way to recover the averaging quandle corresponding to a given commutative quandle under Theorem 3.2. Although we will not use this construction, it is worth recording in our notation. Namely, given a nonempty commutative quandle \\( (X,\ast)\\), fix a basepoint \\(0\in X\\). Bauer showed that the following operations define a \\(k\\)-module structure on \\(X\\) such that \\(0\\) is the additive identity and \\(X_{\mathrm{avg}}\cong(X,\ast)\\):

$$
    \begin{aligned}
    x+y&:= R_0^{-1}(x\ast y), \\
   -x &:= R_x^{-1}(0),\\
   \frac{x}{2}&:= 0\ast x.
    \end{aligned}
    $$

The following example gives an alternative but equivalent construction in a special case. Given a set \\(X\\), let \\(k^{(X)}:=\bigoplus_{x\in X}k\\) denote the free \\(k\\)-module generated by \\(X\\).

**Example 3.4.** Given a nonempty set \\(X\\), consider the affine hull \\(H_X\\) of \\(X\\) in \\(k^{(X)}\\): \\[H_X:= \left\\{\sum^n_{i=1}\lambda_i x_i: n\geq 1,\, \lambda_i\in k,\, x_i\in X,\, \sum^n_{i=1}\lambda_i=1 \right\\}\subset k^{(X)}.\\] Then \\(H_X\\) is a subquandle of the averaging quandle \\( (k^{(X)})_{\mathrm{avg}}\\). 
To write \\(H_X\\) itself as an averaging quandle, fix a basepoint \\(x_0\in X\\), and consider the map

$$
    \begin{aligned}
    H_X & \to (k^{(X-\{x\})})_{\mathrm{avg}} \\
   \sum^n_{i=0}\lambda_i x_i &\mapsto \sum^n_{i=1}\lambda_i x_i.
    \end{aligned}
    $$

The reader can check that this map is a quandle isomorphism. In particular, if \\(\\# X=n+1\\) with \\(n\geq 0\\) a nonnegative integer, then we obtain a quandle isomorphism \\(H_X\cong k^n_{\mathrm{avg}}\\).

## 4. Equivalences of categories

Theorems 3.1 and 3.2 allow us to give an alternative perspective on the classification of medial Latin quandles and commutative quandles. In the following, let \\(\mathsf{AffMod}\_{k}\\) be the category whose objects are \\(k\\)-modules and whose morphisms are affine transformations (that is, sums of \\(k\\)-linear maps and constant functions).[^1] Let \\(\mathsf{CommQnd}\\) be the category of commutative quandles and quandle homomorphisms.

Attempt to define a functor \\(\mathrm{avg}\colon \mathsf{AffMod}_{k}\to \mathsf{CommQnd}\\) on objects by sending every \\(k\\)-module \\(M\\) to its averaging quandle \\(M\_{\mathrm{avg}}\\). Define the action on morphisms to be \\(f\mapsto f-f(0).\\)

**Proposition 4.1.** _\\(\mathrm{avg}\\) is a functor._

_Proof._ By direct computation. QED.

**Proposition 4.2.** _\\(\mathrm{avg}\\) is fully faithful._

_Proof._ Faithfulness is straightforward. To show fullness, let \\(M\\) and \\(N\\) be \\(k\\)-modules, and let \\(f\colon M_{\mathrm{avg}}\to N_{\mathrm{avg}}\\) be a quandle homomorphism. Define \\(T\colon M\to N\\) by \\(T:= f-f(0)\\). It suffices to show that \\(T\\) is \\(k\\)-linear, since then \\(f=\mathrm{avg}(T+f(0))\\). 

Certainly, \\(T(0)=0\\). Since \\(f\\) is a quandle homomorphism, it is easy to see that \\(T\\) is also a quandle homomorphism. In particular, \\(T(x/2)=T(x\ast 0)=T(x)/2\\) for all \\(x\in M\\), so \\[T(x+y)=2T\left(\frac{x+y}{2}\right)=2T(x\ast y)=2(T(x)\ast T(y))=T(x)+T(y)\\] for all \\(x,y\in M\\). In particular, we deduce that \\[T(nx)=nT(x)\\] for all \\(n\in\mathbb{Z}\\). Thererfore, it suffices to show that \\(T(x/2^k)=T(x)/2^k\\) for all \\(x\in M\\) and \\(k\geq 1\\); this follows by induction on \\(k\\). QED.

Combined with Theorem 3.2, Propositions 4.1 and 4.2 show the following.

**Theorem.** _\\(\mathrm{avg}\\) is an equivalence of categories._

## Structure theorems

**Theorem.** 

### Footnotes

Footnotes can be useful for clarifying points in the text, or citing information. Markdown support numeric footnotes, as well as text as long as the values are unique.[^note]

```markdown
This is the regular text.[^1] This is more regular text.[^note]

[^1]: This is the footnote itself.
[^note]: This is another footnote.
```

[^1]: There are many equivalent ways to define the category of affine modules over a commutative ring. The reader can verify that when the ground ring is \\(k\\), then our definition is equivalent to these other ways.
[^note]: When using text for footnotes markers, no spaces are permitted in the name.

## References

\[Ba24\] K. J. Bauer, _quasigroup midpoint algebras = Z[1/2]-modules,_ Frank Blog, 2024. [https://frank-9976.github.io/midpoint.html](https://frank-9976.github.io/midpoint.html) (accessed: 1-14-2026).

\[BE26\] V. Bardakov and M. Elhamdadi. _Idempotents and powers of ideals in quandle rings,_ 2026. arXiv:2601.07057

\[ES01\] M. H. Escardo and A. K. Simpson, _A universal characterization of the closed Euclidean interval._ Proc. 16th Annual IEEE Symposium on Logic in Comp. Sci. (2001), 115–125. doi:10.1109/LICS.2001.932488.

\[Fr08\] P. Freyd, _Algebraic real analysis,_ Theory Appl. Categ. **20** (2008), no. 10, 215–306. MR2425550

\[JPSZ15\] P. Jedlička, A. Pilitowska, D. Stanovský, and A. Zamojska-Dzienio, _The structure of medial quandles,_ J. Algebra **443** (2015), 300–334. MR3400403

\[Jo82\] D. Joyce, _A classifying invariant of knots, the knot quandle,_ J. Pure Appl. Algebra **23** (1982), no. 1, 37–65. MR638121

\[Ma82\] S. V. Matveev, _Distributive groupoids in knot theory,_ Mat. Sb. (N.S.) **119**(161) (1982), no. 1, 78–88, 160. MR672410

\[Si70\] K. Sigmon. _Cancellative medial means are arithmetic,_ Duke Math J. **37** (1970), 439–445. MR274644

***
**Footnotes**

The footnotes in the page will be returned following this line, return to the section on <a href="#footnotes">Markdown Footnotes</a>.
