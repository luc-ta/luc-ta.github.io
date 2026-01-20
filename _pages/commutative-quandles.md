---
permalink: /blog/2026/commutative-quandles/
title: "Structure theory of commutative quandles"
sitemap: false
date: 2026-01-15
redirect_from: /commutative-quandles/
---

## Abstract

In this blogpost, we solve Question 7.1 and partially solve Question 7.3 of Bardakov and Elhamdadi \[BE26\]. In particular, non-medial commutative quandles obstruct a conjectural structure theorem of \[_op. cit._\]. However, assuming mediality makes the conjecture hold; we deduce this from an equivalence of categories between commutative (resp. Latin) medial quandles and affine modules over the ring of dyadic rationals (resp. integral Laurent polynomials).

## 1. Introduction

_Commutative quandles_ and _cancellative midpoint algebras_ are two families of nonassociative algebraic structures appearing in topology. Although these structures originated independently of one another, they coincide in the finite case and turn out to be closely related to affine modules over the ring of dyadic rationals \\(k=\mathbb{Z}[\frac{1}{2}]\\). The purpose of this blogpost is to collect results describing these relationships. In particular, we show that the category of commutative quandles is equivalent to the category of affine modules over the dyadic rationals, and we deduce structure theorems for finitely generated commutative quandles and finite cancellative midpoint algebras. This solves two problems of Bardakov and Elhamdadi \[BE26\].

Joyce \[Jo82\] and Matveev \[Ma82\] independently introduced quandles in 1982 to develop complete invariants of knots. In particular, commutative quandles are important to the theory of certain nonassociative rings called _quandle rings_ \[BE26\]. 
Sigmon \[S70\] introduced cancellative midpoint algebras under the name "medial means" in 1970. Cancellative midpoint algebras allow for categorifications of certain aspects of convex analysis \[ES01, Fr08\], they have connections to (affine) modules over the dyadic rationals \[Ba24, Fr08\].

## 2. Preliminaries

### 2.1. Definitions

First, we recall definitions coming from nonassociative algebra. Recall that a _magma_ is a set \\(X\\) equipped with a binary operation \\(\ast\colon X\to X\\) called _multiplication_. The cardinality of \\(X\\) is called its _order._ Given magmas \\( (X,\ast_X)\\) and \\( (Y,\ast_Y)\\), functions \\(f\colon X\to Y\\) are called _magma homomorphisms_ if \\(f(w\ast_X x)=f(w)\ast_Y f(x)\\) for all \\(w,x\in X\\). 

Let \\((X,\ast)\\) be a magma. For all \\(x\in X\\), define the _right multiplication_ map \\(R_x\colon X\to X\\) by \\(y\mapsto y\ast x\\), and define the _left multiplication map_ \\(L_x\colon X\to X\\) by \\(y\mapsto x\ast y\\).
* \\(X\\) is called a _Latin_ or a _left quasigroup_ if for all \\(x\in X\\), the left multiplication map \\(L_x\\) is invertible. If in addition the right multiplication maps \\(L_x\\) are all invertible, then we call \\(X\\) a _quasigroup_.
* \\(X\\) is called a _rack_ if for all \\(x\in X\\), the right multiplication map \\(R_x\\) is a magma automorphism. In particular, the multiplication \\(\ast\\) is right-distributive: \\[(x\ast y)\ast z=(x\ast z)\ast (y\ast z).\\]
* \\(X\\) is called _idempotent_ if \\(x\ast x=x\\) for all \\(x\in X\\). 
* A _quandle_ is an idempotent rack. A _kei_ is a quandle such that all right multiplication maps \\(R_x\\) are involutions.
* Note that the Cartesian product \\(X\times X\\) is a magma. We call \\(X\\) _medial_ if the multiplication \\(\ast\colon X\times X\to X\\) is a magma homomorphism; that is,\\[(w\ast x)\ast(y\ast z)=(w\ast y)\ast(x\ast z)\\] for all \\(w,x,y,z\in X\\). 
* \\(X\\) is called _commutative_ if \\(x\ast y=y\ast x\\) for all \\(x,y\in X\\).
* A _midpoint algebra_ is an idempotent medial commutative magma.
* \\(X\\) is called _cancellative_ if for all \\(x\in X\\), the left multiplication map \\(L_x\\) is injective.
* \\(X\\) is called _distributive_ if for all \\(x\in X\\), the left and right multiplication maps \\(L_x,R_x\\) are magma endomorphisms.

The prototypical example of a quandle is the _conjugation quandle_ of a group \\(G\\), defined to be the pair \\(\mathrm{Conj}(G):=(G,\ast)\\) with \\[g\ast h:=hgh^{-1}.\\] Another important class of quandles are _core quandles_ of groups \\(G\\), defined to be \\(\mathrm{Core}(G):=(G,\ast)\\) with \\[g\ast h:=hg^{-1}h.\\] On the other hand, _Alexander quandles_ are important examples of medial quandles. Given an automorphism \\(\varphi\\) of an abelian group \\(A\\), the Alexander quandle \\(\mathrm{Alex}(A,\varphi)=(A,\ast)\\) is defined by \\[x\ast y:=\varphi(x)+(\mathrm{id}-\varphi)(y).\\] 

### 2.2. Preliminary results

Commutativity turns out to be a very strong condition for quandles. 
The following lemma is straightforward and left to the reader.

**Lemma 2.1.** 
* _Every Latin rack is an idempotent quasigroup and, in particular, a quandle._ 
* _Every commutative rack is distributive and Latin—in particular, a quasigroup and a quandle._
* _Every distributive quasigroup is a Latin quandle._

**Lemma 2.2** (cf. \[Ba24\])**.** 
* _Let \\( (X,\ast)\\) be a finite commutative magma. Then \\(X\\) is cancellative if and only if it is Latin._
* _Medial commutative quandles are the same as Latin midpoint algebras. In particular, finite medial commutative quandles are the same as finite cancellative midpoint algebras._

_Remark 2.3._ Infinite cancellative midpoint algebras are not necessarily quasigroups; in particular, Lemma 2.1 implies they are not necessarily quandles. See Remark 3.3 for a counterexample.

The following result requires a more involved argument. In \[BE26\], the authors start with a fixed element \\(x\in X\\) and show that \\(X-\\{x\\}\\) consists of \\(2n\\) elements \\(\\{y_1,\dots,y_n,z_1,\dots,z_n\\}\\) such that \\(z_i\ast y_i=x\\) for all \\(1\leq i\leq n\\).

**Lemma 2.4** (\[BE26, Prop. 5.2\])**.** _The order of every finite commutative quandle is odd._

The following solves part (2) of \[BE26, Question 7.1\]; we answer parts (1) and (3) in Section 3.2 and Corollary 4.2, respectively.

**Proposition 2.5.** Let \\(G\\) be a group. Then: \
(1) \\(\mathrm{Conj}(G)\\) is commutative if and only if \\(G\\) is the trivial group. \
(2) \\(\mathrm{Core}(G)\\) is commutative if and only if the exponent of \\(G\\) is \\(\mathrm{exp}(G)=3\\).

_Proof._ (1): If \\(\mathrm{Conj}(G)\\) is commutative, then \\[g=g\ast e=e\ast g=e\\] for all \\(g\in G\\), so \\(G=\\{e\\}\\). The converse is trivial.

(2): If \\(\mathrm{Core}(G)\\) is commutative, then for all \\(g\in G\\), we have \\[g^2=e\ast g=g\ast e=g^{-1}\\] and, hence, \\(g^3=e\\). Conversely, suppose \\(\mathrm{exp}(G)=3\\). Then for all \\(g,h\in G\\), we have \\( (hg^{-1})^2 = (hg^{-1})^{-1} \\), so \\[ g\ast h= hg^{-1}h=(hg^{-1})^2 g = (hg^{-1})^{-1} g = gh^{-1}g=h\ast g, \\] as desired. QED.

## 3. Commutative quandles

Henceforth, \\(k:=\mathbb{Z}[\frac{1}{2}]\\) denotes the ring of dyadic rationals. All abelian groups are denoted additively.

### 3.1. Averaging quandles

In this section, we define a class of commutative quandles called _averaging quandles_. The quandles in parts (1) and (2) of \[BE26, Ex. 5.1\] are special classes of averaging quandles. Later, we show that every commutative quandle is isomorphic to an averaging quandle, and every finitely generated commutative quandle canonically decomposes as the Cartesian product of a free commutative averaging quandle and certain finite averaging quandles \\(C_{2n+1}\\).

**Definition 3.1.** Let \\(A\\) be a unital ring in which \\(2\\\) is invertible, and let \\(M\\) be a left \\(A\\)-module. Define a quandle operation on \\(M\\) by averaging: \\[x\ast y:=\frac{1}{2}(x+y).\\] Then \\( M_{\mathrm{avg}}:=(M,\ast) \\) is a commutative quandle called the _averaging quandle_ on \\(M\\). 

In particular, if \\(M=\mathbb{Z}/(2n+1)\mathbb{Z}\\) is the cyclic group of order \\(2n+1\\) with \\(n\geq 0\\), then we denote the averaging quandle by \\(C\_{2n+1}:=M\_{\mathrm{avg}}\\). Since \\(2^{-1}=n+1\\) in \\(M\\), this definition of \\(C_{2n+1}\\) coincides with the one from \[BE26\].

_Remark 3.2._ Averaging quandles are a special class of Alexander quandles; in particular, all averaging quandles are medial. Indeed, if \\( M_{\mathrm{avg}}\\) is an averaging quandle and \\(\varphi\\) denotes multiplication by \\(1/2\\), then \\(M_{\mathrm{avg}}=\mathrm{Alex}(M,\varphi)\\). In general, though, Alexander quandles are not necessarily commutative.

_Remark 3.3._ Contrary to Example 5.1(3) and Question 7.3 of \[BE26\], the subset \\(X:=\\{n/2^k \mid n,k\in\mathbb{Z}_{\geq 0}\\}\subset k\\) is not a subquandle of \\(k\_{\mathrm{avg}}\\). Indeed, the right multiplication map \\( R_1\\) does not restrict to a permutation of \\(X\\).

### 3.2. An obstruction to structure theorems

In 2026, Bardakov and Elhamdadi \[BE26, Question 7.1\] asked whether every finite commutative quandle can be written as a direct product of averaging quandles of the form \\(C_{2n+1}\\). In this section, we show that the question has a negative answer. Later in this blogpost, we give an additional assumption (viz. mediality) under which this question has a positive answer.

To give a negative answer to \[BE26, Question 7.1\], it suffices to construct a finite commutative quandle that is not medial. This is due to Remark 3.2 and the fact that the direct product of medial quandles is necessarily medial. Indeed, such quandles have already appeared in the literature. In 1981, Kepka and Němec \[KN81, Thm. 12.4\] (see \[St15A, Ex. 3.4\]) constructed non-medial distributive quasigroups (hence quandles by Lemma 2.1) of order 81. (They also showed that these are the smallest such examples.) Of their constructions, the following is in fact a commutative quandle. 

Given an abelian group \\(A\\) and a function \\(f\colon A^3\to A\\), we say that \\(f\\) is _triadditive_ if for all \\(x,y\in A\\), the restrictions \\(f(-,x,y)\\), \\(f(x,-,y)\\), and \\(f(x,y,-)\\) are endomorphisms of \\(A\\). In particular, let \\(A:= (\mathbb{Z}/3\mathbb{Z})^4\\), and let \\(e_1,e_2,e_3,e_4\\) be the canonical generators of \\(A\\). Define a triadditive function \\(f\\) via 

$$ f(e_i,e_j,e_k) = \begin{cases} e_1, & (i,j,k)=(2,3,4)\\ -e_1, & (i,j,k)=(3,2,4)\\ 0, & \text{otherwise.} \end{cases}$$

Make \\(A\\) into a _commutative Moufang loop_ via the operation \\[x\cdot y:=x+y+f(x,y,x-y).\\] (This commutative Moufang loop is called \\(L(1)\\) in \[KN81\] and \\((G_1,\cdot)\\) in \[St15A\].) 
Then \\(A\\) is a quandle with respect to the operation \\[x\ast y := (-x)\cdot(-y).\\] (This quandle is called \\(D(1)\\) in \[KN81\].) Since \\((A,\cdot)\\) is commutative, it follows that \\((A,\ast)\\) is also commutative.

Although it is already shown in \[KN81\] that \\((A,\ast)\\) is not medial, we provide a direct verification for the reader's convenience:

$$
    \begin{aligned}
    (\mathbf{0}\ast e_4) \ast (e_3\ast e_2) & = (-e_4) \ast -(e_2+e_3) \\
   &= e_2+e_3+e_4 \\
  &\neq e_1+e_2+e_3+e_4 \\
  &= (-e_3) \ast -(e_4+e_2)\\
  &= (\mathbf{0}\ast e_3) \ast (e_4\ast e_2).
    \end{aligned}
    $$

## 4. Cocommutative quandles

In this section, we answer part (3) of \[BE26, Question 7.1\]. In the following, let \\((X,\ast)\\) be a quandle, denoted simply by \\(X\\). Recall that the _dual quandle_ is the quandle \\(X^{\mathrm{op}}:=(X,\overline{\ast})\\), where \\[x\overline{\ast}y:=R_y^{-1}(x).\\]
(For a proof that the dual quandle is a quandle, see \[WB26\].) The name is justfied because \\((X^{\mathrm{op}})^{\mathrm{op}}=X\\).

We will say that \\(X\\) is _cocommutative_ if the dual quandle \\(X^{\mathrm{op}}\\) is commutative. Below, we provide a necessary and sufficient condition under which \\(X\\) is cocommutative. In particular, we completely describe quandles that are both commutative and cocommutative; this solves part (3) of \[BE26, Question 7.1\]. These results appear to be new.

**Theorem 4.1.** Let \\((X,\ast)\\) be a quandle. Then the following are equivalent: \
(1) \\(X\\) is cocommutative. \
(2) For all \\(x\in X\\), the left multiplication map \\(L_x\\) is an involution. 

_Proof._ First, note that (2) is equivalent to the statement that \\[x\ast(x\ast y)=y\\] for all \\(x,y\in X\\).

"\\(\implies\\)": Assume that \\(X\\) is cocommutative. Given \\(x,y\in X\\), let \\(z:=R_y^{-1}(x)\\). By assumption, we have \\(z:=R_x^{-1}(y)\\). Since \\(X\\) is a quandle, it follows that
\\[x\ast(x\ast y)=(z\ast y)\ast (x\ast y)=(z\ast x)\ast y=y\ast y=y,\\]
as desired.

"\\(\impliedby\\)": Given \\(x,y\in X\\), let \\(z:=R_y^{-1}(x)\\). We have to show that \\(z=R_x^{-1}(y)\\). Indeed,
\\[ R_x(z)= R_{R_y(z)}(z) = z\ast(z\ast y)=y, \\] where in the last equality we have used the assumption. Since \\(R_x\\) is invertible, the claim follows. QED.

**Corollary 4.2.** Let \\((X,\ast)\\) be a commutative quandle. Then \\(X\\) is cocommutative if and only if \\(X\\) is a kei.

_Proof._ Since \\(X\\) is commutative, we have \\(L_x=R_x\\) for all \\(x\in X\\). Hence, Theorem 4.1 yields the claim. QED.

_Remark 4.3._ Commutative kei are the same as _distributive Steiner quasigroups,_ which are algebraic structures that correspond to combinatorial designs called _Hall triple systems._ See \[St15T, Sec. 3.4\] for further discussion and references on distributive Steiner quasigroups, and see \[NP06\] for a quandle-theoretic treatment of commutative kei.

## 5. Medial Latin quandles

We completely describe medial Latin quandles and commutative medial quandles. The following results were already shown in \[Ba24, JPSZ15\]; we provide new, much shorter proofs at the cost of appealing to the Bruck–Murdoch–Toyoda theorem.

Recall from Lemmas 2.1 and 2.2 that every medial Latin quandle (and, hence, every commutative medial quandle) is a medial quasigroup. These observations allow us to use the _Bruck–Murdoch–Toyoda theorem_, which states the following: For every medial quasigroup \\( (X,\ast)\\), there exists an abelian group \\(A\\), a fixed element \\(c\in A\\), and two commuting automorphisms \\(\varphi,\psi\\) of \\(A\\) such that \\(X\\) is isomorphic to the medial quasigroup \\( (A,\cdot)\\), where \\[a\cdot b := \varphi(a)+\psi(b)+c\\] for all \\(a,b\in A\\).

**Theorem 5.1** (\[JPSZ15, Ex. 2.2 and Cor. 3.4\])**.** _Every medial Latin quandle is isomorphic to an Alexander quandle \\(\mathrm{Alex}(A,\varphi)\\) such that \\(\mathrm{id}-\varphi\\) is a permutation of \\(A\\)._

_Proof._ By the above discussion, every medial Latin quandle is isomorphic to a quasigroup of the form \\( (A,\cdot)\\) described above. By assumption, \\( (A,\cdot)\\) is idempotent, so taking \\(a:=0\\) and \\(b:=0\\) above shows that \\(c=0\\). Therefore, idempotence forces \\(\varphi+\psi=\mathrm{id}\\). That is, \\[a\cdot b=\varphi(a)+(\mathrm{id}-\varphi)(b),\\] so \\( (A,\cdot)=\mathrm{Alex}(A,\varphi),\\) as desired. Finally, since \\( (A,\cdot)\\) is Latin, the left multiplication maps \\(L_a=\varphi(a)+\mathrm{id}-\varphi\\) are invertible. Since addition by \\(\varphi(a)\\) is invertible, it follows that \\(\mathrm{id}-\varphi\\) is also invertible. QED.

**Corollary 5.2** (\[Ba24\])**.** _Every commutative medial quandle is isomorphic to an averaging quandle._

_Proof._ By Theorem 4.1, every commutative medial quandle is isomorphic to an Alexander quandle \\( \mathrm{Alex}(A,\varphi) \\). Commutativity implies that \\[\varphi(a)=a\ast 0=0\ast a=a-\varphi(a)\\] for all \\(a\in A\\); that is, \\(2\varphi=\mathrm{id}\\). Since \\(\varphi\\) is invertible, it follows that multiplication by \\(2\\) is invertible. Hence, \\(A\\) is a \\(k\\)-module, and \\(\varphi\\) is multiplication by \\(1/2\\). QED.

_Remark 5.3._ The "converses" of Theorems 4.1 and 4.2 also hold. Precisely, every Alexander quandle \\(\mathrm{Alex}(A,\varphi)\\) is medial, and if \\(\mathrm{id}-\varphi\\) is invertible, then \\(\mathrm{Alex}(A,\varphi)\\) is also Latin. Moreover, every averaging quandle is commutative.

In light of Lemma 2.2, the construction of Bauer \[Ba24\] can be viewed as a way to recover the averaging quandle corresponding to a given commutative quandle under Theorem 4.2. Although we will not use this construction, it is worth recording in our notation. Namely, given a nonempty commutative quandle \\( (X,\ast)\\), fix a basepoint \\(0\in X\\). Bauer showed that the following operations define a \\(k\\)-module structure on \\(X\\) such that \\(0\\) is the additive identity and \\(X_{\mathrm{avg}}\cong(X,\ast)\\):

$$
    \begin{aligned}
    x+y&:= R_0^{-1}(x\ast y), \\
   -x &:= R_x^{-1}(0),\\
   \frac{x}{2}&:= 0\ast x.
    \end{aligned}
    $$

The following example gives an alternative but equivalent construction in a special case. Given a set \\(X\\), let \\(k^{(X)}\\) denote the free \\(k\\)-module generated by \\(X\\).

**Example 5.4.** Given a nonempty set \\(X\\), consider the affine hull \\(H_X\\) of \\(X\\) in \\(k^{(X)}\\): \\[H_X:= \left\\{\sum^n_{i=0}\lambda_i x_i: n\geq 1,\, \lambda_i\in k,\, x_i\in X,\, \sum^n_{i=0}\lambda_i=1 \right\\}\subset k^{(X)}.\\] Then \\(H_X\\) is a subquandle of the averaging quandle \\( (k^{(X)})_{\mathrm{avg}}\\). 
To write \\(H_X\\) itself as an averaging quandle, fix a basepoint \\(x_0\in X\\), and consider the map

$$
    \begin{aligned}
    H_X & \to (k^{(X-\{x_0\})})_{\mathrm{avg}} \\
   \sum^n_{i=0}\lambda_i x_i &\mapsto \sum^n_{i=1}\lambda_i x_i.
    \end{aligned}
    $$

The reader can check that this map is a quandle isomorphism. In particular, if \\(\\# X=n+1\\) with \\(0\leq n\leq\infty\\), then we obtain a quandle isomorphism \\(H_X\cong k^n_{\mathrm{avg}}\\).

## 6. Equivalences of categories

Theorem 5.1 and Corollary 5.2 allow us to give an alternative perspective on the classification of medial Latin quandles. In the following, let \\(\mathsf{MedQnd}\\) be the category of medial quandles and quandle homomorphisms. Define the quotient ring \\[\Lambda:=\mathbb{Z}[s^{\pm 1},(1-s)^{-1}],\\] and denote the category of _affine modules_ over \\(\Lambda\\) by \\(\mathsf{AffMod}\_{\Lambda}\\). Namely, the objects of \\(\mathsf{AffMod}\_{\Lambda}\\) are \\(\Lambda\\)-modules along with the empty set, and the morphisms are affine transformations (that is, sums of \\(\Lambda\\)-linear maps and constant functions).[^1]

Note that the data of an object \\(M\\) in \\(\mathsf{AffMod}\_{\Lambda}\\) is equivalent to the data of an abelian group automorphism \\(\varphi\in\mathrm{Aut}(M)\\) such that the map \\(\mathrm{id}-\varphi\\) is invertible. (Explicitly, the correspondence is given by \\(s^{\pm 1}\cdot m \leftrightarrow \varphi^{\pm 1}(m)\\) for all \\(m\in M\\); in particular, \\((1-s)^{-1}\cdot m=(\mathrm{id}-\varphi)^{-1}(m)\\).) So, define a functor \\(\mathrm{Alex}\colon\mathsf{AffMod}\_{\Lambda}\to\mathsf{MedQnd}\\) on objects by sending \\(M\\) to the induced Alexander quandle \\(\mathrm{Alex}(M,\varphi)\\). Let \\(\mathrm{Alex}\\) fix all morphisms (as set-theoretic maps).

**Lemma 6.1.** The assignment \\(\mathrm{Alex}\colon\mathsf{AffMod}\_{\Lambda}\to\mathsf{MedQnd}\\) is a functor.

_Proof._ We only have to show that every affine transformation of \\(\Lambda\\)-modules \\(f\colon M\to N\\) is a quandle homomorphism \\(\mathrm{Alex}(M,\varphi)\to\mathrm{Alex}(N,\varphi)\\). If \\(M\\) is empty, then the claim is trivial. Othewise, \\(f\\) factorizes as \\(f=T-c\\) for some \\(\Lambda\\)-linear map \\(T\colon M\to N\\) and some constant \\(c\in N\\). In particular, \\(T\circ\varphi = \psi\circ T\\), so

$$
    \begin{aligned}
    f(x\ast y)&= f(\varphi(x-y)+y) \\
   &= (T\circ\varphi)(x-y)+T(y)+c\\
   &= (\psi\circ T)(x-y) + f(y)\\
   &= \psi(f(x)-f(y)) + f(y)\\
   &= f(x)\ast f(y),
    \end{aligned}
    $$

for all \\(x,y\in M\\). Hence, \\(f\\) is a quandle homomorphism. QED.

**Lemma 6.2.** Let \\(M\\) and \\(N\\) be \\(\Lambda\\)-modules, and let \\(T\colon M\to N\\) be a \\(\mathbb{Z}[s]\\)-linear map. Then \\(T\\) is \\(\Lambda\\)-linear.

_Proof._ Left to the reader; use the facts that \\(T\\) commutes with \\(s\\) and \\(1-s\\) and that multiplication by \\(s\\) and \\(1-s\\) are invertible. QED.

**Theorem 6.3.** The functor \\(\mathrm{Alex}\colon\mathsf{AffMod}\_{\Lambda}\to\mathsf{MedQnd}\\) is an equivalence of categories.

_Proof._ By Lemma 6.1, Theorem 5.1, and the above discussion, \\(\mathrm{Alex}\\) is an essentially surjective functor. Therefore, it suffices to show that \\(\mathrm{Alex}\\) is fully faithful. Faithfulness is clear. To show fullness, let \\(f\colon \mathrm{Alex}(M,\varphi)\to\mathrm{Alex}(N,\varphi)\\) be a homomorphism of Alexander quandles satisfying the conditions of Theorem 5.1, and view \\(M\\) and \\(N\\) as \\(\Lambda\\)-modules as in the above discussion. Let \\(c:= f(0)\\), and define \\(T\colon M\to N\\) by \\(T:= f-c\\). Then \\(f=T-c\\), so we only have to show that \\(T\\) is \\(\Lambda\\)-linear. By Lemma 6.2, it suffices to show that \\(T\\) is a homomorphism of abelian groups such that \\(T\circ\varphi=\psi\circ T\\). Clearly, \\(T(0)=0\\).

Since \\(f\\) is a quandle homomorphism, the reader can verify that \\(T\\) is also a quandle homomorphism. Equivalently,
\\[T(\varphi(x-y)+y)=\psi(T(x))+(\mathrm{id}-\psi)(T(y))\\] for all \\(x,y\in M\\). In particular, for all \\(z\in M\\), taking \\((x,y):=(\varphi^{-1}(z),0)\\) shows that \\(T=\psi\circ T\circ\varphi^{-1}\\). Therefore, \\(T\circ\varphi=\psi\circ T\\), as desired. 

Now, define a function \\(g\colon M^2\to N\\) by \\[g(x,y):=T(x+y)-T(x)-T(y)\\] for all \\(x,y\in M\\). It remains to show that \\(g\equiv 0\\). Since \\(T\\) is a quandle homomorphism and \\(\varphi\\) is a homomorphism of abelian groups, note first that

$$
    \begin{aligned}
    T((a\ast b)+(c\ast d))&= T(\varphi(a+c)+(\mathrm{id}-\varphi)(b+d)) \\
   &= T((a+c)\ast(b+d)) \\
   &= T(a+c)\ast T(b+d)
    \end{aligned}
    $$

for all \\(a,b,c,d\in M\\). Since \\(T\\) is a quandle homomorphism and \\(\psi\\) is a homomorphism of abelian groups, it follows that

$$
    \begin{aligned}
    g((a\ast b),(c\ast d))&= T((a\ast b)+(c\ast d)) - T(a\ast b) - T(d\ast d) \\
   &= [T(a+c)\ast T(b+d)] - [T(a)\ast T(b)] - [T(c)\ast T(d)] \\
   &= \psi(T(a+c)-T(a)-T(c))+(\mathrm{id}-\psi)(T(b\ast d)-T(b)-T(d)) \\
   &= g(a,c)\ast g(b,d)
    \end{aligned}
    $$
    
for all \\(a,b,c,d\in M\\). In particular, given \\(x,y\in M\\), let \\[a:=\varphi^{-1}(x),\quad b:= 0,\quad c:=0,\quad d:=(\mathrm{id}-\varphi)^{-1}(y).\\] Then \\(x=a\ast b\\) and \\( y=c\ast d\\), so \\[g(x,y)=g(a,c)\ast g(b,d)=g(a,0) \ast g(0,d)=0\ast 0=0\\] because \\(g(-,0)\equiv 0\\) and \\(g(0,-)\equiv 0\\). Hence, \\(L\\) is \\(\Lambda\\)-linear. QED.

### Commutative medial quandles

 In the following, let \\(\mathsf{CommQnd}\\) be the category of commutative quandles and quandle homomorphisms. On the other hand, denote the category of _affine modules_ over \\(k\\) by \\(\mathsf{AffMod}\_{k}\\). Namely, the objects of \\(\mathsf{AffMod}\_{k}\\) are \\(k\\)-modules along with the empty set, and the morphisms are affine transformations (that is, sums of \\(k\\)-linear maps and constant functions).
 
Attempt to define a functor \\(\mathrm{avg}\colon \mathsf{AffMod}_{k}\to \mathsf{CommQnd}\\) on objects by sending every \\(k\\)-module \\(M\\) to its averaging quandle \\(M\_{\mathrm{avg}}\\). Define the action on morphisms to be \\(f\mapsto f-f(0).\\)

**Proposition 6.1.** _\\(\mathrm{avg}\\) is a functor._

_Proof._ By direct computation. QED.

**Proposition 6.2.** _\\(\mathrm{avg}\\) is fully faithful._

_Proof._ Faithfulness is straightforward. To show fullness, let \\(M\\) and \\(N\\) be \\(k\\)-modules, and let \\(f\colon M_{\mathrm{avg}}\to N_{\mathrm{avg}}\\) be a quandle homomorphism. Define \\(T\colon M\to N\\) by \\(T:= f-f(0)\\). It suffices to show that \\(T\\) is \\(k\\)-linear, since then \\(f=\mathrm{avg}(T+f(0))\\). 

Certainly, \\(T(0)=0\\). Since \\(f\\) is a quandle homomorphism, it is easy to see that \\(T\\) is also a quandle homomorphism. In particular, \\(T(x/2)=T(x\ast 0)=T(x)/2\\) for all \\(x\in M\\), so \\[T(x+y)=2T\left(\frac{x+y}{2}\right)=2T(x\ast y)=2(T(x)\ast T(y))=T(x)+T(y)\\] for all \\(x,y\in M\\). In particular, we deduce that \\[T(nx)=nT(x)\\] for all \\(n\in\mathbb{Z}\\). Thererfore, it suffices to show that \\(T(x/2^k)=T(x)/2^k\\) for all \\(x\in M\\) and \\(k\geq 1\\); this follows by induction on \\(k\\). QED.

Combined with Corollary 5.2, Propositions 6.1 and 6.2 show the following.

**Theorem 6.3.** _\\(\mathrm{avg}\\) is an equivalence of categories._

_Remark 6.4._ Let \\(F\\) be the free commutative quandle with two generators, say \\(x,y\in F\\). In \[BE26, Question 7.3\], Bardakov and Elhamdadi asked whether \\(F\cong \mathrm{Free}_2\\). By the above, this question has a positive answer if and only if \\(F\\) is medial. The latter condition is true by the following nonelementary argument. By Lemma 2.1, \\(F\\) is distributive. Since \\(x\ast y= y\ast x\\), taking \\(a,d:=x\\) and \\(b,c:=y\\) in the statement of \[JK83, Prop. 3.2\] shows that \\(F\\) is medial. 

## Structure theorems

**Theorem.** 

### Footnotes

Footnotes can be useful for clarifying points in the text, or citing information. Markdown support numeric footnotes, as well as text as long as the values are unique.[^note]

```markdown
This is the regular text.[^1] This is more regular text.[^note]

[^1]: This is the footnote itself.
[^note]: This is another footnote.
```

[^1]: There are many equivalent ways to define the category of affine modules over a commutative ring, some of which come from treating affine modules as a variety in the sense of universal algebra. The reader can verify that when the ground ring is \\(k\\), then our definition is equivalent to these other definitions. 
[^note]: When using text for footnotes markers, no spaces are permitted in the name.

## References

\[Ba24\] K. J. Bauer, _quasigroup midpoint algebras = Z[1/2]-modules,_ Frank Blog, 2024. [https://frank-9976.github.io/midpoint.html](https://frank-9976.github.io/midpoint.html) (accessed: 1-14-2026).

\[BE26\] V. Bardakov and M. Elhamdadi. _Idempotents and powers of ideals in quandle rings,_ 2026. arXiv:2601.07057

\[ES01\] M. H. Escardo and A. K. Simpson, _A universal characterization of the closed Euclidean interval._ Proc. 16th Annual IEEE Symposium on Logic in Comp. Sci. (2001), 115–125. doi:10.1109/LICS.2001.932488.

\[Fr08\] P. Freyd, _Algebraic real analysis,_ Theory Appl. Categ. **20** (2008), no. 10, 215–306. MR2425550

\[JPSZ15\] P. Jedlička, A. Pilitowska, D. Stanovský, and A. Zamojska-Dzienio, _The structure of medial quandles,_ J. Algebra **443** (2015), 300–334. MR3400403

\[JK83\] J. Ježek and T. Kepka, _Notes on distributive groupoids,_ Comment. Math. Univ. Carolin. **24** (1983), no. 2, 237–249. MR0711262

\[Jo82\] D. Joyce, _A classifying invariant of knots, the knot quandle,_ J. Pure Appl. Algebra **23** (1982), no. 1, 37–65. MR638121

\[KN81\] T. Kepka and P. Němec, _Commutative Moufang loops and distributive groupoids of small orders,_ Czechoslovak Math. J. **31(106)** (1981), no. 4, 633–669. MR0631607

\[Ma82\] S. V. Matveev, _Distributive groupoids in knot theory,_ Mat. Sb. (N.S.) **119**(161) (1982), no. 1, 78–88, 160. MR672410

\[NP06\] M. Niebrzydowski and J. H. Przytycki, _Burnside kei,_ Fund. Math. **190** (2006), 211–229. 2232860

\[Si70\] K. Sigmon, _Cancellative medial means are arithmetic,_ Duke Math J. **37** (1970), 439–445. MR274644

\[St15A\] D. Stanovský, _A guide to self-distributive quasigroups, or Latin quandles,_ Quasigroups Related Systems **23** (2015), no. 1, 91–128. MR3353113

\[St15T\] —, _The origins of involutory quandles,_ 2015. arXiv:1506.02389

\[WB26\] W. Burrows and C. Tuffley, _The rack congruence condition and half congruences in racks,_ to appear in J. Knot Theory Ramifications. doi:10.1142/S0218216525500865.

***
**Footnotes**

The footnotes in the page will be returned following this line, return to the section on <a href="#footnotes">Markdown Footnotes</a>.
