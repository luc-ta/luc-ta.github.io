---
permalink: /commutative-quandles/
title: "Structure theory of commutative quandles"
sitemap: false
redirect_from: 
---

## Introduction

In this blogpost, we describe an equivalence of categories between medial Latin (resp. commutative) quandles and affine modules over the ring of integral Laurent polynomials (resp. dyadic rationals). As an application, we obtain structure theorems for finitely generated commutative quandles and finite cancellative midpoint algebras. This solves Questions 7.1 and 7.3 of Bardakov and Elhamdadi \[BE26\], which were heretofore open.

In the following, let \\(k:=\mathbb{Z}[\frac{1}{2}]\\) denote the ring of dyadic rationals.

## 1. Preliminaries

First, we recall definitions coming from nonassociative algebra. Recall that a _magma_ is a set \\(X\)) equipped with a binary operation \\(\ast\colon X\to X\)) called _multiplication_. The cardinality of \\(X\\) is called its _order._ If \\(X,\ast_X\\) and \\(Y,\ast_Y\\) are magmas, then a function \\(f\colon X\to Y\\) is called a _magma homomorphism_ if \\(f(w\ast_X x)=f(w)\ast_Y f(x)\\) for all \\(w,x\in X\\). 

Let \\((X,\ast)\\) be a magma. For all \\(x\in X\\), consider the _right multiplication_ map \\(R_x\colon X\to X\\) given by \\(y\mapsto y\ast x\\) and the _left multiplication map_ \\(L_x\colon X\to X\\) given by \\(y\mapsto x\ast y\\).
* \\(X\\) is called _Latin_ or a _quasigroup_ if for all \\(x\in X\\), the multiplication maps \\(R_x\\) and \\(L_x\\) are permutations.
* \\(X\\) is called a _rack_ if for all \\(x\in X\\), the right multiplication map \\(R_x\\) is a magma automorphism. In particular, the multiplication \\(\ast\\) is right-distributive: \\[(x\ast y)\ast z=(x\ast z)\ast (y\ast z).\\]
* \\(X\\) is called _idempotent_ if \\(x\ast x=x\\) for all \\(x\in X\\).
* A _quandle_ is an idempotent rack.
* Note that the Cartesian product \\(X\times X\\) is a magma. We call \\(X\\) _medial_ if the multiplication \\(\ast\colon X\times X\to X\\) is a magma homomorphism; that is,\\[(w\ast x)\ast(y\ast z)=(w\ast y)\ast(x\ast z)\\] for all \\(w,x,y,z\in X\\). 
* \\(X\\) is called _commutative_ if \\(x\ast y=y\ast x\\) for all \\(x,y\in X\\).
* A _midpoint algebra_ is an idempotent medial commutative magma.
* \\(X\\) is called _cancellative_ if for all \\(x\in X\\), the left multiplication map \\(L_x\\) is injective.

## 1.1. Discussion

Sigmon \[S70\] introduced cancellative midpoint algebras under the name "medial means" in 1970. Cancellative midpoint algebras allow for categorifications of certain notions from convex analysis \[ES01, Fr08\], and they have connections to (affine) modules over the dyadic rationals \\(k\\) \[Ba24, Fr08\].

One motivation for this blog post is to connect the theory of cancellative midpoint algebras to the theory of quandles. Joyce \[Jo82\] and Matveev \[Ma82\] independently introduced quandles in 1982 to develop complete invariants of knots. In particular, commutative quandles are important to the theory of quandle rings \[BE26\]. 

The prototypical example of a quandle is the _conjugation quandle_ of a group \\(G\\), defined to be the pair \\(\mathrm{Conj}(G):=(G,\ast)\\) where \\[h\ast g:=ghg^{-1}.\\] On the other hand, _Alexander quandles_ are important examples of medial quandles. Given an automorphism \\(\varphi\\) of an abelian group \\(A\\), the Alexander quandle \\(\mathrm{Alex}(A,\varphi)=(A,\ast)\\) is defined by \\[x\ast y:=\varphi(x)+(\mathrm{id}-\varphi)(y).\\]

The following two lemmas are straightforward and left to the reader.

**Lemma 1.1.** 
* _Every Latin rack is an idempotent quasigroup and, in particular, a quandle._
* _Every commutative rack is Latin and, in particular, a quandle._

**Lemma 1.2** (cf. \[Ba24\])**.** 
* _Every commutative magma is medial._
* _Let \\(X,\ast\\) be a finite commutative magma. Then \\(X\\) is cancellative if and only if it is a quasigroup._
* _Every commutative quandle is a cancellative midpoint algebra. Conversely, every finite cancellative midpoint algebra is a commutative quandle._

_Remark 1.3._ Infinite cancellative midpoint algebras are not necessarily quasigroups; in particular, they are not necessarily quandles. See Remark 2.5 for a counterexample.

The following result requires a more involved argument. In \[BE26\], the authors start with a fixed element \\(x\in X\\) and show that \\(X-\\{x\\}\\) consists of \\(2n\\) elements \\(\\{y_1,\dots,y_n,z_1,\dots,z_n\\}\\) such that \\(z_i\ast y_i=x\\) for all \\(1\leq i\leq n\\).

**Lemma 1.3** (\[BE26, Prop. 5.2\])**.** _The order of every finite commutative quandle is odd._

## 2. Averaging quandles

We define a class of commutative quandles called _averaging quandles_. Later, we show that every commutative quandle is isomorphic to an averaging quandle, and every finitely generated commutative quandle canonically decomposes as the Cartesian product of free commutative quandles and certain finite averaging quandles \\(C_{2n+1}\\).

**Definition 2.1.** Let \\(A\\) be a unital commutative ring in which \\(2\\\) is invertible, and let \\(M\\) be an \\(A\\)-module. Define a quandle operation on \\(M\\) by averaging: \\[x\ast y:=\frac{1}{2}(x+y).\\] Then \\( M_{\mathrm{avg}}:=(M,\ast) \\) is a commutative quandle called the _averaging quandle_ on \\(M\\). 

In particular, if \\(A=M=\mathbb{Z}/(2n+1)\mathbb{Z}\\) is the cyclic group of order \\(2n+1\\) with \\(n\geq 0\\), then we denote the averaging quandle by \\(C\_{2n+1}:=M\_{\mathrm{avg}}\\). Since \\(2^{-1}=n+1\\) in \\(M\\), this definition of \\(C_{2n+1}\\) coincides with the one from \[BE26\].

_Remark 2.2._ Averaging quandles are a special class of Alexander quandles, which are not commutative in general.

**Example 2.3.** Given a set \\(X\\), consider the affine hull \\(H_X\\) of \\(X\\) as a subset of the free \\(k\\)-module \\(k[X]\\) generated by \\(X\\): \\[H_X:= \left\\{\sum^n_{i=1}\lambda_i x_i: n\geq 1,\, \lambda_i\in k,\, x_i\in X,\, \sum^n_{i=1}\lambda_i=1 \right\\}\subset k[X].\\] Then \\(H_X\\) is a subquandle of the averaging quandle \\( k[X]_{\mathrm{avg}}\\). We denote this subquandle by \\(\mathrm{Free}_X\\); if \\(\\# H=n<\infty\\), then we denote \\(\mathrm{Free}_n:=\mathrm{Free}_X\\). (Later, we show that \\(\mathrm{Free}_X\\) is isomorphic to the free commutative quandle generated by \\(X\\), which justifies the notation.) Note that \\(\mathrm{Free}_0\\) is the empty quandle.

**Lemma 2.4.** _For all \\(n\geq 1\\), the quandle \\(\mathrm{Free}\_n\\) is isomorphic to the averaging quandle \\( (k^{n-1})\_{\mathrm{avg}}\\)._

_Proof._ Denote the generators of \\(\mathrm{Free}\_n\\) by \\(\\{e_1,\dots,e_n\\}\\). Define maps  

$$
    \begin{aligned}
    \mathrm{Free}_n & \to (k^{n-1})_{\mathrm{avg}} \\
   \sum^n_{i=1}\lambda_i e_i &\mapsto (\lambda_1,\dots,\lambda_{n-1}) 
    \end{aligned}
    $$
    
and
    
$$
    \begin{aligned}
    (k^{n-1})_{\mathrm{avg}}&\to\mathrm{Free}_n  \\
   (\lambda_1,\dots,\lambda_{n-1}) &\mapsto \left(1-\sum^{n-1}_{i=1}\lambda_i \right)e_n + \sum^{n-1}_{i=1}\lambda_i e_i .
    \end{aligned}
    $$
    
The reader may verify that these maps are mutually inverse quandle homomorphisms. QED.

_Remark 2.5._ Contrary to Example 5.1(3) and Question 7.3 of \[BE26\], the subset \\(X:=\\{n/2^k \mid n,k\in\mathbb{Z}_{\geq 0}\\}\subset k\\) is not a subquandle of \\(k\_{\mathrm{avg}}\\). Indeed, the right multiplication map \\( x\mapsto x\ast 1\\) does not restrict to a permutation of \\(X\\).

## Markdown guide

### Header three

#### Header four

##### Header five

###### Header six

## 3. Medial Latin quandles

We completely describe medial Latin quandles and commutative quandles. The following results were already shown in \[Br24, JPSZ15\]; we provide new, much shorter proofs at the cost of appealing to the Bruck–Murdoch–Toyoda theorem.

Recall from Lemmas 1.1 and 1.2 that every commutative quandle is medial and Latin, and every Latin quandle is a quasigroup. These observations allow us to use the _Bruck–Murdoch–Toyoda theorem_, which states the following: For every medial quasigroup \\( (X,\ast)\\), there exists an abelian group \\(A\\), a fixed element \\(c\in A\\), and two commuting automorphisms \\(\varphi,\psi\\) of \\(A\\) such that \\(X\\) is isomorphic to the medial quasigroup \\( (A,\cdot)\\), where \\[a\cdot b := \varphi(a)+\psi(b)+c\\] for all \\(a,b\in A\\).

**Theorem 3.1** (\[JPSZ15, Ex. 2.2 and Cor. 3.4\])**.** Every medial Latin quandle is isomorphic to an Alexander quandle \\(\mathrm{Alex}(A,\varphi)\\) such that \\(\mathrm{id}-\varphi\\) is a permutation of \\(A\\).

_Proof._ By the above discussion, every medial Latin quandle is isomorphic to a quasigroup of the form \\( (A,\cdot)\\) described above. By assumption, \\( (A,\cdot)\\) is idempotent, so taking \\(a:=0\\) and \\(b:=0\\) above shows that \\(c=0\\). Therefore, idempotence forces \\(\varphi+\psi=\mathrm{id}\\). That is, \\[a\cdot b=\varphi(a)+(\mathrm{id}-\varphi)(b),\\] so \\( (A,\cdot)=\mathrm{Alex}(A,\varphi),\\) as desired. Finally, since \\( (A,\cdot)\\) is Latin, the left multiplication maps \\(L_a=\varphi(a)+\mathrm{id}-\varphi\\) are invertible. Since addition by \\(\varphi(a)\\) is invertible, it follows that \\(\mathrm{id}-\varphi\\) is also invertible. QED.

**Theorem 3.2** (\[Br24\])**.** Every commutative quandle is isomorphic to an averaging quandle.

_Proof._ By Theorem 3.1, every commutative quandle is isomorphic to an Alexander quandle \\( \mathrm{Alex}(A,\varphi) \\). By commutativity, we have \\[\varphi(a)=a\ast 0=0\ast a=a-\varphi(a)\\] for all \\(a\in A\\), so \\(2\varphi=\mathrm{id}\\). Since \\(\varphi\\) is invertible, it follows that multiplication by \\(2\\) is invertible, and \\(\varphi\\) is multiplication by \\(1/2\\). QED.

## 4. Equivalences of categories

In the following, let \\(\mathsf{AffMod}\_{k}\\) be the category whose objects are \\(k\\)-modules and whose morphisms are affine transformations (that is, sums of \\(k\\)-linear maps and constant functions).[^1] Let \\(\mathsf{CommQnd}\\) be the category of commutative quandles and quandle homomorphisms.

Attempt to define a functor \\(\mathrm{avg}\colon \mathsf{AffMod}_{k}\to \mathsf{CommQnd}\\) on objects by sending every \\(k\\)-module \\(M\\) to its averaging quandle \\(M\_{\mathrm{avg}}\\). Define the action on morphisms to be \\(f\mapsto f-f(0).\\)

**Proposition 4.1.** \\(\mathrm{avg}\\) is a functor.

_Proof._ By direct computation. QED.

**Proposition 4.2.** \\(\mathrm{avg}\\) is fully faithful.

_Proof._ Faithfulness is straightforward. To show fullness, let \\(M\\) and \\(N\\) be \\(k\\)-modules, and let \\(f\colon M_{\mathrm{avg}}\to N_{\mathrm{avg}}\\) be a quandle homomorphism. Define \\(T\colon M\to N\\) by \\(T:= f-f(0)\\). It suffices to show that \\(T\\) is \\(k\\)-linear, since then \\(f=\mathrm{avg}(T+f(0))\\). 

Certainly, \\(T(0)=0\\). Since \\(f\\) is a quandle homomorphism, it is easy to see that \\(T\\) is also a quandle homomorphism. In particular, \\(T(x/2)=T(x\ast 0)=T(x)/2\\) for all \\(x\in M\\), so \\[T(x+y)=2T\left(\frac{x+y}{2}\right)=2T(x\ast y)=2(T(x)\ast T(y))=T(x)+T(y)\\] for all \\(x,y\in M\\). In particular, we deduce that \\[T(nx)=nT(x)\\] for all \\(n\in\mathbb{Z}\\). Thererfore, it suffices to show that \\(T(x/2^k)=T(x)/2^k\\) for all \\(x\in M\\) and \\(k\geq 1\\); this follows by induction on \\(k\\). QED.

Combined with Theorem 3.2, these theorems show the following.

**Theorem.** \\(\mathrm{avg}\\) is an equivalence of categories.

## Structure theorems

**Theorem.** 


## Definition Lists

Definition List Title
:   Definition list division.

Startup
:   A startup company or startup is a company or temporary organization designed to search for a repeatable and scalable business model.

#dowork
:   Coined by Rob Dyrdek and his personal body guard Christopher "Big Black" Boykins, "Do Work" works as a self motivator, to motivating your friends.

Do It Live
:   I'll let Bill O'Reilly [explain](https://www.youtube.com/watch?v=O_HyZ5aW76c "We'll Do It Live") this one.

## Unordered Lists (Nested)

  * List item one 
      * List item one 
          * List item one
          * List item two
          * List item three
          * List item four
      * List item two
      * List item three
      * List item four
  * List item two
  * List item three
  * List item four

## Ordered List (Nested)

  1. List item one 
      1. List item one 
          1. List item one
          2. List item two
          3. List item three
          4. List item four
      2. List item two
      3. List item three
      4. List item four
  2. List item two
  3. List item three
  4. List item four

## Buttons

Make any link standout more when applying the `.btn` class.

## Notices

Basic notices or call-outs are supported using the following syntax:

```markdown
**Watch out!** You can also add notices by appending `{: .notice}` to the line following paragraph.
{: .notice}
```

which wil render as:

**Watch out!** You can also add notices by appending `{: .notice}` to the line following paragraph.
{: .notice}

### Footnotes

Footnotes can be useful for clarifying points in the text, or citing information. Markdown support numeric footnotes, as well as text as long as the values are unique.[^note]

```markdown
This is the regular text.[^1] This is more regular text.[^note]

[^1]: This is the footnote itself.
[^note]: This is another footnote.
```

[^1]: There are many equivalent ways to define the category of affine modules over a commutative ring. The reader can verify that when the ground ring is \\(k\\), then our definition is equivalent to these other ways.
[^note]: When using text for footnotes markers, no spaces are permitted in the name.

## HTML Tags

### Address Tag

<address>
  1 Infinite Loop<br /> Cupertino, CA 95014<br /> United States
</address>

### Anchor Tag (aka. Link)

This is an example of a [link](http://github.com "Github").

### Abbreviation Tag

The abbreviation CSS stands for "Cascading Style Sheets".

*[CSS]: Cascading Style Sheets

### Cite Tag

"Code is poetry." ---<cite>Automattic</cite>

### Code Tag

You will learn later on in these tests that `word-wrap: break-word;` will be your best friend.

You can also write larger blocks of code with syntax highlighting supported for some languages, such as Python:

```python
print('Hello World!')
```

or R:

```R
print("Hello World!", quote = FALSE)
```

### Strike Tag

This tag will let you <strike>strikeout text</strike>.

### Emphasize Tag

The emphasize tag should _italicize_ text.

### Insert Tag

This tag should denote <ins>inserted</ins> text.

### Keyboard Tag

This scarcely known tag emulates <kbd>keyboard text</kbd>, which is usually styled like the `<code>` tag.

### Preformatted Tag

This tag styles large blocks of code.

<pre>
.post-title {
  margin: 0 0 5px;
  font-weight: bold;
  font-size: 38px;
  line-height: 1.2;
  and here's a line of some really, really, really, really long text, just to see how the PRE tag handles it and to find out how it overflows;
}
</pre>

### Quote Tag

<q>Developers, developers, developers&#8230;</q> &#8211;Steve Ballmer

### Strong Tag

This tag shows **bold text**.

### Subscript Tag

Getting our science styling on with H<sub>2</sub>O, which should push the "2" down.

### Superscript Tag

Still sticking with science and Isaac Newton's E = MC<sup>2</sup>, which should lift the 2 up.

### Variable Tag

This allows you to denote <var>variables</var>.

## References

\[Ba24\] K. J. Bauer, _quasigroup midpoint algebras = Z[1/2]-modules,_ Frank Blog, 2024. https://frank-9976.github.io/midpoint.html (accessed: 1-14-2026).

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
