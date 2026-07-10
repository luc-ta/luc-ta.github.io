---
title: 'Infinitely many McCoy rings with non-McCoy subrings'
sitemap: true
date: 2026-07-10
permalink: /blog/2026/mccoy-rings/
redirect_from: /mccoy/
tags:
  - rings-and-algebras
---

We construct an infinite family of McCoy rings containing subrings that are neither left nor right McCoy.

## 1. Introduction

A (unital associative) ring \(R\) is called _left McCoy_ (resp. _right McCoy_) if, whenever \(fg=0\) with \(f,g\in R[x]\) nonzero, there exists a nonzero element \(r\in R\) such that \(rg=0\) (resp.\ \(fr=0\)). We say that \(R\) is _McCoy_ if \(R\) is both left McCoy and right McCoy. 

In 2025, a Math Stack Exchange user posed the question of whether the McCoy property passes to subrings. The purpose of this blogpost is document [my negative answer](https://math.stackexchange.com/a/5141663/1563727) to this question, which was subsequently added to the [Database of Ring Theory](https://ringtheory.herokuapp.com/properties/property/156/).

## 2. The construction

Let \(k\) be an integral domain. We construct a (unital associative) ring \(R\) as follows. The underlying additive group of \(R\) is \(M_2(k)\), the group of \(2\times 2\) matrices with entries in \(k\). We equip \(R\) with the ring multiplication 
\\[AB:=\begin{pmatrix}
a_{11}b_{11} & a_{11}b_{12}+a_{12}b_{22} \\a_{21}b_{11}+a_{22}b_{21} &a_{22}b_{22}
\end{pmatrix}.\\]
Often, \(R\) is called a _Morita context ring_ or _generalized matrix ring_ whose associated bimodule maps are both zero; also, \(R\) is isomorphic to [this ring](https://ringtheory.herokuapp.com/rings/ring/170/). 

In the following, let \(E_{11}\), \(E_{12}\), \(E_{21}\), and \(E_{22}\) denote the usual elementary matrices in \(R\).

**Theorem.** The ring \(R\) is McCoy, but it contains a subring \(S\) that is neither left McCoy nor right McCoy.

_Proof._ Let \(S:= T_2(k)\) be the subset of upper triangular matrices in \(R\), which is a subring with its usual multiplication. We claim that \(S\) is neither left McCoy nor right McCoy. Indeed, consider the polynomials \\[f(x)\coloneq E_{12}x+E_{11},\qquad g(x)\coloneq -E_{12}x+E_{22}\\] in \(S[x]\). Evidently, \(fg=0\). Since \(r\) is upper triangular, it is straightforward to show that if \(r\in S\) and \(rg=0\) or \(fr=0\), then \(r=0\), as desired. That is, \(S\) is neither left McCoy nor right McCoy.

Now, we prove that \(R\) is McCoy. Let \(f,g\in R[x]\cong M_2(k[x])\) be nonzero elements, considered as \(2\times 2\) matrices with polynomial entries \(f_{ij},g_{ij}\in k[x]\). Then the equation \(fg=0\) means that the polynomials 
    \\[f_{11}g_{11},\quad \varphi\coloneq f_{11}g_{12}+f_{12}g_{22},\quad \psi\coloneq f_{21}g_{11}+f_{22}g_{21},\quad \text{and}\quad f_{22}g_{22}\\] in \(k[x]\) all vanish. Since \(k[x]\) is an integral domain, we must have \(f_{11}=0\) or \(g_{11}=0\), and \(f_{22}=0\) or \(g_{22}=0\). 

We claim that \(R\) is right McCoy. If \(f_{11}\neq 0\) and \(f_{22}\neq 0\), then \(g_{11}=0\) and \(g_{22}=0$, so the equations \(\varphi=0\) and \(\psi=0\) imply that \(g_{12}=0\) and \(g_{21}=0\) as well. That is, \(g=0\), which is a contradiction. Therefore, \(f_{11}\) and \(f_{22}\) cannot both be nonzero. If \(f_{11}=0\), then a quick calculation shows that \(fE_{12}=0\); if \(f_{22}=0\), then \(fE_{21}=0$. Hence, \(R\) is right McCoy.

Showing that \(R\) is left McCoy is similar. Here are the details for the sake of convenience: if \(g_{11}\neq 0\) and \(g_{22}\neq 0$, then \(f_{11}= 0\) and \(f_{22}= 0\), so \(f_{12}=0\) and \(f_{21}=0\) as well. That is, \(f=0\), which is a contradiction. If \(g_{11}=0$, then \(E_{21}g=0$; if \(g_{22}=0\), then \(E_{12}g=0\). Hence, \(R\) is left McCoy. QED.
