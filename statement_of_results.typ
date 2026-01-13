#import "@preview/ctheorems:1.1.3": *
#import "@preview/lovelace:0.3.0": *
#show: thmrules.with(qed-symbol: $square$)

#set heading(numbering: "1.1.")

#let theorem = thmbox("theorem", "Theorem", fill: rgb("#eeffee"))
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#eeffee"))
#let corollary = thmplain(
  "corollary",
  "Corollary",
  base: "theorem",
  titlefmt: strong
)
#let definition = thmbox("definition", "Definition", inset: (x: 0em, top: 0em))

#let example = thmplain("example", "Example").with(numbering: none)
#let proof = thmproof("proof", "Proof")


#title[Number-Theoretic Transform in Lean 4]

#let Zmod(p) = $ZZ \/ #p ZZ$
#let NTT = $op("NTT")$
#let INTT = $op("INTT")$
#let FNTT = $op("FNTT")$

= Introduction

The discrete Fourier transform (DFT) of a function taking values in the complex numbers can be generalized to functions taking values in an arbitrary ring $R$. If we specialize the discrete Fourier transform over a ring to $R = Zmod(p)$, the integers modulo a prime $p$, we obtain what is called the number-theoretic Transform (NTT).

The fast Fourier transform algorithm (FFT), used to compute the discrete fourier transform of an $n$-tuple in $O(n log n)$ time, can also be applied to the number-theoretic transform. This project is a formalization of both the number-theoretic transform and the fast algorithm to compute it. The advantage of working in $Zmod(p)$ instead of $CC$, is that all computations can be carried out exactly, making all of our formalization computable.

= Theory and definitions

Let $x = (x_0, ..., x_(n-1))$ be an $n$-tuple of elements of $Zmod(p)$ where $p$ is prime. The NTT of $x$ is obtained by replacing the factors $e^(- i 2 pi / n)$ in the definition of the complex DFT by a _primitive $n$-th root of unity_ $omega in Zmod(p)$:

#definition[
  The number-theoretic Transform (NTT) maps $x$ to another $n$-tuple $y = (y_0, ..., y_(n-1))$ of elements in  $Zmod(p)$ defined by
  $
    NTT(x)_k := sum_(j=0)^(n-1) x_j omega^(j k). 
  $
]

#definition[
  An element $omega in Zmod(p)$ is called a primitive $k$-th root of unity if $omega^k = 1$ and $omega^l = 1 => k | l$.
] 

Just like the DFT, the NTT is invertible:

#definition[
  The inverse number-theoretic Transform (INTT) maps $y = (y_0, ..., y_(n-1))$ back to the $n$-tuple
  $
    NTT(y)_k := n^(-1) sum_(j=0)^(n-1) y_j omega^(-j k).
  $
]

In order to prove that this is indeed an inverse, we need to following theorem about primitive roots:

#theorem[
  Let $omega in Zmod(p)$ be a primitive $n$-th root of unity, then for any $m in ZZ$ it holds that
  $
    ∑_(k=0)^(n-1) ω ^ (k  m) =
    cases(
      n "if" n | m,
      0 "otherwise"
    ).
  $
]<orthogonality>
#proof[
  If $n$ divides $m$, i.e. there is an integer $a$ such that $m = a dot n$, then
  $
    ∑_(k=0)^(n-1) ω ^ (k  m) = ∑_(k=0)^(n-1) (ω ^ n) ^ (k a) = ∑_(k=0)^(n-1) 1 ^ (k a) = n.
  $
  If $n$ does not divide $m$, then by the primitive root property $omega ^ m eq.not 1$. Hence, we can rewrite the geometric sum to
  $
    ∑_(k=0)^(n-1) ω ^ (k  m) =
    ∑_(k=0)^(n-1) (ω ^ m) ^ k =
    ((ω ^ m) ^ n - 1) / (ω ^ m - 1) = 0.
  $
]

#theorem[
  Let $n, p in NN$ and $p$ be prime. If $p divides.not n$, then for any $n$-tuple $x = (x_0, ..., x_(n-1))$ of elements in $Zmod(p)$ we have that $INTT(NTT(x)) = x$.
]
#proof[
  Since $p$ does not divide $n$, $n$ i non-zero in $Zmod(p)$ and hence its inverse $n^(-1)$ is well defined.
  $
    INTT(NTT(x))_j
    &= n^(-1) sum_(k=0)^(n-1) (sum_(l=0)^(n-1) x_l omega^(l k)) omega^(-j k) \
    &= n^(-1) sum_(l=0)^(n-1) x_l (sum_(k=0)^(n-1) omega^((l-j) k))
  $
  Notice that $k | l-j$ if and only if $l=j$, hence 
  $
    &= n^(-1) sum_(l=0)^(n-1) x_l n \
    &= x_j,
  $
]

== Convolution Theorem

For $n$-tuples of elements in $Zmod(p)$ we have the following notion of convolution:

#definition[Circular Convolution][
  Let $x = (x_0, ..., x_(n-1))$ and $y = (y_0, ..., y_(n-1))$ be $n$-tuples of elements in $Zmod(p)$
  $
    (x star y)_k = sum_(j=0)^(n-1) x_j y_((k - j) mod n)
  $
]

The convolution theorem states that the convolution in the time domain corresponds to pointwise multiplication in the frequency domain:

#theorem[
  Let $omega$ be a primitive $n$-th root of unity in $Zmod(p)$, then
  $
    INTT(x star y) = n dot NTT(x) dot NTT(y).
  $
]
#proof[
  Let $z = x star y$. By the definition of the NTT and the cyclic convolution we have
  $
    NTT(z)_k
    &= sum_(m=0)^(n-1) (sum_(j=0)^(n-1) x_j y_((m - j) mod n)) omega^(m k) \
    &= sum_(j=0)^(n-1) x_j sum_(m=0)^(n-1) y_((m - j) mod n) omega^(m k).
  $
  We substitute $l = (m - j) mod n$. As $m$ ranges from $0$ to $n-1$ so does $l$. Also notice that $omega^n = 1$, hence $omega^(m k) = omega^((l + j) k) = omega^(l k) omega^(j k)$.
  $
    &= sum_(j=0)^(n-1) x_j sum_(l=0)^(n-1) y_l omega^(l k) omega^(j k) \
    &= (sum_(j=0)^(n-1) x_j omega^(j k)) (sum_(l=0)^(n-1) y_l omega^(l k)) \
    &= NTT(x)_k dot NTT(y)_k.
  $
]

A similar result holds for the inverse NTT:

#theorem[
  Let $omega$ be a primitive $n$-th root of unity in $Zmod(p)$, then
  $
    NTT(x star y) = NTT(x) dot NTT(y),
  $
  where $dot$ denotes the pointwise multiplication of two $n$-tuples.
]
#proof[
  This follows directly from the fact that if $omega$ is a primitive $n$-th root of unity, then so is $omega^(-1)$, and the previous theorem.
]

= Fast Algorithms

Computing the NTT naively using the definition requires $O(n^2)$ operations in $Zmod(p)$. However, just like the DFT, the NTT can be computed in $O(n log n)$ time using a divide-and-conquer approach.

The existsence of such an algorithm follows almost immediately from the following decomposition of the $NTT$: Let $x$ be a vector in $(Zmod(p))^n$ where $n$ is even and let $omega$ be a primitive $N$-th root of unity in $Zmod(p)$, for any $k = 0, ..., n-1$ we have

$
  (NTT(x))_k = sum_(j=0)^(n-1) x_j omega^(j k) 
  = sum_(j=0)^(n\/2-1) x_(2j) (omega^2)^(j k) + omega^k sum_(j=0)^(n\/2-1) x_(2j+1) (omega^2)^(j k).
$

The right-hand side of the above equation resembles two NTTs of length $n/2$: one for the even-indexed elements of $x$ and one for the odd-indexed elements, using $ω$ as the root of unity. It is easy to verify that if $ω$ is a primitive $n$-th root of unity, then $ω^2$ is a primitive $(n/2)$-th root of unity.

A small caveat is that the index $k$ in the original problem ranges from 0 to $n-1$, while the sub-NTTs on the right-hand side produce vectors defined only for indices from 0 to $n/2-1$. However, we can resolve this by observing that the sub-problems are periodic with period $n/2$
$
  (omega^2)^(j (k mod n/2))
  = (omega^2)^(j(k - n/2 floor(k/(n\/2))))
  = (omega^2)^(j k) (omega^n)^(-j floor(k/(n\/2)))
  = (omega^2)^(j k).
$
Hence, we obtain the following recursive formula for the NTT:
$
  NTT(omega, x)_k = NTT(omega^2, x^"even")_(k mod n/2) + omega^k dot NTT(omega^2, x^"odd")_(k mod n/2),
$
where $x^"even" = (x_0, x_2, ..., x_(n-2))$ and $x^"odd" = (x_1, x_3, ..., x_(n-1))$. By evaluating the sub-NTTs at $k mod n/2$, we save ourselves from having to recompute the two half-length NTTs for the indices $k = n/2, ..., n-1$.

Assuming that $n = 2 ^ l$ for some $l in NN$ and keeping in mind that $omega^(k + n/2) = -omega^k$ we obtain the following recursive algorithm for computing the NTT, called the Fast Number-Theoretic Transform (FNTT):

#pseudocode-list[
    + *function* $FNTT(omega, x)$
      + *match* $l$ *with*
        + $l -> x$
        + $l + 1 ->$
          + $x^"even" <- (x_0, x_2, ..., x_(2^l-2)), quad x^"odd" <- (x_1, x_3, ..., x_(2^l-1))$
          +
          + $y^"even" <- FNTT(omega^2, x^"even"), quad y^"odd" <- FNTT(omega^2, x^"odd")$
          + 
          + *for* $k = 0 ..., 2^l - 1$ *do*
            + $y_k <- y^"even"_k + omega^k dot y^"odd"_k, quad y_(k + 2^l) <- y^"even"_k - omega^k dot y^"odd"_k$
          + *return* $y$
  ]

= Formalization in Lean

== NTT definition properties

The statements in this section are in the file `NTT.lean`, for this entire section assume the variables
```lean
variable {n p : ℕ} [Fact p.Prime]
```
We defined NTT and INTT the following way:
```lean
def ntt (ω : ZMod p) : (Fin n → ZMod p) → (Fin n → ZMod p) :=
  fun x k ↦ ∑ j, x j * ω ^ ((j * k) : ℤ)

def intt_aux (ω : ZMod p) : (Fin n → ZMod p) → (Fin n → ZMod p) :=
  fun x k ↦ ∑ j, x j * ω ^ (-(j * k : ℤ))

def intt (ω : ZMod p) (x : Fin n → ZMod p) : (Fin n → ZMod p) := 
  (n : ZMod p)⁻¹ • intt_aux ω x
```
Defining tuples as functions from `Fin n` is the standard way to represent fixed-length tuples in mathlib, this allow us to us to invoke various lemmas about `Fin n` and sums over `Fin n` from mathlib. 

The theorems `ntt_add` and `ntt_smul` show that the NTT is linear. The theorems `left_inv` and `right_inv` show that NTT and INTT are inverses when `p` does not divide `n`, for this we do assume that `ω` is a primitive `n`-th root of unity:

```lean
variable {ω : ZMod p}

theorem left_inv (hp : ¬p ∣ n) (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    intt ω (ntt ω x) = x

theorem right_inv (hp : ¬p ∣ n) (h : IsPrimitiveRoot ω n) (x : Fin n → ZMod p) :
    ntt ω (intt ω x) = x
```

The main ingredient used in the proofs of these theorems is the orthogonality of roots of unity @orthogonality, which is we formalized in the file `PrimitiveRoots.lean` and is called `IsPrimitiveRoot.sum_zpow_mul_eq`. 

The section `convolution` contains the fornalizations of the convolution theorems. The circular convolution was not defined in mathlib, so we defined it ourselves as `convolution` in the file `Convolution.lean`. The theorems `ntt_convolution` and `intt_convolution` as well as `convolution_ntt` and `convolution_intt` formalize the convolution theorems.

== Primitive roots of unity

The theory of primitvie roots is well developed in mathlib, the missing results we need are in the file `PrimitiveRoots.lean`. This file contains the fact that if `ω` is a primitive `n`-th root of unity in `Zmod(p)`, then $omega ^ 2$ is a primitive `n/2`-th root of unity, as well as @orthogonality

== FNTT on Vectors 

== Running time analysis