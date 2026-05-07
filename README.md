# CS 294-268 Final Project Proposal

**Title:** Communication Complexity

**Group Members:** Lucy Horowitz, Timothe Kasriel, Mihir Singhal

---

## 1. Project Topic

We formalize the foundations of two-party communication complexity, covering deterministic, private-coin, and public-coin models. Our primary aims are:
1. To develop the foundational machinery of communication complexity, such as the rectangle partition structure and the log-rank lower bound.
2. To prove tight upper and lower bounds (both deterministic and randomized) for important functions including equality, inner product, disjointness, indexing, and gap-Hamming distance.

## 2. Background and Motivation

Communication complexity, introduced by Yao (1979), is a cornerstone of theoretical computer science with applications to circuit lower bounds, streaming algorithms, data structures, and property testing. The key functions we target (equality, inner product, disjointness, etc.) are among the most well-studied in the field, with tight bounds that illustrate fundamentally different proof techniques: combinatorial rectangle arguments, rank methods, corruption/information-theoretic methods, and distributional complexity. Also, the results for these functions in particular are often used in other fields (such as streaming lower bounds).

## 3. Formalized Infrastructure

The project builds a reusable Lean library for finite communication-complexity arguments.

- **Protocol models.** `CommunicationComplexity.Basic`,
  `Deterministic.OneWay`, `PublicCoin.Basic`, and `PrivateCoin.Basic` define deterministic,
  one-way, public-coin, and private-coin protocols, their run semantics, their costs, and exact or
  approximate computation predicates.
- **Finite-message protocols.** `Deterministic.FiniteMessage`, `PublicCoin.FiniteMessage`, and
  `PrivateCoin.FiniteMessage` allow messages from arbitrary finite alphabets and prove conversions
  to and from the binary protocol model without changing the computed function or complexity.
- **Complexity notions.** `Deterministic.Complexity`, `PublicCoin.Complexity`, and
  `PrivateCoin.Complexity` define communication complexity as an `ENat` infimum over protocols,
  with the main existence/verification interfaces `communicationComplexity_le_iff`,
  `le_communicationComplexity_iff`, `communicationComplexity_le_iff_finiteMessage`, and
  `communicationComplexity_mono`.
- **Finite probability spaces.** `FiniteProbabilitySpace` packages finite probability spaces,
  real-valued measures, finite-sum integral formulas, conditioning over fibers, Markov-type
  estimates, and product-space identities used throughout the randomized proofs.
- **Information theory and total variation.** `InformationTheory.Entropy`,
  `InformationTheory.KLDivergence`, `InformationTheory.Pinsker`, and
  `InformationTheory.TVDistance` provide finite entropy, mutual information, conditional mutual
  information, KL-divergence formulas, Pinsker's inequality, and total-variation estimates.
- **Rectangle, rank, fooling-set, and discrepancy methods.** `Rectangle.Basic`,
  `Deterministic.Rectangle`, `Deterministic.Rank`, and `PublicCoin.Discrepancy` formalize
  monochromatic rectangle partitions, fooling sets, the log-rank method, and discrepancy lower
  bounds.
- **Randomness reductions.** `PublicCoin.CoinApproximation` and `PrivateCoin.CoinApproximation`
  approximate arbitrary finite probability spaces by `CoinTape`. `PublicCoin.Newman` formalizes a
  Newman-style reduction from public coins to private coins over finite input spaces.

## 4. Main Results

The following are the main theorem statements currently formalized. Here $D$ denotes deterministic
communication complexity, $D^{\to}$ deterministic one-way communication complexity,
$R^{\mathrm{pub}}_\varepsilon$ public-coin complexity at error $\varepsilon$,
$R^{\mathrm{pub},\to}_\varepsilon$ one-way public-coin complexity at error $\varepsilon$, and
$R^{\mathrm{priv}}_\varepsilon$ private-coin complexity at error $\varepsilon$.

### 4.1 Infrastructure and Lemmas

- `Deterministic.mono_partition_of_communicationComplexity_le`:
  if $D(g) \le n$, then $g$ has a monochromatic rectangle partition with at most $2^n$ parts.
- `Deterministic.le_communicationComplexity_of_forall_lt_ncard`:
  if every monochromatic rectangle partition of $g$ has more than $2^n$ parts, then
  $n + 1 \le D(g)$.
- `Deterministic.clog_ncard_le_communicationComplexity`:
  for every fooling set $S$ for $g$, $\lceil \log_2 |S| \rceil \le D(g)$.
- `Deterministic.clog_boolFunctionRank_le_communicationComplexity`:
  for Boolean $f$,
  $\lceil \log_2 \operatorname{rank}(f) \rceil \le D(f)$.
- `Deterministic.communicationComplexity_le_clog_card`,
  `communicationComplexity_le_clog_card_X_alpha`, and
  `communicationComplexity_le_clog_card_Y_alpha`:
  finite input/output cardinalities give the standard send-the-input upper bounds, including
  $D(f) \le \lceil \log_2 |X| \rceil + \lceil \log_2 |\alpha| \rceil$ and
  $D(f) \le \lceil \log_2 |Y| \rceil + \lceil \log_2 |\alpha| \rceil$.
- `PublicCoin.lt_communicationComplexity_of_forall_distributionalError_gt`:
  if some distribution makes every deterministic protocol of complexity at most $n$ err with
  probability greater than $\varepsilon$, then
  $n < R^{\mathrm{pub}}_\varepsilon(f)$.
- `PublicCoin.OneWay.lt_communicationComplexity_of_forall_distributionalError_gt`:
  the corresponding one-way public-coin minimax lower-bound principle:
  if every deterministic one-way protocol of cost at most $n$ has distributional error greater
  than $\varepsilon$, then $n < R^{\mathrm{pub},\to}_\varepsilon(f)$.
- `PublicCoin.lt_communicationComplexity_of_discrepancy_bound`:
  if every rectangle has discrepancy at most $\gamma$ and
  $2^n\gamma < 1 - 2\varepsilon$, then $n < R^{\mathrm{pub}}_\varepsilon(g)$.
- `PrivateCoin.communicationComplexity_le_deterministic`:
  for $\varepsilon \ge 0$, $R^{\mathrm{priv}}_\varepsilon(f) \le D(f)$.
- `PublicCoin.newman`:
  for finite $X$ and $Y$, if $1 < c$ and $c\varepsilon < \varepsilon'$, then
  $R^{\mathrm{priv}}_{\varepsilon'}(f) \le
  R^{\mathrm{pub}}_\varepsilon(f) +
  \lceil \log_2(\operatorname{derandomizationSamples}(X,Y,\varepsilon,c)) \rceil$.
- `Functions.InnerProduct.abs_discrepancy_le_of_isRectangle`:
  every rectangle has inner-product discrepancy at most $\sqrt{1 / 2^n}$ under the uniform
  distribution.
- `Functions.Indexing.one_ninth_lt_distributionalError_of_cost_le`:
  for $n \ge 300$, every deterministic one-way protocol for indexing with cost at most
  $n / 10$ has distributional error greater than $1 / 9$ under the uniform input distribution.
- `Functions.Disjointness.RandomizedLowerBound.const_mul_n_le_complexity_of_distributionalError_le`:
  under the hard disjointness distribution, every deterministic protocol with distributional error
  at most $1 / 32$ has complexity at least
  $\frac{(1/32768)^2 n}{3\log 2}$.

### 4.2 Capstone Theorems

- `Functions.Equality.communicationComplexity_eq`:
  $D(\mathrm{EQ}_n) = n + 1$ for $n \ge 1$.
- `Functions.Equality.publicCoin_communicationComplexity_le`:
  for $\varepsilon > 0$,
  $R^{\mathrm{pub}}_\varepsilon(\mathrm{EQ}_n) \le
  \lceil \log_2(\lceil \varepsilon^{-1} \rceil + 1) \rceil + 1$.
- `Functions.Disjointness.communicationComplexity_eq`:
  for $n \ge 1$, $D(\mathrm{DISJ}_n) = n + 1$.
- `Functions.Disjointness.RandomizedLowerBound.floor_div_pow_lt_publicCoin_communicationComplexity_disjointness`:
  $
  R^{\mathrm{pub}}_{1/32}(\mathrm{DISJ}_n) > n / 2^{32}$.
- `Functions.Indexing.oneWayCommunicationComplexity_eq`:
  $D^{\to}(\mathrm{IND}_n) = n$.
- `Functions.Indexing.div_ten_lt_publicCoinOneWay_communicationComplexity_one_ninth`:
  for $n \ge 300$,
  $R^{\mathrm{pub},\to}_{1/9}(\mathrm{IND}_n) > n/10$.
- `Functions.InnerProduct.publicCoin_le_communicationComplexity_of_hbound`:
  $R^{\mathrm{pub}}_\varepsilon(\mathrm{IP}_n) > n/2 - \log_2(\frac{1}{1 - 2\varepsilon})$.

## 5. File Guide

- `CommunicationComplexity/Basic.lean` and `Deterministic/Basic.lean` contain the core binary
  deterministic protocol model.
- `PublicCoin/*` and `PrivateCoin/*` contain randomized protocols, finite-message variants,
  complexity definitions, coin approximation, composition lemmas, minimax principles, discrepancy,
  and Newman reduction.
- `FiniteProbabilitySpace.lean` and `InformationTheory/*` contain the finite probability and
  information-theoretic support used by the randomized lower bounds.
- `Rectangle/Basic.lean`, `Deterministic/Rectangle.lean`, and `Deterministic/Rank.lean` contain the
  deterministic lower-bound infrastructure.
- `Functions/Equality.lean`, `Functions/Disjointness.lean`,
  `Functions/DisjointnessLowerBound.lean`, `Functions/Indexing.lean`, and
  `Functions/InnerProduct.lean` contain the formalized bounds for the main example functions.

## 6. References

- Kushilevitz, E. and Nisan, N. *Communication Complexity*. Cambridge University Press, 1997.
- Rao, A. and Yehudayoff, A. *Communication Complexity and Applications*. Cambridge University Press, 2020.
- Yao, A. C.-C. Some complexity questions related to distributive computing. *STOC*, 1979.
- Newman, I. Private vs. common random bits in communication complexity. *Information Processing Letters*, 1991.
- Razborov, A. On the distributional complexity of disjointness. *Theoretical Computer Science*, 1992.
