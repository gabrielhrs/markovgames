# markovgames

A Lean 4 / Mathlib formalization of algorithms and certificates for Markov
decision processes (MDPs) and their generalization to concurrent stochastic
games (CSGs). Work in progress.

The repository has two parts:

- **`Mdp/`** — a direct Lean 4 port of the single-player theory: Bellman
  operators, value iteration, and policy iteration for MDPs, following the
  Isabelle/HOL development cited below.
- **`Csg/`** — a from-scratch formalization of the multi-player
  generalization (concurrent stochastic games), including matrix-game
  values, backward induction for bounded objectives, reachability/until/
  reward-until/safety operators for the infinite-horizon case, and
  fixed-point-certificate combinators (both exact-pinning and interval/
  sandwiched forms) for verifying computed values against those operators
  without re-deriving the operators' own correctness.

`Mdp` is nested inside `Csg` mathematically (an MDP is a one-player CSG),
but the two are kept as sibling Lean libraries here because `Mdp` is a
port of existing, published work and `Csg` is new material built on top
of it — the split is about provenance, not about the underlying theory.

## Status

The `Mdp` line (value iteration, policy iteration) is done, confirmed against a
hand-solved closed form. The `Csg` line's zero-sum (two-coalition,
competing) theory is done and validated end to end: bounded objectives via
backward induction, and infinite-horizon reachability/until/reward-until/
safety objectives via monotone fixed-point operators plus certificate
combinators (exact-pinning and interval/sandwiched forms) — every piece of
routing checked against at least one worked instance, from the classic
small examples (matching pennies, rock-paper-scissors) up to a real,
published, third-party model (PRISM-games' intrusion-detection case study,
independently cross-checked against a live PRISM-games run). The
Büchi/co-Büchi (`◇□`/`□◇`) fixed-point-of-a-fixed-point operators are done
too, following de Alfaro and Majumdar above, with a worked instance
(`ConcurrentCoBuchiExample.lean`, their own Example 3 / Fig. 1) confirming
their paper's own point: the MDP shortcut of reducing a Büchi/co-Büchi
condition to plain reachability of the almost-surely-winning set fails for
genuinely concurrent games.

## Credits

This is an independent reformalization in Lean 4, inspired by and citing
the following prior work. It does not incorporate their source code, so no
licensing terms are inherited from them — only their mathematical content
and, in the case of the AFP entries, their proof strategy for the ported
`Mdp/` material.

**The ported MDP theory** (`Mdp/`) follows:

- Maximilian Schäffeler and Mohammad Abdulaziz,
  ["Verified Algorithms for Solving Markov Decision Processes"](https://www.isa-afp.org/entries/MDP-Algorithms.html),
  Archive of Formal Proofs, 2021.
- Maximilian Schäffeler and Mohammad Abdulaziz,
  ["Markov Decision Processes with Rewards"](https://www.isa-afp.org/entries/MDP-Rewards.html),
  Archive of Formal Proofs, 2021.

**The CSG mathematics** (`Csg/`) formalizes definitions and results from:

- Marta Kwiatkowska, Gethin Norman, David Parker, and Gabriel Santos,
  ["Automatic Verification of Concurrent Stochastic Systems"](https://link.springer.com/article/10.1007/s10703-020-00356-y),
  Formal Methods in System Design, vol. 58, 2021.
- Marta Kwiatkowska, Gethin Norman, David Parker, and Gabriel Santos,
  ["Multi-player Equilibria Verification for Concurrent Stochastic Games"](https://link.springer.com/chapter/10.1007/978-3-030-59854-9_7),
  QEST 2020, LNCS 12289, Springer.
- Luca de Alfaro and Rupak Majumdar,
  ["Quantitative Solution of Omega-Regular Games"](https://doi.org/10.1016/j.jcss.2003.07.009),
  Journal of Computer and System Sciences, vol. 68, no. 2, 2004, pp. 374-397. The source for
  `Csg/BuchiOp.lean`/`Csg/CoBuchiOp.lean`'s Büchi/co-Büchi Bellman operators (eq. (4)/(5)) and
  `Csg/ConcurrentCoBuchiExample.lean`'s worked instance (Example 3 / Fig. 1, p. 395).

**The certificate-combinator methodology** (the "automate only the
assembly of a candidate fixed point into a correctness proof, not the
discharge of its side conditions" pattern used throughout `Csg/`) follows
the approach of:

- Krishnendu Chatterjee, Tim Quatmann, Maximilian Schäffeler,
  Maximilian Weininger, Tobias Winkler, and Daniel Zilken,
  ["Fixed Point Certificates for Reachability and Expected Rewards in MDPs"](https://link.springer.com/chapter/10.1007/978-3-031-90653-4_7)
  (reachcert), TACAS 2025.
