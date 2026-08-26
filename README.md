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
  values, reachability/until/safety operators, and fixed-point-certificate
  combinators for verifying computed values against those operators without
  re-deriving the operators' own correctness.

`Mdp` is nested inside `Csg` mathematically (an MDP is a one-player CSG),
but the two are kept as sibling Lean libraries here because `Mdp` is a
port of existing, published work and `Csg` is new material built on top
of it — the split is about provenance, not about the underlying theory.

## Status

Early and incomplete. The `Mdp` line covers value iteration and policy
iteration. The `Csg` line currently covers: matrix-game values and their
continuity, monotone CSG operators, and certificate combinators for
reachability, until, reward-until, and safety objectives in the zero-sum
(two-coalition, competing) case. General-sum equilibria (Nash/SWNE/SCNE)
are not yet formalized — the relevant obstructions are noted in the
project's working notes but are out of scope for this repository as it
stands.

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

**The certificate-combinator methodology** (the "automate only the
assembly of a candidate fixed point into a correctness proof, not the
discharge of its side conditions" pattern used throughout `Csg/`) follows
the approach of:

- Krishnendu Chatterjee, Tim Quatmann, Maximilian Schäffeler,
  Maximilian Weininger, Tobias Winkler, and Daniel Zilken,
  ["Fixed Point Certificates for Reachability and Expected Rewards in MDPs"](https://link.springer.com/chapter/10.1007/978-3-031-90653-4_7)
  (reachcert), TACAS 2025.
