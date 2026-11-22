# Erdős 349 · Exponential floors and additive completeness

For every fixed positive base, this project describes the positive coefficients for which all sufficiently large integers are sums of distinct values of the exponential floor sequence. For a base strictly between one and two, the answer is a countable union of explicit half-open intervals. A finite word of integers and a finite subset-sum computation determine each interval. Its endpoints are rational functions of the base. Every good coefficient has a finite witness and belongs to a whole right-hand interval of good coefficients. At base two the answer is exactly the inverse powers of two, including one. All other positive bases outside the open strip give the empty set in the distinct-value convention.

The project also supplies explicit algebraic parameters, with base approximately 1.5970050092, for which every floor is even. This verifies a concrete instance of the failure of the proposed golden-ratio conjecture. Geneson previously refuted that conjecture using Dubickas's work. The parameter description does not give a terminating decision procedure for negative instances in the open strip. The separate questions concerning the parities of the unscaled powers of 3/2 are outside these theorems. [Written proof, interval endpoints, numerical certificates and sources](PROOF.md)

| Lean declaration | Result |
|---|---|
| [FloorPowers.erdos_349](Prize.lean) | Equality to the explicit parameter set, using integer floors, finite sets of distinct values and eventual membership at infinity |
| [FloorPowers.complete_iff_union_of_intervals](ParameterSet.lean) | Both directions of the interval description |
| [FloorPowers.right_stability](ParameterSet.lean) | Right-hand stability at each good coefficient on the open strip |
| [FloorPowers.complete_base_two_iff](Boundary.lean) | Necessary and sufficient condition at base two |
| [FloorPowers.Example.every_floor_even](Counterexample.lean) | All exponents of the displayed algebraic pair have even floor |
| [FloorPowers.golden_ratio_counterexample](Prize.lean) | Negation of the golden-ratio conjecture in the integer formulation |
| [FloorPowers.Occurrences.full_range](Occurrences.lean) | Parameter description for distinct indices, allowing repeated values at different indices |

The main theorem matches the positive-pair set and the distinct-value definition in Formal Conjectures. The answer on its right side uses integer words, intervals, and a decidable finite test. The historical distinct-index convention is handled separately, including the different behavior at base one. [Formal Conjectures, Erdős 349](https://github.com/google-deepmind/formal-conjectures/blob/2207c54d0dbe960de591d280f997b195bf3f6e28/FormalConjectures/ErdosProblems/349.lean) · [Historical formulation and results](https://arxiv.org/abs/2602.23394)

## Reproduce

Install the Lean version pinned in `lean-toolchain` and run the following from the repository root.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
python verify_counterexample.py
```

Lean 4.31.0 and mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` are pinned. The kernel checks the root existence, rational inequalities, polynomial interpolation and parity for every exponent. The Python script independently reproduces the rational enclosures in the written proof using only the standard library. All displayed declarations in the axiom audit use only `propext`, `Classical.choice`, and `Quot.sound`.

## Authorship and prior work

The submission is maintained by the GitHub account jackanderson123456. OpenAI Codex prepared the mathematical construction, exposition and Lean code for this submission. Existing contributions include Graham's and van Doorn's interval arguments, Geneson's prior counterexample based on Dubickas, and prior Lean proofs of several boundary cases by cepadugato. The five-root interpolation certificate and the joint proof of the full fiber description are given in this repository for review. [van Doorn](https://arxiv.org/abs/2602.23394) · [Geneson](https://arxiv.org/abs/2609.25107) · [Dubickas](https://doi.org/10.1017/S0017089506003090) · [Prior Lean boundary cases](https://github.com/cepadugato/formal-conjectures/blob/19e39e33be27d46713a423263d38312fe40c9e78/FormalConjectures/ErdosProblems/349.lean)
