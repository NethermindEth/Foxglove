<p align="center">
  <img src="docs/assets/foxglove-logo.png" alt="Foxglove logo" width="250">
</p>

# Foxglove

Foxglove is a Lean 4 formalisation, on top of
[iris-lean](https://github.com/leanprover-community/iris-lean), of a separation logic for
probabilistic programs. It is intended to support the verification of cryptographic
primitives formalised in [ArkLib](https://github.com/Verified-zkEVM/ArkLib), whose programs are
written in [VCVio](https://github.com/Verified-zkEVM/VCV-io)'s `OracleComp` monad.

The logic is that of **Bluebell** (Bao, D'Osualdo and Farzan,
[arXiv:2402.18708](https://arxiv.org/abs/2402.18708)), restricted to its unary fragment. From
Bluebell come the resources and the assertion language: a resource is a probability space
carrying its own σ-algebra, separating conjunction is the independent product of two such
spaces, and the assertions are ownership of a space, a random variable having a law
(`E ~ μ`), almost-sure facts (`⌈E⌉`), and the joint conditioning modality (`𝒞⟨μ⟩ v; K v`),
which lets conditional reasoning take place inside the logic. Bluebell's rules for these
connectives (Fig. 9 and Fig. 11 of the paper) and its structural rules for the weakest
precondition (Fig. 10) are all in `Foxglove/Rules.lean`, each theorem named after the rule it
formalises. Left out is everything about relating several programs (relational lifting,
indexed assertions, and the rules with index side conditions) and everything about an
imperative store (permissions, assignment and loops), because Foxglove's programs are
functional.

That last difference is where **Amaryllis** (Lohse, Rohde, Xin, Mück, Kuhn, Dreyer, Garg and
D'Osualdo, [arXiv:2605.13765](https://arxiv.org/abs/2605.13765)) comes in. Bluebell's weakest
precondition is about commands acting on a variable store; Foxglove's, like Amaryllis's, is
about a monadic program returning a value, so sequencing is monadic bind rather than `;` and
the result of a program is a random variable. From Amaryllis come the packaging of the
resources as an ordered unital resource algebra whose upper sets form the BI, the
kernel-based definition of the conditioning modality, the bind rule (`WP_BIND_COND`,
`WP_BIND_C`), the rule that moves a conditioning through `wp` (`C_WP_SWAP`), the requirement that
postconditions be invariant under almost-sure equality (`AEProper`), and a few conditioning
rules (`c-bind`, `distr-subst`, `distr-dirac`). Amaryllis's heap, permissions and frameability
modality are not taken: there is no mutable state, so none of that machinery is owed.

The semantics underneath is an adaptation of Amaryllis's. Amaryllis runs a program on a
probability space by its collecting semantics on indexed valuations (§4.1): a step picks an
atom of the current space and splits it in two along the coin flip the program makes there,
the configuration is carried as a random variable over outcomes, and the big-step relation
`⇓` closes that step. Foxglove keeps that structure and changes the language and the space:
programs are terms of a free monad of coin flips (what VCVio's `OracleComp` compiles to)
rather than pHeapLang, the sample space is the fixed tape `Ω = ℕ → Bool` with the atoms of a
space being cylinder sets of tapes, and a run is computed as the fixpoint of splitting
(`bigStep`, `fixpoint`) rather than as the closure of a step relation, so that it is a function
of the program and the input space. The randomness a run adds is the bits it read
(`freshMs`), and, as in Amaryllis, where an atom is an event of nonzero probability, atoms of
measure zero are not stepped (`prunePrograms`). The weakest precondition has Bluebell's shape
(Def. 4.14: quantify over the ambient space and a frame, and produce a witness inside the
output space), with one extra clause bounding what the witness may measure. Every rule in
`Rules.lean` is proved against this model, with no axioms beyond Lean's own.

This work was generously funded by the Ethereum Foundation.

## Layout

| Path | Contents |
| --- | --- |
| `Foxglove/Basic.lean` | The sample space `Ω` (infinite tapes of coin flips) and random variables `RV α` over it. |
| `Foxglove/Algebra/OURA.lean` | Ordered unital resource algebras, and the BI built from upper sets of one (`Iris.UpperSetBI`). Intended to be upstreamed into [iris-lean](https://github.com/leanprover-community/iris-lean)'s `IrisMath`. |
| `Foxglove/Algebra/MeasureOnSpace.lean` | Probability spaces carrying their own σ-algebra (`PSpace`, `PSp`), their independent product and weighted sums, bounded footprints, and the ordered unital resource algebra they form. Intended to split out into a probabilistic-foundations repo. |
| `Foxglove/Algebra/PMF.lean`, `Kernel.lean`, `PSpace.lean` | The measure theory the rules rest on: products, fusion and pushforward of laws and integration against them; Markov kernels into a space; trims, tilts, mixtures, null sets and the law of a random variable on a space. |
| `Foxglove/Interp/Bernoulli/` | The free Bernoulli monad `BernoulliM` (`flip`) and its big-step semantics over the tape: `ProbTree`, `fixpoint`, `bigStep`, `run`, the fresh randomness `freshMs` of a run, and the composition of runs (`run_bind`). `Helper.lean` holds `ℝ≥0∞` bookkeeping, `Example.lean` worked examples at the level of the semantics. |
| `Foxglove/Interp/OracleComp/` | `OracleBernoulliInterpretable` and `interp`: compiling a VCVio `OracleComp` down into `BernoulliM`, with `split` (rejection sampling on coin flips) implementing the uniform oracle `unifSpec`. `Law.lean` proves that this compilation agrees with VCVio's measure semantics (`lawOf_interp`: `lawOf (interp oa) a = 𝒟[oa] {a}`), and `WP.lean` turns a distribution VCVio computes into a specification (`wp_of_evalDist`). `Adequacy.lean` goes back: a law the logic proves for a closed program is VCVio's distribution (`evalDist_of_wp`), and `Expectation.lean` reads it in Lean core's `Std.WP`, through VCVio's expectation reading (`Expectation.wp_eq_tsum_of_wp`). |
| `Foxglove/Assertion.lean` | The assertion language: `FProp`, ownership `own`/`ownP`, joint conditioning `𝒞⟨μ⟩ v; K v`, laws `E ~ μ`, sure facts `⌈E⌉`, `valuePost`, and the weakest precondition `wp`. |
| `Foxglove/Rules.lean` | The rules of the logic: Bluebell's unary rules and Amaryllis's bind and conditioning rules, one theorem per rule, each sign-posted with the paper's name. |
| `Foxglove/Rules/` | What the rules are proved from: theorems specific to each connective (`Ownership`, `Sure`, `Conditioning`, `Distribution`, `WP`), the semantic cores of the long `wp` rules (`WP/Swap`, `WP/Bind`, `WP/Dist`), the side conditions on postconditions (`WP/Post`), and the counterexamples that fix the side conditions (`WP/Counterexamples`). |
| `Foxglove/Example.lean` | Worked examples in the logic: BI facts in the proof mode, and the uniform-sampling specification of the `unifSpec` query, proved from the rules. |
| `Foxglove/porting.md` | Bookkeeping of the Bluebell rule port. |

## Building

```
lake exe cache get   # optional, fetches Mathlib oleans
lake build
```
