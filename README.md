# Foxglove

A Lean 4 formalisation of a separation logic for probabilistic programs.

The Foxglove logic is based primarily on **Bluebell**, with some ideas borrowed from
**Amaryllis** in order to extend it to functional Hoare triples.

## Layout

| Path | Contents |
| --- | --- |
| `Foxglove/OURA.lean` | Ordered unital resource algebras, and the BI built from upper sets of one (`Iris.UpperSetBI`). Intended to be upstreamed into [iris-lean](https://github.com/leanprover-community/iris-lean)'s `IrisMath`. |
| `Foxglove/MeasureOnSpace.lean` | Probability spaces carrying their own σ-algebra (`ProbSpace`), their independent product, weighted sums, and the resource algebra they form. Intended to become a standalone library. |
| `Foxglove/Basic.lean` | The Foxglove model: the sample space `Ω`, random variables, and the resource-algebra instances for it. |
| `Foxglove/Interp/Bernoulli/` | The free Bernoulli monad `BernoulliM` (`flip`, `split`) and its interpretation into probability spaces. `Helper.lean` holds `ℝ≥0∞` bookkeeping, `Example.lean` the worked examples. |
| `Foxglove/Interp/OracleComp/` | `BernoulliInterpretable` and `interp`: compiling a VCVio `OracleComp` down into `BernoulliM`. |

## Building

```
lake exe cache get   # optional, fetches Mathlib oleans
lake build
```
