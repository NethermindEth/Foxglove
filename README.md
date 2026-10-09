<p align="center">
  <img src="docs/assets/foxglove-logo.png" alt="Foxglove logo" width="250">
</p>

# Foxglove

A Lean 4 formalisation of a separation logic for probabilistic programs using Iris-lean. 
Intend to aid in formally verifying cryptographic primitives formalised as part of the [ArkLib](https://github.com/Verified-zkEVM/ArkLib) effort. 

The Foxglove logic is based primarily on **Bluebell**, with some ideas borrowed from
**Amaryllis** in order to extend it to functional Hoare triples.

## Layout

| Path | Contents |
| --- | --- |
| `Foxglove/OURA.lean` | Ordered unital resource algebras, and the BI built from upper sets of one (`Iris.UpperSetBI`). Intended to be upstreamed into [iris-lean](https://github.com/leanprover-community/iris-lean)'s `IrisMath`. |
| `Foxglove/MeasureOnSpace.lean` | Probability spaces carrying their own σ-algebra (`ProbSpace`), their independent product and weighted sums, and the ordered unital resource algebra they form. Intended to split out into a probabilistic-foundations repo. |
| `Foxglove/Basic.lean` | The Foxglove model: the sample space `Ω`, random variables, and the CMRA/UCMRA/BI instances for `PSp Ω`. |
| `Foxglove/Interp/Bernoulli/` | The free Bernoulli monad `BernoulliM` (`flip`, `split`) and its interpretation into probability spaces. `Helper.lean` holds `ℝ≥0∞` bookkeeping, `Example.lean` the worked examples. |
| `Foxglove/Interp/OracleComp/` | `BernoulliInterpretable` and `interp`: compiling a VCVio `OracleComp` down into `BernoulliM`. |

## Building

```
lake exe cache get   # optional, fetches Mathlib oleans
lake build
```
