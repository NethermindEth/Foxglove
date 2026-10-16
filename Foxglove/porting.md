# This file is worth reading, no robots desecrated it.

## Bluebell rules porting

_Old work_ is relative to:
https://github.com/Verified-zkEVM/iris-lean/blob/julek/Dan/refactor/Bluebell

Commit: `48b1b5c4b4e2ac2803c395745749ed11fd5750c1`

_New work_ is relative to:
https://github.com/NethermindEth/Foxglove/tree/Ferinko/newModel/Foxglove

Following the Bluebell paper https://arxiv.org/pdf/2402.18708, starting in the appendix, page 33.

Format:
<PAPER_NAME> | <OLD_WORK> | <NEW_WORK>

### Distribution ownership rules

- `AND-TO-STAR` | Rules.lean/And_To_Star | ~~Assertion.lean/AND_TO_STAR'~~

- `DIST-INJ` | Rules.lean/Dist_Inj | Assertion.lean/DIST_INJ

- `SURE-MERGE` | Rules.lean/Sure_Merge | Assertion.lean/SURE_MERGE

- `SURE-AND-STAR` | Rules.lean/Sure_And_Star | Assertion.lean/SURE_AND_STAR

- `PROD-SPLIT` | Rules.lean/Prod_Split | Assertion.lean/PROD_SPLIT

### Joint conditioning rules

- `C-TRUE` | Rules.lean/C_True | Assertion.lean/C_TRUE

- `C-TRUE` | Rules.lean/C_False | Assertion.lean/C_FALSE

- `C-CONS` | Rules.lean/C_Cons | Assertion.lean/C_CONS