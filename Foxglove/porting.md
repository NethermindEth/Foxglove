# Porting bookkeeping (hand-written)

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

- `AND-TO-STAR` | Rules.lean/And_To_Star | ~~Assertion.lean/AND_TO_STAR~~

- `DIST-INJ` | Rules.lean/Dist_Inj | Assertion.lean/DIST_INJ

- `SURE-MERGE` | Rules.lean/Sure_Merge | Assertion.lean/SURE_MERGE

- `SURE-AND-STAR` | Rules.lean/Sure_And_Star | Assertion.lean/SURE_AND_STAR (dropped hyp)

- `PROD-SPLIT` | Rules.lean/Prod_Split | Assertion.lean/PROD_SPLIT (style TODO pending | multi notation)

### Joint conditioning rules

- `C-TRUE` | Rules.lean/C_True | Assertion.lean/C_TRUE

- `C-FALSE` | Rules.lean/C_False | Assertion.lean/C_FALSE

- `C-CONS` | Rules.lean/C_Cons | Assertion.lean/C_CONS

- `C-FRAME` | Rules.lean/C_Frame | Assertion.lean/C_FRAME

- `C-UNIT_L` | Rules.lean/C_Unit_L | Assertion.lean/C_UNIT_L (droppped `Countable` requirement)

- `C-UNIT_R` | Rules.lean/C_Unit_R | Assertion.lean/C_UNIT_R

- `C-ASSOC` | Rules.lean/C_Assoc | Assertion.lean/C_ASSOC

- `C-UNASSOC` | Rules.lean/C_Unassoc | Assertion.lean/C_UNASSOC

- `C-AND` | Rules.lean/C_And | ~~Assertion.lean/C_AND~~

- `C-SKOLEM` | Rules.lean/C_Skolem | Assertion.lean/C_SKOLEM

- `C-TRANSF` | Rules.lean/C_Transf | Assertion.lean/C_TRANSF (use the support explicitly)

- `SURE-STR-CONVEX` | Rules.lean/Sure_Str_Convex | Assertion.lean/SURE_STR_CONVEX

- `C-FOR-ALL` | Rules.lean/C_For_All | Assertion.lean/C_FOR_ALL

- `C-PURE` | Rules.lean/C_Pure | Assertion.lean/C_PURE

### Structural WP rules

SKIPPED FOR NOW

### Program WP rules

SKIPPED FOR NOW

### Ownership and distributions

- `SURE-DIRAC` | Rules.lean/Sure_Dirac | Assertion.lean/SURE_DIRAC

- `SURE-EQ-INJ` | Rules.lean/Sure_Eq_Inj | Assertion.lean/SURE_EQ_INJ

- `SURE-SUB` | Rules.lean/Sure_Sub | Assertion.lean/SURE_SUB

- `DIST-FUN` | Rules.lean/Dist_Fun | Assertion.lean/DIST_FUN

- `DIRAC-DUP` | Rules.lean/Dirac_Dup | Assertion.lean/DIRAC_DUP

- `DIST-SUPP` | Rules.lean/Dist_Supp | Assertion.lean/DIST_SUPP

- `PROD-UNSPLIT` | Rules.lean/Prod_Unsplit | Assertion.lean/PROD_UNSPLIT

### Joint conditioning

- `C-FUSE` | Rules.lean/C_Fuse | Assertion.lean/C_FUSE

- `C-SWAP` | Rules.lean/C_Swap | Assertion.lean/C_SWAP

- `SURE-CONVEX` | Rules.lean/Sure_Convex | Assertion.lean/SURE_CONVEX

- `DIST-CONVEX` | Rules.lean/Dist_Convex | Assertion.lean/DIST_CONVEX

- `C-SURE-PROJ` | Rules.lean/C_Sure_Proj | Assertion.lean/C_SURE_PROJ

- `C-SURE-PROJ-MANY` | Rules.lean/C_Sure_Proj_Many | Assertion.lean/C_SURE_PROJ_MANY

- `C-EXTRACT` | Rules.lean/C_Extract | Assertion.lean/C_EXTRACT




