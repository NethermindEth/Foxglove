# Porting bookkeeping (hand-written)

## Bluebell rules porting

_Old work_ is relative to:
https://github.com/Verified-zkEVM/iris-lean/blob/julek/Dan/refactor/Bluebell

Commit: `48b1b5c4b4e2ac2803c395745749ed11fd5750c1`

_New work_ is relative to:
https://github.com/NethermindEth/Foxglove/tree/Ferinko/newModel/Foxglove

Since the split of 2026-10-21 the rules live in `Foxglove/Rules.lean`, one sign-posted
theorem per paper rule; the supporting lemmas are under `Foxglove/Rules/` and
`Foxglove/Algebra/`.

Following the Bluebell paper https://arxiv.org/pdf/2402.18708, starting in the appendix, page 33.

Format:
<PAPER_NAME> | <OLD_WORK> | <NEW_WORK>

### Distribution ownership rules

- `AND-TO-STAR` | Rules.lean/And_To_Star | ~~Rules.lean/AND_TO_STAR~~ (n-ary side condition)

- `DIST-INJ` | Rules.lean/Dist_Inj | Rules.lean/DIST_INJ

- `SURE-MERGE` | Rules.lean/Sure_Merge | Rules.lean/SURE_MERGE

- `SURE-AND-STAR` | Rules.lean/Sure_And_Star | Rules.lean/SURE_AND_STAR (dropped hyp)

- `PROD-SPLIT` | Rules.lean/Prod_Split | Rules.lean/PROD_SPLIT (pair written `E₁ ×ᵣ E₂`)

### Joint conditioning rules

- `C-TRUE` | Rules.lean/C_True | Rules.lean/C_TRUE

- `C-FALSE` | Rules.lean/C_False | Rules.lean/C_FALSE

- `C-CONS` | Rules.lean/C_Cons | Rules.lean/C_CONS

- `C-FRAME` | Rules.lean/C_Frame | Rules.lean/C_FRAME

- `C-UNIT_L` | Rules.lean/C_Unit_L | Rules.lean/C_UNIT_L (droppped `Countable` requirement)

- `C-UNIT_R` | Rules.lean/C_Unit_R | Rules.lean/C_UNIT_R

- `C-ASSOC` | Rules.lean/C_Assoc | Rules.lean/C_ASSOC

- `C-UNASSOC` | Rules.lean/C_Unassoc | Rules.lean/C_UNASSOC

- `C-AND` | Rules.lean/C_And | ~~Rules.lean/C_AND~~ (n-ary side condition)

- `C-SKOLEM` | Rules.lean/C_Skolem | Rules.lean/C_SKOLEM

- `C-TRANSF` | Rules.lean/C_Transf | Rules.lean/C_TRANSF (use the support explicitly)

- `SURE-STR-CONVEX` | Rules.lean/Sure_Str_Convex | Rules.lean/SURE_STR_CONVEX

- `C-FOR-ALL` | Rules.lean/C_For_All | Rules.lean/C_FOR_ALL

- `C-PURE` | Rules.lean/C_Pure | Rules.lean/C_PURE

### Structural WP rules

- `WP-CONS` | — | Rules.lean/WPCons

- `WP-FRAME` | — | Rules.lean/WPFrame

- `WP-NEST` | — | n/a (no composition of program tuples)

- `WP-CONJ` | — | n/a (n-ary side condition)

- `C-WP-SWAP` | — | Rules.lean/CWPSwap (`AEProper` in place of `ownX`)

### Program WP rules

- `WP-SAMP` | — | Rules.lean/WPFlip (instance of Rules.lean/WPDist, the law of any closed program)

- `WP-SKIP`, `WP-SEQ`, `WP-ASSIGN`, `WP-IF-PRIM`, `WP-LOOP-UNF`, `WP-LOOP` | — | n/a (imperative);
  sequencing is Amaryllis's `WP-BIND`, Rules.lean/WPBindC and Rules.lean/WPBind

### Ownership and distributions

- `SURE-DIRAC` | Rules.lean/Sure_Dirac | Rules.lean/SURE_DIRAC

- `SURE-EQ-INJ` | Rules.lean/Sure_Eq_Inj | Rules.lean/SURE_EQ_INJ

- `SURE-SUB` | Rules.lean/Sure_Sub | Rules.lean/SURE_SUB

- `DIST-FUN` | Rules.lean/Dist_Fun | Rules.lean/DIST_FUN

- `DIRAC-DUP` | Rules.lean/Dirac_Dup | Rules.lean/DIRAC_DUP

- `DIST-SUPP` | Rules.lean/Dist_Supp | Rules.lean/DIST_SUPP

- `PROD-UNSPLIT` | Rules.lean/Prod_Unsplit | Rules.lean/PROD_UNSPLIT

### Joint conditioning

- `C-FUSE` | Rules.lean/C_Fuse | Rules.lean/C_FUSE

- `C-SWAP` | Rules.lean/C_Swap | Rules.lean/C_SWAP

- `SURE-CONVEX` | Rules.lean/Sure_Convex | Rules.lean/SURE_CONVEX

- `DIST-CONVEX` | Rules.lean/Dist_Convex | Rules.lean/DIST_CONVEX

- `C-SURE-PROJ` | Rules.lean/C_Sure_Proj | Rules.lean/C_SURE_PROJ (via Rules.lean/C_PROJ_OF_CONVEX)

- `C-SURE-PROJ-MANY` | Rules.lean/C_Sure_Proj_Many | Rules.lean/C_SURE_PROJ_MANY

- `C-EXTRACT` | Rules.lean/C_Extract | Rules.lean/C_EXTRACT

- `C-DIST-PROJ` | — | Rules.lean/C_DIST_PROJ (via Rules.lean/C_PROJ_OF_CONVEX)
