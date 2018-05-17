# AliveInLean

## Setup

- Download Lean 3.4.1 or later from https://leanprover.github.io/download/
- Extract it, and update PATH environmental variable so command `lean` can be executed on the command prompt
- Download & install z3 from https://github.com/Z3Prover/z3 and update PATH so `z3` can be executed as well
- Run `leanpkg upgrade` to install SMT lib interface and mathlib


## Run

```
# Run selected tests from Alive's test suite (which contain
# no precondition and do not require additional grammars)
./run-alive.sh
```

```
# Run random tests for the specification of Z3 expression -
# concrete value, as well as 4 admitted arithmetic lemmas.
# Note that bv_equiv.zext/sext/trunc will have 'omitted' tests
# because sometimes generated expressions try to compare
# bitvectors with different bitwidths.
./run-proptest.sh
```

More test scripts are in `scripts/`.


## Theorems

- Specification, as well as proof, is in `src/spec/`.

1. Execution of `bigstep_exe` with two different value semantics (SMT expr / concrete value)
has some good relations.

```
def encode (ss:irstate_smt) (se:irstate_exec) (η:freevar.env) :=
    irstate_equiv (η⟦ss⟧) se

def bigstep_both:= ∀ ss se (p:program) oss' ose' η
    (HENC:encode ss se η)
    (HOSS': oss' = bigstep_exe irsem_smt ss p)
    (HOSE': ose' = bigstep_exe irsem_exec se p),
  none_or_some oss' ose' (λ ss' se', encode ss' se' η)
-- Its proof is at equiv.lean
```

2. We can generate initial state correctly.

```
def init_state_encode:= ∀ (freevars:list (string × ty)) (sg sg':std_gen) ise iss
    (HUNQ: list.unique $ freevars.map prod.fst)
    (HIE:(ise, sg') = create_init_state_exec freevars sg)
    (HIS:iss = create_init_state_smt freevars),
  ∃ η, encode iss ise η
-- Its proof is at initialstate.lean
```

3. If refinement checking function `check_single_reg0` says it's true, refinement
indeed holds.

```
def refines_single_reg_correct := ∀ (psrc ptgt:program)
    (root:string) (ss0:irstate_smt) sb
    (HSREF:some sb = check_single_reg0 irsem_smt psrc ptgt root ss0)
    (HEQ:∀ (η0:freevar.env) e, b_equiv (η0⟦sb⟧) e → e = tt),
  root_refines_smt psrc ptgt ss0 root
-- Its proof is at refinement.lean
```

- TODO
    - Connect this with `check_single_reg`, which allows a target program to
      use definitions in the source program for convenience
    - Check that `freevars.get` correctly returns all free variables
    - Connect this with correctness criteria in Alive paper

# Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.microsoft.com.

When you submit a pull request, a CLA-bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., label, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.
