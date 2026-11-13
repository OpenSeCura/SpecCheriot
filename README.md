<!--
Copyright 2026 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-->

# SpecCheriot

A simpler, textbook-style specification of the CHERIoT core, proved equivalent to the
specification in `../cheriot`, so the refinement proof of the pipelined implementation carries
over to it.

In `../cheriot`, the ALU (`AluRouting` and `Alu` in `cheriot/Alu.v`) shares its functional units
between instructions: the decoded control bits route operands into shared adders, comparators
and multiplexers. Here, `specAlu` gives each instruction class its own if-then-else block, as a
textbook ISA description would. Single-purpose units (shifter, bounds, sealer, ...) are called
directly; the shared adders and comparators are written out per instruction.

## Main results

- `specAlu_eq_wrappedAlu` (`Proof/AluEq.v`): on every package the decoder can produce,
  `specAlu` returns exactly the same `AluOutUnion` as the shared ALU `wrappedAlu`.
- `spec_SemMod_spec_simpleSpec` / `spec_SemMod_simpleSpec_spec` (`Proof/SpecEq.v`): the
  original `spec` and `simpleSpec` have the same runs.
- `pipelinedMod_refines_simpleSpec` (`Proof/Refines.v`): the pipelined implementation refines
  `simpleSpec`.

`Print Assumptions pipelinedMod_refines_simpleSpec` shows only Guru's flags (`evalExpr`
guarded; `FullFormat` and `Expr` positive). There is no `Admitted` and no `Axiom`.

## Files

| File | Content |
|---|---|
| `Group.v` | `SpecClass` (one constructor per decoder class, plus `cNone`); `specGroup`, the decoder group of an instruction of a class; `SpecWellFormed` |
| `Alu.v` | `specAlu`: one block per class (`specLui`, `specBranch`, `specLoad`, ...); the don't-care values are documented in the header |
| `Spec.v` | `specStepWith alu` (the `specStep` of `cheriot/Spec.v` with the ALU as a parameter), `simpleSpecStep`, `simpleSpec` |
| `Proof/Decode.v` | `spec_decode_wellformed`: the decoder only produces well-formed groups |
| `Proof/AluLib.v` | tactics, the class-independent output fields, and the per-class statements |
| `Proof/AluPre.v` | staged evaluation: `constructAluIn`, `AluRouting`, `Alu` and the dispatch of `specAlu`, each evaluated once |
| `Proof/AluArms1..4.v` | each spec arm evaluated once |
| `Proof/AluC1..8.v` | the 82 per-class lemmas (output value and op for each class) |
| `Proof/AluEq.v` | `specAlu_eq_wrappedAlu` |
| `Proof/SpecEq.v` | `spec` and `simpleSpec` have the same runs |
| `Proof/Refines.v` | `pipelinedMod_refines_simpleSpec` |

## Don't-care values

To be equal to `wrappedAlu` value for value, `specAlu` reproduces what the shared datapath
leaves in fields that are never read:

- `dstValue` of instructions without a register result;
- `NewPcc.ecap` of Branch, Cjal and Mret, and Mret's `NewPcc` address and tag and `interruptStatus`;
- `SpecialValue.tag` and `SpecialValue.ecap` of Csr.

Replacing them with arbitrary values would need a proof that `executeNonDeferred` and the
deferred commit ignore these fields. A natural way: a further spec with nondeterministic
values, related to `simpleSpec` by run inclusion.

## Build

```
make            # builds ../Guru, ../cheriot, then these proofs
```

or, when `../cheriot` is already built:

```
make Makefile.coq.all
make -j16 -f Makefile.coq.all
```

With `-j16` the proofs here take about 45 s wall time (about 275 s CPU); the largest `Qed` is
about 1.4 s.

## How the ALU proof is organized

The ALU equivalence is proved class by class. To keep each class cheap, `Proof/AluPre.v`
evaluates the shared stages once with the class left abstract, and `Proof/AluArms*.v` evaluates
each spec arm once; a class lemma then only reduces these precomputed terms with its concrete
class bits. No bit-vector reasoning is needed beyond `or 0 x = x` and the adder identities.

Each class lemma still spends about 0.9 s removing the multiplexer arms of the other classes.
A one-time syntactic transform of `Or` of `ITE` arms into nested `ITE` would remove this cost.
