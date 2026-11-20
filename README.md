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
- `nondet_SemMod_simpleSpec_nondetSpec` (`Proof/NondetEq.v`): every run of `simpleSpec` is a run
  of `nondetSpec`, which takes arbitrary values in the don't-care fields.
- `pipelinedMod_refines_nondetSpec` (`Proof/NondetRefines.v`): the pipelined implementation
  refines `nondetSpec`, by transitivity.

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
| `NondetAlu.v` | `FreeVals` (the don't-care values) and `nondetAlu`: the arms of `specAlu`, with the don't-care fields taken from `FreeVals` |
| `NondetSpec.v` | `nondetSpec`: `simpleSpec` with a core step that draws `FreeVals` with `NonDet` (`Random`) before the ALU |
| `Proof/NondetEq.v` | `nondetAlu` with the datapath's leftover values is `specAlu`; `simpleSpec` runs are `nondetSpec` runs |
| `Proof/NondetRefines.v` | `pipelinedMod_refines_nondetSpec` |
| `SimpleSim/SimpleInst.v`, `NondetSim/NondetInst.v` | `simpleSpec` and `nondetSpec` on the concrete system of `cheriot/SpecInst.v`, extracted for simulation |

## Don't-care values

To be equal to `wrappedAlu` value for value, `specAlu` reproduces what the shared datapath
leaves in fields that are never read:

- `dstValue` of instructions without a register result;
- `NewPcc.ecap` of Branch, Cjal and Mret, and Mret's `NewPcc` address and tag and `interruptStatus`;
- `SpecialValue.tag` and `SpecialValue.ecap` of Csr.

`nondetSpec` takes arbitrary values (`NonDet`) for these fields instead. Every `simpleSpec` run is
a `nondetSpec` run, so the refinement carries over. The converse (the fields really are never
read: every `nondetSpec` run ends like the matching `simpleSpec` run) is not proved; the
simulator of `nondetSpec` (random values in these fields) checks it on the test suite.

## Build

```
make            # builds ../Guru, ../cheriot, then these proofs
```

or, when `../cheriot` is already built:

```
make Makefile.coq.all
make -j16 -f Makefile.coq.all
```

Simulators of `simpleSpec` and `nondetSpec` (needs `../cheriot` built):

```
make simrtlexe
cd ../cheriot && ./run_all_tests.sh ../SpecCheriot/SimpleSim/sim_obj_dir/VTb
cd ../cheriot && ./run_all_tests.sh ../SpecCheriot/NondetSim/sim_obj_dir/VTb
```

On the test suite (51 tests), both simulators pass everything, with the same cycle counts as
cheriot's spec simulator (test-suite: 7218435 cycles; "All tests finished in 6846144 cycles").

With `-j16` the proofs here take about 45 s wall time (about 275 s CPU); the largest `Qed` is
about 1.4 s.

## How the ALU proof is organized

The ALU equivalence is proved class by class. To keep each class cheap, `Proof/AluPre.v`
evaluates the shared stages once with the class left abstract, and `Proof/AluArms*.v` evaluates
each spec arm once; a class lemma then only reduces these precomputed terms with its concrete
class bits. No bit-vector reasoning is needed beyond `or 0 x = x` and the adder identities.

Each class lemma still spends about 0.9 s removing the multiplexer arms of the other classes.
A one-time syntactic transform of `Or` of `ITE` arms into nested `ITE` would remove this cost.

## Use of AI

AI was used to generate the spec, starting from the atomic, handwritten spec in
https://github.com/OpenSeCura/cheriot, whose ALU is closer to that of the implementation. The AI
was given an explicit directive to keep nondeterministic values in unused fields (`nondetAlu`),
and a clear template for generating the spec and for reusing single-purpose functions such as
`Bounds` from that repository. The resulting `nondetAlu` and `specAlu` specs were thoroughly
reviewed by humans. As described above, `specAlu` is proved equivalent to the atomic, handwritten
spec, and every run of `simpleSpec` is a run of `nondetSpec`. These proofs were also written by AI.
