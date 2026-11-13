(*
 * Copyright 2026 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

(* Precomputed evaluation of the spec arms of [specAlu] (part 3 of 4): [specXF] is the value
 * of [specX] with the functional units folded, computed once here so that the per-class lemmas
 * (AluC*.v) do not evaluate it again. *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.

Import ListNotations.
Local Open Scope guru_scope.

Definition specLuiF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specLui type a0).
Lemma specLui_eq : forall a0, evalLetExpr (@specLui type a0) = specLuiF a0. Proof. reflexivity. Qed.
Definition specCjalrF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 => evalLetExpr (@specCjalr type a0 a1 a2 a3).
Lemma specCjalr_eq : forall a0 a1 a2 a3, evalLetExpr (@specCjalr type a0 a1 a2 a3) = specCjalrF a0 a1 a2 a3. Proof. reflexivity. Qed.
Definition specCTestSubsetF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 => evalLetExpr (@specCTestSubset type a0 a1).
Lemma specCTestSubset_eq : forall a0 a1, evalLetExpr (@specCTestSubset type a0 a1) = specCTestSubsetF a0 a1. Proof. reflexivity. Qed.
Definition specMulDivF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 => evalLetExpr (@specMulDiv type a0 a1 a2).
Lemma specMulDiv_eq : forall a0 a1 a2, evalLetExpr (@specMulDiv type a0 a1 a2) = specMulDivF a0 a1 a2. Proof. reflexivity. Qed.
Definition specAddSubF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 a4 => evalLetExpr (@specAddSub type a0 a1 a2 a3 a4).
Lemma specAddSub_eq : forall a0 a1 a2 a3 a4, evalLetExpr (@specAddSub type a0 a1 a2 a3 a4) = specAddSubF a0 a1 a2 a3 a4. Proof. reflexivity. Qed.
Definition specCAndPermF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 => evalLetExpr (@specCAndPerm type a0 a1).
Lemma specCAndPerm_eq : forall a0 a1, evalLetExpr (@specCAndPerm type a0 a1) = specCAndPermF a0 a1. Proof. reflexivity. Qed.
Definition specCsrF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 => evalLetExpr (@specCsr type a0 a1 a2 a3).
Lemma specCsr_eq : forall a0 a1 a2 a3, evalLetExpr (@specCsr type a0 a1 a2 a3) = specCsrF a0 a1 a2 a3. Proof. reflexivity. Qed.
Definition specCGetHighF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specCGetHigh type a0).
Lemma specCGetHigh_eq : forall a0, evalLetExpr (@specCGetHigh type a0) = specCGetHighF a0. Proof. reflexivity. Qed.
Definition specCSetHighF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 => evalLetExpr (@specCSetHigh type a0 a1).
Lemma specCSetHigh_eq : forall a0 a1, evalLetExpr (@specCSetHigh type a0 a1) = specCSetHighF a0 a1. Proof. reflexivity. Qed.
Definition specFenceF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specFence type a0).
Lemma specFence_eq : forall a0, evalLetExpr (@specFence type a0) = specFenceF a0. Proof. reflexivity. Qed.
