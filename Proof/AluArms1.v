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

(* Precomputed evaluation of the spec arms of [specAlu] (part 1 of 4): [specXF] is the value
 * of [specX] with the functional units folded, computed once here so that the per-class lemmas
 * (AluC*.v) do not evaluate it again. *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.

Import ListNotations.
Local Open Scope guru_scope.

Definition specCSetAddrF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 => evalLetExpr (@specCSetAddr type a0 a1).
Lemma specCSetAddr_eq : forall a0 a1, evalLetExpr (@specCSetAddr type a0 a1) = specCSetAddrF a0 a1. Proof. reflexivity. Qed.
Definition specMretF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 => evalLetExpr (@specMret type a0 a1 a2).
Lemma specMret_eq : forall a0 a1 a2, evalLetExpr (@specMret type a0 a1 a2) = specMretF a0 a1 a2. Proof. reflexivity. Qed.
Definition specCSetBoundsF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 a4 a5 => evalLetExpr (@specCSetBounds type a0 a1 a2 a3 a4 a5).
Lemma specCSetBounds_eq : forall a0 a1 a2 a3 a4 a5, evalLetExpr (@specCSetBounds type a0 a1 a2 a3 a4 a5) = specCSetBoundsF a0 a1 a2 a3 a4 a5. Proof. reflexivity. Qed.
Definition specSealUnsealF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 => evalLetExpr (@specSealUnseal type a0 a1 a2).
Lemma specSealUnseal_eq : forall a0 a1 a2, evalLetExpr (@specSealUnseal type a0 a1 a2) = specSealUnsealF a0 a1 a2. Proof. reflexivity. Qed.
Definition specLoadF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 => evalLetExpr (@specLoad type a0 a1).
Lemma specLoad_eq : forall a0 a1, evalLetExpr (@specLoad type a0 a1) = specLoadF a0 a1. Proof. reflexivity. Qed.
Definition specCGetLenF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specCGetLen type a0).
Lemma specCGetLen_eq : forall a0, evalLetExpr (@specCGetLen type a0) = specCGetLenF a0. Proof. reflexivity. Qed.
Definition specCGetPermF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specCGetPerm type a0).
Lemma specCGetPerm_eq : forall a0, evalLetExpr (@specCGetPerm type a0) = specCGetPermF a0. Proof. reflexivity. Qed.
Definition specCGetAddrF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specCGetAddr type a0).
Lemma specCGetAddr_eq : forall a0, evalLetExpr (@specCGetAddr type a0) = specCGetAddrF a0. Proof. reflexivity. Qed.
Definition specCClearTagF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specCClearTag type a0).
Lemma specCClearTag_eq : forall a0, evalLetExpr (@specCClearTag type a0) = specCClearTagF a0. Proof. reflexivity. Qed.
