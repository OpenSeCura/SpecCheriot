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

(* Precomputed evaluation of the spec arms of [specAlu] (part 2 of 4): [specXF] is the value
 * of [specX] with the functional units folded, computed once here so that the per-class lemmas
 * (AluC*.v) do not evaluate it again. *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.

Import ListNotations.
Local Open Scope guru_scope.

Definition specStoreF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 => evalLetExpr (@specStore type a0 a1 a2).
Lemma specStore_eq : forall a0 a1 a2, evalLetExpr (@specStore type a0 a1 a2) = specStoreF a0 a1 a2. Proof. reflexivity. Qed.
Definition specCGetBaseTopF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 => evalLetExpr (@specCGetBaseTop type a0 a1 a2).
Lemma specCGetBaseTop_eq : forall a0 a1 a2, evalLetExpr (@specCGetBaseTop type a0 a1 a2) = specCGetBaseTopF a0 a1 a2. Proof. reflexivity. Qed.
Definition specSltF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 => evalLetExpr (@specSlt type a0 a1 a2 a3).
Lemma specSlt_eq : forall a0 a1 a2 a3, evalLetExpr (@specSlt type a0 a1 a2 a3) = specSltF a0 a1 a2 a3. Proof. reflexivity. Qed.
Definition specCSetEqualF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 => evalLetExpr (@specCSetEqual type a0 a1).
Lemma specCSetEqual_eq : forall a0 a1, evalLetExpr (@specCSetEqual type a0 a1) = specCSetEqualF a0 a1. Proof. reflexivity. Qed.
Definition specShiftF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 => evalLetExpr (@specShift type a0 a1 a2 a3).
Lemma specShift_eq : forall a0 a1 a2 a3, evalLetExpr (@specShift type a0 a1 a2 a3) = specShiftF a0 a1 a2 a3. Proof. reflexivity. Qed.
Definition specScrF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 => evalLetExpr (@specScr type a0 a1 a2).
Lemma specScr_eq : forall a0 a1 a2, evalLetExpr (@specScr type a0 a1 a2) = specScrF a0 a1 a2. Proof. reflexivity. Qed.
Definition specCGetTypeF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specCGetType type a0).
Lemma specCGetType_eq : forall a0, evalLetExpr (@specCGetType type a0) = specCGetTypeF a0. Proof. reflexivity. Qed.
Definition specCGetTagF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specCGetTag type a0).
Lemma specCGetTag_eq : forall a0, evalLetExpr (@specCGetTag type a0) = specCGetTagF a0. Proof. reflexivity. Qed.
Definition specECallF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specECall type a0).
Lemma specECall_eq : forall a0, evalLetExpr (@specECall type a0) = specECallF a0. Proof. reflexivity. Qed.
