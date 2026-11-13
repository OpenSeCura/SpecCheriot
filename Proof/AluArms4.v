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

(* Precomputed evaluation of the spec arms of [specAlu] (part 4 of 4): [specXF] is the value
 * of [specX] with the functional units folded, computed once here so that the per-class lemmas
 * (AluC*.v) do not evaluate it again. *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.

Import ListNotations.
Local Open Scope guru_scope.

Definition specAuiPccF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 => evalLetExpr (@specAuiPcc type a0 a1).
Lemma specAuiPcc_eq : forall a0 a1, evalLetExpr (@specAuiPcc type a0 a1) = specAuiPccF a0 a1. Proof. reflexivity. Qed.
Definition specAuiCgpF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 => evalLetExpr (@specAuiCgp type a0 a1).
Lemma specAuiCgp_eq : forall a0 a1, evalLetExpr (@specAuiCgp type a0 a1) = specAuiCgpF a0 a1. Proof. reflexivity. Qed.
Definition specCIncAddrF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 => evalLetExpr (@specCIncAddr type a0 a1 a2 a3).
Lemma specCIncAddr_eq : forall a0 a1 a2 a3, evalLetExpr (@specCIncAddr type a0 a1 a2 a3) = specCIncAddrF a0 a1 a2 a3. Proof. reflexivity. Qed.
Definition specBranchF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 => evalLetExpr (@specBranch type a0 a1 a2 a3).
Lemma specBranch_eq : forall a0 a1 a2 a3, evalLetExpr (@specBranch type a0 a1 a2 a3) = specBranchF a0 a1 a2 a3. Proof. reflexivity. Qed.
Definition specCjalF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 => evalLetExpr (@specCjal type a0 a1 a2 a3).
Lemma specCjal_eq : forall a0 a1 a2 a3, evalLetExpr (@specCjal type a0 a1 a2 a3) = specCjalF a0 a1 a2 a3. Proof. reflexivity. Qed.
Definition specLogicalF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 a3 => evalLetExpr (@specLogical type a0 a1 a2 a3).
Lemma specLogical_eq : forall a0 a1 a2 a3, evalLetExpr (@specLogical type a0 a1 a2 a3) = specLogicalF a0 a1 a2 a3. Proof. reflexivity. Qed.
Definition specCramCrrlF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 => evalLetExpr (@specCramCrrl type a0 a1).
Lemma specCramCrrl_eq : forall a0 a1, evalLetExpr (@specCramCrrl type a0 a1) = specCramCrrlF a0 a1. Proof. reflexivity. Qed.
Definition specCMoveF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specCMove type a0).
Lemma specCMove_eq : forall a0, evalLetExpr (@specCMove type a0) = specCMoveF a0. Proof. reflexivity. Qed.
Definition specEBreakF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specEBreak type a0).
Lemma specEBreak_eq : forall a0, evalLetExpr (@specEBreak type a0) = specEBreakF a0. Proof. reflexivity. Qed.
Definition specNoneF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 => evalLetExpr (@specNone type a0).
Lemma specNone_eq : forall a0, evalLetExpr (@specNone type a0) = specNoneF a0. Proof. reflexivity. Qed.
