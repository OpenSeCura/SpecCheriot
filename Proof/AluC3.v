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

(* Per-class lemmas for specAlu_eq_wrappedAlu (part 3 of 8; see AluPre.v). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.
From SpecCheriot.Proof Require Import AluLib AluPre AluArms1 AluArms2 AluArms3 AluArms4.

Import ListNotations.
Local Open Scope guru_scope.

Lemma spec_dst_cCIncAddr : SpecDstEq cCIncAddr. Proof. spec_dst_tac specCIncAddr_eq. Qed.
Lemma spec_dst_cStore : SpecDstEq cStore. Proof. spec_dst_tac specStore_eq. Qed.
Lemma spec_dst_cCGetLen : SpecDstEq cCGetLen. Proof. spec_dst_tac specCGetLen_eq. Qed.
Lemma spec_dst_cCAndPerm : SpecDstEq cCAndPerm. Proof. spec_dst_tac specCAndPerm_eq. Qed.
Lemma spec_dst_cCGetTop : SpecDstEq cCGetTop. Proof. spec_dst_tac specCGetBaseTop_eq. Qed.
Lemma spec_dst_cMret : SpecDstEq cMret. Proof. spec_dst_tac specMret_eq. Qed.
Lemma spec_op_cCSetBounds : SpecOpEq cCSetBounds. Proof. spec_op_tac specCSetBounds_eq. Qed.
Lemma spec_op_cStore : SpecOpEq cStore. Proof. spec_op_tac specStore_eq. Qed.
Lemma spec_op_cLui : SpecOpEq cLui. Proof. spec_op_tac specLui_eq. Qed.
Lemma spec_op_cCGetPerm : SpecOpEq cCGetPerm. Proof. spec_op_tac specCGetPerm_eq. Qed.
Lemma spec_op_cCGetType : SpecOpEq cCGetType. Proof. spec_op_tac specCGetType_eq. Qed.
