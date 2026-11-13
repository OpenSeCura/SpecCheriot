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

(* Per-class lemmas for specAlu_eq_wrappedAlu (part 2 of 8; see AluPre.v). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.
From SpecCheriot.Proof Require Import AluLib AluPre AluArms1 AluArms2 AluArms3 AluArms4.

Import ListNotations.
Local Open Scope guru_scope.

Lemma spec_dst_cUnseal : SpecDstEq cUnseal. Proof. spec_dst_tac specSealUnseal_eq. Qed.
Lemma spec_dst_cMulDiv : SpecDstEq cMulDiv. Proof. spec_dst_tac specMulDiv_eq. Qed.
Lemma spec_dst_cAddSub : SpecDstEq cAddSub. Proof. spec_dst_tac specAddSub_eq. Qed.
Lemma spec_dst_cCGetTag : SpecDstEq cCGetTag. Proof. spec_dst_tac specCGetTag_eq. Qed.
Lemma spec_dst_cCMove : SpecDstEq cCMove. Proof. spec_dst_tac specCMove_eq. Qed.
Lemma spec_op_cLoad : SpecOpEq cLoad. Proof. spec_op_tac specLoad_eq. Qed.
Lemma spec_op_cCGetAddr : SpecOpEq cCGetAddr. Proof. spec_op_tac specCGetAddr_eq. Qed.
Lemma spec_op_cCGetHigh : SpecOpEq cCGetHigh. Proof. spec_op_tac specCGetHigh_eq. Qed.
Lemma spec_op_cCSetHigh : SpecOpEq cCSetHigh. Proof. spec_op_tac specCSetHigh_eq. Qed.
Lemma spec_op_cCClearTag : SpecOpEq cCClearTag. Proof. spec_op_tac specCClearTag_eq. Qed.
