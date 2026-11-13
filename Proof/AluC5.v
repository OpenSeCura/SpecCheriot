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

(* Per-class lemmas for specAlu_eq_wrappedAlu (part 5 of 8; see AluPre.v). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.
From SpecCheriot.Proof Require Import AluLib AluPre AluArms1 AluArms2 AluArms3 AluArms4.

Import ListNotations.
Local Open Scope guru_scope.

Lemma spec_dst_cAuiPcc : SpecDstEq cAuiPcc. Proof. spec_dst_tac specAuiPcc_eq. Qed.
Lemma spec_dst_cLogical : SpecDstEq cLogical. Proof. spec_dst_tac specLogical_eq. Qed.
Lemma spec_dst_cCGetBase : SpecDstEq cCGetBase. Proof. spec_dst_tac specCGetBaseTop_eq. Qed.
Lemma spec_dst_cCClearTag : SpecDstEq cCClearTag. Proof. spec_dst_tac specCClearTag_eq. Qed.
Lemma spec_dst_cFence : SpecDstEq cFence. Proof. spec_dst_tac specFence_eq. Qed.
Lemma spec_op_cAuiPcc : SpecOpEq cAuiPcc. Proof. spec_op_tac specAuiPcc_eq. Qed.
Lemma spec_op_cAuiCgp : SpecOpEq cAuiCgp. Proof. spec_op_tac specAuiCgp_eq. Qed.
Lemma spec_op_cCjalr : SpecOpEq cCjalr. Proof. spec_op_tac specCjalr_eq. Qed.
Lemma spec_op_cCGetLen : SpecOpEq cCGetLen. Proof. spec_op_tac specCGetLen_eq. Qed.
Lemma spec_op_cLogical : SpecOpEq cLogical. Proof. spec_op_tac specLogical_eq. Qed.
Lemma spec_op_cEBreak : SpecOpEq cEBreak. Proof. spec_op_tac specEBreak_eq. Qed.
