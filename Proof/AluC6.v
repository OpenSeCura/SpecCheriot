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

(* Per-class lemmas for specAlu_eq_wrappedAlu (part 6 of 8; see AluPre.v). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.
From SpecCheriot.Proof Require Import AluLib AluPre AluArms1 AluArms2 AluArms3 AluArms4.

Import ListNotations.
Local Open Scope guru_scope.

Lemma spec_dst_cCSetAddr : SpecDstEq cCSetAddr. Proof. spec_dst_tac specCSetAddr_eq. Qed.
Lemma spec_dst_cCTestSubset : SpecDstEq cCTestSubset. Proof. spec_dst_tac specCTestSubset_eq. Qed.
Lemma spec_dst_cCSetEqual : SpecDstEq cCSetEqual. Proof. spec_dst_tac specCSetEqual_eq. Qed.
Lemma spec_dst_cScr : SpecDstEq cScr. Proof. spec_dst_tac specScr_eq. Qed.
Lemma spec_dst_cCGetHigh : SpecDstEq cCGetHigh. Proof. spec_dst_tac specCGetHigh_eq. Qed.
Lemma spec_op_cCSetAddr : SpecOpEq cCSetAddr. Proof. spec_op_tac specCSetAddr_eq. Qed.
Lemma spec_op_cShift : SpecOpEq cShift. Proof. spec_op_tac specShift_eq. Qed.
Lemma spec_op_cCrrl : SpecOpEq cCrrl. Proof. spec_op_tac specCramCrrl_eq. Qed.
Lemma spec_op_cCsr : SpecOpEq cCsr. Proof. spec_op_tac specCsr_eq. Qed.
Lemma spec_op_cCGetTop : SpecOpEq cCGetTop. Proof. spec_op_tac specCGetBaseTop_eq. Qed.
Lemma spec_op_cFence : SpecOpEq cFence. Proof. spec_op_tac specFence_eq. Qed.
