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

(* Per-class lemmas for specAlu_eq_wrappedAlu (part 7 of 8; see AluPre.v). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.
From SpecCheriot.Proof Require Import AluLib AluPre AluArms1 AluArms2 AluArms3 AluArms4.

Import ListNotations.
Local Open Scope guru_scope.

Lemma spec_dst_cAuiCgp : SpecDstEq cAuiCgp. Proof. spec_dst_tac specAuiCgp_eq. Qed.
Lemma spec_dst_cLoad : SpecDstEq cLoad. Proof. spec_dst_tac specLoad_eq. Qed.
Lemma spec_dst_cCram : SpecDstEq cCram. Proof. spec_dst_tac specCramCrrl_eq. Qed.
Lemma spec_dst_cCGetAddr : SpecDstEq cCGetAddr. Proof. spec_dst_tac specCGetAddr_eq. Qed.
Lemma spec_dst_cNone : SpecDstEq cNone. Proof. spec_dst_tac specNone_eq. Qed.
Lemma spec_op_cSeal : SpecOpEq cSeal. Proof. spec_op_tac specSealUnseal_eq. Qed.
Lemma spec_op_cUnseal : SpecOpEq cUnseal. Proof. spec_op_tac specSealUnseal_eq. Qed.
Lemma spec_op_cMulDiv : SpecOpEq cMulDiv. Proof. spec_op_tac specMulDiv_eq. Qed.
Lemma spec_op_cSlt : SpecOpEq cSlt. Proof. spec_op_tac specSlt_eq. Qed.
Lemma spec_op_cCGetTag : SpecOpEq cCGetTag. Proof. spec_op_tac specCGetTag_eq. Qed.
Lemma spec_op_cECall : SpecOpEq cECall. Proof. spec_op_tac specECall_eq. Qed.
