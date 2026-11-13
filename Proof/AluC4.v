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

(* Per-class lemmas for specAlu_eq_wrappedAlu (part 4 of 8; see AluPre.v). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.
From SpecCheriot.Proof Require Import AluLib AluPre AluArms1 AluArms2 AluArms3 AluArms4.

Import ListNotations.
Local Open Scope guru_scope.

Lemma spec_dst_cCSetBounds : SpecDstEq cCSetBounds. Proof. spec_dst_tac specCSetBounds_eq. Qed.
Lemma spec_dst_cSeal : SpecDstEq cSeal. Proof. spec_dst_tac specSealUnseal_eq. Qed.
Lemma spec_dst_cCGetType : SpecDstEq cCGetType. Proof. spec_dst_tac specCGetType_eq. Qed.
Lemma spec_dst_cECall : SpecDstEq cECall. Proof. spec_dst_tac specECall_eq. Qed.
Lemma spec_dst_cEBreak : SpecDstEq cEBreak. Proof. spec_dst_tac specEBreak_eq. Qed.
Lemma spec_op_cCjal : SpecOpEq cCjal. Proof. spec_op_tac specCjal_eq. Qed.
Lemma spec_op_cCTestSubset : SpecOpEq cCTestSubset. Proof. spec_op_tac specCTestSubset_eq. Qed.
Lemma spec_op_cCSetEqual : SpecOpEq cCSetEqual. Proof. spec_op_tac specCSetEqual_eq. Qed.
Lemma spec_op_cCram : SpecOpEq cCram. Proof. spec_op_tac specCramCrrl_eq. Qed.
Lemma spec_op_cCMove : SpecOpEq cCMove. Proof. spec_op_tac specCMove_eq. Qed.
