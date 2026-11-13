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

(* Per-class lemmas for specAlu_eq_wrappedAlu (part 1 of 8; see AluPre.v). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.
From SpecCheriot.Proof Require Import AluLib AluPre AluArms1 AluArms2 AluArms3 AluArms4.

Import ListNotations.
Local Open Scope guru_scope.

Lemma spec_dst_cBranch : SpecDstEq cBranch. Proof. spec_dst_tac specBranch_eq. Qed.
Lemma spec_dst_cCjal : SpecDstEq cCjal. Proof. spec_dst_tac specCjal_eq. Qed.
Lemma spec_dst_cShift : SpecDstEq cShift. Proof. spec_dst_tac specShift_eq. Qed.
Lemma spec_dst_cLui : SpecDstEq cLui. Proof. spec_dst_tac specLui_eq. Qed.
Lemma spec_dst_cCGetPerm : SpecDstEq cCGetPerm. Proof. spec_dst_tac specCGetPerm_eq. Qed.
Lemma spec_op_cBranch : SpecOpEq cBranch. Proof. spec_op_tac specBranch_eq. Qed.
Lemma spec_op_cCAndPerm : SpecOpEq cCAndPerm. Proof. spec_op_tac specCAndPerm_eq. Qed.
