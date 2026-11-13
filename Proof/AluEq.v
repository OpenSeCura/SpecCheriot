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

(* ===========================================================================
 * specAlu computes the same AluOutUnion as wrappedAlu
 * ===========================================================================
 * Main result: [specAlu_eq_wrappedAlu]. The tactics and the class-independent fields
 * are in AluLib.v; the per-class lemmas are in AluC1 .. AluC8 (with the staged evaluation of AluPre.v and AluArms*.v) (split so that
 * make -j builds them in parallel). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.
From SpecCheriot.Proof Require Import AluLib AluC1 AluC2 AluC3 AluC4 AluC5 AluC6 AluC7 AluC8.

Import ListNotations.
Local Open Scope guru_scope.

Lemma spec_dst_eq : forall c, SpecDstEq c.
Proof.
  destruct c.
  - exact spec_dst_cBranch.
  - exact spec_dst_cCjal.
  - exact spec_dst_cAuiPcc.
  - exact spec_dst_cAuiCgp.
  - exact spec_dst_cCIncAddr.
  - exact spec_dst_cCSetAddr.
  - exact spec_dst_cCjalr.
  - exact spec_dst_cCTestSubset.
  - exact spec_dst_cCSetBounds.
  - exact spec_dst_cSeal.
  - exact spec_dst_cUnseal.
  - exact spec_dst_cLoad.
  - exact spec_dst_cStore.
  - exact spec_dst_cMulDiv.
  - exact spec_dst_cAddSub.
  - exact spec_dst_cCGetLen.
  - exact spec_dst_cSlt.
  - exact spec_dst_cCSetEqual.
  - exact spec_dst_cShift.
  - exact spec_dst_cLogical.
  - exact spec_dst_cCram.
  - exact spec_dst_cCrrl.
  - exact spec_dst_cCAndPerm.
  - exact spec_dst_cCsr.
  - exact spec_dst_cScr.
  - exact spec_dst_cLui.
  - exact spec_dst_cCGetPerm.
  - exact spec_dst_cCGetType.
  - exact spec_dst_cCGetBase.
  - exact spec_dst_cCGetTag.
  - exact spec_dst_cCGetAddr.
  - exact spec_dst_cCGetHigh.
  - exact spec_dst_cCGetTop.
  - exact spec_dst_cCSetHigh.
  - exact spec_dst_cCClearTag.
  - exact spec_dst_cCMove.
  - exact spec_dst_cECall.
  - exact spec_dst_cEBreak.
  - exact spec_dst_cMret.
  - exact spec_dst_cFence.
  - exact spec_dst_cNone.
Qed.

Lemma spec_op_eq : forall c, SpecOpEq c.
Proof.
  destruct c.
  - exact spec_op_cBranch.
  - exact spec_op_cCjal.
  - exact spec_op_cAuiPcc.
  - exact spec_op_cAuiCgp.
  - exact spec_op_cCIncAddr.
  - exact spec_op_cCSetAddr.
  - exact spec_op_cCjalr.
  - exact spec_op_cCTestSubset.
  - exact spec_op_cCSetBounds.
  - exact spec_op_cSeal.
  - exact spec_op_cUnseal.
  - exact spec_op_cLoad.
  - exact spec_op_cStore.
  - exact spec_op_cMulDiv.
  - exact spec_op_cAddSub.
  - exact spec_op_cCGetLen.
  - exact spec_op_cSlt.
  - exact spec_op_cCSetEqual.
  - exact spec_op_cShift.
  - exact spec_op_cLogical.
  - exact spec_op_cCram.
  - exact spec_op_cCrrl.
  - exact spec_op_cCAndPerm.
  - exact spec_op_cCsr.
  - exact spec_op_cScr.
  - exact spec_op_cLui.
  - exact spec_op_cCGetPerm.
  - exact spec_op_cCGetType.
  - exact spec_op_cCGetBase.
  - exact spec_op_cCGetTag.
  - exact spec_op_cCGetAddr.
  - exact spec_op_cCGetHigh.
  - exact spec_op_cCGetTop.
  - exact spec_op_cCSetHigh.
  - exact spec_op_cCClearTag.
  - exact spec_op_cCMove.
  - exact spec_op_cECall.
  - exact spec_op_cEBreak.
  - exact spec_op_cMret.
  - exact spec_op_cFence.
  - exact spec_op_cNone.
Qed.

(* ---------------------------------------------------------------------------
 * Main result
 * --------------------------------------------------------------------------- *)

Lemma spec_aluOutUnion_ext : forall x y : type AluOutUnion,
  x.(Fst) = y.(Fst) -> x.(Snd).(Fst) = y.(Snd).(Fst) -> x.(Snd).(Snd).(Fst) = y.(Snd).(Snd).(Fst) ->
  x.(Snd).(Snd).(Snd).(Fst) = y.(Snd).(Snd).(Snd).(Fst) -> x = y.
Proof.
  intros [a [b [c [d []]]]] [a' [b' [c' [d' []]]]]; cbn [Fst Snd]; intros -> -> -> ->; reflexivity.
Qed.

Theorem specAlu_eq_wrappedAlu : forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup),
  SpecWellFormed pkg ->
  evalLetExpr (@specAlu type pcc pkg) = evalLetExpr (@wrappedAlu type pcc pkg).
Proof.
  intros pcc pkg [c [isImm [isExact [isRoundDown [isSub Hg]]]]].
  symmetry; apply spec_aluOutUnion_ext.
  - apply spec_isComp_eq.
  - apply spec_dstIdx_eq.
  - exact (spec_dst_eq c pcc pkg isImm isExact isRoundDown isSub Hg).
  - set (fe := evalExpr (##pkg`"fetchExc")).
    set (de := evalExpr (##pkg`"decodeExc")).
    destruct (orb (orb (orb (orb (orb fe.(Fst) fe.(Snd).(Fst)) fe.(Snd).(Snd).(Fst))
                             fe.(Snd).(Snd).(Snd).(Fst)) de.(Fst)) de.(Snd).(Fst)) eqn:Hfd.
    + exact (spec_op_fdExc pcc pkg Hfd).
    + rewrite !Bool.orb_false_iff in Hfd.
      destruct Hfd as [[[[[H1 H2] H3] H4] H5] H6].
      exact (spec_op_eq c pcc pkg isImm isExact isRoundDown isSub Hg H1 H2 H3 H4 H5 H6).
Qed.
