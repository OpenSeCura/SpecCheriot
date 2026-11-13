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
 * Staged evaluation for the per-class lemmas of specAlu_eq_wrappedAlu
 * ===========================================================================
 * Each stage of [wrappedAlu] ([constructAluIn], [AluRouting], [Alu]) and the dispatch part of
 * [specAlu] is evaluated once here, with the class left abstract and the functional units
 * folded. The spec arms are precomputed in AluArms*.v. A per-class lemma then only reduces
 * these precomputed terms with its concrete class bits, so the string field lookups and the
 * shared stages are not evaluated again for every class. *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.
From SpecCheriot.Proof Require Import AluLib.

Import ListNotations.
Local Open Scope guru_scope.

Lemma spec_ev_LetEx : forall k k' s (e : LetExpr type k') (f : type k' -> LetExpr type k),
  evalLetExpr (LetEx s e f) = evalLetExpr (f (evalLetExpr e)).
Proof. reflexivity. Qed.

Definition specCAIF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun pkg => evalLetExpr (@constructAluIn type pkg).
Lemma specCAIF_eq : forall pkg, evalLetExpr (@constructAluIn type pkg) = specCAIF pkg.
Proof. reflexivity. Qed.

(* Without zeta: the let-bound values of AluRouting stay shared *)
Definition specARF := Eval cbn beta iota match fix cofix delta -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in
  fun pcc ai => evalLetExpr (@AluRouting type pcc ai).
Lemma specARF_eq : forall pcc ai, evalLetExpr (@AluRouting type pcc ai) = specARF pcc ai.
Proof. reflexivity. Qed.

Definition specAF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun ro => evalLetExpr (@Alu type ro).
Lemma specAF_eq : forall ro, evalLetExpr (@Alu type ro) = specAF ro.
Proof. reflexivity. Qed.

(* The dispatch of specAlu, with the arms kept folded *)
Definition specSF := Eval cbn -[specCases specFetchDecodeExc AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z specLui specAuiPcc specAuiCgp specCIncAddr specCSetAddr specBranch specCjal specCjalr specMret specCTestSubset specCSetBounds specSealUnseal specLoad specStore specMulDiv specAddSub specCGetLen specCGetBaseTop specSlt specCSetEqual specShift specLogical specCramCrrl specCAndPerm specCsr specScr specCGetPerm specCGetType specCGetTag specCGetAddr specCGetHigh specCSetHigh specCClearTag specCMove specECall specEBreak specFence specNone] in
  fun pcc pkg => evalLetExpr (@specAlu type pcc pkg).
Lemma specSF_eq : forall pcc pkg, evalLetExpr (@specAlu type pcc pkg) = specSF pcc pkg.
Proof. reflexivity. Qed.

Definition specFetchDecodeExcF := Eval cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z] in fun a0 a1 a2 => evalLetExpr (@specFetchDecodeExc type a0 a1 a2).
Lemma specFetchDecodeExc_eq : forall a0 a1 a2, evalLetExpr (@specFetchDecodeExc type a0 a1 a2) = specFetchDecodeExcF a0 a1 a2. Proof. reflexivity. Qed.

(* Boolean ors of the decoded control bits become [orb], so that they compute *)
Lemma spec_or_if_r : forall k (a v : type k) (p : bool),
  evalOrBinary a (if p then v else getDefault k) = if p then evalOrBinary a v else a.
Proof. intros k a v []; [reflexivity | apply evalOrBinary_getDefault_r]. Qed.

Ltac spec_pre := repeat progress (rewrite ?spec_def_bool, ?spec_def_bit, ?spec_or_if_r, ?spec_evalOr_bool).

Definition specCAIF2_sig : {f | forall pkg, specCAIF pkg = f pkg}.
Proof. eexists. intros. unfold specCAIF. spec_pre. reflexivity. Defined.
Definition specAF2_sig : {f | forall ro, specAF ro = f ro}.
Proof. eexists. intros. unfold specAF. spec_pre. reflexivity. Defined.
Definition specCAIF2 := Eval lazy beta iota delta [proj1_sig specCAIF2_sig] in proj1_sig specCAIF2_sig.
Definition specAF2 := Eval lazy beta iota delta [proj1_sig specAF2_sig] in proj1_sig specAF2_sig.

Lemma specWF_eq : forall pcc pkg, evalLetExpr (@wrappedAlu type pcc pkg) = specAF2 (specARF pcc (specCAIF2 pkg)).
Proof.
  intros. unfold wrappedAlu. rewrite spec_ev_LetEx. cbv beta.
  rewrite specCAIF_eq, (proj2_sig specCAIF2_sig), spec_ev_LetEx. cbv beta.
  rewrite specARF_eq, spec_ev_LetEx. cbv beta. rewrite specAF_eq, (proj2_sig specAF2_sig). reflexivity.
Qed.

(* Reduce with the class bits known, keeping the spec arms folded *)
Ltac spec_sel_cbn := cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z specFetchDecodeExc specLui specAuiPcc specAuiCgp specCIncAddr specCSetAddr specBranch specCjal specCjalr specMret specCTestSubset specCSetBounds specSealUnseal specLoad specStore specMulDiv specAddSub specCGetLen specCGetBaseTop specSlt specCSetEqual specShift specLogical specCramCrrl specCAndPerm specCsr specScr specCGetPerm specCGetType specCGetTag specCGetAddr specCGetHigh specCSetHigh specCClearTag specCMove specECall specEBreak specFence specNone].

Ltac spec_rest E :=
  spec_sel_cbn; rewrite ?specFetchDecodeExc_eq, ?E;
  spec_cbn; spec_norm; spec_split; do 3 (spec_cbn; spec_norm); spec_finish.

(* E is the precomputation lemma of the class's spec arm (AluArms*.v) *)
Ltac spec_dst_tac E :=
  intros pcc pkg isImm isExact isRoundDown isSub Hg; rewrite specWF_eq, specSF_eq; spec_intro_pkg Hg;
  spec_rest E.

Ltac spec_op_tac E :=
  intros pcc pkg isImm isExact isRoundDown isSub Hg fe de H1 H2 H3 H4 H5 H6; subst fe de;
  rewrite specWF_eq, specSF_eq;
  destruct pkg as [wcd [scr [csr [inst [[ill [asr []]] [[ft [fs [fp [fb []]]]] [cs1 [cs2 [grp []]]]]]]]]];
  cbn -[specGroup] in Hg, H1, H2, H3, H4, H5, H6; subst grp ill asr ft fs fp fb; unfold specGroup;
  spec_rest E.
