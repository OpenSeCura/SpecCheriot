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
 * specAlu computes the same AluOutUnion as wrappedAlu: shared part
 * ===========================================================================
 * Tactics, the class-independent fields and the per-class statements used by
 * AluC1 .. SpecAluC14 (the per-class lemmas, split for parallel builds) and AluEq.
 *
 * Original description:
 * ===========================================================================
 * Main result:
 *   - [specAlu_eq_wrappedAlu]: for every package whose decoder group is well formed
 *     ([SpecWellFormed], Group.v), [specAlu] and [wrappedAlu] return the same value.
 *
 * Method: split the AluOutUnion into its four fields. isComp and dstIdx are equal for any
 * package; the op is equal for any package with a fetch or decode exception. The remaining
 * cases go class by class (AluPre.v, AluC*.v): the tactics evaluate both sides with the functional units kept
 * folded, removes the zero arms of the routing multiplexers (or 0 x = x), rewrites the few
 * shared units that the spec writes out (AdderToOutput), and splits on the remaining boolean
 * inputs. No bit-vector reasoning beyond these identities is needed. *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Theorems HelperLemmas.
From Cheriot Require Import SpecDefines FunctionalUnits Alu.
From SpecCheriot Require Import Group Alu.

Import ListNotations.
Local Open Scope guru_scope.

(* ---------------------------------------------------------------------------
 * Evaluation identities
 * --------------------------------------------------------------------------- *)

Lemma spec_or_0_l : forall m (x : Zmod m), Zmod.or Zmod.zero x = x.
Proof. intros m x. unfold Zmod.or. rewrite Zmod.unsigned_0, Z.lor_0_l. apply Zmod.of_Z_unsigned. Qed.

Lemma spec_or_0_r : forall m (x : Zmod m), Zmod.or x Zmod.zero = x.
Proof. intros m x. unfold Zmod.or. rewrite Zmod.unsigned_0, Z.lor_0_r. apply Zmod.of_Z_unsigned. Qed.

Lemma spec_evalOr_bool : forall a b : bool, @evalOrBinary Bool a b = orb a b.
Proof. reflexivity. Qed.

Lemma spec_evalOr_bit : forall n (a b : type (Bit n)), @evalOrBinary (Bit n) a b = Zmod.or a b.
Proof. reflexivity. Qed.

Lemma spec_def_bool : getDefault Bool = false.
Proof. reflexivity. Qed.

Lemma spec_def_bit : forall n, getDefault (Bit n) = Zmod.zero.
Proof. reflexivity. Qed.

Lemma spec_def_fst : forall s k ls, Fst (getDefault (Struct ((s, k) :: ls))) = getDefault k.
Proof. reflexivity. Qed.

Lemma spec_def_snd : forall s k ls, Snd (getDefault (Struct ((s, k) :: ls))) = getDefault (Struct ls).
Proof. reflexivity. Qed.

(* The shared output adder, written out *)
Lemma spec_ato_add : forall a b : type (Bit Xlen),
  evalLetExpr (@AdderToOutput type false a b) = evalExpr (Add [Var type (Bit Xlen) a; Var type (Bit Xlen) b]).
Proof. intros a b. cbn -[Zmod.add]. rewrite Zmod.add_0_r. reflexivity. Qed.

Lemma spec_ato_sub : forall a b : type (Bit Xlen),
  evalLetExpr (@AdderToOutput type true a b) = evalExpr (Sub (Var type (Bit Xlen) a) (Var type (Bit Xlen) b)).
Proof. intros a b. cbn -[Zmod.add Zmod.not]. reflexivity. Qed.

(* CGetBase and CGetTop ignore the length input of the saturater *)
Lemma spec_sat_base : forall b t s,
  evalLetExpr (@Saturater type true false false b t s) = evalLetExpr (@Saturater type true false false b t Zmod.zero).
Proof. reflexivity. Qed.

Lemma spec_sat_top : forall b t s,
  evalLetExpr (@Saturater type false true false b t s) = evalLetExpr (@Saturater type false true false b t Zmod.zero).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------
 * Tactics
 * --------------------------------------------------------------------------- *)

(* Evaluate, keeping the functional units and the bit-vector operations folded *)
Ltac spec_cbn :=
  cbn -[AdderToOutput AdderAccessEnd Shifter AdderBeforeRepCheck SealerUnsealer CjalrUnit Logical
        CAndPerm Bounds BoundsTag Saturater CapSubset CapEq ScrSanitizer EncodeCap DecodeCap
        MemException evalOrBinary getDefault Zmod.or Zmod.add Zmod.firstn Zmod_lastn Zmod.app evalToBit evalFromBit
        Zmod.slu Zmod.sru Zmod.srs Zmod.of_Z].

Ltac spec_norm :=
  repeat progress (rewrite ?spec_evalOr_bool, ?spec_evalOr_bit, ?spec_def_bool, ?spec_def_bit, ?spec_def_fst, ?spec_def_snd,
                           ?Bool.orb_false_l, ?Bool.orb_false_r, ?Bool.andb_false_r, ?Bool.andb_true_r,
                           ?Bool.orb_true_r, ?Bool.andb_true_l, ?Bool.andb_false_l, ?Bool.orb_true_l,
                           ?spec_or_0_l, ?spec_or_0_r, ?evalOrBinary_getDefault_l,
                           ?evalOrBinary_getDefault_r, ?spec_ato_add, ?spec_ato_sub).

Ltac spec_split :=
  repeat match goal with
         | |- context [if ?b then _ else _] => is_var b; destruct b
         | |- context [@evalFromBit Bool ?e] => destruct (@evalFromBit Bool e)
         end.

Ltac spec_finish :=
  first [ reflexivity
        | match goal with
          | |- context [if ?b then _ else _] =>
              let E := fresh "E" in destruct b eqn:E; try rewrite E; spec_cbn; spec_norm; spec_finish
          end ].


Ltac spec_intro_pkg Hg :=
  match goal with
  | pkg : type AluInInstGroup |- _ =>
      destruct pkg as [wcd [scr [csr [inst [dexc [fexc [cs1 [cs2 [grp []]]]]]]]]];
      cbn -[specGroup] in Hg; subst grp; unfold specGroup
  end.

(* ---------------------------------------------------------------------------
 * Fields that do not depend on the class
 * --------------------------------------------------------------------------- *)

Section Fields.
  Variable pcc : type FullECapWithTag.
  Variable pkg : type AluInInstGroup.

  Local Abbreviation lhs := (evalLetExpr (@wrappedAlu type pcc pkg)).
  Local Abbreviation rhs := (evalLetExpr (@specAlu type pcc pkg)).

  Lemma spec_isComp_eq : lhs.(Fst) = rhs.(Fst).
  Proof. reflexivity. Qed.

  Lemma spec_dstIdx_eq : lhs.(Snd).(Fst) = rhs.(Snd).(Fst).
  Proof. reflexivity. Qed.

  (* A fetch or decode exception decides the op, whatever the instruction *)
  Lemma spec_op_fdExc :
    let fe : type FetchException := evalExpr (##pkg`"fetchExc") in
    let de : type DecodeException := evalExpr (##pkg`"decodeExc") in
    orb (orb (orb (orb (orb fe.(Fst) fe.(Snd).(Fst)) fe.(Snd).(Snd).(Fst)) fe.(Snd).(Snd).(Snd).(Fst))
             de.(Fst)) de.(Snd).(Fst) = true ->
    lhs.(Snd).(Snd).(Snd).(Fst) = rhs.(Snd).(Snd).(Snd).(Fst).
  Proof.
    intros fe de H; subst fe de.
    destruct pkg as [wcd [scr [csr [inst [[ill [asr []]] [[ft [fs [fp [fb []]]]] [cs1 [cs2 [grp []]]]]]]]]].
    cbn in H.
    destruct ft; [reflexivity |]. destruct fs; [reflexivity |]. destruct fp; [reflexivity |].
    destruct fb; [reflexivity |]. destruct ill; [reflexivity |]. destruct asr; [reflexivity |].
    discriminate H.
  Qed.
End Fields.

(* ---------------------------------------------------------------------------
 * Class by class
 * --------------------------------------------------------------------------- *)

(* dstValue, for any fetch or decode exceptions *)
Definition SpecDstEq (c : SpecClass) : Prop :=
  forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup) isImm isExact isRoundDown isSub,
    evalExpr (##pkg`"instGroup") = specGroup (evalExpr (##pkg`"inst")) c isImm isExact isRoundDown isSub ->
    (evalLetExpr (@wrappedAlu type pcc pkg)).(Snd).(Snd).(Fst) =
    (evalLetExpr (@specAlu type pcc pkg)).(Snd).(Snd).(Fst).

(* The op, without fetch or decode exceptions *)
Definition SpecOpEq (c : SpecClass) : Prop :=
  forall (pcc : type FullECapWithTag) (pkg : type AluInInstGroup) isImm isExact isRoundDown isSub,
    evalExpr (##pkg`"instGroup") = specGroup (evalExpr (##pkg`"inst")) c isImm isExact isRoundDown isSub ->
    let fe : type FetchException := evalExpr (##pkg`"fetchExc") in
    let de : type DecodeException := evalExpr (##pkg`"decodeExc") in
    fe.(Fst) = false -> fe.(Snd).(Fst) = false -> fe.(Snd).(Snd).(Fst) = false ->
    fe.(Snd).(Snd).(Snd).(Fst) = false -> de.(Fst) = false -> de.(Snd).(Fst) = false ->
    (evalLetExpr (@wrappedAlu type pcc pkg)).(Snd).(Snd).(Snd).(Fst) =
    (evalLetExpr (@specAlu type pcc pkg)).(Snd).(Snd).(Snd).(Fst).
