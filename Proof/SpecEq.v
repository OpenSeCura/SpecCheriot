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
 * simpleSpec and spec have the same runs
 * ===========================================================================
 * Main results:
 *   - [spec_SemMod_spec_simpleSpec], [spec_SemMod_simpleSpec_spec]: every run of [spec] is a run of [simpleSpec]
 *     and conversely, from the same states.
 *
 * The two modules differ only in the ALU of the core step. In the core step the ALU input comes
 * from the register-read stage, which forwards the decoder's group and instruction, so it is
 * well formed (Decode.v), and on well-formed inputs [specAlu] and [wrappedAlu] agree
 * (AluEq.v). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems
  HelperLemmas.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint
  SpecRevoker Plic Spec.
From SpecCheriot Require Import Group Alu Spec.
From SpecCheriot.Proof Require Import AluEq Decode.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Section SpecEq.
  Variable pcAddrInit : Z.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable clint : @ClintInstance regions.
  Variable rev : @RevokerInstance [] regions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions regions)))) regions.
  Local Abbreviation sysTree := (specSysTree pcAddrInit regions).
  Local Abbreviation stepWith := (@specStepWith pcAddrInit config regions clint plic type).

  Ltac spec_mono H :=
    eapply evalActionPropGen_mono; [| exact H]; cbv beta; clear H; intros ? ? H.

  (* The register-read stage forwards the decoder's group and instruction *)
  Lemma spec_regRead_wf : forall (env : Env sysTree) (fo : type FetchOut) s
                               (Q : TreeState ElemState sysTree -> type AluInInstGroup -> Prop),
    evalActionPropGen env (liftAction (np_rf pcAddrInit regions)
                             (regRead pcAddrInit (evalLetExpr (@wrappedDecode type fo)))) s Q ->
    evalActionPropGen env (liftAction (np_rf pcAddrInit regions)
                             (regRead pcAddrInit (evalLetExpr (@wrappedDecode type fo)))) s
      (fun s' v => Q s' v /\ SpecWellFormed v).
  Proof.
    intros env fo s Q H.
    rewrite evalActionPropGen_liftAction in H |- *.
    unfold regRead in H |- *. cbn [evalActionPropGen] in H |- *.
    spec_mono H. spec_mono H.
    split; [exact H |].
    destruct (spec_decode_wellformed (evalExpr (##fo`"inst")) (evalExpr (##fo`"hasAsr")))
      as [c [isImm [isExact [isRoundDown [isSub Hd]]]]].
    exists c, isImm, isExact, isRoundDown, isSub. exact Hd.
  Qed.

  (* Stepping lemmas: each one relates the two runs through one action constructor, so the kernel
   * never compares different action shapes (see the guru-proofs skill, section 1). *)
  Lemma spec_letA_mono : forall (env : Env sysTree) k k' nm (a : Action type sysTree k')
                              (c1 c2 : type k' -> Action type sysTree k) st P1 P2,
    (forall s v, evalActionPropGen env (c1 v) s P1 -> evalActionPropGen env (c2 v) s P2) ->
    evalActionPropGen env (LetAction nm a c1) st P1 -> evalActionPropGen env (LetAction nm a c2) st P2.
  Proof. intros env k k' nm a c1 c2 st P1 P2 Hc H. exact (evalActionPropGen_mono _ _ _ _ _ Hc H). Qed.

  Lemma spec_letA_mono_pre : forall (env : Env sysTree) k k' nm (a : Action type sysTree k')
                                  (c1 c2 : type k' -> Action type sysTree k) st P1 P2 (Pre : type k' -> Prop),
    (forall Q st', evalActionPropGen env a st' Q -> evalActionPropGen env a st' (fun s v => Q s v /\ Pre v)) ->
    (forall s v, Pre v -> evalActionPropGen env (c1 v) s P1 -> evalActionPropGen env (c2 v) s P2) ->
    evalActionPropGen env (LetAction nm a c1) st P1 -> evalActionPropGen env (LetAction nm a c2) st P2.
  Proof.
    intros env k k' nm a c1 c2 st P1 P2 Pre Ha Hc H. cbn [evalActionPropGen] in H |- *.
    apply Ha in H. eapply evalActionPropGen_mono; [| exact H]. intros s v [H1 H2]. exact (Hc s v H2 H1).
  Qed.

  Lemma spec_letL_eq : forall (env : Env sysTree) k k' nm (le1 le2 : LetExpr type k')
                            (c : type k' -> Action type sysTree k) st P,
    evalLetExpr le1 = evalLetExpr le2 ->
    evalActionPropGen env (LetAction nm (toAction _ le1) c) st P ->
    evalActionPropGen env (LetAction nm (toAction _ le2) c) st P.
  Proof.
    intros env k k' nm le1 le2 c st P Heq H. cbn [evalActionPropGen] in H |- *.
    rewrite evalActionPropGen_toAction in H |- *. rewrite <- Heq. exact H.
  Qed.

  Lemma spec_letL_mono : forall (env : Env sysTree) k k' nm (le : LetExpr type k')
                              (c1 c2 : type k' -> Action type sysTree k) st P1 P2,
    (evalActionPropGen env (c1 (evalLetExpr le)) st P1 -> evalActionPropGen env (c2 (evalLetExpr le)) st P2) ->
    evalActionPropGen env (LetAction nm (toAction _ le) c1) st P1 ->
    evalActionPropGen env (LetAction nm (toAction _ le) c2) st P2.
  Proof.
    intros env k k' nm le c1 c2 st P1 P2 Hc H. cbn [evalActionPropGen] in H |- *.
    rewrite evalActionPropGen_toAction in H |- *. exact (Hc H).
  Qed.

  Lemma spec_letE_mono : forall (env : Env sysTree) k k' nm (e : Expr type k')
                              (c1 c2 : type k' -> Action type sysTree k) st P1 P2,
    (forall v, evalActionPropGen env (c1 v) st P1 -> evalActionPropGen env (c2 v) st P2) ->
    evalActionPropGen env (LetExp nm e c1) st P1 -> evalActionPropGen env (LetExp nm e c2) st P2.
  Proof. intros env k k' nm e c1 c2 st P1 P2 Hc H. exact (Hc _ H). Qed.

  Lemma spec_if_mono : forall (env : Env sysTree) k k' nm p (t1 t2 f : Action type sysTree k')
                            (c : type k' -> Action type sysTree k) st P,
    (forall Q, evalActionPropGen env t1 st Q -> evalActionPropGen env t2 st Q) ->
    evalActionPropGen env (IfElse nm p t1 f c) st P -> evalActionPropGen env (IfElse nm p t2 f c) st P.
  Proof.
    intros env k k' nm p t1 t2 f c st P Ht H. cbn [evalActionPropGen] in H |- *.
    destruct (evalExpr p); [exact (Ht _ H) | exact H].
  Qed.

  Lemma spec_regRead_pre : forall (env : Env sysTree) (fo : type FetchOut) Q st,
    evalActionPropGen env (liftAction (np_rf pcAddrInit regions)
                             (regRead pcAddrInit (evalLetExpr (@wrappedDecode type fo)))) st Q ->
    evalActionPropGen env (liftAction (np_rf pcAddrInit regions)
                             (regRead pcAddrInit (evalLetExpr (@wrappedDecode type fo)))) st
      (fun s v => Q s v /\ SpecWellFormed v).
  Proof. intros env fo Q st H. exact (spec_regRead_wf env fo st Q H). Qed.

  (* The core step only depends on the ALU through its values on well-formed inputs *)
  Lemma spec_step_transfer :
    forall (alu1 alu2 : type FullECapWithTag -> type AluInInstGroup -> LetExpr type AluOutUnion),
      (forall pcc pkg, SpecWellFormed pkg -> evalLetExpr (alu1 pcc pkg) = evalLetExpr (alu2 pcc pkg)) ->
      forall (env : Env sysTree) s P,
        evalActionPropGen env (stepWith alu1) s P -> evalActionPropGen env (stepWith alu2) s P.
  Proof.
    intros alu1 alu2 Heq env s P.
    unfold specStepWith.
    apply spec_letA_mono; intros s1 fenceIWait.
    apply spec_letA_mono; intros s2 secondLine.
    apply spec_if_mono; intros Q.
    apply spec_letA_mono; intros s3 meip.
    apply spec_letA_mono; intros s4 mtip.
    apply spec_letA_mono; intros s5 fetchOut.
    apply spec_letL_mono.
    apply (spec_letA_mono_pre _ _ _ _ _ _ _ _ _ _ _ (spec_regRead_pre env fetchOut)); intros s7 pkg Hwf.
    apply spec_letA_mono; intros s8 pcc.
    apply spec_letL_eq. exact (Heq pcc pkg Hwf).
  Qed.
  Lemma spec_step_spec_simpleSpec : forall (env : Env sysTree) s s' r,
    SemAction env (specStep pcAddrInit config clint plic type) s s' r ->
    SemAction env (simpleSpecStep pcAddrInit config clint plic type) s s' r.
  Proof.
    intros env s s' r H.
    rewrite <- specStepWith_wrappedAlu in H.
    rewrite SemAction_iff_evalActionPropGen in H |- *.
    unfold simpleSpecStep.
    exact (spec_step_transfer (@wrappedAlu type) (@specAlu type)
             (fun pcc pkg Hwf => eq_sym (specAlu_eq_wrappedAlu pcc pkg Hwf)) env s _ H).
  Qed.

  Lemma spec_step_simpleSpec_spec : forall (env : Env sysTree) s s' r,
    SemAction env (simpleSpecStep pcAddrInit config clint plic type) s s' r ->
    SemAction env (specStep pcAddrInit config clint plic type) s s' r.
  Proof.
    intros env s s' r H.
    rewrite <- specStepWith_wrappedAlu.
    rewrite SemAction_iff_evalActionPropGen in H |- *.
    unfold simpleSpecStep in H.
    exact (spec_step_transfer (@specAlu type) (@wrappedAlu type)
             (fun pcc pkg Hwf => specAlu_eq_wrappedAlu pcc pkg Hwf) env s _ H).
  Qed.

  (* The rule lists agree except at the core step *)
  Lemma spec_in_spec : forall a,
    In a (spec pcAddrInit config clint rev plic type) ->
    specStep pcAddrInit config clint plic type = a \/ In a (simpleSpec pcAddrInit config clint rev plic type).
  Proof.
    intros a Hin. unfold spec, simpleSpec in *.
    rewrite !in_app_iff in Hin |- *. cbn [In] in Hin |- *. tauto.
  Qed.

  Lemma spec_in_simpleSpec : forall a,
    In a (simpleSpec pcAddrInit config clint rev plic type) ->
    simpleSpecStep pcAddrInit config clint plic type = a \/ In a (spec pcAddrInit config clint rev plic type).
  Proof.
    intros a Hin. unfold spec, simpleSpec in *.
    rewrite !in_app_iff in Hin |- *. cbn [In] in Hin |- *. tauto.
  Qed.

  Lemma spec_simpleSpecStep_in : In (simpleSpecStep pcAddrInit config clint plic type) (simpleSpec pcAddrInit config clint rev plic type).
  Proof. unfold simpleSpec. rewrite !in_app_iff. cbn [In]. tauto. Qed.

  Lemma spec_specStep_in : In (specStep pcAddrInit config clint plic type) (spec pcAddrInit config clint rev plic type).
  Proof. unfold spec. rewrite !in_app_iff. cbn [In]. tauto. Qed.

  Lemma spec_SemActions_spec_simpleSpec : forall (env : Env sysTree) old new,
    SemActions env (spec pcAddrInit config clint rev plic type) old new ->
    SemActions env (simpleSpec pcAddrInit config clint rev plic type) old new.
  Proof.
    intros env old new H. induction H as [old new Heq | old new mid a Hin Ha Hrest IH].
    - eapply NilAction; exact Heq.
    - destruct (spec_in_spec a Hin) as [<- | Hin'].
      + eapply ConsAction; [exact spec_simpleSpecStep_in | exact (spec_step_spec_simpleSpec env _ _ _ Ha) | exact IH].
      + eapply ConsAction; [exact Hin' | exact Ha | exact IH].
  Qed.

  Lemma spec_SemActions_simpleSpec_spec : forall (env : Env sysTree) old new,
    SemActions env (simpleSpec pcAddrInit config clint rev plic type) old new ->
    SemActions env (spec pcAddrInit config clint rev plic type) old new.
  Proof.
    intros env old new H. induction H as [old new Heq | old new mid a Hin Ha Hrest IH].
    - eapply NilAction; exact Heq.
    - destruct (spec_in_simpleSpec a Hin) as [<- | Hin'].
      + eapply ConsAction; [exact spec_specStep_in | exact (spec_step_simpleSpec_spec env _ _ _ Ha) | exact IH].
      + eapply ConsAction; [exact Hin' | exact Ha | exact IH].
  Qed.

  Theorem spec_SemMod_spec_simpleSpec : forall (env : Env sysTree) old new,
    SemMod env (spec pcAddrInit config clint rev plic) old new ->
    SemMod env (simpleSpec pcAddrInit config clint rev plic) old new.
  Proof.
    intros env old new [o n Hinit Hacts].
    constructor; [exact Hinit | exact (spec_SemActions_spec_simpleSpec env _ _ Hacts)].
  Qed.

  Theorem spec_SemMod_simpleSpec_spec : forall (env : Env sysTree) old new,
    SemMod env (simpleSpec pcAddrInit config clint rev plic) old new ->
    SemMod env (spec pcAddrInit config clint rev plic) old new.
  Proof.
    intros env old new [o n Hinit Hacts].
    constructor; [exact Hinit | exact (spec_SemActions_simpleSpec_spec env _ _ Hacts)].
  Qed.
End SpecEq.
