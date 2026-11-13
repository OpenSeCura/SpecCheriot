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
 * Every run of simpleSpec is a run of nondetSpec
 * ===========================================================================
 * Main results:
 *   - [nondetAlu_leftovers]: [nondetAlu] with the values the shared datapath leaves in the
 *     don't-care fields ([leftovers]) is [specAlu].
 *   - [nondet_SemMod_simpleSpec_nondetSpec]: every run of [simpleSpec] is a run of [nondetSpec]
 *     from the same states ([NonDet] chooses [leftovers]). *)

From Stdlib Require Import String List ZArith Zmod Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems
  HelperLemmas.
From Cheriot Require Import SpecDefines Decoder FunctionalUnits Alu SpecFetchDeferred SpecDevice Clint
  SpecRevoker Plic Spec.
From SpecCheriot Require Import Alu Spec NondetAlu NondetSpec.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.
Local Open Scope string_scope.

(* ---------------------------------------------------------------------------
 * The ALU
 * --------------------------------------------------------------------------- *)

(* What the shared datapath leaves in the don't-care fields (Alu.v, header) *)
Definition leftoversE (pcc : type FullECapWithTag) (pkg : type AluInInstGroup) : LetExpr type FreeVals :=
  LetE inst : Inst <- ##pkg`"inst" ;
  LetE cs1 : FullECapWithTag <- ##pkg`"cs1" ;
  LETE dc : CjalrUnitRes <- CjalrUnit cs1 inst ;
  LetE tag : Bool <- ##cs1`"tag" ;
  LetE addr : Addr <- ##cs1`"addr" ;
  LETE dcTag : Bool <- ScrSanitizer tag addr inst ;
  @RetE _ FreeVals (STRUCT {
    "dst"       ::= specNoResult inst ;
    "newPcc"    ::= specCapResult (##pcc`"tag") (##dc`"ecap") (Add [ ##cs1`"addr" ; specSimm12 inst ]) ;
    "intStatus" ::= ##dc`"interruptStatus" ;
    "special"   ::= specCapResult #dcTag (##cs1`"ecap") (Const type Addr Zmod.zero) }).

Definition leftovers pcc pkg : type FreeVals := evalLetExpr (leftoversE pcc pkg).

Lemma nondet_specCases_ext : forall k (l1 l2 : list (Expr type Bool * LetExpr type k)) d1 d2,
  Forall2 (fun x y => evalExpr (fst x) = evalExpr (fst y) /\ evalLetExpr (snd x) = evalLetExpr (snd y)) l1 l2 ->
  evalLetExpr d1 = evalLetExpr d2 ->
  evalLetExpr (specCases l1 d1) = evalLetExpr (specCases l2 d2).
Proof.
  intros k l1 l2 d1 d2 H Hd. induction H as [| [p1 t1] [p2 t2] l1 l2 [Hp Ht] _ IH]; [exact Hd |].
  cbn [specCases evalLetExpr fst snd] in *. rewrite Hp, Ht, IH. reflexivity.
Qed.

(* The arms agree pairwise, the changed ones by evaluation ([leftovers] supplies their values) *)
Lemma nondetAlu_leftovers : forall pcc pkg,
  evalLetExpr (nondetAlu (leftovers pcc pkg) pcc pkg) = evalLetExpr (specAlu pcc pkg).
Proof.
  intros pcc pkg. unfold nondetAlu, specAlu. cbn [evalLetExpr].
  match goal with
  | |- context [evalLetExpr (@specCases _ _ ?L1 ?d1)] =>
      lazymatch L1 with context [nondetBranch] =>
      match goal with
      | |- context [evalLetExpr (@specCases _ _ ?L2 ?d2)] =>
          lazymatch L2 with context [specBranch] =>
          assert (H : evalLetExpr (specCases L1 d1) = evalLetExpr (specCases L2 d2))
          end
      end end
  end.
  { apply nondet_specCases_ext; [| abstract exact eq_refl].
    repeat (apply Forall2_cons; [split; [reflexivity | abstract exact eq_refl] |]).
    apply Forall2_nil. }
  rewrite H. reflexivity.
Qed.

(* ---------------------------------------------------------------------------
 * The runs
 * --------------------------------------------------------------------------- *)

Section NondetEq.
  Variable pcAddrInit : Z.
  Variable config : RevConfig.
  Variable regions : list MemRegion.
  Variable clint : @ClintInstance regions.
  Variable rev : @RevokerInstance [] regions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions regions)))) regions.
  Local Abbreviation sysTree := (specSysTree pcAddrInit regions).

  Lemma nondet_letA_mono : forall (env : Env sysTree) k k' nm (a : Action type sysTree k')
                                (c1 c2 : type k' -> Action type sysTree k) st P1 P2,
    (forall s v, evalActionPropGen env (c1 v) s P1 -> evalActionPropGen env (c2 v) s P2) ->
    evalActionPropGen env (LetAction nm a c1) st P1 -> evalActionPropGen env (LetAction nm a c2) st P2.
  Proof. intros env k k' nm a c1 c2 st P1 P2 Hc H. exact (evalActionPropGen_mono _ _ _ _ _ Hc H). Qed.

  Lemma nondet_letL_mono : forall (env : Env sysTree) k k' nm (le : LetExpr type k')
                                (c1 c2 : type k' -> Action type sysTree k) st P1 P2,
    (evalActionPropGen env (c1 (evalLetExpr le)) st P1 -> evalActionPropGen env (c2 (evalLetExpr le)) st P2) ->
    evalActionPropGen env (LetAction nm (toAction _ le) c1) st P1 ->
    evalActionPropGen env (LetAction nm (toAction _ le) c2) st P2.
  Proof.
    intros env k k' nm le c1 c2 st P1 P2 Hc H. cbn [evalActionPropGen] in H |- *.
    rewrite evalActionPropGen_toAction in H |- *. exact (Hc H).
  Qed.

  Lemma nondet_if_mono : forall (env : Env sysTree) k k' nm p (t1 t2 f : Action type sysTree k')
                              (c : type k' -> Action type sysTree k) st P,
    (forall Q, evalActionPropGen env t1 st Q -> evalActionPropGen env t2 st Q) ->
    evalActionPropGen env (IfElse nm p t1 f c) st P -> evalActionPropGen env (IfElse nm p t2 f c) st P.
  Proof.
    intros env k k' nm p t1 t2 f c st P Ht H. cbn [evalActionPropGen] in H |- *.
    destruct (evalExpr p); [exact (Ht _ H) | exact H].
  Qed.

  (* The ALU step: [NonDet] chooses [leftovers] *)
  Lemma nondet_alu_step : forall (env : Env sysTree) k nm nm' pcc pkg
                               (c : type AluOutUnion -> Action type sysTree k) st P,
    evalActionPropGen env (LetAction nm (toAction _ (@specAlu type pcc pkg)) c) st P ->
    evalActionPropGen env (NonDet nm' FreeVals (fun free =>
                             LetAction nm (toAction _ (@nondetAlu type free pcc pkg)) c)) st P.
  Proof.
    intros env k nm nm' pcc pkg c st P H. cbn [evalActionPropGen] in H |- *.
    exists (leftovers pcc pkg). cbn [evalActionPropGen].
    rewrite evalActionPropGen_toAction in H |- *. rewrite nondetAlu_leftovers. exact H.
  Qed.

  Lemma nondet_step : forall (env : Env sysTree) s P,
    evalActionPropGen env (simpleSpecStep pcAddrInit config clint plic type) s P ->
    evalActionPropGen env (nondetSpecStep pcAddrInit config clint plic type) s P.
  Proof.
    intros env s P.
    unfold simpleSpecStep, specStepWith, nondetSpecStep.
    apply nondet_letA_mono; intros s1 fenceIWait.
    apply nondet_letA_mono; intros s2 secondLine.
    apply nondet_if_mono; intros Q.
    apply nondet_letA_mono; intros s3 meip.
    apply nondet_letA_mono; intros s4 mtip.
    apply nondet_letA_mono; intros s5 fetchOut.
    apply nondet_letL_mono.
    apply nondet_letA_mono; intros s7 pkg.
    apply nondet_letA_mono; intros s8 pcc.
    apply nondet_alu_step.
  Qed.

  Lemma nondet_SemAction_step : forall (env : Env sysTree) s s' r,
    SemAction env (simpleSpecStep pcAddrInit config clint plic type) s s' r ->
    SemAction env (nondetSpecStep pcAddrInit config clint plic type) s s' r.
  Proof.
    intros env s s' r H. rewrite SemAction_iff_evalActionPropGen in H |- *. exact (nondet_step env s _ H).
  Qed.

  (* The rule lists agree except at the core step *)
  Lemma nondet_in_simpleSpec : forall a,
    In a (simpleSpec pcAddrInit config clint rev plic type) ->
    simpleSpecStep pcAddrInit config clint plic type = a \/
    In a (nondetSpec pcAddrInit config clint rev plic type).
  Proof.
    intros a Hin. unfold simpleSpec, nondetSpec in *.
    rewrite !in_app_iff in Hin |- *. cbn [In] in Hin |- *. tauto.
  Qed.

  Lemma nondet_nondetSpecStep_in :
    In (nondetSpecStep pcAddrInit config clint plic type) (nondetSpec pcAddrInit config clint rev plic type).
  Proof. unfold nondetSpec. rewrite !in_app_iff. cbn [In]. tauto. Qed.

  Lemma nondet_SemActions_simpleSpec_nondetSpec : forall (env : Env sysTree) old new,
    SemActions env (simpleSpec pcAddrInit config clint rev plic type) old new ->
    SemActions env (nondetSpec pcAddrInit config clint rev plic type) old new.
  Proof.
    intros env old new H. induction H as [old new Heq | old new mid a Hin Ha Hrest IH].
    - eapply NilAction; exact Heq.
    - destruct (nondet_in_simpleSpec a Hin) as [<- | Hin'].
      + eapply ConsAction; [exact nondet_nondetSpecStep_in | exact (nondet_SemAction_step env _ _ _ Ha) | exact IH].
      + eapply ConsAction; [exact Hin' | exact Ha | exact IH].
  Qed.

  Theorem nondet_SemMod_simpleSpec_nondetSpec : forall (env : Env sysTree) old new,
    SemMod env (simpleSpec pcAddrInit config clint rev plic) old new ->
    SemMod env (nondetSpec pcAddrInit config clint rev plic) old new.
  Proof.
    intros env old new [o n Hinit Hacts].
    constructor; [exact Hinit | exact (nondet_SemActions_simpleSpec_nondetSpec env _ _ Hacts)].
  Qed.
End NondetEq.
