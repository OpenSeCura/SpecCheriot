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
 * pipelinedMod refines simpleSpec
 * ===========================================================================
 * Main result:
 *   - [pipelinedMod_refines_simpleSpec]: [pipelinedMod_refines_spec] (Proof/RefTop.v) with [simpleSpec]
 *     (the specification with the instruction-by-instruction ALU) in place of [spec]. The
 *     software rule is stated on [simpleSpec] runs too. *)

From Stdlib Require Import String List ZArith Zmod Lia Bool.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics Composition Theorems HelperLemmas.
From Cheriot Require Import SpecDefines Spec SpecDevice Clint Plic SpecRevoker.
From Cheriot Require Import Impl ImplCommon ImplDevice ImplRevoker ImplMulDiv ImplInst.
From Cheriot.Proof Require Import StateRel ImplSpec Refinement SimDevices RefRel RefCoreRel RefRevBitRule RefRedirect RefTop.
From SpecCheriot Require Import Spec.
From SpecCheriot.Proof Require Import SpecEq.

Unset Implicit Arguments.
Unset Strict Implicit.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope guru_scope.

Section SpecTop.
  Variable pcAddrInit : Z.
  Variable issueWidth : nat.
  Variable fetchCapacity instCapacity decodeCapacity dataMemCapacity : nat.
  Variable mulCapacity divCapacity mulStages divStages : nat.
  Variable mulDivMode : MulDivMode.
  Variable bp : WithInstPredIfc.
  Variable config : RevConfig.
  Variables pre post : list MemRegion.
  Variable revBase : Z.
  Variable revPfB : Is_true ((0 <=? revBase) && (revBase + RevokerSizeBytes <=? Z.shiftl 1 AddrSz))%Z.
  Variable revPfA : Is_true (revBase mod (2 ^ LgLineBytes) =? 0)%Z.

  Local Abbreviation specRegions := (specRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation implRegions := (implRegionsOf pre post revBase revPfB revPfA).
  Local Abbreviation revSpec := (revSpecOf pre post revBase revPfB revPfA).
  Local Abbreviation rev := (revImplOf pre post revBase revPfB revPfA).

  Variable clintS : @ClintInstance specRegions.
  Variable clint : @ClintInstance implRegions.
  Variable plicS : @PlicInstance (S (S (length (collectIrqActions specRegions)))) specRegions.
  Variable plic : @PlicInstance (S (S (length (collectIrqActions implRegions)))) implRegions.

  Hypothesis Hdisj : Is_true (pairwiseDisjoint specRegions).
  Hypothesis HrevTab : Is_true (revTableInExternalMem config specRegions).
  Hypothesis HclintIdx : clintIdx clint = clintIdx clintS.
  Hypothesis HplicIdx : plicIdx plic = plicIdx plicS.
  Hypothesis Hmd : Is_true (mulDivStagesDivideXlen mulStages divStages).
  Hypothesis HdetPre : Forall (fun r => allTreeInitDet (memRegionTree r) = true) pre.
  Hypothesis HdetPost : Forall (fun r => allTreeInitDet (memRegionTree r) = true) post.
  Hypothesis HpcEven : pcAligned (Zmod.of_Z _ pcAddrInit).

  Local Abbreviation sTree := (SpecTree pcAddrInit specRegions).
  Local Abbreviation simpleSpecMod := (@simpleSpec pcAddrInit config specRegions clintS revSpec plicS).
  Local Abbreviation pipeMod :=
    (@pipelinedMod pcAddrInit issueWidth fetchCapacity instCapacity decodeCapacity
       dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp
       config implRegions clint rev plic).
  Local Abbreviation implEnvL initLine fwc :=
    (implEnv pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
             mulCapacity divCapacity mulStages divStages mulDivMode bp config implRegions initLine fwc).
  Local Abbreviation specEnvL initLine fwc := (specEnv pcAddrInit specRegions initLine fwc).
  Local Abbreviation SRuleL initLine :=
    (SpecRevBitRule pcAddrInit config pre post revBase revPfB revPfA initLine).
  Local Abbreviation RelL initLine fwc :=
    (RefRelR pcAddrInit fetchCapacity instCapacity decodeCapacity dataMemCapacity
            mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post revBase revPfB revPfA
            clintS clint plicS plic initLine fwc).

  (* The software rule of RefTop.v, on runs of simpleSpec *)
  Definition SpecSoftwareRevBitsRule initLine fwc (old2 : TreeState ElemState sTree) : Prop :=
    forall s2 s2' a,
      SemActions (specEnvL initLine fwc) (simpleSpecMod type) old2 s2 ->
      In a (simpleSpecMod type) ->
      SemAction (specEnvL initLine fwc) a s2 s2' Zmod.zero ->
      SRuleL initLine s2 s2'.

  Lemma spec_rule_transfer : forall initLine fwc old2,
    SpecSoftwareRevBitsRule initLine fwc old2 ->
    SoftwareRevBitsRule pcAddrInit config pre post revBase revPfB revPfA clintS plicS initLine fwc old2.
  Proof.
    intros initLine fwc old2 H s2 s2' a Hrun Hin Ha.
    pose proof (spec_SemActions_spec_simpleSpec _ _ _ _ _ _ _ _ _ Hrun) as Hrun'.
    destruct (spec_in_spec _ _ _ _ _ _ a Hin) as [<- | Hin'].
    - exact (H s2 s2' _ Hrun' (spec_simpleSpecStep_in _ _ _ _ _ _) (spec_step_spec_simpleSpec _ _ _ _ _ _ _ _ _ Ha)).
    - exact (H s2 s2' a Hrun' Hin' Ha).
  Qed.

  Theorem pipelinedMod_refines_simpleSpec :
    forall initLine fwc old1 new1,
      SemMod (implEnvL initLine fwc) pipeMod old1 new1 ->
      forall old2, InitStateConsistent sTree old2 ->
      SpecSoftwareRevBitsRule initLine fwc old2 ->
      exists fwc' new2, SemMod (specEnvL initLine fwc') simpleSpecMod old2 new2 /\ RelL initLine fwc new1 new2.
  Proof.
    intros initLine fwc old1 new1 Hsem old2 Hinit2 Hrule.
    destruct (pipelinedMod_refines_spec pcAddrInit issueWidth fetchCapacity instCapacity decodeCapacity
                dataMemCapacity mulCapacity divCapacity mulStages divStages mulDivMode bp config pre post
                revBase revPfB revPfA clintS clint plicS plic Hdisj HrevTab HclintIdx HplicIdx Hmd HdetPre
                HdetPost HpcEven initLine fwc old1 new1 Hsem old2 Hinit2 (spec_rule_transfer _ _ _ Hrule))
      as [fwc' [new2 [Hspec Hrel]]].
    exists fwc', new2. split; [exact (spec_SemMod_spec_simpleSpec _ _ _ _ _ _ _ _ _ Hspec) | exact Hrel].
  Qed.
End SpecTop.
