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
 * Instruction classes and well-formed decoder groups
 * ===========================================================================
 * [SpecClass] names the instruction class that the decoder selects in [InstGroup] (one class bit,
 * or none for an illegal instruction). [specGroup inst c isImm isExact isRoundDown isSub] is the
 * [InstGroup] the decoder produces for an instruction [inst] of class [c]:
 *   - exactly the class bit of [c] is set (no class bit for [cNone]);
 *   - [isCompressed] is [isCompressed inst];
 *   - the side flags CSetBounds_isExact / CSetBounds_isRoundDown / AddSub_isSub are only set
 *     together with their class;
 *   - the comparator controls are the ones the decoder derives from funct3 (Branch, Slt) or the
 *     constant ones (CSetEqual), and are clear for every other class.
 * The equivalence of [specAlu] (Alu.v) with [wrappedAlu] holds for every package whose group is
 * of this form; Decode.v shows that the decoder only produces such groups. *)

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Cheriot Require Import SpecDefines.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.

Inductive SpecClass :=
| cBranch | cCjal | cAuiPcc | cAuiCgp | cCIncAddr | cCSetAddr | cCjalr | cCTestSubset | cCSetBounds
| cSeal | cUnseal | cLoad | cStore | cMulDiv | cAddSub | cCGetLen | cSlt | cCSetEqual | cShift
| cLogical | cCram | cCrrl | cCAndPerm | cCsr | cScr | cLui | cCGetPerm | cCGetType | cCGetBase
| cCGetTag | cCGetAddr | cCGetHigh | cCGetTop | cCSetHigh | cCClearTag | cCMove | cECall | cEBreak
| cMret | cFence | cNone.

Scheme Equality for SpecClass.

Section Group.
  Variable ty : Kind -> Type.
  Variable inst : ty Inst.
  Variable c : SpecClass.
  Variable isImm isExact isRoundDown isSub : bool.

  Local Abbreviation cls x := (Const ty Bool (SpecClass_beq x c)).
  Local Abbreviation clsAnd x b := (Const ty Bool (andb (SpecClass_beq x c) b)).

  Definition specGroupExpr : Expr ty InstGroup :=
    STRUCT {
      "isCompressed"                 ::= isCompressed inst ;
      "isImm"                        ::= Const ty Bool isImm ;
      "Branch"                       ::= cls cBranch ;
      "Cjal"                         ::= cls cCjal ;
      "AuiPcc"                       ::= cls cAuiPcc ;
      "AuiCgp"                       ::= cls cAuiCgp ;
      "CIncAddr"                     ::= cls cCIncAddr ;
      "CSetAddr"                     ::= cls cCSetAddr ;
      "Cjalr"                        ::= cls cCjalr ;
      "CTestSubset"                  ::= cls cCTestSubset ;
      "CSetBounds"                   ::= cls cCSetBounds ;
      "CSetBounds_isExact"           ::= clsAnd cCSetBounds isExact ;
      "CSetBounds_isRoundDown"       ::= clsAnd cCSetBounds isRoundDown ;
      "Seal"                         ::= cls cSeal ;
      "Unseal"                       ::= cls cUnseal ;
      "Load"                         ::= cls cLoad ;
      "Store"                        ::= cls cStore ;
      "MulDiv"                       ::= cls cMulDiv ;
      "AddSub"                       ::= cls cAddSub ;
      "AddSub_isSub"                 ::= clsAnd cAddSub isSub ;
      "CGetLen"                      ::= cls cCGetLen ;
      "Slt"                          ::= cls cSlt ;
      "CSetEqual"                    ::= cls cCSetEqual ;
      "Shift"                        ::= cls cShift ;
      "Logical"                      ::= cls cLogical ;
      "Cram"                         ::= cls cCram ;
      "Crrl"                         ::= cls cCrrl ;
      "CAndPerm"                     ::= cls cCAndPerm ;
      "Csr"                          ::= cls cCsr ;
      "Scr"                          ::= cls cScr ;
      "Lui"                          ::= cls cLui ;
      "CGetPerm"                     ::= cls cCGetPerm ;
      "CGetType"                     ::= cls cCGetType ;
      "CGetBase"                     ::= cls cCGetBase ;
      "CGetTag"                      ::= cls cCGetTag ;
      "CGetAddr"                     ::= cls cCGetAddr ;
      "CGetHigh"                     ::= cls cCGetHigh ;
      "CGetTop"                      ::= cls cCGetTop ;
      "CSetHigh"                     ::= cls cCSetHigh ;
      "CClearTag"                    ::= cls cCClearTag ;
      "CMove"                        ::= cls cCMove ;
      "ECall"                        ::= cls cECall ;
      "EBreak"                       ::= cls cEBreak ;
      "Mret"                         ::= cls cMret ;
      "Fence"                        ::= cls cFence ;
      "ComparatorGeneral_isUnsigned" ::=
        match c with
        | cBranch => FromBit Bool ((#inst`[14:12])`[1:1])
        | cSlt    => FromBit Bool ((#inst`[14:12])`[0:0])
        | _       => ConstBool false
        end ;
      "ComparatorGeneral_checkLt"    ::=
        match c with
        | cBranch => FromBit Bool ((#inst`[14:12])`[2:2])
        | cSlt    => ConstBool true
        | _       => ConstBool false
        end ;
      "ComparatorGeneral_checkEq"    ::=
        match c with
        | cBranch   => Not (FromBit Bool ((#inst`[14:12])`[2:2]))
        | cCSetEqual => ConstBool true
        | _         => ConstBool false
        end ;
      "ComparatorGeneral_invertRes"  ::=
        match c with
        | cBranch => FromBit Bool ((#inst`[14:12])`[0:0])
        | _       => ConstBool false
        end
    }.
End Group.

Definition specGroup (inst : type Inst) (c : SpecClass) (isImm isExact isRoundDown isSub : bool)
  : type InstGroup :=
  evalExpr (specGroupExpr inst c isImm isExact isRoundDown isSub).

(* A package is well formed when its group is the decoder's group for its instruction. *)
Definition SpecWellFormed (pkg : type AluInInstGroup) : Prop :=
  exists c isImm isExact isRoundDown isSub,
    evalExpr (##pkg`"instGroup") =
    specGroup (evalExpr (##pkg`"inst")) c isImm isExact isRoundDown isSub.
