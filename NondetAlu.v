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
 * ALU with arbitrary values in the don't-care fields (nondetAlu)
 * ===========================================================================
 * [nondetAlu pcc pkg free] is [specAlu pcc pkg] (Alu.v) except that the fields no consumer reads
 * take their values from [free] instead of reproducing what the shared datapath leaves there:
 *   - [dstValue] of instructions that write no register result: [free.dst];
 *   - [NewPcc.ecap] of Branch and Cjal: [free.newPcc.ecap];
 *   - [NewPcc] and [interruptStatus] of Mret: [free.newPcc] and [free.intStatus];
 *   - [SpecialValue.tag] and [SpecialValue.ecap] of Csr: [free.special].
 * The spec step (NondetSpec.v) draws [free] with [NonDet]. All other arms are those of Alu.v.
 * Main entry: [nondetAlu]. *)

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations.
From Cheriot Require Import SpecDefines FunctionalUnits.
From SpecCheriot Require Import Alu.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.

(* The arbitrary values for the don't-care fields *)
Definition FreeVals := STRUCT_TYPE {
  "dst"       :: FullECapWithTag ;
  "newPcc"    :: FullECapWithTag ;
  "intStatus" :: Option Bool ;
  "special"   :: FullECapWithTag }.

Section NondetAlu.
  Variable ty : Kind -> Type.
  Variable free : ty FreeVals.

  (* Branches: BEQ, BNE, BLT, BGE, BLTU, BGEU rs1, rs2, bimm12 *)
  Definition nondetBranch (pcc cs1 cs2 : ty FullECapWithTag) (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE pccTag : Bool <- ##pcc`"tag" ;
    LetE pccECap : ECap <- ##pcc`"ecap" ;
    LetE pccBase : Bit (AddrSz + 1) <- ##pccECap`"base" ;
    LetE pcc_cE : Bit ExpSz <- ##pccECap`"cE" ;
    LetE pccExp : Bit ExpSz <- get_E_from_cE pcc_cE ;
    LetE target : Addr <- Add [ ##pcc`"addr" ; getBImm inst ] ;
    LETE inBounds : Bool <- specRepresentable pccTag pccBase pccExp target ;
    LetE funct3 : Bit 3 <- ##inst`[14:12] ;
    LetE isLt : Bool <- FromBit Bool (#funct3`[2:2]) ;
    LetE isUnsigned : Bool <- FromBit Bool (#funct3`[1:1]) ;
    LetE negate : Bool <- FromBit Bool (#funct3`[0:0]) ;
    LetE a : Bit Xlen <- ##cs1`"addr" ;
    LetE b : Bit Xlen <- ##cs2`"addr" ;
    LETE lt : Bool <- specLessThan isUnsigned a b ;
    LetE cmp : Bool <- ITE #isLt #lt (Eq #a #b) ;
    LetE taken : Bool <- ITE #negate (Not #cmp) #cmp ;
    specOut (##free`"dst")
      (specOpCf (STRUCT {
         "NewPcc"     ::= specCapResult #inBounds ((##free`"newPcc")`"ecap") #target ;
         "capChanged" ::= And [ #taken ; Not (Eq #inBounds #pccTag) ] ;
         "CfOp"       ::= UNION (CfOpType, "ControlFlowAddrOnly" ::=
                                   UNION (ControlFlowAddrOnlyOpType, "Branch" ::= #taken)) })).

  (* CJAL cd, jimm20 *)
  Definition nondetCjal (pcc : ty FullECapWithTag) (isComp : ty Bool) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE pccTag : Bool <- ##pcc`"tag" ;
    LetE pccECap : ECap <- ##pcc`"ecap" ;
    LetE pccBase : Bit (AddrSz + 1) <- ##pccECap`"base" ;
    LetE pcc_cE : Bit ExpSz <- ##pccECap`"cE" ;
    LetE pccExp : Bit ExpSz <- get_E_from_cE pcc_cE ;
    LetE target : Addr <- Add [ ##pcc`"addr" ; getJImm inst ] ;
    LETE inBounds : Bool <- specRepresentable pccTag pccBase pccExp target ;
    LetE isCall : Bool <- Eq (getCd inst) $Cra ;
    specOut (specCapResult #pccTag #pccECap (specLinkAddr pcc isComp))
      (specOpCf (STRUCT {
         "NewPcc"     ::= specCapResult #inBounds ((##free`"newPcc")`"ecap") #target ;
         "capChanged" ::= Not (Eq #inBounds #pccTag) ;
         "CfOp"       ::= UNION (CfOpType, "ControlFlowAddrOnly" ::=
                                   UNION (ControlFlowAddrOnlyOpType, "Cjal" ::= #isCall)) })).

  (* MRET: executeNonSequential computes the new pcc from MEPCC *)
  Definition nondetMret : LetExpr ty SpecInstOut :=
    specOut (##free`"dst")
      (specOpCf (STRUCT {
         "NewPcc"     ::= (##free`"newPcc") ;
         "capChanged" ::= Const ty Bool true ;
         "CfOp"       ::= UNION (CfOpType, "ControlFlowAddrECap" ::=
                                   STRUCT { "interruptStatus" ::= ##free`"intStatus" ;
                                            "op" ::= UNION (ControlFlowAddrECapOpType, "Mret" ::=
                                                        Const ty (Bit 0) Zmod.zero) }) })).

  (* CSR access: CSRRW, CSRRS, CSRRC rd, csr, rs1 and CSRRWI, CSRRSI, CSRRCI rd, csr, zimm5 *)
  Definition nondetCsr (cs1 : ty FullECapWithTag) (csrIdx : ty (Bit CsrIdxSz)) (isImm : ty Bool)
                       (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE addr : Addr <- ##cs1`"addr" ;
    LetE funct2 : Bit 2 <- ##inst`[13:12] ;
    specOut (##free`"dst")
      (specOpScrCsr (STRUCT {
         "SpecialDest"  ::= UNION (ScrCsrIdx, "Csr" ::= #csrIdx) ;
         "SpecialValue" ::= specCapResult ((##free`"special")`"tag") ((##free`"special")`"ecap")
                              (ITE #isImm (ZeroExtendTo Xlen (##inst`[19:15])) #addr) ;
         "isSet"        ::= Eq #funct2 $2 ;
         "isClear"      ::= Eq #funct2 $3 ;
         "isWrite"      ::= Or [ Eq #funct2 $1 ; isNotZero (getCs1 inst) ] })).

  (* CSpecialRw cd, scr, cs1 (the register result comes from the SCR itself) *)
  Definition nondetScr (cs1 : ty FullECapWithTag) (scrIdx : ty (Bit ScrIdxSz)) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE tag : Bool <- ##cs1`"tag" ;
    LetE addr : Addr <- ##cs1`"addr" ;
    LETE newTag : Bool <- ScrSanitizer tag addr inst ;
    LetE scrAddr : Bit ScrAddrSz <- getScr inst ;
    LetE isSpecialPcc : Bool <- Or [ Eq #scrAddr $(getScrAddr "MePcc"%string) ;
                                     Eq #scrAddr $(getScrAddr "Mtcc"%string) ] ;
    LetE funct2 : Bit 2 <- ##inst`[13:12] ;
    specOut (##free`"dst")
      (specOpScrCsr (STRUCT {
         "SpecialDest"  ::= UNION (ScrCsrIdx, "Scr" ::= #scrIdx) ;
         "SpecialValue" ::= specCapResult #newTag (##cs1`"ecap")
                              (ITE #isSpecialPcc
                                 {< TruncMsb (AddrSz - 1) 1 #addr, Const ty (Bit 1) Zmod.zero >} #addr) ;
         "isSet"        ::= Eq #funct2 $2 ;
         "isClear"      ::= Eq #funct2 $3 ;
         "isWrite"      ::= Or [ Eq #funct2 $1 ; isNotZero (getCs1 inst) ] })).

  (* ECALL and EBREAK *)
  Definition nondetECall : LetExpr ty SpecInstOut :=
    specOut (##free`"dst") (specOpExc (mkExceptionInfo $EXC_ECallM (mkCheriMtval (Const ty Bool false) $0 $0))).

  Definition nondetEBreak : LetExpr ty SpecInstOut :=
    specOut (##free`"dst") (specOpExc (mkExceptionInfo $EXC_Breakpoint (mkCheriMtval (Const ty Bool false) $0 $0))).

  (* FENCE, FENCE.TSO and FENCE.I *)
  Definition nondetFence (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE isFenceI : Bool <- isNotZero (##inst`[12:12]) ;
    LetE isTso : Bool <- isNotZero (##inst`[31:31]) ;
    LetE pred_r : Bool <- isNotZero (##inst`[25:25]) ;
    LetE pred_w : Bool <- isNotZero (##inst`[24:24]) ;
    LetE succ_r : Bool <- isNotZero (##inst`[21:21]) ;
    LetE succ_w : Bool <- isNotZero (##inst`[20:20]) ;
    LetE fence : FenceOp <- STRUCT {
      "RR"     ::= And [ #pred_r ; #succ_r ] ;
      "RW"     ::= And [ #pred_r ; #succ_w ] ;
      "WR"     ::= And [ Not #isTso ; #pred_w ; #succ_r ] ;
      "WW"     ::= And [ #pred_w ; #succ_w ] ;
      "FenceI" ::= #isFenceI } ;
    specOut (##free`"dst") (specOpDataMem (UNION (MemFenceType, "Fence" ::= #fence))).

  (* No class bit: the decoder flags the instruction as illegal *)
  Definition nondetNone : LetExpr ty SpecInstOut := specOut (##free`"dst") (@specOpNormal ty).

  (* ---------------------------------------------------------------------------
   * Dispatch
   * --------------------------------------------------------------------------- *)

  Definition nondetAlu (pcc : ty FullECapWithTag) (pkg : ty AluInInstGroup) : LetExpr ty AluOutUnion :=
    LetE g : InstGroup <- ##pkg`"instGroup" ;
    LetE inst : Inst <- ##pkg`"inst" ;
    LetE cs1 : FullECapWithTag <- ##pkg`"cs1" ;
    LetE cs2 : FullECapWithTag <- ##pkg`"cs2" ;
    LetE fetchExc : FetchException <- ##pkg`"fetchExc" ;
    LetE decodeExc : DecodeException <- ##pkg`"decodeExc" ;
    LetE scrIdx : Bit ScrIdxSz <- ##pkg`"readWriteScrIdx" ;
    LetE csrIdx : Bit CsrIdxSz <- ##pkg`"readWriteCsrIdx" ;
    LetE isComp : Bool <- isCompressed inst ;
    LetE isImm : Bool <- ##g`"isImm" ;
    LetE isSub : Bool <- ##g`"AddSub_isSub" ;
    LetE isExact : Bool <- ##g`"CSetBounds_isExact" ;
    LetE isRoundDown : Bool <- ##g`"CSetBounds_isRoundDown" ;
    LetE true_ : Bool <- Const ty Bool true ;
    LetE false_ : Bool <- Const ty Bool false ;
    LETE fdExc : Option ExceptionInfo <- specFetchDecodeExc fetchExc decodeExc inst ;
    LETE out : SpecInstOut <-
      specCases [
        (##g`"Lui"         , specLui inst) ;
        (##g`"AuiPcc"      , specAuiPcc pcc inst) ;
        (##g`"AuiCgp"      , specAuiCgp cs1 inst) ;
        (##g`"CIncAddr"    , specCIncAddr cs1 cs2 isImm inst) ;
        (##g`"CSetAddr"    , specCSetAddr cs1 cs2) ;
        (##g`"Branch"      , nondetBranch pcc cs1 cs2 inst) ;
        (##g`"Cjal"        , nondetCjal pcc isComp inst) ;
        (##g`"Cjalr"       , specCjalr pcc cs1 isComp inst) ;
        (##g`"Mret"        , nondetMret) ;
        (##g`"CTestSubset" , specCTestSubset cs1 cs2) ;
        (##g`"CSetBounds"  , specCSetBounds cs1 cs2 isImm isExact isRoundDown inst) ;
        (##g`"Seal"        , specSealUnseal cs1 cs2 false_) ;
        (##g`"Unseal"      , specSealUnseal cs1 cs2 true_) ;
        (##g`"Load"        , specLoad cs1 inst) ;
        (##g`"Store"       , specStore cs1 cs2 inst) ;
        (##g`"MulDiv"      , specMulDiv cs1 cs2 inst) ;
        (##g`"AddSub"      , specAddSub cs1 cs2 isImm isSub inst) ;
        (##g`"CGetLen"     , specCGetLen cs1) ;
        (##g`"CGetBase"    , specCGetBaseTop cs1 true_ false_) ;
        (##g`"CGetTop"     , specCGetBaseTop cs1 false_ true_) ;
        (##g`"Slt"         , specSlt cs1 cs2 isImm inst) ;
        (##g`"CSetEqual"   , specCSetEqual cs1 cs2) ;
        (##g`"Shift"       , specShift cs1 cs2 isImm inst) ;
        (##g`"Logical"     , specLogical cs1 cs2 isImm inst) ;
        (##g`"Cram"        , specCramCrrl cs1 true) ;
        (##g`"Crrl"        , specCramCrrl cs1 false) ;
        (##g`"CAndPerm"    , specCAndPerm cs1 cs2) ;
        (##g`"Csr"         , nondetCsr cs1 csrIdx isImm inst) ;
        (##g`"Scr"         , nondetScr cs1 scrIdx inst) ;
        (##g`"CGetPerm"    , specCGetPerm cs1) ;
        (##g`"CGetType"    , specCGetType cs1) ;
        (##g`"CGetTag"     , specCGetTag cs1) ;
        (##g`"CGetAddr"    , specCGetAddr cs1) ;
        (##g`"CGetHigh"    , specCGetHigh cs1) ;
        (##g`"CSetHigh"    , specCSetHigh cs1 cs2) ;
        (##g`"CClearTag"   , specCClearTag cs1) ;
        (##g`"CMove"       , specCMove cs1) ;
        (##g`"ECall"       , nondetECall) ;
        (##g`"EBreak"      , nondetEBreak) ;
        (##g`"Fence"       , nondetFence inst)
      ] nondetNone ;
    @RetE _ AluOutUnion (STRUCT {
      "isComp"   ::= #isComp ;
      "dstIdx"   ::= ITE0 (##pkg`"writesCd")
                       (TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd inst)) ;
      "dstValue" ::= ##out`"dstValue" ;
      "Op"       ::= ITE (##fdExc`"valid") (specOpExc (##fdExc`"data")) (##out`"op")
    }).
End NondetAlu.
