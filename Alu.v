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
 * Instruction-by-instruction ALU specification (specAlu)
 * ===========================================================================
 * [specAlu pcc pkg] computes the same [AluOutUnion] as [wrappedAlu pcc pkg] (cheriot/Alu.v), but each
 * instruction class is its own if-then-else block that computes its result directly, instead of
 * sharing the functional units of FunctionalUnits.v through the [AluControl] routing.
 *
 * Shared adders and comparators are written out (Add, Sub, Ult, ...). Units that serve a single
 * purpose (Bounds, Shifter, Logical, CjalrUnit, SealerUnsealer, CAndPerm, EncodeCap, DecodeCap,
 * MemException, MulDiv, Saturater, AdderBeforeRepCheck, AdderAccessEnd, CapSubset, CapEq,
 * BoundsTag, ScrSanitizer) are called directly.
 *
 * DON'T-CARE VALUES. The equivalence is an equality of [AluOutUnion] values, so the spec also
 * reproduces the values the shared datapath leaves in fields that no consumer reads. They are
 * marked "don't care" below:
 *   - [dstValue] of instructions that write no register result: [specNoResult], which is
 *     {tag = false; ecap = default; addr = uimm20}.
 *   - [NewPcc.ecap] of Branch, Cjal and Mret: the CJALR unit's capability (cs1 with its otype
 *     cleared). Mret also takes [NewPcc.addr] (cs1.addr + simm12), [NewPcc.tag] (pcc.tag) and
 *     [interruptStatus] from the datapath; executeNonSequential reads MEPCC instead.
 *   - [SpecialValue.tag] and [SpecialValue.ecap] of Csr: the SCR sanitizer output and cs1.ecap;
 *     a CSR write only uses [SpecialValue.addr].
 *
 * Fetch and decode exceptions are checked first, for every instruction, in priority order.
 * Main entry: [specAlu]. *)

From Stdlib Require Import String List ZArith Zmod.
From Guru Require Import Primitives Library Syntax Combinators Notations.
From Cheriot Require Import SpecDefines FunctionalUnits.

Set Implicit Arguments.
Unset Strict Implicit.
Set Asymmetric Patterns.

Import ListNotations.
Local Open Scope guru_scope.
Local Open Scope string_scope.

(* The result of one instruction when there is no fetch or decode exception. *)
Definition SpecInstOut := STRUCT_TYPE {
  "dstValue" :: FullECapWithTag ;
  "op"       :: AluOpUnion }.

Section Alu.
  Variable ty : Kind -> Type.

  (* ---------------------------------------------------------------------------
   * Immediates and register results
   * --------------------------------------------------------------------------- *)

  Definition specSimm12 (inst : ty Inst) : Expr ty (Bit Xlen) := SignExtendTo Xlen (##inst`[31:20]).
  Definition specStoreImm (inst : ty Inst) : Expr ty (Bit Xlen) :=
    SignExtendTo Xlen ({< ##inst`[31:25], ##inst`[11:7] >}).
  Definition specZimm12 (inst : ty Inst) : Expr ty (Bit Xlen) := ZeroExtendTo Xlen (##inst`[31:20]).
  Definition specUimm20 (inst : ty Inst) : Expr ty (Bit Xlen) :=
    {< ##inst`[31:12], Const ty (Bit 12) Zmod.zero >}.
  Definition specUimm20_11 (inst : ty Inst) : Expr ty (Bit Xlen) :=
    {< ##inst`[31:31], ##inst`[31:12], Const ty (Bit 11) Zmod.zero >}.

  (* An integer result: untagged, default metadata *)
  Definition specIntResult (v : Expr ty (Bit Xlen)) : Expr ty FullECapWithTag :=
    STRUCT { "tag" ::= Const ty Bool false ; "ecap" ::= Const ty ECap (getDefault _) ; "addr" ::= v }.

  Definition specCapResult (tag : Expr ty Bool) (ecap : Expr ty ECap) (addr : Expr ty Addr)
    : Expr ty FullECapWithTag :=
    STRUCT { "tag" ::= tag ; "ecap" ::= ecap ; "addr" ::= addr }.

  (* Don't care: dstValue of an instruction without a register result *)
  Definition specNoResult (inst : ty Inst) : Expr ty FullECapWithTag := specIntResult (specUimm20 inst).

  (* ---------------------------------------------------------------------------
   * Operation kinds
   * --------------------------------------------------------------------------- *)

  Definition specOpNormal : Expr ty AluOpUnion :=
    UNION (AluOpUnionType, "Sequential" ::=
             UNION (SequentialUnionType, "Normal" ::= Const ty (Bit 0) Zmod.zero)).

  Definition specOpMulDiv (md : Expr ty MulDivUnion) : Expr ty AluOpUnion :=
    UNION (AluOpUnionType, "Sequential" ::= UNION (SequentialUnionType, "MulDiv" ::= md)).

  Definition specOpExc (e : Expr ty ExceptionInfo) : Expr ty AluOpUnion :=
    UNION (AluOpUnionType, "NonSequential" ::= UNION (NonSequentialUnionType, "Exception" ::= e)).

  Definition specOpNoExc (e : Expr ty NoExceptionUnion) : Expr ty AluOpUnion :=
    UNION (AluOpUnionType, "NonSequential" ::= UNION (NonSequentialUnionType, "NoException" ::= e)).

  Definition specOpDataMem (m : Expr ty MemFenceUnion) : Expr ty AluOpUnion :=
    specOpNoExc (UNION (NoExceptionUnionType, "DataMem" ::= m)).

  Definition specOpCf (cf : Expr ty CfPayload) : Expr ty AluOpUnion :=
    specOpNoExc (UNION (NoExceptionUnionType, "CfScrCsr" ::= UNION (CfScrCsrType, "ControlFlow" ::= cf))).

  Definition specOpScrCsr (p : Expr ty ScrCsrPayload) : Expr ty AluOpUnion :=
    specOpNoExc (UNION (NoExceptionUnionType, "CfScrCsr" ::= UNION (CfScrCsrType, "ScrCsr" ::= p))).

  Definition specOut (dst : Expr ty FullECapWithTag) (op : Expr ty AluOpUnion) : LetExpr ty SpecInstOut :=
    RetE (STRUCT { "dstValue" ::= dst ; "op" ::= op }).

  (* ---------------------------------------------------------------------------
   * Comparisons and bounds checks
   * --------------------------------------------------------------------------- *)

  Definition specUle n (a b : Expr ty (Bit n)) : Expr ty Bool := Or [ Ult a b ; Eq a b ].

  (* Signed (isUnsigned = false) or unsigned less-than: flip the sign bits for a signed compare *)
  Definition specLessThan (isUnsigned : ty Bool) (a b : ty (Bit Xlen)) : LetExpr ty Bool :=
    LetE flipBit : Bit 1 <- ToBit (Not #isUnsigned) ;
    let flipMsb e := {< Xor [#flipBit; TruncMsb 1 (Xlen-1) e], TruncLsb 1 (Xlen-1) e >} in
    RetE (Ult (flipMsb #a) (flipMsb #b)).

  (* A capability with this tag, base and exponent can hold address [addr] *)
  Definition specRepresentable (tag : ty Bool) (base : ty (Bit (AddrSz + 1))) (exp : ty (Bit ExpSz))
                             (addr : ty Addr) : LetExpr ty Bool :=
    LETE repLimit : Bit (AddrSz + 2) <- AdderBeforeRepCheck base exp ;
    RetE (And [ #tag ; And [ Ult (ZeroExtendTo (AddrSz + 2) #addr) #repLimit ;
                             Uge (ZeroExtendTo (AddrSz + 1) #addr) #base ] ]).

  (* A tagged capability [cs] grants access to the 2^lgSize bytes at [addr] *)
  Definition specAccessInBounds (cs : ty FullECapWithTag) (addr : ty Addr)
                              (lgSize : ty (Bit LgLgNumBytesFullCapSz)) : LetExpr ty Bool :=
    LetE ecap : ECap <- ##cs`"ecap" ;
    LETE accessEnd : Bit (AddrSz + 2) <- AdderAccessEnd addr lgSize ;
    RetE (And [ ##cs`"tag" ; And [ specUle #accessEnd (##ecap`"top") ;
                                   Uge (ZeroExtendTo (AddrSz + 1) #addr) (##ecap`"base") ] ]).

  (* ---------------------------------------------------------------------------
   * Fetch and decode exceptions, in priority order
   * --------------------------------------------------------------------------- *)

  Definition specFetchDecodeExc (fetchExc : ty FetchException) (decodeExc : ty DecodeException)
                              (inst : ty Inst) : LetExpr ty (Option ExceptionInfo) :=
    LetE scrIdx : Bit RegIdxSz <- getScr inst ;
    RetE (
      ITE (##fetchExc`"tag")
        (mkSome (mkExceptionInfo $EXC_CHERI (mkCheriMtval (Const ty Bool false) $0 $CapEx_TagViolation)))
      (ITE (##fetchExc`"seal")
        (mkSome (mkExceptionInfo $EXC_CHERI (mkCheriMtval (Const ty Bool false) $0 $CapEx_SealViolation)))
      (ITE (##fetchExc`"perm")
        (mkSome (mkExceptionInfo $EXC_CHERI (mkCheriMtval (Const ty Bool false) $0 $CapEx_PermitExecuteViolation)))
      (ITE (##fetchExc`"bounds")
        (mkSome (mkExceptionInfo $EXC_CHERI (mkCheriMtval (Const ty Bool false) $0 $CapEx_BoundsViolation)))
      (ITE (##decodeExc`"illegal")
        (mkSome (mkExceptionInfo $EXC_IllegalInst (mkCheriMtval (Const ty Bool false) $0 $0)))
      (ITE (##decodeExc`"asr")
        (mkSome (mkExceptionInfo $EXC_CHERI
                   (mkCheriMtval (Const ty Bool true) #scrIdx $CapEx_AccessSystemRegsViolation)))
        (mkNone ty))))))).

  (* ---------------------------------------------------------------------------
   * Instructions
   * --------------------------------------------------------------------------- *)

  (* LUI rd, uimm20 *)
  Definition specLui (inst : ty Inst) : LetExpr ty SpecInstOut :=
    specOut (specIntResult (specUimm20 inst)) specOpNormal.

  (* AUIPCC cd, uimm20_11: pcc with address pcc.addr + uimm20_11, untagged if unrepresentable *)
  Definition specAuiPcc (pcc : ty FullECapWithTag) (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##pcc`"ecap" ;
    LetE base : Bit (AddrSz + 1) <- ##ecap`"base" ;
    LetE cE : Bit ExpSz <- ##ecap`"cE" ;
    LetE exp : Bit ExpSz <- get_E_from_cE cE ;
    LetE tag : Bool <- ##pcc`"tag" ;
    LetE addr : Addr <- Add [ ##pcc`"addr" ; specUimm20_11 inst ] ;
    LETE ok : Bool <- specRepresentable tag base exp addr ;
    specOut (specCapResult #ok #ecap #addr) specOpNormal.

  (* AUICGP cd, uimm20_11 (cs1 is cgp) and CIncAddr[Imm] cd, cs1, rs2/simm12:
     cs1 with address cs1.addr + offset, untagged if unrepresentable *)
  Definition specIncAddr (cs1 : ty FullECapWithTag) (offset : ty Addr) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    LetE base : Bit (AddrSz + 1) <- ##ecap`"base" ;
    LetE cE : Bit ExpSz <- ##ecap`"cE" ;
    LetE exp : Bit ExpSz <- get_E_from_cE cE ;
    LetE tag : Bool <- ##cs1`"tag" ;
    LetE addr : Addr <- Add [ ##cs1`"addr" ; #offset ] ;
    LETE ok : Bool <- specRepresentable tag base exp addr ;
    specOut (specCapResult #ok #ecap #addr) specOpNormal.

  Definition specAuiCgp (cs1 : ty FullECapWithTag) (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE offset : Addr <- specUimm20_11 inst ;
    specIncAddr cs1 offset.

  Definition specCIncAddr (cs1 cs2 : ty FullECapWithTag) (isImm : ty Bool) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE offset : Addr <- ITE #isImm (specSimm12 inst) (##cs2`"addr") ;
    specIncAddr cs1 offset.

  (* CSetAddr cd, cs1, rs2: cs1 with address rs2, untagged if unrepresentable *)
  Definition specCSetAddr (cs1 cs2 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    LetE base : Bit (AddrSz + 1) <- ##ecap`"base" ;
    LetE cE : Bit ExpSz <- ##ecap`"cE" ;
    LetE exp : Bit ExpSz <- get_E_from_cE cE ;
    LetE tag : Bool <- ##cs1`"tag" ;
    LetE addr : Addr <- ##cs2`"addr" ;
    LETE ok : Bool <- specRepresentable tag base exp addr ;
    specOut (specCapResult #ok #ecap #addr) specOpNormal.

  (* Return address: pcc.addr + instruction size *)
  Definition specLinkAddr (pcc : ty FullECapWithTag) (isComp : ty Bool) : Expr ty Addr :=
    Add [ ##pcc`"addr" ; ITE #isComp $(CompInstSz/8) $(InstSz/8) ].

  (* Branches: BEQ, BNE, BLT, BGE, BLTU, BGEU rs1, rs2, bimm12 *)
  Definition specBranch (pcc cs1 cs2 : ty FullECapWithTag) (inst : ty Inst) : LetExpr ty SpecInstOut :=
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
    LETE dc : CjalrUnitRes <- CjalrUnit cs1 inst ; (* don't care: NewPcc.ecap *)
    specOut (specNoResult inst)
      (specOpCf (STRUCT {
         "NewPcc"     ::= specCapResult #inBounds (##dc`"ecap") #target ;
         "capChanged" ::= And [ #taken ; Not (Eq #inBounds #pccTag) ] ;
         "CfOp"       ::= UNION (CfOpType, "ControlFlowAddrOnly" ::=
                                   UNION (ControlFlowAddrOnlyOpType, "Branch" ::= #taken)) })).

  (* CJAL cd, jimm20 *)
  Definition specCjal (pcc cs1 : ty FullECapWithTag) (isComp : ty Bool) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE pccTag : Bool <- ##pcc`"tag" ;
    LetE pccECap : ECap <- ##pcc`"ecap" ;
    LetE pccBase : Bit (AddrSz + 1) <- ##pccECap`"base" ;
    LetE pcc_cE : Bit ExpSz <- ##pccECap`"cE" ;
    LetE pccExp : Bit ExpSz <- get_E_from_cE pcc_cE ;
    LetE target : Addr <- Add [ ##pcc`"addr" ; getJImm inst ] ;
    LETE inBounds : Bool <- specRepresentable pccTag pccBase pccExp target ;
    LetE isCall : Bool <- Eq (getCd inst) $Cra ;
    LETE dc : CjalrUnitRes <- CjalrUnit cs1 inst ; (* don't care: NewPcc.ecap *)
    specOut (specCapResult #pccTag #pccECap (specLinkAddr pcc isComp))
      (specOpCf (STRUCT {
         "NewPcc"     ::= specCapResult #inBounds (##dc`"ecap") #target ;
         "capChanged" ::= Not (Eq #inBounds #pccTag) ;
         "CfOp"       ::= UNION (CfOpType, "ControlFlowAddrOnly" ::=
                                   UNION (ControlFlowAddrOnlyOpType, "Cjal" ::= #isCall)) })).

  (* CJALR cd, cs1, simm12 *)
  Definition specCjalr (pcc cs1 : ty FullECapWithTag) (isComp : ty Bool) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE pccTag : Bool <- ##pcc`"tag" ;
    LetE pccECap : ECap <- ##pcc`"ecap" ;
    LetE target : Addr <- Add [ ##cs1`"addr" ; specSimm12 inst ] ;
    LETE j : CjalrUnitRes <- CjalrUnit cs1 inst ;
    LetE cd : Bit RegIdxSz <- getCd inst ;
    LetE isCall : Bool <- Eq #cd $Cra ;
    LetE isReturn : Bool <- And [ isZero #cd ; Eq (getCs1 inst) $Cra ] ;
    specOut (specCapResult (##cs1`"tag") #pccECap (specLinkAddr pcc isComp))
      (specOpCf (STRUCT {
         "NewPcc"     ::= specCapResult (##j`"tag") (##j`"ecap")
                            {< TruncMsb (AddrSz - 1) 1 #target, Const ty (Bit 1) Zmod.zero >} ;
         "capChanged" ::= Or [ Not (Eq (##j`"tag") #pccTag) ; Not (Eq (##j`"ecap") #pccECap) ] ;
         "CfOp"       ::= UNION (CfOpType, "ControlFlowAddrECap" ::=
                                   STRUCT { "interruptStatus" ::= ##j`"interruptStatus" ;
                                            "op" ::= UNION (ControlFlowAddrECapOpType, "Cjalr" ::=
                                                        STRUCT { "isCall" ::= #isCall ;
                                                                 "isReturn" ::= #isReturn }) }) })).

  (* MRET: executeNonSequential computes the new pcc from MEPCC *)
  Definition specMret (pcc cs1 : ty FullECapWithTag) (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE target : Addr <- Add [ ##cs1`"addr" ; specSimm12 inst ] ; (* don't care *)
    LETE dc : CjalrUnitRes <- CjalrUnit cs1 inst ;                (* don't care *)
    specOut (specNoResult inst)
      (specOpCf (STRUCT {
         "NewPcc"     ::= specCapResult (##pcc`"tag") (##dc`"ecap") #target ;
         "capChanged" ::= Const ty Bool true ;
         "CfOp"       ::= UNION (CfOpType, "ControlFlowAddrECap" ::=
                                   STRUCT { "interruptStatus" ::= ##dc`"interruptStatus" ;
                                            "op" ::= UNION (ControlFlowAddrECapOpType, "Mret" ::=
                                                        Const ty (Bit 0) Zmod.zero) }) })).

  (* CTestSubset rd, cs1, cs2 *)
  Definition specCTestSubset (cs1 cs2 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    LetE ecap1 : ECap <- ##cs1`"ecap" ;
    LetE ecap2 : ECap <- ##cs2`"ecap" ;
    LetE tag1 : Bool <- ##cs1`"tag" ;
    LetE tag2 : Bool <- ##cs2`"tag" ;
    LetE perms1 : CapPerms <- ##ecap1`"perms" ;
    LetE perms2 : CapPerms <- ##ecap2`"perms" ;
    LetE topLe : Bool <- specUle (##ecap1`"top") (##ecap2`"top") ;
    LetE baseGe : Bool <- Uge (##ecap1`"base") (##ecap2`"base") ;
    LETE subset : Bool <- CapSubset topLe baseGe tag1 tag2 perms1 perms2 ;
    specOut (specIntResult (ZeroExtendTo Xlen (ToBit #subset))) specOpNormal.

  (* CSetBounds, CSetBoundsExact, CSetBoundsRoundDown cd, cs1, rs2 and CSetBoundsImm cd, cs1, zimm12 *)
  Definition specCSetBounds (cs1 cs2 : ty FullECapWithTag) (isImm isExact isRoundDown : ty Bool)
                          (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    LetE base : Addr <- ##cs1`"addr" ;
    LetE length : Addr <- ITE #isImm (specZimm12 inst) (##cs2`"addr") ;
    LetE reqTop : Addr <- Add [ #base ; #length ] ;
    LetE inBounds : Bool <-
      And [ ##cs1`"tag" ; And [ specUle (ZeroExtendTo (AddrSz + 2) #reqTop) (##ecap`"top") ;
                                Uge (ZeroExtendTo (AddrSz + 1) #base) (##ecap`"base") ] ] ;
    LETE bounds : BoundsRes <- Bounds isRoundDown base length ;
    LetE boundsExact : Bool <- ##bounds`"exact" ;
    LETE tag : Bool <- BoundsTag isExact inBounds boundsExact ;
    specOut (specCapResult #tag
             (STRUCT { "R"      ::= ##ecap`"R" ;
                       "perms"  ::= ##ecap`"perms" ;
                       "cOType" ::= ##ecap`"cOType" ;
                       "cE"     ::= ##bounds`"cE" ;
                       "top"    ::= ##bounds`"top" ;
                       "base"   ::= ##bounds`"base" })
             #base)
      specOpNormal.

  (* CSeal cd, cs1, cs2 (isUnseal = false) and CUnseal cd, cs1, cs2 (isUnseal = true):
     the otype (cs2.addr for CSeal, cs1's otype for CUnseal) must be in cs2's bounds *)
  Definition specSealUnseal (cs1 cs2 : ty FullECapWithTag) (isUnseal : ty Bool) : LetExpr ty SpecInstOut :=
    LetE ecap1 : ECap <- ##cs1`"ecap" ;
    LetE ecap2 : ECap <- ##cs2`"ecap" ;
    LetE tag1 : Bool <- ##cs1`"tag" ;
    LetE otype1 : Bit CapOTypeSz <- getFullOType ecap1 ;
    LetE otype2 : Addr <- ##cs2`"addr" ;
    LetE otypeTop : Bit (AddrSz + 2) <-
      ITE #isUnseal (ZeroExtendTo (inSz := CapOTypeSz) (AddrSz + 2) #otype1)
          (ZeroExtendTo (inSz := AddrSz) (AddrSz + 2) #otype2) ;
    LetE otypeBase : Bit (AddrSz + 1) <-
      ITE #isUnseal (ZeroExtendTo (inSz := CapOTypeSz) (AddrSz + 1) #otype1)
          (ZeroExtendTo (inSz := AddrSz) (AddrSz + 1) #otype2) ;
    LetE inBounds : Bool <-
      And [ #tag1 ; And [ Ult #otypeTop (##ecap2`"top") ; Uge #otypeBase (##ecap2`"base") ] ] ;
    LETE res : TagECap <- SealerUnsealer isUnseal inBounds tag1 ecap1 cs2 ;
    specOut (specCapResult (##res`"tag") (##res`"ecap") (##cs1`"addr")) specOpNormal.

  (* Loads: LB, LH, LW, LBU, LHU, LC rd, simm12(cs1) *)
  Definition specLoad (cs1 : ty FullECapWithTag) (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    LetE perms : CapPerms <- ##ecap`"perms" ;
    LetE tag : Bool <- ##cs1`"tag" ;
    LetE addr : Addr <- Add [ ##cs1`"addr" ; specSimm12 inst ] ;
    LetE memSize : Bit LgLgNumBytesFullCapSz <- getMemSize inst ;
    LETE inBounds : Bool <- specAccessInBounds cs1 addr memSize ;
    LetE isStore : Bool <- Const ty Bool false ;
    LetE cs1Idx : Bit RegIdxSz <- getCs1 inst ;
    LETE exc : Option ExceptionInfo <- MemException isStore tag ecap cs1Idx inBounds addr memSize ;
    LetE loadOp : LoadOp <- STRUCT { "isUnsigned" ::= FromBit Bool (##inst`[14:14]) ;
                                     "isLM"       ::= ##perms`"LM" ;
                                     "isLG"       ::= ##perms`"LG" } ;
    LetE payload : MemPayload <- STRUCT { "memSize" ::= #memSize ;
                                          "memOp"   ::= UNION (LoadOrStoreType, "Load" ::= #loadOp) } ;
    specOut (specIntResult #addr)
      (ITE (##exc`"valid") (specOpExc (##exc`"data"))
                           (specOpDataMem (UNION (MemFenceType, "Mem" ::= #payload)))).

  (* Stores: SB, SH, SW, SC rs2, store_imm(cs1) *)
  Definition specStore (cs1 cs2 : ty FullECapWithTag) (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    LetE perms : CapPerms <- ##ecap`"perms" ;
    LetE ecap2 : ECap <- ##cs2`"ecap" ;
    LetE perms2 : CapPerms <- ##ecap2`"perms" ;
    LetE tag : Bool <- ##cs1`"tag" ;
    LetE addr : Addr <- Add [ ##cs1`"addr" ; specStoreImm inst ] ;
    LetE memSize : Bit LgLgNumBytesFullCapSz <- getMemSize inst ;
    LETE inBounds : Bool <- specAccessInBounds cs1 addr memSize ;
    LetE isStore : Bool <- Const ty Bool true ;
    LetE cs1Idx : Bit RegIdxSz <- getCs1 inst ;
    LETE exc : Option ExceptionInfo <- MemException isStore tag ecap cs1Idx inBounds addr memSize ;
    LETE cap : Cap <- EncodeCap ecap2 ;
    LetE storeVal : FullCapWithTag <-
      STRUCT { "tag"  ::= And [ ##cs2`"tag" ; Or [ ##perms`"SL" ; ##perms2`"GL" ] ] ;
               "cap"  ::= #cap ;
               "addr" ::= ##cs2`"addr" } ;
    LetE payload : MemPayload <- STRUCT { "memSize" ::= #memSize ;
                                          "memOp"   ::= UNION (LoadOrStoreType, "Store" ::= #storeVal) } ;
    specOut (specIntResult #addr)
      (ITE (##exc`"valid") (specOpExc (##exc`"data"))
                           (specOpDataMem (UNION (MemFenceType, "Mem" ::= #payload)))).

  (* MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU rd, rs1, rs2: deferred to the MulDiv unit,
     which takes rs1 from dstValue.addr *)
  Definition specMulDiv (cs1 cs2 : ty FullECapWithTag) (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE isMulDiv : Bool <- Const ty Bool true ;
    LetE op2 : Addr <- ##cs2`"addr" ;
    LETE md : Option MulDivUnion <- MulDiv isMulDiv inst op2 ;
    specOut (specIntResult (##cs1`"addr")) (specOpMulDiv (##md`"data")).

  (* ADD, SUB, ADDI rd, rs1, rs2/simm12 and CSub rd, cs1, cs2 *)
  Definition specAddSub (cs1 cs2 : ty FullECapWithTag) (isImm isSub : ty Bool) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE a : Bit Xlen <- ##cs1`"addr" ;
    LetE b : Bit Xlen <- ITE #isImm (specSimm12 inst) (##cs2`"addr") ;
    specOut (specIntResult (ITE #isSub (Sub #a #b) (Add [ #a ; #b ]))) specOpNormal.

  (* CGetLen rd, cs1: top - base, saturated *)
  Definition specCGetLen (cs1 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    LetE base : Bit (AddrSz + 1) <- ##ecap`"base" ;
    LetE top : Bit (AddrSz + 2) <- ##ecap`"top" ;
    LetE len : Bit AddrSz <- Sub (TruncLsb 2 AddrSz #top) (TruncLsb 1 AddrSz #base) ;
    LetE isBase : Bool <- Const ty Bool false ;
    LetE isTop : Bool <- Const ty Bool false ;
    LetE isLen : Bool <- Const ty Bool true ;
    LETE res : Bit Xlen <- Saturater isBase isTop isLen base top len ;
    specOut (specIntResult #res) specOpNormal.

  (* CGetBase rd, cs1 (isBase) and CGetTop rd, cs1 (isTop): saturated *)
  Definition specCGetBaseTop (cs1 : ty FullECapWithTag) (isBase isTop : ty Bool) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    LetE base : Bit (AddrSz + 1) <- ##ecap`"base" ;
    LetE top : Bit (AddrSz + 2) <- ##ecap`"top" ;
    LetE unused : Bit AddrSz <- $0 ;
    LetE isLen : Bool <- Const ty Bool false ;
    LETE res : Bit Xlen <- Saturater isBase isTop isLen base top unused ;
    specOut (specIntResult #res) specOpNormal.

  (* SLT, SLTU, SLTI, SLTIU rd, rs1, rs2/simm12 *)
  Definition specSlt (cs1 cs2 : ty FullECapWithTag) (isImm : ty Bool) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE funct3 : Bit 3 <- ##inst`[14:12] ;
    LetE isUnsigned : Bool <- FromBit Bool (#funct3`[0:0]) ;
    LetE a : Bit Xlen <- ##cs1`"addr" ;
    LetE b : Bit Xlen <- ITE #isImm (specSimm12 inst) (##cs2`"addr") ;
    LETE lt : Bool <- specLessThan isUnsigned a b ;
    specOut (specIntResult (ZeroExtendTo Xlen (ToBit #lt))) specOpNormal.

  (* CSetEqual rd, cs1, cs2 *)
  Definition specCSetEqual (cs1 cs2 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    LetE addrEq : Bool <- Eq (##cs1`"addr") (##cs2`"addr") ;
    LetE tag1 : Bool <- ##cs1`"tag" ;
    LetE tag2 : Bool <- ##cs2`"tag" ;
    LetE ecap1 : ECap <- ##cs1`"ecap" ;
    LetE ecap2 : ECap <- ##cs2`"ecap" ;
    LETE eq : Bool <- CapEq addrEq tag1 tag2 ecap1 ecap2 ;
    specOut (specIntResult (ZeroExtendTo Xlen (ToBit #eq))) specOpNormal.

  (* SLL, SRL, SRA rd, rs1, rs2 and SLLI, SRLI, SRAI rd, rs1, shamt *)
  Definition specShift (cs1 cs2 : ty FullECapWithTag) (isImm : ty Bool) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE data : Bit Xlen <- ##cs1`"addr" ;
    LetE shamt : Bit RegIdxSz <-
      ITE #isImm (##inst`[24:20]) (TruncLsb (AddrSz - RegIdxSz) RegIdxSz (##cs2`"addr")) ;
    LETE res : Bit Xlen <- Shifter inst data shamt ;
    specOut (specIntResult #res) specOpNormal.

  (* AND, OR, XOR rd, rs1, rs2 and ANDI, ORI, XORI rd, rs1, simm12 *)
  Definition specLogical (cs1 cs2 : ty FullECapWithTag) (isImm : ty Bool) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE a : Bit Xlen <- ##cs1`"addr" ;
    LetE b : Bit Xlen <- ITE #isImm (specSimm12 inst) (##cs2`"addr") ;
    LETE res : Bit Xlen <- Logical inst a b ;
    specOut (specIntResult #res) specOpNormal.

  (* CRAM rd, rs1 (isCram) and CRRL rd, rs1 *)
  Definition specCramCrrl (cs1 : ty FullECapWithTag) (isCram : bool) : LetExpr ty SpecInstOut :=
    LetE roundDown : Bool <- Const ty Bool false ;
    LetE len : Addr <- ##cs1`"addr" ;
    LETE bounds : BoundsRes <- Bounds roundDown len len ;
    specOut (specIntResult (if isCram then TruncLsb 1 AddrSz (##bounds`"cram")
                        else TruncLsb 1 AddrSz (##bounds`"length")))
      specOpNormal.

  (* CAndPerm cd, cs1, rs2 *)
  Definition specCAndPerm (cs1 cs2 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    LetE tag : Bool <- ##cs1`"tag" ;
    LetE ecap : ECap <- ##cs1`"ecap" ;
    LetE mask : Addr <- ##cs2`"addr" ;
    LETE res : TagECap <- CAndPerm tag ecap mask ;
    specOut (specCapResult (##res`"tag") (##res`"ecap") (##cs1`"addr")) specOpNormal.

  (* CSR access: CSRRW, CSRRS, CSRRC rd, csr, rs1 and CSRRWI, CSRRSI, CSRRCI rd, csr, zimm5 *)
  Definition specCsr (cs1 : ty FullECapWithTag) (csrIdx : ty (Bit CsrIdxSz)) (isImm : ty Bool)
                   (inst : ty Inst) : LetExpr ty SpecInstOut :=
    LetE tag : Bool <- ##cs1`"tag" ;
    LetE addr : Addr <- ##cs1`"addr" ;
    LETE dcTag : Bool <- ScrSanitizer tag addr inst ; (* don't care: SpecialValue.tag *)
    LetE funct2 : Bit 2 <- ##inst`[13:12] ;
    specOut (specNoResult inst)
      (specOpScrCsr (STRUCT {
         "SpecialDest"  ::= UNION (ScrCsrIdx, "Csr" ::= #csrIdx) ;
         "SpecialValue" ::= specCapResult #dcTag (##cs1`"ecap") (* don't care: ecap *)
                              (ITE #isImm (ZeroExtendTo Xlen (##inst`[19:15])) #addr) ;
         "isSet"        ::= Eq #funct2 $2 ;
         "isClear"      ::= Eq #funct2 $3 ;
         "isWrite"      ::= Or [ Eq #funct2 $1 ; isNotZero (getCs1 inst) ] })).

  (* CSpecialRw cd, scr, cs1. MePcc and Mtcc hold instruction addresses, which are always even:
     the written address has its LSB cleared and the tag is cleared if that bit was set. *)
  Definition specScr (cs1 : ty FullECapWithTag) (scrIdx : ty (Bit ScrIdxSz)) (inst : ty Inst)
    : LetExpr ty SpecInstOut :=
    LetE tag : Bool <- ##cs1`"tag" ;
    LetE addr : Addr <- ##cs1`"addr" ;
    LETE newTag : Bool <- ScrSanitizer tag addr inst ;
    LetE scrAddr : Bit ScrAddrSz <- getScr inst ;
    LetE isSpecialPcc : Bool <- Or [ Eq #scrAddr $(getScrAddr "MePcc"%string) ;
                                     Eq #scrAddr $(getScrAddr "Mtcc"%string) ] ;
    LetE funct2 : Bit 2 <- ##inst`[13:12] ;
    specOut (specNoResult inst)
      (specOpScrCsr (STRUCT {
         "SpecialDest"  ::= UNION (ScrCsrIdx, "Scr" ::= #scrIdx) ;
         "SpecialValue" ::= specCapResult #newTag (##cs1`"ecap")
                              (ITE #isSpecialPcc
                                 {< TruncMsb (AddrSz - 1) 1 #addr, Const ty (Bit 1) Zmod.zero >} #addr) ;
         "isSet"        ::= Eq #funct2 $2 ;
         "isClear"      ::= Eq #funct2 $3 ;
         "isWrite"      ::= Or [ Eq #funct2 $1 ; isNotZero (getCs1 inst) ] })).

  (* Capability field reads: CGetPerm, CGetType, CGetTag, CGetAddr, CGetHigh rd, cs1 *)
  Definition specCGetPerm (cs1 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    specOut (specIntResult (ZeroExtendTo Xlen (ToBit (##ecap`"perms")))) specOpNormal.

  Definition specCGetType (cs1 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    specOut (specIntResult (ZeroExtendTo Xlen (getFullOType ecap))) specOpNormal.

  Definition specCGetTag (cs1 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    specOut (specIntResult (ZeroExtendTo Xlen (ToBit (##cs1`"tag")))) specOpNormal.

  Definition specCGetAddr (cs1 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    specOut (specIntResult (##cs1`"addr")) specOpNormal.

  Definition specCGetHigh (cs1 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    LetE ecap : ECap <- ##cs1`"ecap" ;
    LETE cap : Cap <- EncodeCap ecap ;
    specOut (specIntResult (ZeroExtendTo Xlen (ToBit #cap))) specOpNormal.

  (* CSetHigh cd, cs1, rs2: decode rs2 as the metadata of a capability with address cs1.addr *)
  Definition specCSetHigh (cs1 cs2 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    LetE cap : Cap <- FromBit Cap (##cs2`"addr") ;
    LetE addr : Addr <- ##cs1`"addr" ;
    LETE ecap : ECap <- DecodeCap cap addr ;
    specOut (specCapResult (Const ty Bool false) #ecap #addr) specOpNormal.

  (* CClearTag cd, cs1 and CMove cd, cs1 *)
  Definition specCClearTag (cs1 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    specOut (specCapResult (Const ty Bool false) (##cs1`"ecap") (##cs1`"addr")) specOpNormal.

  Definition specCMove (cs1 : ty FullECapWithTag) : LetExpr ty SpecInstOut :=
    specOut (specCapResult (##cs1`"tag") (##cs1`"ecap") (##cs1`"addr")) specOpNormal.

  (* ECALL and EBREAK *)
  Definition specECall (inst : ty Inst) : LetExpr ty SpecInstOut :=
    specOut (specNoResult inst)
      (specOpExc (mkExceptionInfo $EXC_ECallM (mkCheriMtval (Const ty Bool false) $0 $0))).

  Definition specEBreak (inst : ty Inst) : LetExpr ty SpecInstOut :=
    specOut (specNoResult inst)
      (specOpExc (mkExceptionInfo $EXC_Breakpoint (mkCheriMtval (Const ty Bool false) $0 $0))).

  (* FENCE, FENCE.TSO and FENCE.I *)
  Definition specFence (inst : ty Inst) : LetExpr ty SpecInstOut :=
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
    specOut (specNoResult inst) (specOpDataMem (UNION (MemFenceType, "Fence" ::= #fence))).

  (* No class bit: the decoder flags the instruction as illegal *)
  Definition specNone (inst : ty Inst) : LetExpr ty SpecInstOut :=
    specOut (specNoResult inst) specOpNormal.

  (* ---------------------------------------------------------------------------
   * Dispatch
   * --------------------------------------------------------------------------- *)

  (* if p1 then t1 else if p2 then t2 ... else def *)
  Fixpoint specCases k (cases : list (Expr ty Bool * LetExpr ty k)) (def : LetExpr ty k) : LetExpr ty k :=
    match cases with
    | nil => def
    | (p, t) :: rest => IfElseE "" p t (specCases rest def) (fun x => RetE (Var ty k x))
    end.

  Definition specAlu (pcc : ty FullECapWithTag) (pkg : ty AluInInstGroup) : LetExpr ty AluOutUnion :=
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
        (##g`"Branch"      , specBranch pcc cs1 cs2 inst) ;
        (##g`"Cjal"        , specCjal pcc cs1 isComp inst) ;
        (##g`"Cjalr"       , specCjalr pcc cs1 isComp inst) ;
        (##g`"Mret"        , specMret pcc cs1 inst) ;
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
        (##g`"Csr"         , specCsr cs1 csrIdx isImm inst) ;
        (##g`"Scr"         , specScr cs1 scrIdx inst) ;
        (##g`"CGetPerm"    , specCGetPerm cs1) ;
        (##g`"CGetType"    , specCGetType cs1) ;
        (##g`"CGetTag"     , specCGetTag cs1) ;
        (##g`"CGetAddr"    , specCGetAddr cs1) ;
        (##g`"CGetHigh"    , specCGetHigh cs1) ;
        (##g`"CSetHigh"    , specCSetHigh cs1 cs2) ;
        (##g`"CClearTag"   , specCClearTag cs1) ;
        (##g`"CMove"       , specCMove cs1) ;
        (##g`"ECall"       , specECall inst) ;
        (##g`"EBreak"      , specEBreak inst) ;
        (##g`"Fence"       , specFence inst)
      ] (specNone inst) ;
    @RetE _ AluOutUnion (STRUCT {
      "isComp"   ::= #isComp ;
      "dstIdx"   ::= ITE0 (##pkg`"writesCd")
                       (TruncLsb (RegIdxSz - RegIdxSzReal) RegIdxSzReal (getCd inst)) ;
      "dstValue" ::= ##out`"dstValue" ;
      "Op"       ::= ITE (##fdExc`"valid") (specOpExc (##fdExc`"data")) (##out`"op")
    }).
End Alu.
