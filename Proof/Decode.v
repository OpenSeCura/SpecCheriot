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
 * The decoder only produces well-formed instruction groups
 * ===========================================================================
 * Main result:
 *   - [spec_decode_wellformed]  the [instGroup] of [decodeUncompressed inst hasAsr] is
 *                             [specGroup inst c isImm isExact isRoundDown isSub] for some class [c].
 *
 * Method: evaluate the decoder group once (cbn), abstract the instruction fields (opcode,
 * funct3, funct7, rs2, rs1, rd, csrAddr, fm) and the CSR/SCR decoder validity bits, turn every
 * field comparison into [Z.eqb field K], and abstract each such comparison as a boolean, keeping
 * for each field the fact that at most one of its comparisons holds ([amo]). The case analysis
 * then runs over these booleans on a small goal: opcode first, then funct3 (enumerated), then the
 * other fields only where they still occur. At each leaf the class is read off the group
 * ([specPick]) and both sides are computed. *)

From Stdlib Require Import String List ZArith Zmod Lia Bool Btauto.
From Guru Require Import Primitives Library Syntax Combinators Notations Semantics.
From Cheriot Require Import SpecDefines Decoder.
From SpecCheriot Require Import Group.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope guru_scope.

(* ---------------------------------------------------------------------------
 * specGroup with its instruction-dependent parts (isCompressed, funct3) as arguments
 * --------------------------------------------------------------------------- *)

Section SpecGroupF.
  Variable comp : type Bool.
  Variable f3 : type (Bit 3).
  Variable c : SpecClass.
  Variable isImm isExact isRoundDown isSub : bool.

  Local Abbreviation cls x := (Const type Bool (SpecClass_beq x c)).
  Local Abbreviation clsAnd x b := (Const type Bool (andb (SpecClass_beq x c) b)).

  Definition specGroupF : type InstGroup := evalExpr (
    STRUCT {
      "isCompressed"                 ::= Const type Bool comp ;
      "isImm"                        ::= Const type Bool isImm ;
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
        | cBranch => FromBit Bool ((#f3)`[1:1])
        | cSlt    => FromBit Bool ((#f3)`[0:0])
        | _       => ConstBool false
        end ;
      "ComparatorGeneral_checkLt"    ::=
        match c with
        | cBranch => FromBit Bool ((#f3)`[2:2])
        | cSlt    => ConstBool true
        | _       => ConstBool false
        end ;
      "ComparatorGeneral_checkEq"    ::=
        match c with
        | cBranch    => Not (FromBit Bool ((#f3)`[2:2]))
        | cCSetEqual => ConstBool true
        | _          => ConstBool false
        end ;
      "ComparatorGeneral_invertRes"  ::=
        match c with
        | cBranch => FromBit Bool ((#f3)`[0:0])
        | _       => ConstBool false
        end
    }).
End SpecGroupF.

Lemma dec_specGroup_F (inst : type Inst) c isImm isExact isRoundDown isSub :
  specGroup inst c isImm isExact isRoundDown isSub =
  specGroupF (evalExpr (isCompressed inst)) (evalExpr (#inst`[14:12])) c isImm isExact isRoundDown isSub.
Proof. destruct c; reflexivity. Qed.

(* ---------------------------------------------------------------------------
 * Reading the class and the side flags off a group
 * --------------------------------------------------------------------------- *)

Definition specClasses : list SpecClass :=
  [ cBranch; cCjal; cAuiPcc; cAuiCgp; cCIncAddr; cCSetAddr; cCjalr; cCTestSubset; cCSetBounds; cSeal; cUnseal; cLoad; cStore; cMulDiv; cAddSub; cCGetLen; cSlt; cCSetEqual; cShift; cLogical; cCram; cCrrl; cCAndPerm; cCsr; cScr; cLui; cCGetPerm; cCGetType; cCGetBase; cCGetTag; cCGetAddr; cCGetHigh; cCGetTop; cCSetHigh; cCClearTag; cCMove; cECall; cEBreak; cMret; cFence ].

Definition specClassBits (g : type InstGroup) : list bool :=
  [ evalExpr (##g`"Branch");
    evalExpr (##g`"Cjal");
    evalExpr (##g`"AuiPcc");
    evalExpr (##g`"AuiCgp");
    evalExpr (##g`"CIncAddr");
    evalExpr (##g`"CSetAddr");
    evalExpr (##g`"Cjalr");
    evalExpr (##g`"CTestSubset");
    evalExpr (##g`"CSetBounds");
    evalExpr (##g`"Seal");
    evalExpr (##g`"Unseal");
    evalExpr (##g`"Load");
    evalExpr (##g`"Store");
    evalExpr (##g`"MulDiv");
    evalExpr (##g`"AddSub");
    evalExpr (##g`"CGetLen");
    evalExpr (##g`"Slt");
    evalExpr (##g`"CSetEqual");
    evalExpr (##g`"Shift");
    evalExpr (##g`"Logical");
    evalExpr (##g`"Cram");
    evalExpr (##g`"Crrl");
    evalExpr (##g`"CAndPerm");
    evalExpr (##g`"Csr");
    evalExpr (##g`"Scr");
    evalExpr (##g`"Lui");
    evalExpr (##g`"CGetPerm");
    evalExpr (##g`"CGetType");
    evalExpr (##g`"CGetBase");
    evalExpr (##g`"CGetTag");
    evalExpr (##g`"CGetAddr");
    evalExpr (##g`"CGetHigh");
    evalExpr (##g`"CGetTop");
    evalExpr (##g`"CSetHigh");
    evalExpr (##g`"CClearTag");
    evalExpr (##g`"CMove");
    evalExpr (##g`"ECall");
    evalExpr (##g`"EBreak");
    evalExpr (##g`"Mret");
    evalExpr (##g`"Fence") ].

(* The first class whose bit is set *)
Fixpoint specPickL (bs : list bool) (cs : list SpecClass) : SpecClass :=
  match bs, cs with
  | b :: bs', c :: cs' => if b then c else specPickL bs' cs'
  | _, _ => cNone
  end.

Definition specPick (g : type InstGroup) : SpecClass := specPickL (specClassBits g) specClasses.

Definition specImm (g : type InstGroup) : bool := evalExpr (##g`"isImm").
Definition specExact (g : type InstGroup) : bool := evalExpr (##g`"CSetBounds_isExact").
Definition specRoundDown (g : type InstGroup) : bool := evalExpr (##g`"CSetBounds_isRoundDown").
Definition specSub (g : type InstGroup) : bool := evalExpr (##g`"AddSub_isSub").

(* ---------------------------------------------------------------------------
 * At most one comparison of a field against distinct constants holds
 * --------------------------------------------------------------------------- *)

Lemma dec_bits3_cases (x : bits 3) :
  x = Zmod.of_Z (2^3) 0 \/ x = Zmod.of_Z (2^3) 1 \/ x = Zmod.of_Z (2^3) 2 \/ x = Zmod.of_Z (2^3) 3 \/
  x = Zmod.of_Z (2^3) 4 \/ x = Zmod.of_Z (2^3) 5 \/ x = Zmod.of_Z (2^3) 6 \/ x = Zmod.of_Z (2^3) 7.
Proof.
  pose proof (Zmod.unsigned_pos_bound x ltac:(lia)) as H.
  remember (Zmod.unsigned x) as u eqn:Hu.
  assert (E : 2^3 = 8) by reflexivity. rewrite E in H.
  assert (u = 0 \/ u = 1 \/ u = 2 \/ u = 3 \/ u = 4 \/ u = 5 \/ u = 6 \/ u = 7) as Hc by lia.
  repeat destruct Hc as [Hc | Hc];
    repeat first [ left; apply Zmod.unsigned_inj; rewrite <- Hu, Hc; reflexivity | right ];
    apply Zmod.unsigned_inj; rewrite <- Hu, Hc; reflexivity.
Qed.


(* ---------------------------------------------------------------------------
 * Tactics
 * --------------------------------------------------------------------------- *)

Ltac dec_has_var K := match K with context [?x] => is_var x end.

(* Replace every closed [Zmod.unsigned K] by its value. *)
Ltac dec_closed_toZ :=
  repeat match goal with
  | |- context [Zmod.unsigned ?K] =>
      tryif dec_has_var K then fail else
      let v := eval vm_compute in (Zmod.unsigned K) in
      change (Zmod.unsigned K) with v
  end.

(* Give every [Zmod.unsigned X] the modulus of the type of [X]. *)
Ltac dec_norm_mod X :=
  let T := type of X in
  lazymatch eval hnf in T with
  | Zmod ?m0 =>
      repeat match goal with
      | |- context [@Zmod.unsigned ?m X] =>
          tryif constr_eq m m0 then fail else change (@Zmod.unsigned m X) with (@Zmod.unsigned m0 X)
      end
  end.

Tactic Notation "dec_gen_slice" constr(n) constr(k) ident(nm) :=
  match goal with
  | |- context [@Zmod_lastn n ?w (@Zmod.firstn (k + n) ?w2 ?i)] =>
      generalize (@Zmod_lastn n w (@Zmod.firstn (k + n) w2 i)) as nm; intros nm
  end.

Ltac dec_simp := cbn [andb orb negb Z.eqb Pos.eqb].

Tactic Notation "dec_gen_int" ident(X) ident(x) :=
  dec_norm_mod X; generalize (Zmod.unsigned X) as x; intros x; clear X.

Ltac dec_f3_eval :=
  repeat match goal with
  | |- context [Zmod.unsigned (@Zmod_lastn ?n ?w (@Zmod.firstn ?k ?w2 (Zmod.of_Z ?m ?j)))] =>
      let t := constr:(Zmod.unsigned (@Zmod_lastn n w (@Zmod.firstn k w2 (Zmod.of_Z m j)))) in
      let v := eval vm_compute in t in change t with v
  | |- context [@Zmod.unsigned ?m (Zmod.of_Z ?m2 ?j)] =>
      let t := constr:(@Zmod.unsigned m (Zmod.of_Z m2 j)) in
      let v := eval vm_compute in t in change t with v
  end;
  cbn [Z.eqb Pos.eqb].

(* ---------------------------------------------------------------------------
 * The first set bit of a pairwise exclusive list
 * --------------------------------------------------------------------------- *)

Fixpoint pairwise (bs : list bool) : bool :=
  match bs with
  | [] => true
  | b :: r => andb (forallb (fun x => negb (andb b x)) r) (pairwise r)
  end.

Lemma spec_beq_refl : forall x, SpecClass_beq x x = true.
Proof. intros x. apply internal_SpecClass_dec_lb. reflexivity. Qed.

Lemma spec_beq_false : forall x y, x <> y -> SpecClass_beq x y = false.
Proof.
  intros x y Hne. destruct (SpecClass_beq x y) eqn:E; [| reflexivity].
  apply internal_SpecClass_dec_bl in E. contradiction.
Qed.

Lemma specPickL_in : forall bs cs, specPickL bs cs = cNone \/ In (specPickL bs cs) cs.
Proof.
  induction bs as [| b bs IH]; intros [| c cs]; cbn [specPickL]; auto.
  destruct b; [right; left; reflexivity |]. destruct (IH cs) as [H | H]; auto. right; right; exact H.
Qed.

Lemma specPickL_beq : forall bs cs,
  NoDup cs -> ~ In cNone cs -> length bs = length cs -> pairwise bs = true ->
  forall i, (i < length cs)%nat -> nth i bs false = SpecClass_beq (nth i cs cNone) (specPickL bs cs).
Proof.
  induction bs as [| b bs IH]; intros [| c cs] Hnd Hnn Hlen Hpw i Hi; cbn [length] in *; try lia.
  inversion Hnd as [| c' cs' Hnin Hnd']; subst.
  cbn [pairwise] in Hpw. apply andb_true_iff in Hpw as [Hall Hpw].
  assert (Hc : c <> cNone) by (intros ->; apply Hnn; left; reflexivity).
  assert (Hnn' : ~ In cNone cs) by (intros H; apply Hnn; right; exact H).
  destruct i as [| j]; cbn [nth specPickL].
  - destruct b; [symmetry; apply spec_beq_refl |].
    symmetry; apply spec_beq_false. intros Heq.
    destruct (specPickL_in bs cs) as [H | H]; rewrite <- Heq in H; [exact (Hc H) | exact (Hnin H)].
  - destruct b.
    + rewrite forallb_forall in Hall.
      assert (Hj : (j < length bs)%nat) by lia.
      specialize (Hall (nth j bs false) (nth_In _ _ Hj)). cbn [andb negb] in Hall.
      destruct (nth j bs false); [discriminate Hall |].
      symmetry; apply spec_beq_false. intros Heq. apply Hnin. rewrite <- Heq. apply nth_In. lia.
    + apply IH; auto; lia.
Qed.

Lemma specPick_beq : forall g, pairwise (specClassBits g) = true ->
  forall i, (i < 40)%nat -> nth i (specClassBits g) false = SpecClass_beq (nth i specClasses cNone) (specPick g).
Proof.
  intros g Hpw i Hi. apply specPickL_beq; [| | reflexivity | exact Hpw | exact Hi].
  - unfold specClasses. repeat constructor; cbn [In]; intuition discriminate.
  - unfold specClasses. cbn [In]. intuition discriminate.
Qed.

(* ---------------------------------------------------------------------------
 * Tactics on small boolean goals
 * --------------------------------------------------------------------------- *)

Ltac dec_in_goal b := lazymatch goal with |- context [b] => idtac end.

Lemma spec_prod_eq : forall (A B : Type) (a c : A) (b d : B), a = c -> b = d -> (a ,, b) = (c ,, d).
Proof. intros; subst; reflexivity. Qed.

(* ---------------------------------------------------------------------------
 * Case split on which class bit is set
 * --------------------------------------------------------------------------- *)

(* Turn [Z.eqb (unsigned F3) k = true] into [F3 = of_Z k] and substitute it. *)
Lemma dec_f3_of_eqb : forall (x : bits 3) k, (Zmod.unsigned x =? k)%Z = true -> x = Zmod.of_Z (2^3) k.
Proof.
  intros x k H. apply Z.eqb_eq in H. rewrite <- H. symmetry. apply Zmod.of_Z_unsigned.
Qed.

(* Evaluate closed bit-slice comparisons in hypotheses; discard contradictions. *)
Ltac dec_hyps_eval :=
  repeat match goal with
  | H : context [Zmod.unsigned (@Zmod_lastn ?n ?w (@Zmod.firstn ?k ?w2 (Zmod.of_Z ?m ?j)))] |- _ =>
      let t := constr:(Zmod.unsigned (@Zmod_lastn n w (@Zmod.firstn k w2 (Zmod.of_Z m j)))) in
      let v := eval vm_compute in t in change t with v in H
  | H : context [@Zmod.unsigned ?m (Zmod.of_Z ?m2 ?j)] |- _ =>
      let t := constr:(@Zmod.unsigned m (Zmod.of_Z m2 j)) in
      let v := eval vm_compute in t in change t with v in H
  end;
  repeat match goal with
  | H : _ = _ |- _ => progress cbn [andb orb negb Z.eqb Pos.eqb] in H
  end;
  try discriminate.

(* Decompose a true formula into atomic facts and use them. *)
Ltac dec_use_true E :=
  lazymatch type of E with
  | andb _ _ = true =>
      let E1 := fresh "E" in let E2 := fresh "E" in
      apply andb_true_iff in E; destruct E as [E1 E2]; dec_use_true E1; dec_use_true E2
  | orb _ _ = true =>
      apply orb_true_iff in E; destruct E as [E | E]; dec_use_true E
  | negb ?x = true => apply negb_true_iff in E; dec_use_false E
  | (Zmod.unsigned ?F =? _)%Z = true =>
      tryif is_var F then (apply dec_f3_of_eqb in E; subst F; dec_f3_eval; dec_hyps_eval)
      else (try rewrite E)
  | (?x =? _)%Z = true =>
      tryif is_var x then (apply Z.eqb_eq in E; subst x) else (try rewrite E)
  | ?b = true => tryif is_var b then subst b else (try rewrite E)
  | _ => idtac
  end
with dec_use_false E :=
  lazymatch type of E with
  | orb _ _ = false =>
      let E1 := fresh "E" in let E2 := fresh "E" in
      apply orb_false_iff in E; destruct E as [E1 E2]; dec_use_false E1; dec_use_false E2
  | negb ?x = false => apply negb_false_iff in E; dec_use_true E
  | ?b = false => tryif is_var b then subst b else (try rewrite E)
  | _ => idtac
  end.

(* ---------------------------------------------------------------------------
 * Pairwise exclusivity of two class bits, on a small goal
 * --------------------------------------------------------------------------- *)

Ltac dec_contra F3 :=
  dec_hyps_eval;
  first [ discriminate
        | lazymatch goal with H : context [F3] |- _ => idtac end;
          destruct (dec_bits3_cases F3) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
          dec_f3_eval; dec_hyps_eval ].

Ltac dec_pair F3 :=
  dec_simp; try reflexivity;
  lazymatch goal with
  | |- negb (andb ?x _) = true =>
      let E1 := fresh "E" in
      destruct x eqn:E1; [ | reflexivity ];
      dec_use_true E1; dec_simp; try reflexivity;
      lazymatch goal with
      | |- negb ?y = true =>
          let E2 := fresh "E" in
          destruct y eqn:E2; [ | reflexivity ];
          dec_use_true E2; dec_simp; dec_contra F3
      end
  end.

Ltac dec_btauto := match goal with |- ?a = ?b => change (@eq bool a b) end; btauto.

Ltac dec_idx X :=
  lazymatch X with
  | cBranch => constr:(0%nat)
  | cCjal => constr:(1%nat)
  | cAuiPcc => constr:(2%nat)
  | cAuiCgp => constr:(3%nat)
  | cCIncAddr => constr:(4%nat)
  | cCSetAddr => constr:(5%nat)
  | cCjalr => constr:(6%nat)
  | cCTestSubset => constr:(7%nat)
  | cCSetBounds => constr:(8%nat)
  | cSeal => constr:(9%nat)
  | cUnseal => constr:(10%nat)
  | cLoad => constr:(11%nat)
  | cStore => constr:(12%nat)
  | cMulDiv => constr:(13%nat)
  | cAddSub => constr:(14%nat)
  | cCGetLen => constr:(15%nat)
  | cSlt => constr:(16%nat)
  | cCSetEqual => constr:(17%nat)
  | cShift => constr:(18%nat)
  | cLogical => constr:(19%nat)
  | cCram => constr:(20%nat)
  | cCrrl => constr:(21%nat)
  | cCAndPerm => constr:(22%nat)
  | cCsr => constr:(23%nat)
  | cScr => constr:(24%nat)
  | cLui => constr:(25%nat)
  | cCGetPerm => constr:(26%nat)
  | cCGetType => constr:(27%nat)
  | cCGetBase => constr:(28%nat)
  | cCGetTag => constr:(29%nat)
  | cCGetAddr => constr:(30%nat)
  | cCGetHigh => constr:(31%nat)
  | cCGetTop => constr:(32%nat)
  | cCSetHigh => constr:(33%nat)
  | cCClearTag => constr:(34%nat)
  | cCMove => constr:(35%nat)
  | cECall => constr:(36%nat)
  | cEBreak => constr:(37%nat)
  | cMret => constr:(38%nat)
  | cFence => constr:(39%nat)
  end.

(* The class bit of class [X] is [SpecClass_beq X c]; replace the latter by the bit. *)
Ltac dec_use_hb Hb c :=
  repeat match goal with
  | |- context [SpecClass_beq ?X c] =>
      let i := dec_idx X in
      let Hi := fresh "Hi" in
      pose proof (Hb i ltac:(lia)) as Hi;
      cbn [nth specClassBits specClasses evalExpr readDiffTuple Fst Snd finNum] in Hi;
      rewrite <- Hi; clear Hi
  end.

(* [specGroupF] as a tuple *)
Lemma dec_specGroupF_eq : forall comp (f3 : type (Bit 3)) c isImm isExact isRoundDown isSub,
  specGroupF comp f3 c isImm isExact isRoundDown isSub =
  (comp,,
   (isImm,,
   (SpecClass_beq cBranch c,,
   (SpecClass_beq cCjal c,,
   (SpecClass_beq cAuiPcc c,,
   (SpecClass_beq cAuiCgp c,,
   (SpecClass_beq cCIncAddr c,,
   (SpecClass_beq cCSetAddr c,,
   (SpecClass_beq cCjalr c,,
   (SpecClass_beq cCTestSubset c,,
   (SpecClass_beq cCSetBounds c,,
   (andb (SpecClass_beq cCSetBounds c) isExact,,
   (andb (SpecClass_beq cCSetBounds c) isRoundDown,,
   (SpecClass_beq cSeal c,,
   (SpecClass_beq cUnseal c,,
   (SpecClass_beq cLoad c,,
   (SpecClass_beq cStore c,,
   (SpecClass_beq cMulDiv c,,
   (SpecClass_beq cAddSub c,,
   (andb (SpecClass_beq cAddSub c) isSub,,
   (SpecClass_beq cCGetLen c,,
   (SpecClass_beq cSlt c,,
   (SpecClass_beq cCSetEqual c,,
   (SpecClass_beq cShift c,,
   (SpecClass_beq cLogical c,,
   (SpecClass_beq cCram c,,
   (SpecClass_beq cCrrl c,,
   (SpecClass_beq cCAndPerm c,,
   (SpecClass_beq cCsr c,,
   (SpecClass_beq cScr c,,
   (SpecClass_beq cLui c,,
   (SpecClass_beq cCGetPerm c,,
   (SpecClass_beq cCGetType c,,
   (SpecClass_beq cCGetBase c,,
   (SpecClass_beq cCGetTag c,,
   (SpecClass_beq cCGetAddr c,,
   (SpecClass_beq cCGetHigh c,,
   (SpecClass_beq cCGetTop c,,
   (SpecClass_beq cCSetHigh c,,
   (SpecClass_beq cCClearTag c,,
   (SpecClass_beq cCMove c,,
   (SpecClass_beq cECall c,,
   (SpecClass_beq cEBreak c,,
   (SpecClass_beq cMret c,,
   (SpecClass_beq cFence c,,
   (evalExpr (match c with cBranch => FromBit Bool ((#f3)`[1:1]) | cSlt => FromBit Bool ((#f3)`[0:0]) | _ => ConstBool false end),,
   (evalExpr (match c with cBranch => FromBit Bool ((#f3)`[2:2]) | cSlt => ConstBool true | _ => ConstBool false end),,
   (evalExpr (match c with cBranch => Not (FromBit Bool ((#f3)`[2:2])) | cCSetEqual => ConstBool true | _ => ConstBool false end),,
   (evalExpr (match c with cBranch => FromBit Bool ((#f3)`[0:0]) | _ => ConstBool false end),,
   tt))))))))))))))))))))))))))))))))))))))))))))))))).
Proof. reflexivity. Qed.

(* The comparator controls of [specGroupF], as boolean combinations of class tests *)
Lemma dec_cg_u : forall (a b : Expr type Bool) c,
  evalExpr (match c with cBranch => a | cSlt => b | _ => ConstBool false end) =
  orb (andb (SpecClass_beq cBranch c) (evalExpr a)) (andb (SpecClass_beq cSlt c) (evalExpr b)).
Proof. intros a b c; destruct c; cbn; rewrite ?andb_false_r, ?orb_false_r; reflexivity. Qed.

Lemma dec_cg_lt : forall (a : Expr type Bool) c,
  evalExpr (match c with cBranch => a | cSlt => ConstBool true | _ => ConstBool false end) =
  orb (andb (SpecClass_beq cBranch c) (evalExpr a)) (SpecClass_beq cSlt c).
Proof. intros a c; destruct c; cbn; rewrite ?andb_false_r, ?orb_false_r; reflexivity. Qed.

Lemma dec_cg_eq : forall (a : Expr type Bool) c,
  evalExpr (match c with cBranch => Not a | cCSetEqual => ConstBool true | _ => ConstBool false end) =
  orb (andb (SpecClass_beq cBranch c) (negb (evalExpr a))) (SpecClass_beq cCSetEqual c).
Proof. intros a c; destruct c; cbn; rewrite ?andb_false_r, ?orb_false_r; reflexivity. Qed.

Lemma dec_cg_inv : forall (a : Expr type Bool) c,
  evalExpr (match c with cBranch => a | _ => ConstBool false end) =
  andb (SpecClass_beq cBranch c) (evalExpr a).
Proof. intros a c; destruct c; cbn; rewrite ?andb_false_r, ?orb_false_r; reflexivity. Qed.

(* ---------------------------------------------------------------------------
 * Main lemma
 * --------------------------------------------------------------------------- *)

Lemma dec_main (inst : type Inst) (hasAsr : type Bool) :
  let d := evalLetExpr (@decodeUncompressed type inst hasAsr) in
  exists c isImm isExact isRoundDown isSub,
    evalExpr (##d`"instGroup") =
    specGroupF (evalExpr (isCompressed inst)) (evalExpr (#inst`[14:12])) c isImm isExact isRoundDown isSub.
Proof.
  intros d. subst d. unfold decodeUncompressed.
  cbn [evalLetExpr evalExpr Fst Snd fst snd readDiffTuple mapDiffTuple fold_left map finNum
       evalAndBinary evalOrBinary evalBinary evalNot isZero isNotZero ConstExtract getDefault
       InvDefault KindCustomInd isEq evalFromBit getCs1 getCs2 getCd].
  match goal with |- context [evalExpr (isCompressed ?i)] =>
    generalize (evalExpr (isCompressed i)) as comp; intros comp end.
  match goal with |- context [Fst (Snd (evalExpr (csrAddrDecoder ?a)))] =>
    generalize (Fst (Snd (evalExpr (csrAddrDecoder a)))) as vCsr; intros vCsr end.
  match goal with |- context [Fst (Snd (evalExpr (scrAddrDecoder ?a)))] =>
    generalize (Fst (Snd (evalExpr (scrAddrDecoder a)))) as vScr; intros vScr end.
  match goal with |- context [isEq ?a (getDefault Inst)] =>
    generalize (isEq a (getDefault Inst)) as iz; intros iz end.
  dec_gen_slice 5 2 O. dec_gen_slice 3 12 F3. dec_gen_slice 7 25 F7. dec_gen_slice 5 20 RS2.
  dec_gen_slice 5 15 RS1. dec_gen_slice 5 7 RD. dec_gen_slice 12 20 CSR. dec_gen_slice 4 28 FM.
  clear inst hasAsr.
  unfold Zmod.eqb.
  dec_closed_toZ.
  dec_gen_int O o. dec_gen_int F7 f7. dec_gen_int RS2 rs2. dec_gen_int RS1 rs1.
  dec_gen_int RD rd. dec_gen_int CSR csr. dec_gen_int FM fm.
  dec_simp.
  match goal with |- exists _ _ _ _ _, ?L = _ =>
    assert (Hpw : pairwise (specClassBits L) = true);
    [ unfold specClassBits; cbn [evalExpr readDiffTuple Fst Snd finNum pairwise forallb];
      repeat (apply andb_true_iff; split); dec_pair F3
    | pose proof (specPick_beq L Hpw) as Hb;
      exists (specPick L), (specImm L), (specExact L), (specRoundDown L), (specSub L);
      set (c := specPick L) in *; clearbody c ]
  end.
  rewrite dec_specGroupF_eq.
  repeat apply spec_prod_eq; try reflexivity;
  unfold specExact, specRoundDown, specSub; cbn [evalExpr readDiffTuple Fst Snd finNum].
  all: rewrite ?dec_cg_u, ?dec_cg_lt, ?dec_cg_eq, ?dec_cg_inv; dec_use_hb Hb c;
    cbn [evalExpr Fst Snd fst snd evalNot ConstExtract getDefault InvDefault KindCustomInd isEq evalFromBit];
    unfold Zmod.eqb; dec_closed_toZ; first [ reflexivity | dec_btauto ].
Qed.

Theorem spec_decode_wellformed : forall (inst : type Inst) (hasAsr : type Bool),
  let d := evalLetExpr (@decodeUncompressed type inst hasAsr) in
  exists c isImm isExact isRoundDown isSub,
    evalExpr (##d`"instGroup") = specGroup inst c isImm isExact isRoundDown isSub.
Proof.
  intros inst hasAsr d.
  destruct (dec_main inst hasAsr) as (c & isImm & isExact & isRoundDown & isSub & H).
  exists c, isImm, isExact, isRoundDown, isSub.
  rewrite dec_specGroup_F. exact H.
Qed.
