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

(* simpleSpec with the concrete system of cheriot/SpecInst.v, compiled for simulation *)

From Stdlib Require Import String List ZArith.
From Guru Require Import Primitives Library Syntax Combinators Notations.
From Cheriot Require Import SpecDefines SpecDevice Clint SpecRevoker Plic SpecInst.
From SpecCheriot Require Import Spec NondetSpec.

Definition simpleSpecModInst : Mod specSysTreeInst :=
  @simpleSpec PcAddrInit concreteRevConfig concreteRegions concreteClint concreteRevoker concretePlic.

From Guru Require Import Extraction Compiler.
Set Extraction Output Directory "./SimpleSim".

Definition compiledMod := compile simpleSpecModInst.
Extraction "Compile" kindSize Z.log2_up getDefault isEq compiledMod.
