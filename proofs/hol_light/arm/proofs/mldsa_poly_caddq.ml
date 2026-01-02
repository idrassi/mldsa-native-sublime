(*
 * Copyright (c) The mldsa-native project authors
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Modular reduction of a polynomial with coefficients in (-q, q) to (0, q)  *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;

(**** print_literal_from_elf "arm/mldsa/mldsa_poly_caddq.o";;
 ****)

let mldsa_poly_caddq_mc = define_assert_from_elf "mldsa_poly_caddq_mc" "arm/mldsa/mldsa_poly_caddq.o"
[
  0x529c0029;       (* arm_MOV W9 (rvalue (word 57345)) *)
  0x72a00fe9;       (* arm_MOVK W9 (word 127) 16 *)
  0x4e040d24;       (* arm_DUP_GEN Q4 X9 32 128 *)
  0xd2800201;       (* arm_MOV X1 (rvalue (word 16)) *)
  0x3dc00000;       (* arm_LDR Q0 X0 (Immediate_Offset (word 0)) *)
  0x3dc00401;       (* arm_LDR Q1 X0 (Immediate_Offset (word 16)) *)
  0x3dc00802;       (* arm_LDR Q2 X0 (Immediate_Offset (word 32)) *)
  0x3dc00c03;       (* arm_LDR Q3 X0 (Immediate_Offset (word 48)) *)
  0x6f210405;       (* arm_USHR_VEC Q5 Q0 31 32 128 *)
  0x4ea494a0;       (* arm_MLA_VEC Q0 Q5 Q4 32 128 *)
  0x6f210425;       (* arm_USHR_VEC Q5 Q1 31 32 128 *)
  0x4ea494a1;       (* arm_MLA_VEC Q1 Q5 Q4 32 128 *)
  0x6f210445;       (* arm_USHR_VEC Q5 Q2 31 32 128 *)
  0x4ea494a2;       (* arm_MLA_VEC Q2 Q5 Q4 32 128 *)
  0x6f210465;       (* arm_USHR_VEC Q5 Q3 31 32 128 *)
  0x4ea494a3;       (* arm_MLA_VEC Q3 Q5 Q4 32 128 *)
  0x3d800401;       (* arm_STR Q1 X0 (Immediate_Offset (word 16)) *)
  0x3d800802;       (* arm_STR Q2 X0 (Immediate_Offset (word 32)) *)
  0x3d800c03;       (* arm_STR Q3 X0 (Immediate_Offset (word 48)) *)
  0x3c840400;       (* arm_STR Q0 X0 (Postimmediate_Offset (word 64)) *)
  0xf1000421;       (* arm_SUBS X1 X1 (rvalue (word 1)) *)
  0x54fffde1;       (* arm_BNE (word 2097084) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let MLDSA_POLY_CADDQ_EXEC = ARM_MK_EXEC_RULE mldsa_poly_caddq_mc;;

(* ------------------------------------------------------------------------- *)
(* Code length constants                                                     *)
(* ------------------------------------------------------------------------- *)

let LENGTH_POLY_CADDQ_MC =
  REWRITE_CONV[mldsa_poly_caddq_mc] `LENGTH mldsa_poly_caddq_mc`
  |> CONV_RULE (RAND_CONV LENGTH_CONV);;

let LENGTH_SIMPLIFY_CONV =
  REWRITE_CONV[LENGTH_POLY_CADDQ_MC];;


(* ------------------------------------------------------------------------- *)
(* Specification                                                             *)
(* ------------------------------------------------------------------------- *)

let POLY_CADDQ_GOAL = `forall pc ptr x returnaddress.
    nonoverlapping (word pc, LENGTH mldsa_poly_caddq_mc) (ptr, 1024)
    ==>
    ensures arm
      (\s. // Assert that poly_tomont is loaded at PC
           aligned_bytes_loaded s (word pc) mldsa_poly_caddq_mc /\
           read PC s = word pc  /\
           // Remember LR as point-to-stop
           read X30 s = returnaddress /\
           // poly_caddq takes one argument, the base pointer
           C_ARGUMENTS [ptr] s  /\
           // Give name to 32-bit coefficients stored at ptr to be
           // able to refer to them in the post-condition
           (!i. i < 256 ==> read(memory :> bytes32(word_add ptr (word (4 * i)))) s = x i)
      )
      (\s. // We have reached the LR
           read PC s = returnaddress /\
           // Coefficients are initially in (-Q, Q)
           (!i. i < 256 ==> abs(ival(x i)) <= &8380416)
            ==>
              // Coefficients are in >= 0 and <MLDSA_Q
              (!i. i < 256 ==> ival(read(memory :> bytes32(word_add ptr (word (4 * i)))) s) = ival(x i) rem &8380417)
      )
      // Register and memory footprint
      (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
       MAYCHANGE [memory :> bytes(ptr, 1024)])
  `;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let POLY_CADDQ_SPEC = prove(POLY_CADDQ_GOAL,
  CONV_TAC LENGTH_SIMPLIFY_CONV THEN
  (* Strips the outermost universal quantifier from the conclusion of a goal *)
  REPEAT STRIP_TAC THEN
  (* Start symbolic execution with state 's0' *)
  ENSURES_INIT_TAC "s0" THEN

  (* Symbolically run instructions *)
  ARM_STEPS_TAC MLDSA_POLY_CADDQ_EXEC (1--23) THEN
  (* Try to prove the postcondition and frame as much as possible *)
  ENSURES_FINAL_STATE_TAC
);;