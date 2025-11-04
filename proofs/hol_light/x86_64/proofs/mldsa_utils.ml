(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* from s2n-bignum/common/bignum.ml *)
(* ------------------------------------------------------------------------- *)
(* Some convenient proof tools.                                              *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let SIMD_SIMPLIFY_CONV unfold_defs =
  TOP_DEPTH_CONV
   (REWR_CONV WORD_SUBWORD_AND ORELSEC WORD_SIMPLE_SUBWORD_CONV) THENC
  DEPTH_CONV WORD_NUM_RED_CONV THENC
  REWRITE_CONV (map GSYM unfold_defs);;

let SIMD_SIMPLIFY_TAC unfold_defs =
  let simdable = can (term_match [] `read X (s:armstate):int128 = whatever`) in
  TRY(FIRST_X_ASSUM
   (ASSUME_TAC o
    CONV_RULE(RAND_CONV (SIMD_SIMPLIFY_CONV unfold_defs)) o
    check (simdable o concl)));;

let MEMORY_128_FROM_16_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(16*i) in
      READ_MEMORY_MERGE_CONV 3 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

(* This tactic repeated calls `f n with monotonically increasing values of n
   until the target PC matches one of the assumptions.

   The goal must be of the form `ensure arm ...`. Clauses constraining the PC
   must be of the form `read PC some_state = some_value`. *)
let MAP_UNTIL_TARGET_PC f n = fun (asl, w) ->
  let is_pc_condition = can (term_match [] `read PC some_state = some_value`) in
  (* We assume that the goal has the form
     `ensure arm (\s. ... /\ read PC s = some_value /\ ...)` *)
  let extract_target_pc_from_goal goal =
    let _, insts, _ = term_match [] `eventually arm (\s'. P) some_state` goal in
    insts
      |> rev_assoc `P: bool`
      |> conjuncts
      |> find is_pc_condition in
  (* Find PC-constraining assumption from the list of all assumptions. *)
  let extract_pc_assumption asl =
    try Some (find (is_pc_condition o concl o snd) asl |> snd |> concl) with find -> None in
  (* Check if there is an assumption constraining the PC to the target PC *)
  let has_matching_pc_assumption asl target_pc =
    match extract_pc_assumption asl with
     | None -> false
     | Some(asm) -> can (term_match [`returnaddress: 64 word`; `pc: num`] target_pc) asm in
  let target_pc = extract_target_pc_from_goal w in
  (* ALL_TAC if we reached the target PC, NO_TAC otherwise, so
     TARGET_PC_REACHED_TAC target_pc ORELSE SOME_OTHER_TACTIC
     is effectively `if !(target_pc_reached) SOME_OTHER_TACTIC` *)
  let TARGET_PC_REACHED_TAC target_pc = fun (asl, w) ->
    if has_matching_pc_assumption asl target_pc then
      ALL_TAC (asl, w)
    else
      NO_TAC (asl, w) in
  let rec core n (asl, w) =
    (TARGET_PC_REACHED_TAC target_pc ORELSE (f n THEN core (n + 1))) (asl, w)
  in
    core n (asl, w);;

(*
 from common/relational.ml
 *)

(* ========================================================================= *)
(* A relational model of programs (in a general sense) and Hoare-type rules. *)
(*                                                                           *)
(* We use a relation "R:S->S->bool" to model a program with state space S,   *)
(* where "R s s'" means "starting in s it is possible to reach s'". This is  *)
(* mainly intended for a "single-step" setting but that single step may be   *)
(* decomposed by relational decomposition into smaller steps. Hence we build *)
(* in the possibility of nondeterminism (e.g. that some flags are undefined) *)
(* from the outset, even if in common special cases R is functional.         *)
(* ========================================================================= *)

needs "Library/rstc.ml";;
needs "common/components.ml";;

(* ------------------------------------------------------------------------- *)
(* Composition of relations, which essentially stands for sequencing.        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix(",,",(13,"right"));;

let seq = new_definition
 `((r1:B->C->bool) ,, r2) = \s0 s2:A. ?s1. r1 s0 s1 /\ r2 s1 s2`;;

let SEQ_ASSOC = prove
 (`!r1 r2 r3. r1 ,, (r2 ,, r3) = (r1 ,, r2) ,, r3`,
  REWRITE_TAC[FUN_EQ_THM; seq] THEN MESON_TAC[]);;

let SEQ_ID = prove
 (`(!r. (=) ,, r = r) /\ (!r. r ,, (=) = r)`,
  REWRITE_TAC[FUN_EQ_THM; seq] THEN MESON_TAC[]);;

let SEQ_TRIVIAL = prove
  (`!r. ((\a:A b:B. T) ,, (\a:B b:C. T)) = (\a:A b:C. T)`,
   REWRITE_TAC [FUN_EQ_THM; seq]);;

(* ------------------------------------------------------------------------- *)
(* Subsumption of relations, basically just curried subset                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("subsumed",(12,"right"));;

let subsumed = new_definition
 `R subsumed R' <=> !x y. R x y ==> R' x y`;;

let SUBSUMED_SEQ = prove
 (`!C1 C2 D1 D2.
        C1 subsumed D1 /\ C2 subsumed D2
        ==> (C1 ,, C2) subsumed (D1 ,, D2)`,
  REWRITE_TAC[subsumed; seq] THEN MESON_TAC[]);;

let SUBSUMED_FOR_SEQ = prove
 (`!C1 C2 D.
        D ,, D = D /\
        C1 subsumed D /\
        C2 subsumed D
        ==>  (C1 ,, C2) subsumed D`,
  REWRITE_TAC[FUN_EQ_THM; seq; subsumed] THEN MESON_TAC[]);;

let SUBSUMED_ID_SEQ = prove
 (`!R R'. (=) subsumed R /\ (=) subsumed R' ==> (=) subsumed (R ,, R')`,
  REWRITE_TAC[subsumed; seq] THEN MESON_TAC[]);;

let SUBSUMED_REFL = prove
 (`!R. R subsumed R`,
  REWRITE_TAC[subsumed] THEN MESON_TAC[]);;

let SUBSUMED_SEQ_LEFT = prove
 (`!C D1 D2.
     C subsumed D1 /\ (=) subsumed D2
     ==> C subsumed (D1 ,, D2)`,
  REWRITE_TAC[FUN_EQ_THM; seq; subsumed] THEN MESON_TAC[]);;

let SUBSUMED_SEQ_RIGHT = prove
 (`!C D1 D2.
     (=) subsumed D1 /\ C subsumed D2
     ==> C subsumed (D1 ,, D2)`,
  REWRITE_TAC[FUN_EQ_THM; seq; subsumed] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Assignment to a state component as a (functional) relation.               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix(":=",(14,"right"));;

let assign = new_definition
 `(c := y) = \s s'. write c y s = s'`;;

let SEQ = prove
 (`((c := y) ,, r) s = r (write c y s)`,
  REWRITE_TAC[assign; seq; FUN_EQ_THM] THEN MESON_TAC[]);;

let ASSIGN_ZEROTOP_8 = prove
 (`!c y. ((c :> zerotop_8) := y) = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_8]);;

let ASSIGN_ZEROTOP_16 = prove
 (`!c y. ((c :> zerotop_16) := y) = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_16]);;

let ASSIGN_ZEROTOP_32 = prove
 (`!c y. ((c :> zerotop_32) := y) = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_32]);;

let ASSIGN_ZEROTOP_64 = prove
 (`!c y. ((c :> zerotop_64) := y) = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_64]);;

let ASSIGN_ZEROTOP_128 = prove
 (`!c y. ((c :> zerotop_128) := y) = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_128]);;

let ASSIGN_ZEROTOP_256 = prove
 (`!c y. ((c :> zerotop_256) := y) = (c := word_zx y)`,
  REWRITE_TAC[assign; WRITE_ZEROTOP_256]);;

(* ------------------------------------------------------------------------- *)
(* A nondeterministic assignment of a state component.                       *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS = new_definition
 `ASSIGNS (c:(A,B)component) s s' <=> ?y. (c := y) s s'`;;

let ASSIGNS_THM = prove
 (`ASSIGNS c = \s s'. ?y. write c y s = s'`,
  REWRITE_TAC[FUN_EQ_THM; ASSIGNS; assign]);;

let ASSIGNS_SEQ = prove
 (`(ASSIGNS c ,, r) = \s s'. ?y. r (write c y s) s'`,
  REWRITE_TAC[ASSIGNS; assign; seq; FUN_EQ_THM] THEN MESON_TAC[]);;

let SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT = prove
 (`!c:(S,A)component.
        extensionally_valid_component c ==> (=) subsumed (ASSIGNS c)`,
  REWRITE_TAC[subsumed; ASSIGNS_THM; extensionally_valid_component] THEN
  MESON_TAC[]);;

let SUBSUMED_ASSIGNS_SUBCOMPONENTS = prove
 (`!c d1 d2. ASSIGNS d1 subsumed ASSIGNS d2
             ==> ASSIGNS (c :> d1) subsumed ASSIGNS (c :> d2)`,
  REWRITE_TAC[subsumed; ASSIGNS_THM; READ_COMPONENT_COMPOSE;
              WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

let SUBSUMED_ASSIGNS_SUBCOMPONENT = prove
 (`!c d. ASSIGNS (c :> d) subsumed ASSIGNS c`,
  REWRITE_TAC[subsumed; ASSIGNS_THM; READ_COMPONENT_COMPOSE;
              WRITE_COMPONENT_COMPOSE] THEN
  MESON_TAC[]);;

let ASSIGNS_PULL_THM = prove
 (`((if P then ASSIGNS c else c := y) =
    (\s s'. ?d. (c := if P then d else y) s s')) /\
   ((if P then c := y else ASSIGNS c) =
    (\s s'. ?d. (c := if P then y else d) s s')) /\
   ((if P then c := y else \s s'. ?d. (c := f d s) s s') =
    \s s'. ?d. (c := (if P then y else f d s)) s s') /\
   ((if P then \s s'. ?d. (c := f d s) s s' else c := y) =
    \s s'. ?d. (c := (if P then f d s else y)) s s')`,
  REWRITE_TAC[ASSIGNS_THM; assign; FUN_EQ_THM] THEN MESON_TAC[]);;

let SEQ_PULL_THM = prove
 (`((\s s'. ?y. Q y s s') ,, R = \s s'. ?y. (Q y ,, R) s s') /\
   (R ,, (\s s'. ?y. Q y s s') = \s s'. ?y. (R ,, Q y) s s')`,
  REWRITE_TAC[seq; FUN_EQ_THM] THEN MESON_TAC[]);;

let ASSIGNS_ASSIGN = prove
 (`ASSIGNS c = \s s'. ?y. (c := y) s s'`,
  REWRITE_TAC[FUN_EQ_THM; ASSIGNS; assign] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Absorbing state component modification statements into others.            *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_ABSORB_SAME_COMPONENTS = prove
 (`!c:(A,B)component.
        weakly_valid_component c
        ==> ASSIGNS c ,, ASSIGNS c = ASSIGNS c`,
  SIMP_TAC[ASSIGNS_SEQ; ASSIGNS_THM; weakly_valid_component]);;

let ASSIGNS_ABSORB_BITELEMENT = prove
 (`!i. ASSIGNS(bitelement i) ,, ASSIGNS(bitelement i) =
       ASSIGNS(bitelement i)`,
  REWRITE_TAC[ASSIGNS_SEQ; ASSIGNS_THM; WRITE_WRITE_BITELEMENT]);;

let ASSIGNS_ABSORB_ENTIRETY_R = prove
 (`!(c:(A,B)component).
        ASSIGNS c ,, ASSIGNS entirety = ASSIGNS entirety`,
  REWRITE_TAC[ASSIGNS_SEQ; ASSIGNS_THM; WRITE_ENTIRETY]);;

let ASSIGNS_ABSORB_ENTIRETY_L = prove
 (`!(c:(A,B)component).
        extensionally_valid_component c
        ==> ASSIGNS entirety ,, ASSIGNS c = ASSIGNS entirety`,
  SIMP_TAC[FUN_EQ_THM; ASSIGNS_SEQ; ASSIGNS_THM; WRITE_ENTIRETY] THEN
  REWRITE_TAC[extensionally_valid_component] THEN MESON_TAC[]);;

let ASSIGNS_ABSORB_SUBCOMPONENT_R = prove
 (`!(c:(A,B)component) (d:(B,C)component).
        valid_component c
        ==> ASSIGNS (c :> d) ,, ASSIGNS c = ASSIGNS c`,
  SIMP_TAC[FUN_EQ_THM; ASSIGNS_SEQ; ASSIGNS_THM; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[valid_component] THEN MESON_TAC[]);;

let ASSIGNS_ABSORB_SUBCOMPONENT_L = prove
 (`!(c:(A,B)component) (d:(B,C)component).
        extensionally_valid_component c /\
        extensionally_valid_component d
        ==> ASSIGNS c ,, ASSIGNS (c :> d) = ASSIGNS c`,
  SIMP_TAC[FUN_EQ_THM; ASSIGNS_SEQ; ASSIGNS_THM; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[extensionally_valid_component] THEN MESON_TAC[]);;

let ASSIGNS_RVALUE = prove
 (`!y. ASSIGNS(rvalue y) = (=)`,
  REWRITE_TAC[FUN_EQ_THM; ASSIGNS_THM; READ_WRITE_RVALUE]);;

let ASSIGNS_ABSORB_RVALUE = prove
 (`(!c y. ASSIGNS c ,, ASSIGNS (rvalue y) = ASSIGNS c) /\
   (!c y. ASSIGNS (rvalue y) ,, ASSIGNS c = ASSIGNS c) /\
   (!c d y. ASSIGNS c ,, ASSIGNS (rvalue y :> d ) = ASSIGNS c) /\
   (!c d y. ASSIGNS (rvalue y :> d) ,, ASSIGNS c = ASSIGNS c)`,
  REWRITE_TAC[COMPONENT_COMPOSE_RVALUE; ASSIGNS_RVALUE] THEN
  REWRITE_TAC[SEQ_ID]);;

(* ------------------------------------------------------------------------- *)
(* Commuting state component modification statements.                        *)
(* These are uniform even in cases where there is an absorption result.      *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_SWAP_ORTHOGONAL_COMPONENTS = prove
 (`!(c:(A,B)component) (d:(A,C)component).
        orthogonal_components c d
        ==> ASSIGNS c ,, ASSIGNS d = ASSIGNS d ,, ASSIGNS c`,
  REWRITE_TAC[orthogonal_components; seq] THEN
  REWRITE_TAC[ASSIGNS_SEQ; ASSIGNS_THM; FUN_EQ_THM] THEN
  MESON_TAC[]);;

let ASSIGNS_SWAP_ELEMENTS = prove
 (`!i j:K. ASSIGNS (element i) ,, ASSIGNS (element j) =
           ASSIGNS (element j) ,, ASSIGNS (element i)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i:K = j` THEN
  ASM_SIMP_TAC[ASSIGNS_ABSORB_SAME_COMPONENTS; VALID_COMPONENT_ELEMENT] THEN
  MATCH_MP_TAC ASSIGNS_SWAP_ORTHOGONAL_COMPONENTS THEN
  ASM_SIMP_TAC[ORTHOGONAL_COMPONENTS_ELEMENT]);;

let ASSIGNS_SWAP_BITELEMENTS = prove
 (`!i j. ASSIGNS (bitelement i) ,, ASSIGNS (bitelement j) =
         ASSIGNS (bitelement j) ,, ASSIGNS (bitelement i)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i:num = j` THEN
  ASM_REWRITE_TAC[ASSIGNS_ABSORB_BITELEMENT] THEN
  MATCH_MP_TAC ASSIGNS_SWAP_ORTHOGONAL_COMPONENTS THEN
  ASM_SIMP_TAC[ORTHOGONAL_COMPONENTS_BITELEMENT]);;

let ASSIGNS_SWAP_SUBCOMPONENTS = prove
 (`!(c:(A,B)component) (d:(B,C)component) (d':(B,D)component).
        valid_component c /\
        ASSIGNS d ,, ASSIGNS d' = ASSIGNS d' ,, ASSIGNS d
        ==> ASSIGNS (c :> d) ,, ASSIGNS (c :> d') =
            ASSIGNS (c :> d') ,, ASSIGNS (c :> d)`,
  REWRITE_TAC[valid_component; seq; ASSIGNS; assign;
              FUN_EQ_THM; WRITE_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[UNWIND_THM1] THEN SIMP_TAC[] THEN MESON_TAC[]);;

let ASSIGNS_SWAP_SUBCOMPONENTS_L = prove
 (`!(c:(A,B)component) (d:(B,C)component).
        valid_component c /\
        extensionally_valid_component d
        ==> ASSIGNS (c :> d) ,, ASSIGNS c =
            ASSIGNS c ,, ASSIGNS (c :> d)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(MESON[COMPOSE_ENTIRETY]
   `ASSIGNS (c:(A,B)component) = ASSIGNS (c :> entirety)`) THEN
  MATCH_MP_TAC ASSIGNS_SWAP_SUBCOMPONENTS THEN
  ASM_SIMP_TAC[ASSIGNS_ABSORB_ENTIRETY_R; ASSIGNS_ABSORB_ENTIRETY_L]);;

let ASSIGNS_SWAP_SUBCOMPONENTS_R = prove
 (`!(c:(A,B)component) (d:(B,C)component).
        valid_component c /\
        extensionally_valid_component d
        ==> ASSIGNS c ,, ASSIGNS (c :> d) =
            ASSIGNS (c :> d) ,, ASSIGNS c`,
  MATCH_ACCEPT_TAC(GSYM ASSIGNS_SWAP_SUBCOMPONENTS_L));;

let ASSIGNS_BYTES = prove
 (`(!a:A word. ASSIGNS (bytes(a,0)) = (=)) /\
   (!(a:A word) k.
       ASSIGNS (bytes(a,SUC k)) =
       ASSIGNS (element (word_add a (word k))) ,, ASSIGNS (bytes(a,k)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `s:A word->byte` THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `s':A word->byte` THEN
  REWRITE_TAC[ASSIGNS_SEQ; ASSIGNS_THM; bytes] THEN
  EQ_TAC THENL [MESON_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`b:byte`; `n:num`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXISTS_TAC `val(b:byte) * 2 EXP (8 * k) + n MOD 2 EXP (8 * k)` THEN
  ONCE_REWRITE_TAC[WRITE_BYTES_RESTRICT] THEN
  REWRITE_TAC[MOD_MULT_ADD; MOD_MOD_REFL] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[WORD_VAL_GALOIS] THEN
  SIMP_TAC[LIMB_BOUND; MOD_LT; GSYM DIMINDEX_8] THEN
  SIMP_TAC[limb; DIMINDEX_8; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; ADD_CLAUSES] THEN
  MATCH_MP_TAC MOD_LT THEN REWRITE_TAC[VAL_BOUND; GSYM DIMINDEX_8]);;

let ASSIGNS_SWAP_ELEMENT_BYTES = prove
 (`!(a:A word) b k.
        ASSIGNS (element a) ,, ASSIGNS (bytes(b,k)) =
        ASSIGNS (bytes(b,k)) ,, ASSIGNS (element a)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[ASSIGNS_BYTES; SEQ_ID] THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[SEQ_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ASSIGNS_SWAP_ELEMENTS] THEN
  ASM_REWRITE_TAC[GSYM SEQ_ASSOC]);;

let ASSIGNS_SWAP_BYTES = prove
 (`!(a:A word) k b j.
        ASSIGNS (bytes(a,k)) ,, ASSIGNS (bytes(b,j)) =
        ASSIGNS (bytes(b,j)) ,, ASSIGNS (bytes(a,k))`,
  GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[ASSIGNS_BYTES; SEQ_ID] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM SEQ_ASSOC] THEN
  REWRITE_TAC[SEQ_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC ASSIGNS_SWAP_ELEMENT_BYTES);;

let ASSIGNS_BYTES_ASWORD = prove
 (`!(a:A word) k.
        8 * k <= dimindex(:N)
        ==> ASSIGNS (bytes(a,k) :> (asword:(num,N word)component)) =
            ASSIGNS (bytes(a,k))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ASSIGNS_THM; WRITE_COMPONENT_COMPOSE;
              asword; write; through] THEN
  REWRITE_TAC[EXISTS_WORD] THEN ONCE_REWRITE_TAC[WRITE_BYTES_RESTRICT] THEN
  REWRITE_TAC[VAL_WORD; MOD_MOD_EXP_MIN] THEN
  ASM_REWRITE_TAC[ARITH_RULE `MIN a b = if b <= a then b else a`]);;

let ASSIGNS_BYTES8 = prove
 (`!a. ASSIGNS (bytes8 a) = ASSIGNS(bytes(a,1))`,
  GEN_TAC THEN REWRITE_TAC[bytes8] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES16 = prove
 (`!a. ASSIGNS (bytes16 a) = ASSIGNS(bytes(a,2))`,
  GEN_TAC THEN REWRITE_TAC[bytes16] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES32 = prove
 (`!a. ASSIGNS (bytes32 a) = ASSIGNS(bytes(a,4))`,
  GEN_TAC THEN REWRITE_TAC[bytes32] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES64 = prove
 (`!a. ASSIGNS (bytes64 a) = ASSIGNS(bytes(a,8))`,
  GEN_TAC THEN REWRITE_TAC[bytes64] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES128 = prove
 (`!a. ASSIGNS (bytes128 a) = ASSIGNS(bytes(a,16))`,
  GEN_TAC THEN REWRITE_TAC[bytes128] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let ASSIGNS_BYTES256 = prove
 (`!a. ASSIGNS (bytes256 a) = ASSIGNS(bytes(a,32))`,
  GEN_TAC THEN REWRITE_TAC[bytes256] THEN
  MATCH_MP_TAC ASSIGNS_BYTES_ASWORD THEN
  CONV_TAC(ONCE_DEPTH_CONV DIMINDEX_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV);;

let SUBSUMED_ASSIGNS_BYTES = prove
 (`!a1 (a2:int64) k1 k2.
        contained_modulo (2 EXP 64) (val a1,k1) (val a2,k2)
        ==> ASSIGNS (bytes(a1,k1)) subsumed ASSIGNS (bytes(a2,k2))`,
  REWRITE_TAC[GSYM DIMINDEX_64; CONTAINED_MODULO_WORDWISE] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[ASSIGNS_BYTES; NUMSEG_CLAUSES_LT] THEN
  REWRITE_TAC[IMAGE_CLAUSES; INSERT_SUBSET] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
    REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_BYTES];
    MATCH_MP_TAC SUBSUMED_FOR_SEQ THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ASSIGNS_ABSORB_SAME_COMPONENTS THEN
      REWRITE_TAC[WEAKLY_VALID_COMPONENT_BYTES];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_IMAGE]);
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    POP_ASSUM_LIST(K ALL_TAC)] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`i:num`;` k2:num`] THEN
  MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[ASSIGNS_BYTES; LT] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
   [MATCH_MP_TAC SUBSUMED_SEQ_LEFT THEN REWRITE_TAC[SUBSUMED_REFL] THEN
    MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
    REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_BYTES];
    MATCH_MP_TAC SUBSUMED_SEQ_RIGHT THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
    REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_ELEMENT]]);;

let ASSIGNS_BYTES_SPLIT = prove
 (`!(a:N word) m n.
     ASSIGNS(bytes(a,m + n)) =
     ASSIGNS(bytes(a,m)) ,, ASSIGNS(bytes(word_add a (word m),n))`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; ASSIGNS_BYTES; SEQ_ID] THEN
  REWRITE_TAC[SEQ_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ASSIGNS_SWAP_ELEMENT_BYTES] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC WORD_RULE);;

let ASSIGNS_BYTES_MONO = prove
 (`!(a:N word) m n.
        m <= n ==> ASSIGNS(bytes(a,m)) subsumed ASSIGNS(bytes(a,n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n:num = m + (n - m)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[ASSIGNS_BYTES_SPLIT]] THEN
  MATCH_MP_TAC SUBSUMED_SEQ_LEFT THEN REWRITE_TAC[SUBSUMED_REFL] THEN
  MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
  REWRITE_TAC[EXTENSIONALLY_VALID_COMPONENT_BYTES]);;

let ASSIGNS_BYTES_SUBSUMED_SPLIT = prove
 (`!k n (a:N word).
     ASSIGNS(bytes(a,n)) subsumed
     ASSIGNS(bytes(a,k)) ,, ASSIGNS(bytes(word_add a (word k),n - k))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n:num <= k` THENL
   [SUBGOAL_THEN `n - k = 0` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[SUB_EQ_0]; REWRITE_TAC[ASSIGNS_BYTES]] THEN
    ASM_SIMP_TAC[SEQ_ID; ASSIGNS_BYTES_MONO];
    SUBGOAL_THEN `n:num = k + (n - k)` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[ASSIGNS_BYTES_SPLIT; SUBSUMED_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Using a component on a relation.                                          *)
(* ------------------------------------------------------------------------- *)

let VIA = define
  `VIA (c:(S,V)component) (R:V->V->bool) =
    \s1 s2. ?y. R (read c s1) y /\ (c := y) s1 s2`;;

let VIA_COMPOSE = prove
 (`!c1 c2 R. VIA (c1 :> c2) R = VIA c1 (VIA c2 R)`,
  REWRITE_TAC[FUN_EQ_THM; FORALL_COMPONENT; VIA; assign;
    component_compose; read; write; o_DEF; GSYM LEFT_EXISTS_AND_THM] THEN
  REPEAT GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REFL_TAC);;

let VIA_SUBSUMED_ASSIGNS = prove
 (`!c:(S,V)component R. VIA c R subsumed ASSIGNS c`,
  REWRITE_TAC[VIA; subsumed; ASSIGNS] THEN MESON_TAC[]);;

let SUBSUMED_VIA = prove
 (`!c:(S,V)component R S. R subsumed S ==> VIA c R subsumed VIA c S`,
  REWRITE_TAC[VIA; subsumed; ASSIGNS] THEN MESON_TAC[]);;

let VIA_ASSIGN = prove
 (`!c:(S,V)component y. VIA c1 (c2 := y) = (c1 :> c2 := y)`,
  REWRITE_TAC[FUN_EQ_THM; VIA; assign; WRITE_COMPONENT_COMPOSE] THEN
  REPEAT GEN_TAC THEN CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REFL_TAC);;

let VIA_ASSIGNS = prove
 (`!c1 c2. VIA c1 (ASSIGNS c2) = ASSIGNS (c1 :> c2)`,
  REWRITE_TAC[FUN_EQ_THM; VIA; ASSIGNS; GSYM VIA_ASSIGN] THEN MESON_TAC[]);;

let VIA_ENTIRETY = prove
 (`!c. VIA c (ASSIGNS entirety) = ASSIGNS c`,
  REWRITE_TAC[VIA_ASSIGNS; COMPOSE_ENTIRETY]);;

let VIA_ID = prove
 (`!c:(S,V)component. extensionally_valid_component c ==> VIA c (=) = (=)`,
  REWRITE_TAC[FUN_EQ_THM; VIA; assign; extensionally_valid_component] THEN
  REPEAT STRIP_TAC THEN CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN
  ASM_REWRITE_TAC[]);;

let VIA_SEQ = prove
 (`!c:(S,V)component R1 R2. strongly_valid_component c ==>
   VIA c (R1 ,, R2) = VIA c R1 ,, VIA c R2`,
  REWRITE_TAC[FUN_EQ_THM; VIA; seq; assign; GSYM LEFT_EXISTS_AND_THM;
    strongly_valid_component] THEN
  CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `s1:V` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `y:V`;
    MAP_EVERY EXISTS_TAC [`y':V`; `y:V`] THEN
    POP_ASSUM (fun t -> POP_ASSUM (MP_TAC o C CONJ t))] THEN
  ASM_REWRITE_TAC[]);;

let VIA_SYM = prove
 (`!c:(S,V)component d:(S,W)component A B. orthogonal_components c d ==>
   VIA c A ,, VIA d B = VIA d B ,, VIA c A`,
  REWRITE_TAC[FUN_EQ_THM; VIA; seq; assign; orthogonal_components;
    GSYM LEFT_EXISTS_AND_THM; GSYM RIGHT_EXISTS_AND_THM] THEN
  CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN MESON_TAC[]);;

let VIA_ASSIGNS_SYM = MESON [VIA_SYM; VIA_ENTIRETY]
 `!c:(S,V)component d:(S,W)component A. orthogonal_components c d ==>
  VIA c A ,, ASSIGNS d = ASSIGNS d ,, VIA c A`;;

let ASSIGNS_VIA_SYM = MESON [VIA_SYM; VIA_ENTIRETY]
 `!c:(S,V)component d:(S,W)component A. orthogonal_components c d ==>
  ASSIGNS c ,, VIA d A = VIA d A ,, ASSIGNS c`;;

(* ------------------------------------------------------------------------- *)
(* Using a component on a function.                                          *)
(* ------------------------------------------------------------------------- *)

let modify = define
  `modify (c:(S,V)component) (f:V->V) =
    \s. write c (f (read c s)) s`;;

let MODIFY_COMPOSE = prove
 (`!(c:(A,B)component) (d:(B,C)component) f.
   modify (c :> d) f = modify c (modify d f)`,
  REWRITE_TAC [FUN_EQ_THM; FORALL_COMPONENT; read; write; modify;
    component_compose; o_DEF]);;

let MODIFY_CONST = prove
  (`!c:(S,V)component y. modify c (\x. y) = write c y`,
   REWRITE_TAC [modify; ETA_AX]);;

let WRITE_COMPOSE = prove
  (`!(c:(A,B)component) (d:(B,C)component) x.
    write (c :> d) x = modify c (write d x)`,
    REWRITE_TAC [FUN_EQ_THM; modify; WRITE_COMPONENT_COMPOSE]);;

let MODIFY_VIA = prove
  (`!(c:(S,V)component) f s s'.
    modify c f s = s' <=> VIA c (\a a'. f a = a') s s'`,
    REWRITE_TAC [modify; VIA; assign] THEN
    CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REWRITE_TAC[]);;

let MODIFY_ID = prove
 (`!c:(S,V)component. extensionally_valid_component c ==> modify c I = I`,
  REWRITE_TAC [FUN_EQ_THM; MODIFY_VIA; I_DEF; ETA_AX] THEN
  IMP_REWRITE_TAC [VIA_ID]);;

let MODIFY_o = prove
 (`!c:(S,V)component f g. strongly_valid_component c ==>
   modify c (f o g) = modify c f o modify c g`,
  REWRITE_TAC[FUN_EQ_THM; modify; o_DEF; strongly_valid_component] THEN
  CONV_TAC (ONCE_DEPTH_CONV UNWIND_CONV) THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let MODIFY_o_WRITE = prove
 (`!c:(S,V)component f x. strongly_valid_component c ==>
   modify c f o write c x = write c (f x)`,
  IMP_REWRITE_TAC [GSYM MODIFY_CONST; GSYM MODIFY_o] THEN
  REWRITE_TAC [o_DEF]);;

let WRITE_o_MODIFY = prove
 (`!c:(S,V)component x f. weakly_valid_component c ==>
   write c x o modify c f = write c x`,
  IMP_REWRITE_TAC [FUN_EQ_THM; modify; weakly_valid_component; o_DEF]);;

let MODIFY_SYM = prove
 (`!c:(S,V)component d:(S,W)component f g. orthogonal_components c d ==>
   modify c f o modify d g = modify d g o modify c f`,
  REWRITE_TAC[FUN_EQ_THM; modify; o_DEF; orthogonal_components] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MODIFY_WRITE_SYM = prove
 (`!c:(S,V)component d:(S,W)component f x. orthogonal_components c d ==>
   modify c f o write d x = write d x o modify c f`,
  REWRITE_TAC [GSYM MODIFY_CONST] THEN MATCH_ACCEPT_TAC MODIFY_SYM);;

let WRITE_MODIFY_SYM = METIS [ORTHOGONAL_COMPONENTS_SYM; MODIFY_WRITE_SYM]
 `!c:(S,V)component d:(S,W)component f x. orthogonal_components c d ==>
  write c x o modify d f = modify d f o write c x`;;

let READ_MODIFY_VALID_COMPONENT = prove
 (`!c:(S,V)component f s. valid_component c ==>
   read c (modify c f s) = f (read c s)`,
  REWRITE_TAC [modify; valid_component] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let READ_MODIFY_ORTHOGONAL_COMPONENTS = prove
 (`!c d f s. orthogonal_components c d ==> read c (modify d f s) = read c s`,
  REWRITE_TAC[orthogonal_components; modify] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Express "a step only (possibly) changes these state components".          *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE = define
 `MAYCHANGE [] = (=) /\
  MAYCHANGE (CONS c cs) = ASSIGNS c ,, MAYCHANGE cs`;;

let MAYCHANGE_SING = prove
 (`!c:(S,V)component. MAYCHANGE [c] = ASSIGNS c`,
  REWRITE_TAC[MAYCHANGE; SEQ_ID]);;

let MAYCHANGE_STARTER = prove
 (`!s:A. MAYCHANGE [] s s`,
  REWRITE_TAC[MAYCHANGE]);;

let MAYCHANGE_WRITE = prove
 (`R s0 s1 ==> !c y. (R ,, MAYCHANGE [c]) s0 (write c y s1)`,
  REWRITE_TAC[MAYCHANGE_SING; ASSIGNS; seq; assign] THEN MESON_TAC[]);;

let MAYCHANGE_LID = prove
 (`MAYCHANGE [] ,, R = R`,
  REWRITE_TAC[MAYCHANGE; SEQ_ID]);;

(* ------------------------------------------------------------------------- *)
(* This is just ASSIGNS or MAYCHANGE but with a different setting in mind.   *)
(* ------------------------------------------------------------------------- *)

let UNDEFINED_VALUE = new_definition
 `UNDEFINED_VALUE = ASSIGNS`;;

let UNDEFINED_VALUES = define
 `UNDEFINED_VALUES [] = (=) /\
  UNDEFINED_VALUES (CONS c cs) = ASSIGNS c ,, UNDEFINED_VALUES cs`;;

(* ------------------------------------------------------------------------- *)
(* Canonize `ASSIGNS c` term, canonizing component and scrubbing bytes_nnn   *)
(* It will not however expand "bytes_nn" nested inside :> compositions.      *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_CANON_CONV =
  let byteconv =
    GEN_REWRITE_CONV TRY_CONV
     [ASSIGNS_BYTES8; ASSIGNS_BYTES16; ASSIGNS_BYTES32; ASSIGNS_BYTES64;
      ASSIGNS_BYTES128; ASSIGNS_BYTES256] in
  fun tm ->
    match tm with
      Comb(Const("ASSIGNS",_),c) ->
       (RAND_CONV COMPONENT_CANON_CONV THENC byteconv) tm
    | _ -> failwith "ASSIGNS_CANON_CONV";;

(* ------------------------------------------------------------------------- *)
(* Compress `ASSIGNS c ,, ASSIGNS c = ASSIGNS c` for the restricted          *)
(* case of exactly the same component (not one a subcomponent).              *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_IDEMPOT_TAC =
  MATCH_MP_TAC ASSIGNS_ABSORB_SAME_COMPONENTS THEN
  CONV_TAC WEAKLY_VALID_COMPONENT_CONV;;

let ASSIGNS_IDEMPOT_CONV tm =
  let th = PART_MATCH (lhand o rand) ASSIGNS_ABSORB_SAME_COMPONENTS tm in
  MP th (WEAKLY_VALID_COMPONENT_CONV(lhand(concl th)));;

let ASSIGNS_IDEMPOT_RULE tm =
  let th = ISPEC tm ASSIGNS_ABSORB_SAME_COMPONENTS in
  MP th (WEAKLY_VALID_COMPONENT_CONV(lhand(concl th)));;

(* ------------------------------------------------------------------------- *)
(* Commute `ASSIGNS c ,, ASSIGNS d` (don't absorb even if possible).         *)
(* This will work pretty generally, but "zerotop_32" spoils things. It's OK. *)
(* We'll never purposely put both in a modifies list and the automatic ones  *)
(* will all expand to something happening on the full space anyway.          *)
(* ------------------------------------------------------------------------- *)

let ASSIGNS_SWAP_TAC =
  let pth = REFL `ASSIGNS c ,, ASSIGNS d` in
  let toptac = CONV_TAC(BINOP_CONV(BINOP_CONV ASSIGNS_CANON_CONV)) in
  let basetac =
    MATCH_ACCEPT_TAC pth ORELSE
    MATCH_ACCEPT_TAC ASSIGNS_SWAP_ELEMENTS ORELSE
    MATCH_ACCEPT_TAC ASSIGNS_SWAP_BITELEMENTS ORELSE
    MATCH_ACCEPT_TAC ASSIGNS_SWAP_BYTES ORELSE
    MATCH_ACCEPT_TAC ASSIGNS_SWAP_ELEMENT_BYTES ORELSE
    MATCH_ACCEPT_TAC(GSYM ASSIGNS_SWAP_ELEMENT_BYTES) ORELSE
    (MATCH_MP_TAC ASSIGNS_SWAP_SUBCOMPONENTS_L THEN CONJ_TAC THENL
      [CONV_TAC VALID_COMPONENT_CONV;
       CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV]) ORELSE
    (MATCH_MP_TAC ASSIGNS_SWAP_SUBCOMPONENTS_R THEN CONJ_TAC THENL
      [CONV_TAC VALID_COMPONENT_CONV;
       CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV]) in
  let rec maintac g =
    (basetac ORELSE
     (MATCH_MP_TAC ASSIGNS_SWAP_SUBCOMPONENTS THEN CONJ_TAC THENL
       [CONV_TAC VALID_COMPONENT_CONV;
        toptac THEN maintac])) g in
  (toptac THEN maintac) ORELSE
  (* ORTHOGONAL_COMPONENTS_CONV can be expensive; rely on it as the last
     resort. *)
  (MATCH_MP_TAC ASSIGNS_SWAP_ORTHOGONAL_COMPONENTS THEN
     CONV_TAC ORTHOGONAL_COMPONENTS_CONV);;

(* A cache that stores `ASSIGNS x ,, ASSIGNS y` theorems.
   `assoc y !(assoc x !assigns_swap_conv_cache)` must return the
   theorem, if the entry exists. *)
let assigns_swap_conv_cache:
    (term * ((term * thm) list ref)) list ref = ref [];;

let ASSIGNS_SWAP_CONV tm =
  match tm with
    Comb(Comb((Const(",,",_) as stm),
              (Comb(Const("ASSIGNS",_),x) as ctm)),
         (Comb(Const("ASSIGNS",_),y) as dtm)) ->
      if ctm = dtm then REFL tm else
      let the_goal:term = mk_eq(tm,mk_comb(mk_comb(stm,dtm),ctm)) in
      if is_const(x) && is_const(y) then
        (* Use cache if x and y are constants, e.g., `PC` and `X1`. *)
        try
          let lref = assoc x !assigns_swap_conv_cache in
          try assoc y !lref
          with _ ->
            let newth = prove(the_goal,ASSIGNS_SWAP_TAC) in
            lref := (y, newth)::!lref; newth
        with _ ->
          let newth = prove(the_goal,ASSIGNS_SWAP_TAC) in
          assigns_swap_conv_cache := (x, ref [(y,newth)])::!assigns_swap_conv_cache;
          newth
      else
        prove(the_goal,ASSIGNS_SWAP_TAC)
  | _ -> failwith "ASSIGNS_SWAP_CONV";;

(* ------------------------------------------------------------------------- *)
(* Canonize ASSIGNS / MAYCHANGE chain into right-assoc ASSIGNS only.         *)
(* In the degenerate case it will be just (=).                               *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE_CANON_CONV =
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [MAYCHANGE; SEQ_ID; GSYM SEQ_ASSOC];;

(* ------------------------------------------------------------------------- *)
(* Prove equality relation is subsumed by a MAYCHANGE/ASSIGNS sequence       *)
(* ------------------------------------------------------------------------- *)

let SUBSUMED_ID_MAYCHANGE_TAC =
  CONV_TAC(RAND_CONV MAYCHANGE_CANON_CONV) THEN
  REPEAT(MATCH_MP_TAC SUBSUMED_ID_SEQ THEN CONJ_TAC) THEN
  TRY(MATCH_ACCEPT_TAC(ISPEC `(=)` SUBSUMED_REFL)) THEN
  MATCH_MP_TAC SUBSUMED_ID_EXTENSIONALLY_VALID_COMPONENT THEN
  CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV THEN NO_TAC;;

(* ------------------------------------------------------------------------- *)
(* Given (a_1 ,, ... ,, a_n) ,, b, commute b leftwards down the chain until  *)
(* either you eliminate it using the argument conversion (typically when you *)
(* absorb it into the same component) or you get right back to the start, or *)
(* you get stuck. The returned value is +1 for absorption, 0 for commuting   *)
(* to the start and -1 for getting stuck in the middle.                      *)
(* ------------------------------------------------------------------------- *)

let rec ASSIGNS_MOVE_BACK_CONV acv tm =
  try let th0 = GEN_REWRITE_CONV I [GSYM SEQ_ASSOC] tm in
      let ltm,rtm = dest_comb(rand(concl th0)) in
      let (p,th1) = ASSIGNS_MOVE_BACK_CONV acv rtm in
      let th2 = TRANS th0 (AP_TERM ltm th1) in
      if p <> 0 then (p,th2) else
      let th3 = GEN_REWRITE_RULE RAND_CONV [SEQ_ASSOC] th2 in
      (try 1,CONV_RULE (RAND_CONV (LAND_CONV acv)) th3
       with Failure _ -> try
         let th4 = CONV_RULE (RAND_CONV (LAND_CONV ASSIGNS_SWAP_CONV)) th3 in
         0,GEN_REWRITE_RULE RAND_CONV [GSYM SEQ_ASSOC] th4
       with Failure _ -> -1,th2)
  with Failure _ -> try 1,acv tm
  with Failure _ -> try 0,ASSIGNS_SWAP_CONV tm
  with Failure _ -> -1,REFL tm;;

(* ------------------------------------------------------------------------- *)
(* Now implement idempotence for a whole chain of ASSIGNS clauses.           *)
(* ASSIGNS_SEQ_ABSORB_CONV takes a term of the form                         *)
(* (ASSIGNS a1 ,, ... ,, ASSIGNS an) ,, (ASSIGNS b1 ,, ... ASSIGNS bm)       *)
(* where each bi occurs somewhere in the a list that it can be commuted      *)
(* back to and absorbed by in sequence. In the common case the a and b lists *)
(* are identical. Returns equality with just the a's list.                   *)
(* ------------------------------------------------------------------------- *)

let rec ASSIGNS_SEQ_ABSORB_CONV tm =
  match tm with
    Comb(Comb(Const(",,",_),_),Comb(Comb(Const(",,",_),_),_)) ->
      let th0 = GEN_REWRITE_CONV I [SEQ_ASSOC] tm in
      let lop,rtm = dest_comb(rand(concl th0)) in
      let op,ltm = dest_comb lop in
      let n,th1 = ASSIGNS_MOVE_BACK_CONV ASSIGNS_IDEMPOT_CONV ltm in
      if n <> 1 then failwith "ASSIGNS_SEQ_ABSORB_CONV" else
      let th2 = TRANS th0 (AP_THM (AP_TERM op th1) rtm) in
      TRANS th2 (ASSIGNS_SEQ_ABSORB_CONV (rand(concl th2)))
  | _ ->
      let n,th = ASSIGNS_MOVE_BACK_CONV ASSIGNS_IDEMPOT_CONV tm in
      if n <> 1 then failwith "ASSIGNS_SEQ_ABSORB_CONV" else th;;

let ASSIGNS_SEQ_IDEMPOT_CONV tm =
  match tm with
    Comb(Comb(Const(",,",_),ltm),rtm) when ltm = rtm ->
        ASSIGNS_SEQ_ABSORB_CONV tm
  | _ -> failwith "ASSIGNS_SEQ_IDEMPOT_CONV: Non-identical sequences";;

(* ------------------------------------------------------------------------- *)
(* Tactic to prove FRAMES ,, FRAMES = FRAMES where FRAMES is a ,,-sequence   *)
(* of ASSIGNS and CHANGES statements.                                        *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE_IDEMPOT_TAC =
  let the_truth = `true` in
  fun (asl,w as gl) ->
    match w with
      Comb(Comb(Const("=",_) as etm,Comb(Comb(Const(",,",_) as ctm,ltm),rtm)),stm)
          when ltm = stm && rtm = stm ->
        if is_gabs ltm && snd (strip_gabs ltm) = the_truth then
          MATCH_ACCEPT_TAC SEQ_TRIVIAL gl
        else
          let th1 = MAYCHANGE_CANON_CONV stm in
          let th2 = MK_BINOP ctm (th1,th1) in
          let th3 = MK_BINOP etm (th2,th1) in
          let th4 = if is_const(rand(concl th1))
                    then ISPEC (rand(concl th1)) (CONJUNCT1 SEQ_ID)
                    else ASSIGNS_SEQ_IDEMPOT_CONV(lhand(rand(concl th3))) in
          ACCEPT_TAC (EQ_MP (SYM th3) th4) gl
    | _ -> failwith "MAYCHANGE_IDEMPOT_TAC";;

(* ------------------------------------------------------------------------- *)
(* Identify a "MAYCHANGE"-containing term.                                   *)
(* ------------------------------------------------------------------------- *)

let maychange_term =
  let pred t = match t with
    Const("MAYCHANGE",_) -> true
  | _ -> false in
  can (find_term pred);;

(* ------------------------------------------------------------------------- *)
(* Produce a modified update list given theorems                             *)
(* th = |- (MAYCHANGE [....] ,, MAYCHANGE [...] ... ) s0 s1                  *)
(* uth = |- write c1 y1 (write c2 y2 (write .... s1)) = s2                   *)
(* give back                                                                 *)
(* th' = |- (MAYCHANGE [....] ,, MAYCHANGE [...] ... ) s0 s1                 *)
(* Tries to absorb components already in the list, otherwise                 *)
(* simply appends them individually. Not optimal but OK.                     *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE_UPDATE_RULE =
  let JUSTADD_CONV =
    GEN_REWRITE_CONV I [MAYCHANGE_LID] ORELSEC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM SEQ_ASSOC] in
  let MAYCHANGE_SIMPLE_ABSORB_CONV tm =
    match tm with
      Comb(Comb(Const(",,",_) as cop,ltm),rtm) ->
          let lth = MAYCHANGE_CANON_CONV ltm
          and rth = MAYCHANGE_CANON_CONV rtm in
          let tm' = mk_comb(mk_comb(cop,rand(concl lth)),rand(concl rth)) in
          let n,eth = ASSIGNS_MOVE_BACK_CONV ASSIGNS_IDEMPOT_CONV tm' in
          if n <> 1 then JUSTADD_CONV tm else
          let th' = MK_COMB(AP_TERM cop lth,rth) in
          TRANS (TRANS th' eth) (SYM lth)
    | _ -> failwith "MAYCHANGE_SIMPLE_ABSORB_CONV" in
  let rec BASIC_MAYCHANGE_UPDATE_RULE tm th =
      match tm with
        Comb(Comb(Comb(Const("write",_),c),y),s) ->
           let th1 = BASIC_MAYCHANGE_UPDATE_RULE s th in
           let th2 = ISPECL [c;y] (MATCH_MP MAYCHANGE_WRITE th1) in
           CONV_RULE(RATOR_CONV(RATOR_CONV MAYCHANGE_SIMPLE_ABSORB_CONV)) th2
      | _ -> th in
  fun uth th ->
    let th' = BASIC_MAYCHANGE_UPDATE_RULE (lhand(concl uth)) th in
    EQ_MP (AP_TERM (rator(concl th')) uth) th';;

(* ------------------------------------------------------------------------- *)
(* Produce updated "MAYCHANGE" assumption from one in assumptions.           *)
(* Absorbs simple duplicates but otherwise doesn't try to be clever.         *)
(* Works from antecedent in the goal specifying the state update.            *)
(* ------------------------------------------------------------------------- *)

let MAYCHANGE_STATE_UPDATE_TAC =
  DISCH_THEN(fun uth ->
    MP_TAC uth THEN
    FIRST_X_ASSUM(ASSUME_TAC o MAYCHANGE_UPDATE_RULE uth o
           check(maychange_term o concl)));;

(* ------------------------------------------------------------------------- *)
(* A property P always becomes true "eventually". This correctly reflects    *)
(* nondeterminism: we need the property to hold eventually along *every*     *)
(* possible path from the initial state. It also requires (unless P already  *)
(* holds in the initial state) that there *is* indeed a successor state, so  *)
(* the "on all paths from the current state" quantifier never holds          *)
(* degenerately because there are no such paths.                             *)
(* ------------------------------------------------------------------------- *)

let eventually_RULES,eventually_INDUCT,eventually_CASES =
  new_inductive_definition
   `(!s. P s ==> eventually step P s) /\
    (!s. (?s'. step s s') /\
         (!s'. step s s' ==> eventually step P s') ==> eventually step P s)`;;

let EVENTUALLY_MONO = prove
 (`!step P Q. (!s. P s ==> Q s)
              ==> (!s. eventually step P s ==> eventually step Q s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC eventually_INDUCT THEN
  ASM_MESON_TAC[eventually_RULES]);;

let EVENTUALLY_IMP_EVENTUALLY = prove
 (`!step P Q. (!s. eventually step P s ==> eventually step Q s) <=>
              (!s. P s ==> eventually step Q s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[eventually_RULES]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC eventually_INDUCT THEN
  ASM_REWRITE_TAC[eventually_RULES]);;

let EVENTUALLY_EVENTUALLY = prove
 (`!step P. eventually step (eventually step P) = eventually step P`,
  GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; FORALL_AND_THM; TAUT
   `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  REWRITE_TAC[eventually_RULES] THEN
  REWRITE_TAC[EVENTUALLY_IMP_EVENTUALLY; eventually_RULES]);;


let EVENTUALLY_P_INOUT = prove(
  `!(s0:S). P /\ eventually step (\s. Q s) s0 <=>
            eventually step (\s. P /\ Q s) s0`,
  ASM_CASES_TAC `P:bool` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT`~p <=> (p ==> F)`] THEN
  MATCH_MP_TAC eventually_INDUCT THEN MESON_TAC[]);;

let EVENTUALLY_DISJ1 = prove(
  `!(step:S->S->bool) P Q s.
    eventually step (\s. P s) s ==> eventually step (\s. P s \/ Q s) s`,
  REPEAT_N 3 GEN_TAC THEN MATCH_MP_TAC EVENTUALLY_MONO THEN MESON_TAC[]);;

let EVENTUALLY_DISJ2 = prove(
  `!(step:S->S->bool) P Q s.
    eventually step (\s. Q s) s ==> eventually step (\s. P s \/ Q s) s`,
  REPEAT_N 3 GEN_TAC THEN MATCH_MP_TAC EVENTUALLY_MONO THEN MESON_TAC[]);;

let EVENTUALLY_TRIVIAL = prove(
  `!(step:S->S->bool) s. eventually step (\s.T) s`,
  MESON_TAC[eventually_CASES]);;

let EVENTUALLY_CONSTANT = prove(`!(s0:S). eventually step (\s. P) s0 <=> P`,
  ONCE_REWRITE_TAC[TAUT `(\(s:S). P) = \(s:S). (P /\ (\(s2:S). T) s)`] THEN
  REWRITE_TAC[GSYM EVENTUALLY_P_INOUT] THEN
  STRIP_TAC THEN ASM_CASES_TAC `P:bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (CONJUNCT1 (ISPECL [`step:S->S->bool`;`\(s:S). T`] eventually_RULES)) THEN MESON_TAC[]);;

let EVENTUALLY_EXISTS = prove(
  `!(step:S->S->bool) (P:S->T->bool) (s:S).
    (?x. eventually step (\s'. P s' x) s) ==>
    eventually step (\s'. ?x. P s' x) s`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `eventually (step:S->S->bool) (\s'. P s' (x:T)) s` THEN
  SPEC_TAC (`s:S`,`s:S`) THEN
  MATCH_MP_TAC EVENTUALLY_MONO THEN MESON_TAC[]);;

let EVENTUALLY_IMP_INOUT = prove(
  `!(step:S->S->bool) P (Q:S->bool) s.
    (P ==> eventually step (\s'. Q s') s) <=>
    (P ==> eventually step (\s'. P /\ Q s') s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `eventually (step:S->S->bool) (\s'. Q s') s` MP_TAC THENL
    [ASM_MESON_TAC[];ALL_TAC] THEN
    SPEC_TAC (`s:S`,`s:S`) THEN MATCH_MP_TAC EVENTUALLY_MONO THEN BETA_TAC THEN ASM_REWRITE_TAC[];

    ASM_CASES_TAC `P:bool` THEN ASM_REWRITE_TAC[]
  ]);;

(* ------------------------------------------------------------------------- *)
(* A more explicit and non-inductive equivalent of "eventually R P s":       *)
(* starting in state s there is no infinite sequence of non-P states         *)
(* nor a finite sequence of non-P states ending in a stuck state, where      *)
(* all sequences have adjacent pairs connected by the relation.              *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_SEQUENTIALLY = prove
 (`!R p s:A.
        eventually R p s <=>
        ~(?x:num->A. x 0 = s /\
                     (!n. R (x n) (x(n + 1))) /\
                     (!n. ~p(x n))) /\
        ~(?N x:num->A. x 0 = s /\
                       (!n. n < N ==> R (x n) (x(n + 1))) /\
                       (!n. ~p(x n)) /\
                       ~(?s'. R (x N) s'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAUT
   `(p <=> q /\ r) <=> (p ==> q) /\ (p ==> r) /\ (~p ==> ~q \/ ~r)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN SPEC_TAC(`s:A`,`s:A`) THEN
    MATCH_MP_TAC eventually_INDUCT THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:A` THEN DISCH_TAC THEN
    X_GEN_TAC `x:num->A` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(x:num->A) 1` o CONJUNCT2) THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `\i. (x:num->A) (i + 1)`) THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!n:num. n <= N ==> eventually R (p:A->bool) (x n)`
    (MP_TAC o SPEC `N:num`) THENL
     [ALL_TAC; ASM_MESON_TAC[eventually_CASES; LE_REFL]] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC_LT; ADD1] THEN
    ASM_MESON_TAC[eventually_CASES; LT_IMP_LE];
    DISCH_TAC THEN GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    SUBGOAL_THEN
      `?x. x 0 = (s:A) /\ (!n. ~eventually R p (x n)) /\
           (!n s'. R (x n) s' ==> R (x n) (x(SUC n)))`
    MP_TAC THENL
     [MATCH_MP_TAC DEPENDENT_CHOICE_FIXED THEN
      ASM_MESON_TAC[eventually_CASES];
      MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC `x:num->A` THEN ONCE_REWRITE_TAC[eventually_CASES] THEN
    REWRITE_TAC[ADD1; DE_MORGAN_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `!n:num. ?s'. (R:A->A->bool) (x n) s'` THENL
     [ASM_MESON_TAC[]; DISJ2_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Traditional Hoare triples, with a few rules.                              *)
(* ------------------------------------------------------------------------- *)

let hoare = define
 `hoare step pre post <=> !s. pre s ==> eventually step post s`;;

let HOARE_PRECONDITION = prove
 (`!step pre pre' post.
      hoare step pre post /\ (!s. pre' s ==> pre s) ==> hoare step pre' post`,
  REWRITE_TAC[hoare] THEN MESON_TAC[]);;

let HOARE_POSTCONDITION = prove
 (`!step pre post post'.
        hoare step pre post /\ (!s. post s ==> post' s)
        ==> hoare step pre post'`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[hoare] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP EVENTUALLY_MONO) THEN SIMP_TAC[ETA_AX]);;

let HOARE = prove
 (`!step pre post:A->bool.
        hoare step pre post <=>
        !s. eventually step pre s ==> eventually step post s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hoare] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o ISPEC `step:A->A->bool` o
      MATCH_MP EVENTUALLY_MONO) THEN
    REWRITE_TAC[EVENTUALLY_EVENTUALLY; ETA_AX];
    MESON_TAC[eventually_RULES]]);;

let HOARE_TRANS = prove
 (`!step pre mid post.
      hoare step pre mid /\ hoare step mid post ==> hoare step pre post`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [HOARE] THEN
  REWRITE_TAC[hoare] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A variant with an explicit frame condition or action in the TLA sense.    *)
(* ------------------------------------------------------------------------- *)

let ensures = define
 `ensures step precondition postcondition frame <=>
        !s. precondition s
            ==> eventually step (\s'. postcondition s' /\ frame s s') s`;;

let ENSURES_TRIVIAL = prove
 (`!step q f. ensures step (\x. F) q f`,
  REWRITE_TAC[ensures]);;

let ENSURES_ALREADY = prove
 (`!step p q r.
        (!x. p x ==> q x) /\ (=) subsumed r ==> ensures step p q r`,
  REWRITE_TAC[ensures; subsumed] THEN MESON_TAC[eventually_CASES]);;


(* ------------------------------------------------------------------------- *)
(*     Hoare Logic with the number of small steps explicitly annotated.      *)
(* Tactics in this file (common/relationa.ml) will support both 'ensures'    *)
(* and ensures_n.                                                            *)
(* ------------------------------------------------------------------------- *)

needs "common/relational_n.ml";;

(* If t is 'ensures ...' or 'eventually ...', return x
   If t is 'ensures_n ...' or 'eventually_n ...', return y
   Otherwise, raise a failure *)
let ensures_or_ensures_n (w:term) (x:'a) (y:'a): 'a =
  let c,_ = strip_comb w in
  let n = name_of c in
  if n = "ensures" || n = "eventually" then x
  else if n = "ensures_n" || n = "eventually_n" then y
  else failwith
          ("The term is neither ensures, eventually, ensures_n or " ^
                     "eventually_n");;

let ENSURES_OR_ENSURES_N_TAC tac_for_ensures tac_for_ensures_n: tactic =
  W(fun (asl,w) ->
      ensures_or_ensures_n w tac_for_ensures tac_for_ensures_n);;


(* ------------------------------------------------------------------------- *)
(* Initialization of breaking down an "ensures" triple                       *)
(* ------------------------------------------------------------------------- *)

let ENSURES_INIT_TAC sname =
  ENSURES_OR_ENSURES_N_TAC
      (GEN_REWRITE_TAC I [ensures])
      (GEN_REWRITE_TAC I [ensures_n])
      THEN
  BETA_TAC THEN
  W(fun (asl,w) ->
        let ty = type_of(fst(dest_forall w)) in
        let svar = mk_var(sname,ty) in
        X_GEN_TAC svar THEN
        DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
        ASSUME_TAC(ISPEC svar MAYCHANGE_STARTER));;


(* ========================================================================= *)
(* Generic stuff about bignums. This works for x86 and ARM, but is not quite *)
(* loadable independently since it uses the "memory" component.              *)
(* ========================================================================= *)

let bigdigit = new_definition
 `bigdigit n i = (n DIV (2 EXP (64 * i))) MOD (2 EXP 64)`;;

let BIGDIGITSUM_WORKS_GEN = prove
 (`!n k. nsum {i | i < k} (\i. 2 EXP (64 * i) * bigdigit n i) =
         n MOD (2 EXP (64 * k))`,
  REWRITE_TAC[bigdigit; EXP_MULT; DIGITSUM_WORKS_GEN]);;

let BIGDIGITSUM_WORKS = prove
 (`!n k. n < 2 EXP (64 * k)
         ==> nsum {i | i < k} (\i. 2 EXP (64 * i) * bigdigit n i) = n`,
  REWRITE_TAC[bigdigit; EXP_MULT; DIGITSUM_WORKS]);;

let BIGDIGIT_BOUND = prove
 (`!n i. bigdigit n i < 2 EXP 64`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit] THEN
  REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let VAL_WORD_BIGDIGIT = prove
 (`!n i. val(word(bigdigit n i):int64) = bigdigit n i`,
  SIMP_TAC[VAL_WORD_EQ; DIMINDEX_64; BIGDIGIT_BOUND]);;

let BIGDIGIT_0 = prove
 (`!i. bigdigit 0 i = 0`,
  REWRITE_TAC[bigdigit; DIV_0; MOD_0]);;

let BIGDIGIT_ZERO = prove
 (`!n i. n < 2 EXP (64 * i) ==> bigdigit n i = 0`,
  SIMP_TAC[bigdigit; DIV_LT; MOD_0]);;

let BIGDIGIT_ADD_LEFT =
  prove(`forall a n b i.
  i < n ==> bigdigit (a + 2 EXP (64 * n) * b) i = bigdigit a i`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bigdigit] THEN
  SUBGOAL_THEN `2 EXP (64 * n) = 2 EXP (64 * i) * (2 EXP (64 * (n-i)))` SUBST_ALL_TAC THENL [
    REWRITE_TAC[GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LEFT_ADD_DISTRIB] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;

    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    IMP_REWRITE_TAC[DIV_MULT_ADD; EXP_2_NE_0] THEN
    SUBGOAL_THEN
      `2 EXP (64*(n-i)) = 2 EXP 64 * (2 EXP (64*(n-i-1)))`
      SUBST_ALL_TAC THENL [
      REWRITE_TAC[GSYM EXP_ADD] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC;

      ALL_TAC
    ] THEN
    REWRITE_TAC[GSYM MULT_ASSOC] THEN
    IMP_REWRITE_TAC[MOD_MULT_ADD; EXP_2_NE_0]]);;

let BIGDIGIT_SUC = prove(`forall n i t.
  t < 2 EXP 64 ==> bigdigit (t + 2 EXP 64 * n) (SUC i) = bigdigit n i`,

  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bigdigit;ARITH_RULE`SUC i = 1 + i`;LEFT_ADD_DISTRIB;EXP_ADD;GSYM DIV_DIV;
              ARITH_RULE`64 * 1 = 64`] THEN
  IMP_REWRITE_TAC[DIV_MULT_ADD;EXP_2_NE_0;SPECL [`t:num`;`2 EXP 64`] DIV_LT] THEN
  REWRITE_TAC[ADD]);;

let highdigits = new_definition
 `highdigits n i = n DIV (2 EXP (64 * i))`;;

let lowdigits = new_definition
 `lowdigits n i = n MOD (2 EXP (64 * i))`;;

let HIGH_LOW_DIGITS = prove
 (`(!n i. 2 EXP (64 * i) * highdigits n i + lowdigits n i = n) /\
   (!n i. lowdigits n i + 2 EXP (64 * i) * highdigits n i = n) /\
   (!n i. highdigits n i * 2 EXP (64 * i) + lowdigits n i = n) /\
   (!n i. lowdigits n i + highdigits n i * 2 EXP (64 * i) = n)`,
  REWRITE_TAC[lowdigits; highdigits] THEN
  MESON_TAC[DIVISION_SIMP; ADD_SYM; MULT_SYM]);;

let HIGHDIGITS_CLAUSES = prove
 (`(!n. highdigits n 0 = n) /\
   (!n i. highdigits n (i + 1) = highdigits n i DIV 2 EXP 64)`,
  REWRITE_TAC[highdigits; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[EXP; DIV_1; EXP_ADD; GSYM DIV_DIV]);;

let HIGHDIGITS_STEP = prove
 (`!n i. highdigits n i = 2 EXP 64 * highdigits n (i + 1) + bigdigit n i`,
  REWRITE_TAC[highdigits; bigdigit; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD; GSYM DIV_DIV] THEN ARITH_TAC);;

let LOWDIGITS_CLAUSES = prove
 (`(!n. lowdigits n 0 = 0) /\
   (!n i. lowdigits n (i + 1) =
          2 EXP (64 * i) * bigdigit n i + lowdigits n i)`,
  REWRITE_TAC[lowdigits; highdigits; bigdigit; EXP; MOD_1; MULT_CLAUSES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; EXP_ADD; MOD_MULT_MOD]);;

let HIGHDIGITS_EQ_0 = prove
 (`!n i. highdigits n i = 0 <=> n < 2 EXP (64 * i)`,
  SIMP_TAC[highdigits; DIV_EQ_0; EXP_EQ_0; ARITH_EQ]);;

let HIGHDIGITS_0 = prove
 (`!n. highdigits n 0 = n`,
  REWRITE_TAC[HIGHDIGITS_CLAUSES]);;

let HIGHDIGITS_ZERO = prove
 (`!n i. n < 2 EXP (64 * i) ==> highdigits n i = 0`,
  REWRITE_TAC[HIGHDIGITS_EQ_0]);;

let HIGHDIGITS_TRIVIAL = prove
 (`!n. highdigits 0 n = 0`,
  REWRITE_TAC[highdigits; DIV_0]);;

let LOWDIGITS_0 = prove
 (`!n. lowdigits n 0 = 0`,
  REWRITE_TAC[LOWDIGITS_CLAUSES]);;

let LOWDIGITS_1 = prove
 (`!n. lowdigits n 1 = bigdigit n 0`,
  SUBST1_TAC(ARITH_RULE `1 = 0 + 1`) THEN
  REWRITE_TAC[LOWDIGITS_CLAUSES; LOWDIGITS_0] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES]);;

let HIGHDIGITS_TOP = prove
 (`!n k. n < 2 EXP (64 * k) ==> highdigits n (k - 1) = bigdigit n (k - 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[highdigits; bigdigit] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  SIMP_TAC[RDIV_LT_EQ; EXP_EQ_0; ARITH_EQ; GSYM EXP_ADD] THEN
  TRANS_TAC LTE_TRANS `2 EXP (64 * k)` THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let LOWDIGITS_BOUND = prove
 (`!n i. lowdigits n i < 2 EXP (64 * i)`,
  REWRITE_TAC[lowdigits; MOD_LT_EQ; EXP_EQ_0; ARITH_EQ]);;

let LOWDIGITS_EQ_SELF = prove
 (`!n i. lowdigits n i = n <=> n < 2 EXP (64 * i)`,
  SIMP_TAC[lowdigits; MOD_EQ_SELF; EXP_EQ_0; ARITH_EQ]);;

let LOWDIGITS_SELF = prove
 (`!n i. n < 2 EXP (64 * i) ==> lowdigits n i = n`,
  REWRITE_TAC[LOWDIGITS_EQ_SELF]);;

let LOWDIGITS_TRIVIAL = prove
 (`!n. lowdigits 0 n = 0`,
  REWRITE_TAC[lowdigits; MOD_0]);;

let LOWDIGITS_LE = prove
 (`!n i. lowdigits n i <= n`,
  REWRITE_TAC[lowdigits; MOD_LE]);;

let LOWDIGITS_LOWDIGITS = prove
 (`!n i j. lowdigits (lowdigits n i) j = lowdigits n (MIN i j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lowdigits; MOD_MOD_EXP_MIN] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let BIGDIGIT_HIGHDIGITS = prove
 (`!n i j. bigdigit (highdigits n i) j = bigdigit n (i + j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; highdigits] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; DIV_DIV]);;

let HIGHDIGITS_HIGHDIGITS = prove
 (`!n i j. highdigits (highdigits n i) j = highdigits n (i + j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[highdigits] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; EXP_ADD; DIV_DIV]);;

let BIGDIGIT_LOWDIGITS = prove
 (`!n i j. bigdigit (lowdigits n i) j = if j < i then bigdigit n j else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; lowdigits] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[DIV_MOD; GSYM EXP_ADD; MOD_MOD_EXP_MIN] THEN
    ASM_SIMP_TAC[ARITH_RULE
     `j < i ==> MIN (64 * i) (64 * j + 64) = 64 * j + 64`];
    MATCH_MP_TAC(MESON[MOD_0] `x = 0 ==> x MOD n = 0`) THEN
    SIMP_TAC[DIV_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    TRANS_TAC LTE_TRANS `2 EXP (64 * i)` THEN
    REWRITE_TAC[MOD_LT_EQ; EXP_EQ_0; ARITH_EQ; LE_EXP] THEN ASM_ARITH_TAC]);;

let BIGDIGIT_DIV = prove
 (`!a i e.
     e <= 64
     ==> bigdigit (a DIV 2 EXP e) i =
         2 EXP (64 - e) * bigdigit a (i + 1) MOD 2 EXP e +
         bigdigit a i DIV 2 EXP e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bigdigit] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[MULT_SYM] DIV_DIV] THEN
  REWRITE_TAC[GSYM DIV_DIV; EXP_ADD; ARITH_RULE
   `64 * (i + 1) = 64 * i + 64`] THEN
  SPEC_TAC(`a DIV 2 EXP (64 * i)`,`a:num`) THEN GEN_TAC THEN
  ASM_SIMP_TAC[MOD_MOD_EXP_MIN; ARITH_RULE `e <= 64 ==> MIN 64 e = e`] THEN
  GEN_REWRITE_TAC (funpow 3 LAND_CONV)
   [ARITH_RULE `a = 2 EXP 64 * a DIV 2 EXP 64 + a MOD 2 EXP 64`] THEN
  MP_TAC(ARITH_RULE `a MOD 2 EXP 64 < 2 EXP 64`) THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIV_MOD_DISJOINT_BITS; DISJOINT_BITS_CLAUSES] THEN
  BINOP_TAC THENL [ALL_TAC; ASM_MESON_TAC[MOD_LT; DIV_LE; LET_TRANS]] THEN
  REWRITE_TAC[DIV_MOD; MOD_MULT2;
              ARITH_RULE `e * 2 EXP 64 = 2 EXP 64 * e`] THEN
  ASM_SIMP_TAC[MULT_DIV; DIVIDES_EXP_LE_IMP; DIV_EXP; ARITH_EQ]);;

let WORD_BIGDIGIT_DIV = prove
 (`!a i e.
        e <= 64
        ==> word(bigdigit (a DIV 2 EXP e) i):int64 =
            word_subword ((word_join:int64->int64->int128)
                          (word (bigdigit a (i + 1))) (word (bigdigit a i)))
                         (e,64)`,
  SIMP_TAC[GSYM VAL_EQ; VAL_WORD_BIGDIGIT; VAL_WORD_SUBWORD_JOIN_64;
           DIMINDEX_64; ARITH_LE; ARITH_LT] THEN
  REWRITE_TAC[BIGDIGIT_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Mapping little-endian word list to/from natural number (general size).    *)
(* ------------------------------------------------------------------------- *)

let num_of_wordlist = define
 `num_of_wordlist ([]:(N word) list) = 0 /\
  num_of_wordlist (CONS (h:N word) t) =
     val h + 2 EXP dimindex(:N) * num_of_wordlist t`;;

let wordlist_of_num = define
 `(wordlist_of_num 0 n :(N word)list = []) /\
  (wordlist_of_num (SUC k) n =
     CONS (word(n MOD 2 EXP dimindex(:N)):N word)
          (wordlist_of_num k (n DIV 2 EXP dimindex(:N))))`;;

let NUM_OF_WORDLIST_SING = prove
 (`!h:N word. num_of_wordlist [h] = val h`,
  REWRITE_TAC[num_of_wordlist; MULT_CLAUSES; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_APPEND = prove
 (`!lis1 lis2:(N word)list.
        num_of_wordlist(APPEND lis1 lis2) =
        num_of_wordlist lis1 +
        2 EXP (dimindex(:N) * LENGTH lis1) * num_of_wordlist lis2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; LENGTH; num_of_wordlist] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; EXP; ADD_CLAUSES] THEN
  REWRITE_TAC[EXP_ADD] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_LENGTH = prove
 (`!l:(N word)list. num_of_wordlist l < 2 EXP (dimindex(:N) * LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; EXP_ADD; ARITH] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o lhand o snd) THEN
  MATCH_MP_TAC(ARITH_RULE
   `n * (x + 1) <= y ==> h < n ==> h + n * x < y`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND = prove
 (`!l:(N word)list n.
        LENGTH l <= n ==> num_of_wordlist l < 2 EXP (dimindex(:N) * n)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LTE_TRANS `2 EXP (dimindex(:N) * LENGTH(l:(N word)list))` THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_BOUND_LENGTH; LE_EXP; LE_MULT_LCANCEL] THEN
  ASM_ARITH_TAC);;

let NUM_OF_WORDLIST_BOUND_GEN = prove
 (`!l:((N word)list) n.
        dimindex(:N) * LENGTH l <= n ==> num_of_wordlist l < 2 EXP n`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand NUM_OF_WORDLIST_BOUND_LENGTH o
    lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let NUM_OF_WORDLIST_DIV = prove
 (`!(w:N word) ws.
        num_of_wordlist (CONS w ws) DIV 2 EXP dimindex(:N) =
        num_of_wordlist ws`,
  SIMP_TAC[num_of_wordlist; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_MOD = prove
 (`!(w:N word) ws.
        num_of_wordlist (CONS w ws) MOD 2 EXP dimindex(:N) = val w`,
  REWRITE_TAC[num_of_wordlist; MOD_MULT_ADD] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND]);;

let NUM_OF_WORDLIST_ZAP = prove
 (`!l:(N word)list.
        2 EXP dimindex(:N) * num_of_wordlist l =
        num_of_wordlist(CONS (word 0) l)`,
  REWRITE_TAC[num_of_wordlist; VAL_WORD_0; ADD_CLAUSES]);;

let LENGTH_WORDLIST_OF_NUM = prove
 (`!k n. LENGTH(wordlist_of_num k n:(N word)list) = k`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[wordlist_of_num; LENGTH]);;

let NUM_OF_WORDLIST_BOUND = prove
 (`!l:(N word)list. num_of_wordlist l < 2 EXP (dimindex(:N) * LENGTH l)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; num_of_wordlist; ARITH; EXP; MULT_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN DISCH_TAC THEN
  REWRITE_TAC[EXP_ADD] THEN  MATCH_MP_TAC(ARITH_RULE
     `h < n /\ n * (t + 1) <= n * e
      ==> h + n * t < n * e`) THEN
  REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN ASM_ARITH_TAC);;

let WORDLIST_OF_NUM_OF_WORDLIST = prove
 (`!l:(N word)list. wordlist_of_num (LENGTH l) (num_of_wordlist l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[num_of_wordlist; wordlist_of_num; LENGTH] THEN FIRST_X_ASSUM
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  SIMP_TAC[CONS_11; MOD_MULT_ADD; DIV_MULT_ADD; ARITH_EQ; WORD_VAL_GALOIS;
           EXP_EQ_0; MOD_MOD_REFL; MOD_EQ_SELF] THEN
  SIMP_TAC[VAL_BOUND; DIV_LT; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_OF_NUM_0 = prove
 (`!k. num_of_wordlist(wordlist_of_num k 0:(N word)list) = 0`,
  INDUCT_TAC THEN SIMP_TAC[num_of_wordlist; wordlist_of_num] THEN
  ASM_REWRITE_TAC[VAL_WORD_0; DIV_0; MOD_0; MULT_CLAUSES; ADD_CLAUSES]);;

let NUM_OF_WORDLIST_OF_NUM = prove
 (`!k n. num_of_wordlist(wordlist_of_num k n:(N word)list) =
         n MOD 2 EXP (dimindex(:N) * k)`,
  INDUCT_TAC THEN REWRITE_TAC[num_of_wordlist] THENL
   [REWRITE_TAC[wordlist_of_num; num_of_wordlist; EXP; MOD_1; MULT_CLAUSES];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[wordlist_of_num; num_of_wordlist] THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE `n * SUC k = n + n * k`; MOD_MULT_MOD] THEN
  REWRITE_TAC[VAL_WORD; MOD_MOD_REFL] THEN ARITH_TAC);;

let WORDLIST_OF_NUM_MOD = prove
 (`!k n. wordlist_of_num k (n MOD 2 EXP (dimindex(:N) * k)):(N word)list =
         wordlist_of_num k n`,
  REPEAT GEN_TAC THEN REWRITE_TAC [GSYM NUM_OF_WORDLIST_OF_NUM] THEN
  REWRITE_TAC [REWRITE_RULE [LENGTH_WORDLIST_OF_NUM]
    (SPEC `wordlist_of_num k n:(N word)list` WORDLIST_OF_NUM_OF_WORDLIST)]);;

let NUM_OF_WORDLIST_OF_NUM_EQ_SELF = prove
 (`!k n. n < 2 EXP (dimindex(:N) * k)
         ==> num_of_wordlist(wordlist_of_num k n:(N word)list) = n`,
  SIMP_TAC[NUM_OF_WORDLIST_OF_NUM; MOD_LT]);;

let NUM_OF_WORDLIST_LT = prove
 (`!(m0:N word) m1 (n0:N word) n1.
        num_of_wordlist(CONS m0 m1) < num_of_wordlist(CONS n0 n1) <=>
        num_of_wordlist m1 < num_of_wordlist n1 \/
        num_of_wordlist m1 = num_of_wordlist n1 /\ val m0 < val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LT THEN REWRITE_TAC[VAL_BOUND]);;

let NUM_OF_WORDLIST_LE = prove
 (`!(m0:N word) m1 (n0:N word) n1.
        num_of_wordlist(CONS m0 m1) <= num_of_wordlist(CONS n0 n1) <=>
        num_of_wordlist m1 < num_of_wordlist n1 \/
        num_of_wordlist m1 = num_of_wordlist n1 /\ val m0 <= val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LE THEN REWRITE_TAC[VAL_BOUND]);;

let NUM_OF_WORDLIST_EQ = prove
 (`!(m0:N word) m1 (n0:N word) n1.
        num_of_wordlist(CONS m0 m1) = num_of_wordlist(CONS n0 n1) <=>
        m0 = n0 /\ num_of_wordlist m1 = num_of_wordlist n1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[num_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[VAL_BOUND]);;

let NUM_OF_WORDLIST_SUB_LIST_0 = prove
 (`!(l:(N word)list) n.
        num_of_wordlist(SUB_LIST(0,n) l) =
        num_of_wordlist l MOD 2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; MOD_1] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[MOD_UNIQUE] THEN
  REWRITE_TAC[EXP_ADD] THEN CONJ_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC(ARITH_RULE
     `h < n /\ n * (t + 1) <= n * e
      ==> h + n * t < n * e`) THEN
    REWRITE_TAC[VAL_BOUND; LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `n + 1 <= m <=> n < m`; MOD_LT_EQ] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    MATCH_MP_TAC(NUMBER_RULE
     `(t == t') (mod d)
      ==> (h + e * t == h + e * t') (mod (e * d))`) THEN
    REWRITE_TAC[CONG_RMOD; CONG_REFL]]);;

let NUM_OF_WORDLIST_SUB_LIST = prove
 (`!(l:(N word)list) m n.
        num_of_wordlist (SUB_LIST(m,n) l) =
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * m)) MOD
        2 EXP (dimindex(:N) * n)`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist; DIV_0; MOD_0] THEN
  MAP_EVERY X_GEN_TAC [`h:N word`; `t:(N word)list`] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SUB_LIST_0; GSYM(CONJUNCT2 num_of_wordlist);
              EXP; DIV_1; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[SUB_LIST_CLAUSES; num_of_wordlist] THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `n:num` THEN
  SIMP_TAC[EXP_ADD; GSYM DIV_DIV; DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ] THEN
  SIMP_TAC[DIV_LT; VAL_BOUND; ADD_CLAUSES]);;

(* Add SUB_LIST_1 definition from misc.ml *)
let SUB_LIST_1 = prove
 (`!(l:A list) n. SUB_LIST(n,1) l = if n < LENGTH l then [EL n l] else []`,
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; SUB_LIST_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`h:A`; `t:A list`] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[SUB_LIST_CLAUSES; LT_0; num_CONV `1`; EL; TL] THEN
  ASM_REWRITE_TAC[GSYM(num_CONV `1`); LT_SUC; HD]);;

let NUM_OF_WORDLIST_EL = prove
 (`!(l:(N word)list) n.
        (num_of_wordlist l DIV 2 EXP (dimindex(:N) * n)) MOD
        2 EXP (dimindex(:N)) =
        if n < LENGTH l then val(EL n l) else 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`l:(N word)list`; `n:num`; `1`]
   NUM_OF_WORDLIST_SUB_LIST) THEN
  REWRITE_TAC[SUB_LIST_1; MULT_CLAUSES] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN COND_CASES_TAC THEN
  REWRITE_TAC[NUM_OF_WORDLIST_SING; num_of_wordlist]);;

let EL_NUM_OF_WORDLIST = prove
 (`!(l:(N word)list) n.
        n < LENGTH l
        ==> EL n l = word(num_of_wordlist l DIV 2 EXP (dimindex(:N) * n))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`l:(N word)list`; `n:num`] NUM_OF_WORDLIST_EL) THEN
  ASM_REWRITE_TAC[WORD_VAL_GALOIS]);;

let LISTS_NUM_OF_WORDLIST_EQ = prove
 (`!l1 l2:(N word)list.
        l1 = l2 <=>
        LENGTH l1 = LENGTH l2 /\
        num_of_wordlist l1 = num_of_wordlist l2`,
  MESON_TAC[WORDLIST_OF_NUM_OF_WORDLIST]);;

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND = prove
 (`!m (a:int64) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word) t.
    dimindex(:N) <= len
    ==> (read (m :> bytes(a,len)) s = num_of_wordlist (CONS h t) <=>
         read (m :> wbytes a) s = h /\
         read (m :> bytes(word_add a (word(dimindex(:N))),len-dimindex(:N))) s=
         num_of_wordlist t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM VAL_EQ; VAL_READ_WBYTES; READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[num_of_wordlist; DIMINDEX_TYBIT0] THEN
  REWRITE_TAC[ARITH_RULE `2 * 2 * 2 * n = 8 * n`] THEN
  REWRITE_TAC[ARITH_RULE `(8 * n) DIV 8 = n`] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `d:num <= l ==> l = d + (l - d)`)) THEN
  REWRITE_TAC[READ_BYTES_COMBINE; ADD_SUB2] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * 2 * n = 8 * n`]);;

let BYTES_EQ_NUM_OF_WORDLIST_APPEND = prove
 (`!m (a:int64) (s:S) lis1 (lis2:(N word)list) len1 len2.
        dimindex(:N) * LENGTH lis1 = 8 * len1
        ==>  (read (m :> bytes(a,len1+len2)) s =
              num_of_wordlist(APPEND lis1 lis2) <=>
              read (m :> bytes(a,len1)) s = num_of_wordlist lis1 /\
              read (m :> bytes(word_add a (word len1),len2)) s =
              num_of_wordlist lis2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_COMBINE] THEN
  ASM_REWRITE_TAC[NUM_OF_WORDLIST_APPEND] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ THEN REWRITE_TAC[READ_BYTES_BOUND] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_BOUND_GEN THEN ASM_REWRITE_TAC[LE_REFL]);;

let BYTES_EQ_NUM_OF_WORDLIST_EXPAND_CONV =
  let pth = prove
   (`!m (a:int64) len (s:S) (h:((((N)tybit0)tybit0)tybit0) word).
        dimindex(:N) = len
        ==> (read (m :> bytes(a,len)) s = num_of_wordlist [h] <=>
             read (m :> wbytes a) s = h)`,
    SIMP_TAC[BYTES_EQ_NUM_OF_WORDLIST_EXPAND; LE_REFL] THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; SUB_REFL; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[num_of_wordlist]) in
  let frule = PART_MATCH (lhand o rand) pth
  and brule = PART_MATCH (lhand o rand) BYTES_EQ_NUM_OF_WORDLIST_EXPAND in
  let baseconv tm =
    let ith = frule tm in
    let sth = (LAND_CONV DIMINDEX_CONV THENC NUM_EQ_CONV)
              (lhand(concl ith)) in
    MP ith (EQT_ELIM sth) in
  let rec conv tm =
    try baseconv tm with Failure _ ->
    let ith = brule tm in
    let dth = DIMINDEX_CONV(lhand(lhand(concl ith))) in
    let ith' = SUBS[dth] ith in
    let ath = MP ith' (EQT_ELIM(NUM_LE_CONV(lhand(concl ith')))) in
    let bth = CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV
               (RAND_CONV
                 (BINOP2_CONV (TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV)
                              NUM_SUB_CONV))))))) ath in
    CONV_RULE(RAND_CONV(RAND_CONV conv)) bth in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Mapping a little-endian word list into a number (64-bit case of above).   *)
(* ------------------------------------------------------------------------- *)

let bignum_of_list = define
 `bignum_of_list [] = 0 /\
  bignum_of_list (CONS h t) = h + 2 EXP 64 * bignum_of_list t`;;

let bignum_of_wordlist = define
 `bignum_of_wordlist [] = 0 /\
  bignum_of_wordlist (CONS (h:int64) t) =
     val h + 2 EXP 64 * bignum_of_wordlist t`;;

bounder_prenorm_thms := union [bignum_of_wordlist] (!bounder_prenorm_thms);;

let BIGNUM_OF_WORDLIST_DIV = prove
 (`!w ws. bignum_of_wordlist (CONS w ws) DIV 2 EXP 64 = bignum_of_wordlist ws`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_of_wordlist] THEN
  SIMP_TAC[DIV_MULT_ADD; EXP_EQ_0; ARITH_EQ; EQ_ADD_RCANCEL_0; DIV_EQ_0] THEN
  W(MP_TAC o PART_MATCH lhand VAL_BOUND o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_64]);;

let BIGNUM_OF_WORDLIST_SING = prove
 (`!w. bignum_of_wordlist [w] = val w`,
  REWRITE_TAC[bignum_of_wordlist] THEN ARITH_TAC);;

let BIGNUM_OF_WORDLIST_MOD = prove
 (`!w ws. bignum_of_wordlist (CONS w ws) MOD 2 EXP 64 = val w`,
  REWRITE_TAC[bignum_of_wordlist; MOD_MULT_ADD] THEN
  SIMP_TAC[MOD_LT; VAL_BOUND_64]);;

let BIGNUM_OF_WORDLIST_ZAP = prove
 (`!l. 2 EXP 64 * bignum_of_wordlist l = bignum_of_wordlist(CONS (word 0) l)`,
  REWRITE_TAC[bignum_of_wordlist; VAL_WORD_0] THEN ARITH_TAC);;

let BIGNUM_OF_WORDLIST_BOUND_LENGTH = prove
 (`!l. bignum_of_wordlist l < 2 EXP (64 * LENGTH l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; bignum_of_wordlist] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; EXP_ADD] THEN
  MP_TAC(SPEC `h:int64` VAL_BOUND_64) THEN ASM_ARITH_TAC);;

let BIGNUM_OF_WORDLIST_BOUND = prove
 (`!l n. LENGTH l <= n ==> bignum_of_wordlist l < 2 EXP (64 * n)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LTE_TRANS `2 EXP (64 * LENGTH(l:int64 list))` THEN
  ASM_REWRITE_TAC[BIGNUM_OF_WORDLIST_BOUND_LENGTH; LE_EXP] THEN
  ASM_ARITH_TAC);;

let BIGNUM_FROM_WORDLIST_BOUND_GEN = prove
 (`!l n. 64 * LENGTH l <= n ==> bignum_of_wordlist l < 2 EXP n`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand BIGNUM_OF_WORDLIST_BOUND_LENGTH o
    lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let BIGNUM_OF_WORDLIST_APPEND = prove
 (`!l1 l2. bignum_of_wordlist (APPEND l1 l2) =
           bignum_of_wordlist l1 +
           2 EXP (64 * LENGTH l1) * bignum_of_wordlist l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[bignum_of_wordlist; APPEND; LENGTH; MULT_CLAUSES] THEN
  REWRITE_TAC[EXP; EXP_ADD] THEN ARITH_TAC);;

let BIGNUM_OF_WORDLIST_LT = prove
 (`!m0 m1 n0 n1.
        bignum_of_wordlist(CONS m0 m1) < bignum_of_wordlist(CONS n0 n1) <=>
        bignum_of_wordlist m1 < bignum_of_wordlist n1 \/
        bignum_of_wordlist m1 = bignum_of_wordlist n1 /\ val m0 < val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bignum_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LT_64 THEN REWRITE_TAC[VAL_BOUND_64]);;

let BIGNUM_OF_WORDLIST_LE = prove
 (`!m0 m1 n0 n1.
        bignum_of_wordlist(CONS m0 m1) <= bignum_of_wordlist(CONS n0 n1) <=>
        bignum_of_wordlist m1 < bignum_of_wordlist n1 \/
        bignum_of_wordlist m1 = bignum_of_wordlist n1 /\ val m0 <= val n0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[bignum_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_LE_64 THEN REWRITE_TAC[VAL_BOUND_64]);;

let BIGNUM_OF_WORDLIST_EQ = prove
 (`!m0 m1 n0 n1.
        bignum_of_wordlist(CONS m0 m1) = bignum_of_wordlist(CONS n0 n1) <=>
        m0 = n0 /\ bignum_of_wordlist m1 = bignum_of_wordlist n1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM VAL_EQ] THEN
  REWRITE_TAC[bignum_of_wordlist] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  MATCH_MP_TAC LEXICOGRAPHIC_EQ_64 THEN REWRITE_TAC[VAL_BOUND_64]);;

let BIGNUM_OF_WORDLIST_EQ_0 = prove
 (`!l. bignum_of_wordlist l = 0 <=> ALL (\x. x = word 0) l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL; bignum_of_wordlist; ADD_EQ_0; MULT_EQ_0; EXP_EQ_0] THEN
  ASM_REWRITE_TAC[ARITH_EQ; VAL_EQ_0]);;

let BIGNUM_OF_WORDLIST_EQ_MAX = prove
 (`!l n. 64 * LENGTH l = n
         ==> (bignum_of_wordlist l = 2 EXP n - 1 <=>
              ALL (\x. x = word_not(word 0)) l)`,
  GEN_TAC THEN REWRITE_TAC[FORALL_UNWIND_THM1] THEN
  MP_TAC(SPEC `MAP word_not (l:int64 list)` BIGNUM_OF_WORDLIST_EQ_0) THEN
  REWRITE_TAC[WORD_RULE `x = word_not(word 0) <=> word_not x = word 0`] THEN
  REWRITE_TAC[ALL_MAP; o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC(ARITH_RULE `n = a + b + 1 ==> (a = n - 1 <=> b = 0)`) THEN
  SPEC_TAC(`l:int64 list`,`l:int64 list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[bignum_of_wordlist; MAP; LENGTH] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; EXP_ADD] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES; REAL_VAL_WORD_NOT; DIMINDEX_64] THEN
  REAL_ARITH_TAC);;

let BIGNUM_OF_WORDLIST_LT_MAX = prove
 (`!l n. 64 * LENGTH l = n
         ==> (bignum_of_wordlist l < 2 EXP n - 1 <=>
              EX (\x. ~(x = word_not(word 0))) l)`,
  SIMP_TAC[GSYM NOT_ALL; GSYM BIGNUM_OF_WORDLIST_EQ_MAX] THEN
  REWRITE_TAC[ARITH_RULE `a < n - 1 <=> a < n /\ ~(a = n - 1)`] THEN
  SIMP_TAC[LT_LE; BIGNUM_FROM_WORDLIST_BOUND_GEN; LE_REFL]);;

let BIGNUM_OF_WORDLIST_DIV_CONV =
  let pth = prove
   (`64 <= n
     ==> bignum_of_wordlist (CONS w ws) DIV 2 EXP n =
         bignum_of_wordlist ws DIV 2 EXP (n - 64)`,
    REWRITE_TAC[ARITH_RULE `64 <= n <=> n = 64 + (n - 64)`] THEN
    DISCH_THEN(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[EXP_ADD; GSYM DIV_DIV; BIGNUM_OF_WORDLIST_DIV]) in
  let rule = PART_MATCH (lhand o rand) pth in
  let rec conv tm =
    try let th1 = rule tm in
        let th2 = MP th1 (EQT_ELIM(NUM_LE_CONV(lhand(concl th1)))) in
        let th3 = CONV_RULE(funpow 3 RAND_CONV NUM_SUB_CONV) th2 in
        CONV_RULE(RAND_CONV conv) th3
    with Failure _ -> REFL tm in
  let patok = can (term_match [] `bignum_of_wordlist l DIV 2 EXP n`) in
  (conv o check patok) THENC
  GEN_REWRITE_CONV (TRY_CONV o LAND_CONV)
   [BIGNUM_OF_WORDLIST_SING; CONJUNCT1 bignum_of_wordlist] THENC
  GEN_REWRITE_CONV TRY_CONV [DIV_0; ARITH_RULE `n DIV 2 EXP 0 = n`];;

let BIGDIGIT_BIGNUM_OF_WORDLIST = prove(`forall l i.
  i < LENGTH l ==> bigdigit (bignum_of_wordlist l) i = val (EL i l)`,

  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[LENGTH] THEN ARITH_TAC;

    REWRITE_TAC[LENGTH; bignum_of_wordlist] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    STRIP_TAC THENL [
      (* i = 0 *)
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[bigdigit;EL;HD] THEN
      REWRITE_TAC[MULT_0;EXP;DIV_1] THEN
      ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
      REWRITE_TAC[MOD_MULT; ADD_0; MOD_MOD_REFL] THEN
      SIMP_TAC[VAL_BOUND_64;MOD_LT];

      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[EL;TL] THEN
      IMP_REWRITE_TAC[BIGDIGIT_SUC;VAL_BOUND_64] THEN
      ASM_ARITH_TAC
    ]
  ]);;

(* ------------------------------------------------------------------------- *)
(* Reading a general word list from memory. This may be somewhat incoherent  *)
(* unless the total number of bits dimindex(:N) * n is a multiple of 8.      *)
(* ------------------------------------------------------------------------- *)

let wordlist_from_memory = define
 `wordlist_from_memory(a,n) s:(N word)list =
    wordlist_of_num n
     (read (memory :> bytes(a,(dimindex(:N) * n + 7) DIV 8)) s)`;;

let WORDLIST_FROM_MEMORY_GEN = prove
 (`!n m a s.
        dimindex(:N) * n <= 8 * m
        ==> wordlist_from_memory(a,n) s:(N word)list =
            wordlist_of_num n (read(memory :> bytes(a,m)) s)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[wordlist_from_memory] THEN
  ONCE_REWRITE_TAC[GSYM WORDLIST_OF_NUM_MOD] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `(dimindex (:N) * n + 7) DIV 8 = MIN m ((dimindex (:N) * n + 7) DIV 8)`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; GSYM READ_BYTES_MOD] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ARITH_RULE `MIN a b = b <=> b <= a`] THEN ARITH_TAC);;

let WORDLIST_FROM_MEMORY = prove
 (`!a n s. wordlist_from_memory(a,n) s:((((N tybit0)tybit0)tybit0)word)list =
           wordlist_of_num n (read(memory :> bytes(a,dimindex(:N) * n)) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[wordlist_from_memory] THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN REPLICATE_TAC 4 AP_TERM_TAC THEN
  ARITH_TAC);;

let LENGTH_WORDLIST_FROM_MEMORY = prove
 (`!a n s. LENGTH(wordlist_from_memory(a,n) s:(N word)list) = n`,
  REWRITE_TAC[wordlist_from_memory; LENGTH_WORDLIST_OF_NUM]);;

let NUM_OF_WORDLIST_FROM_MEMORY_GEN = prove
 (`!n m a s.
        dimindex(:N) * n = 8 * m
        ==> num_of_wordlist(wordlist_from_memory(a,n) s:(N word)list) =
            read(memory :> bytes(a,m)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[wordlist_from_memory] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(8 * m + 7) DIV 8 = m`] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_OF_NUM_EQ_SELF THEN
  ASM_REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_BOUND]);;

let NUM_OF_WORDLIST_FROM_MEMORY = prove
 (`!a n s.
        num_of_wordlist
         (wordlist_from_memory(a,n) s:((((N tybit0)tybit0)tybit0)word)list) =
        read(memory :> bytes(a,dimindex(:N) * n)) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NUM_OF_WORDLIST_FROM_MEMORY_GEN THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN ARITH_TAC);;

let WORDLIST_FROM_MEMORY_EQ_ALT = prove
 (`!addr len size l s.
        dimindex(:N) * len = 8 * size
        ==> (wordlist_from_memory(addr,len) s:(N word)list = l <=>
             LENGTH l = len /\
             read (memory :> bytes(addr,size)) s = num_of_wordlist l)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH(l:(N word)list) = len` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[LENGTH_WORDLIST_FROM_MEMORY]] THEN
  EQ_TAC THENL [ASM_MESON_TAC[NUM_OF_WORDLIST_FROM_MEMORY_GEN]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `wordlist_of_num len:num->(N word)list`) THEN
  MATCH_MP_TAC EQ_IMP THEN
  BINOP_TAC THENL [ALL_TAC; ASM_MESON_TAC[WORDLIST_OF_NUM_OF_WORDLIST]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC WORDLIST_FROM_MEMORY_GEN THEN
  ASM_REWRITE_TAC[LE_REFL]);;

let WORDLIST_FROM_MEMORY_CLAUSES = prove
 (`(!a s. wordlist_from_memory(a,0) s:(N word)list = []) /\
   (!a n s.
     wordlist_from_memory(a,SUC n) s :((((N tybit0)tybit0)tybit0)word)list =
     APPEND (wordlist_from_memory(a,n) s)
            [read (memory :> wbytes(word_add a (word(dimindex(:N) * n)))) s])`,
  CONJ_TAC THENL
   [REWRITE_TAC[wordlist_from_memory; MULT_CLAUSES; ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES_TRIVIAL] THEN
    REWRITE_TAC[wordlist_of_num];
    REPEAT GEN_TAC] THEN
  REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  REWRITE_TAC[LENGTH_WORDLIST_FROM_MEMORY; LENGTH_APPEND; LENGTH; ADD_CLAUSES;
              NUM_OF_WORDLIST_FROM_MEMORY; wordlist_of_num;
              NUM_OF_WORDLIST_APPEND; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; NUM_OF_WORDLIST_SING] THEN
  REWRITE_TAC[ARITH_RULE `x * SUC y = x * y + x`; READ_BYTES_COMBINE] THEN
  REWRITE_TAC[VAL_READ_WBYTES; DIMINDEX_TYBIT0; DIMINDEX_TYBIT1] THEN
  REWRITE_TAC[GSYM MULT_ASSOC; ARITH_RULE `2 * 2 * 2 * x = 8 * x`] THEN
  REWRITE_TAC[ARITH_RULE `(8 * n) DIV 8 = n`]);;

let WORDLIST_FROM_MEMORY_CONV =
  let pthc = prove
   (`l:((((N tybit0)tybit0)tybit0)word)list = APPEND l [] /\
     APPEND (wordlist_from_memory(a,0) s) l = l /\
     APPEND (wordlist_from_memory(a,SUC n) s) l =
     APPEND (wordlist_from_memory(a,n) s)
     (CONS (read(memory :> wbytes(word_add a (word(dimindex(:N) * n)))) s) l)`,
    REWRITE_TAC[WORDLIST_FROM_MEMORY_CLAUSES] THEN
    REWRITE_TAC[APPEND_NIL; APPEND; GSYM APPEND_ASSOC]) in
  let pths = CONJUNCTS pthc
  and avars = sort (<) (frees(concl pthc))
  and timfn = type_match (type_of(lhand(lhand(concl pthc))))
  and prule =
       (PURE_REWRITE_RULE o map GSYM)
       [BYTES8_WBYTES; BYTES16_WBYTES; BYTES32_WBYTES; BYTES64_WBYTES;
        BYTES128_WBYTES; BYTES256_WBYTES] in
  fun tm ->
    match tm with
      Comb(Comb(Const("wordlist_from_memory",_),
                Comb(Comb(Const(",",_),_),n)),_) when is_numeral n ->
      let tyin = timfn (type_of tm) [] in
      let [a_tm;l_tm;n_tm;s_tm] = map (inst tyin) avars
      and [pth_init;pth_base;pth_step] =
        map (CONV_RULE(ONCE_DEPTH_CONV DIMINDEX_CONV) o INST_TYPE tyin) pths in
      let rule_base = GEN_REWRITE_RULE RAND_CONV [pth_base]
      and rule_step =
        CONV_RULE(RAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV num_CONV)) THENC
                  GEN_REWRITE_CONV I [pth_step] THENC
                  RAND_CONV(LAND_CONV(LAND_CONV (funpow 2 RAND_CONV
                    (funpow 2 RAND_CONV NUM_MULT_CONV THENC
                     TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
                     GEN_REWRITE_CONV TRY_CONV
                      [WORD_RULE `word_add z (word 0):int64 = z`])))))) in
      let rec conv th =
        try rule_base th with Failure _ ->
        let th' = rule_step th in conv th' in
      prule(conv (INST [tm,l_tm] pth_init))
    | _ -> failwith "WORDLIST_FROM_MEMORY_CONV";;

(* ------------------------------------------------------------------------- *)
(* Pairing up elements of a word list, relation with above value             *)
(* ------------------------------------------------------------------------- *)

let pair_wordlist = define
 `(!hi (lo:N word) rest.
     pair_wordlist (CONS lo (CONS hi rest)) =
     CONS (word_join hi lo:((N)tybit0)word) (pair_wordlist rest)) /\
  (!w. pair_wordlist [w] = [word_join (word 0:N word) w]) /\
  pair_wordlist [] = []`;;

let LENGTH_PAIR_WORDLIST = prove
 (`!l:(N word)list. LENGTH(pair_wordlist l) = (LENGTH l + 1) DIV 2`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(N word)list)` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N word)list`,`l:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[ARITH_RULE `n < SUC(SUC n)`] THEN ARITH_TAC);;

let NUM_OF_PAIR_WORDLIST = prove
 (`!l:(N word)list. num_of_wordlist (pair_wordlist l) = num_of_wordlist l`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(l:(N word)list)` THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`l:(N word)list`,`l:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  MAP_EVERY X_GEN_TAC [`lo:N word`; `med:(N word)list`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SPEC_TAC(`med:(N word)list`,`med:(N word)list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[pair_wordlist; num_of_wordlist] THEN
  SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; VAL_WORD_JOIN_SIMPLE; DIMINDEX_TYBIT0;
           VAL_WORD_0; GSYM MULT_2; LENGTH; ARITH_RULE `n < SUC(SUC n)`] THEN
  REWRITE_TAC[MULT_2; EXP_ADD] THEN ARITH_TAC);;

let WORDLIST_FROM_MEMORY_PAIR_GEN = prove
 (`!a n s. 4 divides (dimindex(:N) * n)
           ==> wordlist_from_memory(a,n) s =
               pair_wordlist(wordlist_from_memory(a,2*n) s:(N word)list)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LISTS_NUM_OF_WORDLIST_EQ] THEN
  ASM_REWRITE_TAC[LENGTH_PAIR_WORDLIST; LENGTH_WORDLIST_FROM_MEMORY] THEN
  REWRITE_TAC[NUM_OF_PAIR_WORDLIST] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:num` o REWRITE_RULE[divides]) THEN
  TRANS_TAC EQ_TRANS `read(memory :> bytes(a,m)) s` THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC NUM_OF_WORDLIST_FROM_MEMORY_GEN THEN
  REWRITE_TAC[DIMINDEX_TYBIT0] THEN POP_ASSUM MP_TAC THEN CONV_TAC NUM_RING);;

let WORDLIST_FROM_MEMORY_PAIR = prove
 (`!a n s. wordlist_from_memory(a,n) s =
           pair_wordlist
             (wordlist_from_memory(a,2*n) s:(((N tybit0)tybit0)word)list)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC WORDLIST_FROM_MEMORY_PAIR_GEN THEN
  REWRITE_TAC[DIMINDEX_TYBIT0; ARITH_RULE `2 * 2 * n = n * 4`] THEN
  NUMBER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Extracting a bignum from memory.                                          *)
(* ------------------------------------------------------------------------- *)

let bignum_from_memory = new_definition
 `bignum_from_memory(a,k) s =
    nsum {i | i < k}
         (\i. 2 EXP (64 * i) *
              read (memory :> bytes(word_add a (word(8 * i)),8)) s)`;;

let BIGNUM_FROM_MEMORY_BOUND = prove
 (`!k a s. bignum_from_memory(a,k) s < 2 EXP (64 * k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory; EXP_MULT] THEN
  MATCH_MP_TAC DIGITSUM_BOUND THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `64 = 8 * 8`) THEN REWRITE_TAC[READ_BYTES_BOUND]);;

let BIGNUM_FROM_MEMORY_TRIVIAL = prove
 (`!a s. bignum_from_memory(a,0) s = 0`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH lhand BIGNUM_FROM_MEMORY_BOUND o lhand o snd) THEN
  ARITH_TAC);;

let BIGNUM_FROM_MEMORY = prove
 (`!k a s.
       bignum_from_memory(a,k) s =
       nsum {i | i < k}
            (\i. 2 EXP (64 * i) *
                 val(read (memory :> bytes64(word_add a (word(8 * i)))) s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[bytes64; COMPONENT_COMPOSE_ASSOC] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[asword; through; read; VAL_WORD] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN
  REWRITE_TAC[DIMINDEX_64] THEN REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  SUBST1_TAC(ARITH_RULE `64 = 8 * 8`) THEN REWRITE_TAC[READ_BYTES_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Some stepping and lex comparison theorems                                 *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROM_MEMORY_STEP = prove
 (`!k a s. bignum_from_memory(a,k+1) s =
           bignum_from_memory(a,k) s +
           2 EXP (64 * k) *
           val(read (memory :> bytes64(word_add a (word(8 * k)))) s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory] THEN
  REWRITE_TAC[ARITH_RULE `i:num < k + 1 <=> i = k \/ i < k`] THEN
  REWRITE_TAC[SET_RULE `{x | x = a \/ P x} = a INSERT {x | P x}`] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[READ_COMPONENT_COMPOSE; bytes64] THEN
  REWRITE_TAC[read; through; asword] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC VAL_WORD_EQ THEN
  W(MP_TAC o PART_MATCH lhand READ_BYTES_BOUND o lhand o snd) THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_SING = prove
 (`!a s. bignum_from_memory(a,1) s = val(read (memory :> bytes64 a) s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `1 = 0 + 1`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD_0]);;

let BIGNUM_FROM_MEMORY_MOD = prove
 (`!a k n s. (bignum_from_memory(a,k) s) MOD (2 EXP (64 * n)) =
             bignum_from_memory(a,MIN k n) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory; EXP_MULT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_MOD o lhand o snd) THEN
  REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `i < MIN k n <=> i < k /\ i < n`] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; ARITH_RULE `64 = 8 * 8`] THEN
  REWRITE_TAC[READ_BYTES_BOUND]);;

let BIGNUM_FROM_MEMORY_DIV = prove
 (`!a k n s. (bignum_from_memory(a,k) s) DIV (2 EXP (64 * n)) =
             bignum_from_memory(word_add a (word(8 * n)),k - n) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bignum_from_memory; EXP_MULT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) DIGITSUM_DIV_NUMSEG o lhand o snd) THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE; ARITH_RULE `64 = 8 * 8`] THEN
  REWRITE_TAC[READ_BYTES_BOUND] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; WORD_ADD] THEN REWRITE_TAC[WORD_ADD_AC]);;

let LOWDIGITS_BIGNUM_FROM_MEMORY = prove
 (`!a k n s.
        lowdigits (bignum_from_memory(a,k) s) n =
        bignum_from_memory(a,MIN k n) s`,
  REWRITE_TAC[lowdigits; BIGNUM_FROM_MEMORY_MOD]);;

let HIGHDIGITS_BIGNUM_FROM_MEMORY = prove
 (`!a k n s.
        highdigits (bignum_from_memory(a,k) s) n =
        bignum_from_memory(word_add a (word(8 * n)),k - n) s`,
  REWRITE_TAC[highdigits; BIGNUM_FROM_MEMORY_DIV]);;

let BIGNUM_FROM_MEMORY_SPLIT = prove
 (`!a m n s.
        bignum_from_memory(a,m+n) s =
        2 EXP (64 * m) * bignum_from_memory(word_add a (word(8 * m)),n) s +
        bignum_from_memory(a,m) s`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC(SYM(SPECL [`bignum_from_memory(a,m+n) s`; `2 EXP (64 * m)`]
        (CONJUNCT1 DIVISION_SIMP))) THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_MOD; BIGNUM_FROM_MEMORY_DIV] THEN
  REWRITE_TAC[ADD_SUB2; ARITH_RULE `MIN (m + n) m = m`] THEN ARITH_TAC);;

let BIGDIGIT_BIGNUM_FROM_MEMORY = prove
 (`!k a s i.
      bigdigit (bignum_from_memory(a,k) s) i =
      if i < k then val(read (memory :> bytes64(word_add a (word(8 * i)))) s)
      else 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bigdigit; BIGNUM_FROM_MEMORY_DIV] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 2 EXP (64 * 1)`] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_MOD] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i < k ==> MIN (k - i) 1 = 1`;
               ARITH_RULE `~(i < k) ==> MIN (k - i) 1 = 0`;
               BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY; ARITH_RULE `i < 1 <=> i = 0`] THEN
  REWRITE_TAC[SING_GSPEC; NSUM_SING; MULT_CLAUSES; EXP; WORD_ADD_0]);;

let BIGNUM_FROM_MEMORY_LT_STEP = prove
 (`!k a s n.
        bignum_from_memory(a,k) s < 2 EXP (64 * n) <=>
        k <= n \/
        read (memory :> bytes64(word_add a (word(8 * n)))) s = word 0 /\
        bignum_from_memory(a,k) s < 2 EXP (64 * (n + 1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY] THEN
  REWRITE_TAC[GSYM VAL_EQ_0; GSYM EXP_EXP; GSYM MULT_ASSOC] THEN
  MATCH_MP_TAC DIGITSUM_LT_STEP THEN
  REWRITE_TAC[GSYM DIMINDEX_64; VAL_BOUND] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC NUM_REDUCE_CONV);;

let BIGNUM_FROM_MEMORY_LEXICOGRAPHIC = prove
 (`!k a b s.
        bignum_from_memory(a,k+1) s < bignum_from_memory(b,k+1) s <=>
        val(read (memory :> bytes64(word_add a (word(8 * k)))) s) <
        val(read (memory :> bytes64(word_add b (word(8 * k)))) s) \/
        val(read (memory :> bytes64(word_add a (word(8 * k)))) s) =
        val(read (memory :> bytes64(word_add b (word(8 * k)))) s) /\
        bignum_from_memory(a,k) s < bignum_from_memory(b,k) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_MP_TAC LEXICOGRAPHIC_LT THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BOUND]);;

let BIGNUM_FROM_MEMORY_EXPAND = prove
 (`!k a s. bignum_from_memory(a,k) s =
           if k = 0 then 0 else
           val(read (memory :> bytes64 a) s) +
           2 EXP 64 * bignum_from_memory(word_add a (word 8),k - 1) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BIGNUM_FROM_MEMORY] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
  SUBGOAL_THEN
   `{i | i < k} = 0 INSERT IMAGE (\i. i + 1) {i | i < k - 1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[IN_INSERT; EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    REWRITE_TAC[ARITH_RULE `x = y + 1 <=> y = x - 1 /\ ~(x = 0)`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; ARITH_RULE `~(0 = i + 1)`] THEN
  SIMP_TAC[NSUM_IMAGE; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[MULT_CLAUSES; EXP; WORD_ADD_0] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL] THEN MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[MULT_ASSOC; GSYM(CONJUNCT2 EXP); EXP_MULT; o_DEF] THEN
  REWRITE_TAC[ADD1] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM WORD_ADD_ASSOC; GSYM WORD_ADD] THEN
  REWRITE_TAC[ARITH_RULE `8 + 8 * i = 8 * (i + 1)`]);;

let BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS = prove
 (`!x n a i s.
      bignum_from_memory(x,n) s = highdigits a i <=>
      if n = 0 then a < 2 EXP (64 * i) else
      read(memory :> bytes64 x) s = word(bigdigit a i) /\
      bignum_from_memory(word_add x (word 8),n - 1) s = highdigits a (i + 1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
   [ONCE_REWRITE_RULE[ADD_SYM] BIGNUM_FROM_MEMORY_EXPAND] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MESON_TAC[HIGHDIGITS_EQ_0]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [HIGHDIGITS_STEP] THEN
  SIMP_TAC[LEXICOGRAPHIC_EQ; BIGDIGIT_BOUND; VAL_BOUND_64] THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  MESON_TAC[]);;

let BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS = prove
 (`!x n a i j s.
        bignum_from_memory(word_add x (word (8 * i)),n) s = highdigits a j <=>
        if n = 0 then a < 2 EXP (64 * j) else
        read(memory :> bytes64(word_add x (word(8 * i)))) s =
        word(bigdigit a j) /\
        bignum_from_memory(word_add x (word (8 * (i + 1))),n - 1) s =
        highdigits a (j + 1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add x (word (8 * i))) (word 8) =
    word_add x (word(8 * (i + 1)))`]);;

let BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS_ALT = prove
 (`!x n a i s.
      bignum_from_memory(x,n) s = highdigits a i <=>
      (if n = 0 then a < 2 EXP (64 * i) else
       read(memory :> bytes64 x) s = word(bigdigit a i)) /\
      bignum_from_memory(word_add x (word 8),n - 1) s = highdigits a (i + 1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUB_0; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
  REWRITE_TAC[MESON[] `(p <=> p /\ a = b) <=> p ==> b = a`] THEN
  REWRITE_TAC[HIGHDIGITS_EQ_0] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LTE_TRANS) THEN
  REWRITE_TAC[LE_EXP] THEN ARITH_TAC);;

let BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS_ALT = prove
 (`!x n a i j s.
        bignum_from_memory(word_add x (word (8 * i)),n) s = highdigits a j <=>
        (if n = 0 then a < 2 EXP (64 * j) else
         read(memory :> bytes64(word_add x (word(8 * i)))) s =
         word(bigdigit a j)) /\
        bignum_from_memory(word_add x (word (8 * (i + 1))),n - 1) s =
        highdigits a (j + 1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [BIGNUM_FROM_MEMORY_EQ_HIGHDIGITS_ALT] THEN
  REWRITE_TAC[WORD_RULE
   `word_add (word_add x (word (8 * i))) (word 8) =
    word_add x (word(8 * (i + 1)))`]);;

let BIGNUM_FROM_MEMORY_EQ_LOWDIGITS = prove
 (`!x a n s.
      bignum_from_memory(x,n+1) s = lowdigits a (n+1) <=>
      read (memory :> bytes64 (word_add x (word (8 * n)))) s =
      word(bigdigit a n) /\
      bignum_from_memory(x,n) s = lowdigits a n`,
  REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; LOWDIGITS_CLAUSES] THEN
  ONCE_REWRITE_TAC[ARITH_RULE
   `a + e * b:num = e * c + d <=> e * b + a = e * c + d`] THEN
  SIMP_TAC[LEXICOGRAPHIC_EQ; BIGNUM_FROM_MEMORY_BOUND; LOWDIGITS_BOUND] THEN
  REWRITE_TAC[VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Now a "packaged" version where the first word encodes the size            *)
(* ------------------------------------------------------------------------- *)

let packaged_bignum_from_memory = new_definition
 `packaged_bignum_from_memory a s =
    bignum_from_memory(word_add a (word 8),read (bytes(a,8)) s)`;;

(* ------------------------------------------------------------------------- *)
(* Thanks to little-endian encoding this is true. It's handy to use it since *)
(* we already have some orthogonality infrastructure for "bytes".            *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_FROM_MEMORY_BYTES = prove
 (`!k a. bignum_from_memory(a,k) = read (memory :> bytes(a,8 * k))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  INTRO_TAC "![s]" THEN REWRITE_TAC[bignum_from_memory] THEN
  REWRITE_TAC[READ_COMPONENT_COMPOSE] THEN
  REWRITE_TAC[READ_BYTES; DIMINDEX_64] THEN
  SPEC_TAC(`read memory s`,`m:int64->byte`) THEN GEN_TAC THEN
  REWRITE_TAC[GSYM NSUM_LMUL; EXP_MULT; ARITH_RULE `2 EXP 8 = 256`] THEN
  REWRITE_TAC[ARITH_RULE `2 EXP 64 = 256 EXP 8`] THEN
  REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD; EXP_EXP] THEN
  SIMP_TAC[NSUM_NSUM_PRODUCT; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC [`\(i,j). 8 * i + j`; `\n. n DIV 8,n MOD 8`] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; FORALL_PAIR_THM; WORD_VAL] THEN
  REWRITE_TAC[WORD_ADD; WORD_VAL] THEN REWRITE_TAC[WORD_RULE
   `word_add (word_add x y) z = word_add x (word_add y z)`] THEN
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
  CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; MATCH_MP_TAC DIVMOD_UNIQ THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Passing between alternative byte component formulations.                  *)
(* ------------------------------------------------------------------------- *)

let READ_BYTES_EQ_BYTELIST = prove
 (`!x n k s.
        read (memory :> bytes(x,k)) s = n <=>
        n < 256 EXP k /\
        read (memory :> bytelist(x,k)) s = bytelist_of_num k n`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist; through; read] THEN
  MESON_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; READ_BYTES_BOUND_ALT]);;

let READ_BYTELIST_EQ_BYTES = prove
 (`!x l k s.
        read (memory :> bytelist(x,k)) s = l <=>
        LENGTH l = k /\
        read (memory :> bytes(x,k)) s = num_of_bytelist l`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bytelist; through; read] THEN
  MESON_TAC[NUM_OF_BYTELIST_OF_NUM_EQ; BYTELIST_OF_NUM_OF_BYTELIST;
            READ_BYTES_BOUND_ALT; LENGTH_BYTELIST_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Conversion to expand "bytes_loaded" in 64-bit word assignments.           *)
(* ------------------------------------------------------------------------- *)

let DATA64_CONV =
  let pth = prove
   (`bytes_loaded s (word pc)
      (CONS d0 (CONS d1 (CONS d2 (CONS d3
         (CONS d4 (CONS d5 (CONS d6 (CONS d7 l)))))))) <=>
     read (memory :> bytes64 (word pc)) s =
     word(num_of_bytelist [d0;d1;d2;d3;d4;d5;d6;d7]) /\
     bytes_loaded s (word(pc + 8)) l`,
    SUBST1_TAC(SYM(ISPEC `l:byte list` (CONJUNCT1 APPEND))) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] THEN REWRITE_TAC[CONJUNCT1 APPEND] THEN
    REWRITE_TAC[bytes_loaded_append] THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
    REWRITE_TAC[WORD_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[bytes_loaded; READ_BYTELIST_EQ_BYTES] THEN
    REWRITE_TAC[bytes64; asword; READ_COMPONENT_COMPOSE; through; read] THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD; DIMINDEX_64] THEN
    CONV_TAC SYM_CONV THEN BINOP_TAC THEN MATCH_MP_TAC MOD_LT THEN
    REWRITE_TAC[GSYM(NUM_MULT_CONV `8 * 8`); READ_BYTES_BOUND] THEN
    W(MP_TAC o PART_MATCH lhand NUM_OF_BYTELIST_BOUND o lhand o snd) THEN
    CONV_TAC(ONCE_DEPTH_CONV LENGTH_CONV) THEN ARITH_TAC) in
  let rec conv tm =
   TRY_CONV
    (GEN_REWRITE_CONV I [pth] THENC
    BINOP2_CONV
      (REWRITE_CONV[num_of_bytelist] THENC
       DEPTH_CONV WORD_NUM_RED_CONV)
      (LAND_CONV (RAND_CONV
        (GEN_REWRITE_CONV I [GSYM ADD_ASSOC] THENC
         RAND_CONV NUM_ADD_CONV)) THENC
       conv)) tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Bignum as a state component (little-endian only of course).               *)
(* ------------------------------------------------------------------------- *)

let bignum = define
 `bignum(a:int64,k) = bytes(a,8 * k)`;;

add_component_alias_thms [bignum];;

simulation_precanon_thms :=
  union [bignum; BIGNUM_FROM_MEMORY_BYTES] (!simulation_precanon_thms);;

let BIGNUM_FROM_MEMORY_BIGNUM = prove
 (`!k a. bignum_from_memory(a,k) = read (memory :> bignum(a,k))`,
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; bignum]);;

let READ_BIGNUM_BOUND = prove
 (`(!k a m. read (bignum(a,k)) m < 2 EXP (64 * k)) /\
   (!k a s. read (memory :> bignum(a,k)) s < 2 EXP (64 * k))`,
  REWRITE_TAC[READ_COMPONENT_COMPOSE; bignum] THEN
  SUBST1_TAC(ARITH_RULE `64 = 8 * 8`) THEN
  REWRITE_TAC[READ_BYTES_BOUND; GSYM MULT_ASSOC]);;

let READ_BIGNUM_TRIVIAL = prove
 (`(!a m. read (bignum(a,0)) m = 0) /\
   (!a s. read (memory :> bignum(a,0)) s = 0)`,
  MP_TAC READ_BIGNUM_BOUND THEN MATCH_MP_TAC MONO_AND THEN
  CONJ_TAC THEN DISCH_THEN(MP_TAC o SPEC `0`) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Get ranges of bignum abbreviation out of precondition.                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_TERMRANGE_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND]) in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th ->
        ENSURES_OR_ENSURES_N_TAC
            (REWRITE_TAC[th; ENSURES_TRIVIAL])
            (REWRITE_TAC[th; ENSURES_N_TRIVIAL]) THEN NO_TAC)
     (SPECL [k; m] pth);;

let BIGNUM_RANGE_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND])
  and nty = `:num` in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th -> REWRITE_TAC[th; ENSURES_TRIVIAL] THEN NO_TAC)
     (SPECL [mk_var(k,nty); mk_var(m,nty)] pth);;

(* ------------------------------------------------------------------------- *)
(* Conversion to expand `bignum_from_memory(x,n) s` for specific n           *)
(* into a reasonably naturally normalized sum of 64-bit words.               *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_EXPAND_CONV =
  let pth = prove
   (`bignum_from_memory(x,0) s = 0 /\
     bignum_from_memory(x,SUC n) s =
        nsum(0..n) (\i. 2 EXP (64 * i) *
             val(read(memory :> bytes64(word_add x (word (8 * i)))) s))`,
    REWRITE_TAC[BIGNUM_FROM_MEMORY] THEN
    REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
    REWRITE_TAC[numseg; LT_SUC_LE; LE_0])
  and tth = ARITH_RULE `2 EXP 0 * n = n`
  and address_conv =
   TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV  THENC
   GEN_REWRITE_CONV TRY_CONV [WORD_RULE `word_add z (word 0) = z`] in
  GEN_REWRITE_CONV (TRY_CONV o RATOR_CONV)
    [GSYM BIGNUM_FROM_MEMORY_BIGNUM;
     GSYM BIGNUM_FROM_MEMORY_BYTES] THENC
  (GEN_REWRITE_CONV I [CONJUNCT1 pth] ORELSEC
   (LAND_CONV(RAND_CONV num_CONV) THENC
    GEN_REWRITE_CONV I [CONJUNCT2 pth] THENC
    EXPAND_NSUM_CONV THENC
    DEPTH_BINOP_CONV `(+):num->num->num`
     (BINOP2_CONV
        (RAND_CONV NUM_MULT_CONV)
        (RAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
          (RAND_CONV(RAND_CONV NUM_MULT_CONV) THENC
          address_conv))))) THENC
      GEN_REWRITE_CONV TRY_CONV [tth])));;

(* ------------------------------------------------------------------------- *)
(* Expand a bignum and introduce abbreviations for digits                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_DIGITIZE_TAC =
  let strip_add = striplist (dest_binop `(+):num->num->num`)
  and ty64 = `:int64` in
  fun s tm ->
    let th = BIGNUM_EXPAND_CONV tm in
    let mts = strip_add(rand(concl th)) in
    let tms =
      if mts = [] then [] else map rand ((hd mts)::map rand (tl mts)) in
    let vs =
      map (fun i -> mk_var(s^string_of_int i,ty64)) (0--(length tms - 1)) in
    let abseqs = map2 (curry mk_eq) vs tms in
    SUBST_ALL_TAC th THEN MAP_EVERY ABBREV_TAC abseqs;;

(* ------------------------------------------------------------------------- *)
(* Expansion of bignum_of_wordlist, corresponding digitization variants.     *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_OF_WORDLIST_CONV =
  let [conv_0;conv_1;conv_2;conv_base;conv_step] =
     (map (fun t -> GEN_REWRITE_CONV I [t]) o CONJUNCTS o prove)
   (`bignum_of_wordlist [] = 0 /\
     bignum_of_wordlist [h] = val h /\
     bignum_of_wordlist (CONS h t) =
     val h + 2 EXP 64 * bignum_of_wordlist t /\
     2 EXP n * bignum_of_wordlist [h] = 2 EXP n * val h /\
     2 EXP n * bignum_of_wordlist(CONS h t) =
     2 EXP n * val h + 2 EXP (n + 64) * bignum_of_wordlist t`,
    REWRITE_TAC[bignum_of_wordlist; EXP_ADD] THEN ARITH_TAC) in
    let rec coreconv tm =
      (conv_base ORELSEC
       (conv_step THENC
        RAND_CONV (LAND_CONV(RAND_CONV NUM_ADD_CONV) THENC coreconv))) tm in
    conv_0 ORELSEC conv_1 ORELSEC (conv_2 THENC RAND_CONV coreconv);;

let BIGNUM_OF_WORDLIST_SPLIT_RULE =
  let int64_ty = `:int64`
  and append_tm = `APPEND:int64 list->int64 list->int64 list` in
  fun (m,n) ->
    let vs = map (fun n -> mk_var("x"^string_of_int n,int64_ty)) (1--(m+n)) in
    let vs1,vs2 = chop_list m vs in
    let th = SPECL [mk_list(vs1,int64_ty); mk_list(vs2,int64_ty)]
                   BIGNUM_OF_WORDLIST_APPEND in
    CONV_RULE
     (BINOP2_CONV
       (GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [APPEND])
       (RAND_CONV(LAND_CONV(RAND_CONV
         (GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [LENGTH] THENC
          NUM_REDUCE_CONV))))) th;;

let BIGNUM_LEXPAND_CONV =
  let strip_add = striplist (dest_binop `(+):num->num->num`)
  and ofw_tm = `bignum_of_wordlist`
  and ty64 = `:int64` in
  fun tm ->
    let th = BIGNUM_EXPAND_CONV tm in
    let mts = strip_add(rand(concl th)) in
    let tms =
      if mts = [] then [] else map rand ((hd mts)::map rand (tl mts)) in
    let tm' = mk_comb(ofw_tm,mk_list(tms,ty64)) in
    TRANS th (SYM(BIGNUM_OF_WORDLIST_CONV tm'));;

let BIGNUM_LDIGITIZE_TAC =
  let ty64 = `:int64` in
  fun s tm ->
    let th = BIGNUM_LEXPAND_CONV tm in
    let tms = dest_list(rand(rand(concl th))) in
    let vs =
      map (fun i -> mk_var(s^string_of_int i,ty64)) (0--(length tms - 1)) in
    let abseqs = map2 (curry mk_eq) vs tms in
    SUBST_ALL_TAC th THEN MAP_EVERY ABBREV_TAC abseqs;;

(* ------------------------------------------------------------------------- *)
(* Expansion of bytes by analogy.                                            *)
(* ------------------------------------------------------------------------- *)

let BYTES_EXPAND_CONV =
  let pth = prove
   (`read (memory :> bytes(x,0)) s = 0 /\
     read (memory :> bytes(x,SUC n)) s =
        nsum(0..n) (\i. 2 EXP (8 * i) *
             val(read(memory :> bytes8(word_add x (word i))) s))`,
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_BYTES] THEN
    REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; NSUM_CLAUSES] THEN
    REWRITE_TAC[numseg; LT_SUC_LE; LE_0] THEN
    REWRITE_TAC[READ_BYTES_1; READ_COMPONENT_COMPOSE; bytes8;
                asword; through; read; WORD_VAL])
  and tth = ARITH_RULE `2 EXP 0 * n = n`
  and address_conv =
   TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV  THENC
   GEN_REWRITE_CONV TRY_CONV [WORD_RULE `word_add z (word 0) = z`] in
  (GEN_REWRITE_CONV I [CONJUNCT1 pth] ORELSEC
   (LAND_CONV(funpow 3 RAND_CONV num_CONV) THENC
    GEN_REWRITE_CONV I [CONJUNCT2 pth] THENC
    EXPAND_NSUM_CONV THENC
    DEPTH_BINOP_CONV `(+):num->num->num`
     (BINOP2_CONV
        (RAND_CONV NUM_MULT_CONV)
        (RAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
          address_conv)))) THENC
      GEN_REWRITE_CONV TRY_CONV [tth])));;


let BYTES_DIGITIZE_TAC =
  let strip_add = striplist (dest_binop `(+):num->num->num`)
  and ty8 = `:byte` in
  fun s tm ->
    let th = BYTES_EXPAND_CONV tm in
    let mts = strip_add(rand(concl th)) in
    let tms =
      if mts = [] then [] else map rand ((hd mts)::map rand (tl mts)) in
    let vs =
      map (fun i -> mk_var(s^string_of_int i,ty8)) (0--(length tms - 1)) in
    let abseqs = map2 (curry mk_eq) vs tms in
    SUBST_ALL_TAC th THEN MAP_EVERY ABBREV_TAC abseqs;;


(* ------------------------------------------------------------------------- *)
(* Expansion of bytelist by analogy, occasionally useful for bignums.        *)
(* ------------------------------------------------------------------------- *)

let BYTELIST_EXPAND_CONV =
  let pth = prove
   (`read (memory :> bytelist (x,0)) s = [] /\
     read (memory :> bytelist (x,SUC n)) s =
     CONS (read (memory :> bytes8 x) s)
          (read (memory :> bytelist (word_add x (word 1),n)) s)`,
    REWRITE_TAC[bytelist_clauses; READ_COMPONENT_COMPOSE;
                bytes8; READ_BYTES_1; asword; read; through; WORD_VAL]) in
  let rewr_base = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and rewr_step = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec conv tm =
    (rewr_base ORELSEC
     (LAND_CONV (funpow 3 RAND_CONV num_CONV) THENC
      rewr_step THENC
      RAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV(LAND_CONV
        (TRY_CONV NORMALIZE_RELATIVE_ADDRESS_CONV))))) THENC
      RAND_CONV conv)) tm in
  conv;;

let BYTELIST_DIGITIZE_TAC =
  let ty8 = `:byte` in
  fun s tm ->
    let th = BYTELIST_EXPAND_CONV tm in
    let tms = dest_list(rand(concl th)) in
    let vs =
      map (fun i -> mk_var(s^string_of_int i,ty8)) (0--(length tms - 1)) in
    let abseqs = map2 (curry mk_eq) vs tms in
    SUBST_ALL_TAC th THEN MAP_EVERY ABBREV_TAC abseqs;;

(* ------------------------------------------------------------------------- *)
(* Some general stuff for fiddling with the chunksize for memory             *)
(* ------------------------------------------------------------------------- *)

let READ_MEMORY_MERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let READ_MEMORY_FULLMERGE_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_SPLIT] THENC
    LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV))))) in
  let rec conv tm =
    (baseconv THENC BINOP_CONV(TRY_CONV conv)) tm in
  conv;;

let MEMORY_128_FROM_16_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(16*i) in
      READ_MEMORY_MERGE_CONV 3 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

let MEMORY_128_FROM_64_TAC =
  let a_tm = `a:int64` and n_tm = `n:num` and i64_ty = `:int64`
  and pat = `read (memory :> bytes128(word_add a (word n))) s0` in
  fun v boff n ->
    let pat' = subst[mk_var(v,i64_ty),a_tm] pat in
    let f i =
      let itm = mk_small_numeral(boff + 16*i) in
      READ_MEMORY_MERGE_CONV 1 (subst[itm,n_tm] pat') in
    MP_TAC(end_itlist CONJ (map f (0--(n-1))));;

let READ_MEMORY_SPLIT_CONV =
  let baseconv =
    GEN_REWRITE_CONV I [READ_MEMORY_BYTESIZED_UNSPLIT] THENC
    BINOP_CONV(LAND_CONV(LAND_CONV(RAND_CONV(RAND_CONV
     (TRY_CONV(GEN_REWRITE_CONV I [GSYM WORD_ADD_ASSOC] THENC
               RAND_CONV WORD_ADD_CONV)))))) in
  let rec conv n tm =
    if n = 0 then REFL tm else
    (baseconv THENC BINOP_CONV (conv(n - 1))) tm in
  conv;;

let MEMORY_SPLIT_TAC k =
  let tac =
    STRIP_ASSUME_TAC o
    CONV_RULE (BINOP_CONV(BINOP2_CONV
       (ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) WORD_REDUCE_CONV)) o
    GEN_REWRITE_RULE I [el k (CONJUNCTS READ_MEMORY_BYTESIZED_UNSPLIT)] in
  EVERY_ASSUM (fun th -> try tac th with Failure _ -> ALL_TAC);;
