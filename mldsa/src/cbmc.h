/*
 * Copyright (c) The mldsa-native project authors
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT
 */

#ifndef MLD_CBMC_H
#define MLD_CBMC_H
/***************************************************
 * Basic replacements for __CPROVER_XXX contracts
 ***************************************************/
#ifndef CBMC

#define __contract__(x)
#define __loop__(x)
#define cassert(x)

#else /* !CBMC */

#include <stdint.h>

#define __contract__(x) x
#define __loop__(x) x

/* https://diffblue.github.io/cbmc/contracts-assigns.html */
#define assigns(...) __CPROVER_assigns(__VA_ARGS__)

/* https://diffblue.github.io/cbmc/contracts-requires-ensures.html */
#define requires(...) __CPROVER_requires(__VA_ARGS__)
#define ensures(...) __CPROVER_ensures(__VA_ARGS__)
/* https://diffblue.github.io/cbmc/contracts-loops.html */
#define invariant(...) __CPROVER_loop_invariant(__VA_ARGS__)
#define decreases(...) __CPROVER_decreases(__VA_ARGS__)
/* cassert to avoid confusion with in-built assert */
#define cassert(x) __CPROVER_assert(x, "cbmc assertion failed")
#define assume(...) __CPROVER_assume(__VA_ARGS__)

/***************************************************
 * Macros for "expression" forms that may appear
 * _inside_ top-level contracts.
 ***************************************************/

/*
 * function return value - useful inside ensures
 * https://diffblue.github.io/cbmc/contracts-functions.html
 */
#define return_value (__CPROVER_return_value)

/*
 * assigns l-value targets
 * https://diffblue.github.io/cbmc/contracts-assigns.html
 */
#define object_whole(...) __CPROVER_object_whole(__VA_ARGS__)
#define memory_slice(...) __CPROVER_object_upto(__VA_ARGS__)
#define same_object(...) __CPROVER_same_object(__VA_ARGS__)

/*
 * Pointer-related predicates
 * https://diffblue.github.io/cbmc/contracts-memory-predicates.html
 */
#define memory_no_alias(...) __CPROVER_is_fresh(__VA_ARGS__)
#define readable(...) __CPROVER_r_ok(__VA_ARGS__)
#define writeable(...) __CPROVER_w_ok(__VA_ARGS__)

/* Maximum supported buffer size
 *
 * Larger buffers may be supported, but due to internal modeling constraints
 * in CBMC, the proofs of memory- and type-safety won't be able to run.
 *
 * If you find yourself in need for a buffer size larger than this,
 * please contact the maintainers, so we can prioritize work to relax
 * this somewhat artificial bound.
 */
#define MLD_MAX_BUFFER_SIZE (SIZE_MAX >> 12)


/*
 * History variables
 * https://diffblue.github.io/cbmc/contracts-history-variables.html
 */
#define old(...) __CPROVER_old(__VA_ARGS__)
#define loop_entry(...) __CPROVER_loop_entry(__VA_ARGS__)

/*
 * Quantifiers
 * Note that the range on qvar is _exclusive_ between qvar_lb .. qvar_ub
 * https://diffblue.github.io/cbmc/contracts-quantifiers.html
 */

/*
 * Prevent clang-format from corrupting CBMC's special ==> operator
 */
/* clang-format off */
#define forall(qvar, qvar_lb, qvar_ub, predicate)                 \
  __CPROVER_forall                                                \
  {                                                               \
    unsigned qvar;                                                \
    ((qvar_lb) <= (qvar) && (qvar) < (qvar_ub)) ==> (predicate)   \
  }

#define exists(qvar, qvar_lb, qvar_ub, predicate)         \
  __CPROVER_exists                                              \
  {                                                             \
    unsigned qvar;                                              \
    ((qvar_lb) <= (qvar) && (qvar) < (qvar_ub)) && (predicate)  \
  }
/* clang-format on */

/***************************************************
 * Convenience macros for common contract patterns
 ***************************************************/

/* Helper to chain conditions with && */
#define _OBJS_NO_ALIAS_1(x) memory_no_alias((x), sizeof(*(x)))
#define _OBJS_NO_ALIAS_2(x, y) \
  (_OBJS_NO_ALIAS_1(x) && _OBJS_NO_ALIAS_1(y))
#define _OBJS_NO_ALIAS_3(x, y, z) \
  (_OBJS_NO_ALIAS_2(x, y) && _OBJS_NO_ALIAS_1(z))
#define _OBJS_NO_ALIAS_4(x, y, z, w) \
  (_OBJS_NO_ALIAS_3(x, y, z) && _OBJS_NO_ALIAS_1(w))
#define _OBJS_NO_ALIAS_5(x, y, z, w, v) \
  (_OBJS_NO_ALIAS_4(x, y, z, w) && _OBJS_NO_ALIAS_1(v))
#define _OBJS_NO_ALIAS_6(x, y, z, w, v, u) \
  (_OBJS_NO_ALIAS_5(x, y, z, w, v) && _OBJS_NO_ALIAS_1(u))
#define _OBJS_NO_ALIAS_7(x, y, z, w, v, u, t) \
  (_OBJS_NO_ALIAS_6(x, y, z, w, v, u) && _OBJS_NO_ALIAS_1(t))
#define _OBJS_NO_ALIAS_8(x, y, z, w, v, u, t, s) \
  (_OBJS_NO_ALIAS_7(x, y, z, w, v, u, t) && _OBJS_NO_ALIAS_1(s))
#define _OBJS_NO_ALIAS_9(x, y, z, w, v, u, t, s, r) \
  (_OBJS_NO_ALIAS_8(x, y, z, w, v, u, t, s) && _OBJS_NO_ALIAS_1(r))
#define _OBJS_NO_ALIAS_10(x, y, z, w, v, u, t, s, r, q) \
  (_OBJS_NO_ALIAS_9(x, y, z, w, v, u, t, s, r) && _OBJS_NO_ALIAS_1(q))

#define _GET_OBJS_MACRO(_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,NAME,...) NAME
#define objs_no_alias(...) \
  _GET_OBJS_MACRO(__VA_ARGS__, _OBJS_NO_ALIAS_10, _OBJS_NO_ALIAS_9, \
    _OBJS_NO_ALIAS_8, _OBJS_NO_ALIAS_7, _OBJS_NO_ALIAS_6, \
    _OBJS_NO_ALIAS_5, _OBJS_NO_ALIAS_4, _OBJS_NO_ALIAS_3, \
    _OBJS_NO_ALIAS_2, _OBJS_NO_ALIAS_1)(__VA_ARGS__)

#define _ARRAYS_NO_ALIAS_1(x, sz) memory_no_alias((x), (sz))
#define _ARRAYS_NO_ALIAS_2(x0, sz0, x1, sz1) \
  (_ARRAYS_NO_ALIAS_1(x0, sz0) && _ARRAYS_NO_ALIAS_1(x1, sz1))
#define _ARRAYS_NO_ALIAS_3(x0, sz0, x1, sz1, x2, sz2) \
  (_ARRAYS_NO_ALIAS_2(x0, sz0, x1, sz1) && _ARRAYS_NO_ALIAS_1(x2, sz2))
#define _ARRAYS_NO_ALIAS_4(x0, sz0, x1, sz1, x2, sz2, x3, sz3) \
  (_ARRAYS_NO_ALIAS_3(x0, sz0, x1, sz1, x2, sz2) && \
   _ARRAYS_NO_ALIAS_1(x3, sz3))
#define _ARRAYS_NO_ALIAS_5(x0, sz0, x1, sz1, x2, sz2, x3, sz3, x4, sz4) \
  (_ARRAYS_NO_ALIAS_4(x0, sz0, x1, sz1, x2, sz2, x3, sz3) && \
   _ARRAYS_NO_ALIAS_1(x4, sz4))

#define _GET_ARRAYS_MACRO(_1,_2,_3,_4,_5,_6,_7,_8,_9,_10,NAME,...) NAME
#define arrays_no_alias(...) \
  _GET_ARRAYS_MACRO(__VA_ARGS__, _ARRAYS_NO_ALIAS_5, _dummy, \
    _ARRAYS_NO_ALIAS_4, _dummy, _ARRAYS_NO_ALIAS_3, _dummy, \
    _ARRAYS_NO_ALIAS_2, _dummy, _ARRAYS_NO_ALIAS_1)(__VA_ARGS__)

/* Helper to chain assigns clauses */
#define _ASSIGNS_OBJS_1(x) assigns(memory_slice((x), sizeof(*(x))))
#define _ASSIGNS_OBJS_2(x, y) _ASSIGNS_OBJS_1(x) _ASSIGNS_OBJS_1(y)
#define _ASSIGNS_OBJS_3(x, y, z) \
  _ASSIGNS_OBJS_2(x, y) _ASSIGNS_OBJS_1(z)
#define _ASSIGNS_OBJS_4(x, y, z, w) \
  _ASSIGNS_OBJS_3(x, y, z) _ASSIGNS_OBJS_1(w)
#define _ASSIGNS_OBJS_5(x, y, z, w, v) \
  _ASSIGNS_OBJS_4(x, y, z, w) _ASSIGNS_OBJS_1(v)
#define _ASSIGNS_OBJS_6(x, y, z, w, v, u) \
  _ASSIGNS_OBJS_5(x, y, z, w, v) _ASSIGNS_OBJS_1(u)
#define _ASSIGNS_OBJS_7(x, y, z, w, v, u, t) \
  _ASSIGNS_OBJS_6(x, y, z, w, v, u) _ASSIGNS_OBJS_1(t)
#define _ASSIGNS_OBJS_8(x, y, z, w, v, u, t, s) \
  _ASSIGNS_OBJS_7(x, y, z, w, v, u, t) _ASSIGNS_OBJS_1(s)

#define assigns_objs(...) \
  _GET_OBJS_MACRO(__VA_ARGS__, _dummy, _dummy, _ASSIGNS_OBJS_8, \
    _ASSIGNS_OBJS_7, _ASSIGNS_OBJS_6, _ASSIGNS_OBJS_5, \
    _ASSIGNS_OBJS_4, _ASSIGNS_OBJS_3, _ASSIGNS_OBJS_2, \
    _ASSIGNS_OBJS_1)(__VA_ARGS__)

#define _ASSIGNS_ARRS_1(x, sz) assigns(memory_slice((x), (sz)))
#define _ASSIGNS_ARRS_2(x0, sz0, x1, sz1) \
  _ASSIGNS_ARRS_1(x0, sz0) _ASSIGNS_ARRS_1(x1, sz1)
#define _ASSIGNS_ARRS_3(x0, sz0, x1, sz1, x2, sz2) \
  _ASSIGNS_ARRS_2(x0, sz0, x1, sz1) _ASSIGNS_ARRS_1(x2, sz2)
#define _ASSIGNS_ARRS_4(x0, sz0, x1, sz1, x2, sz2, x3, sz3) \
  _ASSIGNS_ARRS_3(x0, sz0, x1, sz1, x2, sz2) _ASSIGNS_ARRS_1(x3, sz3)
#define _ASSIGNS_ARRS_5(x0, sz0, x1, sz1, x2, sz2, x3, sz3, x4, sz4) \
  _ASSIGNS_ARRS_4(x0, sz0, x1, sz1, x2, sz2, x3, sz3) \
  _ASSIGNS_ARRS_1(x4, sz4)

#define assigns_arrs(...) \
  _GET_ARRAYS_MACRO(__VA_ARGS__, _ASSIGNS_ARRS_5, _dummy, \
    _ASSIGNS_ARRS_4, _dummy, _ASSIGNS_ARRS_3, _dummy, \
    _ASSIGNS_ARRS_2, _dummy, _ASSIGNS_ARRS_1)(__VA_ARGS__)

/*
 * Prevent clang-format from corrupting CBMC's special ==> operator
 */
/* clang-format off */
#define CBMC_CONCAT_(left, right) left##right
#define CBMC_CONCAT(left, right) CBMC_CONCAT_(left, right)

#define array_bound_core(qvar, qvar_lb, qvar_ub, array_var,            \
                         value_lb, value_ub)                           \
  __CPROVER_forall                                                     \
  {                                                                    \
    unsigned qvar;                                                     \
    ((qvar_lb) <= (qvar) && (qvar) < (qvar_ub)) ==>                    \
        (((int)(value_lb) <= ((array_var)[(qvar)])) &&		       \
         (((array_var)[(qvar)]) < (int)(value_ub)))		       \
  }

#define array_bound(array_var, qvar_lb, qvar_ub, value_lb, value_ub) \
  array_bound_core(CBMC_CONCAT(_cbmc_idx, __COUNTER__), (qvar_lb),      \
      (qvar_ub), (array_var), (value_lb), (value_ub))

#define array_unchanged_core(qvar, qvar_lb, qvar_ub, array_var)        \
  __CPROVER_forall                                                     \
  {                                                                    \
    unsigned qvar;                                                     \
    ((qvar_lb) <= (qvar) && (qvar) < (qvar_ub)) ==>                    \
    ((array_var)[(qvar)]) == (old(* (int16_t (*)[(qvar_ub)])(array_var)))[(qvar)] \
  }

#define array_unchanged(array_var, N) \
    array_unchanged_core(CBMC_CONCAT(_cbmc_idx, __COUNTER__), 0, (N), (array_var))

#define array_unchanged_u64_core(qvar, qvar_lb, qvar_ub, array_var)        \
  __CPROVER_forall                                                     \
  {                                                                    \
    unsigned qvar;                                                     \
    ((qvar_lb) <= (qvar) && (qvar) < (qvar_ub)) ==>                    \
    ((array_var)[(qvar)]) == (old(* (uint64_t (*)[(qvar_ub)])(array_var)))[(qvar)] \
  }

#define array_unchanged_u64(array_var, N) \
    array_unchanged_u64_core(CBMC_CONCAT(_cbmc_idx, __COUNTER__), 0, (N), (array_var))
/* clang-format on */

/* Wrapper around array_bound operating on absolute values.
 *
 * The absolute value bound `k` is exclusive.
 *
 * Note that since the lower bound in array_bound is inclusive, we have to
 * raise it by 1 here.
 */
#define array_abs_bound(arr, lb, ub, k) \
  array_bound((arr), (lb), (ub), -((int)(k)) + 1, (k))

#endif /* CBMC */

#endif /* !MLD_CBMC_H */
