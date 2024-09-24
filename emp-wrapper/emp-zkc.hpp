#ifndef _CODECPP_
#define _CODECPP_

#ifdef __cplusplus
  #define EXPORT_C extern "C"
#else
  #define EXPORT_C
#endif

#include <stdint.h>
#include <stdbool.h>

//============ C++ Only Header =================//
#ifdef __cplusplus
#include <emp-zk/emp-zk.h>
#include "emp-tool/emp-tool.h"
#include <unordered_map>
#include <variant>

#endif //-- End of __cplusplus definition //

typedef void* empFp; //opaque pointer for IntFp objects
typedef void* arrPtr;

typedef void* hEnv;
typedef void* chPtr; //size_t*


EXPORT_C hEnv init_env(const char* ip, int port, int party, int threads);
EXPORT_C void del_env(hEnv env);

///////////////////////////////////////////////////////
//rust-allocated interface

EXPORT_C void r_int_new(empFp vp, uint64_t a, int party);
EXPORT_C void r_int_mul(empFp a, empFp b, empFp res);
EXPORT_C void r_int_add(empFp a, empFp b, empFp res);
EXPORT_C void r_int_not(empFp a, empFp res);
EXPORT_C void r_int_or(empFp a, empFp b, empFp res);
EXPORT_C void r_int_xor(empFp a, empFp b, empFp res);
EXPORT_C void r_dbg_reveal(empFp a);
EXPORT_C void r_assert_zero(empFp a);
EXPORT_C void r_assert_eq(empFp a,empFp b);
EXPORT_C void r_assert_eq_uints_bools(empFp a, arrPtr arr, uint64_t len, int wire_size);
EXPORT_C void r_copy_val(empFp a, empFp res);
EXPORT_C void r_challenge(chPtr modulus, int modulus_limbs, chPtr out_limbs, int out_elements);

#endif
