#include "emp-zkc.hpp"

#include "emp-zk/emp-zk.h"
#include "emp-tool/emp-tool.h"
#include <unordered_map>
#include <variant>

static IntFp ONE_FP;

EXPORT_C hEnv init_env(const char* ip, int port, int party, int threads){
    using BoolIOPtr = BoolIO<NetIO>*;
    auto ios = new BoolIOPtr[threads];

    for(int i = 0; i < threads; ++i)
        ios[i] = new BoolIO<NetIO>(new NetIO(party == ALICE?nullptr:ip,port+i), party==ALICE);
    setup_zk_arith<BoolIO<NetIO>>(ios, threads, party);
    ONE_FP = IntFp(1,PUBLIC);
    return ios;
}

EXPORT_C void del_env(hEnv env){
    finalize_zk_arith<BoolIO<NetIO>>();
    using BoolIOPtr = BoolIO<NetIO>*;
    auto envPtr = reinterpret_cast<BoolIOPtr*>(env);
    delete envPtr;
    std::cout << "Backend completed successfully." << std::endl;
}

EXPORT_C void r_int_new(empFp vp, uint64_t a, int party){
    auto ptr = reinterpret_cast<IntFp*>(vp);
    *ptr = IntFp(a,party);
}

EXPORT_C void r_int_mul(empFp a, empFp b, empFp res){
    auto ap = reinterpret_cast<const IntFp*>(a);
    auto bp = reinterpret_cast<const IntFp*>(b);
    *reinterpret_cast<IntFp*>(res) = (*ap)*(*bp);
}

EXPORT_C void r_int_add(empFp a, empFp b, empFp res){
    auto ap = reinterpret_cast<const IntFp*>(a);
    auto bp = reinterpret_cast<const IntFp*>(b);
    *reinterpret_cast<IntFp*>(res) = (*ap)+(*bp);
}

EXPORT_C void r_dbg_reveal(empFp a){
    auto ap = reinterpret_cast<IntFp*>(a);
    std::cout << "I was: " << (*ap).reveal() << std::endl;
}

EXPORT_C void r_assert_zero(empFp a){
    auto ap = reinterpret_cast<IntFp*>(a);
    (*ap).reveal(0);
}

EXPORT_C void r_int_sub(empFp a, empFp b, empFp res){
    auto ap = reinterpret_cast<const IntFp*>(a);
    auto bp = reinterpret_cast<IntFp*>(b);
    *reinterpret_cast<IntFp*>(res) = (*ap)+(*bp).negate();
}

EXPORT_C void r_int_not(empFp a, empFp res){
    //not := (public)1 - (private)x
    auto ap = reinterpret_cast<IntFp*>(a);
    *reinterpret_cast<IntFp*>(res) = ONE_FP + (*ap).negate();
}

IntFp or_internal(IntFp &a, IntFp &b) {
    return ONE_FP + ((ONE_FP + a.negate()) * (ONE_FP + b.negate())).negate();
}

EXPORT_C void r_int_or(empFp a, empFp b, empFp res){
    auto ap = reinterpret_cast<IntFp*>(a);
    auto bp = reinterpret_cast<IntFp*>(b);
    // 1 - (1-a)*(1-b)
    *reinterpret_cast<IntFp*>(res) = or_internal(*ap,*bp);
}

//using the disjunctive form of xor because or is computationally heavier than and
//(!a * b) + (!b * a)
EXPORT_C void r_int_xor(empFp a, empFp b, empFp res){
    auto ap = reinterpret_cast<IntFp*>(a);
    auto bp = reinterpret_cast<IntFp*>(b);
    auto a_negated = ONE_FP + (*ap).negate(); // !a
    auto b_negated = ONE_FP + (*bp).negate(); // !b
    auto first_disjunct  = a_negated * (*bp); // !a * b
    auto second_disjunct = b_negated * (*ap); // !b * a
    *reinterpret_cast<IntFp*>(res) = or_internal(first_disjunct,second_disjunct);
}

EXPORT_C void r_assert_eq(empFp a,empFp b) {
    auto ap = reinterpret_cast<IntFp*>(a);
    auto bp = reinterpret_cast<IntFp*>(b);
    auto diff = (*ap) + (*bp).negate();
    diff.reveal(0);
}

EXPORT_C void r_copy_val(empFp a, empFp res) {
    auto ap = reinterpret_cast<const IntFp*>(a);
    *reinterpret_cast<IntFp*>(res) = (*ap)*ONE_FP;
}

/*
Sum and Pow are prover domain variables where the initial value is known to the verifier (they can read this code)
Two is a public constant for exponentiation of pow.
As sum gets incremented by [secret bit i]*2^i, the new value remains hidden from the verifier as sum is in prover domain.
*/
EXPORT_C void r_assert_eq_uints_bools(empFp a, arrPtr arr, uint64_t len, int wire_size){
    auto ap = reinterpret_cast<const IntFp*>(a);

    auto sum = IntFp(0,ALICE);
    auto pow = IntFp(1,ALICE);
    auto two = IntFp(2,PUBLIC);

    for(int i = 0; i < len ; i++){
        auto it = *reinterpret_cast<IntFp**>(arr + i*wire_size);
        sum = sum + pow*(*it);
        pow = pow*two;
    }

    auto diff = (*ap) + sum.negate();
    diff.reveal(0);
}

/*
    Challenges are added to a buffer in TA1 and popped back to front. This
    function is called when the buffer is empty.

    Modulus : size_t* pointer to limbs of the Rust num_bigint containing the modulus
    modulus_limbs : number of limbs in both modulus and out_limbs
    out_limbs : size_t* pointer to an already allocated section of memory where to write the output
    out_limbs length is assumed to be modulus_limbs*out_elements
    out_elements : number of field elements to output into out_limbs

    Field elements that are multiple limbs large are in little endian order.
    Can currently assume that the only modulus used is F61p    
*/
EXPORT_C void r_challenge(chPtr modulus, int modulus_limbs, chPtr out_limbs, int out_elements){
    //TODO [emp]: Implement me 
    auto modulus_pointer = reinterpret_cast<size_t*>(modulus);
    auto output_pointer = reinterpret_cast<size_t*>(out_limbs);

    output_pointer[0] = 24601;
    for(int i = 1; i < out_elements*modulus_limbs; i++){
        output_pointer[i] = i;
    }
}
