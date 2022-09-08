
#include "ubs.h"

// Hardware specific constants
#define LINE_SIZE 32
#define L1_CACHE_SIZE (16*1024)
//SELENE
#define L2_CACHE_SIZE (1024*1024)
//DERISC
//#define L2_CACHE_SIZE (256*1024)


#define	GET_x2(x)		x	x
#define	GET_x5(x)		x	x	x	x	x
#define	GET_x10(x)		GET_x2(GET_x5(x))
#define	GET_x100(x)		GET_x10(GET_x10(x))
#define	GET_x1K(x)		GET_x100(GET_x10(x))
#define	GET_x10K(x)		GET_x1K(GET_x10(x))

#define	GET_x4(x)		GET_x2(GET_x2(x))
#define	GET_x8(x)		GET_x2(GET_x4(x))
#define	GET_x16(x)		GET_x2(GET_x8(x))
#define	GET_x32(x)		GET_x2(GET_x16(x))
#define	GET_x64(x)		GET_x2(GET_x32(x))
#define	GET_x128(x)		GET_x2(GET_x64(x))

#define	GET_x128K(x)	GET_x128(GET_x1K(x))

#define	GET_x12K8(x)	GET_x128(GET_x100(x))


// Test specific constants
#define ITER_COUNT          1280

// In each loop iteration we perform ITER_COUNT ld/st for each cache line
#define ITERATION_INCREMENT (LINE_SIZE*ITER_COUNT)

// Stringification for the Macros
#define STR1(x) #x
#define STR(x) STR1(x)

void ub_ld_l1hit(void *p){    
  __asm__ volatile  (
    ".rept " STR(ITER_COUNT) "\n\t"
    "ld %0, (%1)              \n\t"
    ".endr                    \n\t"    
    "ret                    \n\t"
  :: "r"(0), "r"(p));

  __asm__ volatile (
    ".4byte 0x0b5cca05    \n\t"
    ::);  
}

void ub_st_l1hit(void *p) {
  __asm__ __volatile__ (    
    "ld %0, (%1)              \n\t"                
    ".rept " STR(ITER_COUNT) "\n\t"
    "sd %0, (%1)              \n\t"
    ".endr                    \n\t"
    :: "r"(0), "r"(p));

      __asm__ volatile (
    ".4byte 0x0b5cca05    \n\t"
    ::);  
}

const ub_t ubs[] = {
    {    ub_ld_l1hit,    "ub_ld_l1hit"  },
    {    ub_st_l1hit,    "ub_st_l1hit"  },
};

const int ubs_size = sizeof(ubs)/sizeof(ubs[0]);

