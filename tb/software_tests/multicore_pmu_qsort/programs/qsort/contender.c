#include <stdlib.h>
#include <stdint.h>

//ICACHE L1
#define L1I_WAYS 4
#define L1I_SETS 64
#define L1I_LINE 128/8*4 //bytes
#define L1I_SIZE L1_WAYS*L1_SETS*L1_LINE //bytes

//DCACHE L1
#define L1D_WAYS 4
#define L1D_SETS 64
#define L1D_LINE 128/8*4 //bytes
#define L1D_SIZE L1_WAYS*L1_SETS*L1_LINE //bytes

//CACHE L2
//Write alocate
//Inclusive, L2 evicts L1
//Interleaved access to the banks
//Replace policy, random
#define L2_BANKS 2
#define L2_WAYS 8
#define L2_SETS 256
#define L2_LINE 128/8*4 //bytes
#define L2_SIZE L2_BANKS*L2_WAYS*L2_SETS*L2_LINE //bytes

//Strides
#define L1D_WAY_STRIDE = L1D_SIZE/L1D_WAYS
#define L1D_LINE_STRIDE = L1D_LINE

#define L2_WAY_STRIDE = L2_SIZE/L2_WAYS
#define L2_LINE_STRIDE = L2_LINE

//Range of addresses were mem ops are issued shall be the size of L2
#define RANGE = L2_SIZE
//Define iterations assembly loop
#define iterations 1000

/*
//Generate an array with the range of memory that we want to acces
void gen_acces_seq(void){
//To get the full Range of stores in L2
//Way stride = 8192 bytes 2048 32b words, Offset Address 0x00 to 0x800 | 2048
//Line stride = 16 bytes  4 words, Offset Address  0x00 to 0xc


//L2 size = 65536 bytes .  6384 32b words, Offset Address 0x00 to 0x18f0 | 6384
    uint32_t array_size= 6384;// number of words 
    uint32_t [array_size] array;//define array of addresses
    //fill all the array
    array[0]=0;
    for (int i=1; i<array_size; i++){
        array[i] = array[i-1]+L2_LINE_STRIDE; 
    }

}*/


void cont_hitL2_load(void)
{
    asm (
      "addi t0, x0, 8" "\n\t" //since L2_WAYS happen to be 2048bytes each
//      "lui t1, 1" "\n\t"//place initial adress for t1 = 0xF000
      "lui t1, 0x70000" "\n\t"//place initial adress for t1 = 0xF000
      "cont_start:"  "\n\t"
      "lw a0, 0(t1)"  "\n\t"
      "lw a0, 64(t1)"  "\n\t"
      "lw a0, 128(t1)"  "\n\t"
      "lw a0, 192(t1)"  "\n\t"
      "lw a0, 256(t1)"  "\n\t"
      "lw a0, 320(t1)"  "\n\t"
      "lw a0, 384(t1)"  "\n\t"
      "lw a0, 448(t1)"  "\n\t"
      "lw a0, 512(t1)"  "\n\t"
      "lw a0, 576(t1)"  "\n\t"
      "lw a0, 640(t1)"  "\n\t"
      "lw a0, 704(t1)"  "\n\t"
      "lw a0, 768(t1)"  "\n\t"
      "lw a0, 832(t1)"  "\n\t"
      "lw a0, 896(t1)"  "\n\t"
      "lw a0, 960(t1)"  "\n\t"
      "lw a0, 1024(t1)"  "\n\t"
      "lw a0, 1088(t1)"  "\n\t"
      "lw a0, 1152(t1)"  "\n\t"
      "lw a0, 1216(t1)"  "\n\t"
      "lw a0, 1280(t1)"  "\n\t"
      "lw a0, 1344(t1)"  "\n\t"
      "lw a0, 1408(t1)"  "\n\t"
      "lw a0, 1472(t1)"  "\n\t"
      "lw a0, 1536(t1)"  "\n\t"
      "lw a0, 1600(t1)"  "\n\t"
      "lw a0, 1664(t1)"  "\n\t"
      "lw a0, 1728(t1)"  "\n\t"
      "lw a0, 1792(t1)"  "\n\t"
      "lw a0, 1856(t1)"  "\n\t"
      "lw a0, 1920(t1)"  "\n\t"
      "lw a0, 1984(t1)"  "\n\t"
      "addi t1, t1, -2048" "\n\t"
      "addi t0, t0, -1" "\n\t"
      "bgtz t0, cont_start" "\n\t"
      );
}


