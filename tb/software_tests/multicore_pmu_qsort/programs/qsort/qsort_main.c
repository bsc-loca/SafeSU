// See LICENSE for license details.

//**************************************************************************
// Quicksort benchmark
//--------------------------------------------------------------------------
//
// This benchmark uses quicksort to sort an array of integers. The
// implementation is largely adapted from Numerical Recipes for C. The
// input data (and reference data) should be generated using the
// qsort_gendata.pl perl script and dumped to a file named
// dataset1.h The smips-gcc toolchain does not support system calls
// so printf's can only be used on a host system, not on the smips
// processor simulator itself. You should not change anything except
// the HOST_DEBUG and PREALLOCATE macros for your timing run.

#include "util.h"
#include <string.h>
#include <assert.h>
#include <PMU.h>
#ifdef __UART__  
#include "uart.h"
#endif           
                 

// The INSERTION_THRESHOLD is the size of the subarray when the
// algorithm switches to using an insertion sort instead of
// quick sort.

#define INSERTION_THRESHOLD 10

// NSTACK is the required auxiliary storage.
// It must be at least 2*lg(DATA_SIZE)

#define NSTACK 50

//--------------------------------------------------------------------------
// Input/Reference Data

#define type int
#include "dataset1.h"

// Swap macro for swapping two values.

#define SWAP(a,b) do { typeof(a) temp=(a);(a)=(b);(b)=temp; } while (0)
#define SWAP_IF_GREATER(a, b) do { if ((a) > (b)) SWAP(a, b); } while (0)

//--------------------------------------------------------------------------
//multicore chunks
void contender_loop(uint32_t entry, uint32_t exit,uint32_t aligment){
    volatile uint32_t *var;
    volatile uint32_t reader;
    #ifdef __UART__
    ee_printf("\n *** Memory dump***\n\n");
    #endif
    for(uint32_t i=entry;i<exit+4;i=i+aligment){
        var=(uint32_t*)(i);
        reader=*var;
        #ifdef __UART__
        ee_printf("addres:%x \n",i);
        ee_printf("value :%d \n",reader);
        #endif
    }
    #ifdef __UART__
    ee_printf("\n *** END DUMP ***\n\n");
    #endif
}

void contender(void){
#ifdef __UART__
    ee_printf("\n ***load_contender***\n\n");
#endif
contender_loop(0x4000,0x16000,0x2000);

}


void thread_entry(int cid, int nc)
{
  if (cid > 0){
    while(1){
ub_dpath_01_01_03_run(ub_dpath_01_01_03_init());
//        contender();
    }
  }
}
//multicore chunks end
//--------------------------------------------------------------------------
// Quicksort function

static void insertion_sort(size_t n, type arr[])
{
  type *i, *j;
  type value;
  for (i = arr+1; i < arr+n; i++)
  {
    value = *i;
    j = i;
    while (value < *(j-1))
    {
      *j = *(j-1);
      if (--j == arr)
        break;
    }
    *j = value;
  }
}

static void selection_sort(size_t n, type arr[])
{
  for (type* i = arr; i < arr+n-1; i++)
    for (type* j = i+1; j < arr+n; j++)
      SWAP_IF_GREATER(*i, *j);
}

void sort(size_t n, type arr[])
{
  type* ir = arr+n;
  type* l = arr+1;
  type* stack[NSTACK];
  type** stackp = stack;

  for (;;)
  {
#if HOST_DEBUG
    printArray( "", n, arr );
#endif

    // Insertion sort when subarray small enough.
    if ( ir-l < INSERTION_THRESHOLD )
    {
      insertion_sort(ir - l + 1, l - 1);

      if ( stackp == stack ) break;

      // Pop stack and begin a new round of partitioning.
      ir = *stackp--;
      l = *stackp--;
    }
    else
    {
      // Choose median of left, center, and right elements as
      // partitioning element a. Also rearrange so that a[l-1] <= a[l] <= a[ir-].
      SWAP(arr[((l-arr) + (ir-arr))/2-1], l[0]);
      SWAP_IF_GREATER(l[-1], ir[-1]);
      SWAP_IF_GREATER(l[0], ir[-1]);
      SWAP_IF_GREATER(l[-1], l[0]);

      // Initialize pointers for partitioning.
      type* i = l+1;
      type* j = ir;

      // Partitioning element.
      type a = l[0];

      for (;;) {                    // Beginning of innermost loop.
        while (*i++ < a);           // Scan up to find element > a.
        while (*(j-- - 2) > a);     // Scan down to find element < a.
        if (j < i) break;           // Pointers crossed. Partitioning complete.
        SWAP(i[-1], j[-1]);         // Exchange elements.
      }                             // End of innermost loop.

      // Insert partitioning element.
      l[0] = j[-1];
      j[-1] = a;
      stackp += 2;

      // Push pointers to larger subarray on stack,
      // process smaller subarray immediately.

#if HOST_DEBUG
      assert(stackp < stack+NSTACK);
#endif

      if ( ir-i+1 >= j-l )
      {
        stackp[0] = ir;
        stackp[-1] = i;
        ir = j-1;
      }
      else
      {
        stackp[0] = j-1;
        stackp[-1] = l;
        l = i;
      }
    }
  }
}

//--------------------------------------------------------------------------
// Main

int main( int argc, char* argv[] )
{
  // Output the input array
  printArray( "input", DATA_SIZE, input_data );
  printArray( "verify", DATA_SIZE, verify_data );

#if PREALLOCATE
  // If needed we preallocate everything in the caches
  sort(DATA_SIZE, verify_data);
  if (verify(DATA_SIZE, input_data, input_data))
    return 1;
#endif
#ifdef __UART__
    uart_init();
#endif/*
    uint32_t *var;
    var=(uint32_t*)(0x8002004c);
    *var=1;*/
enable_PMU_32b();

  // Do the sort
  setStats(1);
  sort( DATA_SIZE, input_data );
  setStats(0);

  // Print out the results
  printArray( "test", DATA_SIZE, input_data );
disable_PMU_32b();
  // Check the results
  return verify( DATA_SIZE, input_data, verify_data );
}