/** @file csr.h
 *  @brief Functions to manager csr interrupts registers.
 *
 *  @author Juan C. Rodriguez (jrodrig9)
 *  @copyright Barcelona Supercomputing Center. All rights reserved.
 *  @bug None.
 *  @doc https://people.eecs.berkeley.edu/~krste/papers/riscv-privileged-v1.9.1.pdf
 */

#ifndef CSR_H
#define CSR_H

#if __riscv_xlen==32
typedef uint32_t uint_xlen_t;
typedef uint32_t uint_csr32_t;
typedef uint32_t uint_csr64_t;
#elif __riscv_xlen==64
typedef uint64_t uint_xlen_t;
typedef uint32_t uint_csr32_t;
typedef uint64_t uint_csr64_t;
#else
#endif

/********************************************************************
* Machine
*********************************************************************/

#define MSTATUS_MIE_BIT_MASK     0x8
#define MIE_MEIE_BIT_MASK     0x800

/**
 * @brief Read csr machine register mhartid.
 *
 * @return saved value in the register as a uint_xlen_t.
 */

static inline uint_xlen_t  csr_read_mhartid(void)
{
    uint_xlen_t  value;
    __asm__ volatile ("csrr    %0, mhartid"
    : "=r" (value)  /* output : register */
    : /* input : none */
    : /* clobbers: none */);
    return value;
}
/**
 * @brief Read csr machine register mstatus.
 *
 * @return Saved value in the register as a uint_xlen_t.
 */
static inline uint_xlen_t  csr_read_mstatus(void)
{
    uint_xlen_t  value;
    __asm__ volatile ("csrr    %0, mstatus"
    : "=r" (value)  /* output : register */
    : /* input : none */
    : /* clobbers: none */);
    return value;
}
/**
 * @brief Write csr machine register mstatus.
 *
 * @param value - Data to saved inside the register.
 */
static inline void csr_write_mstatus(uint_xlen_t   value)
{
    __asm__ volatile ("csrrw    zero, mstatus, %0"
    : /* output: none */
    : "r" (value)  /* input : register */
    : /* clobbers: none */);
}
/**
 * @brief Clear csr machine register mstatus using a mask.
 *
 * @param mask - Mask with the bits to modify.
 */
static inline void csr_clr_bits_mstatus(uint_xlen_t   mask)
{
    __asm__ volatile ("csrrc    zero, mstatus, %0"
    : /* output: none */
    : "r" (mask)  /* input : register */
    : /* clobbers: none */);
}
/**
 * @brief Set csr machine register mstatus using a mask.
 *
 * @param mask - Mask with the bits to modify.
 */
static inline void csr_set_bits_mstatus(uint_xlen_t  mask)
{
    __asm__ volatile ("csrrs    zero, mstatus, %0"
    : /* output: none */
    : "r" (mask)  /* input : register */
    : /* clobbers: none */);
}
/**
 * @brief Read csr machine register mie.
 *
 * @return Saved value in the register as a uint_xlen_t.
 */
static inline uint_xlen_t  csr_read_mie(void)
{
    uint_xlen_t  value;
    __asm__ volatile ("csrr    %0, mie"
    : "=r" (value)  /* output : register */
    : /* input : none */
    : /* clobbers: none */);
    return value;
}
/**
 * @brief Write csr machine register mie.
 *
 * @param value - Data to saved inside the register.
 */
static inline void csr_write_mie(uint_xlen_t  value)
{
    __asm__ volatile ("csrw    mie, %0"
    : /* output: none */
    : "r" (value) /* input : from register */
    : /* clobbers: none */);
}
/**
 * @brief Clear csr machine register mie using a mask.
 *
 * @param mask - Mask with the bits to modify.
 */
static inline void csr_clr_bits_mie(uint_xlen_t   mask)
{
    __asm__ volatile ("csrrc    zero, mie, %0"
    : /* output: none */
    : "r" (mask)  /* input : register */
    : /* clobbers: none */);
}
/**
 * @brief Set csr machine register mie using a mask.
 *
 * @param mask - Mask with the bits to modify.
 */
static inline void csr_set_bits_mie(uint_xlen_t  mask)
{
    __asm__ volatile ("csrrs    zero, mie, %0"
    : /* output: none */
    : "r" (mask)  /* input : register */
    : /* clobbers: none */);
}
/**
 * @brief Read csr machine register mtvec.
 *
 * @return Saved value in the register as a uint_xlen_t.
 */
static inline uint_xlen_t  csr_read_mtvec(void)
{
    uint_xlen_t  value;
    __asm__ volatile ("csrr    %0, mtvec"
    : "=r" (value)  /* output : register */
    : /* input : none */
    : /* clobbers: none */);
    return value;
}
/**
 * @brief Write csr machine register mtvec.
 *
 * @param value - Data to saved inside the register.
 */
static inline void csr_write_mtvec(uint_xlen_t  value)
{
    __asm__ volatile ("csrw    mtvec, %0"
    : /* output: none */
    : "r" (value) /* input : from register */
    : /* clobbers: none */);
}
/**
 * @brief Read csr machine register mcause.
 *
 * @return Saved value in the register as a uint_xlen_t.
 */
static inline uint_xlen_t  csr_read_mcause(void) {
    uint_xlen_t  value;
    __asm__ volatile ("csrr    %0, mcause"
    : "=r" (value)  /* output : register */
    : /* input : none */
    : /* clobbers: none */);
    return value;
}

/********************************************************************
* Hipervisor
*********************************************************************/

/********************************************************************
* Supervisor
*********************************************************************/

/********************************************************************
* User
*********************************************************************/

#endif //CSR_H
