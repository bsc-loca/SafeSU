/** @file plic.h
 *  @brief Functions to manager RISC-V Platform-Level Interrupt Controller(Selene specs).
 *
 *  @author Juan C. Rodriguez (jrodrig9).
 *  @copyright Barcelona Supercomputing Center. All rights reserved.
 *  @bug None.
 *  @doc https://github.com/riscv/riscv-plic-spec/blob/master/riscv-plic.adoc
 *  @note Some operations may be different for other RISC-V Platforms.
 *  @note Context priority must be less than source priority.
 */
#include <stdint.h>

#ifndef PLIC_H
#define PLIC_H

//grmon_scripts: info sys
#define PLIC_BASE 0xf8000000

/********************************************************************
* DEFINE CPU MODES
*********************************************************************/
#define MACHINE_MODE 0
#define SUPERVISOR_MODE 1
#define USER_MODE 2
#define HIPERVISOR_MODE 3

/********************************************************************
* SOURCE MASKS
*********************************************************************/
#define MASK_SOURCE_1 0x2
#define MASK_SOURCE_2 0x4
#define MASK_SOURCE_3 0x8
#define MASK_SOURCE_4 0x10
#define MASK_SOURCE_5 0x20
#define MASK_SOURCE_6 0x40
#define MASK_SOURCE_7 0x80
#define MASK_SOURCE_8 0x100
#define MASK_SOURCE_9 0x200
#define MASK_SOURCE_10 0x400
#define MASK_SOURCE_11 0x800
#define MASK_SOURCE_12 0x1000
#define MASK_SOURCE_13 0x2000
#define MASK_SOURCE_14 0x4000
#define MASK_SOURCE_15 0x8000
#define MASK_SOURCE_16 0x10000
#define MASK_SOURCE_17 0x20000
#define MASK_SOURCE_18 0x40000
#define MASK_SOURCE_19 0x80000
#define MASK_SOURCE_20 0x100000
#define MASK_SOURCE_21 0x200000
#define MASK_SOURCE_22 0x400000
#define MASK_SOURCE_23 0x800000
#define MASK_SOURCE_24 0x01000000
#define MASK_SOURCE_25 0x02000000
#define MASK_SOURCE_26 0x04000000
#define MASK_SOURCE_27 0x08000000
#define MASK_SOURCE_28 0x10000000
#define MASK_SOURCE_29 0x20000000
#define MASK_SOURCE_30 0x40000000
#define MASK_SOURCE_31 0x80000000

/**
 * @brief Set a specific priority for a source.
 *
 * @param source - Interrupt source.
 * @param priority - Priority value.
 * @note Put priority to zero if you want disable interrupt.
 */
void plic_set_source_priority(uint32_t source, uint8_t priority);
/**
 * @brief Clear priority for a source.
 *
 * @param source - Interrupt source.
 */
void plic_clear_source_priority(uint32_t source);
/**
 * @brief Enable source for a specific context.
 *
 * @param mode - CPU modes: Machine, Hipervisor, Supervisor and User.
 * @param core - CPU cores: 0-5.
 * @param mask - The bit of the source that you want enable.
 * @note You have got CPU modes definitions up.
 */
void plic_enable_source(uint8_t mode, uint8_t core, uint32_t mask);
/**
 * @brief Clear source for a specific context.
 *
 * @param mode - CPU modes: Machine, Hipervisor, Supervisor and User.
 * @param core - CPU cores: 0-5.
 * @param mask - The bit of the source that you want disable.
 * @note You have got CPU modes definitions up.
 */
void plic_clear_source(uint8_t mode, uint8_t core, uint32_t mask);
/**
 * @brief Set a specific priority for a context.
 *
 * @param mode - CPU modes: Machine, Hipervisor, Supervisor and User.
 * @param core - CPU cores: 0-5.
 * @param priority - Priority value.
 * @note You have got CPU modes definitions up.
 * @note1 This priority value must be less than source priority.
 */
void plic_set_core_priority(uint8_t mode, uint8_t core, uint8_t priority);
/**
 * @brief Clear priority for a context.
 *
 * @param mode - CPU modes: Machine, Hipervisor, Supervisor and User.
 * @param core - CPU cores: 0-5.
 * @note You have got CPU modes definitions up.
 */
void plic_clear_core_priority(uint8_t mode, uint8_t core);

/**
 * @brief Get pending IRQs.
 *
 * @return - uint32_t register where every bits with 1 value indicate the pending irq source.
 */
static inline __attribute__((always_inline)) uint32_t
plic_pending_irq (void)
{
    volatile uint32_t *address;

    address = (volatile uint32_t *) (uintptr_t) (PLIC_BASE + 0x001000);
    return *address;
}
/**
 * @brief Complete pending IRQ for specific context.
 *
 * @param mode - CPU modes: Machine, Hipervisor, Supervisor and User.
 * @param core - CPU cores: 0-5.
 * @note You have got CPU modes definitions up.
 */
static inline __attribute__((always_inline)) void
plic_claim_complete_core_irq (uint8_t mode, uint8_t core)
{
    volatile uint32_t *address;

    address = (volatile uint32_t *) (uintptr_t) (PLIC_BASE + 0x200004 +
                                     (0x4000 * core) + (0x1000 * mode));
    *address = *address;
}

#endif //PLIC_H
