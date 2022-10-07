/** @file plic.c
 *  @brief Functions to manager RISC-V Platform-Level Interrupt Controller(Selene specs).
 *
 *  @author Juan C. Rodriguez (jrodrig9).
 *  @copyright Barcelona Supercomputing Center. All rights reserved.
 *  @bug None.
 *  @doc https://github.com/riscv/riscv-plic-spec/blob/master/riscv-plic.adoc
 *  @note Some operations may be different for other RISC-V Platforms.
 *  @note Context priority must be less than source priority.
 */

#include "plic.h"

void
plic_set_source_priority (uint32_t source, uint8_t priority)
{
    volatile uint32_t *address;

    address = (volatile uint32_t *)(PLIC_BASE + 0x4 * source);
    *address = priority;
}

void
plic_clear_source_priority (uint32_t source)
{
    volatile uint32_t *address;

    address = (volatile uint32_t *)(PLIC_BASE + 0x4 * source);
    *address = 0;
}

void
plic_enable_source (uint8_t mode, uint8_t core, uint32_t mask)
{
    volatile uint32_t *address;

    address = (volatile uint32_t *)(PLIC_BASE + 0x002000 +
                                    (0x200 * core) + (0x80 * mode));
    *address = *address | mask;
}

void
plic_clear_source (uint8_t mode, uint8_t core, uint32_t mask)
{
    volatile uint32_t *address;

    address = (volatile uint32_t *)(PLIC_BASE + 0x002000 +
                                    (0x200 * core) + (0x80 * mode));
    *address = *address & !mask;
}

void
plic_set_core_priority (uint8_t mode, uint8_t core, uint8_t priority)
{
    volatile uint32_t *address;

    address = (volatile uint32_t *)(PLIC_BASE + 0x200000 +
                                    (0x4000 * core) + (0x1000 * mode));
    *address = priority;
}

void
plic_clear_core_priority (uint8_t mode, uint8_t core)
{
    volatile uint32_t *address;

    address = (volatile uint32_t *)(PLIC_BASE + 0x200000 +
                                    (0x4000 * core) + (0x1000 * mode));
    *address = 0;
}


