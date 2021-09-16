#include <pmu_hw.h>
#include <math.h>
#include "util.h"
#define PLIC_BASE 0x84000000
#define __PMU_LIB_DEBUG__

/*
 *   Function    : pmu_counters_enable
 *   Description : It enables the event counters.
 *   Parameters  : None
 *   Return      : None   
 */
void pmu_counters_enable(void) {
    PMUCFG0 |= 0x00000001;
    #ifdef __PMU_LIB_DEBUG__
    printf("Enable counters\n");
    printf("CFG0 = 0x%08x\n", PMUCFG0);
    #endif
}

/*
 *   Function    : pmu_counters_disable
 *   Description : It disables the event counters.
 *   Parameters  : None
 *   Return      : None   
 */
void pmu_counters_disable(void) {
    PMUCFG0 &= 0xFFFFFFFE;
    #ifdef __PMU_LIB_DEBUG__
    printf("Disable counters\n");
    printf("CFG0 = 0x%08x\n", PMUCFG0);
    #endif
}

/*
 *   Function    : pmu_counters_reset
 *   Description : It resets (set to 0) all the event counters.
 *   Parameters  : None
 *   Return      : None   
 */
void pmu_counters_reset(void) {
    PMUCFG0 |= 0x00000002;
    PMUCFG0 &= 0xFFFFFFFD;
    #ifdef __PMU_LIB_DEBUG__
    printf("Softreset counters\n");
    printf("CFG0 = 0x%08x\n", PMUCFG0);
    #endif
}

/*
 *   Function    : pmu_configure_crossbar
 *   Description : It routes the HDL wired signals with the 
 *                 counter modules.
 *   Parameters  : 
 *     - output        : Crossbar output number. See the CROSSBAR_OUTPUT_X 
 *                       defines in pmu_vars.h
 *     - event_index   : Event index of the wired signat in the HDL code. Refer to
 *                       SafePMU User's manual, section 2.2,table 2.1.
 *   Return      : None   
 */
//TODO:update 6-core
static unsigned pmu_configure_crossbar(unsigned int output, unsigned int event_index) {
    if (event_index>CROSSBAR_INPUTS){
        #ifdef __UART__
        printf("Input port %d selected out of range\n", event_index);
        #endif
    return (1);
    } 
    if (output>N_COUNTERS){
        #ifdef __UART__
        printf("Output port %d selected out of range\n", output);
        #endif
    return (1);
    } 

    unsigned int ev_idx = (event_index & CROSSBAR_INPUTS ); //?
    unsigned int fieldw = log2(CROSSBAR_INPUTS);
   
    //Blank Mask. It will reset any configuration field
    unsigned int bmask ; 
    bmask=(1<<fieldw)-1;
    //Get the bit position if all registers where concatenated
    unsigned tmp,reg_idx,field_idx;
    tmp = event_index*fieldw;
    //Get the register index given a register width
    reg_idx = tmp/REG_WIDTH;
    //Get the position of the crossbar configuration field
    field_idx = (int)tmp % REG_WIDTH;
    // check if the configuration field has bits in two different registers
    unsigned fieldw1 = fieldw; // Bits in first register
    unsigned fieldw2 = 0; //Bits in second register
    if ((field_idx+fieldw)>REG_WIDTH) {
        fieldw1 = REG_WIDTH-field_idx;
        fieldw2 = fieldw - fieldw1;
        // Clear previous field
        _PMU_CROSSBAR[reg_idx] &= (~((1<<fieldw1)-1) << field_idx); 
        _PMU_CROSSBAR[reg_idx+1] &= ~((1<<fieldw2)-1); 
        //Set new values
        _PMU_CROSSBAR[reg_idx] |= ev_idx << field_idx; 
        _PMU_CROSSBAR[reg_idx] |= (ev_idx>>fieldw1); 
    } else {
        _PMU_CROSSBAR[reg_idx] &= (~((bmask) << field_idx)); // Erease the output field
        _PMU_CROSSBAR[reg_idx] |= ev_idx << field_idx; // Write into the output field
    };
    return (0);
}

/*
 *   Function    : pmu_register_events
 *   Description : It registers all the event given by the ev_table parameter
 *   Parameters  : 
 *       - ev_table      : Table of register events.
 *       - event_count   : Number of register events.
 *   Return      : None   
 */
void pmu_register_events(const crossbar_event_t * ev_table, unsigned int event_count) {
    for (int i = 0; i < event_count; ++i) {
        pmu_configure_crossbar(ev_table[i].output, ev_table[i].event);
    }
}

/*
 *   Function    : pmu_counters_print
 *   Description : It prompt the register events with their
 *                 descriptions.
 *   Parameters  : 
 *       - table         : Table of register events.
 *       - event_count   : Number of register events.
 *   Return      : None   
 */
void pmu_counters_print(const crossbar_event_t * table, unsigned int event_count) {
    for (int i = 0; i < event_count; ++i) {
        printf("PMU_COUNTER[%d] = %d\t%s\n", i, _PMU_COUNTERS[table[i].output], table[i].description);
    }
}

/* **********************************
          OVERFLOW SUBMODULE
* **********************************/

/* 
 *   Function    : pmu_overflow_enable
 *   Description : Enable the PMU overflow submodule.
 *   Parameters  : None
 *   Return      : None   
 */
void pmu_overflow_enable(void) {
    PMUCFG0 |= 0x00000004;
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_overflow_enable\n");
    printf("PMUCFG0 = 0x%08x\n");
    #endif
}

/*
 *   Function    : pmu_overflow_disable
 *   Description : Disable the PMU overflow submodule.
 *   Parameters  : None
 *   Return      : None   
 */
void pmu_overflow_disable(void) {
    PMUCFG0 &= 0xFFFFFFFB;
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_overflow_disable\n");
    printf("PMUCFG0 = 0x%08x\n", PMUCFG0);
    #endif
}

/*
 *   Function    : pmu_overflow_reset
 *   Description : It resets the overflow flags.
 *   Parameters  : None
 *   Return      : None   
 */
void pmu_overflow_reset(void) {
    PMUCFG0 |= 0x00000008;
    PMUCFG0 &= 0xFFFFFFF7;
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_overflow_reset\n");
    #endif
}

/*
 *   Function    : pmu_overflow_enable_interrupt
 *   Description : It enables the interrupts for overflow submodule.
 *   Parameters  : 
 *       - mask  : Mask for each counter.
 *   Return      : None   
 */
void pmu_overflow_enable_interrupt(unsigned int mask) {
    PMU_OVERLFOW_IE |= mask;
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_overflow_enable_interrupt\n");
    printf("PMU_OVERLFOW_IE = 0x%08x\n", PMU_OVERLFOW_IE);
    #endif
}

/*
 *   Function    : pmu_overflow_disable_interrupt
 *   Description : It disables the interrupts for overflow submodule.
 *   Parameters  : None
 *   Return      : None   
 */
void pmu_overflow_disable_interrupt(unsigned int mask) {
    PMU_OVERLFOW_IE &= ~mask;
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_overflow_disable_interrupt\n");
    #endif
}

/*
 *   Function    : pmu_overflow_get_iv
 *   Description : It disables the interrupts for overflow submodule.
 *   Parameters  : 
 *       - mask  : Mask of each counter.
 *   Return      : 
 *       - 1     : One or more of the counters passed by mask has caused an overflow interrupt.
 *       - 0     : None of the counters passed by mask has caused an overflow interrupt.
 */
unsigned int pmu_overflow_get_interrupt(unsigned int mask) {
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_overflow_get_interrupt\n");
    #endif

    return ((PMU_OVERFLOW_IV & mask) != 0);
}

/*
 *   Function    : pmu_overflow_get_iv
 *   Description : It disables the interrupts for overflow submodule.
 *   Parameters  : None
 *   Return      : It returns the Overflow Interrupt Vector register.
 */
unsigned int pmu_overflow_get_iv(void) {
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_overflow_get_iv\n");
    #endif
    return (PMU_OVERFLOW_IV);
}

// TODO: Change priority
void pmu_overflow_register_interrupt(void( * isr)(void)) {
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_overflow_register_interrupt IN\n");
    #endif

    volatile unsigned int * p;

    p = (unsigned int * )(PLIC_BASE + 0x001000 + 4 * PMU_OVERFLOW_INT_INDEX);
    printf("Pending interrupt %d\n", * p);

    // p = (unsigned int *)(PLIC_BASE + 0x200000);
    // printf("Priority threshold for context 0 = %d\n", *p);
    // *p = 0;

    p = (unsigned int * )(PLIC_BASE + 0x200004);
    printf("Claim complete interrupt for context 0 = %d\n", * p);
    * p = PMU_OVERFLOW_INT_INDEX;

    write_csr(mtvec, isr);

    // Stablishes the priority level for a given interrupt index.
    p = (unsigned int * )(PLIC_BASE + 4 * PMU_OVERFLOW_INT_INDEX);
    * p = 7; // Priority

    // Enables the interrupt for index 7 (0x40) on context 0
    p = (unsigned int * )(PLIC_BASE + 0x002000);
    * p = 0x00000040;

    // // configure CLINT
    // write_csr(mstatus, 0x00006008);
    // write_csr(mie, 0xffffffff);

    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_overflow_register_interrupt OUT\n");
    #endif
}

/* **********************************
           MCCU SUBMODULE
* **********************************/

/*
 *   Function    : pmu_mccu_enable
 *   Description : It enables the MCCU submodule.
 *   Parameters  : None.
 *   Return      : None.
 */
void pmu_mccu_enable(void) {
    PMUCFG1 |= 0x00000001;
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_mccu_enable\n");
    printf("PMUCFG1 = %d\n", PMUCFG1);
    #endif
}

/*
 *   Function    : pmu_mccu_disable
 *   Description : It disable the MCCU submodule.
 *   Parameters  : None.
 *   Return      : None.
 */
void pmu_mccu_disable(void) {
    PMUCFG1 &= 0xFFFFFFFE;
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_mccu_disable\n");
    printf("PMUCFG1 = %d\n", PMUCFG1);
    #endif
}

/*
 *   Function    : pmu_mccu_reset
 *   Description : It resets the MCCU submodule.
 *   Parameters  : None.
 *   Return      : None.
 */
void pmu_mccu_reset(void) {
    PMUCFG1 |= 0x00000002;
    PMUCFG1 &= 0xFFFFFFFD;
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_mccu_reset\n");
    printf("PMUCFG1 = %d\n", PMUCFG1);
    #endif
}

/*
 *   Function    : pmu_mccu_set_quota_limit
 *   Description : It sets the quota limits for MCCU submodule
 *   Parameters  : 
 *       - core  :  Target core for quota monitoring. Select core number 1, 2, 3 or 4.
 *       - quota :  32 bits wide quota for selected core.
 *   Return      : Unsigned int. 0 no error.
 */
unsigned int pmu_mccu_set_quota_limit(const unsigned int core,
    const unsigned int quota) {
    if(core>MCCU_N_CORES){
        printf("mccu_set_quota: core %d does not exist\n", core);
	return(1);
    }
    //set update bits
    PMUCFG1 |= 1<<(core+2);//Offset are enable en reset bits
    //set target quota
    _PMU_MCCU_QUOTA[core]=quota;
    //release set bits
    PMUCFG1 &= ~(0x3f<<2);//shift 2 bits due to enable and reset mccu
                          // 0xf ->4cores / 0x3f -> 6cores
}

/*
 *   Function    : pmu_mccu_get_quota_remaining
 *   Description : Get the remaining quota for a single core.
 *   Parameters  : 
 *       - core  : Target core for quota monitoring. Select core number 1, 2, 3 or 4.
 *   Return      : The remaining quota for a selected core.
 */
unsigned int pmu_mccu_get_quota_remaining(unsigned int core) {
    char err_msg[] = "ERR on pmu_mccu_get_quota_remaining <core> parameter out of range";
    PMU_ASSERT((core >= 1 U) && (core <= 4 U), err_msg);
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_mccu_get_quota_remaining\n");
    #endif
    return (_PMU_MCCU_QUOTA[3 + core]);
}

/*
 *   Function    : pmu_mccu_set_event_weigths
 *   Description : It sets the weigths for a selected input.
 *   Parameters  : 
 *      - input  : A given input from 0 to 7.
 *      - weigth : 8 bits wide for a given input.
 *   
 *   Return      : Unsigned int. 0 no error.
 */
void pmu_mccu_set_event_weigths(const unsigned int input,
    const unsigned int weigth) {
    switch (input) {
    case 0:
    case 1:
    case 2:
    case 3:
        EVENT_WEIGHT_REG0 &= ~(0x000000FF << (input << 3));
        EVENT_WEIGHT_REG0 |= (weigth & 0x000000FF) << (input << 3);
        break;

    case 4:
    case 5:
    case 6:
    case 7:
        EVENT_WEIGHT_REG1 &= ~(0x000000FF << (input << 3));
        EVENT_WEIGHT_REG1 |= (weigth & 0x000000FF) << (input << 3);
        break;
    case 8:
    case 9:
    case 10:
    case 11:
        EVENT_WEIGHT_REG2 &= ~(0x000000FF << (input << 3));
        EVENT_WEIGHT_REG2 |= (weigth & 0x000000FF) << (input << 3);
        break;

    default:
        printf("mccu_set_event_weigths: input %d does not exist\n", input);
        return (1);
    }

    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_mccu_set_event_weigths\n");
    printf("EVENT_WEIGHT_REG0 = %u\n", EVENT_WEIGHT_REG0);
    printf("EVENT_WEIGHT_REG1 = %u\n", EVENT_WEIGHT_REG1);
    printf("EVENT_WEIGHT_REG2 = %u\n", EVENT_WEIGHT_REG2);
    #endif
    return (0);
}

/* **********************************
           RDC SUBMODULE
* **********************************/

/*
 *   Function    : pmu_rdc_enable
 *   Description : It enables the RDC submodule.
 *   Parameters  : None.
 *   Return      : None.
 */
void pmu_rdc_enable(void) {
    PMUCFG1 |= 1<<(2+MCCU_N_CORES);
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_rdc_enable\n");
    printf("PMUCFG1 = %d\n", PMUCFG1);
    #endif
}

/*
 *   Function    : pmu_rdc_disable
 *   Description : It disables the RDC disable.
 *   Parameters  : None.
 *   Return      : None.
 */
void pmu_rdc_disable(void) {
    PMUCFG1 &= ~(1<<(2+MCCU_N_CORES));
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_rdc_disable\n");
    printf("PMUCFG1 = %d\n", PMUCFG1);
    #endif
}

/*
 *   Function    : pmu_rdc_reset
 *   Description : It resets the RDC disable.
 *   Parameters  : None.
 *   Return      : None.
 */
void pmu_rdc_reset(void) {
    PMUCFG1 |= 1<<(2+MCCU_N_CORES+1);//2(enable,reset mccu),(ncores) quota updates, 1 (enable RDC)
    PMUCFG1 &= ~(1<<(2+MCCU_N_CORES+1));//2(enable,reset mccu),(ncores) quota updates, 1 (enable RDC)
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_rdc_reset\n");
    printf("PMUCFG1 = %d\n", PMUCFG1);
    #endif
}

/*
 *   Function    : pmu_rdc_read_watermark
 *   Description : It gets the watermarks for a given input.
 *   Parameters  : 
 *       - input : A given input from 0 to 7.
 *   Return      : It return the watermark for a given input.
 */
unsigned int pmu_rdc_read_watermark(unsigned int input) {
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_rdc_read_watermark\n");
    printf("PMU_RDC_WATERMARK_REG0 = 0x%08x\n", PMU_RDC_WATERMARK_REG0);
    printf("PMU_RDC_WATERMARK_REG1 = 0x%08x\n", PMU_RDC_WATERMARK_REG1);
    #endif

    char err_msg[] = "ERR on pmu_rdc_read_watermark. <input> parameter out of range";
    PMU_ASSERT((input >= 0) && (input < MCCU_N_EVENTS*MCCU_N_CORES), err_msg);
    
    unsigned int idx, tmp; 
    idx = input/(REG_WIDTH/MCCU_WEIGHTS_WIDTH);
    tmp = (_PMU_RDC_WATERMARKS[idx] & (0x000000FF << (input << 3))) >> (input << 3)
    return (tmp);
}

/*
 *   Function    : pmu_rdc_read_iv
 *   Description : It resets the RDC disable.
 *   Parameters  : None.
 *   Return      : It returns the Interrupt Vector for the RDC.
 */
unsigned int pmu_rdc_read_iv() {
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_rdc_read_iv\n");
    #endif

    return (PMU_RDC_IV);
}

/*
 *   Function    : pmu_rdc_get_interrupt
 *   Description : Get the interrupt for a given core. It interrupts when the 
 *                 quota get to 0. 
 *   Parameters  : 
 *       - core  : Core to monitor the RDC interrupt.
 *   Return      : 
 *       - 1 : The RDC for the given core has interrupted.
 *       - 0 : The RDC for the given core has not interrupted.
 */
unsigned int pmu_rdc_get_interrupt(unsigned int core) {
    #ifdef __PMU_LIB_DEBUG__
    printf("pmu_rdc_get_interrupt\n");
    printf("PMU_RDC_IV = 0x%04x\n", PMU_RDC_IV);
    #endif

    return ((PMU_RDC_IV & (0x00000001 << core)) != 0);
}
