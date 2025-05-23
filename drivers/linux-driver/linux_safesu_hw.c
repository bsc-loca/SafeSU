#include "linux_safesu_hw.h"
#include <sys/ioctl.h>
#include <fcntl.h>
#include <unistd.h>
#include <math.h>
#include <stdio.h>

// #define __SAFESU_LIB_DEBUG__


    // open_safesu_driver / close_safesu_driver are 'static' / only used within this library
    // I.e. they're not meant to be called from user code.
    // open_safesu_driver is automagicalled at the start of any safesu_xxxx(..) call:
    //      if(!driver_fd) open_safesu_driver();
static int driver_fd = 0;

static void open_safesu_driver(void) {
    driver_fd = open("/dev/safesu", O_RDWR);
    if(driver_fd == 0) {
        printf("Cannot open device for safesafesu...\n");
    }
}

static void close_safesu_driver(void) {
    if(driver_fd) {
        close(driver_fd);
        driver_fd = 0;
    }
}

// Calls to llseek+read / llseek+write are encapsulated within these two functions:
//      - unsigned int read_safesu_reg(offs)
//      - unsigned int write_safesu_reg(offs)

inline static unsigned int read_safesu_reg(unsigned int offs) {
    unsigned int value;
        // printf("I'm going to lseek register: %d\n", offs);
    lseek(driver_fd, offs, SEEK_SET);
    read(driver_fd, &value, 4);
        // printf("I'm going to read register: %d\n", offs);
    // Either lseek+read, or read (actually the same)
    //pread(driver_fd, &value, 4, offs);
        // printf("read_safesu_reg(...) done, value: %d\n", value);
    return value;
}

inline static void write_safesu_reg(unsigned int offs, unsigned int value) {
        // printf("I'm going to lseek register: %d\n", offs);
    lseek(driver_fd, offs, SEEK_SET);
    write(driver_fd, &value, 4);
        // printf("I'm going to write register: %d; with value %d\n", offs, value);

    // Either lseek+write, or write (actually the same)
    //pwrite(driver_fd, &value, 4, offs);

        // printf("write_safesu_reg(..) done, wrote register: %d; with value %d\n", offs, value);
        
        // Code below disabled. Just did it to check that we do read what we've written
    // lseek(driver_fd, offs, SEEK_SET);
    // read(driver_fd, &value, 4);
        //  printf("write_safesu_reg(..) value after read is %d\n", value);
}

unsigned int dummy;

void enable_mie(void) {
    // if(!driver_fd) open_safesu_driver();

    // printf("lib: Enabling interrupts:\n");

    ioctl(driver_fd, ENABLE_PLIC_INT, &dummy);
}

void disable_mie(void) {
    if(!driver_fd) open_safesu_driver();

    ioctl(driver_fd, DISABLE_PLIC_INT, &dummy);
}

void call_ub(void *ub_fn) {
    if(!driver_fd) open_safesu_driver();

    ioctl(driver_fd, RUN_UB, ub_fn);
}


/*
 *   Function    : safesu_counters_enable
 *   Description : It enables the event counters.
 *   Parameters  : None
 *   Return      : None   
 */
void safesu_counters_enable(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESUCFG0, read_safesu_reg(SAFESUCFG0)|0x00000001);

#ifdef __SAFESU_LIB_DEBUG__
    printf("Enable counters\n");
    printf("CFG0 = 0x%08x\n", read_safesu_reg(SAFESUCFG0));
#endif

}

/*
 *   Function    : safesu_counters_disable
 *   Description : It disables the event counters.
 *   Parameters  : None
 *   Return      : None   
 */
void safesu_counters_disable(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESUCFG0, read_safesu_reg(SAFESUCFG0)&0xFFFFFFFE);

#ifdef __SAFESU_LIB_DEBUG__
    printf("Disable counters\n");
    printf("CFG0 = 0x%08x\n", read_safesu_reg(SAFESUCFG0));
#endif

}

/*
 *   Function    : safesu_counters_reset
 *   Description : It resets (set to 0) all the event counters.
 *   Parameters  : None
 *   Return      : None   
 */
void safesu_counters_reset(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESUCFG0, read_safesu_reg(SAFESUCFG0)|0x00000002);
    write_safesu_reg(SAFESUCFG0, read_safesu_reg(SAFESUCFG0)&0xFFFFFFFD);

#ifdef __SAFESU_LIB_DEBUG__
    printf("Softreset counters\n");
    printf("CFG0 = 0x%08x\n", read_safesu_reg(SAFESUCFG0));
#endif

}

/*
 *   Function    : safesu_configure_crossbar
 *   Description : It routes the HDL wired signals with the 
 *                 counter modules.
 *   Parameters  : 
 *     - output        : Crossbar output number. See the CROSSBAR_OUTPUT_X 
 *                       defines in safesu_vars.h
 *     - event_index   : Event index of the wired signat in the HDL code. Refer to
 *                       SafeSAFESU User's manual, section 2.2,table 2.1.
 *   Return      : None   
 */
unsigned safesu_configure_crossbar(unsigned int output, unsigned int event_index) {

    if(!driver_fd) open_safesu_driver();

    if (event_index>CROSSBAR_INPUTS) {
#ifdef __UART__
        printf("Input port %d selected out of range\n", event_index);
#endif

        return (1);
    } 

    if (output>N_COUNTERS)  {

#ifdef __UART__
        printf("Output port %d selected out of range\n", output);
#endif

        return (1);
    } 
    unsigned int ev_idx = event_index;
    unsigned int fieldw = log2(CROSSBAR_INPUTS);
    //Blank Mask. It will reset any configuration field
    unsigned int bmask ; 
    bmask=(1<<fieldw)-1;
    unsigned int tmp,reg_idx,field_idx;
    //Get the bit position if all registers where concatenated
    tmp = output*fieldw;
    //Get the register index given a register width
    reg_idx = tmp/REG_WIDTH;
    //Get the position of the crossbar configuration field
    field_idx = (int)tmp % REG_WIDTH;
    // check if the configuration field has bits in two different registers
    unsigned int fieldw1 = fieldw; // Bits in first register
    unsigned int fieldw2 = 0; //Bits in second register
    if ((field_idx+fieldw)>REG_WIDTH) {
        fieldw1 = REG_WIDTH-field_idx;
        fieldw2 = fieldw - fieldw1;
        // Clear previous field
        write_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx], read_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx])&(~(((1<<fieldw1)-1) << field_idx)));
        write_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx+1], read_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx+1])&~((1<<fieldw2)-1));
        //Set new values
        write_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx], read_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx])|ev_idx << field_idx);
        write_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx+1], read_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx+1])|(ev_idx>>fieldw1));
    } else {
        write_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx], read_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx])&(~((bmask) << field_idx)));
        write_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx], read_safesu_reg((unsigned long int)&_SAFESU_CROSSBAR[reg_idx])|(ev_idx << field_idx));
    };
    return (0);
}

/*
 *   Function    : safesu_register_events
 *   Description : It registers all the event given by the ev_table parameter
 *   Parameters  : 
 *       - ev_table      : Table of register events.
 *       - event_count   : Number of register events.
 *   Return      : None   
 */
void safesu_register_events(const crossbar_event_t * ev_table, unsigned int event_count) {

    if(!driver_fd) open_safesu_driver();

    for (int i = 0; i < event_count; ++i) {
        safesu_configure_crossbar(ev_table[i].output, ev_table[i].event);
    }
}

/*
 *   Function    : safesu_counters_print
 *   Description : It prompt the register events with their
 *                 descriptions.
 *   Parameters  : 
 *       - table         : Table of register events.
 *       - event_count   : Number of register events.
 *   Return      : None   
 */
void safesu_counters_print(const crossbar_event_t * table, unsigned int event_count) {

    if(!driver_fd) open_safesu_driver();

    for (int i = 0; i < event_count; ++i) {
        printf("SAFESU_COUNTER[%2d] = %10d\t%s\n", i, read_safesu_reg((unsigned long int)&_SAFESU_COUNTERS[table[i].output]), table[i].description);        
    }
}

void safesu_counters_fill_default_descriptions(crossbar_event_t* table, unsigned int event_count){
    for(int i = 0; i < event_count; i++){
        table[i].description = counterDescriptions[table[i].event];    
	}
}

/* **********************************
          OVERFLOW SUBMODULE
* **********************************/

/* 
 *   Function    : safesu_overflow_enable
 *   Description : Enable the SAFESU overflow submodule.
 *   Parameters  : None
 *   Return      : None   
 */
void safesu_overflow_enable(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESUCFG0, read_safesu_reg(SAFESUCFG0)|0x00000004);

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_overflow_enable\n");
    printf("SAFESUCFG0 = 0x%08x\n");
#endif

}

/*
 *   Function    : safesu_overflow_disable
 *   Description : Disable the SAFESU overflow submodule.
 *   Parameters  : None
 *   Return      : None   
 */
void safesu_overflow_disable(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESUCFG0, read_safesu_reg(SAFESUCFG0)&0xFFFFFFFB);

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_overflow_disable\n");
    printf("SAFESUCFG0 = 0x%08x\n", SAFESUCFG0);
#endif

}

/*
 *   Function    : safesu_overflow_reset
 *   Description : It resets the overflow flags.
 *   Parameters  : None
 *   Return      : None   
 */
void safesu_overflow_reset(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESUCFG0, read_safesu_reg(SAFESUCFG0)|0x00000008);
    write_safesu_reg(SAFESUCFG0, read_safesu_reg(SAFESUCFG0)&0xFFFFFFF7);

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_overflow_reset\n");
#endif

}

/*
 *   Function    : safesu_overflow_enable_interrupt
 *   Description : It enables the interrupts for overflow submodule.
 *   Parameters  : 
 *       - mask  : Mask for each counter.
 *   Return      : None   
 */
void safesu_overflow_enable_interrupt(unsigned int mask) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESU_OVERLFOW_IE, read_safesu_reg(SAFESU_OVERLFOW_IE)|mask);

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_overflow_enable_interrupt\n");
    printf("SAFESU_OVERLFOW_IE = 0x%08x\n", read_safesu_reg(SAFESU_OVERLFOW_IE));
#endif

}

/*
 *   Function    : safesu_overflow_disable_interrupt
 *   Description : It disables the interrupts for overflow submodule.
 *   Parameters  : None
 *   Return      : None   
 */
void safesu_overflow_disable_interrupt(unsigned int mask) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESU_OVERLFOW_IE, read_safesu_reg(SAFESU_OVERLFOW_IE)&~mask);

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_overflow_disable_interrupt\n");
#endif

}

/*
 *   Function    : safesu_overflow_get_iv
 *   Description : It disables the interrupts for overflow submodule.
 *   Parameters  : 
 *       - mask  : Mask of each counter.
 *   Return      : 
 *       - 1     : One or more of the counters passed by mask has caused an overflow interrupt.
 *       - 0     : None of the counters passed by mask has caused an overflow interrupt.
 */
unsigned int safesu_overflow_get_interrupt(unsigned int mask) {

    if(!driver_fd) open_safesu_driver();

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_overflow_get_interrupt\n");
#endif

    return ((read_safesu_reg(SAFESU_OVERFLOW_IV) & mask) != 0);
}

/*
 *   Function    : safesu_overflow_get_iv
 *   Description : It disables the interrupts for overflow submodule.
 *   Parameters  : None
 *   Return      : It returns the Overflow Interrupt Vector register.
 */
unsigned int safesu_overflow_get_iv(void) {

    if(!driver_fd) open_safesu_driver();

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_overflow_get_iv\n");
#endif

    return (read_safesu_reg(SAFESU_OVERFLOW_IV));
}

// TODO: Change priority
void safesu_overflow_register_interrupt(void( * isr)(void)) {
#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_overflow_register_interrupt IN\n");
#endif

    // volatile unsigned int * p;

    // p = (unsigned int * )(PLIC_BASE + 0x001000 + 4 * SAFESU_OVERFLOW_INT_INDEX);
    // printf("Pending interrupt %d\n", * p);

    // // p = (unsigned int *)(PLIC_BASE + 0x200000);
    // // printf("Priority threshold for context 0 = %d\n", *p);
    // // *p = 0;

    // p = (unsigned int * )(PLIC_BASE + 0x200004);
    // printf("Claim complete interrupt for context 0 = %d\n", * p);
    // * p = SAFESU_OVERFLOW_INT_INDEX;

    // // write_csr(mtvec, isr);

    // // Stablishes the priority level for a given interrupt index.
    // p = (unsigned int * )(PLIC_BASE + 4 * SAFESU_OVERFLOW_INT_INDEX);
    // * p = 7; // Priority

    // // Enables the interrupt for index 7 (0x40) on context 0
    // p = (unsigned int * )(PLIC_BASE + 0x002000);
    // * p = 0x00000040;

    // // // configure CLINT
    // // write_csr(mstatus, 0x00006008);
    // // write_csr(mie, 0xffffffff);

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_overflow_register_interrupt OUT\n");
#endif

}

/* **********************************
           MCCU SUBMODULE
* **********************************/

/*
 *   Function    : safesu_mccu_enable
 *   Description : It enables the MCCU submodule.
 *   Parameters  : None.
 *   Return      : None.
 */
void safesu_mccu_enable(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESUCFG1, read_safesu_reg(SAFESUCFG1)|0x00000001);

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_mccu_enable\n");
    printf("SAFESUCFG1 = %d\n", read_safesu_reg(SAFESUCFG1));
#endif

}

/*
 *   Function    : safesu_mccu_disable
 *   Description : It disable the MCCU submodule.
 *   Parameters  : None.
 *   Return      : None.
 */
void safesu_mccu_disable(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESUCFG1, read_safesu_reg(SAFESUCFG1)&0xFFFFFFFE);

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_mccu_disable\n");
    printf("SAFESUCFG1 = %d\n", read_safesu_reg(SAFESUCFG1));
#endif

}

/*
 *   Function    : safesu_mccu_reset
 *   Description : It resets the MCCU submodule.
 *   Parameters  : None.
 *   Return      : None.
 */
void safesu_mccu_reset(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(SAFESUCFG1, read_safesu_reg(SAFESUCFG1)|0x00000002);
    write_safesu_reg(SAFESUCFG1, read_safesu_reg(SAFESUCFG1)&0xFFFFFFFD);

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_mccu_reset\n");
    printf("SAFESUCFG1 = %d\n", SAFESUCFG1);
#endif

}

/*
 *   Function    : safesu_mccu_set_quota_limit
 *   Description : It sets the quota limits for MCCU submodule
 *   Parameters  : 
 *       - core  :  Target core for quota monitoring. Select core number 1, 2, 3 or 4.
 *       - quota :  32 bits wide quota for selected core.
 *   Return      : Unsigned int. 0 no error.
 */
unsigned safesu_mccu_set_quota_limit(const unsigned int core,
    const unsigned int quota) {

    if(!driver_fd) open_safesu_driver();

    if(core>MCCU_N_CORES){
        printf("mccu_set_quota: core %d does not exist\n", core);
	    return(1);
    }

        //set update bits / Offset are enable en reset bits        
    write_safesu_reg(SAFESUCFG1, read_safesu_reg(SAFESUCFG1)|1<<(core+2));
    
        //set target quota    
    write_safesu_reg(_SAFESU_MCCU_QUOTA[core], quota);

    //release set bits
    write_safesu_reg(SAFESUCFG1, read_safesu_reg(SAFESUCFG1)&~(0x3f<<2));
}

/*
 *   Function    : safesu_mccu_get_quota_remaining
 *   Description : Get the remaining quota for a single core.
 *   Parameters  : 
 *       - core  : Target core for quota monitoring. Select core number 1, 2, 3 or 4.
 *   Return      : The remaining quota for a selected core.
 */
unsigned int safesu_mccu_get_quota_remaining(unsigned int core) {

    if(!driver_fd) open_safesu_driver();

    char err_msg[] = "ERR on safesu_mccu_get_quota_remaining <core> parameter out of range";

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_mccu_get_quota_remaining\n");
#endif

    return (read_safesu_reg(_SAFESU_MCCU_QUOTA[MCCU_N_CORES + core]));
}

/*
 *   Function    : safesu_mccu_set_event_weigths
 *   Description : It sets the weigths for a selected input.
 *   Parameters  : 
 *      - input  : A given input from 0 to 7.
 *      - weigth : 8 bits wide for a given input.
 *   
 *   Return      : Unsigned int. 0 no error.
 */
unsigned safesu_mccu_set_event_weigths(const unsigned int input,
    const unsigned int weigth) {

    if(!driver_fd) open_safesu_driver();

    switch (input) {
    case 0:
    case 1:
    case 2:
    case 3:
        write_safesu_reg(EVENT_WEIGHT_REG0, read_safesu_reg(EVENT_WEIGHT_REG0)&~(0x000000FF << (input << 3)));
        write_safesu_reg(EVENT_WEIGHT_REG0, read_safesu_reg(EVENT_WEIGHT_REG0)|(weigth & 0x000000FF) << (input << 3));
        break;

    case 4:
    case 5:
    case 6:
    case 7:
        write_safesu_reg(EVENT_WEIGHT_REG1, read_safesu_reg(EVENT_WEIGHT_REG1)&~(0x000000FF << (input << 3)));
        write_safesu_reg(EVENT_WEIGHT_REG1, read_safesu_reg(EVENT_WEIGHT_REG1)|(weigth & 0x000000FF) << (input << 3));
        break;
    case 8:
    case 9:
    case 10:
    case 11:
        write_safesu_reg(EVENT_WEIGHT_REG2, read_safesu_reg(EVENT_WEIGHT_REG2)&~(0x000000FF << (input << 3)));
        write_safesu_reg(EVENT_WEIGHT_REG2, read_safesu_reg(EVENT_WEIGHT_REG2)|(weigth & 0x000000FF) << (input << 3));
        break;

    default:
        printf("mccu_set_event_weigths: input %d does not exist\n", input);
        return (1);
    }

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_mccu_set_event_weigths\n");
    printf("EVENT_WEIGHT_REG0 = %u\n", read_safesu_reg(EVENT_WEIGHT_REG0));
    printf("EVENT_WEIGHT_REG1 = %u\n", read_safesu_reg(EVENT_WEIGHT_REG1));
    printf("EVENT_WEIGHT_REG2 = %u\n", read_safesu_reg(EVENT_WEIGHT_REG2));
#endif

    return (0);
}

void safesu_mccu_enable_HQ(){
    unsigned mask = 1 << 31;
    write_safesu_reg(SAFESUCFG1, read_safesu_reg(SAFESUCFG1)| mask);    
}
void safesu_mccu_disable_HQ(){
    unsigned mask = 1 << 31;
    write_safesu_reg(SAFESUCFG1, read_safesu_reg(SAFESUCFG1)& ~mask);    
}

/* **********************************
           RDC SUBMODULE
* **********************************/

/*
 *   Function    : safesu_rdc_enable
 *   Description : It enables the RDC submodule.
 *   Parameters  : None.
 *   Return      : None.
 */
void safesu_rdc_enable(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(EVENT_WEIGHT_REG0, read_safesu_reg(SAFESUCFG1)| 1<<(2+MCCU_N_CORES));

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_rdc_enable\n");
    printf("SAFESUCFG1 = %d\n", read_safesu_reg(SAFESUCFG1));
#endif

}

/*
 *   Function    : safesu_rdc_disable
 *   Description : It disables the RDC disable.
 *   Parameters  : None.
 *   Return      : None.
 */
void safesu_rdc_disable(void) {

    if(!driver_fd) open_safesu_driver();

    write_safesu_reg(EVENT_WEIGHT_REG0, read_safesu_reg(SAFESUCFG1)&~(1<<(2+MCCU_N_CORES)));

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_rdc_disable\n");
    printf("SAFESUCFG1 = %d\n", SAFESUCFG1);
#endif

}

/*
 *   Function    : safesu_rdc_reset
 *   Description : It resets the RDC disable.
 *   Parameters  : None.
 *   Return      : None.
 */
void safesu_rdc_reset(void) {

    if(!driver_fd) open_safesu_driver();

        //2(enable,reset mccu),(ncores) quota updates, 1 (enable RDC)
    write_safesu_reg(EVENT_WEIGHT_REG0, read_safesu_reg(SAFESUCFG1) | 1<<(2+MCCU_N_CORES+1));     
        //2(enable,reset mccu),(ncores) quota updates, 1 (enable RDC)
    write_safesu_reg(EVENT_WEIGHT_REG0, read_safesu_reg(SAFESUCFG1) & ~(1<<(2+MCCU_N_CORES+1))); 

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_rdc_reset\n");
    printf("SAFESUCFG1 = %d\n", SAFESUCFG1);
#endif

}

/*
 *   Function    : safesu_rdc_read_watermark
 *   Description : It gets the watermarks for a given input.
 *   Parameters  : 
 *       - input : A given input from 0 to 7.
 *   Return      : It return the watermark for a given input.
 */
unsigned int safesu_rdc_read_watermark(unsigned int input) {

    if(!driver_fd) open_safesu_driver();

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_rdc_read_watermark\n");
    printf("SAFESU_RDC_WATERMARK_REG0 = 0x%08x\n", read_safesu_reg(SAFESU_RDC_WATERMARK_REG0));
    printf("SAFESU_RDC_WATERMARK_REG1 = 0x%08x\n", read_safesu_reg(SAFESU_RDC_WATERMARK_REG1));
#endif

    char err_msg[] = "ERR on safesu_rdc_read_watermark. <input> parameter out of range";
    
    unsigned int idx, tmp; 
    idx = input/(REG_WIDTH/MCCU_WEIGHTS_WIDTH);
    tmp = (read_safesu_reg(_SAFESU_RDC_WATERMARKS[idx]) & (0x000000FF << (input << 3))) >> (input << 3);
    return (tmp);
}

/*
 *   Function    : safesu_rdc_read_iv
 *   Description : It resets the RDC disable.
 *   Parameters  : None.
 *   Return      : It returns the Interrupt Vector for the RDC.
 */
unsigned int safesu_rdc_read_iv() {

    if(!driver_fd) open_safesu_driver();

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_rdc_read_iv\n");
#endif

    return (read_safesu_reg(SAFESU_RDC_IV));
}

/*
 *   Function    : safesu_rdc_get_interrupt
 *   Description : Get the interrupt for a given core. It interrupts when the 
 *                 quota get to 0. 
 *   Parameters  : 
 *       - core  : Core to monitor the RDC interrupt.
 *   Return      : 
 *       - 1 : The RDC for the given core has interrupted.
 *       - 0 : The RDC for the given core has not interrupted.
 */
unsigned int safesu_rdc_get_interrupt(unsigned int core) {

    if(!driver_fd) open_safesu_driver();

#ifdef __SAFESU_LIB_DEBUG__
    printf("safesu_rdc_get_interrupt\n");
    printf("SAFESU_RDC_IV = 0x%04x\n", read_safesu_reg(SAFESU_RDC_IV));
#endif

    return ((read_safesu_reg(SAFESU_RDC_IV) & (0x00000001 << core)) != 0);
}

/* 
 *  Legacy Functions
 */
void enable_counters (void){    safesu_counters_enable();  }
void disable_counters (void){   safesu_counters_disable(); }
void reset_counters (void){     safesu_counters_reset();   }
void reset_RDC(void){   safesu_rdc_reset(); }

void enable_RDC (void){    safesu_rdc_enable();    }
void disable_RDC (void){    safesu_rdc_disable();  }

struct report_s report_safesu (void){

    if(!driver_fd) open_safesu_driver();

    volatile void *var;
    volatile unsigned int reader;
    struct report_s report;
    unsigned long int safesu_addr = SAFESU_ADDR;

    //Counters
    var=(void*)(safesu_addr+BASE_COUNTERS*4);
    reader=read_safesu_reg((unsigned long int)var);

#ifdef __UART__
    printf("Counters  *******: %d\n",N_COUNTERS);
    printf("SoC events  *******: %d\n",CROSSBAR_INPUTS);
#endif

#ifdef __UART__
    printf("address:%x ,                 Counter0: %10u\n",var,reader);
#endif
    report.ev0 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter1: %10u\n",var,reader);
#endif
    report.ev1 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter2: %10u\n",var,reader);
#endif
    report.ev2 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);  
#ifdef __UART__
    printf("address:%x ,                 Counter3: %10u\n",var,reader);
#endif
    report.ev3 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter4: %10u\n",var,reader);
#endif
    report.ev4 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter5: %10u\n",var,reader);
#endif
    report.ev5 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter6: %10u\n",var,reader);
#endif
    report.ev6 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter7: %10u\n",var,reader);
#endif
    report.ev7 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter8: %10u\n",var,reader);
#endif
    report.ev8 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter9: %10u\n",var,reader);
#endif
    report.ev9 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter10: %10u\n",var,reader);
#endif
    report.ev10 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter11: %10u\n",var,reader);
#endif
    report.ev11 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter12: %10u\n",var,reader);
#endif
    report.ev12 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter13: %10u\n",var,reader);
#endif
    report.ev13 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter14: %10u\n",var,reader);
#endif
    report.ev14 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter15: %10u\n",var,reader);
#endif
    report.ev15 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter16: %10u\n",var,reader);
#endif
    report.ev16 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter17: %10u\n",var,reader);
#endif
    report.ev17 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter18: %10u\n",var,reader);
#endif
    report.ev18 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter19: %10u\n",var,reader);
#endif
    report.ev19 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter20: %10u\n",var,reader);
#endif
    report.ev20 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter21: %10u\n",var,reader);
#endif
    report.ev21 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter22: %10u\n",var,reader);
#endif
    report.ev22 = reader;

    var=(unsigned int*)(var+4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x ,                 Counter23: %10u\n",var,reader);
#endif
    report.ev23 = reader;

    //RDC Watermarks
    var=(unsigned int*)(safesu_addr+BASE_RDC_WATERMARK*4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x , watermark_0 : %u\n",var,reader & 0x000000ff);
    printf("address:%x , watermark_1 : %u\n",var+1, (reader & 0x0000ff00) >> 8);
    printf("address:%x , watermark_2 : %u\n",var+2, (reader & 0x00ff0000) >> 16);
    printf("address:%x , watermark_3 : %u\n\n",var+3, (reader & 0xff000000) >> 24);
#endif
    var=(unsigned int*)(safesu_addr+(BASE_RDC_WATERMARK+1)*4);
    reader=read_safesu_reg((unsigned long int)var);
#ifdef __UART__
    printf("address:%x , watermark_4 : %u\n",var,reader & 0x000000ff);
    printf("address:%x , watermark_5 : %u\n",var+1, (reader & 0x0000ff00) >> 8);
    printf("address:%x , watermark_6 : %u\n",var+2, (reader & 0x00ff0000) >> 16);
    printf("address:%x , watermark_7 : %u\n\n",var+3, (reader & 0xff000000) >> 24);
#endif
    return(report);
}

void masked_and_write (unsigned int entry, unsigned int mask){
    volatile void *p;
    volatile unsigned int current_value;
#ifdef __SAFESU_LIB_DEBUG__
    printf("\n *** Write AND mask register***\n\n");
#endif
    p=(void*)((unsigned long int)SAFESU_ADDR+(entry*4));
    //get current value 
    current_value=read_safesu_reg((unsigned long int)p);
    //set reset bit
    write_safesu_reg((unsigned long int)p, current_value & mask); 
#ifdef __SAFESU_LIB_DEBUG__
    printf("address:%x \n",(SAFESU_ADDR+(entry*4)));
    printf("current value :%x \n",current_value);
    printf("mask:%x \n", mask);
    printf("masked value :%x \n",(current_value & mask));
    printf("\n *** end Write AND mask register ***\n\n");
#endif
}

// ** or mask
void masked_or_write (unsigned int entry, unsigned int mask){
    volatile void *p;
    volatile unsigned int current_value;
#ifdef __SAFESU_LIB_DEBUG__
    printf("\n *** Write OR mask register***\n\n");
#endif
    p=(void*)((unsigned long int)SAFESU_ADDR+(entry*4));
    //get current value 
    current_value=read_safesu_reg((unsigned long int)p);
    //set reset bit
    write_safesu_reg((unsigned long int)p, current_value | mask);
#ifdef __SAFESU_LIB_DEBUG__
    printf("address:%x \n",(SAFESU_ADDR+(entry*4)));
    printf("current value :%x \n",current_value);
    printf("mask:%x \n", mask);
    printf("masked value :%x \n",(current_value & mask));
    printf("\n *** end Write OR mask register ***\n\n");
#endif
}

//Select test mode
unsigned int select_test_mode (unsigned int mode){
    volatile unsigned int MASK_MODE;
    volatile unsigned int CLEAR_MODE = 0xf0000000;
    switch (mode)
    {
        case 0:
            //pass through
#ifdef __SAFESU_LIB_DEBUG__
            printf("No selftests, events are passed through\n");
#endif
            MASK_MODE = 0x000000000;
            break;
        case 1:
            //ALL ones
#ifdef __SAFESU_LIB_DEBUG__
            printf("Selftests, All events set to 1\n");
#endif
            MASK_MODE = 0x40000000;
            break;
        case 2:
            //ALL zeros
#ifdef __SAFESU_LIB_DEBUG__
            printf("Selftests, All events set to 0\n");
#endif
            MASK_MODE = 0x80000000;
            break;
        case 3:
            //First singnal 1 all the other 0
#ifdef __SAFESU_LIB_DEBUG__
            printf("Selftests, First event is 1 all the other are 0\n");
#endif
            MASK_MODE = 0xf0000000;
            break;
        default:
#ifdef __SAFESU_LIB_DEBUG__
            printf("Invalid mode for selftest\n");
#endif
            MASK_MODE = 0x00000000;
            return 1;
    }
    //clear previous mode
    masked_and_write(BASE_CFG,~CLEAR_MODE);
    masked_or_write(BASE_CFG,MASK_MODE);
    return 0;
}
