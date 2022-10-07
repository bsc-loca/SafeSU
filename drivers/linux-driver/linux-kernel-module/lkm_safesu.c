
 #define _XOPEN_SOURCE 500

#include <linux/init.h>
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/fs.h>
#include <asm/uaccess.h>
#include <linux/cdev.h>
#include <linux/uaccess.h> 
#include <linux/interrupt.h>
#include <asm/csr.h>
#include "lkm_safesu.h"
#include "encoding.h"
#include <asm/irqflags.h>

// #define __DEBUG__

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Barcelona Supercomputing Center");
MODULE_DESCRIPTION("Linux module providing raw access to SAFESU registers");
MODULE_VERSION("0.01");

//   adev17    Various contributions  Contributed core 2
//             AHB: 80100000 - 80200000
//             IRQ: 1

#define DEVICE_NAME "SAFESU"
#define SIGSAFESU 314

    //   adev16    Various contributions  Contributed core 2
    //     AHB: 80100000 - 80200000
    //     IRQ: 1


#define IRQ_NO 9

#define SAFESU_ADDR    0x80100000
#define SAFESU_BYTES   240 

    //   clint0    Cobham Gaisler  RISC-V CLINT
    //             AHB: e0000000 - e0100000
    //   plic0     Cobham Gaisler  RISC-V PLIC
    //             AHB: f8000000 - fc000000
    //             16 contexts, 32 interrupt sources

#define PLIC_ADDR    0xf8000000
#define PLIC_BYTES   0x4000000 

dev_t dev = 0;

static struct class *dev_class;
static struct cdev safesu_cdev;
uint8_t *kernel_buffer;

unsigned long phy_offset = 0;

char *safesu_curr_virtual_address = (void *)0;
char *safesu_start_virtual_address = (void *)0;

char *plic_virtual_address = (void *)0;

/* Signaling to Application */
static struct task_struct *task = NULL;
static int signum = 0;

/* Prototypes for device functions */
static loff_t device_llseek(struct file *flip, loff_t offset, int whence);
static int device_open(struct inode *, struct file *);
static int device_release(struct inode *, struct file *);
static ssize_t device_read(struct file *, char *, size_t, loff_t *);
static ssize_t device_write(struct file *, const char *, size_t, loff_t *);
static long device_unlocked_ioctl(struct file *, unsigned int, unsigned long);

static int device_open_count = 0;

#define SAFESU_MSG      DEVICE_NAME " drv: "

/* This structure points to all of the device functions */
static struct file_operations file_ops = {
    .owner = THIS_MODULE,
    .llseek = device_llseek,
    .read = device_read,
    .write = device_write,    
    .unlocked_ioctl = device_unlocked_ioctl,
    .open = device_open,
    .release = device_release
};

//Interrupt handler for IRQ 11. 
static irqreturn_t irq_handler(int irq,void *dev_id) {
    kernel_siginfo_t info;
    pr_info(SAFESU_MSG "Shared IRQ: Interrupt Occurred");
    
    //Sending signal to app
    memset(&info, 0, sizeof(struct siginfo));
    info.si_signo = SIGSAFESU;
    info.si_code = SI_QUEUE;
    info.si_int = 1;
 
    if (task != NULL) {
        pr_info(SAFESU_MSG "Sending signal to app\n");
        if(send_sig_info(SIGSAFESU, &info, task) < 0) {
            pr_info(SAFESU_MSG "Unable to send signal\n");
        }
    }
 
    return IRQ_HANDLED;
}

/* When a process llseeks from our device, this gets called. */

    // Philosophy of the driver is to use "llseek + read" and "llseek + write"
    // This is, placing the pointer in the right location, then exec operation
    // Two ways of placing the pointer:
    //      - The bad one: SEEK_CUR. moves with respect to current position. I don't think
    //                      that it is very useful
    //      - The good one: SEEK_SET. moves with respect to initial location of the file (of the set of regs)
    //                      I think it makes much more sense
loff_t device_llseek(struct file *flip, loff_t offset, int whence) {
    switch(whence) {
            // If whence is SEEK_CUR, the pointer is set to its current location plus offset.
        case SEEK_CUR:
                    // Check it's not going beyond end of the region for the dev, with respect current offset
                if(offset<=SAFESU_BYTES-phy_offset) {                    
                    iounmap(safesu_curr_virtual_address);                    
                    phy_offset += offset;    
                    if((safesu_curr_virtual_address = ioremap(((unsigned long int)SAFESU_ADDR+phy_offset), 
                                                    SAFESU_BYTES-phy_offset)) == NULL){
                        pr_err(SAFESU_MSG "llseek(..): Cannot remap virtual address to new offset\n");  
                        goto llseek_err;      
                    }                
                } else {
                    return -EINVAL;
                }
            break;

            // If whence is SEEK_END, the pointer is set to the size of the file plus offset.
            // If whence is SEEK_HOLE, the offset of the start of the next hole greater than or equal to the supplied offset is returned. The definition of a hole immediately follows this list.
            // If whence is SEEK_DATA, the file pointer is set to the start of the next non-hole file region greater than or equal to the supplied offset.
        case SEEK_END:
        case SEEK_HOLE:
        case SEEK_DATA:
                return -EINVAL;
            break;

            // If whence is SEEK_SET, the pointer is set to offset bytes.                    
        default:    // SEEK_SET
                if(offset<=SAFESU_BYTES) {                    
                    iounmap(safesu_curr_virtual_address);
                    phy_offset = offset;                    
                    if((safesu_curr_virtual_address = ioremap(((unsigned long int)SAFESU_ADDR+offset), 
                                                    SAFESU_BYTES-offset)) == NULL){
                        pr_err(SAFESU_MSG "llseek(..): Cannot remap virtual address to new offset\n");        
                        goto llseek_err;      
                    }                
                } else {
                    return -EINVAL;
                }
            break;
    }

#ifdef  __DEBUG__
    pr_info(SAFESU_MSG "seek function exit, safesu_curr_virtual_address= 0x%016lx / phy= 0x%08lx!\n",  
                (unsigned long int)safesu_curr_virtual_address, (unsigned long int)SAFESU_ADDR+phy_offset); 
#endif

    return phy_offset;

llseek_err:
    return -EFAULT;
}

/* When a process reads from our device, this gets called. */
static ssize_t device_read(struct file *flip, char *buffer, size_t len, loff_t *offset) {

    unsigned int out_len;
    char my_buf[SAFESU_BYTES];

              // Check if ask for more bytes than those remaining in safesu_bytes
    out_len = (len>SAFESU_BYTES-phy_offset)?SAFESU_BYTES-phy_offset:len;

#ifdef  __DEBUG__
    pr_info(SAFESU_MSG "read function called, len=%ld/out_len=%u, safesu_curr_virtual_address= 0x%016lx! / phy= 0x%08lx!\n", len, out_len, 
                    (unsigned long int)safesu_curr_virtual_address, (unsigned long int)SAFESU_ADDR+phy_offset);    
#endif

    if(!out_len) {
        pr_info(SAFESU_MSG "EOF - no bytes left at input\n");
        return -1;
    }

#ifdef  __DEBUG__
    int i;
    for(i=0; i<out_len; i++) {
        pr_info(SAFESU_MSG "byte %d: %02x\t", i, ((char *)safesu_curr_virtual_address)[i]);
    }
    pr_info("\n");
#endif

    // extract data from IO, but still put it within the kernel
    memcpy_fromio(my_buf, safesu_curr_virtual_address, out_len);

    // and now move it to user-space
    if( copy_to_user(buffer, my_buf, out_len) )
    {
        pr_err(SAFESU_MSG "Data Read : Err!\n");
    }

    // now we are to remap 'forward' the bytes that we've offered to userspace.
    // doesn't make much sense / file-like philosophy, but that's how read should do    
    iounmap(safesu_curr_virtual_address);
    phy_offset += out_len;    
    if((safesu_curr_virtual_address = ioremap(((unsigned long int)SAFESU_ADDR+phy_offset), 
                                    SAFESU_BYTES-phy_offset)) == NULL){
        pr_err(SAFESU_MSG "read(..): Cannot remap virtual address to new offset\n");        
    }

#ifdef  __DEBUG__
    pr_info(SAFESU_MSG "read function exit, len=%u, safesu_curr_virtual_address= 0x%016lx / phy= 0x%08lx!\n", out_len, 
                    (unsigned long int)safesu_curr_virtual_address, (unsigned long int)SAFESU_ADDR+phy_offset);    
#endif

    return out_len;
}

/* Called when a process tries to write to our device */
static ssize_t device_write(struct file *flip, const char *buffer, size_t len, loff_t *offset) {

    unsigned int out_len;    
    char my_buf[SAFESU_BYTES];

#ifdef  __DEBUG__
    pr_info(SAFESU_MSG "write function called, safesu_curr_virtual_address= 0x%016lx / phy= 0x%08lx!\n",
                    (unsigned long int)safesu_curr_virtual_address, (unsigned long int)SAFESU_ADDR+phy_offset);       
#endif

        // Check if ask for more bytes than those remaining in safesu_bytes
    out_len = (len>SAFESU_BYTES-phy_offset)?SAFESU_BYTES-phy_offset:len;

    if(!out_len) {
        pr_info(SAFESU_MSG "EOF - no bytes left at input\n");
        return -1;
    }

    // first retrieve data provided by the user and put it in the kernel
    if(copy_from_user(my_buf, buffer, out_len)) {
        pr_err("Could not cpy from buffer to my_buf");
    }

    // now copy from the kernel to io space
    memcpy_toio((void *)safesu_curr_virtual_address, my_buf, out_len);

#ifdef  __DEBUG__
    int i;
    pr_info("We wrote: \n");
    for(i=0; i<out_len; i++) {
        pr_info(SAFESU_MSG "byte %d: %02x\t", i, ((char *)safesu_curr_virtual_address)[i]);
    }
    pr_info("\n");
#endif

    // and now move the pointer to next location. Note we're using same pointer for read and write    
    iounmap(safesu_curr_virtual_address);
    phy_offset += out_len;    
    if((safesu_curr_virtual_address = ioremap(((unsigned long int)SAFESU_ADDR+phy_offset), 
                                    SAFESU_BYTES-phy_offset)) == NULL){
        pr_err(SAFESU_MSG "write(..): Cannot remap virtual address to new offset\n");        
    }

#ifdef  __DEBUG__
    pr_info(SAFESU_MSG "write function exit, safesu_curr_virtual_address= 0x%016lx / phy= 0x%08lx!\n", 
                    (unsigned long int)safesu_curr_virtual_address, (unsigned long int)SAFESU_ADDR+phy_offset);    
#endif

    return out_len;
}

    // These are a couple of functions to enable/disable (supervisor/linux-level)-interrupts
    // I'm just using them for testing, see call in ioctl. The idea (untested), is being able
    // to run a full microbenchmark in kernel space, with interrupts disabled
inline static void enable_int(void) {
    arch_local_irq_enable();
}

inline static void disable_int(void) {
    arch_local_irq_disable();
}

static long device_unlocked_ioctl(struct file *flip, unsigned int cmd, unsigned long arg) {

    pr_info("performing ioctl (%08x) vs (%08x)\n", cmd & ~0xc0000000, (unsigned int)RUN_UB & ~0xc0000000);
    char my_fn[1024 * 1024];
    void (*ub_kernel_ptr)(void *) = (void*)&my_fn[0];
    ub_run_t    ub;
    
    switch(cmd & ~0xc0000000) {

                // This ioctl 'registers current (user) task' as receiver of a signal
                // this signal is sent when an interrupt occurs, from 'irq_handler' routine 
                // (if any task registered)
                // -- The mechanism for interrupts is NOT working. request_irq() mechanism won't return
                // success. 
        case (REG_CURRENT_TASK & ~0xc0000000):

#ifdef  __DEBUG__
                pr_info("REG_CURRENT_TASK\n");
#endif

                task = get_current();
                signum = SIGSAFESU;
            break;

        case (DISABLE_PLIC_INT & ~0xc0000000):                
                disable_int();
            break;

        case (ENABLE_PLIC_INT & ~0xc0000000):
                enable_int();
            break;

        case (RUN_UB & ~0xc0000000):
                    // in order to be able to access data from userspace, we need first to "copy_from_user" it
                    // to kernel space.
                copy_from_user((void *)&ub, (void *)arg, sizeof(ub_run_t));                
                copy_from_user((void *)ub_kernel_ptr, (void *)ub.ub_run_fn, ub.ub_run_fn_bytes_len);
                pr_info("allocating %d bytes\n", ub.ub_run_fn_bytes_len);
                void *my_kmem = kmalloc(1024 * 1024, GFP_KERNEL);
                pr_info("done allocation");
                
                pr_info(SAFESU_MSG "EOF - no bytes left at input\n");

                //ub.ub_run_fn(my_kmem);
                ub_kernel_ptr(my_kmem);
                pr_info("#done!\n");
            break;
    }
    
    return 0;
}

/* Called when a process opens our device */
static int device_open(struct inode *inode, struct file *file) {
	 /* If device is open, return busy */
	if (device_open_count) {
        return -EBUSY;
	}

    device_open_count++;
	try_module_get(THIS_MODULE);

    /*Allocate I/O memory regions*/

        // ------- SAFESU

    // request_mem_region tells the kernel that your driver is going to use this range of 
    // I/O addresses, which will prevent other drivers to make any overlapping call to 
    // the same region through request_mem_region. This mechanism does not do any kind of 
    // mapping, it's a pure reservation mechanism, which relies on the fact that all 
    // kernel device drivers must be nice, and they must call request_mem_region, check 
    // the return value, and behave properly in case of error.

        // jjorba: So, it's not needed, but somewhat elegant to do it.

    if((request_mem_region(SAFESU_ADDR, SAFESU_BYTES, "safesu_memory")) == NULL){
        pr_err(SAFESU_MSG "Cannot allocate I/O memory for SAFESU\n");
        goto r_device;
    }

    /*Obtain the physical address of the safesu*/

            // ioremap maps region of I/O memory to a virtual addr accessible by the kernel.
    if((safesu_curr_virtual_address = ioremap(SAFESU_ADDR, SAFESU_BYTES)) == NULL){
        pr_err(SAFESU_MSG "Cannot obtain the virtual address for SAFESU\n");
        goto r_device;
    }

    if((safesu_start_virtual_address = ioremap(SAFESU_ADDR, SAFESU_BYTES))== NULL){
        pr_err(SAFESU_MSG "Cannot obtain the virtual address for SAFESU\n");
        goto r_device;
    }

        // ------- PLIC


    // jjorba: This driver is not meant to deal with PLIC. I'm mapping registers anyway to take 
    // a look at its regs / understand what's going on.

    // Note that:
    //      mstatus won't be accessible, as machine mode is handled from hypervisor (opensbi layer)
    //      sstatus doesn't seem to exist in the platform (exception when attempting to read_csr on
    //      it). 

    // jjorba: I'm reserving it also here. Since there must be already another PLIC
    // driver in the kernel, may not be fully consistent (i.e. the other driver may
    // need to reserve it). Anyway, doing it, and seems not to pose trouble.

    if((request_mem_region(PLIC_ADDR, PLIC_BYTES, "plic_memory")) == NULL){
        pr_err(SAFESU_MSG "Cannot allocate I/O memory for PLIC\n");
        goto r_device;
    }

    /*Obtain the physical address of the safesu*/

        // ioremap maps region of I/O memory to a virtual addr accessible by the kernel.
    if((plic_virtual_address = ioremap(PLIC_ADDR, PLIC_BYTES)) == NULL){
        pr_err(SAFESU_MSG "Cannot obtain the virtual address for PLIC\n");
        goto r_device;
    }

// unsigned int my_buf[100];
// 
//     /*Tell which interrupts are enabled*/
// #define INTERRUPT_ENABLE_REG_OFFSET 0x002000
// #define CONTEXT_OFFSET  0x80
// #define N_CONTEXTS  10

//     memcpy_fromio((void *)my_buf, plic_virtual_address + INTERRUPT_ENABLE_REG_OFFSET, 
//                 CONTEXT_OFFSET * 4 * N_CONTEXTS);

//     int ct;
//     for(ct=0; ct<N_CONTEXTS; ++ct) {    
//         int reg;
//         for(reg=0; reg<10; ++reg) {
//             printk("PLIC [%08x]/INTERRUPT_ENABLE_REG\tct %d\t reg %d= %08x\r\n", 
//                 plic_virtual_address + INTERRUPT_ENABLE_REG_OFFSET + CONTEXT_OFFSET * ct + reg*4, ct, reg, my_buf[0]);
//         }
//     }

// #define INTERRUPT_1_PRIORITY_REG_OFFSET 0x000004    
// #define N_INTERRUPTS 24
//     memcpy_fromio((void *)my_buf, plic_virtual_address + INTERRUPT_1_PRIORITY_REG_OFFSET, 4*N_INTERRUPTS /* two 32-bit regs*/);

//     int i;
//     for(i=0; i<N_INTERRUPTS; ++i) {
//         printk("PLIC [%08x]/INTERRUPT_%02d_PRIORITY_REG= %08x\r\n", plic_virtual_address + INTERRUPT_1_PRIORITY_REG_OFFSET + 4*i, i+1, my_buf[i]);
//     }

    phy_offset = 0;

    pr_info(SAFESU_MSG "device_open(...): Ok\n");

	return 0;

r_device:
    return -EFAULT;
}
/* Called when a process closes our device */
static int device_release(struct inode *inode, struct file *file) {

    struct task_struct *ref_task = get_current();

	 /* Decrement the open counter and usage count. Without this, the module would not unload. */    
    iounmap(safesu_curr_virtual_address);
    release_mem_region(SAFESU_ADDR, SAFESU_BYTES);    

    iounmap(plic_virtual_address);
    release_mem_region(PLIC_ADDR, PLIC_BYTES);  

    device_open_count--;

    module_put(THIS_MODULE);

    safesu_curr_virtual_address = (void *)0;    

    pr_info(SAFESU_MSG "device_release(...): Ok\n");
    
    //delete the task
    if(ref_task == task) {
        task = NULL;
    }

    return 0;
}

static char *chmod_dev(struct device *dev, umode_t *mode)
{
    if (!mode) return NULL;
            
    *mode = 0666;

    return NULL;
}

static int __init lkm_safesu_init(void) {

    /*Allocating Major number*/
    if((alloc_chrdev_region(&dev, 0, 1, "safesu_dev")) <0){
            pr_err(SAFESU_MSG "Cannot allocate major number\n");
            return -1;
    }
    pr_info(SAFESU_MSG "Major = %d Minor = %d \n",MAJOR(dev), MINOR(dev));

    /*Creating cdev structure*/
    cdev_init(&safesu_cdev, &file_ops);

    /*Adding character device to the system*/
    if((cdev_add(&safesu_cdev,dev,1)) < 0){
        pr_err(SAFESU_MSG "Cannot add the device to the system\n");
        goto r_class;
    }

    /*Creating struct class*/
    if((dev_class = class_create(THIS_MODULE,"safesu_class")) == NULL){
        pr_err(SAFESU_MSG "Cannot create the struct for class\n");
        goto r_class;
    }

    dev_class->devnode = chmod_dev;

    /*Creating device in /dev, avoid need to mknod from user side */
    if((device_create(dev_class,NULL,dev,NULL,"safesu")) == NULL){
        pr_err(SAFESU_MSG "Cannot create device\n");
        goto r_device;
    }

    // int err_code = 0;
    // if (err_code = request_irq(IRQ_NO, irq_handler, 0, "safesu_device", (void *)(irq_handler))) {
    //     pr_info(SAFESU_MSG "cannot register IRQ: %d ", err_code);
    //     goto r_irq;
    // }

    pr_info(SAFESU_MSG "Device Driver Init... done\n");

    return 0;

r_irq:
    // free_irq(IRQ_NO,(void *)(irq_handler));
r_device:
    class_destroy(dev_class);
r_class:
    unregister_chrdev_region(dev,1);
    return -EFAULT;
}

static void __exit lkm_safesu_exit(void) {
    device_destroy(dev_class,dev);
    class_destroy(dev_class);
    cdev_del(&safesu_cdev);
    unregister_chrdev_region(dev, 1);
    pr_info(SAFESU_MSG "Device Driver Remove...Done!!!\n");
}

/* Register module functions */
module_init(lkm_safesu_init);
module_exit(lkm_safesu_exit);

