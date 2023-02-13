# SafeSU RISC-V Linux Driver

Linux Driver to use SafeSU from the user space. The driver is installed as a kernel module.


## Usage instructions:

   1. Clone ISAR release from repository: https://github.com/siemens/isar-riscv

   2. Follow instructions to build firmware image and root filesystem - https://github.com/siemens/isar-riscv/blob/main/doc/NOELV.md

   3. Clone this repository (https://gitlab.bsc.es/caos_hw/hdl_ip/bsc_pmu/-/tree/develop/drivers/linux-driver/linux-kernel-module).
   For this step, RISC-V GCC will be required to compile the source files (https://github.com/riscv-collab/riscv-gnu-toolchain)

   - Note that lkm directory above contains kernel headers for kernel version 5.10.25-r0. If kernel version in ISAR repository is updated, kernel headers will need to be consistently updated (see build/tmp/work/debian-sid-ports-riscv64/linux-noelv in your isar directory to check version).
   - If you want to use the kernel version inside lkm/linux-noelv/5.10.25-r0/ folder to compile the lkm_safesu driver, execute the next commands in your linux terminal:
          
          * cd lkm/linux-noelv/5.10.25-r0/
          * mkdir linux-5.10.25-headers
          * dpkg-deb -x linux-headers-noelv_5.10.25+r0_riscv64.deb linux-5.10.25-headers/

   5. Run 'make' on each folder above, copy output files (lkm/lkm_safesu.ko & libsafesu/test) to the nfs root filesystem obtained from 2 (eg /home/riscv/...).

   6. Run the firmware image and root filesystem from 2 in the Xilinx board (grmon), and access using an SSH client (e.g., using IP 192.168.125.3 below):

    ssh riscv@192.168.125.3 

   7. Load kernel module with:

    sudo insmod lkm_safesu.ko

   - In GRMON's console for the kernel messages following lines should appear confirming load of the driver:

    [  910.770494] lkm_safesu: loading out-of-tree module taints kernel.
    [  911.351005] SAFESU drv: Major = 247 Minor = 0
    [  911.423712] SAFESU drv: Device Driver Init... done

   - A new character device 'safesu' will appear as well in /dev:

    riscv@noelv:~/lkm$ ls -als /dev | grep safesu
    0 crw-rw-rw-  1 root root 247,   0 Jul 13 17:44 safesu

## Reference documentation:

   * Risc-V specification Unprivileged (vol1) / Privileged instructions (vol2): 
        - https://riscv.org/technical/specifications
   * RISC-V PLiC specification:
        - https://github.com/riscv/riscv-plic-spec/blob/master/riscv-plic.adoc
   * Interrupt Cookbook (SiFive): 
        - https://starfivetech.com/uploads/sifive-interrupt-cookbook-v1p2.pdf
   * CLiNT (Core Local Interrupt Controller) specification for Arianne Core (not Noel-V): 
        - https://github.com/pulp-platform/clint
   * SafeSU (/SafePMU) specification: 
        - https://gitlab.bsc.es/caos_hw/hdl_ip/bsc_pmu/-/tree/develop/docs
   * RISC-V assembly programming manual:
        - https://github.com/riscv-non-isa/riscv-asm-manual/blob/master/riscv-asm.md
   * OpenSBI API:
        - https://github.com/riscv-software-src/opensbi/blob/master/docs/library_usage.md
 
