#ifndef _LKM_SAFESU_H_
#define _LKM_SAFESU_H_

#ifndef _IOW

#define	IOC_IN		0x80000000ul	/* copy in parameters */

#define	IOCPARM_MASK	0x1fff		/* parameter length, at most 13 bits */

#define _IOC(inout,group,num,len) \
	(inout | ((len & IOCPARM_MASK) << 16) | ((group) << 8) | (num))
#define	_IOW(g,n,t)	_IOC(IOC_IN,	(g), (n), sizeof(t))

#endif /* _IOW */

typedef struct {
    void (*ub_run_fn)(void *dataset);
    void *dataset;
    unsigned int ub_run_fn_bytes_len;
} ub_run_t;

    // ioctl with write parameters (copy_from_user)
            // Pick letter 'a' - see https://01.org/linuxgraphics/gfx-docs/drm/ioctl/ioctl-number.html
            // [...] You can register the block by patching this file and submitting the patch to Linus Torvalds. 
            // Or you can e-mail me at <mec@shout.net> and I'll register one for you.
#define REG_CURRENT_TASK _IOW('a','a',unsigned int*)
#define DISABLE_PLIC_INT _IOW('b','b',unsigned int*)
#define ENABLE_PLIC_INT  _IOW('c','c',unsigned int*)
#define RUN_UB           _IOW('d','d',void*)



#endif /* _LKM_SAFESU_H_ */