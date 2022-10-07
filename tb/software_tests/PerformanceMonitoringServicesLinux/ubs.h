#ifndef _UBS_H_
#define _UBS_H_

typedef struct {
    void (*fn)(void *); 
    char name[50];
} ub_t;

extern const ub_t ubs[];
extern const int ubs_size;

void ub_ld_l1hit(void *p);  
void ub_st_l1hit(void *p);

#endif /* _UBS_H_ */