#ifndef MAIN_H
#define MAIN_H

typedef unsigned long int ui;

#define  addlist(i, l)      (i = malloc(sizeof(*l)), i->next = l, l = i)
#define  forlist(i, l)      for(i = l; i; i = i->next)
#define  dellist(i, l)      for(; ((i = l)); l = i->next, free(i))

extern int verbose;

extern ui ver_code, fal_code, ann_code, equ_code;
extern ui neg_code, con_code, dis_code, imp_code;
extern ui eql_code, uni_code, exi_code, spc_code;
extern ui pmi_code, dhd_code;
#define DHD     1

#define putstr(x)   fputs(x, stdout)

#define PRF     '+'
#define UNP     '-'
#define TIM     '?'
#define BND     '_'

#endif
