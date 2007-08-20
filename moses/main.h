/*
 *  SAD / Moses / main.h -- common types, variables, and macros
 *  Copyright (C) 2001-2004  SAD Development Team (see ../README)
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

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
