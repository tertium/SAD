/*
 *  main.h -- common types, variables, and macros
 *  Copyright (c) 2001-2008  Andrei Paskevich <atertium@gmail.com>
 *
 *  This file is part of SAD/Moses - a simple goal-driven tableau prover.
 *
 *  SAD/Moses is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  SAD/Moses is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
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
