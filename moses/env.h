/*
 *  env.h -- maintains the initial clause set
 *  Copyright (c) 2001,2004,2007   Andrei Paskevich <atertium@gmail.com>
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

#ifndef ENV_H
#define ENV_H

#include "main.h"
#include "term.h"

typedef struct _formula Formula;
typedef struct _literal Lit;
typedef struct _clause Clause;

struct _formula { Term * fterm; char * mark; ui weight; Formula * next; };
struct _literal { Term * term; ui sign, annt; Clause * cls; Lit * next; };
struct _clause { Lit * lit; Formula * fla; ui length; Clause * next; };

extern Formula * Gl_Fla;
extern Clause * Gl_Cls;
extern Clause * support;

extern int prop, brand;

extern void add_formula(char * mark, Term * t);
extern void lit_out(Lit * l, ui gen);

typedef struct _llist litlist;
struct _llist { Lit * lit; litlist * next; };

typedef struct _slist symlist;
struct _slist { char * str; litlist * pos, * neg; symlist * next; };

extern ui sym_put(char *);
#define sym_lst(n)      ((symlist *) n)
#define sym_get(n)      (sym_lst(n)->str)

#define lit_sym(l)      (sym_lst((l)->term->name))

#define litsame(l)      ((l)->sign ? lit_sym(l)->neg : lit_sym(l)->pos)
#define litcomp(l)      ((l)->sign ? lit_sym(l)->pos : lit_sym(l)->neg)

#endif
