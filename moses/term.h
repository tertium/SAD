/*
 *  term.h -- datastructures for terms and substitutions
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

#ifndef TERM_H
#define TERM_H

#include "main.h"
#include "term.h"

typedef struct _term Term;
typedef struct _node Node;
typedef struct _map  Map;

struct _term { ui name, ix, vr; Term * br, * ch; };
struct _node { Term * term; ui gen; };
struct _map  { Node node, prim; Map * next, * cons; };

#define NODE(t, g)      ((Node) { t, g })
#define ARG1(t)         ((t)->ch)
#define ARG2(t)         ((t)->ch->br)
#define ARG3(t)         ((t)->ch->br->br)
#define ARG4(t)         ((t)->ch->br->br->br)

extern void add_gen(ui gen, ui weight);
extern void del_gen(ui gen);

extern Map * bound;

extern int  unify(Node n1, Node n2);
extern int  constr(Node n1, Node n2);
extern void cancel(Map * ml);

extern Term * term_set(ui nm, ui ix, ui vr);
extern Term * term_dup(Term * t);
extern void term_del(Term * t);
extern void term_out(Term * t, int br);
extern void node_out(Node n);
#endif
