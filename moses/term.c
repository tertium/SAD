/*
 *  SAD / Moses / term.c -- unification: solves equations and constraints
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

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>

#include "env.h"
#include "term.h"

Map ** Gl_Map;

void add_gen(ui gen, ui weight)
{
    ui l = Gl_Map ? (ui) Gl_Map[0] : 0;

    if (gen > l) {
        l = ((gen >> 8) + 1) << 8;
        Gl_Map = realloc(Gl_Map, l * sizeof(Map *));
        Gl_Map[0] = (void *) l - 1;
    }

    if (!weight) { Gl_Map[gen] = NULL; return; }
    Gl_Map[gen] = calloc(weight + 1, sizeof(Map));
}

void del_gen(ui gen)
{   free(Gl_Map[gen]); Gl_Map[gen] = NULL; }


Map * bound = NULL;

void cancel(Map * ml)
{ Map * c;
    while (ml) if (ml->node.term) { ml->node.term = NULL; ml = ml->next; }
    else { c = ml->cons; ml->cons = c->cons; ml = c->next; free(c); }
}


#define BR(n)           NODE(n.term->br, n.gen)
#define CH(n)           NODE(n.term->ch, n.gen)
#define LEQ(n1, n2)     (n1.gen == n2.gen && n1.term == n2.term)
#define VEQ(n1, n2)     (n1.gen == n2.gen && n1.term->name == n2.term->name)
#define NEQ(n1, n2)     (n1.term->name == n2.term->name)

#define MAP(n)          (Gl_Map[n.gen] + n.term->ix)
#define LINK(n)         (MAP(n)->node)
#define FIND(n)         while (n.term->ix && LINK(n).term) n = LINK(n)

static Node curr;

static int isin(Node n)
{
    if (!n.term) return 0; if (isin(BR(n))) return 1;
    FIND(n); return (VEQ(n, curr)) ? 1 : isin(CH(n));
}


static Node p1, p2;

static inline int cns(Map * m)
{
    Map * c = malloc(sizeof(Map)); c->node = p1; c->prim = p2;
    c->cons = m->cons; m->cons = c; c->next = bound; bound = m;
    return 0;
}

#define constrainer(n1, n2)     (NEQ(n1, n2) ? subconstrainer(CH(n1), CH(n2)) : 0)

static int subconstrainer(Node n1, Node n2)
{
    if (!n1.term && !n2.term) return 1;
    if (!n1.term || !n2.term) return 0;
    if (!subconstrainer(BR(n1), BR(n2))) return 0;
    FIND(n1); FIND(n2); if (LEQ(n1, n2)) return 1;
    if (n1.term->ix && n2.term->ix)
        return  (n1.gen < n2.gen) ? cns(MAP(n1)) :
                (n1.gen > n2.gen) ? cns(MAP(n2)) :
                (n1.term->name < n2.term->name) ? cns(MAP(n1)) :
                (n1.term->name > n2.term->name) ? cns(MAP(n2)) : 1;
    if (n1.term->ix)
        return  ((curr = n1, isin(CH(n2))) ? 0 : cns(MAP(n1)));
    if (n2.term->ix)
        return  ((curr = n2, isin(CH(n1))) ? 0 : cns(MAP(n2)));
    return constrainer(n1, n2);
}

int constr(Node n1, Node n2)
{
    p1 = n1; p2 = n2;
    if (!constrainer(n1, n2)) return 1;
    cancel(bound); bound = NULL; return 0;
}


static Node * eqarr = NULL;
static int eqind = 0, eqlen = 0;

#define unifier(n1, n2)     (NEQ(n1, n2) ? subunifier(CH(n1), CH(n2)) : 0)

static int subunifier(Node n1, Node n2)
{
    if (!n1.term && !n2.term) return 1;
    if (!n1.term || !n2.term) return 0;
    if (!subunifier(BR(n1), BR(n2))) return 0;
    FIND(n1); FIND(n2); if (LEQ(n1, n2)) return 1;
    if (!n1.term->vr && !n2.term->vr) return unifier(n1, n2);
    if (VEQ(n1, n2)) return 1;
    if (eqind == eqlen)
        eqarr = realloc(eqarr, (eqlen += 8096) * sizeof(Node));
    eqarr[eqind++] = n1; eqarr[eqind++] = n2; return 1;
}


#define unf(m, n)   ( m->node = n, m->next = bound, bound = m, 1 )

static inline int as_unifier(Node n1, Node n2)
{
    FIND(n1); FIND(n2); if (LEQ(n1, n2)) return 1;
    if (n1.term->ix && n2.term->ix)
        return  (n1.gen < n2.gen) ? unf(MAP(n1), n2) :
                (n1.gen > n2.gen) ? unf(MAP(n2), n1) :
                (n1.term->name < n2.term->name) ? unf(MAP(n1), n2) :
                (n1.term->name > n2.term->name) ? unf(MAP(n2), n1) : 1;
    if (n1.term->ix)
        return  ((curr = n1, isin(CH(n2))) ? 0 : unf(MAP(n1), n2));
    if (n2.term->ix)
        return  ((curr = n2, isin(CH(n1))) ? 0 : unf(MAP(n2), n1));
    return unifier(n1, n2);
}

int unify(Node n1, Node n2)
{
    Map * l, * c;

    if (!unifier(n1, n2)) goto fail;
    while (eqind) if (!as_unifier(eqarr[--eqind], eqarr[--eqind])) goto fail;

    forlist(l, bound) for (c = l->cons; c; c = c->cons)
        if (!constr(c->node, c->prim)) return 0;
    return 1;

fail:
    forlist(bound, bound) bound->node.term = NULL; eqind = 0; return 0;
}


Term * term_set(ui nm, ui ix, ui vr)
{
    Term * t = malloc(sizeof(Term));
    t->name = nm; t->ix = ix; t->vr = vr;
    t->ch = t->br = NULL; return t;
}

Term * term_dup(Term * t)
{
    Term * s = malloc(sizeof(Term));
    s->ch = t->ch ? term_dup(t->ch) : NULL;
    s->br = t->br ? term_dup(t->br) : NULL;
    s->ix = t->ix; s->vr = t->vr;
    s->name = t->name; return s;
}

void term_del(Term * t)
{ if (t->ch) term_del(t->ch); if (t->br) term_del(t->br); free(t); }

void term_out(Term * t, int br)
{
    char c = sym_get(t->name)[0];
    switch (c) {
        case '+' :  putchar('T'); break;
        case '-' :  putchar('F'); break;
        case ':' :  term_out(ARG2(t), 0); break;
        case '!' :  putstr("- "); term_out(ARG1(t), 0); break;
        case '=' : case '&' : case '|' : case '>' : case '~' :
                    putchar('('); term_out(ARG1(t), 0);
                    printf(" %c ", c); term_out(ARG2(t), 0);
                    putchar(')'); break;
        case '@' : case '$' :
                    printf("%c ", c); term_out(ARG1(t), 0);
                    putchar(' '); term_out(ARG2(t), 0); break;
        default  :  putstr(sym_get(t->name)); if (t->ch)
                    { putchar('('); term_out(t->ch, 1); putchar(')'); }
                    if (br && t->br) { putstr(", "); term_out(t->br, 1); }
    }
}

void node_out(Node n)
{
    Node m = n; if (n.gen) FIND(n);
    if (!LEQ(n,m)) printf("%s{%lu} <- ", sym_get(m.term->name), m.gen);
    putstr(sym_get(n.term->name));
    if (n.gen && n.term->vr) printf(n.term->ix ? "{%lu}" : "[%lu]", n.gen);
    if (n.term->vr && !n.term->ix && !n.gen) putstr("[]"); if (!n.term->vr)
    { putchar('('); if (n.term->ch) node_out(CH(n)); putchar(')'); }
    if (m.term->br) { putstr(", "); node_out(BR(m)); }
}
