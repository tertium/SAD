/*
 *  SAD / Moses / core.c -- inference search in a goal-driven calculus
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
#include <stdio.h>
#include <string.h>
#include <assert.h>

#include "core.h"
#include "term.h"

ui node_count, step_count;
ui depth_count, time_out;
ui tree_nodes, tree_depth;

static Tree Root;
static Tree * Gl_Tail, * Gl_Root;
static ui Gl_Gen = 0, lev_limit = 0;

static void new_leaf(Tree * n, Lit * lit);

#define NOT(t)      t->ch
#define TOP(t)      t->ch->next

static void backtrack(Tree * n)
{ Tree * c; Fold * f;

    forlist(c, Gl_Tail)
    {
        cancel(c->bound); c->bound = NULL;

        if (c->gen)
        {
            c->gen = 0; del_gen(Gl_Gen--);
            free(c->ch); c->ch = NULL;
        }

        dellist(f, c->fold)
            if (f->t2) TOP(f->t1) = f->t2;
            else f->t1->sup = f->t1->sup->sup;

        if (c == n) { Gl_Tail = c; break; }
    }
}

static int advance()
{ Tree * n; Fold * f;

    for (n = Gl_Tail; n->par; n = n->par)
    {
        if (n->ch)
        {
            addlist(f, Gl_Tail->fold); f->t1 = TOP(n); f->t2 = NULL;
            NOT(n)->sup = TOP(n)->sup; TOP(n)->sup = NOT(n);
            NOT(n)->limit = TOP(n)->limit;
        }

        if (n->br)
        {   n->br->next = Gl_Tail; Gl_Tail = n->br; return 0; }
    }
    return 1;
}

#define TNODE(t)    NODE(t->lit->term, t->par->gen)
#define NNODE(l)    NODE(l->term, Gl_Gen)
#define FAIL        { del_gen(Gl_Gen--); goto cont; }

#define TLNODE(t)   NODE(t->lit->term->ch, t->par->gen)
#define TRNODE(t)   NODE(t->lit->term->ch->br, t->par->gen)
#define NLNODE(l)   NODE(l->term->ch, Gl_Gen)
#define NRNODE(l)   NODE(l->term->ch->br, Gl_Gen)

#define is_equ(l)   (sym_get(l->term->name)[0] == '=')

#define is_cmpl(l,m)    (l->term->name == m->term->name && l->sign != m->sign)
#define is_same(l,m)    (l->term->name == m->term->name && l->sign == m->sign)

#define account(n)      ((n)->bound = bound, bound = NULL, step_count++)

static int make_step()
{
    Tree * n = Gl_Tail, * p, * q;
    Lit * l = n->lit, * m, * ll;
    Fold * f; ui len;

    if (n->refl) { n->refl = 0;
        if (l->sign && is_equ(l) && unify(TLNODE(n), TRNODE(n)))
            { account(n); return advance(); } }

    while ((p = n->up))
    {
        n->up = p->sup; if (!p->lit) continue;
        if (!is_cmpl(l, p->lit)) continue;
        if (!unify(TNODE(n), TNODE(p))) continue;

        account(n);

        for (q = n->par; q->limit < p->limit; q = q->par)
            if (TOP(q)->limit > p->limit)
            { addlist(f, n->fold); f->t1 = q; f->t2 = TOP(q); TOP(q) = p; }

        return advance();
    }

    while (n->down)
    {
        m = n->down->lit; n->down = n->down->next;

        if ((len = m->cls->length) > 1 && !n->limit)
        { lev_limit = 1; continue; }

//        if (m->annt == ADG) continue;
        if (m->annt & n->lit->annt & DHD) continue;

        add_gen(++Gl_Gen, m->cls->fla->weight);
        if (!unify(TNODE(n), NNODE(m))) FAIL;

        if ((p = n->par->par)) for (p = p->ch->br; p; p = p->br) if (p != n->par)
            if (is_cmpl(n->lit, p->lit) && !constr(TNODE(n), TNODE(p))) FAIL;

        forlist(l, m->cls->lit)
        {
            for (p = n->sup; p; p = p->sup) if (p->lit)
                if (is_same(l, p->lit) && !constr(NNODE(l), TNODE(p))) FAIL;

            forlist(ll, l->next)
                if (is_cmpl(ll, l) && !constr(NNODE(l), NNODE(ll))) FAIL;

            if (!l->sign && is_equ(l) && !constr(NLNODE(l), NRNODE(l))) FAIL;
        }

        account(n); n->gen = Gl_Gen; node_count += len;

        p = malloc(len * sizeof(Tree));
        forlist(l, m->cls->lit) if (l != m) new_leaf(p + --len, l);
        new_leaf(p, m); TOP(n) = Gl_Root; if (!p->br) return advance();
        p->br->next = Gl_Tail; Gl_Tail = p->br; return 0; cont: ;
    }

    n->refl = 1; n->up = n->par;
    n->down = litcomp(n->lit);
    backtrack(prop ? n->par : n->next);
    return (Gl_Tail->lit) ? 0 : -1;
}

static void tree_stats();

int search(ui start, ui stop, ui step)
{
    Lit * l, * m; ui len; Clause * c; Tree * p;
    node_count = step_count = depth_count = 0;
    tree_nodes = tree_depth = 0;

    if (stop == 0) stop = (ui) -1;

    Gl_Tail = Gl_Root = &Root; memset(Gl_Root, sizeof(Tree), 0);

    for (depth_count = start; depth_count <= stop; depth_count += step)
    {
        Gl_Tail->limit = depth_count; lev_limit = 0;

        for (c = Gl_Cls; c != support; c = c->next)
        {
            if (!(len = c->length)) return PRF;

            add_gen(Gl_Tail->gen = ++Gl_Gen, c->fla->weight);
            forlist(l, c->lit) forlist(m, l->next)
                if (is_cmpl(m, l) && !constr(NNODE(l), NNODE(m))) FAIL;
            forlist(l, c->lit)
                if (!l->sign && is_equ(l) && !constr(NLNODE(l), NRNODE(l))) FAIL;
            account(Gl_Tail); node_count += len;

            p = malloc(len * sizeof(Tree));
            forlist(l, c->lit) new_leaf(p + --len, l);
            Gl_Tail->ch->next = Gl_Tail; Gl_Tail = Gl_Tail->ch;

            while (!time_out && !make_step());

            if (time_out) return TIM;

            if (Gl_Tail->lit) { tree_stats(); return PRF; }

            cont: ;
        }
        if (!lev_limit) return UNP;
    }
    return BND;
}

static void new_leaf(Tree * n, Lit * lit)
{
    n->lit = lit; n->up = n->par = n->sup = Gl_Tail;
    n->down = litcomp(lit); n->limit = n->par->limit - 1;
    n->br = n->par->ch; n->par->ch = n; n->ch = NULL;
    n->gen = 0; n->bound = NULL; n->fold = NULL; n->refl = 1;
}

static int trdep(Tree * n)
{
    ui h, mh = 0; for (n = n->ch; n; tree_nodes++, n = n->br)
    if ((h = trdep(n)) > mh) mh = h; return mh + 1;
}

static void tree_out(Tree * n, ui d)
{
    if (n->lit)
    {
        ui i = d; while (i--) putstr("   ");
        lit_out(n->lit, n->par->gen);
        putchar('\n');
    }
    for (n = n->ch; n; n = n->br) tree_out(n, d + 1);
}

static void proof_out()
{
    printf("proof tree (%lu nodes, %lu levels):\n", tree_nodes, tree_depth);
    tree_out(Gl_Root, 0);
}

static void tree_stats()
{
    tree_depth = trdep(Gl_Root) - 1;
    if (verbose) proof_out();
}

