/*
 *  env.c -- maintains the initial clause set
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

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>

#include "env.h"

Formula * Gl_Fla = NULL;
Clause * Gl_Cls  = NULL;
Clause * support = NULL;

int prop = 1;
int brand = 0;

static struct vstack
{ ui var, index, flag; struct vstack * next; } * v_st = NULL;

static ui v_index = 0;
static ui exv_put(char * str);

static void index_var(int sign, int br, Term * t)
{
    struct vstack * v; Term * tc = NULL;
    char c = sym_get(t->name)[0];

    switch (c) {
        case '~' :  index_var(1 - sign, 0, ARG4(t));
                    index_var(sign, 0, ARG3(t));
        case '>' :  index_var(sign, 0, ARG2(t));
        case '!' :  index_var(1 - sign, 0, ARG1(t)); break;
        case '@' : case '$' :
                    addlist(v, v_st);
                    if ((c == '@') ^ sign) {
                        v->var = ARG1(t)->name; v->flag = 1;
                        v->index = ++v_index; prop = 0;
                        ARG1(t)->ix = v->index;
                    } else {
                        v->var = ARG1(t)->name; v->flag = 0;
                        v->index = exv_put(sym_get(v->var));
                        ARG1(t)->name = v->index;
                    }
                    index_var(sign, 0, ARG2(t));
                    v_st = v->next; free(v); break;
        case ':' :  index_var(sign, 0, ARG2(t)); break;
        default :   if (t->ch) index_var(sign, 1, t->ch); if (!t->vr) break;
                    forlist(v, v_st) if (t->name == v->var) break;
                    assert(v); if (v->flag) { t->ix = v->index; break; }
                    t->name = v->index; forlist(v, v->next) if (v->flag) {
                        if (tc) tc = tc->br = term_set(v->var, v->index, 1);
                        else    tc = t->ch  = term_set(v->var, v->index, 1); }
    }
    if (br && t->br) index_var(sign, br, t->br);
}

#define TDUP(t)     memcpy(malloc(sizeof(Term)), t, sizeof(Term))

static void brandify(int sign, Term * t);
static char nv_name[32];

static void flatten(int sign, Term * t, Term * s)
{
    Term * nt; ui nvn, nvi;

    for (; s; s = s->br)
    {
        if (s->ix) continue;
        sprintf(nv_name, "br_%lu", nvi = ++v_index);
        nvn = sym_put(nv_name);

        nt = TDUP(t); t->ix = t->vr = 0;
        t->name = sign ? con_code : pmi_code;
        ARG1(t) = nt;
        ARG2(t) = term_set(equ_code, 0, 0);
        ARG1(ARG2(t)) = TDUP(s);
        ARG2(ARG2(t)) = term_set(nvn, nvi, 1);
        s->name = nvn; s->ix = nvi; s->vr = 1;
        s->ch = NULL; brandify(1, ARG2(t));
    }
}

static void brandify(int sign, Term * t)
{
    Term * t1, * t2; ui nvi, nvn;
    char c = sym_get(t->name)[0];
    assert(c != '<');

    switch (c) {
        case '+' : case '-' : break;
        case '&' : case '|' :
                    brandify(sign, ARG1(t));
        case '@' : case '$' : case ':' :
                    brandify(sign, ARG2(t)); break;
        case '~' :  brandify(1 - sign, ARG4(t));
                    brandify(sign, ARG3(t));
        case '>' :  brandify(sign, ARG2(t));
        case '!' :  brandify(1 - sign, ARG1(t)); break;

        case '=' :  t1 = ARG1(t); t2 = ARG2(t);
                    flatten(sign, t, t1->ch);
                    flatten(sign, t, t2->ch);

                    if (sign) break; else t1->br = NULL;

                    while (sym_get(t->name)[0] != '=') t = ARG1(t);
                    t->name = con_code; t->ix = t->vr = 0;

                    sprintf(nv_name, "br_%lu", nvi = ++v_index);
                    nvn = sym_put(nv_name);
                    ARG1(t) = term_set(pmi_code, 0, 0);
                    ARG1(ARG1(t)) = term_set(equ_code, 0, 0);
                    ARG1(ARG1(ARG1(t))) = t1;
                    ARG2(ARG1(ARG1(t))) = term_set(nvn, nvi, 1);
                    ARG2(ARG1(t)) = term_set(equ_code, 0, 0);
                    ARG1(ARG2(ARG1(t))) = t2;
                    ARG2(ARG2(ARG1(t))) = term_set(nvn, nvi, 1);

                    sprintf(nv_name, "br_%lu", nvi = ++v_index);
                    nvn = sym_put(nv_name);
                    ARG2(t) = term_set(pmi_code, 0, 0);
                    ARG1(ARG2(t)) = term_set(equ_code, 0, 0);
                    ARG1(ARG1(ARG2(t))) = term_dup(t2);
                    ARG2(ARG1(ARG2(t))) = term_set(nvn, nvi, 1);
                    ARG2(ARG2(t)) = term_set(equ_code, 0, 0);
                    ARG1(ARG2(ARG2(t))) = term_dup(t1);
                    ARG2(ARG2(ARG2(t))) = term_set(nvn, nvi, 1);
                    break;

        default  :  flatten(sign, t, t->ch);
    }
}

static Clause * cls_add(Clause * cl2, Clause * cl1)
{
    Clause * cl;

    if (!cl1) return cl2; if (!cl2) return cl1;
    forlist(cl, cl1) if (!cl->next) break;
    cl->next = cl2; return cl1;
}

static Clause * cls_mul(Clause * cl1, Clause * cl2)
{
    Clause * cl, * c1, * c2, * cls = NULL;
    Lit * l, * m, * n;

    forlist(c1, cl1) forlist(c2, cl2)
    {
        addlist(cl,cls); cl->lit = NULL;
        cl->length = c1->length + c2->length;

        forlist(m, c1->lit)
        { addlist(l, cl->lit); l->term = m->term;
            l->sign = m->sign; l->annt = m->annt; }

        forlist(m, c2->lit)
        { addlist(l, cl->lit); l->term = m->term;
            l->sign = m->sign; l->annt = m->annt; }

        l = NULL; m = cl->lit; while (m)
        { n = m->next; m->next = l; l = m; m = n; }
        cl->lit = l;
    }

    dellist(c1, cl1) dellist(l, c1->lit);
    dellist(c2, cl2) dellist(l, c2->lit);

    return cls;
}

ui annt = 0;
static void annotate(ui code)
{
    if (code == dhd_code) annt ^= DHD;
}

static Clause * clausify(int sign, Term * t)
{
    Clause * cl, * cl1, * cl2, * cl3, * cl4;
    Term * t1; char c = sym_get(t->name)[0];

    switch (c) {
        case '+' : case '-' :
            if ((c == '+') ^ sign) return NULL;
            cl = malloc(sizeof(Clause));
            cl->lit = NULL; cl->length = 0;
            cl->next = NULL; return cl;
        case '!' :
            return clausify(1 - sign, ARG1(t));
        case ':' :
            annotate(ARG1(t)->name);
            cl = clausify(sign, ARG2(t));
            annotate(ARG1(t)->name);
            return cl;
        case '@' : case '$' :
            return clausify(sign, ARG2(t));
        case '&' : case '|' :
            cl1 = clausify(sign, ARG1(t));
            cl2 = clausify(sign, ARG2(t));
            if ((c == '&') ^ sign) return cls_add(cl1, cl2);
            return cls_mul(cl1, cl2);
        case '<' :
            cl1 = clausify(sign, ARG1(t));
            cl2 = clausify(1 - sign, ARG2(t));
            if (sign) return cls_add(cl1, cl2);
            return cls_mul(cl1, cl2);
        case '>' :
            cl1 = clausify(1 - sign, ARG1(t));
            cl2 = clausify(sign, ARG2(t));
            if (sign) return cls_add(cl1, cl2);
            return cls_mul(cl1, cl2);
        case '~' :
            cl1 = clausify(1 - sign, ARG1(t));
            cl2 = clausify(sign, ARG2(t));
            cl3 = clausify(sign, ARG3(t));
            cl4 = clausify(1 - sign, ARG4(t));
            if (sign) return cls_add(cls_mul(cl1,cl4), cls_mul(cl3,cl2));
            return cls_add(cls_mul(cl2,cl1), cls_mul(cl4,cl3));
        case '=' :
            t1 = term_set(spc_code, 0, 0);
            t1->br = term_set(spc_code, 0, 0);
            ARG1(t1) = ARG1(t); ARG1(t1->br) = ARG2(t);
            ARG1(t)->br = NULL; t->ch = t1;
        default :
            cl = malloc(sizeof(Clause));
            cl->lit = malloc(sizeof(Lit));
            cl->lit->term = t; cl->lit->sign = sign;
            cl->lit->annt = annt; cl->lit->next = NULL;
            cl->length = 1; cl->next = NULL; return cl;
    }
}

void add_formula(char * mark, Term * t)
{
    Clause * cl; Formula * f;
    Lit * l; litlist * s;

    v_index = 0; index_var(0, 0, t);

    if (verbose > 1)
    { putstr("got formula: "); term_out(t,0); putchar('\n'); }

    if (brand) { prop = 0; brandify(0, t); }

    addlist(f, Gl_Fla); f->fterm = t;
    f->mark = mark; f->weight = v_index;

    cl = clausify(0, t); if (!cl) return;
    support = Gl_Cls; Gl_Cls = cl; forlist(cl, Gl_Cls)
    {
        forlist(l, cl->lit)
        {
            if (l->sign) addlist(s, lit_sym(l)->neg);
                    else addlist(s, lit_sym(l)->pos);
            s->lit = l; l->cls = cl;
        }

        if (verbose > 2)
        { putstr("  "); forlist(l, cl->lit) { lit_out(l, 0);
            if (l->next) putstr("  |  "); } putchar('\n'); }

        cl->fla = f; if (!cl->next) { cl->next = support; break; }
    }
}

void lit_out(Lit * l, ui gen)
{
    Term * t = l->term->br; l->term->br = NULL;
//    if (l->annt) printf("<%i :: ", l->annt);
    if (l->term->name == equ_code)
    {
        node_out(NODE(ARG1(ARG1(l->term)),gen));
        putstr(l->sign ? " != " : " = ");
        node_out(NODE(ARG1(ARG2(l->term)),gen));
    } else {
        if (l->sign) putchar('-');
        node_out(NODE(l->term,gen));
    }
//    if (l->annt) putchar('>');
    l->term->br = t;
}

static symlist * syms[1022];

ui sym_put(char * str)
{
    ui i, S = 1; symlist * l;

    for (i = 0; str[i]; i++) S = (S*str[i]) % 1021;

    for (l = syms[S]; l; l = l->next)
        if (!strcmp(l->str, str)) return (ui) l;

    addlist(l, syms[S]); l->str = strdup(str);
    l->pos = l->neg = NULL; return (ui) l;
}

static ui exv_put(char * str)
{
    symlist * l;
    addlist(l, syms[1021]); l->str = str;
    l->pos = l->neg = NULL; return (ui) l;
}

