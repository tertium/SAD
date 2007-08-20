/*
 *  SAD / Moses / main.c -- parses the input problem and launches the search
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
#include <ctype.h>
#include <sys/times.h>
#include <unistd.h>
#include <signal.h>

#include "main.h"
#include "core.h"
#include "env.h"
#include "term.h"

#define isspec(c)   (c == '(' || c == ')' || c == '?')
#define isconn(c)   (c == '+' || c == '-' || c == ':' || c == '=' || \
                        c == '!' || c == '&' || c == '|' || c == '>' || \
                        c == '~' || c == '@' || c == '$')
#define issymb(c)   (c == '_' || c == '#' || isalnum(c))
#define isvalid(c)  (isspec(c) || issymb(c) || isconn(c))

int verbose = 0;

ui ver_code, fal_code, ann_code, equ_code;
ui neg_code, con_code, dis_code, imp_code;
ui eql_code, uni_code, exi_code, spc_code;
ui pmi_code, dhd_code;

static ui code(char c)
{
    switch (c) {
        case '+' : return ver_code; case '-' : return fal_code;
        case ':' : return ann_code; case '=' : return equ_code;
        case '!' : return neg_code; case '&' : return con_code;
        case '|' : return dis_code; case '>' : return imp_code;
        case '~' : return eql_code; case '@' : return uni_code;
        case '$' : return exi_code; default  : return 0; }
}

static int  last;
static char str[128];

static int get_lexem()
{ int i, c;
    do { c = getc(stdin); if (c == EOF) return (last = 0); }
    while (!isvalid(c)); if (!issymb(c)) return (last = c);
    for (i = 0; i < 126 && issymb(c); c = getc(stdin)) str[i++] = c;
    str[i] = '\0'; ungetc(c, stdin); return (last = 'v');
}

static Term * read_formula()
{
    Term * t, * tc = NULL; char c = last;

    if (last == 'v') {
        t = term_set(sym_put(str), 0, 1);
        get_lexem(); if (last != '(') return t; t->vr = 0; get_lexem();
        while (last != ')') if (tc) tc = tc->br = read_formula();
                            else    tc = t->ch  = read_formula();
        get_lexem(); return t;
    }

    t = term_set(code(c), 0, 0); get_lexem();
    switch (c) {
        case '+' : case '-' : break;
        case '@' : case '$' : case ':' :
                    ARG1(t) = term_set(sym_put(str), 0, 1);
                    get_lexem(); ARG2(t) = read_formula(); break;
        default  :  ARG1(t) = read_formula(); if (c == '!') break;
                    ARG2(t) = read_formula(); if (c == '=') brand = 1;
                    if (c == '~') ARG3(t) = term_dup(t->ch);
    }
    return t;
}

static ui start = 1, stop = 0, step = 1;

void alarm_handler(int n) { time_out = 1; }

/*
 *  And the children of Israel did eat manna forty years,
 *  until they came to a land inhabited; they did eat manna,
 *  until they came unto the borders of the land of Canaan.
 *  (Exodus 16:35)
 */

int main(int argc, char** argv)
{
    Formula *f, *g, *fls = NULL;
    long msec; struct sigaction action;
    struct tms tp1, tp2; clock_t tt;
    char res; ui time, i, nb = 0;

    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    action.sa_handler = alarm_handler;
    sigaction(SIGALRM, &action, NULL);

    for (i = 1; i < argc; i++)
    {
        if (argv[i][0] == 'i' && i+1 < argc) start = atoi(argv[++i]); else
        if (argv[i][0] == 'f' && i+1 < argc) stop  = atoi(argv[++i]); else
        if (argv[i][0] == 'b') nb = 1; else
        if (argv[i][0] == 'v') verbose++; else
        {
            fprintf(stderr, "Options:  i <num>   initial depth bound\n");
            fprintf(stderr, "          f <num>   final depth bound (0 for no limit)\n");
            fprintf(stderr, "          v         add one level of verbosity (0-3)\n");
            fprintf(stderr, "          b         don't use Brand's modification\n");
            fprintf(stderr, "                    even for problems with equality\n");
            return 1;
        }
    }
    if (start < 1) start = 1; if (stop < start) stop = 0;

    ver_code = sym_put("+"); fal_code = sym_put("-"); ann_code = sym_put(":");
    equ_code = sym_put("="); neg_code = sym_put("!"); con_code = sym_put("&");
    dis_code = sym_put("|"); imp_code = sym_put(">"); eql_code = sym_put("~");
    uni_code = sym_put("@"); exi_code = sym_put("$"); spc_code = sym_put("#");
    pmi_code = sym_put("<"); dhd_code = sym_put("DHD");

    get_lexem(); while (last != '?')
    {
        addlist(f,fls); f->mark = strdup(str);
        get_lexem(); f->fterm = read_formula();
    }
    addlist(f,fls); f->mark = "#";
    f->fterm = term_set(neg_code, 0, 0);
    get_lexem(); f->fterm->ch = read_formula();
    time  = atoi(str); if (time < 1) time = 180;

    if (nb) brand = 0; g = NULL;
    forlist(f, fls->next) { fls->next = g; g = fls; fls = f; }
    fls->next = g; dellist(f, fls) add_formula(f->mark, f->fterm);

    printf("launch (time limit: %lu sec, initial db: %lu, final db: %lu)\n",
                                                        time, start, stop);
    fflush(stdout);

    time_out = 0; alarm(time); times(&tp1);
    res = search(start, stop, step); times(&tp2);
    alarm(0); tt = (tp2.tms_stime - tp1.tms_stime)
                 + (tp2.tms_utime - tp1.tms_utime);
    msec = tt * 1000 / sysconf(_SC_CLK_TCK);

    switch (res) {
        case PRF : putstr("proved"); break;
        case UNP : putstr("found unprovable"); break;
        case BND : putstr("reached final depth bound"); break;
        case TIM : putstr("timeout"); break;
    }
    printf(" in %lu ms", msec);
    if (res == PRF) printf(" -- proof tree nodes: %lu -- proof tree depth: %lu",
                                                            tree_nodes, tree_depth);
    printf("\ninference steps: %lu -- born nodes: %lu -- depth bound: %lu\n",
                                                step_count, node_count, depth_count);
    return 0;
}
