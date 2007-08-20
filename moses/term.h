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
