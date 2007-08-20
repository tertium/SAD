#ifndef CORE_H
#define CORE_H

#include "env.h"
#include "main.h"
#include "term.h"

typedef struct _fold Fold;
typedef struct _tree Tree;

/* Fold keeps the list of fold assignement made on
 * a current step, serves for backtraking cleaning
 * t1 -- the node assigned a new foldfather, if (t2 == NULL)
 *    -- the node assigned a new lowest ancestor, otherwise
 * t2 -- the previous lowest ancestor needed to refute t1
 */
struct _fold { Tree * t1, * t2; Fold * next; };

/* lit -- literal (NULL for Gl_Root)
 * gen -- generation of children (0 for childless nodes)
 * limit -- depth available (unit expansion is possible when 0)
 * bound -- substitutions and constraints made when unified
 * fold -- fold assignments made when reduced or advanced
 * up -- next candidate for reduction
 * down -- next candidate for expansion
 * next -- backtracking direction
 * par -- real father (NULL for Gl_Root)
 * sup -- foldfather, if any (== par, otherwise)
 * br -- younger brother, ch->br -- elder son
 * ch == NOT(_) -- complement in the expansion clause
 * ch->next == TOP(_) -- current lowest ancestor needed for refutation
 *         (Gl_Root for autonomous nodes and not refuted nodes)
 *         TOP(_)->sup == NOT(_) -- when refuted, the complement
 *                                  becomes foldfather of TOP(_)
 *                                  with the same depth limit
 */
struct _tree {
    Lit * lit; ui gen, limit;
    Map * bound; Fold * fold;
    Tree * up; litlist * down;
    Tree * next, * par, * sup;
    Tree * br, * ch; int refl;
};

extern ui node_count, step_count;
extern ui depth_count, time_out;
extern ui tree_nodes, tree_depth;

extern int search(ui start, ui stop, ui step);

#endif
