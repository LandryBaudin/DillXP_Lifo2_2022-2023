#include <stdbool.h>
#include <stdlib.h>
#include <limits.h>

#define MAX_SIZE INT_MAX-1

#define CIRCULAR_LIST(name) \
  static void *name##_circular_list = NULL; \
  static circular_list_t name = (circular_list_t)&name##_circular_list

typedef struct cl **circular_list_t;

struct cl {
  struct cl *next;
};

/*@
predicate separated_from_list{L} (struct cl* element, \list<struct cl*> l) =
	\forall integer n; 0 <= n < \length(l) ==>
	\separated(\nth(l,n), element);

predicate all_separated_in_list{L}(\list<struct cl*> l) =
	\forall integer n; 0 <= n < \length(l) ==>
		\forall integer m; n < m < \length(l) ==>
			\separated(\nth(l,n), \nth(l,m));

predicate in_list{L} (struct cl* element, \list<struct cl*> l) =
	\exists integer n;
	0 <= n < \length(l) && \nth(l,n) == element;


predicate unchanged{L1,L2}(\list<struct cl*> l) =
	\length(\at(l,L1)) == \length(\at(l,L2)) &&
	\forall integer n; 0 <= n < \length(l) ==>
		(\valid{L1}(\nth(l,n)) && \valid{L2}(\nth(l,n)) &&
		\at(\nth(l,n)->next,L1) == \at(\nth(l,n)->next,L2));

*/

/*@

inductive linked_ll_aux{L}(struct cl *root, struct cl *bound, \list<struct cl*> l) {

	case linked_ll_aux_bound{L}:
		\forall struct cl *bound;
			linked_ll_aux{L}(bound,bound,\Nil);

	case linked_ll_aux_cons{L}:
		\forall struct cl *root, *bound, \list<struct cl*> tail;
			\separated(root,bound) ==>
			linked_ll_aux{L}(root->next, bound, tail) ==>
			separated_from_list(root,tail) ==>
			linked_ll_aux{L}(root, bound, \Cons(root, tail));

}

inductive linked_ll{L}(struct cl *root, struct cl *bound, \list<struct cl*> l) {

	case linked_ll_empty{L}:
		\forall struct cl *bound;
			linked_ll{L}(NULL,bound,\Nil);

	case linked_ll_cons{L}:
		\forall struct cl *root, *bound, \list<struct cl*> tail;
			linked_ll_aux{L}(root->next, bound, tail) ==>
			separated_from_list(root,tail) ==>
			linked_ll{L}(root, bound, \Cons(root, tail));
}
*/

/*@
inductive all_valid_aux{L}(struct cl* cur, struct cl* bound) {

	case all_valid_aux_bound{L}:
		\forall struct cl *bound;
			\valid(&bound->next) ==> all_valid_aux{L}(bound,bound);

	case all_valid_aux_rec{L}:
		\forall struct cl *root, *bound;
			\separated(root,bound) ==> \valid(&root->next) ==>
				all_valid_aux{L}(root->next,bound) ==>
				all_valid_aux{L}(root,bound);
}

predicate all_valid{L}(struct cl* cur, struct cl* bound) =
	\valid(cur) && \valid(&cur->next) && all_valid_aux{L}(cur->next,bound);
*/


/*@
axiomatic to_logic_list {

	logic \list<struct cl*>
	to_ll{L}(struct cl *root, struct cl *bound)
		reads { e->next | struct cl *e;
			\valid(e) && in_list(e, to_ll(root,bound)) };

	logic \list<struct cl*>
	to_ll_aux{L}(struct cl *root, struct cl *bound)
		reads { e->next | struct cl *e;
			\valid(e) && in_list(e, to_ll_aux(root,bound)) };


	axiom to_ll_nil{L}:
		\forall struct cl *bound;
			to_ll(NULL,bound) == \Nil;

	axiom to_ll_cons{L}:
		\forall struct cl *root, *bound;
		\let tail = to_ll_aux{L}(root->next,bound);
		\valid(root) ==> \valid(bound) ==>
		separated_from_list(root,tail) ==>
			to_ll{L}(root, bound) == \Cons(root,tail);



	axiom to_ll_aux_nil{L}:
		\forall struct cl *bound;
			to_ll_aux(bound,bound) == \Nil;

	axiom to_ll_aux_cons{L}:
		\forall struct cl *root, *bound;
		\let tail = to_ll_aux{L}(root->next,bound);
		(\separated(root,bound) && \valid(root) && \valid(bound) &&
		separated_from_list(root,tail)) ==>
			to_ll_aux{L}(root,bound) == \Cons(root,tail);
}
*/


/*@ lemma linked_ll_unchanged {L1,L2}:
		\forall struct cl *root, *bound , \list< struct cl*> l ;
		linked_ll{L1}(root,bound,l) ==>
		unchanged{L1,L2}(l) ==>
		linked_ll{L2}(root,bound,l);

	lemma to_ll_split {L}:
		\forall struct cl *root , *bound , *sep , \list<struct cl*> l;
		linked_ll(root,bound,l) ==> //implies to_ll(root,bound) == l
		in_list (sep ,l) ==>
		l == (to_ll (root , sep) ^ to_ll(sep,bound));

	lemma to_ll_merge {L}:
		\forall struct cl *root, *sep, *bound, \list<struct cl*> l1, l2;
		linked_ll(root,sep,l1) ==> //implies to_ll(root,sep) == l1
		to_ll (sep,bound) == l2 ==>
		\separated(root, bound) ==> all_separated_in_list(l1^l2) ==>
		to_ll(root,bound) == (l1 ^ l2);
*/

/*@
	lemma to_ll_aux_nil_lemma {L}:
		\forall struct cl *root; to_ll_aux(root,root) == \Nil;

	lemma last_element:
		\forall struct cl *root, *bound;
		root->next == bound ==> \nth(to_ll(bound,bound),\length(to_ll(bound,bound))) == root;
*/

/*---------------------------------------------------------------------------*/


/*@
requires \valid(cl);
requires \length(\to_ll(*cl,*cl)) <= INT_MAX ;
requires all_valid(*cl,*cl);
requires all_separated_in_list(to_ll(*cl,*cl));
requires Linked:		linked_ll(*cl, *cl, to_ll(*cl, *cl));
requires AllValid:		*cl == NULL || all_valid(*cl,*cl);

behavior is_cl_null:
  assumes *cl == NULL;
  assigns \nothing;
  ensures \result == NULL;

behavior not_cl_null:
  assumes *cl != NULL ;
  ensures \result == \nth(to_ll(*cl,*cl), \length(to_ll(*cl, *cl)) -1);

complete behaviors;
disjoint behaviors;
*/
void *
circular_list_tail(const circular_list_t cl)
{
  //@ requires \valid(this);
  struct cl *this;

  if(*cl == NULL) {
    return NULL;
  }

  //@ ghost int i = 0;
  // requires INT_MIN <= i <= INT_MAX;
  /*@ loop invariant all_valid(this,*cl);
  loop invariant linked_ll(*cl,*cl, to_ll(*cl,*cl));
  loop invariant \nth(to_ll(*cl,*cl),i) == this;
  loop invariant i+1 <= INT_MAX;
  loop assigns this, i;
  */
  for(this = *cl; this->next != *cl; this = this->next){
    //@ ghost i++;
  }

  return this;
}
