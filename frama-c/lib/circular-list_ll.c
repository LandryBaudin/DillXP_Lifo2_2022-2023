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


/*@ requires ValidPtr:		\valid_read(cl);
	requires AllValid:		*cl == NULL || all_valid(*cl,*cl);
	requires LengthMax:		\length(to_ll(*cl,*cl)) <= MAX_SIZE;
	requires all_separated_in_list(to_ll(*cl,*cl));
	requires Linked:		linked_ll(*cl, *cl, to_ll(*cl, *cl));


	assigns \nothing;

	ensures \result == \length(to_ll(*cl, *cl));

*/
unsigned long
circular_list_length(const circular_list_t cl)
{
  unsigned long len = 1;
  struct cl *this;

  if(circular_list_is_empty(cl)) {
//@ assert \length(to_ll(*cl,*cl)) == 0;
    return 0;
  }

//@ assert \length(to_ll(*cl,*cl)) > 0;
//@ assert \nth(to_ll(*cl,*cl),0) == *cl;

/*@ loop invariant all_valid(this,*cl);
	loop invariant linked_ll(*cl,*cl, to_ll(*cl,*cl));
	loop invariant linked_ll(this,*cl, to_ll(this,*cl));
	loop invariant len-1 == \length(to_ll(*cl,*cl)) - \length(to_ll(this,*cl));
	loop invariant \nth(to_ll(*cl,*cl),len-1) == this;
	loop assigns len, this;
	loop variant \length(to_ll(this, *cl));
*/
  for(this = *cl; this->next != *cl; this = this->next) {
  	len++;
  }
	
//@ assert \length(to_ll(*cl,*cl)) == len;
  return len;
}


/*---------------------------------------------------------------------------*/


/*@	requires \valid(cl) && \valid(element);
	requires *cl == NULL || all_valid(*cl,*cl);
	requires \length(to_ll(*cl,*cl)) <= MAX_SIZE-2;
	requires all_separated_in_list(to_ll(*cl,*cl));
	requires linked_ll(*cl, *cl, to_ll(*cl, *cl));
	requires in_list(element, to_ll(*cl, *cl)) || separated_from_list(element, to_ll(*cl,*cl));

	assigns *cl,
		{ l->next | struct cl *l; \at(l->next, Pre) == element &&
			in_list(l, to_ll{Pre}(\at(*cl, Pre), *cl)) };

	ensures linked_ll(*cl,*cl, to_ll(*cl,*cl));
	ensures separated_from_list(element, to_ll(*cl, *cl));

	behavior empty:
		assumes *cl == NULL;
		ensures *cl == NULL;

	behavior not_in_cl:
		assumes *cl != NULL && ! in_list(element, to_ll(*cl,*cl));
		ensures unchanged{Pre,Post}(to_ll(*cl,*cl));

	behavior in_cl_single:
		assumes *cl != NULL && in_list(element, to_ll(*cl,*cl)) && \length(to_ll(*cl,*cl)) == 1;
		ensures *cl == NULL;
		
	behavior in_cl:
		assumes *cl != NULL && in_list(element, to_ll(*cl,*cl)) && \length(to_ll(*cl,*cl)) > 1;
		ensures \forall integer i_element; \nth(to_ll(\old(*cl), \old(*cl)),i_element) == element ==> (
			(*cl == element ==> to_ll(*cl,*cl) == to_ll{Pre}(\old(*cl)->next,\old(*cl)) ) &&
			(*cl != element ==> to_ll(*cl,*cl) == ([| *cl |] ^ to_ll(element->next,*cl)) ) );

	complete behaviors;
	disjoint behaviors;

*/
void
circular_list_remove(circular_list_t cl, struct cl *element)
{
  struct cl *this, *previous;

  if(*cl == NULL) {
    return;
  }

  //@ assert \length(to_ll(*cl,*cl)) > 0;

   /*
   * We start traversing from the second element.
   * The head will be visited last. We always update the list's head after
   * removal, just in case we have just removed the head.
   */
  previous = *cl;
  this = previous->next;
  //@ ghost int i = 1;
  //@ ghost int n = circular_list_length(cl);
  
	//@ assert in_list(previous,to_ll(*cl,*cl)) && this == previous->next ==> in_list(this,to_ll(*cl,*cl));
/*@
	loop invariant \nth(to_ll(*cl, *cl), i) == this && this != NULL;

	loop invariant linked_ll(*cl,*cl,to_ll(*cl,*cl));
	loop invariant linked_ll(this,*cl,to_ll(this,*cl));
	loop invariant linked_ll(*cl,this,to_ll(*cl,this));
	
	loop invariant i>0 ==> i == \length(to_ll(*cl,this));
	loop invariant 0 <= i <= \length(to_ll(*cl,*cl));
	
	loop invariant unchanged{Pre, Here}(to_ll(*cl, *cl)) ;
	loop invariant \forall integer k ; 1 <= k < i ==> \nth(to_ll(*cl,*cl), k) != element;
	
	loop assigns i, this, previous, *cl,
		{ e->next | struct cl *e; \at(e->next, Pre) == element &&
			in_list(e, to_ll{Pre}(\at(*cl, Pre), \at(*cl, Pre))) };
*/
  do {
    if(this == element) {
      //@ assert in_list(this,to_ll(*cl,*cl));
      //@ assert in_list(element,to_ll(*cl,*cl));
      previous->next = this->next;
      //*cl = this->next == this ? NULL : previous;
      //@ ghost i = 0;
      if (this->next == this) {
      	//@ assert to_ll(this,this) == [|this|];
      	*cl = NULL;
      } else {
      	*cl = previous;
      }
  	  //@ assert ! in_list(element,to_ll(*cl,*cl));
      return;
    }
	//@ assert ! in_list(element,to_ll(*cl,this) ^ [|this|]);
    previous = this;
    this = this->next;
    //@ ghost i = (i+1)%n;
  } while(this != (*cl)->next);
  //@ assert unchanged{Pre,Here}(to_ll(*cl,*cl));
  //@ assert ! in_list(element,to_ll(*cl,*cl));
}


/*---------------------------------------------------------------------------*/


/*@
requires \valid_read(cl);
assigns \nothing;

ensures \result == true || \result == false;

behavior is_cl_null:
  assumes *cl == NULL;
  ensures \result == true;

  behavior not_cl_null:
    assumes *cl != NULL;
    ensures \result == false;

  disjoint behaviors;
  complete behaviors;
*/
bool circular_list_is_empty(const circular_list_t cl /*@ wp__nullable */){
  return *cl == NULL ? true : false;
}


/*---------------------------------------------------------------------------*/


/*@ requires ValidPtr:		\valid_read(cl);
	requires AllValid:		*cl == NULL || all_valid(*cl,*cl);
	requires LengthMax:		\length(to_ll(*cl,*cl)) <= MAX_SIZE;
	requires all_separated_in_list(to_ll(*cl,*cl));
	requires Linked:		linked_ll(*cl, *cl, to_ll(*cl, *cl));


	assigns \nothing;

	ensures \result == \length(to_ll(*cl, *cl));

*/
unsigned long
circular_list_length(const circular_list_t cl)
{
  unsigned long len = 1;
  struct cl *this;

  if(circular_list_is_empty(cl)) {
//@ assert \length(to_ll(*cl,*cl)) == 0;
    return 0;
  }

//@ assert \length(to_ll(*cl,*cl)) > 0;
//@ assert \nth(to_ll(*cl,*cl),0) == *cl;

/*@ loop invariant all_valid(this,*cl);
	loop invariant linked_ll(*cl,*cl, to_ll(*cl,*cl));
	loop invariant linked_ll(this,*cl, to_ll(this,*cl));
	loop invariant len-1 == \length(to_ll(*cl,*cl)) - \length(to_ll(this,*cl));
	loop invariant \nth(to_ll(*cl,*cl),len-1) == this;
	loop assigns len, this;
	loop variant \length(to_ll(this, *cl));
*/
  for(this = *cl; this->next != *cl; this = this->next) {
  	len++;
  }
	
//@ assert \length(to_ll(*cl,*cl)) == len;
  return len;
}


/*---------------------------------------------------------------------------*/


/*@
requires \valid(cl);
requires all_valid(*cl,*cl);

behavior is_cl_null:
  assumes *cl == NULL;
  assigns \nothing;
  ensures \result == NULL;

  behavior not_cl_null:
    assumes *cl != NULL ;
    ensures \result == \nth(to_ll(*cl,*cl), \length(to_ll(*cl, *cl)) -1);

  disjoint behaviors;
  complete behaviors;

*/
void *
circular_list_tail(const circular_list_t cl)
{
  //@ requires \valid(this);
  struct cl *this;

  if(*cl == NULL) {
    return NULL;
  }

  /*@ loop invariant all_valid(this,*cl);
  	loop assigns this;
  */
  for(this = *cl; this->next != *cl; this = this->next);

  return this;
}


/*---------------------------------------------------------------------------*/


/*@ requires \valid(cl);
	ensures *cl == NULL;
	assigns *cl;
*/
void
circular_list_init(circular_list_t cl)
{
  *cl = NULL;
}


/*---------------------------------------------------------------------------*/


/*@ requires \valid_read(cl);
	ensures \result == *cl;
	assigns \nothing;
*/
struct cl *
circular_list_head(const circular_list_t cl)
{
  return *cl;
}


