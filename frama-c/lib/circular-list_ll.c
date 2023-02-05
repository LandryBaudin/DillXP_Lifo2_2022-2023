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
			\separated(root,bound) ==> \valid(root) ==> \valid(bound) ==>
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
			\valid(root) ==> \valid(bound) ==>
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


/* @
requires \valid(cList) && \valid(element);
requires \valid(&(*cList)->next);
requires linked_ll(*cList, *cList, to_ll(*cList, *cList));
requires in_list(element, to_ll(*cList, *cList)) ||
	separated_from_list(element, to_ll(*cList,*cList));

assigns *cList,
	{ cl->next | struct cl *cl; \at(cl->next, Pre) == element &&
		in_list(cl, to_ll{Pre}(\at(*cList, Pre), *cList)) };

ensures linked_ll(*cList, *cList, to_ll(*cList,*cList));
ensures separated_from_list(element, to_ll(*cList, *cList));

behavior not_in_clist:
	assumes ! in_list(element, to_ll(*cList,*cList));
	ensures to_ll(*cList,*cList) == to_ll{Pre}(\old(*cList),*cList);

behavior in_clist:
	assumes in_list(element, to_ll(*cList,*cList));
	ensures to_ll (*cList , *cList ) ==
		(to_ll{Pre}(\old(*cList), element) ^ to_ll{Pre}(element->next, *cList));

complete behaviors;
disjoint behaviors;

*/
void
circular_list_remove(circular_list_t cList, struct cl *element)
{
  struct cl *this, *previous;

  if(*cList == NULL) {
    return;
  }
  
  //@ assert \length(to_ll(*cList,*cList)) > 0;
  
   /*
   * We start traversing from the second element.
   * The head will be visited last. We always update the list's head after
   * removal, just in case we have just removed the head.
   */
  previous = *cList;
  this = previous->next;
  //@ ghost int i = 1;
  
/* @ loop invariant this == \nth(to_ll(*cList,*cList),i%\length(to_ll(*cList,*cList)));
	loop assigns i, this, previous;
	loop variant \length(to_ll(*cList,*cList)) - i;
*/
  do {
    if(this == element) {
      previous->next = this->next;
      *cList = this->next == this ? NULL : previous;
      return;
    }
    
    previous = this;
    this = this->next;
    //@ ghost i++;
  } while(this != (*cList)->next);
}


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


/*@ requires \valid_read(cl);
	requires *cl == NULL || all_valid(*cl,*cl);
	requires to_ll_aux(*cl,*cl) == \Nil ==> \length(to_ll(*cl,*cl)) <= MAX_SIZE;
	requires to_ll_aux(*cl,*cl) == \Nil ==> all_separated_in_list(to_ll(*cl,*cl));
	
	requires to_ll_aux(*cl,*cl) == \Nil ==> linked_ll(*cl, *cl, to_ll(*cl, *cl));
		
	
	assigns \nothing;
	
	ensures \result >= 0;
	
	behavior empty:
		assumes *cl == NULL;
		ensures \result == 0;
		
	behavior not_empty:
		assumes *cl != NULL;
		ensures \result > 0;
		ensures \result == \length(to_ll(*cl, *cl));
	
  disjoint behaviors;
  complete behaviors;
*/
unsigned long
circular_list_length(const circular_list_t cl)
{
  unsigned long len = 1;
  struct cl *this;

  if(circular_list_is_empty(cl)) {
    return 0;
  }
  

/*@ loop invariant all_valid(this,*cl);
	loop invariant len == \length(to_ll(*cl,this->next));
	loop assigns len, this;
*/
  for(this = *cl; this->next != *cl; this = this->next) {
    len++;
  }
  
  return len;
}


