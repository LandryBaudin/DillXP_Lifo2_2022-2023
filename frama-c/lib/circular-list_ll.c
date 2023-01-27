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

// We exclude the last element which represents the end of a cycle
/*@
predicate separated_from_clist{L} (struct cl* element, \list<struct cl*> l) =
	\forall integer n; 0 <= n < \length(l) - 1 ==> 
	\separated(\nth(l,n), element);

predicate in_clist{L} (struct cl* element, \list<struct cl*> l) =
	\exists integer n; 
	0 <= n < \length(l) - 1 && \nth(l,n) == element;
*/

// root = current element, bound = first and last element of the original liste
/*@
inductive linked_ll{L}(struct cl *root, struct cl *bound, \list<struct cl*> l) {
	
	case linked_ll_bound{L}:
		\forall struct cl *root; linked_ll{L}(root,root,\Nil);
	
	case linked_ll_cons{L}:
		\forall struct cl *root, *bound, \list<struct cl*> tail;
			\separated(root,bound) ==> \valid(root) ==>
			linked_ll{L}(root->next, bound, tail) ==>
			separated_from_clist(root,tail) ==>
			linked_ll{L}(root,bound, \Cons(root, tail));
}


axiomatic to_logic_list {

	logic \list<struct cl*>
	to_ll{L}(struct cl *root, struct cl *bound)
		reads { e->next | struct cl *e; 
			\valid(e) && in_clist(e, to_ll(root,bound)) };
			
}
*/


/*@
requires \valid(cList) && \valid(element);
requires linked_ll(*cList, *cList, to_ll(*cList, *cList));
requires in_clist(element, to_ll(*cList, *cList)) ||
	separated_from_clist(element, to_ll(*cList,*cList));

assigns *cList,
	{ cl->next | struct cl *cl; \at(cl->next, Pre) == element &&
		in_clist(cl, to_ll{Pre}(\at(*cList, Pre), *cList)) };

ensures linked_ll(*cList, *cList, to_ll(*cList,*cList));
ensures separated_from_clist(element, to_ll(*cList, *cList));

behavior not_in_clist:
	assumes ! in_clist(element, to_ll(*cList,*cList));
	ensures to_ll(*cList,*cList) == to_ll{Pre}(\old(*cList),*cList);

behavior in_clist:
	assumes in_clist(element, to_ll(*cList,*cList));
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
  
   /*
   * We start traversing from the second element.
   * The head will be visited last. We always update the list's head after
   * removal, just in case we have just removed the head.
   */
  previous = *cList;
  this = previous->next;
  
  
  do {
    if(this == element) {
      previous->next = this->next;
      *cList = this->next == this ? NULL : previous;
      return;
    }
    
    previous = this;
    this = this->next;
    
  } while(this != ((struct cl *)*cList)->next);
}
