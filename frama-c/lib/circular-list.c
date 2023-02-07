#include <stdbool.h>
#include <stdlib.h>
#include <limits.h>

#define MAX_SIZE INT_MAX-1

#define CIRCULAR_LIST(name) \
  static void *name##_circular_list = NULL; \
  static circular_list_t name = (circular_list_t)&name##_circular_list

typedef void **circular_list_t;

struct cl {
  struct cl *next;
};

/*----------------------------------------------------------------------------------------*/

/*@
	predicate unchanged{L1,L2}(struct cl **cArr, integer down, integer up) =
		\forall integer i; down <= i < up ==>
			\at(cArr[i],L1) == \at(cArr[i],L2) &&
			(\valid{L1}(\at(cArr[i],L1)) ==> \valid{L2}(\at(cArr[i],L2))) &&
			\at(*(cArr[i]),L1) == \at(*(cArr[i]), L2);
*/

/* @
	inductive linked_n{L}(struct cl* root, struct cl **cArr, integer index, integer n) {
		case linked_n_root{L}:
			\forall struct cl **cArr, *root, integer index;
				0 <= index <= MAX_SIZE ==> linked_n(root, cArr, index, 0);
		case linked_n_cons{L}:
			\forall struct cl **cArr, *root, integer index, n;
				0 <= n ==> 0 <= index ==> 0 <= index + n <= MAX_SIZE ==>
				\valid(root) ==> root == cArr[index] ==>
				linked_n(root->next, cArr, index+1, n-1) ==>
					linked_n(root, cArr, index, n);
	}

	lemma stay_linked{L1,L2}:
		\forall struct cl *root, **cArr, integer i, n ;
			linked_n{L1} (root, cArr, i, n) &&
				unchanged{L1,L2}(cArr, i, i+n) ==>
					linked_n{L2} (root, cArr, i, n);

	lemma linked_split_segment:
		\forall struct cl *root, **cArr, integer i, n, k;
			n > 0 ==> k >= 0 ==>
				linked_n(root,cArr,i,n+k) ==>
					(linked_n(root,cArr,i,n) && linked_n(root,cArr,i+n,k));
*/

/*@
	requires \valid(element) && \valid(array + (0 .. MAX_SIZE));
	requires 0 <= first && 0 <= n < MAX_SIZE && first + n < MAX_SIZE;

	assigns \nothing;

	behavior element_in:
		assumes \exists integer index; first <= index < first+n && array[index] == element;
		ensures array[\result] == element;

	behavior element_not_in:
		assumes \forall integer index; first <= index < first+n ==> array[index] != element;
		ensures \result == -1;

  disjoint behaviors;
  complete behaviors;
*/
int index_of(struct cl *element, struct cl **array, int first, int n) {
	/*@
		loop invariant \forall integer k; first <= k < i ==> array[k] != element;
		loop invariant first <= i <= first+n;
		loop assigns i;
		loop variant first+n - i;
	*/
	for (int i=first; i<first+n; i++)
		if (array[i] == element)
			return i;
	return -1;
}

/*----------------------------------------------------------------------------------------*/


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
bool is_empty(const circular_list_t cl /*@ wp__nullable */){
  return *cl == NULL ? true : false;
}


/*---------------------------------------------------------------------------*/

/*@ requires \valid(cl);
assigns *cl;
ensures *cl == NULL;
*/
void
circular_list_init(circular_list_t cl)
{
  *cl = NULL;
}

/*---------------------------------------------------------------------------*/

/*@ requires \valid(cl);
assigns \nothing;
ensures \result == *cl;
*/
void *
circular_list_head(const circular_list_t cl)
{
  return *cl;
}
