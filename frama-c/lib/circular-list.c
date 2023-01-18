#include <stdbool.h>
#include <stdlib.h>

#define CIRCULAR_LIST(name) \
  static void *name##_circular_list = NULL; \
  static circular_list_t name = (circular_list_t)&name##_circular_list

typedef void **circular_list_t;

struct cl {
  struct cl *next;
};

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