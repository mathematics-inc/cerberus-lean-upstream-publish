/* Expected: 42. */
#include "node.h"
static int total;
static void add(struct node *n) { total += n->v; }
int main(void) {
  struct node b = { 0, 2, add }, a = { &b, 40, add };
  run_all(&a);
  return total;
}
