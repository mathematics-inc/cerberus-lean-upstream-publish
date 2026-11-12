/* funptr-struct-recursive, TU 1: walks the list and calls each node's
   callback, defined in TU 2. Compatibility of the recursive struct must
   terminate (assumed-pair rule of ISO 6.2.7#1). */
#include "node.h"
void run_all(struct node *head) { for (; head; head = head->next) head->func(head); }
