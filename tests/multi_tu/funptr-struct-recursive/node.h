/* A self-referential node with a callback, the shape of list and RCU heads. */
struct node { struct node *next; int v; void (*func)(struct node *); };
void run_all(struct node *head);
