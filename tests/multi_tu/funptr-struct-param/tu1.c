/* funptr-struct-param, TU 1: a service that invokes a callback stored in a
   struct, the shape of Linux timer, work and RCU callbacks. The callback is
   defined in the OTHER TU, so its parameter type `struct timer *` names that
   TU's tag. The two definitions of struct timer correspond member by member,
   so the types are compatible (ISO 6.2.7#1) and the call is defined. */
struct timer { int expired; void (*function)(struct timer *); };
void fire(struct timer *t) { t->function(t); }
