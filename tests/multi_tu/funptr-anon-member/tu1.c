/* funptr-anon-member, TU 1: Linux struct work_struct begins with
   atomic_long_t data, a typedef of an anonymous struct. Comparing the two
   units' struct work member by member reaches the anonymous struct, which has
   no tag in either unit; with corresponding members the types are compatible
   (ISO 6.2.7#1) and the call is defined. */
typedef struct { long counter; } atomic_long_t;
struct work { atomic_long_t data; void (*func)(struct work *); };
void run(struct work *w) { w->func(w); }
