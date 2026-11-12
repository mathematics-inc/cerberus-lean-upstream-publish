/* funptr-anon-incompatible, TU 1: a control. The two units' anonymous
   structs have members of different types (long here, int in TU 2), so the
   function types are not compatible and the call is undefined (ISO 6.5.2.2#9):
   expected UB041. */
typedef struct { long counter; } count_t;
void call(void (*f)(count_t *), count_t *c) { f(c); }
