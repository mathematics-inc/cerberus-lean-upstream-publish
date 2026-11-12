/* funptr-struct-param-incompatible, TU 1: the same tag as TU 2 but with
   different members, so the two struct types are NOT compatible
   (ISO 6.2.7#1). Calling TU 2's callback through a pointer whose type names
   this TU's struct s is undefined (ISO 6.5.2.2#9): UB041 is expected. */
struct s { long k; int extra; };
void call(void (*f)(struct s *), struct s *p) { f(p); }
