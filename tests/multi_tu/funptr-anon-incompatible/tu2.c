/* funptr-anon-incompatible, TU 2. */
typedef struct { int counter; } count_t;
void call(void (*f)(count_t *), count_t *c);
static void cb(count_t *c) { c->counter = 1; }
int main(void) { count_t c = { 0 }; call(cb, &c); return c.counter; }
