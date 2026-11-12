/* funptr-struct-param, TU 2: registers its own static callback and lets
   TU 1 call it twice. Expected: 2. */
struct timer { int expired; void (*function)(struct timer *); };
void fire(struct timer *t);
static void expired(struct timer *t) { ++t->expired; }
int main(void) {
  struct timer t = { 0, expired };
  fire(&t);
  fire(&t);
  return t.expired;
}
