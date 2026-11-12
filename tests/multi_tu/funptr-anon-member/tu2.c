/* funptr-anon-member, TU 2: defines the callback. Expected: 7. */
typedef struct { long counter; } atomic_long_t;
struct work { atomic_long_t data; void (*func)(struct work *); };
void run(struct work *w);
static void cb(struct work *w) { w->data.counter += 7; }
int main(void) {
  struct work w = { { 0 }, cb };
  run(&w);
  return (int)w.data.counter;
}
