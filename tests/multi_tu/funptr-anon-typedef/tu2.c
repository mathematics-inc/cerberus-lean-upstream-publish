/* funptr-anon-typedef, TU 2. Expected: 5. */
typedef struct { unsigned long key[2]; } key_t;
void call(void (*f)(key_t *), key_t *k);
static void cb(key_t *k) { k->key[1] = 5; }
int main(void) {
  key_t k = { { 0, 0 } };
  call(cb, &k);
  return (int)k.key[1];
}
