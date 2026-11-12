/* funptr-anon-typedef, TU 1: the callback's parameter is a pointer to a
   typedef of an anonymous struct, as siphash_key_t is. Both units declare it
   without a tag and with corresponding members, so the types are compatible
   (ISO 6.2.7#1). */
typedef struct { unsigned long key[2]; } key_t;
void call(void (*f)(key_t *), key_t *k) { f(k); }
