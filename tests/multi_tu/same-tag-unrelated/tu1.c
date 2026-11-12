/* same-tag-unrelated, TU 1: each TU has its own, different struct entry.
   They are never mixed, so the program is defined: different same-named
   tag definitions must link and run. Expected: 42. */
struct entry { int key; };
int b_weight(void);
int main(void) { struct entry e = { 40 }; return e.key + b_weight(); }
