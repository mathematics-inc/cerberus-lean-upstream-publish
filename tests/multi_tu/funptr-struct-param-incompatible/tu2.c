struct s { int k; };
void call(void (*f)(struct s *), struct s *p);
static void cb(struct s *p) { p->k = 1; }
int main(void) { struct s v = { 0 }; call(cb, &v); return v.k; }
