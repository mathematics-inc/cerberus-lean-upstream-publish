struct entry { short tag; long weight; };
int b_weight(void) { struct entry e = { 7, 2 }; return (int)e.weight; }
