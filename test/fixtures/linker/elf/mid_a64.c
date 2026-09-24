/* Archive member mid: defines add_val + msg, needs leaf_fn (pulled on 2nd closure pass). */
const char msg[] = "hi\n";
extern long leaf_fn(long x);
long add_val(long x) { return leaf_fn(x); }
