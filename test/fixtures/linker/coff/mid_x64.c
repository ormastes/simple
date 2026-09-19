/* Archive member: pulled in by chain_entry, itself pulls leaf_fn. */
extern int leaf_fn(int);
int mid_fn(int x) { return leaf_fn(x) + 1; }
