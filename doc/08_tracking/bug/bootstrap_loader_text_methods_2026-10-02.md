# Loader native text method gaps

Producer 7cc8409e/source4e33 reaches normal MIR failure for the loader closure.
The retained U0002 evidence has four unresolved `index_of` calls and three
undefined `text` receivers paired with three unresolved `from_char_code` calls.
These are separate from the five Dict.contains and nominal receiver cascades.

The one-argument `index_of` spelling was omitted from the proven-text method
family even though its two-argument form and the `find` alias already existed.
The candidate adds that spelling to the same arity, provenance and runtime
dispatch logic. It preserves custom owner resolution and the offset overload.

HIR creates the builtin `text` name as a synthetic Function declaration with
no defining owner or callable type. MIR previously tried to load this name as
a value receiver. A narrow pre-dispatch helper now recognizes that declaration
identity and emits the existing `rt_char_from_code` ABI without a receiver
load. User declarations named text retain ordinary resolution. LLVM already
declares and adapts this runtime entry. Invalid scalars retain its empty-text
behavior; wrong arity produces a fatal diagnostic.

Native fixtures cover found/missing/empty text search, offsets, local/custom
owners, UTF-8, control bytes, invalid scalars and arity. Source review found no
P0/P1 in the two changes; native execution is UNRUN. No blanket U0002 closure
or release PASS is claimed. No prior passing receiver criterion was rerun.
