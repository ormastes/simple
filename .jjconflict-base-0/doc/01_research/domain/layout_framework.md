# Layout Framework Domain Research

## Primary Sources

- [CSS Display Module Level 3](https://www.w3.org/TR/css-display-3/) defines independent formatting contexts as separate layout environments and identifies flex, grid, out-of-flow, containment, and scroll cases that create or preserve those boundaries.
- [CSS Containment Module Level 3](https://www.w3.org/TR/css-contain-3/) defines containment as subtree independence and documents indirect intrinsic-size dependencies that prevent treating every contained subtree as dependency-free.
- [CSS Positioned Layout Module Level 3](https://www.w3.org/TR/css-position-3/) defines containing-block dependencies for static, relative, sticky, absolute, and fixed boxes.
- Tarjan's [Depth-First Search and Linear Graph Algorithms](https://epubs.siam.org/doi/abs/10.1137/0201010) establishes linear-time strongly connected component discovery, suitable for condensing cyclic layout constraints before wave scheduling.

## Consequences

1. Island discovery may use independent formatting-context and containment boundaries, but must retain sizing and containing-block edges crossing those boundaries.
2. Inline formatting stays CPU-bound because shaping and line breaking are ordered services, not homogeneous geometry kernels.
3. SCC condensation gives a deterministic acyclic wave graph; members of a cyclic component require a bounded fixed point and explicit non-convergence.
4. GPU choice must compare end-to-end predicted latency, including transfer and synchronization, rather than kernel work alone.

