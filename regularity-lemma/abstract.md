This submission states Szemerédi's regularity lemma for finite simple graphs.

The formalization uses clean equitable vertex partitions: the parts are
nonempty, pairwise disjoint, cover all vertices, and any two part sizes differ
by at most one.  Edge densities are real-valued.  A pair of parts is
\(\varepsilon\)-regular when every sufficiently large pair of subsets has edge
density within \(\varepsilon\) of the density of the original pair.  A partition
is \(\varepsilon\)-regular when at most \(\varepsilon k^2\) unordered pairs of
distinct parts are irregular, where \(k\) is the number of parts.

The proof architecture follows the textbook energy-increment argument.  It
uses the weighted mean-square density of a partition, a bounded refinement
which raises that energy whenever an equitable partition is irregular, and an
equitable-cleanup lemma which restores equitability with arbitrarily small
energy loss.  This isolates the extra step needed to avoid an exceptional
class in the final statement.

The main statement is the standard lower-bound form: for every
\(\varepsilon>0\) and every \(m_0>0\), there is \(M\ge m_0\) such that every
finite graph on at least \(m_0\) vertices has an equitable
\(\varepsilon\)-regular partition into \(k\) parts with \(m_0\le k\le M\).

The classical statement and the energy-increment presentation follow
Reinhard Diestel's *Graph Theory*, 5th edition, Section 7.4.  Diestel uses an
exceptional class so that the remaining classes have exactly equal size; the
form stated here uses the equivalent clean equipartition convention in which
all vertices belong to nonempty parts whose sizes differ by at most one.
