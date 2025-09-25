import java.util.Arrays;
import java.util.HashSet;

public class BAAPTwoColor_2stage {

    // === Public API ===

    /** Compute B(k,l).
     *  Stage 1: find B(k) = minimal N such that every 2-coloring has a k-AAP in some color.
     *  Stage 2: search down from B(k) to get minimal N such that every 2-coloring has red k-AAP OR blue l-AAP.
     *  If l > k and B(k,l) > B(k), we expand the upper bound upward until the predicate holds or we hit Nmax.
     *  Returns -1 if unresolved within Nmax. */
    public static int computeB(int k, int l, int Nmax) {
        int Bk = minimalNFor(k, k, Nmax);            // B(k) = B(k,k)
        if (Bk == -1) return -1;

        // If property holds at Bk for (k,l), binary search in [1, Bk]; else expand upward first.
        if (!existsCounterexampleAvoidBoth(Bk, k, l)) {
            return binarySearchMinN(1, Bk, k, l);
        } else {
            // l may be > k: expand upward (doubling) until predicate holds or Nmax reached
            int lo = Bk + 1, hi = Math.min(Math.max(2*Bk, 1), Nmax);
            boolean foundUpper = false;
            while (lo <= Nmax) {
                if (!existsCounterexampleAvoidBoth(hi, k, l)) { foundUpper = true; break; }
                if (hi == Nmax) break;
                lo = hi + 1;
                hi = Math.min(hi * 2, Nmax);
            }
            if (!foundUpper) return -1;
            return binarySearchMinN(lo, hi, k, l);
        }
    }

    // === Stage helper: find minimal N for (k1,k2) ===

    /** Find minimal N such that EVERY coloring has (red k1-AAP OR blue k2-AAP). */
    private static int minimalNFor(int k1, int k2, int Nmax) {
        // Exponential search to get an upper bound where predicate holds:
        int lo = 1;
        int hi = 1;
        while (hi <= Nmax && existsCounterexampleAvoidBoth(hi, k1, k2)) {
            // counterexample exists => predicate false -> need larger N
            if (hi == Nmax) break;
            hi = Math.min(hi * 2, Nmax);
        }
        if (hi > Nmax || existsCounterexampleAvoidBoth(hi, k1, k2)) {
            // Never found an N <= Nmax where predicate holds
            return -1;
        }
        // Binary search on [lo, hi] for minimal N with predicate true
        return binarySearchMinN(lo, hi, k1, k2);
    }

    /** Monotone binary search: P(N) = !existsCounterexampleAvoidBoth(N, k1, k2). */
    private static int binarySearchMinN(int lo, int hi, int k1, int k2) {
        int ans = hi;
        while (lo <= hi) {
            int mid = (lo + hi) >>> 1;
            if (!existsCounterexampleAvoidBoth(mid, k1, k2)) {
                ans = mid;
                hi = mid - 1;
            } else {
                lo = mid + 1;
            }
        }
        return ans;
    }

    // === Counterexample oracle ===
    // Is there a 2-coloring of {0..N-1} that avoids: (red k1-AAP) AND (blue k2-AAP)?
    private static boolean existsCounterexampleAvoidBoth(int N, int k1, int k2) {
        if (N <= 0) return true; // vacuously avoid both on empty set
        int[] col = new int[N];
        Arrays.fill(col, -1);

        // Symmetry: fix position 0 to RED (0) to halve the tree
        col[0] = 0;
        return dfsAvoidBoth(1, N, k1, k2, col, new PrefixMemo());
    }

    private static boolean dfsAvoidBoth(int idx, int N, int k1, int k2, int[] col, PrefixMemo memo) {
        if (idx == N) return true; // built a full coloring that avoids both

        long key = memo.key(col, idx);
        if (memo.hit(key)) return false;   // already explored this prefix

        // Branching heuristic: try color with fewer points so far
        int red = 0, blue = 0;
        for (int i = 0; i < idx; i++) {
            if (col[i] == 0) red++; else if (col[i] == 1) blue++;
        }
        int first = (blue < red) ? 1 : 0;

        for (int t = 0; t < 2; t++) {
            int c = (t == 0) ? first : (1 - first);
            col[idx] = c;
            boolean violates = (c == 0) ? createsKAAP(idx, k1, 0, col)
                                        : createsKAAP(idx, k2, 1, col);
            if (!violates) {
                if (dfsAvoidBoth(idx + 1, N, k1, k2, col, memo)) return true;
            }
            col[idx] = -1;
        }
        memo.add(key);
        return false;
    }

    // === KAAP detectors ===
    private static boolean createsKAAP(int idx, int k, int color, int[] col) {
        if (k <= 2) return false;
        if (k == 3) return createsKAAP3(idx, color, col);
        return createsKAAPGeneral(idx, k, color, col);
    }

    // Fast path for k=3: need j < m < idx, same color, with (m-j) != (idx-m)
    private static boolean createsKAAP3(int idx, int color, int[] col) {
        for (int m = 1; m < idx; m++) {
            if (col[m] != color) continue;
            int jAP = 2*m - idx;   // the unique j that would make equal gaps; may be <0 or >=m
            boolean seenOther = false;
            for (int j = 0; j < m; j++) {
                if (col[j] != color) continue;
                if (j != jAP) { seenOther = true; break; }
            }
            if (seenOther) return true;
        }
        return false;
    }

    // General k-AAP (k>=3): check chains that END at idx with gaps from {a,b}, 1<=a<b, both used.
    private static boolean createsKAAPGeneral(int idx, int k, int color, int[] col) {
        int need = k - 1;                // number of backward steps
        int maxA = idx / need;
        for (int a = 1; a <= maxA; a++) {
            int bMax = idx - (need - 1)*a;
            if (bMax <= a) continue;
            for (int b = a + 1; b <= bMax; b++) {
                if (walkAAP(idx, color, col, need, a, b, false, false)) return true;
            }
        }
        return false;
    }

    private static boolean walkAAP(int pos, int color, int[] col,
                                   int need, int a, int b, boolean usedA, boolean usedB) {
        if (need == 0) return usedA && usedB;
        int p = pos - a;
        if (p >= 0 && col[p] == color) {
            if (walkAAP(p, color, col, need - 1, a, b, true, usedB)) return true;
        }
        p = pos - b;
        if (p >= 0 && col[p] == color) {
            if (walkAAP(p, color, col, need - 1, a, b, usedA, true)) return true;
        }
        return false;
    }

    // === Prefix memoization with 64-bit rolling hash (no Strings, no parsing) ===
    private static final class PrefixMemo {
        private final HashSet<Long> seen = new HashSet<>();
        long key(int[] col, int idx) {
            long h = 0xcbf29ce484222325L;    // FNV offset basis
            final long P = 0x100000001b3L;   // FNV prime
            for (int i = 0; i < idx; i++) {
                // col[i] is 0 or 1 for i<idx (assigned). Map to 1 or 2 to avoid zero-only stream.
                int sym = (col[i] + 1) & 3;  // 0->1, 1->2
                long tok = ((long)sym) ^ (((long)i) << 2);
                h ^= tok;
                h *= P;
            }
            h ^= (long) idx;
            h *= P;
            return h;
        }
        boolean hit(long k) { return !seen.add(k); }
        void add(long k) { seen.add(k); }
    }

    // === Demo ===
    public static void main(String[] args) {
        int k = 5, l = 20, Nmax = 300;

        long t0 = System.nanoTime();
        int B = computeB(k, l, Nmax);
        long t1 = System.nanoTime();
        
        if (B == -1) {
            System.out.println("Unresolved up to Nmax=" + Nmax);
        } else {
            System.out.println("B(" + k + "," + l + ") = " + B);
        }

        System.out.printf("Elapsed: %.3f ms%n", (t1 - t0) / 1e6);
    }
}
