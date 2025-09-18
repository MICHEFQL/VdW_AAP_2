import java.util.Arrays;

public class BAAPTwoColor {

    // Entry: search B(k, l) up to a cap Nmax. Returns -1 if not found by Nmax.
    public static int computeB(int k, int l, int Nmax) {
        for (int N = 1; N <= Nmax; N++) {
            if (!existsCounterexample(N, k, l)) {
                // No 2-coloring avoids both patterns -> this N is minimal: B(k, l) = N
                return N;
            }
        }
        return -1; // not resolved within Nmax
    }

    // Does there exist a 2-coloring of {0..N-1} avoiding: color0 has k-AAP AND color1 has l-AAP?
    // Return true if such a coloring exists (i.e., still below the threshold).
    private static boolean existsCounterexample(int N, int k, int l) {
        int[] coloring = new int[N];
        Arrays.fill(coloring, -1);
        return dfs(0, N, k, l, coloring);
    }

    // Backtrack: assign index idx -> color 0 or 1; prune if that color completes its forbidden AAP.
    private static boolean dfs(int idx, int N, int k, int l, int[] coloring) {
        if (idx == N) return true; // built a full coloring avoiding both patterns

        // Try color 0 then 1
        for (int c = 0; c <= 1; c++) {
            coloring[idx] = c;
            boolean violates =
                    (c == 0 ? createsKAAP(idx, k, 0, coloring)
                            : createsKAAP(idx, l, 1, coloring));
            if (!violates) {
                if (dfs(idx + 1, N, k, l, coloring)) return true;
            }
            coloring[idx] = -1;
        }
        return false;
    }

    // --------- KAAP detectors ---------
    // Public dispatcher: use a k=3 fast path; otherwise general.
    private static boolean createsKAAP(int idx, int k, int color, int[] coloring) {
        if (k <= 2) return false;     // need at least 3 points to have two distinct gaps
        if (k == 3) return createsKAAP3(idx, color, coloring);
        return createsKAAPGeneral(idx, k, color, coloring);
    }

    // Fast detector for 3-AAP:
    // We need j < m < idx, all same color, with (m - j) != (idx - m).
    // Equivalent: for some middle m (same color), there exists an earlier j (same color)
    // different from jAP = 2*m - idx (the unique j that would make an exact AP).
    private static boolean createsKAAP3(int idx, int color, int[] coloring) {
        // Scan all potential middles m
        for (int m = 1; m < idx; m++) {
            if (coloring[m] != color) continue;

            int jAP = 2 * m - idx; // the only j that would make equal gaps
            boolean seenOther = false;
            // Is there at least one j < m of this color that's not jAP?
            for (int j = 0; j < m; j++) {
                if (coloring[j] != color) continue;
                if (j != jAP) { seenOther = true; break; }
            }
            if (seenOther) return true;
        }
        return false;
    }

    // General k-AAP detector (k >= 3):
    // A k-AAP is a chain of k points with consecutive gaps drawn from {a, b} with 1 <= a < b,
    // and both a and b used at least once. We only check chains that END at idx (because we increment N)
    private static boolean createsKAAPGeneral(int idx, int k, int color, int[] coloring) {
        int need = k - 1;                 // number of backward gaps to build
        int maxA = idx / need;            // if all gaps were 'a', need*a <= idx

        for (int a = 1; a <= maxA; a++) {
            // Need at least one 'b' > a: minimal total with one b is (need-1)*a + b <= idx
            int bMax = idx - (need - 1) * a;
            if (bMax <= a) continue;     // no b>a fits
            for (int b = a + 1; b <= bMax; b++) {
                if (walkAAP(idx, color, coloring, need, a, b, false, false)) {
                    return true;
                }
            }
        }
        return false;
    }

    // Recursive walk: from 'pos', take 'need' steps of length a or b (both must be used),
    // staying on the same color. Returns true if such a chain exists.
    private static boolean walkAAP(int pos, int color, int[] coloring,
                                   int need, int a, int b, boolean usedA, boolean usedB) {
        if (need == 0) return usedA && usedB;

        // step 'a'
        int p = pos - a;
        if (p >= 0 && coloring[p] == color) {
            if (walkAAP(p, color, coloring, need - 1, a, b, true, usedB)) return true;
        }
        // step 'b'
        p = pos - b;
        if (p >= 0 && coloring[p] == color) {
            if (walkAAP(p, color, coloring, need - 1, a, b, usedA, true)) return true;
        }
        return false;
    }

    // --------- demo ---------
    public static void main(String[] args) {
        int k = 3;       // AAP length to force in color 0
        int l = 3;       // AAP length to force in color 1
        int Nmax = 200;  // search cap 
        // if (args.length >= 1) k = Integer.parseInt(args[0]);
        // if (args.length >= 2) l = Integer.parseInt(args[1]);
        // if (args.length >= 3) Nmax = Integer.parseInt(args[2]);

        long t0 = System.nanoTime();
        int B = computeB(k, l, Nmax);
        long t1 = System.nanoTime();

        if (B == -1) {
            System.out.println("No resolution up to Nmax=" + Nmax + ". Try increasing Nmax.");
        } else {
            System.out.println("B(" + k + "," + l + ") = " + B);
        }
        System.out.printf("Elapsed: %.3f ms%n", (t1 - t0) / 1e6);
    }
}
