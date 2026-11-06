// Ternary (0/1/X) forward reachability with lasso closure on a closed AIGER model.
//
// Usage: tsim model.aig reset_input_index frames max_period out_prefix
//
// Abstract domain: one ternary cube per frame.  Every primary input is X, except
// the reset input: it is 0 in frame 0 (the model's initial-state constraint) and
// 1 on the main trajectory afterwards.  Re-reset is covered separately below.
// Latch initial values come from the AIGER file; a latch whose reset literal is
// its own literal is uninitialized and starts as X.  Kleene AND/NOT evaluation
// is monotone, so gamma(post#(c)) contains post(gamma(c)) for every cube c.
//
// Invariant construction:
//   S_0 = initial cube, S_{t+1} = post#(S_t, rst_t)            t < T
//   W_0 = S_T join S_{T-p} (widened until closed), W_{i+1} = post#(W_i, 1)
//   accept iff S_T <= W_0 and W_p <= W_0.
// Re-reset: reset is unconstrained after frame 0 in the model, so for every cube c
// in {S_1..S_{T-1}, W_0..W_{p-1}} we require post#(c, rst=0) <= S_1.
// Then Inv = {S_0..S_{T-1}} U {W_0..W_{p-1}} contains every reachable state under
// every reset schedule.  For each (cube, admitted reset value) pair we require
// bad == 0 or the constraint == 0 (constraint == X with bad != 0 is a failure),
// and we join every output value.  An output joined to a single binary value is
// constant on all reachable frames.
//
// Files written: <out>.frames.tsv (main trajectory), <out>.outjoin.bin (O bytes:
// 0, 1, 2 = varies/unknown, 3 = never evaluated), <out>.outs.bin ((T+1) x O bytes,
// main-trajectory output values), <out>.result.txt (key value lines).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint8_t tv;  // 0, 1, 2 = X
static const tv TAND[9] = {0, 0, 0, 0, 1, 2, 0, 2, 2};
static uint32_t M, I, L, O, A, B, C;
static uint32_t *lnext, *linit, *outs, *bads, *cons, *r0, *r1;
static tv *val;
static int rst_index;

static inline tv lv(uint32_t lit) {
  tv v = val[lit >> 1];
  return v == 2 ? 2 : (tv)(v ^ (lit & 1));
}

static uint32_t decode(FILE *f) {
  uint32_t x = 0, i = 0;
  int ch;
  while ((ch = getc(f)) != EOF && (ch & 0x80)) x |= (uint32_t)(ch & 0x7f) << (7 * i++);
  if (ch == EOF) { fprintf(stderr, "truncated AND section\n"); exit(2); }
  return x | ((uint32_t)ch << (7 * i));
}

static void eval(const tv *state, int rst) {
  val[0] = 0;
  for (uint32_t i = 1; i <= I; i++) val[i] = 2;
  val[1 + rst_index] = (tv)rst;
  for (uint32_t i = 0; i < L; i++) val[I + 1 + i] = state[i];
  for (uint32_t i = 0; i < A; i++) val[I + L + 1 + i] = TAND[lv(r0[i]) * 3 + lv(r1[i])];
}

static void post(tv *dst) {
  for (uint32_t i = 0; i < L; i++) dst[i] = lv(lnext[i]);
}

static int leq(const tv *a, const tv *b) {  // a <= b in the information order
  for (uint32_t i = 0; i < L; i++)
    if (b[i] != 2 && a[i] != b[i]) return 0;
  return 1;
}

static uint32_t join_into(tv *dst, const tv *src) {  // dst := dst join src
  uint32_t changed = 0;
  for (uint32_t i = 0; i < L; i++)
    if (dst[i] != 2 && dst[i] != src[i]) { dst[i] = 2; changed++; }
  return changed;
}

static uint32_t xcount(const tv *s) {
  uint32_t n = 0;
  for (uint32_t i = 0; i < L; i++) n += s[i] == 2;
  return n;
}

static tv *outjoin;
static uint64_t checks = 0, failures = 0;

// Check properties and join outputs for the current evaluation.
static void observe(const char *where, long index, int rst) {
  tv constraint = 1;
  for (uint32_t i = 0; i < C; i++) {
    tv v = lv(cons[i]);
    constraint = TAND[constraint * 3 + v];
  }
  checks++;
  if (constraint == 0) return;  // no admitted behavior at this (cube, reset) pair
  for (uint32_t i = 0; i < B; i++) {
    if (lv(bads[i]) != 0) {
      failures++;
      if (failures <= 20)
        fprintf(stderr, "property %u not known safe at %s %ld rst=%d (constraint %c)\n", i, where, index,
                rst, "01X"[constraint]);
    }
  }
  for (uint32_t i = 0; i < O; i++) {
    tv v = lv(outs[i]);
    tv *d = &outjoin[i];
    if (*d == 3) *d = v;
    else if (*d != v) *d = 2;
  }
}

int main(int argc, char **argv) {
  if (argc != 6) {
    fprintf(stderr, "usage: tsim model.aig reset_input_index frames max_period out_prefix\n");
    return 2;
  }
  FILE *f = fopen(argv[1], "rb");
  if (!f) { perror(argv[1]); return 2; }
  rst_index = atoi(argv[2]);
  int T = atoi(argv[3]);
  int P = atoi(argv[4]);
  const char *prefix = argv[5];
  char hdr[256];
  if (!fgets(hdr, sizeof hdr, f)) return 2;
  uint32_t J = 0, F = 0;
  int n = sscanf(hdr, "aig %u %u %u %u %u %u %u %u %u", &M, &I, &L, &O, &A, &B, &C, &J, &F);
  if (n < 5 || J || F || M != I + L + A || rst_index < 0 || (uint32_t)rst_index >= I || T < 2 || P < 1 ||
      P >= T) {
    fprintf(stderr, "unsupported header or arguments: %s", hdr);
    return 2;
  }
  if (n < 7) B = C = 0;
  lnext = malloc(4 * (size_t)L); linit = malloc(4 * (size_t)L);
  for (uint32_t i = 0; i < L; i++) {
    char line[128];
    if (!fgets(line, sizeof line, f)) return 2;
    unsigned a, b;
    int k = sscanf(line, "%u %u", &a, &b);
    if (k < 1) return 2;
    uint32_t self = 2 * (I + 1 + i);
    lnext[i] = a;
    linit[i] = (k == 2) ? (b == self ? 2u : b) : 0u;
    if (linit[i] > 2) { fprintf(stderr, "unsupported latch init %u\n", b); return 2; }
  }
  outs = malloc(4 * (size_t)(O + 1)); bads = malloc(4 * (size_t)(B + 1)); cons = malloc(4 * (size_t)(C + 1));
  for (uint32_t i = 0; i < O; i++) if (fscanf(f, "%u\n", &outs[i]) != 1) return 2;
  for (uint32_t i = 0; i < B; i++) if (fscanf(f, "%u\n", &bads[i]) != 1) return 2;
  for (uint32_t i = 0; i < C; i++) if (fscanf(f, "%u\n", &cons[i]) != 1) return 2;
  r0 = malloc(4 * (size_t)A); r1 = malloc(4 * (size_t)A);
  for (uint32_t i = 0; i < A; i++) {
    uint32_t lhs = 2 * (I + L + 1 + i);
    uint32_t d0 = decode(f), d1 = decode(f);
    r0[i] = lhs - d0; r1[i] = r0[i] - d1;
    if (d0 == 0 || r0[i] < r1[i] || r0[i] >= lhs) { fprintf(stderr, "bad AND %u\n", i); return 2; }
  }
  fclose(f);
  val = malloc(M + 1);
  outjoin = malloc(O + 1);
  memset(outjoin, 3, O + 1);
  tv *hist = malloc((size_t)(T + 1) * L);
  tv *scratch = malloc(L), *reset_next = malloc(L);
  if (!hist || !scratch || !reset_next || !val || !outjoin) { fprintf(stderr, "out of memory\n"); return 2; }
  for (uint32_t i = 0; i < L; i++) hist[i] = (tv)linit[i];

  char path[1024];
  snprintf(path, sizeof path, "%s.frames.tsv", prefix);
  FILE *tr = fopen(path, "w");
  snprintf(path, sizeof path, "%s.outs.bin", prefix);
  FILE *of = fopen(path, "wb");
  tv *outv = malloc(O + 1);
  fprintf(tr, "frame\treset_input\tx_latches\tbad\tconstraint\n");

  // Main trajectory S_0..S_T.
  for (int t = 0; t <= T; t++) {
    tv *state = hist + (size_t)t * L;
    int rst = (t == 0) ? 0 : 1;
    eval(state, rst);
    fprintf(tr, "%d\t%d\t%u\t", t, rst, xcount(state));
    for (uint32_t i = 0; i < B; i++) fputc("01X"[lv(bads[i])], tr);
    fputc('\t', tr);
    for (uint32_t i = 0; i < C; i++) fputc("01X"[lv(cons[i])], tr);
    fputc('\n', tr);
    for (uint32_t i = 0; i < O; i++) outv[i] = lv(outs[i]);
    fwrite(outv, 1, O, of);
    if (t == T) break;
    observe("frame", t, rst);
    post(state + L);
  }
  fclose(tr); fclose(of);
  const tv *S1 = hist + L;

  // Choose the period with the fewest differing latches between S_T and S_{T-p}.
  const tv *ST = hist + (size_t)T * L;
  uint32_t best_diff = UINT32_MAX; int p = 0;
  for (int q = 1; q <= P; q++) {
    const tv *Sq = hist + (size_t)(T - q) * L;
    uint32_t d = 0;
    for (uint32_t i = 0; i < L && d < best_diff; i++) d += Sq[i] != ST[i];
    if (d < best_diff) { best_diff = d; p = q; }
  }
  tv *cycle = malloc((size_t)(p + 1) * L);
  memcpy(cycle, ST, L);
  join_into(cycle, hist + (size_t)(T - p) * L);
  int rounds = 0, closed = 0;
  for (rounds = 1; rounds <= 256; rounds++) {
    for (int i = 0; i < p; i++) {
      eval(cycle + (size_t)i * L, 1);
      post(cycle + (size_t)(i + 1) * L);
    }
    if (leq(cycle + (size_t)p * L, cycle)) { closed = 1; break; }
    join_into(cycle, cycle + (size_t)p * L);
  }
  int entry_ok = leq(ST, cycle);

  // Properties/outputs over the closed cycle on the main reset value.
  for (int i = 0; i < p; i++) {
    eval(cycle + (size_t)i * L, 1);
    observe("cycle", i, 1);
  }
  // Re-reset coverage over every non-initial cube.
  uint64_t rereset_bad = 0;
  for (int t = 1; t < T + p; t++) {
    const tv *c = (t < T) ? hist + (size_t)t * L : cycle + (size_t)(t - T) * L;
    eval(c, 0);
    observe(t < T ? "rereset-frame" : "rereset-cycle", t < T ? t : t - T, 0);
    post(reset_next);
    if (!leq(reset_next, S1)) {
      rereset_bad++;
      if (rereset_bad <= 5) {
        uint32_t d = 0;
        for (uint32_t i = 0; i < L; i++) d += S1[i] != 2 && reset_next[i] != S1[i];
        fprintf(stderr, "re-reset successor of %s %d not covered by S_1 (%u latches)\n",
                t < T ? "frame" : "cycle", t < T ? t : t - T, d);
      }
    }
  }
  uint32_t joined_const = 0, joined_x = 0, never = 0;
  for (uint32_t i = 0; i < O; i++) {
    if (outjoin[i] == 3) never++;
    else if (outjoin[i] == 2) joined_x++;
    else joined_const++;
  }
  snprintf(path, sizeof path, "%s.outjoin.bin", prefix);
  FILE *jf = fopen(path, "wb");
  fwrite(outjoin, 1, O, jf);
  fclose(jf);
  snprintf(path, sizeof path, "%s.result.txt", prefix);
  FILE *rf = fopen(path, "w");
  fprintf(rf, "header %u %u %u %u %u %u %u\n", M, I, L, O, A, B, C);
  fprintf(rf, "frames %d\nperiod %d\nperiod_initial_diff %u\nwidening_rounds %d\nclosed %d\nentry_ok %d\n", T,
          p, best_diff, rounds, closed, entry_ok);
  fprintf(rf, "cycle_x_latches %u\nfinal_frame_x_latches %u\n", xcount(cycle), xcount(ST));
  fprintf(rf, "property_checks %llu\nproperty_failures %llu\nrereset_uncovered %llu\n",
          (unsigned long long)checks, (unsigned long long)failures, (unsigned long long)rereset_bad);
  fprintf(rf, "outputs_constant %u\noutputs_varying %u\noutputs_never %u\n", joined_const, joined_x, never);
  int ok = closed && entry_ok && failures == 0 && rereset_bad == 0 && never == 0;
  fprintf(rf, "invariant_ok %d\n", ok);
  fclose(rf);
  printf("M=%u I=%u L=%u O=%u A=%u B=%u C=%u T=%d p=%d diff=%u rounds=%d closed=%d entry=%d "
         "failures=%llu rereset_uncovered=%llu const=%u varying=%u ok=%d\n",
         M, I, L, O, A, B, C, T, p, best_diff, rounds, closed, entry_ok, (unsigned long long)failures,
         (unsigned long long)rereset_bad, joined_const, joined_x, ok);
  return ok ? 0 : 1;
}
