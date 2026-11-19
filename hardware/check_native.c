/* Standalone qualification of the exact production C core, without Lean. */
#include "directed_core.h"
#include <inttypes.h>
#include <stdio.h>
#include <string.h>

#pragma STDC FENV_ACCESS ON

struct state { uint64_t control, status, x87_control, x87_status; };
static struct state state(void) {
    struct state s = {gia_fp_control(), 0, 0, 0};
#if defined(__aarch64__)
    __asm__ volatile("mrs %0, fpsr" : "=r"(s.status));
#else
    unsigned short control, status;
    __asm__ volatile("fnstcw %0" : "=m"(control));
    __asm__ volatile("fnstsw %0" : "=m"(status));
    s.x87_control = control; s.x87_status = status;
#endif
    return s;
}
static int same(struct state a, struct state b) {
    return a.control == b.control && a.status == b.status &&
           a.x87_control == b.x87_control && a.x87_status == b.x87_status;
}
static double value(uint64_t b) { double d; memcpy(&d, &b, 8); return d; }
static uint64_t bits(double d) { uint64_t b; memcpy(&b, &d, 8); return b; }
static const int modes[] = {FE_TONEAREST, FE_DOWNWARD, FE_UPWARD, FE_TOWARDZERO};

static int environment(void) {
    fenv_t outer;
    if (fegetenv(&outer) != 0) return 1;
    int ok = 1;
#if defined(__aarch64__)
    const unsigned controls[] = {0, 1, 2, 8, 9, 10, 11, 12, 15, 19, 24, 25, 26};
    for (unsigned bit = 0; bit < 64; ++bit)
        if (gia_fp_control_supported(UINT64_C(1) << bit) != (bit == 22 || bit == 23)) ok = 0;
#else
    const unsigned controls[] = {6, 15};
#endif
    for (unsigned i = 0; i < sizeof(controls) / sizeof(*controls); ++i) {
        if (fesetenv(FE_DFL_ENV) != 0 || feclearexcept(FE_ALL_EXCEPT) != 0) return 1;
        uint64_t requested = UINT64_C(1) << controls[i];
        uint64_t original = gia_fp_control();
        gia_set_fp_control(original | requested);
        struct state before = state();
        int available = (before.control & requested) != 0;
        int rejected = available, restored = available;
        int mandatory = controls[i] == 24;
#if defined(__x86_64__)
        mandatory = 1;
#endif
        if (mandatory && !available) ok = 0;
        if (available) for (int op = 0; op < 5; ++op) {
            double lo, hi;
            if (gia_bounds(1.0, 1.0, &lo, &hi, op)) rejected = 0;
            if (!same(before, state())) restored = 0;
        }
        gia_set_fp_control(original);
        if (fesetenv(&outer) != 0) return 1;
        if (available && (!rejected || !restored)) ok = 0;
        printf("control bit=%u available=%d rejected=%d restored=%d\n",
               controls[i], available, rejected, restored);
    }
    /* Sticky flags other than the five C flags must also survive. */
#if defined(__aarch64__)
    if (fesetenv(FE_DFL_ENV) != 0) return 1;
    uint64_t fpsr = UINT64_C(1) << 27; /* QC: unrelated cumulative SIMD saturation. */
    __asm__ volatile("msr fpsr, %0" : : "r"(fpsr) : "memory");
    struct state before = state();
    double lo, hi;
    int success = gia_bounds(1.0, 0x1p-54, &lo, &hi, 0);
    int preserved = same(before, state());
    int failure = !gia_bounds(value(UINT64_C(0x7fefffffffffffff)), 2.0, &lo, &hi, 2);
    preserved = preserved && same(before, state());
    if (fesetenv(&outer) != 0) return 1;
    if (!success || !failure || !preserved || before.status != fpsr) ok = 0;
    printf("non_c_status_preserved=%d\n", preserved);
#endif
    return ok ? 0 : 1;
}
int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "--environment") == 0) return environment();
    if (argc != 1) return 2;
    fenv_t outer;
    if (fegetenv(&outer) != 0 || !gia_fp_control_supported(gia_fp_control())) return 3;
    unsigned operation; uint64_t a, b; size_t id = 0;
    while (scanf("%u %" SCNx64 " %" SCNx64, &operation, &a, &b) == 3) {
        for (unsigned mode = 0; mode < 4; ++mode) for (unsigned seed = 0; seed < 2; ++seed) {
            if (fesetround(modes[mode]) != 0 || feclearexcept(FE_ALL_EXCEPT) != 0) return 4;
            if (seed && feraiseexcept(FE_DIVBYZERO) != 0) return 4;
            if (fegetround() != modes[mode] ||
                fetestexcept(FE_ALL_EXCEPT) != (seed ? FE_DIVBYZERO : 0)) return 4;
            struct state before = state();
            double lo = 0, hi = 0;
            int success = gia_bounds(value(a), value(b), &lo, &hi, (int)operation);
            int preserved = same(before, state());
            uint64_t lb = success ? bits(lo) : 0, hb = success ? bits(hi) : 0;
            if (fesetenv(&outer) != 0) return 4;
            printf("%zu %u %u %d %016" PRIx64 " %016" PRIx64 " %d\n",
                   id, mode, seed, success, lb, hb, preserved);
            if (!preserved) return 5;
        }
        ++id;
    }
    if (!feof(stdin)) return 6;
    return 0;
}
