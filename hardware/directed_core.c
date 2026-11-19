#include "directed_core.h"
#include <float.h>
#include <string.h>

#pragma STDC FENV_ACCESS ON
#if defined(__FAST_MATH__) || (defined(__FINITE_MATH_ONLY__) && __FINITE_MATH_ONLY__)
#error "Directed bounds require strict floating-point compilation"
#endif
_Static_assert(FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024 &&
               sizeof(double) == 8 && FLT_EVAL_METHOD == 0,
               "This adapter requires binary64 double without excess precision");

static uint64_t bits(double value) {
    uint64_t result;
    memcpy(&result, &value, sizeof(result));
    return result;
}
static int finite_bits(uint64_t value) {
    return (value & UINT64_C(0x7ff0000000000000)) != UINT64_C(0x7ff0000000000000);
}

int gia_bounds(double a, double b, double *lo, double *hi, int operation) {
    /* Bit classification precedes all FP operations: even signaling NaNs and
       rejected environments must leave the caller's exception flags intact. */
    uint64_t ab = bits(a), bb = bits(b);
    if (!gia_fp_control_supported(gia_fp_control()) || !finite_bits(ab) ||
        !finite_bits(bb) || operation < 0 || operation > 4) return 0;
    if (operation == 4 && (ab >> 63) && (ab << 1)) return 0;
    fenv_t saved, held;
    if (fegetenv(&saved) != 0) return 0;
    int ok = 0;
    /* Even a failed hold may have changed state; retain a prior snapshot. */
    if (feholdexcept(&held) != 0) goto restore;
    volatile double av = a, bv = b;
    if (fesetround(FE_DOWNWARD) == 0 && fegetround() == FE_DOWNWARD &&
        gia_fp_control_supported(gia_fp_control())) {
        volatile double down = operation == 4 ? sqrt(av) : (operation == 3 ? av / bv : (operation == 2 ? av * bv : (operation == 1 ? av - bv : av + bv)));
        *lo = down;
        if (fesetround(FE_UPWARD) == 0 && fegetround() == FE_UPWARD &&
            gia_fp_control_supported(gia_fp_control())) {
            volatile double up = operation == 4 ? sqrt(av) : (operation == 3 ? av / bv : (operation == 2 ? av * bv : (operation == 1 ? av - bv : av + bv)));
            *hi = up;
            ok = finite_bits(bits(*lo)) && finite_bits(bits(*hi)) && *lo <= *hi;
        }
    }
restore:
    /* Restoration failure cannot safely return into Lean with altered state. */
    if (fesetenv(&saved) != 0) abort();
    return ok;
}
