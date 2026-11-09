#include <lean/lean.h>
#include <fenv.h>
#include <float.h>
#include <math.h>
#include <stdlib.h>
#include <stdint.h>
#include <xmmintrin.h>
#if !defined(__x86_64__)
#error "This first adapter is tested and supported only on x86_64"
#endif
#pragma STDC FENV_ACCESS ON
_Static_assert(FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024 && sizeof(double) == 8,
               "This demo requires binary64 double");

/* This adapter is not verified. Failure returns unknown, never absence.
   Hold exceptions, change rounding only within this call, and restore fenv. */
static int bounds(double a, double b, double *lo, double *hi, int operation) {
    if (!isfinite(a) || !isfinite(b)) return 0;
    if (operation == 4 && a < 0.0) return 0;
    /* Reject flush-to-zero and denormals-are-zero execution modes. */
    if ((_mm_getcsr() & 0x8040u) != 0) return 0;
    fenv_t saved;
    if (feholdexcept(&saved) != 0) return 0;
    int ok = 0;
    volatile double av = a, bv = b;
    if (fesetround(FE_DOWNWARD) == 0 && fegetround() == FE_DOWNWARD) {
        volatile double down = operation == 4 ? sqrt(av) : (operation == 3 ? av / bv : (operation == 2 ? av * bv : (operation == 1 ? av - bv : av + bv)));
        *lo = down;
        if (fesetround(FE_UPWARD) == 0 && fegetround() == FE_UPWARD) {
            volatile double up = operation == 4 ? sqrt(av) : (operation == 3 ? av / bv : (operation == 2 ? av * bv : (operation == 1 ? av - bv : av + bv)));
            *hi = up;
            ok = isfinite(*lo) && isfinite(*hi) && *lo <= *hi;
        }
    }
    /* Restoration failure cannot safely return into Lean with altered state. */
    if (fesetenv(&saved) != 0) abort();
    return ok;
}

static lean_obj_res boxed_bounds(double a, double b, int operation) {
    double lo, hi;
    lean_object *option = lean_box(0);
    if (bounds(a, b, &lo, &hi, operation)) {
        lean_object *pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, lean_box_float(lo));
        lean_ctor_set(pair, 1, lean_box_float(hi));
        option = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(option, 0, pair);
    }
    return lean_io_result_mk_ok(option);
}

LEAN_EXPORT lean_obj_res gia_directed_add(double a, double b, lean_obj_arg world) {
    (void)world;
    return boxed_bounds(a, b, 0);
}

LEAN_EXPORT lean_obj_res gia_directed_sub(double a, double b, lean_obj_arg world) {
    (void)world;
    return boxed_bounds(a, b, 1);
}

LEAN_EXPORT lean_obj_res gia_directed_mul(double a, double b, lean_obj_arg world) {
    (void)world;
    return boxed_bounds(a, b, 2);
}

LEAN_EXPORT lean_obj_res gia_directed_div(double a, double b, lean_obj_arg world) {
    (void)world;
    return boxed_bounds(a, b, 3);
}

LEAN_EXPORT lean_obj_res gia_directed_sqrt(double a, lean_obj_arg world) {
    (void)world;
    return boxed_bounds(a, 0.0, 4);
}

LEAN_EXPORT lean_obj_res gia_rounding_restored(lean_obj_arg world) {
    (void)world;
    fenv_t saved;
    if (feholdexcept(&saved) != 0) return lean_io_result_mk_ok(lean_box(0));
    int ok = 1;
    const int modes[] = {FE_TONEAREST, FE_DOWNWARD, FE_UPWARD, FE_TOWARDZERO};
    for (unsigned i = 0; i < 4; ++i) for (int operation = 0; operation < 5; ++operation) {
        double lo, hi;
        if (fesetround(modes[i]) != 0) { ok = 0; break; }
        /* Confirm that the multiplication probe really raises fresh flags. */
        if (operation == 2) {
            feclearexcept(FE_ALL_EXCEPT);
            volatile double tiny = 0x1p-1074, half = 0.5;
            volatile double underflow = tiny * half;
            (void)underflow;
            int raised = fetestexcept(FE_UNDERFLOW | FE_INEXACT);
            if (raised != (FE_UNDERFLOW | FE_INEXACT)) ok = 0;
        }
        if (operation == 3) {
            feclearexcept(FE_ALL_EXCEPT);
            volatile double one = 1.0, three = 3.0;
            volatile double inexact = one / three;
            (void)inexact;
            if (!(fetestexcept(FE_INEXACT) & FE_INEXACT)) ok = 0;
        }
        if (operation == 4) {
            feclearexcept(FE_ALL_EXCEPT);
            volatile double two = 2.0;
            volatile double inexact = sqrt(two);
            (void)inexact;
            if (!(fetestexcept(FE_INEXACT) & FE_INEXACT)) ok = 0;
        }
        feclearexcept(FE_ALL_EXCEPT);
        feraiseexcept(FE_INVALID);
        int flags = fetestexcept(FE_ALL_EXCEPT);
        double a = operation == 4 ? 2.0 : (operation == 2 ? 0x1p-1074 : 1.0);
        double b = operation == 3 ? 3.0 : (operation == 2 ? 0.5 : 0x1p-54);
        if (!bounds(a, b, &lo, &hi, operation) || fegetround() != modes[i] ||
            fetestexcept(FE_ALL_EXCEPT) != flags) ok = 0;
    }
    /* Unsupported flush modes must yield unknown, not a false finite bound. */
    unsigned int csr = _mm_getcsr();
    double lo, hi;
    _mm_setcsr(csr | 0x8040u);
    if (bounds(1.0, 1.0, &lo, &hi, 0) || bounds(1.0, 1.0, &lo, &hi, 1) || bounds(1.0, 1.0, &lo, &hi, 2) || bounds(1.0, 1.0, &lo, &hi, 3) || bounds(1.0, 0.0, &lo, &hi, 4)) ok = 0;
    _mm_setcsr(csr);
    if (fesetenv(&saved) != 0) abort();
    return lean_io_result_mk_ok(lean_box(ok));
}
