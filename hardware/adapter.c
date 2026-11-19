#include <lean/lean.h>
#include "directed_core.h"

#pragma STDC FENV_ACCESS ON

static lean_obj_res boxed_bounds(double a, double b, int operation) {
    double lo, hi;
    lean_object *option = lean_box(0);
    if (gia_bounds(a, b, &lo, &hi, operation)) {
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
        if (!gia_bounds(a, b, &lo, &hi, operation) || fegetround() != modes[i] ||
            fetestexcept(FE_ALL_EXCEPT) != flags) ok = 0;
    }
    /* Check each flush mode independently; never infer rejection from an
       ignored control write or from the other enabled flush mode. */
    uint64_t csr = gia_fp_control();
#if defined(__x86_64__)
    const uint64_t flushes[] = {UINT64_C(1) << 6, UINT64_C(1) << 15};
#else
    const uint64_t flushes[] = {UINT64_C(1) << 24};
#endif
    for (unsigned i = 0; i < sizeof(flushes) / sizeof(*flushes); ++i) {
        gia_set_fp_control(csr | flushes[i]);
        uint64_t rejected_control = gia_fp_control();
        if (!(rejected_control & flushes[i])) ok = 0;
        for (int operation = 0; operation < 5; ++operation) {
            double lo, hi;
            if (gia_bounds(1.0, 1.0, &lo, &hi, operation) ||
                gia_fp_control() != rejected_control) ok = 0;
        }
        gia_set_fp_control(csr);
    }
    if (fesetenv(&saved) != 0) abort();
    return lean_io_result_mk_ok(lean_box(ok));
}
