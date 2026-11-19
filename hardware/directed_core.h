#ifndef GIA_DIRECTED_CORE_H
#define GIA_DIRECTED_CORE_H

#include <fenv.h>
#include <math.h>
#include <stdint.h>
#include <stdlib.h>

#if defined(__x86_64__)
#include <xmmintrin.h>
static inline uint64_t gia_fp_control(void) { return _mm_getcsr(); }
static inline void gia_set_fp_control(uint64_t value) { _mm_setcsr((unsigned)value); }
static inline int gia_fp_control_supported(uint64_t value) {
    return (value & UINT64_C(0x8040)) == 0;
}
#elif defined(__aarch64__)
static inline uint64_t gia_fp_control(void) {
    uint64_t value;
    __asm__ volatile("mrs %0, fpcr" : "=r"(value));
    return value;
}
static inline void gia_set_fp_control(uint64_t value) {
    __asm__ volatile("msr fpcr, %0" : : "r"(value) : "memory");
}
static inline int gia_fp_control_supported(uint64_t value) {
    /* Admit only the four RMode encodings. Fail closed on FZ, FZ16, DN,
       AHP, AH, FIZ, trap enables, and any additional/unknown controls.
       Half-precision is not used; rejecting FZ16 is deliberately conservative. */
    return (value & ~UINT64_C(0x00c00000)) == 0;
}
#else
#error "The directed adapter supports only qualified x86_64 and AArch64 targets"
#endif

/* Finite-result binary64 operation: 0 add, 1 subtract, 2 multiply,
   3 divide, 4 square root. Failure means unknown, never absence.
   This C implementation and its compiler/processor correspondence are unproved. */
int gia_bounds(double a, double b, double *lo, double *hi, int operation);
#endif
