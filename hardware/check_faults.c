/* Fault injection tests only; production uses the actual libc fenv functions. */
#include "directed_core.h"
#include <signal.h>
#include <stdio.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

#pragma STDC FENV_ACCESS ON
static int fault, round_calls;
int gia_test_feholdexcept(fenv_t *env) {
    int result = feholdexcept(env);
    if (fault == 1) { fesetround(FE_UPWARD); feraiseexcept(FE_INEXACT); return 1; }
    return result;
}
int gia_test_fesetround(int mode) {
    int result = fesetround(mode);
    ++round_calls;
    if ((fault == 2 && round_calls == 1) || (fault == 3 && round_calls == 2)) return 1;
    return result;
}
int gia_test_fesetenv(const fenv_t *env) {
    if (fault == 4) return 1;
    return fesetenv(env);
}
int main(void) {
    fenv_t outer;
    if (fegetenv(&outer) != 0) return 1;
    for (fault = 1; fault <= 3; ++fault) {
        if (fesetround(FE_TOWARDZERO) || feclearexcept(FE_ALL_EXCEPT) ||
            feraiseexcept(FE_DIVBYZERO)) return 1;
        uint64_t control = gia_fp_control();
        int flags = fetestexcept(FE_ALL_EXCEPT);
        round_calls = 0;
        double lo, hi;
        int ok = !gia_bounds(1.0, 0x1p-54, &lo, &hi, 0) &&
            fegetround() == FE_TOWARDZERO && fetestexcept(FE_ALL_EXCEPT) == flags &&
            gia_fp_control() == control;
        if (fesetenv(&outer) != 0 || !ok) return 2;
    }
    pid_t child = fork();
    if (child < 0) return 3;
    if (child == 0) {
        struct rlimit limit = {0, 0};
        if (setrlimit(RLIMIT_CORE, &limit) != 0) _exit(4);
        fault = 4; round_calls = 0;
        double lo, hi;
        (void)gia_bounds(1.0, 0x1p-54, &lo, &hi, 0);
        _exit(5);
    }
    int status;
    if (waitpid(child, &status, 0) != child || !WIFSIGNALED(status) ||
        WTERMSIG(status) != SIGABRT) return 6;
    puts("PASS: failed hold/downward/upward setup restores caller; restore failure aborts");
    return 0;
}
