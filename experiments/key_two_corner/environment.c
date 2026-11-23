/* Test-only caller-state probe; no arithmetic implementation. */
#include <lean/lean.h>
#include <fenv.h>
#include <stdint.h>
static fenv_t saved;
static unsigned iteration;
static int expected_mode, expected_flags;
LEAN_EXPORT lean_obj_res gia_experiment_begin(lean_obj_arg world) {
 (void)world;
 const int modes[] = {FE_TONEAREST, FE_DOWNWARD, FE_UPWARD, FE_TOWARDZERO};
 int ok = fegetenv(&saved)==0;
 expected_mode=modes[(iteration/3)%4];
 expected_flags=(iteration/12)%2 ? FE_DIVBYZERO : 0;
 ++iteration;
 ok &= feclearexcept(FE_ALL_EXCEPT)==0;
 ok &= fesetround(expected_mode)==0;
 if(expected_flags) ok &= feraiseexcept(expected_flags)==0;
 return lean_io_result_mk_ok(lean_box(ok));
}
LEAN_EXPORT lean_obj_res gia_experiment_end(lean_obj_arg world) {
 (void)world;
 int ok=fegetround()==expected_mode && fetestexcept(FE_ALL_EXCEPT)==expected_flags;
 ok &= fesetenv(&saved)==0;
 return lean_io_result_mk_ok(lean_box(ok));
}
