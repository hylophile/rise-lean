#include <lean/lean.h>

extern const char* run_egg(const char* input);

lean_obj_res run_egg_c(lean_obj_arg i) {
    const char* input = lean_string_cstr(i);
    const char* res = run_egg(input);
    return lean_mk_string(res);
}
