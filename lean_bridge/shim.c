#include <lean/lean.h>

/* lean_string_cstr / lean_dec are static inline in lean.h; expose them for Rust. */
char const * lean_bridge_string_cstr(lean_object * o) {
    return lean_string_cstr(o);
}

void lean_bridge_dec(lean_object * o) {
    lean_dec(o);
}
