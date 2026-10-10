#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

/* lean_string_cstr / lean_dec are static inline in lean.h; expose them for Rust. */
char const * lean_binding_string_cstr(lean_object * o) {
    return lean_string_cstr(o);
}

void lean_binding_dec(lean_object * o) {
    lean_dec(o);
}

void lean_binding_inc(lean_object * o) {
    lean_inc(o);
}

/* Build a Lean `Array UInt32` for `lean_rv32_expand_words_snapshot`. */
lean_object * lean_binding_mk_uint32_array(uint32_t const * data, size_t len) {
    lean_object * arr = lean_alloc_array(len, len);
    for (size_t i = 0; i < len; i++) {
        lean_array_set_core(arr, i, lean_box_uint32(data[i]));
    }
    return arr;
}

lean_object * lean_binding_mk_string(char const * utf8) {
    return lean_mk_string(utf8);
}
