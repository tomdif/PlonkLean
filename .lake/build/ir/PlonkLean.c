// Lean compiler output
// Module: PlonkLean
// Imports: public import Init public meta import Init public import PlonkLean.Field.Basic public import PlonkLean.Polynomial.Vanishing public import PlonkLean.Polynomial.Lagrange public import PlonkLean.Arithmetization.Wire public import PlonkLean.Arithmetization.Gate public import PlonkLean.Arithmetization.ConstraintSystem public import PlonkLean.Permutation.Sigma public import PlonkLean.Permutation.GrandProduct public import PlonkLean.Lookup.Plookup public import PlonkLean.Identity
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Field_Basic(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Polynomial_Vanishing(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Polynomial_Lagrange(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Arithmetization_Wire(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Arithmetization_Gate(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Arithmetization_ConstraintSystem(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Permutation_Sigma(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Permutation_GrandProduct(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Lookup_Plookup(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Identity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlonkLean_PlonkLean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Field_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Polynomial_Vanishing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Polynomial_Lagrange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Arithmetization_Wire(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Arithmetization_Gate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Arithmetization_ConstraintSystem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Permutation_Sigma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Permutation_GrandProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Lookup_Plookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Identity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
