// Lean compiler output
// Module: PlonkLean.Field.Basic
// Imports: public import Init public meta import Init public import Mathlib.Algebra.Field.Basic public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots public import Mathlib.FieldTheory.Finite.Basic
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_EvaluationDomain_element___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_EvaluationDomain_element___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_EvaluationDomain_element(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_EvaluationDomain_element___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_EvaluationDomain_element___redArg(lean_object* v_inst_1_, lean_object* v_D_2_, lean_object* v_i_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_toSemiring_6_; lean_object* v_npow_7_; lean_object* v___x_8_; 
v___x_4_ = lp_mathlib_Field_toSemifield___redArg(v_inst_1_);
v___x_5_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_4_);
v_toSemiring_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc_ref(v_toSemiring_6_);
lean_dec_ref(v___x_5_);
v_npow_7_ = lean_ctor_get(v_toSemiring_6_, 3);
lean_inc(v_npow_7_);
lean_dec_ref(v_toSemiring_6_);
v___x_8_ = lean_apply_2(v_npow_7_, v_i_3_, v_D_2_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_EvaluationDomain_element___redArg___boxed(lean_object* v_inst_9_, lean_object* v_D_10_, lean_object* v_i_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = lp_PlonkLean_PlonkLean_EvaluationDomain_element___redArg(v_inst_9_, v_D_10_, v_i_11_);
lean_dec_ref(v_inst_9_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_EvaluationDomain_element(lean_object* v_F_13_, lean_object* v_inst_14_, lean_object* v_n_15_, lean_object* v_D_16_, lean_object* v_i_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lp_PlonkLean_PlonkLean_EvaluationDomain_element___redArg(v_inst_14_, v_D_16_, v_i_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_EvaluationDomain_element___boxed(lean_object* v_F_19_, lean_object* v_inst_20_, lean_object* v_n_21_, lean_object* v_D_22_, lean_object* v_i_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = lp_PlonkLean_PlonkLean_EvaluationDomain_element(v_F_19_, v_inst_20_, v_n_21_, v_D_22_, v_i_23_);
lean_dec(v_n_21_);
lean_dec_ref(v_inst_20_);
return v_res_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Field_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_RootsOfUnity_PrimitiveRoots(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_FieldTheory_Finite_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlonkLean_PlonkLean_Field_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Field_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_RootsOfUnity_PrimitiveRoots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_FieldTheory_Finite_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
