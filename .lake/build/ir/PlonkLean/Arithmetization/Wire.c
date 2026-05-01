// Lean compiler output
// Module: PlonkLean.Arithmetization.Wire
// Imports: public import Init public meta import Init public import Mathlib.Data.Fin.Basic public import PlonkLean.Field.Basic
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten___redArg(lean_object* v_n_1_, lean_object* v_w_2_, lean_object* v_i_3_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = lean_nat_dec_lt(v_i_3_, v_n_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_5_ = lean_unsigned_to_nat(2u);
v___x_6_ = lean_nat_mul(v___x_5_, v_n_1_);
v___x_7_ = lean_nat_dec_lt(v_i_3_, v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v_c_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_c_8_ = lean_ctor_get(v_w_2_, 2);
lean_inc(v_c_8_);
lean_dec_ref(v_w_2_);
v___x_9_ = lean_nat_sub(v_i_3_, v___x_6_);
lean_dec(v___x_6_);
lean_dec(v_i_3_);
v___x_10_ = lean_apply_1(v_c_8_, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_b_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec(v___x_6_);
v_b_11_ = lean_ctor_get(v_w_2_, 1);
lean_inc(v_b_11_);
lean_dec_ref(v_w_2_);
v___x_12_ = lean_nat_sub(v_i_3_, v_n_1_);
lean_dec(v_i_3_);
v___x_13_ = lean_apply_1(v_b_11_, v___x_12_);
return v___x_13_;
}
}
else
{
lean_object* v_a_14_; lean_object* v___x_15_; 
v_a_14_ = lean_ctor_get(v_w_2_, 0);
lean_inc(v_a_14_);
lean_dec_ref(v_w_2_);
v___x_15_ = lean_apply_1(v_a_14_, v_i_3_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten___redArg___boxed(lean_object* v_n_16_, lean_object* v_w_17_, lean_object* v_i_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten___redArg(v_n_16_, v_w_17_, v_i_18_);
lean_dec(v_n_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten(lean_object* v_F_20_, lean_object* v_n_21_, lean_object* v_w_22_, lean_object* v_i_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten___redArg(v_n_21_, v_w_22_, v_i_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten___boxed(lean_object* v_F_25_, lean_object* v_n_26_, lean_object* v_w_27_, lean_object* v_i_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_PlonkLean_PlonkLean_Arithmetization_Witness_flatten(v_F_25_, v_n_26_, v_w_27_, v_i_28_);
lean_dec(v_n_26_);
return v_res_29_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fin_Basic(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Field_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlonkLean_PlonkLean_Arithmetization_Wire(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Field_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
