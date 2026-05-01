// Lean compiler output
// Module: PlonkLean.Arithmetization.Gate
// Imports: public import Init public meta import Init public import PlonkLean.Arithmetization.Wire
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
lean_object* lp_mathlib_Field_toEuclideanDomain___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Selectors_gateValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Selectors_gateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Selectors_gateValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Selectors_gateValue___redArg(lean_object* v_inst_1_, lean_object* v_S_2_, lean_object* v_w_3_, lean_object* v_i_4_){
_start:
{
lean_object* v___x_5_; lean_object* v_toCommRing_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v_toMul_10_; lean_object* v_toAdd_11_; lean_object* v_qM_12_; lean_object* v_qL_13_; lean_object* v_qR_14_; lean_object* v_qO_15_; lean_object* v_qC_16_; lean_object* v_a_17_; lean_object* v_b_18_; lean_object* v_c_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_5_ = lp_mathlib_Field_toEuclideanDomain___redArg(v_inst_1_);
v_toCommRing_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc_ref(v_toCommRing_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_6_);
v___x_8_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_7_);
v___x_9_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_8_);
v_toMul_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_n(v_toMul_10_, 5);
v_toAdd_11_ = lean_ctor_get(v___x_9_, 1);
lean_inc_n(v_toAdd_11_, 4);
lean_dec_ref(v___x_9_);
v_qM_12_ = lean_ctor_get(v_S_2_, 0);
lean_inc(v_qM_12_);
v_qL_13_ = lean_ctor_get(v_S_2_, 1);
lean_inc(v_qL_13_);
v_qR_14_ = lean_ctor_get(v_S_2_, 2);
lean_inc(v_qR_14_);
v_qO_15_ = lean_ctor_get(v_S_2_, 3);
lean_inc(v_qO_15_);
v_qC_16_ = lean_ctor_get(v_S_2_, 4);
lean_inc(v_qC_16_);
lean_dec_ref(v_S_2_);
v_a_17_ = lean_ctor_get(v_w_3_, 0);
lean_inc(v_a_17_);
v_b_18_ = lean_ctor_get(v_w_3_, 1);
lean_inc(v_b_18_);
v_c_19_ = lean_ctor_get(v_w_3_, 2);
lean_inc(v_c_19_);
lean_dec_ref(v_w_3_);
lean_inc_n(v_i_4_, 7);
v___x_20_ = lean_apply_1(v_qM_12_, v_i_4_);
v___x_21_ = lean_apply_1(v_a_17_, v_i_4_);
lean_inc(v___x_21_);
v___x_22_ = lean_apply_2(v_toMul_10_, v___x_20_, v___x_21_);
v___x_23_ = lean_apply_1(v_b_18_, v_i_4_);
lean_inc(v___x_23_);
v___x_24_ = lean_apply_2(v_toMul_10_, v___x_22_, v___x_23_);
v___x_25_ = lean_apply_1(v_qL_13_, v_i_4_);
v___x_26_ = lean_apply_2(v_toMul_10_, v___x_25_, v___x_21_);
v___x_27_ = lean_apply_2(v_toAdd_11_, v___x_24_, v___x_26_);
v___x_28_ = lean_apply_1(v_qR_14_, v_i_4_);
v___x_29_ = lean_apply_2(v_toMul_10_, v___x_28_, v___x_23_);
v___x_30_ = lean_apply_2(v_toAdd_11_, v___x_27_, v___x_29_);
v___x_31_ = lean_apply_1(v_qO_15_, v_i_4_);
v___x_32_ = lean_apply_1(v_c_19_, v_i_4_);
v___x_33_ = lean_apply_2(v_toMul_10_, v___x_31_, v___x_32_);
v___x_34_ = lean_apply_2(v_toAdd_11_, v___x_30_, v___x_33_);
v___x_35_ = lean_apply_1(v_qC_16_, v_i_4_);
v___x_36_ = lean_apply_2(v_toAdd_11_, v___x_34_, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Selectors_gateValue(lean_object* v_F_37_, lean_object* v_inst_38_, lean_object* v_n_39_, lean_object* v_S_40_, lean_object* v_w_41_, lean_object* v_i_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_PlonkLean_PlonkLean_Arithmetization_Selectors_gateValue___redArg(v_inst_38_, v_S_40_, v_w_41_, v_i_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Arithmetization_Selectors_gateValue___boxed(lean_object* v_F_44_, lean_object* v_inst_45_, lean_object* v_n_46_, lean_object* v_S_47_, lean_object* v_w_48_, lean_object* v_i_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_PlonkLean_PlonkLean_Arithmetization_Selectors_gateValue(v_F_44_, v_inst_45_, v_n_46_, v_S_47_, v_w_48_, v_i_49_);
lean_dec(v_n_46_);
return v_res_50_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Arithmetization_Wire(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlonkLean_PlonkLean_Arithmetization_Gate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Arithmetization_Wire(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
