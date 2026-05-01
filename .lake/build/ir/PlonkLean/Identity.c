// Lean compiler output
// Module: PlonkLean.Identity
// Imports: public import Init public meta import Init public import PlonkLean.Arithmetization.ConstraintSystem public import PlonkLean.Permutation.GrandProduct public import PlonkLean.Polynomial.Vanishing public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic public import Mathlib.Algebra.Polynomial.Roots
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_PlonkLean_PlonkLean_Permutation_flatOut(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesA___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesA___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesA(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesA___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesB___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesB___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesB(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesB___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesC___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesC___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesC(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesC___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesA___redArg(lean_object* v_inst_1_, lean_object* v_n_2_, lean_object* v_D_3_, lean_object* v_00_u03c3_4_, lean_object* v_k1_5_, lean_object* v_k2_6_, lean_object* v_i_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(v_inst_1_, v_n_2_, v_D_3_, v_00_u03c3_4_, v_k1_5_, v_k2_6_, v_i_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesA___redArg___boxed(lean_object* v_inst_9_, lean_object* v_n_10_, lean_object* v_D_11_, lean_object* v_00_u03c3_12_, lean_object* v_k1_13_, lean_object* v_k2_14_, lean_object* v_i_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_PlonkLean_PlonkLean_sigmaValuesA___redArg(v_inst_9_, v_n_10_, v_D_11_, v_00_u03c3_12_, v_k1_13_, v_k2_14_, v_i_15_);
lean_dec(v_k2_14_);
lean_dec(v_k1_13_);
lean_dec(v_n_10_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesA(lean_object* v_F_17_, lean_object* v_inst_18_, lean_object* v_n_19_, lean_object* v_D_20_, lean_object* v_00_u03c3_21_, lean_object* v_k1_22_, lean_object* v_k2_23_, lean_object* v_i_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(v_inst_18_, v_n_19_, v_D_20_, v_00_u03c3_21_, v_k1_22_, v_k2_23_, v_i_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesA___boxed(lean_object* v_F_26_, lean_object* v_inst_27_, lean_object* v_n_28_, lean_object* v_D_29_, lean_object* v_00_u03c3_30_, lean_object* v_k1_31_, lean_object* v_k2_32_, lean_object* v_i_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = lp_PlonkLean_PlonkLean_sigmaValuesA(v_F_26_, v_inst_27_, v_n_28_, v_D_29_, v_00_u03c3_30_, v_k1_31_, v_k2_32_, v_i_33_);
lean_dec(v_k2_32_);
lean_dec(v_k1_31_);
lean_dec(v_n_28_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesB___redArg(lean_object* v_inst_35_, lean_object* v_n_36_, lean_object* v_D_37_, lean_object* v_00_u03c3_38_, lean_object* v_k1_39_, lean_object* v_k2_40_, lean_object* v_i_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_nat_add(v_i_41_, v_n_36_);
v___x_43_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(v_inst_35_, v_n_36_, v_D_37_, v_00_u03c3_38_, v_k1_39_, v_k2_40_, v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesB___redArg___boxed(lean_object* v_inst_44_, lean_object* v_n_45_, lean_object* v_D_46_, lean_object* v_00_u03c3_47_, lean_object* v_k1_48_, lean_object* v_k2_49_, lean_object* v_i_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = lp_PlonkLean_PlonkLean_sigmaValuesB___redArg(v_inst_44_, v_n_45_, v_D_46_, v_00_u03c3_47_, v_k1_48_, v_k2_49_, v_i_50_);
lean_dec(v_i_50_);
lean_dec(v_k2_49_);
lean_dec(v_k1_48_);
lean_dec(v_n_45_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesB(lean_object* v_F_52_, lean_object* v_inst_53_, lean_object* v_n_54_, lean_object* v_D_55_, lean_object* v_00_u03c3_56_, lean_object* v_k1_57_, lean_object* v_k2_58_, lean_object* v_i_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_PlonkLean_PlonkLean_sigmaValuesB___redArg(v_inst_53_, v_n_54_, v_D_55_, v_00_u03c3_56_, v_k1_57_, v_k2_58_, v_i_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesB___boxed(lean_object* v_F_61_, lean_object* v_inst_62_, lean_object* v_n_63_, lean_object* v_D_64_, lean_object* v_00_u03c3_65_, lean_object* v_k1_66_, lean_object* v_k2_67_, lean_object* v_i_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = lp_PlonkLean_PlonkLean_sigmaValuesB(v_F_61_, v_inst_62_, v_n_63_, v_D_64_, v_00_u03c3_65_, v_k1_66_, v_k2_67_, v_i_68_);
lean_dec(v_i_68_);
lean_dec(v_k2_67_);
lean_dec(v_k1_66_);
lean_dec(v_n_63_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesC___redArg(lean_object* v_inst_70_, lean_object* v_n_71_, lean_object* v_D_72_, lean_object* v_00_u03c3_73_, lean_object* v_k1_74_, lean_object* v_k2_75_, lean_object* v_i_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lp_PlonkLean_PlonkLean_Permutation_flatOut(v_n_71_, v_i_76_);
v___x_78_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(v_inst_70_, v_n_71_, v_D_72_, v_00_u03c3_73_, v_k1_74_, v_k2_75_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesC___redArg___boxed(lean_object* v_inst_79_, lean_object* v_n_80_, lean_object* v_D_81_, lean_object* v_00_u03c3_82_, lean_object* v_k1_83_, lean_object* v_k2_84_, lean_object* v_i_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lp_PlonkLean_PlonkLean_sigmaValuesC___redArg(v_inst_79_, v_n_80_, v_D_81_, v_00_u03c3_82_, v_k1_83_, v_k2_84_, v_i_85_);
lean_dec(v_i_85_);
lean_dec(v_k2_84_);
lean_dec(v_k1_83_);
lean_dec(v_n_80_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesC(lean_object* v_F_87_, lean_object* v_inst_88_, lean_object* v_n_89_, lean_object* v_D_90_, lean_object* v_00_u03c3_91_, lean_object* v_k1_92_, lean_object* v_k2_93_, lean_object* v_i_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lp_PlonkLean_PlonkLean_sigmaValuesC___redArg(v_inst_88_, v_n_89_, v_D_90_, v_00_u03c3_91_, v_k1_92_, v_k2_93_, v_i_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_sigmaValuesC___boxed(lean_object* v_F_96_, lean_object* v_inst_97_, lean_object* v_n_98_, lean_object* v_D_99_, lean_object* v_00_u03c3_100_, lean_object* v_k1_101_, lean_object* v_k2_102_, lean_object* v_i_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = lp_PlonkLean_PlonkLean_sigmaValuesC(v_F_96_, v_inst_97_, v_n_98_, v_D_99_, v_00_u03c3_100_, v_k1_101_, v_k2_102_, v_i_103_);
lean_dec(v_i_103_);
lean_dec(v_k2_102_);
lean_dec(v_k1_101_);
lean_dec(v_n_98_);
return v_res_104_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Arithmetization_ConstraintSystem(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Permutation_GrandProduct(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Polynomial_Vanishing(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_Polynomial_Cyclotomic_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_Roots(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlonkLean_PlonkLean_Identity(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Arithmetization_ConstraintSystem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Permutation_GrandProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Polynomial_Vanishing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_Polynomial_Cyclotomic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_Roots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
