// Lean compiler output
// Module: PlonkLean.Permutation.GrandProduct
// Imports: public import Init public meta import Init public import PlonkLean.Permutation.Sigma public import PlonkLean.Polynomial.Lagrange public import PlonkLean.Polynomial.Vanishing public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
lean_object* lp_mathlib_Field_toEuclideanDomain___redArg(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lp_mathlib_Field_toDivisionRing___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_PlonkLean_PlonkLean_EvaluationDomain_element___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_decompose(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_decompose___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_cosetRep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_cosetRep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_cosetRep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_cosetRep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_idValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_idValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_idValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_idValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_sigmaValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_sigmaValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatLeft___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatLeft___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatOut(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatOut___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_num___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_num___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_num(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_num___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_denom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_denom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_denom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_denom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_decompose(lean_object* v_n_1_, lean_object* v_i_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_lt(v_i_2_, v_n_1_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_mul(v___x_4_, v_n_1_);
v___x_6_ = lean_nat_dec_lt(v_i_2_, v___x_5_);
if (v___x_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_nat_sub(v_i_2_, v___x_5_);
lean_dec(v___x_5_);
lean_dec(v_i_2_);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_4_);
lean_ctor_set(v___x_8_, 1, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
lean_dec(v___x_5_);
v___x_9_ = lean_unsigned_to_nat(1u);
v___x_10_ = lean_nat_sub(v_i_2_, v_n_1_);
lean_dec(v_i_2_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_9_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
return v___x_11_;
}
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_unsigned_to_nat(0u);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v_i_2_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_decompose___boxed(lean_object* v_n_14_, lean_object* v_i_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_PlonkLean_PlonkLean_Permutation_decompose(v_n_14_, v_i_15_);
lean_dec(v_n_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_cosetRep___redArg(lean_object* v_inst_17_, lean_object* v_k1_18_, lean_object* v_k2_19_, lean_object* v_x_20_){
_start:
{
lean_object* v___x_21_; lean_object* v_toRing_22_; lean_object* v___x_23_; lean_object* v_toAddMonoidWithOne_24_; lean_object* v_toOne_25_; lean_object* v_zero_26_; uint8_t v_isZero_27_; 
v___x_21_ = lp_mathlib_Field_toDivisionRing___redArg(v_inst_17_);
v_toRing_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_toRing_22_);
lean_dec_ref(v___x_21_);
v___x_23_ = lp_mathlib_Ring_toAddGroupWithOne___redArg(v_toRing_22_);
v_toAddMonoidWithOne_24_ = lean_ctor_get(v___x_23_, 1);
lean_inc_ref(v_toAddMonoidWithOne_24_);
lean_dec_ref(v___x_23_);
v_toOne_25_ = lean_ctor_get(v_toAddMonoidWithOne_24_, 2);
lean_inc(v_toOne_25_);
lean_dec_ref(v_toAddMonoidWithOne_24_);
v_zero_26_ = lean_unsigned_to_nat(0u);
v_isZero_27_ = lean_nat_dec_eq(v_x_20_, v_zero_26_);
if (v_isZero_27_ == 1)
{
return v_toOne_25_;
}
else
{
lean_object* v_one_28_; lean_object* v_n_29_; uint8_t v_isZero_30_; 
lean_dec(v_toOne_25_);
v_one_28_ = lean_unsigned_to_nat(1u);
v_n_29_ = lean_nat_sub(v_x_20_, v_one_28_);
v_isZero_30_ = lean_nat_dec_eq(v_n_29_, v_zero_26_);
if (v_isZero_30_ == 1)
{
lean_dec(v_n_29_);
lean_inc(v_k1_18_);
return v_k1_18_;
}
else
{
lean_object* v_n_31_; uint8_t v_isZero_32_; 
v_n_31_ = lean_nat_sub(v_n_29_, v_one_28_);
lean_dec(v_n_29_);
v_isZero_32_ = lean_nat_dec_eq(v_n_31_, v_zero_26_);
lean_dec(v_n_31_);
lean_inc(v_k2_19_);
return v_k2_19_;
}
}
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_cosetRep___redArg___boxed(lean_object* v_inst_33_, lean_object* v_k1_34_, lean_object* v_k2_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_PlonkLean_PlonkLean_Permutation_cosetRep___redArg(v_inst_33_, v_k1_34_, v_k2_35_, v_x_36_);
lean_dec(v_x_36_);
lean_dec(v_k2_35_);
lean_dec(v_k1_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_cosetRep(lean_object* v_F_38_, lean_object* v_inst_39_, lean_object* v_k1_40_, lean_object* v_k2_41_, lean_object* v_x_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_PlonkLean_PlonkLean_Permutation_cosetRep___redArg(v_inst_39_, v_k1_40_, v_k2_41_, v_x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_cosetRep___boxed(lean_object* v_F_44_, lean_object* v_inst_45_, lean_object* v_k1_46_, lean_object* v_k2_47_, lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = lp_PlonkLean_PlonkLean_Permutation_cosetRep(v_F_44_, v_inst_45_, v_k1_46_, v_k2_47_, v_x_48_);
lean_dec(v_x_48_);
lean_dec(v_k2_47_);
lean_dec(v_k1_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_idValue___redArg(lean_object* v_inst_50_, lean_object* v_n_51_, lean_object* v_D_52_, lean_object* v_k1_53_, lean_object* v_k2_54_, lean_object* v_i_55_){
_start:
{
lean_object* v___x_56_; lean_object* v_toCommRing_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_toMul_61_; lean_object* v_p_62_; lean_object* v_fst_63_; lean_object* v_snd_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
lean_inc_ref_n(v_inst_50_, 2);
v___x_56_ = lp_mathlib_Field_toEuclideanDomain___redArg(v_inst_50_);
v_toCommRing_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc_ref(v_toCommRing_57_);
lean_dec_ref(v___x_56_);
v___x_58_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_57_);
v___x_59_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_58_);
v___x_60_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_59_);
v_toMul_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_toMul_61_);
lean_dec_ref(v___x_60_);
v_p_62_ = lp_PlonkLean_PlonkLean_Permutation_decompose(v_n_51_, v_i_55_);
v_fst_63_ = lean_ctor_get(v_p_62_, 0);
lean_inc(v_fst_63_);
v_snd_64_ = lean_ctor_get(v_p_62_, 1);
lean_inc(v_snd_64_);
lean_dec_ref(v_p_62_);
v___x_65_ = lp_PlonkLean_PlonkLean_Permutation_cosetRep___redArg(v_inst_50_, v_k1_53_, v_k2_54_, v_fst_63_);
lean_dec(v_fst_63_);
v___x_66_ = lp_PlonkLean_PlonkLean_EvaluationDomain_element___redArg(v_inst_50_, v_D_52_, v_snd_64_);
lean_dec_ref(v_inst_50_);
v___x_67_ = lean_apply_2(v_toMul_61_, v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_idValue___redArg___boxed(lean_object* v_inst_68_, lean_object* v_n_69_, lean_object* v_D_70_, lean_object* v_k1_71_, lean_object* v_k2_72_, lean_object* v_i_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = lp_PlonkLean_PlonkLean_Permutation_idValue___redArg(v_inst_68_, v_n_69_, v_D_70_, v_k1_71_, v_k2_72_, v_i_73_);
lean_dec(v_k2_72_);
lean_dec(v_k1_71_);
lean_dec(v_n_69_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_idValue(lean_object* v_F_75_, lean_object* v_inst_76_, lean_object* v_n_77_, lean_object* v_D_78_, lean_object* v_k1_79_, lean_object* v_k2_80_, lean_object* v_i_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lp_PlonkLean_PlonkLean_Permutation_idValue___redArg(v_inst_76_, v_n_77_, v_D_78_, v_k1_79_, v_k2_80_, v_i_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_idValue___boxed(lean_object* v_F_83_, lean_object* v_inst_84_, lean_object* v_n_85_, lean_object* v_D_86_, lean_object* v_k1_87_, lean_object* v_k2_88_, lean_object* v_i_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lp_PlonkLean_PlonkLean_Permutation_idValue(v_F_83_, v_inst_84_, v_n_85_, v_D_86_, v_k1_87_, v_k2_88_, v_i_89_);
lean_dec(v_k2_88_);
lean_dec(v_k1_87_);
lean_dec(v_n_85_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(lean_object* v_inst_91_, lean_object* v_n_92_, lean_object* v_D_93_, lean_object* v_00_u03c3_94_, lean_object* v_k1_95_, lean_object* v_k2_96_, lean_object* v_i_97_){
_start:
{
lean_object* v_toFun_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_toFun_98_ = lean_ctor_get(v_00_u03c3_94_, 0);
lean_inc(v_toFun_98_);
lean_dec_ref(v_00_u03c3_94_);
v___x_99_ = lean_apply_1(v_toFun_98_, v_i_97_);
v___x_100_ = lp_PlonkLean_PlonkLean_Permutation_idValue___redArg(v_inst_91_, v_n_92_, v_D_93_, v_k1_95_, v_k2_96_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg___boxed(lean_object* v_inst_101_, lean_object* v_n_102_, lean_object* v_D_103_, lean_object* v_00_u03c3_104_, lean_object* v_k1_105_, lean_object* v_k2_106_, lean_object* v_i_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(v_inst_101_, v_n_102_, v_D_103_, v_00_u03c3_104_, v_k1_105_, v_k2_106_, v_i_107_);
lean_dec(v_k2_106_);
lean_dec(v_k1_105_);
lean_dec(v_n_102_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_sigmaValue(lean_object* v_F_109_, lean_object* v_inst_110_, lean_object* v_n_111_, lean_object* v_D_112_, lean_object* v_00_u03c3_113_, lean_object* v_k1_114_, lean_object* v_k2_115_, lean_object* v_i_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(v_inst_110_, v_n_111_, v_D_112_, v_00_u03c3_113_, v_k1_114_, v_k2_115_, v_i_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_sigmaValue___boxed(lean_object* v_F_118_, lean_object* v_inst_119_, lean_object* v_n_120_, lean_object* v_D_121_, lean_object* v_00_u03c3_122_, lean_object* v_k1_123_, lean_object* v_k2_124_, lean_object* v_i_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue(v_F_118_, v_inst_119_, v_n_120_, v_D_121_, v_00_u03c3_122_, v_k1_123_, v_k2_124_, v_i_125_);
lean_dec(v_k2_124_);
lean_dec(v_k1_123_);
lean_dec(v_n_120_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatLeft___redArg(lean_object* v_j_127_){
_start:
{
lean_inc(v_j_127_);
return v_j_127_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatLeft___redArg___boxed(lean_object* v_j_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = lp_PlonkLean_PlonkLean_Permutation_flatLeft___redArg(v_j_128_);
lean_dec(v_j_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatLeft(lean_object* v_n_130_, lean_object* v_j_131_){
_start:
{
lean_inc(v_j_131_);
return v_j_131_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatLeft___boxed(lean_object* v_n_132_, lean_object* v_j_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = lp_PlonkLean_PlonkLean_Permutation_flatLeft(v_n_132_, v_j_133_);
lean_dec(v_j_133_);
lean_dec(v_n_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatRight(lean_object* v_n_135_, lean_object* v_j_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_nat_add(v_j_136_, v_n_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatRight___boxed(lean_object* v_n_138_, lean_object* v_j_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = lp_PlonkLean_PlonkLean_Permutation_flatRight(v_n_138_, v_j_139_);
lean_dec(v_j_139_);
lean_dec(v_n_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatOut(lean_object* v_n_141_, lean_object* v_j_142_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lean_unsigned_to_nat(2u);
v___x_144_ = lean_nat_mul(v___x_143_, v_n_141_);
v___x_145_ = lean_nat_add(v_j_142_, v___x_144_);
lean_dec(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_flatOut___boxed(lean_object* v_n_146_, lean_object* v_j_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = lp_PlonkLean_PlonkLean_Permutation_flatOut(v_n_146_, v_j_147_);
lean_dec(v_j_147_);
lean_dec(v_n_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_num___redArg(lean_object* v_inst_149_, lean_object* v_n_150_, lean_object* v_D_151_, lean_object* v_w_152_, lean_object* v_00_u03b2_153_, lean_object* v_00_u03b3_154_, lean_object* v_k1_155_, lean_object* v_k2_156_, lean_object* v_j_157_){
_start:
{
lean_object* v___x_158_; lean_object* v_toCommRing_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_toMul_163_; lean_object* v_toAdd_164_; lean_object* v_a_165_; lean_object* v_b_166_; lean_object* v_c_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_inc_ref_n(v_inst_149_, 3);
v___x_158_ = lp_mathlib_Field_toEuclideanDomain___redArg(v_inst_149_);
v_toCommRing_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_toCommRing_159_);
lean_dec_ref(v___x_158_);
v___x_160_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_159_);
v___x_161_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_160_);
v___x_162_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_161_);
v_toMul_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc_n(v_toMul_163_, 5);
v_toAdd_164_ = lean_ctor_get(v___x_162_, 1);
lean_inc_n(v_toAdd_164_, 6);
lean_dec_ref(v___x_162_);
v_a_165_ = lean_ctor_get(v_w_152_, 0);
lean_inc(v_a_165_);
v_b_166_ = lean_ctor_get(v_w_152_, 1);
lean_inc(v_b_166_);
v_c_167_ = lean_ctor_get(v_w_152_, 2);
lean_inc(v_c_167_);
lean_dec_ref(v_w_152_);
lean_inc_n(v_j_157_, 4);
v___x_168_ = lean_apply_1(v_a_165_, v_j_157_);
lean_inc_n(v_D_151_, 2);
v___x_169_ = lp_PlonkLean_PlonkLean_Permutation_idValue___redArg(v_inst_149_, v_n_150_, v_D_151_, v_k1_155_, v_k2_156_, v_j_157_);
lean_inc_n(v_00_u03b2_153_, 2);
v___x_170_ = lean_apply_2(v_toMul_163_, v_00_u03b2_153_, v___x_169_);
v___x_171_ = lean_apply_2(v_toAdd_164_, v___x_168_, v___x_170_);
lean_inc_n(v_00_u03b3_154_, 2);
v___x_172_ = lean_apply_2(v_toAdd_164_, v___x_171_, v_00_u03b3_154_);
v___x_173_ = lean_apply_1(v_b_166_, v_j_157_);
v___x_174_ = lean_nat_add(v_j_157_, v_n_150_);
v___x_175_ = lp_PlonkLean_PlonkLean_Permutation_idValue___redArg(v_inst_149_, v_n_150_, v_D_151_, v_k1_155_, v_k2_156_, v___x_174_);
v___x_176_ = lean_apply_2(v_toMul_163_, v_00_u03b2_153_, v___x_175_);
v___x_177_ = lean_apply_2(v_toAdd_164_, v___x_173_, v___x_176_);
v___x_178_ = lean_apply_2(v_toAdd_164_, v___x_177_, v_00_u03b3_154_);
v___x_179_ = lean_apply_2(v_toMul_163_, v___x_172_, v___x_178_);
v___x_180_ = lean_apply_1(v_c_167_, v_j_157_);
v___x_181_ = lp_PlonkLean_PlonkLean_Permutation_flatOut(v_n_150_, v_j_157_);
lean_dec(v_j_157_);
v___x_182_ = lp_PlonkLean_PlonkLean_Permutation_idValue___redArg(v_inst_149_, v_n_150_, v_D_151_, v_k1_155_, v_k2_156_, v___x_181_);
v___x_183_ = lean_apply_2(v_toMul_163_, v_00_u03b2_153_, v___x_182_);
v___x_184_ = lean_apply_2(v_toAdd_164_, v___x_180_, v___x_183_);
v___x_185_ = lean_apply_2(v_toAdd_164_, v___x_184_, v_00_u03b3_154_);
v___x_186_ = lean_apply_2(v_toMul_163_, v___x_179_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_num___redArg___boxed(lean_object* v_inst_187_, lean_object* v_n_188_, lean_object* v_D_189_, lean_object* v_w_190_, lean_object* v_00_u03b2_191_, lean_object* v_00_u03b3_192_, lean_object* v_k1_193_, lean_object* v_k2_194_, lean_object* v_j_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = lp_PlonkLean_PlonkLean_Permutation_num___redArg(v_inst_187_, v_n_188_, v_D_189_, v_w_190_, v_00_u03b2_191_, v_00_u03b3_192_, v_k1_193_, v_k2_194_, v_j_195_);
lean_dec(v_k2_194_);
lean_dec(v_k1_193_);
lean_dec(v_n_188_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_num(lean_object* v_F_197_, lean_object* v_inst_198_, lean_object* v_n_199_, lean_object* v_D_200_, lean_object* v_w_201_, lean_object* v_00_u03b2_202_, lean_object* v_00_u03b3_203_, lean_object* v_k1_204_, lean_object* v_k2_205_, lean_object* v_j_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lp_PlonkLean_PlonkLean_Permutation_num___redArg(v_inst_198_, v_n_199_, v_D_200_, v_w_201_, v_00_u03b2_202_, v_00_u03b3_203_, v_k1_204_, v_k2_205_, v_j_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_num___boxed(lean_object* v_F_208_, lean_object* v_inst_209_, lean_object* v_n_210_, lean_object* v_D_211_, lean_object* v_w_212_, lean_object* v_00_u03b2_213_, lean_object* v_00_u03b3_214_, lean_object* v_k1_215_, lean_object* v_k2_216_, lean_object* v_j_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = lp_PlonkLean_PlonkLean_Permutation_num(v_F_208_, v_inst_209_, v_n_210_, v_D_211_, v_w_212_, v_00_u03b2_213_, v_00_u03b3_214_, v_k1_215_, v_k2_216_, v_j_217_);
lean_dec(v_k2_216_);
lean_dec(v_k1_215_);
lean_dec(v_n_210_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_denom___redArg(lean_object* v_inst_219_, lean_object* v_n_220_, lean_object* v_D_221_, lean_object* v_00_u03c3_222_, lean_object* v_w_223_, lean_object* v_00_u03b2_224_, lean_object* v_00_u03b3_225_, lean_object* v_k1_226_, lean_object* v_k2_227_, lean_object* v_j_228_){
_start:
{
lean_object* v___x_229_; lean_object* v_toCommRing_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_toMul_234_; lean_object* v_toAdd_235_; lean_object* v_a_236_; lean_object* v_b_237_; lean_object* v_c_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
lean_inc_ref_n(v_inst_219_, 3);
v___x_229_ = lp_mathlib_Field_toEuclideanDomain___redArg(v_inst_219_);
v_toCommRing_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc_ref(v_toCommRing_230_);
lean_dec_ref(v___x_229_);
v___x_231_ = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(v_toCommRing_230_);
v___x_232_ = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(v___x_231_);
v___x_233_ = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(v___x_232_);
v_toMul_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc_n(v_toMul_234_, 5);
v_toAdd_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc_n(v_toAdd_235_, 6);
lean_dec_ref(v___x_233_);
v_a_236_ = lean_ctor_get(v_w_223_, 0);
lean_inc(v_a_236_);
v_b_237_ = lean_ctor_get(v_w_223_, 1);
lean_inc(v_b_237_);
v_c_238_ = lean_ctor_get(v_w_223_, 2);
lean_inc(v_c_238_);
lean_dec_ref(v_w_223_);
lean_inc_n(v_j_228_, 4);
v___x_239_ = lean_apply_1(v_a_236_, v_j_228_);
lean_inc_ref_n(v_00_u03c3_222_, 2);
lean_inc_n(v_D_221_, 2);
v___x_240_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(v_inst_219_, v_n_220_, v_D_221_, v_00_u03c3_222_, v_k1_226_, v_k2_227_, v_j_228_);
lean_inc_n(v_00_u03b2_224_, 2);
v___x_241_ = lean_apply_2(v_toMul_234_, v_00_u03b2_224_, v___x_240_);
v___x_242_ = lean_apply_2(v_toAdd_235_, v___x_239_, v___x_241_);
lean_inc_n(v_00_u03b3_225_, 2);
v___x_243_ = lean_apply_2(v_toAdd_235_, v___x_242_, v_00_u03b3_225_);
v___x_244_ = lean_apply_1(v_b_237_, v_j_228_);
v___x_245_ = lean_nat_add(v_j_228_, v_n_220_);
v___x_246_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(v_inst_219_, v_n_220_, v_D_221_, v_00_u03c3_222_, v_k1_226_, v_k2_227_, v___x_245_);
v___x_247_ = lean_apply_2(v_toMul_234_, v_00_u03b2_224_, v___x_246_);
v___x_248_ = lean_apply_2(v_toAdd_235_, v___x_244_, v___x_247_);
v___x_249_ = lean_apply_2(v_toAdd_235_, v___x_248_, v_00_u03b3_225_);
v___x_250_ = lean_apply_2(v_toMul_234_, v___x_243_, v___x_249_);
v___x_251_ = lean_apply_1(v_c_238_, v_j_228_);
v___x_252_ = lp_PlonkLean_PlonkLean_Permutation_flatOut(v_n_220_, v_j_228_);
lean_dec(v_j_228_);
v___x_253_ = lp_PlonkLean_PlonkLean_Permutation_sigmaValue___redArg(v_inst_219_, v_n_220_, v_D_221_, v_00_u03c3_222_, v_k1_226_, v_k2_227_, v___x_252_);
v___x_254_ = lean_apply_2(v_toMul_234_, v_00_u03b2_224_, v___x_253_);
v___x_255_ = lean_apply_2(v_toAdd_235_, v___x_251_, v___x_254_);
v___x_256_ = lean_apply_2(v_toAdd_235_, v___x_255_, v_00_u03b3_225_);
v___x_257_ = lean_apply_2(v_toMul_234_, v___x_250_, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_denom___redArg___boxed(lean_object* v_inst_258_, lean_object* v_n_259_, lean_object* v_D_260_, lean_object* v_00_u03c3_261_, lean_object* v_w_262_, lean_object* v_00_u03b2_263_, lean_object* v_00_u03b3_264_, lean_object* v_k1_265_, lean_object* v_k2_266_, lean_object* v_j_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = lp_PlonkLean_PlonkLean_Permutation_denom___redArg(v_inst_258_, v_n_259_, v_D_260_, v_00_u03c3_261_, v_w_262_, v_00_u03b2_263_, v_00_u03b3_264_, v_k1_265_, v_k2_266_, v_j_267_);
lean_dec(v_k2_266_);
lean_dec(v_k1_265_);
lean_dec(v_n_259_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_denom(lean_object* v_F_269_, lean_object* v_inst_270_, lean_object* v_n_271_, lean_object* v_D_272_, lean_object* v_00_u03c3_273_, lean_object* v_w_274_, lean_object* v_00_u03b2_275_, lean_object* v_00_u03b3_276_, lean_object* v_k1_277_, lean_object* v_k2_278_, lean_object* v_j_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lp_PlonkLean_PlonkLean_Permutation_denom___redArg(v_inst_270_, v_n_271_, v_D_272_, v_00_u03c3_273_, v_w_274_, v_00_u03b2_275_, v_00_u03b3_276_, v_k1_277_, v_k2_278_, v_j_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* lp_PlonkLean_PlonkLean_Permutation_denom___boxed(lean_object* v_F_281_, lean_object* v_inst_282_, lean_object* v_n_283_, lean_object* v_D_284_, lean_object* v_00_u03c3_285_, lean_object* v_w_286_, lean_object* v_00_u03b2_287_, lean_object* v_00_u03b3_288_, lean_object* v_k1_289_, lean_object* v_k2_290_, lean_object* v_j_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = lp_PlonkLean_PlonkLean_Permutation_denom(v_F_281_, v_inst_282_, v_n_283_, v_D_284_, v_00_u03c3_285_, v_w_286_, v_00_u03b2_287_, v_00_u03b3_288_, v_k1_289_, v_k2_290_, v_j_291_);
lean_dec(v_k2_290_);
lean_dec(v_k1_289_);
lean_dec(v_n_283_);
return v_res_292_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Permutation_Sigma(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Polynomial_Lagrange(uint8_t builtin);
lean_object* initialize_PlonkLean_PlonkLean_Polynomial_Vanishing(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_PlonkLean_PlonkLean_Permutation_GrandProduct(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Permutation_Sigma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Polynomial_Lagrange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_PlonkLean_PlonkLean_Polynomial_Vanishing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Group_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
