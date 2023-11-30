// Lean compiler output
// Module: SumSq.Basic
// Imports: Init SumSq.Defs Mathlib.Algebra.GroupPower.Basic
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
static lean_object* l_instReprSumSqType___rarg___closed__2;
LEAN_EXPORT lean_object* l_instAddSumSqType__1(lean_object*);
static lean_object* l_instReprSumSqType___rarg___closed__4;
static lean_object* l_aTermOfSumSqTypeInZ___closed__1;
LEAN_EXPORT lean_object* l_Double(lean_object*);
LEAN_EXPORT lean_object* l___private_SumSq_Basic_0__SumSq_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAddSumSqType__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_NonUnitalNonAssocSemiring_toDistrib___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instReprSumSqType___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableIsSumSqOfNatToOfNat0ToZeroToMonoidWithZero___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAddSumSqType__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Double___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Semiring_toNonAssocSemiring___rarg(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableIsSumSqOfNatToOfNat0ToZeroToMonoidWithZero(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSumSqType(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Addition___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Double___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SumSqTypeAddition___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_SumSq_Basic_0__SumSq_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Addition___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_instReprSumSqType___rarg___closed__1;
LEAN_EXPORT lean_object* l_SumSqTypeAddition___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAddSumSqType(lean_object*);
LEAN_EXPORT lean_object* l_instAddSumSqType___rarg(lean_object*);
LEAN_EXPORT lean_object* l_aTermOfSumSqTypeInZ;
static lean_object* l_instReprSumSqType___rarg___closed__3;
LEAN_EXPORT lean_object* l_instReprSumSqType___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSumSqType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Addition(lean_object*);
LEAN_EXPORT lean_object* l_SumSqTypeAddition(lean_object*);
LEAN_EXPORT lean_object* l___private_SumSq_Basic_0__SumSq_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_SumSq_Basic_0__SumSq_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_SumSq_Basic_0__SumSq_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_SumSq_Basic_0__SumSq_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_SumSq_Basic_0__SumSq_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_SumSq_Basic_0__SumSq_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Addition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Semiring_toNonAssocSemiring___rarg(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_NonUnitalNonAssocSemiring_toDistrib___rarg(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Addition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Addition___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Addition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Addition___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instAddSumSqType___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Addition___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instAddSumSqType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instAddSumSqType___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Double___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_Addition___rarg(x_1, x_2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Double(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Double___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Double___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Double___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instAddSumSqType__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Semiring_toNonAssocSemiring___rarg(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_NonUnitalNonAssocSemiring_toDistrib___rarg(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_instAddSumSqType__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_instAddSumSqType__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instAddSumSqType__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instAddSumSqType__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_SumSqTypeAddition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Semiring_toNonAssocSemiring___rarg(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_NonUnitalNonAssocSemiring_toDistrib___rarg(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_SumSqTypeAddition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_SumSqTypeAddition___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_SumSqTypeAddition___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_SumSqTypeAddition___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_instReprSumSqType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" is a sum of squares because the property IsSumSq ", 50);
return x_1;
}
}
static lean_object* _init_l_instReprSumSqType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprSumSqType___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_instReprSumSqType___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" has been proven.", 17);
return x_1;
}
}
static lean_object* _init_l_instReprSumSqType___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instReprSumSqType___rarg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instReprSumSqType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_apply_2(x_1, x_2, x_4);
x_6 = l_instReprSumSqType___rarg___closed__2;
lean_inc(x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
x_9 = l_instReprSumSqType___rarg___closed__4;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_instReprSumSqType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_instReprSumSqType___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprSumSqType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_instReprSumSqType___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instReprSumSqType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instReprSumSqType(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_aTermOfSumSqTypeInZ___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_aTermOfSumSqTypeInZ() {
_start:
{
lean_object* x_1; 
x_1 = l_aTermOfSumSqTypeInZ___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_instDecidableIsSumSqOfNatToOfNat0ToZeroToMonoidWithZero(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableIsSumSqOfNatToOfNat0ToZeroToMonoidWithZero___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instDecidableIsSumSqOfNatToOfNat0ToZeroToMonoidWithZero(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_SumSq_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_GroupPower_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SumSq_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SumSq_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_GroupPower_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instReprSumSqType___rarg___closed__1 = _init_l_instReprSumSqType___rarg___closed__1();
lean_mark_persistent(l_instReprSumSqType___rarg___closed__1);
l_instReprSumSqType___rarg___closed__2 = _init_l_instReprSumSqType___rarg___closed__2();
lean_mark_persistent(l_instReprSumSqType___rarg___closed__2);
l_instReprSumSqType___rarg___closed__3 = _init_l_instReprSumSqType___rarg___closed__3();
lean_mark_persistent(l_instReprSumSqType___rarg___closed__3);
l_instReprSumSqType___rarg___closed__4 = _init_l_instReprSumSqType___rarg___closed__4();
lean_mark_persistent(l_instReprSumSqType___rarg___closed__4);
l_aTermOfSumSqTypeInZ___closed__1 = _init_l_aTermOfSumSqTypeInZ___closed__1();
lean_mark_persistent(l_aTermOfSumSqTypeInZ___closed__1);
l_aTermOfSumSqTypeInZ = _init_l_aTermOfSumSqTypeInZ();
lean_mark_persistent(l_aTermOfSumSqTypeInZ);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
