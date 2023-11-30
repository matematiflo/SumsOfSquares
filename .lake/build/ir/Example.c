// Lean compiler output
// Module: Example
// Imports: Init SumSq
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
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_SumSqAux___at_main___spec__5___boxed(lean_object*, lean_object*);
static lean_object* l_List_toString___at_main___spec__2___closed__1;
static lean_object* l_List_toString___at_main___spec__2___closed__2;
LEAN_EXPORT lean_object* l_SumSqAux___at_main___spec__5(lean_object*, lean_object*);
lean_object* l_String_trim(lean_object*);
static lean_object* l_main___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at_main___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
static lean_object* l_main___closed__1;
static lean_object* l_main___closed__5;
static lean_object* l_main___closed__4;
LEAN_EXPORT lean_object* l_List_toString___at_main___spec__2(lean_object*);
lean_object* lean_get_stdin(lean_object*);
static lean_object* l_List_foldl___at_main___spec__3___closed__1;
static lean_object* l_List_toString___at_main___spec__2___closed__3;
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SumSqTR___at_main___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_main___spec__1(lean_object*, lean_object*);
lean_object* l_String_toInt_x21(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_List_foldl___at_main___spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at_main___spec__3(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
static lean_object* l_main___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_List_foldl___at_main___spec__3___closed__2;
LEAN_EXPORT lean_object* l_List_toString___at_main___spec__2___boxed(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_String_trim(x_5);
lean_dec(x_5);
x_8 = l_String_toInt_x21(x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_String_trim(x_10);
lean_dec(x_10);
x_13 = l_String_toInt_x21(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l_List_foldl___at_main___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_main___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_main___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldl___at_main___spec__3___closed__1;
x_6 = lean_string_append(x_1, x_5);
x_7 = l_List_foldl___at_main___spec__3___closed__2;
x_8 = lean_int_dec_lt(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_nat_abs(x_3);
x_10 = l_Nat_repr(x_9);
x_11 = lean_string_append(x_6, x_10);
lean_dec(x_10);
x_1 = x_11;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_nat_abs(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_add(x_15, x_14);
lean_dec(x_15);
x_17 = l_Nat_repr(x_16);
x_18 = l_List_foldl___at_main___spec__3___closed__3;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_string_append(x_6, x_19);
lean_dec(x_19);
x_1 = x_20;
x_2 = x_4;
goto _start;
}
}
}
}
static lean_object* _init_l_List_toString___at_main___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[]", 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_main___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_main___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_main___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_main___spec__2___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_List_foldl___at_main___spec__3___closed__2;
x_6 = lean_int_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_nat_abs(x_4);
x_8 = l_Nat_repr(x_7);
x_9 = l_List_toString___at_main___spec__2___closed__2;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_List_toString___at_main___spec__2___closed__3;
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_nat_abs(x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_add(x_15, x_14);
lean_dec(x_15);
x_17 = l_Nat_repr(x_16);
x_18 = l_List_foldl___at_main___spec__3___closed__3;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_List_toString___at_main___spec__2___closed__2;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_List_toString___at_main___spec__2___closed__3;
x_23 = lean_string_append(x_21, x_22);
return x_23;
}
}
else
{
lean_object* x_24; uint32_t x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = 93;
x_26 = l_List_foldl___at_main___spec__3___closed__2;
x_27 = lean_int_dec_lt(x_24, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_nat_abs(x_24);
x_29 = l_Nat_repr(x_28);
x_30 = l_List_toString___at_main___spec__2___closed__2;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = l_List_foldl___at_main___spec__3(x_31, x_3);
x_33 = lean_string_push(x_32, x_25);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_nat_abs(x_24);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_sub(x_34, x_35);
lean_dec(x_34);
x_37 = lean_nat_add(x_36, x_35);
lean_dec(x_36);
x_38 = l_Nat_repr(x_37);
x_39 = l_List_foldl___at_main___spec__3___closed__3;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_List_toString___at_main___spec__2___closed__2;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_List_foldl___at_main___spec__3(x_42, x_3);
x_44 = lean_string_push(x_43, x_25);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_SumSqAux___at_main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Int_pow(x_3, x_5);
x_7 = lean_int_add(x_1, x_6);
lean_dec(x_6);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_SumSqTR___at_main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_List_foldl___at_main___spec__3___closed__2;
x_3 = l_SumSqAux___at_main___spec__5(x_2, x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Please enter a list of integers in the form 1, -2, 3 (as many integers as you want, seperated by a comma).", 106);
return x_1;
}
}
static lean_object* _init_l_main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("The list you entered is ", 24);
return x_1;
}
}
static lean_object* _init_l_main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(". Its sum of squares is ", 24);
return x_1;
}
}
static lean_object* _init_l_main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_get_stdin(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_get_stdout(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_main___closed__1;
lean_inc(x_6);
x_9 = l_IO_FS_Stream_putStrLn(x_6, x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_apply_1(x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_main___closed__2;
x_16 = l_String_splitOn(x_13, x_15);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at_main___spec__1(x_16, x_17);
x_19 = l_List_toString___at_main___spec__2(x_18);
x_20 = l_main___closed__3;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_main___closed__4;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_SumSqTR___at_main___spec__4(x_18);
x_25 = l_List_foldl___at_main___spec__3___closed__2;
x_26 = lean_int_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_nat_abs(x_24);
lean_dec(x_24);
x_28 = l_Nat_repr(x_27);
x_29 = lean_string_append(x_23, x_28);
lean_dec(x_28);
x_30 = l_main___closed__5;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_IO_FS_Stream_putStrLn(x_6, x_31, x_14);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_nat_abs(x_24);
lean_dec(x_24);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_33, x_34);
lean_dec(x_33);
x_36 = lean_nat_add(x_35, x_34);
lean_dec(x_35);
x_37 = l_Nat_repr(x_36);
x_38 = l_List_foldl___at_main___spec__3___closed__3;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = lean_string_append(x_23, x_39);
lean_dec(x_39);
x_41 = l_main___closed__5;
x_42 = lean_string_append(x_40, x_41);
x_43 = l_IO_FS_Stream_putStrLn(x_6, x_42, x_14);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
return x_12;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
return x_9;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_9, 0);
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_9);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_main___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_main___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_main___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at_main___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_SumSqAux___at_main___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_SumSqAux___at_main___spec__5(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_SumSq(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Example(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SumSq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_foldl___at_main___spec__3___closed__1 = _init_l_List_foldl___at_main___spec__3___closed__1();
lean_mark_persistent(l_List_foldl___at_main___spec__3___closed__1);
l_List_foldl___at_main___spec__3___closed__2 = _init_l_List_foldl___at_main___spec__3___closed__2();
lean_mark_persistent(l_List_foldl___at_main___spec__3___closed__2);
l_List_foldl___at_main___spec__3___closed__3 = _init_l_List_foldl___at_main___spec__3___closed__3();
lean_mark_persistent(l_List_foldl___at_main___spec__3___closed__3);
l_List_toString___at_main___spec__2___closed__1 = _init_l_List_toString___at_main___spec__2___closed__1();
lean_mark_persistent(l_List_toString___at_main___spec__2___closed__1);
l_List_toString___at_main___spec__2___closed__2 = _init_l_List_toString___at_main___spec__2___closed__2();
lean_mark_persistent(l_List_toString___at_main___spec__2___closed__2);
l_List_toString___at_main___spec__2___closed__3 = _init_l_List_toString___at_main___spec__2___closed__3();
lean_mark_persistent(l_List_toString___at_main___spec__2___closed__3);
l_main___closed__1 = _init_l_main___closed__1();
lean_mark_persistent(l_main___closed__1);
l_main___closed__2 = _init_l_main___closed__2();
lean_mark_persistent(l_main___closed__2);
l_main___closed__3 = _init_l_main___closed__3();
lean_mark_persistent(l_main___closed__3);
l_main___closed__4 = _init_l_main___closed__4();
lean_mark_persistent(l_main___closed__4);
l_main___closed__5 = _init_l_main___closed__5();
lean_mark_persistent(l_main___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
void lean_initialize();

  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  #endif
  lean_object* in; lean_object* res;
lean_initialize();
lean_set_panic_messages(false);
res = initialize_Example(1 /* builtin */, lean_io_mk_world());
lean_set_panic_messages(true);
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
res = _lean_main(lean_io_mk_world());
}
lean_finalize_task_manager();
if (lean_io_result_is_ok(res)) {
  int ret = 0;
  lean_dec_ref(res);
  return ret;
} else {
  lean_io_result_show_error(res);
  lean_dec_ref(res);
  return 1;
}
}
#ifdef __cplusplus
}
#endif
