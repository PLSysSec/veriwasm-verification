(*

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 
 *)


val linenum = ref 0

datatype B_binary_operators = 
      B_And
     | B_Or
     | B_Eq 
     | B_Xor
     | B_Iff
     | B_Implies


datatype BV_ternary_operators = 
BV_Vfmsub132_Single | (* (32bit,32bit,32bit) \<rightarrow> 32bit *)
BV_Vfmadd132_Single |(* (32bit,32bit,32bit) \<rightarrow> 32bit *)
BV_Vfnmadd132_Single |  (* (32bit,32bit,32bit) \<rightarrow> 32bit *)
BV_Vfnmsub132_Single | (* (32bit,32bit,32bit) \<rightarrow> 32bit *)
BV_Vfnmadd132_Double | (* (64bit,64bit,64bit) \<rightarrow> 64bit *)
BV_Vnfmsub132_Double | (* (64bit,64bit,64bit) \<rightarrow> 64bit *)
BV_Vfmsub132_Double | (* (64bit,64bit,64bit) \<rightarrow> 64bit *)
BV_Vfmadd132_Double  (* (64bit,64bit,64bit) \<rightarrow> 64bit *)

datatype BV_binary_operators =
(* Standard Binary Ops (Xbit,Xbit)\<rightarrow>Xbit*) 
BV_And | BV_Concat | BV_Div | BV_Minus | BV_Modulus  | BV_Mult | BV_Or | BV_Plus |
BV_Rot_Left | BV_Rot_Right | BV_Shift_Left | BV_Shift_Right | BV_Signed_Div | BV_Signed_Mod |
BV_Sign_Shift_Right | BV_Xor |

(* (32bit,32bit)\<rightarrow>32bit*)
BV_Add_Single | BV_Sub_Single | BV_Div_Single | BV_Mul_Single |

(* (64bit,64bit)\<rightarrow>64bit*)
BV_Add_Double | BV_Sub_Double | BV_Div_Double | BV_Mul_Double |

(* (32bit,32bit)\<rightarrow>2bit*)
BV_Cmpf | BV_Cmpd |

(* (32bit,32bit)\<rightarrow>1bit*)
 BV_Maxcmp_Single | BV_Mincmp_Single |

(* (64bit,64bit)\<rightarrow>1bit*)
BV_Maxcmp_Double |  BV_Mincmp_Double |   

(* (16bit,8bit)\<rightarrow>8bit*)
BV_Idiv_Quotient_Int8 | BV_Idiv_Remainder_Int8 | BV_Div_Quotient_Int8 | BV_Div_Remainder_Int8 |

(* (32bit,16bit)\<rightarrow>16bit*)
BV_Idiv_Quotient_Int16 | BV_Idiv_Remainder_Int16 | BV_Div_Quotient_Int16 | BV_Div_Remainder_Int16 |

(* (64bit,32bit)\<rightarrow>32bit*)
BV_Idiv_Quotient_Int32 | BV_Idiv_Remainder_Int32 | BV_Div_Quotient_Int32 | BV_Div_Remainder_Int32 |

(* (128bit,64bit)\<rightarrow>64bit*)
BV_Idiv_Quotient_Int64 | BV_Idiv_Remainder_Int64 | BV_Div_Quotient_Int64 | BV_Div_Remainder_Int64

datatype BV_unary_operators =
      BV_SExtend16 
    | BV_SExtend32 
    | BV_SExtend64 
    | BV_SExtend128
    | BV_SExtend256
    | BV_Not
    | BV_Neg
    | BV_Cvt_Int32_To_Double (* 32 \<rightarrow> 64 bit*)
    | BV_Cvt_Single_To_Double (* 32 \<rightarrow> 64 bit*)
    | BV_Cvt_Double_To_Int64 (*64 \<rightarrow> 64 bit *) 
    | BV_Cvt_Single_To_Int64 (* 32 \<rightarrow> 64 bit*)
    | BV_Cvt_Double_To_Int64_Truncate  (*64 \<rightarrow> 64 bit *) 
    | BV_Cvt_Single_To_Int64_Truncate (* 32 \<rightarrow> 64 bit*)
    | BV_Cvt_Int32_To_Single (* 32 \<rightarrow> 32 bit*)
    | BV_Cvt_Double_To_Int32  (*64 \<rightarrow> 32 bit*)
    | BV_Cvt_Double_To_Single (*64 \<rightarrow> 32 bit*)
    | BV_Cvt_Single_To_Int32 (* 32 \<rightarrow> 32 bit*)
    | BV_Cvt_Int64_To_Double (*64 \<rightarrow> 64 bit *)
    | BV_Cvt_Int64_To_Single  (*64 \<rightarrow> 32 bit*)
    | BV_Cvt_Double_To_Int32_Truncate (*64 \<rightarrow> 32 bit*)
    | BV_Cvt_Single_To_Int32_Truncate (* 32 \<rightarrow> 32 bit*)
    | BV_Approx_Reciprocal_Single (* 32 \<rightarrow> 32 bit*)
    | BV_Approx_Reciprocal_Sqrt_Single (* 32 \<rightarrow> 32 bit*)
    | BV_Sqrt_Single (* 32 \<rightarrow> 32 bit*)
    | BV_Sqrt_Double  (*64 \<rightarrow> 64 bit *)


datatype BV_var =
   BV_Operand1  
 | BV_Operand2 
 | BV_Operand3 (* Resolves to operand X. This is the "parameterization aspect to these formulas.
                                              General registers this can be read or written too. For SSE Registers only read from. *)
 |  BV_Var_Direct of string (* Some instructions directly read write to specific generic 64-bit registers *)


datatype bitvector_formula  = 
     BV_Assignment of (BV_var*bitvector_formula) (* assignment *)
  |  BV_Flag_Assignment of (flag*bitvector_formula) (* flag assignment *)
  |  BV_Immediate of (int * int) (* value, number_of_bits *)
  |  BV_Get of BV_var
  |  BV_Slice of (bitvector_formula * int * int) (* end_bit, start_bit IE: 15 0 being the first two bytes *)
  |  BV_Unop of (BV_unary_operators * bitvector_formula )
  |  BV_Binop of (BV_binary_operators * bitvector_formula * bitvector_formula)
  |  BV_Ternop of (BV_ternary_operators * bitvector_formula * bitvector_formula* bitvector_formula)
  |  BV_ITE of (bitvector_formula * bitvector_formula * bitvector_formula)
  |  B_Binop of (B_binary_operators * bitvector_formula * bitvector_formula)
  | B_Get of flag
  | B_True | B_False
  |  BV_Undefined

fun mk_bvvar (BV_Operand1) = @{term "BV_Operand1"}
| mk_bvvar (BV_Operand2) = @{term "BV_Operand2"} 
| mk_bvvar (BV_Operand3) = @{term "BV_Operand3"} 
| mk_bvvar (BV_Var_Direct s) = @{term "BV_Var_Direct"} $ mk_register_mnemonic s

fun mk_bvunop (BV_SExtend16) = @{term "BV_SExtend16"} 
    | mk_bvunop(BV_SExtend32) = @{term "BV_SExtend32"} 
    | mk_bvunop(BV_SExtend64) = @{term "BV_SExtend64"} 
    | mk_bvunop(BV_SExtend128) = @{term "BV_SExtend128"} 
    | mk_bvunop(BV_SExtend256) = @{term "BV_SExtend256"} 
    | mk_bvunop(BV_Not) = @{term "BV_Not"}
    | mk_bvunop(BV_Neg) = @{term "BV_Neg"}
    | mk_bvunop(BV_Cvt_Int32_To_Double) = @{term "BV_Cvt_Int32_To_Double"} (* 32 \<rightarrow> 64 bit*)
    | mk_bvunop(BV_Cvt_Single_To_Double) = @{term "BV_Cvt_Single_To_Double"} (* 32 \<rightarrow> 64 bit*)
    | mk_bvunop(BV_Cvt_Double_To_Int64) = @{term "BV_Cvt_Double_To_Int64"} (*64 \<rightarrow> 64 bit *) 
    | mk_bvunop(BV_Cvt_Single_To_Int64) = @{term "BV_Cvt_Single_To_Int64"} (* 32 \<rightarrow> 64 bit*)
    | mk_bvunop(BV_Cvt_Double_To_Int64_Truncate) = @{term "BV_Cvt_Double_To_Int64_Truncate"}  (*64 \<rightarrow> 64 bit *) 
    | mk_bvunop(BV_Cvt_Single_To_Int64_Truncate) = @{term "BV_Cvt_Single_To_Int64_Truncate"} (* 32 \<rightarrow> 64 bit*)
    | mk_bvunop(BV_Cvt_Int32_To_Single) = @{term "BV_Cvt_Int32_To_Single"} (* 32 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Cvt_Double_To_Int32) = @{term "BV_Cvt_Double_To_Int32"}  (*64 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Cvt_Double_To_Single) = @{term "BV_Cvt_Double_To_Single"} (*64 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Cvt_Single_To_Int32) = @{term "BV_Cvt_Single_To_Int32"} (* 32 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Cvt_Int64_To_Double) = @{term "BV_Cvt_Int64_To_Double"} (*64 \<rightarrow> 64 bit *)
    | mk_bvunop(BV_Cvt_Int64_To_Single) = @{term "BV_Cvt_Int64_To_Single"}  (*64 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Cvt_Double_To_Int32_Truncate) = @{term "BV_Cvt_Double_To_Int32_Truncate"} (*64 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Cvt_Single_To_Int32_Truncate) = @{term "BV_Cvt_Single_To_Int32_Truncate"} (* 32 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Approx_Reciprocal_Single) = @{term "BV_Approx_Reciprocal_Single"} (* 32 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Approx_Reciprocal_Sqrt_Single) = @{term "BV_Approx_Reciprocal_Sqrt_Single"} (* 32 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Sqrt_Single) = @{term "BV_Sqrt_Single"} (* 32 \<rightarrow> 32 bit*)
    | mk_bvunop(BV_Sqrt_Double) = @{term "BV_Sqrt_Double"}  (*64 \<rightarrow> 64 bit *)

fun mk_bvbinop(BV_And) = @{term "BV_And"} | mk_bvbinop(BV_Concat) = @{term "BV_Concat"} 
| mk_bvbinop(BV_Div) = @{term "BV_Div"} | mk_bvbinop(BV_Minus) = @{term "BV_Minus"} 
| mk_bvbinop(BV_Modulus) = @{term "BV_Modulus"}  | mk_bvbinop(BV_Mult) = @{term "BV_Mult"} 
| mk_bvbinop(BV_Or) = @{term "BV_Or"} | mk_bvbinop(BV_Plus) = @{term "BV_Plus"} 
| mk_bvbinop(BV_Rot_Left) = @{term "BV_Rot_Left"} | mk_bvbinop(BV_Rot_Right) = @{term "BV_Rot_Right"} 
| mk_bvbinop(BV_Shift_Left) = @{term "BV_Shift_Left"} | mk_bvbinop(BV_Shift_Right) = @{term "BV_Shift_Right"} 
| mk_bvbinop(BV_Signed_Div) = @{term "BV_Signed_Div"} | mk_bvbinop(BV_Signed_Mod) = @{term "BV_Signed_Mod"} 
| mk_bvbinop(BV_Sign_Shift_Right) = @{term "BV_Sign_Shift_Right"} | mk_bvbinop(BV_Xor) = @{term "BV_Xor"} 
| mk_bvbinop(BV_Add_Single) = @{term "BV_Add_Single"} | mk_bvbinop(BV_Sub_Single) = @{term "BV_Sub_Single"} 
| mk_bvbinop(BV_Div_Single) = @{term "BV_Div_Single"} | mk_bvbinop(BV_Mul_Single) = @{term "BV_Mul_Single"} 
| mk_bvbinop(BV_Add_Double) = @{term "BV_Add_Double"} | mk_bvbinop(BV_Sub_Double) = @{term "BV_Sub_Double"} 
| mk_bvbinop(BV_Div_Double) = @{term "BV_Div_Double"} | mk_bvbinop(BV_Mul_Double) = @{term "BV_Mul_Double"} 
| mk_bvbinop(BV_Cmpf) = @{term "BV_Cmpf"} | mk_bvbinop(BV_Cmpd) = @{term "BV_Cmpd"} 
| mk_bvbinop(BV_Maxcmp_Single) = @{term "BV_Maxcmp_Single"} | mk_bvbinop(BV_Mincmp_Single) = @{term "BV_Mincmp_Single"} 
| mk_bvbinop(BV_Maxcmp_Double) = @{term "BV_Maxcmp_Double"} |  mk_bvbinop(BV_Mincmp_Double) = @{term "BV_Mincmp_Double"} 
| mk_bvbinop(BV_Idiv_Quotient_Int8) = @{term "BV_Idiv_Quotient_Int8"} | mk_bvbinop(BV_Idiv_Remainder_Int8) = @{term "BV_Idiv_Remainder_Int8"} 
| mk_bvbinop(BV_Div_Quotient_Int8) = @{term "BV_Div_Quotient_Int8"} | mk_bvbinop(BV_Div_Remainder_Int8) = @{term "BV_Div_Remainder_Int8"} 
| mk_bvbinop(BV_Idiv_Quotient_Int16) = @{term "BV_Idiv_Quotient_Int16"} | mk_bvbinop(BV_Idiv_Remainder_Int16) = @{term "BV_Idiv_Remainder_Int16"} 
| mk_bvbinop(BV_Div_Quotient_Int16) = @{term "BV_Div_Quotient_Int16"} | mk_bvbinop(BV_Div_Remainder_Int16) = @{term "BV_Div_Remainder_Int16"} 
| mk_bvbinop(BV_Idiv_Quotient_Int32) = @{term "BV_Idiv_Quotient_Int32"} | mk_bvbinop(BV_Idiv_Remainder_Int32) = @{term "BV_Idiv_Remainder_Int32"} 
| mk_bvbinop(BV_Div_Quotient_Int32) = @{term "BV_Div_Quotient_Int32"} | mk_bvbinop(BV_Div_Remainder_Int32) = @{term "BV_Div_Remainder_Int32"} 
| mk_bvbinop(BV_Idiv_Quotient_Int64) = @{term "BV_Idiv_Quotient_Int64"} | mk_bvbinop(BV_Idiv_Remainder_Int64) = @{term "BV_Idiv_Remainder_Int64"} 
| mk_bvbinop(BV_Div_Quotient_Int64) = @{term "BV_Div_Quotient_Int64"} | mk_bvbinop(BV_Div_Remainder_Int64) = @{term "BV_Div_Remainder_Int64"}

fun mk_bvternop(BV_Vfmsub132_Single) = @{term "BV_Vfmsub132_Single"} | mk_bvternop(BV_Vfmadd132_Single) = @{term "BV_Vfmadd132_Single"} 
|mk_bvternop(BV_Vfnmadd132_Single) = @{term "BV_Vfnmadd132_Single"} | mk_bvternop(BV_Vfnmsub132_Single) = @{term "BV_Vfnmsub132_Single"} 
| mk_bvternop(BV_Vfnmadd132_Double) = @{term "BV_Vfnmadd132_Double"} | mk_bvternop(BV_Vnfmsub132_Double) = @{term "BV_Vnfmsub132_Double"} 
| mk_bvternop(BV_Vfmsub132_Double) = @{term "BV_Vfmsub132_Double"} | mk_bvternop(BV_Vfmadd132_Double) = @{term "BV_Vfmadd132_Double"} 

fun mk_bbinop(B_And) = @{term "B_And"} | mk_bbinop(B_Or) = @{term "B_Or"} 
| mk_bbinop(B_Eq) = @{term "B_Eq"} | mk_bbinop(B_Xor) = @{term "B_Xor"} 
| mk_bbinop(B_Iff) = @{term "B_Iff"}  | mk_bbinop(B_Implies) = @{term "B_Implies"} 


fun mk_bvf (BV_Assignment (v,bvf)) = @{term "BV_Assignment"} $ mk_bvvar v $ mk_bvf bvf
| mk_bvf (BV_Flag_Assignment (fv,bvf)) = @{term "BV_Flag_Assignment"} $ mk_flg fv $ mk_bvf bvf
| mk_bvf (BV_Immediate (v,size)) = @{term "BV_Immediate"} $ mk_int v $ mk_nat size
| mk_bvf (BV_Get g) = @{term "BV_Get"} $ mk_bvvar g
| mk_bvf (BV_Slice (bv,e,s)) = @{term "BV_Slice"} $ mk_bvf bv $ mk_nat e $ mk_nat s
| mk_bvf (BV_Unop (u,bv1)) = @{term "BV_Unop"} $ mk_bvunop u $ mk_bvf bv1 
| mk_bvf (BV_Binop (u,bv1,bv2)) = @{term "BV_Binop"} $ mk_bvbinop u $ mk_bvf bv1 $ mk_bvf bv2
| mk_bvf (BV_Ternop (u,bv1,bv2,bv3)) = @{term "BV_Ternop"} $ mk_bvternop u $ mk_bvf bv1 $ mk_bvf bv2 $ mk_bvf bv3
| mk_bvf (BV_ITE (bf,bv0,bv1)) = @{term "BV_ITE"} $ mk_bvf bf $ mk_bvf bv0 $ mk_bvf bv1
| mk_bvf (B_Binop (u,bv0,bv1)) = @{term "B_Binop"} $ mk_bbinop u $ mk_bvf bv0 $ mk_bvf bv1
| mk_bvf (B_Get f) = @{term "B_Get"} $ mk_flg f
| mk_bvf (B_True) = @{term "B_True"} | mk_bvf (B_False) = @{term "B_False"}
| mk_bvf (BV_Undefined) = @{term "BV_Undefined"} 

(* fun mk_bvf_option (bv) = @{term "Some"} $ mk_bvf(bv) *)

fun mk_bvfs bvfs =  mk_list @{typ "bitvector_formula"} (map mk_bvf bvfs);

fun toString_bvvar (BV_Operand1) = "BV_Operand1"
| toString_bvvar (BV_Operand2) = "BV_Operand2"
| toString_bvvar (BV_Operand3) = "BV_Operand3"
| toString_bvvar (BV_Var_Direct s) = "(BV_Var_Direct " ^ s ^ ")"

fun toString_bvunop (BV_SExtend16) = "BV_SExtend16"
    | toString_bvunop(BV_SExtend32) = "BV_SExtend32"
    | toString_bvunop(BV_SExtend64) = "BV_SExtend64"
    | toString_bvunop(BV_SExtend128) = "BV_SExtend128"
    | toString_bvunop(BV_SExtend256) = "BV_SExtend256"
    | toString_bvunop(BV_Not) = "BV_Not"
    | toString_bvunop(BV_Neg) = "BV_Neg"
    | toString_bvunop(BV_Cvt_Int32_To_Double) = "BV_Cvt_Int32_To_Double"
    | toString_bvunop(BV_Cvt_Single_To_Double) = "BV_Cvt_Single_To_Double"
    | toString_bvunop(BV_Cvt_Double_To_Int64) = "BV_Cvt_Double_To_Int64"
    | toString_bvunop(BV_Cvt_Single_To_Int64) = "BV_Cvt_Single_To_Int64"
    | toString_bvunop(BV_Cvt_Double_To_Int64_Truncate) = "BV_Cvt_Double_To_Int64_Truncate"
    | toString_bvunop(BV_Cvt_Single_To_Int64_Truncate) = "BV_Cvt_Single_To_Int64_Truncate"
    | toString_bvunop(BV_Cvt_Int32_To_Single) = "BV_Cvt_Int32_To_Single"
    | toString_bvunop(BV_Cvt_Double_To_Int32) = "BV_Cvt_Double_To_Int32"
    | toString_bvunop(BV_Cvt_Double_To_Single) = "BV_Cvt_Double_To_Single"
    | toString_bvunop(BV_Cvt_Single_To_Int32) = "BV_Cvt_Single_To_Int32"
    | toString_bvunop(BV_Cvt_Int64_To_Double) = "BV_Cvt_Int64_To_Double"
    | toString_bvunop(BV_Cvt_Int64_To_Single) = "BV_Cvt_Int64_To_Single"
    | toString_bvunop(BV_Cvt_Double_To_Int32_Truncate) = "BV_Cvt_Double_To_Int32_Truncate"
    | toString_bvunop(BV_Cvt_Single_To_Int32_Truncate) = "BV_Cvt_Single_To_Int32_Truncate"
    | toString_bvunop(BV_Approx_Reciprocal_Single) = "BV_Approx_Reciprocal_Single"
    | toString_bvunop(BV_Approx_Reciprocal_Sqrt_Single) = "BV_Approx_Reciprocal_Sqrt_Single"
    | toString_bvunop(BV_Sqrt_Single) = "BV_Sqrt_Single"
    | toString_bvunop(BV_Sqrt_Double) = "BV_Sqrt_Double"

fun toString_bvbinop(BV_And) = "BV_And" | toString_bvbinop(BV_Concat) = "BV_Concat"  
| toString_bvbinop(BV_Div) = "BV_Div" | toString_bvbinop(BV_Minus) = "BV_Minus"  
| toString_bvbinop(BV_Modulus) = "BV_Modulus" | toString_bvbinop(BV_Mult) = "BV_Mult"  
| toString_bvbinop(BV_Or) = "BV_Or" | toString_bvbinop(BV_Plus) = "BV_Plus"  
| toString_bvbinop(BV_Rot_Left) = "BV_RotateLeft" | toString_bvbinop(BV_Rot_Right) = "BV_RotateRight"  
| toString_bvbinop(BV_Shift_Left) = "BV_Shift_Left" | toString_bvbinop(BV_Shift_Right) = "BV_Shift_Right"  
| toString_bvbinop(BV_Signed_Div) = "BV_Signed_Div" | toString_bvbinop(BV_Signed_Mod) = "BV_Sign_Mod"  
| toString_bvbinop(BV_Sign_Shift_Right) = "BV_Sign_Shift_Right" | toString_bvbinop(BV_Xor) = "BV_Xor"  
| toString_bvbinop(BV_Add_Single) = "BV_Add_Single" | toString_bvbinop(BV_Sub_Single) = "BV_Sub_Single"  
| toString_bvbinop(BV_Div_Single) = "BV_Div_Single" | toString_bvbinop(BV_Mul_Single) = "BV_Mul_Single"  
| toString_bvbinop(BV_Add_Double) = "BV_Add_Double" | toString_bvbinop(BV_Sub_Double) = "BV_Sub_Double"  
| toString_bvbinop(BV_Div_Double) = "BV_Div_Double" | toString_bvbinop(BV_Mul_Double) = "BV_Mul_Double"  
| toString_bvbinop(BV_Cmpf) = "BV_Cmpf" | toString_bvbinop(BV_Cmpd) = "BV_Cmpd"  
| toString_bvbinop(BV_Maxcmp_Single) = "BV_Maxcmp_Single" | toString_bvbinop(BV_Mincmp_Single) = "BV_Mincmp_Single"  
| toString_bvbinop(BV_Maxcmp_Double) = "BV_Maxcmp_Double" | toString_bvbinop(BV_Mincmp_Double) = "BV_Mincmp_Double"  
| toString_bvbinop(BV_Idiv_Quotient_Int8) = "BV_Idiv_Quotient_Int8" | toString_bvbinop(BV_Idiv_Remainder_Int8) = "BV_Idiv_Remainder_Int8"  
| toString_bvbinop(BV_Div_Quotient_Int8) = "BV_Div_Quotient_Int8" | toString_bvbinop(BV_Div_Remainder_Int8) = "BV_Div_Remainder_Int8"  
| toString_bvbinop(BV_Idiv_Quotient_Int16) = "BV_Idiv_Quotient_Int16" | toString_bvbinop(BV_Idiv_Remainder_Int16) = "BV_Idiv_Remainder_Int16"  
| toString_bvbinop(BV_Div_Quotient_Int16) = "BV_Div_Quotient_Int16" | toString_bvbinop(BV_Div_Remainder_Int16) = "BV_Div_Remainder_Int16"  
| toString_bvbinop(BV_Idiv_Quotient_Int32) = "BV_Idiv_Quotient_Int32" | toString_bvbinop(BV_Idiv_Remainder_Int32) = "BV_Idiv_Remainder_Int32"  
| toString_bvbinop(BV_Div_Quotient_Int32) = "BV_Div_Quotient_Int32" | toString_bvbinop(BV_Div_Remainder_Int32) = "BV_Div_Remainder_Int32"  
| toString_bvbinop(BV_Idiv_Quotient_Int64) = "BV_Idiv_Quotient_Int64" | toString_bvbinop(BV_Idiv_Remainder_Int64) = "BV_Idiv_Remainder_Int64"  
| toString_bvbinop(BV_Div_Quotient_Int64) = "BV_Div_Quotient_Int64" | toString_bvbinop(BV_Div_Remainder_Int64) = "BV_Div_Remainder_Int64" 

fun toString_bvternop(BV_Vfmsub132_Single) = "BV_Vfmsub132_Single"
| toString_bvternop(BV_Vfmadd132_Single) = "BV_Vfmadd132_Single" 
| toString_bvternop(BV_Vfnmadd132_Single) = "BV_Vfnmadd132_Single"
| toString_bvternop(BV_Vfnmsub132_Single) = "BV_Vfnmsub132_Single" 
| toString_bvternop(BV_Vfnmadd132_Double) = "BV_Vfnmadd132_Double"
| toString_bvternop(BV_Vnfmsub132_Double) = "BV_Vnfmsub132_Double" 
| toString_bvternop(BV_Vfmsub132_Double) = "BV_Vfmsub132_Double"
| toString_bvternop(BV_Vfmadd132_Double) = "BV_Vfmadd132_Double" 

fun toString_bbinop(B_And) = "\<and>" | toString_bbinop(B_Or) = "\<or>"  
| toString_bbinop(B_Eq) = "==" | toString_bbinop(B_Xor) = "^"  
| toString_bbinop(B_Iff) = "\<longleftrightarrow>" | toString_bbinop(B_Implies) = "\<longrightarrow>"  

fun toString_bvf (BV_Assignment (g,bvf)) = "[BV_Assignment " ^ toString_bvvar g ^ " " ^ toString_bvf bvf ^"]"
| toString_bvf (BV_Flag_Assignment (g,bvf)) = "[BV_Flag_Assignment " ^ toString_flag g ^ " " ^ toString_bvf bvf ^"]"
| toString_bvf (BV_Immediate (v,size)) = "[BV_Immediate " ^ toString v ^ " " ^  toString size ^ "]"
| toString_bvf (BV_Get g) = toString_bvvar g
| toString_bvf (BV_Slice (bv,e,s)) = "[BV_Slice " ^ toString_bvf bv ^ " " ^ toString e ^ " " ^ toString s ^ "]"
| toString_bvf (BV_Unop (u, bv)) = "[BV_Unop::" ^toString_bvunop u ^ " " ^ toString_bvf bv ^ "]"
| toString_bvf (BV_Binop (u,bv1,bv2)) = "[BV_Binop::" ^ toString_bvbinop u ^ " " ^ toString_bvf bv1 ^ " " ^  toString_bvf bv2 ^ "]"
| toString_bvf (BV_Ternop (u,bv1,bv2,bv3)) = "[BV_Ternop::" ^ toString_bvternop u ^ " " ^ toString_bvf bv1 ^ " " ^  toString_bvf bv2 ^ " " ^  toString_bvf bv3 ^  "]"
| toString_bvf (BV_ITE (bf,bv0,bv1)) = "[" ^ toString_bvf bf ^ " ? " ^  toString_bvf bv0 ^ " : " ^ toString_bvf bv1 ^ "]"
| toString_bvf (B_Binop (u,bv0,bv1)) = toString_bvf bv0 ^ " " ^ toString_bbinop u ^ " " ^ toString_bvf bv1
| toString_bvf (B_Get f) = toString_flag f
| toString_bvf (B_True) = "True"
| toString_bvf (B_False) = "False"
| toString_bvf (BV_Undefined) = "Undefined"

fun toString_bvfs bvfs = 
  String.concat (
    [" ( Assignments: " ] @
      map add_semicolon (map toString_bvf bvfs)
    @ [") "]
  )

(* BV Formula END *)




(* Semantic Start *)

type semantics = 
{  
  instr_semantics  : instr_mnemonic -> (operand_sig -> (bitvector_formula option) option)
}

(* fun mk_semantic ((ins_mnemonic,operand_sig, bv)) =  HOLogic.mk_prod (mk_instr_mnemonic ins_mnemonic, HOLogic.mk_prod (mk_operand_sig operand_sig, mk_bvfs bv)) *)

fun mk_semantic ((((ins_fam,ins_mnemonic),operand_sig), bv)) = (mk_instr_mnemonic_family ins_fam, mk_instr_mnemonic ins_mnemonic, mk_operand_sig operand_sig, mk_bvfs bv)

fun toString_semantic ((((ins_fam,instr_mnem), operand_sig), bv)) = "[" ^ toString_instr_mnemonic instr_mnem ^ toString_operand_sig operand_sig ^ "-->" ^ toString_bvfs bv

(* Semantic End *)

fun mk_mapDT D  = Type ("List.list", [D]);
fun mk_mapRT D R = Type ("Map.map", [D, R]);

fun convert ts domainT rangeT = Const ("Map.map_of", domainT --> rangeT ) $ ts;

fun mk_map ts domain_list domain_map range_map =
  let
    val domainT = mk_mapDT domain_list; 
    val rangeT = mk_mapRT domain_map range_map;
  in
    convert ts domainT rangeT
end

(* The first parameter is a set of distinct instruction mnemonics.
The second parameter is a list of tuples containing (mnemonic,operand_sig,bvf)

The retrun value 
*)
fun fst (a,b,c,d) = a
fun fst_two (a,b,c,d) = (a,b)
fun snd (a,b,c,d) = b
fun trd (a,b,c,d) = c
fun last_three (a,b,c,d) = (b,c,d)
fun last_two_4 (a,b,c,d) = (c,d)
fun last_two_3 (a,b,c) = (b,c)
 
fun 
  build_families_to_submaps [] _ a = a 
| build_families_to_submaps (family::fam_remaining) instr_maps family_funcs = 
      let
        val fam_formulas = filter (fn (fam,_, _) => fam=family) instr_maps;
        val leftover_formulas = filter (fn (fam,_,_) => fam<>family) instr_maps;

        val fam_list_for_map = mk_list @{typ "(instr_mnemonic \<times> (operand_sig \<rightharpoonup> (bitvector_formula list)))"} (map HOLogic.mk_prod (map last_two_3 fam_formulas));  
        val fam_partial_func = mk_map fam_list_for_map @{typ "(instr_mnemonic \<times> (operand_sig \<rightharpoonup> (bitvector_formula list)))"} @{typ "instr_mnemonic"} @{typ "(operand_sig \<rightharpoonup> (bitvector_formula list))"};                                      
        val result = HOLogic.mk_prod (family, fam_partial_func);
      in 
        build_families_to_submaps fam_remaining leftover_formulas (result::family_funcs)
end

fun 
  build_operands_to_bf_functions [] _ a = a 
| build_operands_to_bf_functions ((fam,nemonic)::nem_remaining) formulas operand_sig_bvf_funcs = 
      let
        val nem_formulas = filter (fn (_,nem,_,_) => nem=nemonic) formulas;
        val leftover_formulas = filter (fn (_,nem,_,_) => nem<>nemonic) formulas;

        val nem_list_for_map = mk_list @{typ "operand_sig \<times> (bitvector_formula list)"} (map HOLogic.mk_prod (map last_two_4 nem_formulas));  
        val nem_partial_func = mk_map nem_list_for_map @{typ "operand_sig \<times> (bitvector_formula list)"} @{typ "operand_sig"} @{typ "bitvector_formula list"};                                      
        val result = (fam,nemonic,nem_partial_func);
      in 
        build_operands_to_bf_functions nem_remaining leftover_formulas (result::operand_sig_bvf_funcs)
end


fun distinct_list [] = []
| distinct_list (a::b) = a:: (distinct_list (filter (fn (x) => x <> a) b))

fun mk_semantics is = 
  let 
      val fourtuple_semantics = (map mk_semantic is);
      val nemonics = distinct_list (map fst_two fourtuple_semantics); (* The list of mnemonics used *)
      val families = distinct_list (map fst fourtuple_semantics); (* The list of families used *)
      val threetuple_semantics = (build_operands_to_bf_functions nemonics fourtuple_semantics []);   
      val family_maps = (build_families_to_submaps families threetuple_semantics []);   
      val ls = mk_list @{typ "instr_mnemonic_family \<times> (instr_mnemonic \<rightharpoonup> (operand_sig \<rightharpoonup> (bitvector_formula list)))"} family_maps 
  in 
  @{term "semantics.make"} $ 
    mk_map ls @{typ "instr_mnemonic_family \<times> (instr_mnemonic \<rightharpoonup> (operand_sig \<rightharpoonup> (bitvector_formula list)))"} @{typ "instr_mnemonic_family"} @{typ "(instr_mnemonic \<rightharpoonup> (operand_sig \<rightharpoonup> (bitvector_formula list)))"}
  end

fun add_newline s = s ^ "\n"

fun toString_semantics is =
  String.concat (
    ["Semantics: " ^ "\n"] @
    map add_newline (map toString_semantic is)
  )




  
   
