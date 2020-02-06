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

theory Chum_Datatypes
  imports reassembly_datatypes.MachineDatatypes 
begin

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
    | BV_Neg (* TODO *)
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
     | BV_Operand3
     | BV_Var_Direct register_mnemonic (* Some instructions directly read write to specific generic 64-bit registers *)

datatype bitvector_formula  = 
     BV_Assignment BV_var bitvector_formula 
  |  BV_Flag_Assignment flag bitvector_formula
  |  BV_Immediate int nat (* value, number_of_bits *)
  |  BV_Get BV_var
  |  BV_Slice bitvector_formula nat nat (* end_bit, start_bit IE: 15 0 being the first two bytes *)
  |  BV_Unop BV_unary_operators bitvector_formula
  |  BV_Binop BV_binary_operators bitvector_formula bitvector_formula
  |  BV_Ternop BV_ternary_operators bitvector_formula bitvector_formula bitvector_formula
  |  BV_ITE bitvector_formula bitvector_formula bitvector_formula
  |  BV_Undefined
  | B_Get flag
  | B_Binop B_binary_operators bitvector_formula bitvector_formula
  | B_True |  B_False

record semantics =
  instr_semantics  :: "instr_mnemonic_family \<rightharpoonup>  (instr_mnemonic \<rightharpoonup> (operand_sig \<rightharpoonup> (bitvector_formula list)))" 
(*   optimized_instr_semantics  :: "instr_mnemonic_family \<rightharpoonup>  (instr \<rightharpoonup> (bitvector_formula list))"  TBD for instruction semantics that don't operation on whole instruction variants classes *)


end
