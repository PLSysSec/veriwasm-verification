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

theory Chum_Execution              
imports Manual_Execution
begin

context execution_context
begin

primrec BV_ternary_operate :: "BV_ternary_operators \<Rightarrow> bv \<Rightarrow>  bv \<Rightarrow> bv \<Rightarrow> bv"
  where "BV_ternary_operate BV_Vfmsub132_Single bv1 bv2 bv3  = undefined"
|  "BV_ternary_operate BV_Vfmsub132_Double bv1 bv2 bv3  = undefined"
|  "BV_ternary_operate BV_Vfnmadd132_Single bv1 bv2 bv3  = undefined"
|  "BV_ternary_operate BV_Vfnmadd132_Double  bv1 bv2 bv3  = undefined"
|  "BV_ternary_operate BV_Vfnmsub132_Single bv1 bv2 bv3  = undefined"
|  "BV_ternary_operate BV_Vnfmsub132_Double bv1 bv2 bv3  = undefined"
|  "BV_ternary_operate BV_Vfmadd132_Single bv1 bv2 bv3  = undefined"
|  "BV_ternary_operate BV_Vfmadd132_Double bv1 bv2 bv3  = undefined"

primrec BV_binary_operate :: "BV_binary_operators \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv"
  where "BV_binary_operate BV_And bv1 bv2 = (let (w1,s1) = bv1;(w2,s2) = bv2 in(((AND) w1 w2), max s1 s2))"
  | "BV_binary_operate BV_Concat bv1 bv2 = bv_cat bv1 bv2"
  | "BV_binary_operate BV_Div bv1 bv2 = undefined"
  | "BV_binary_operate BV_Minus bv1 bv2 = (let (w1,s1) = bv1;(w2,s2) = bv2 in(((-) w1 w2), max s1 s2))"
  | "BV_binary_operate BV_Modulus _ _ = undefined"
  | "BV_binary_operate BV_Mult _ _ = undefined"
  | "BV_binary_operate BV_Or bv1 bv2 = (let (w1,s1) = bv1;(w2,s2) = bv2 in(((OR) w1 w2), max s1 s2))" 
  | "BV_binary_operate BV_Plus bv1 bv2 = bv1 +\<^sup>b\<^sup>v bv2"
  | "BV_binary_operate BV_Rot_Left _ _ = undefined"
  | "BV_binary_operate BV_Rot_Right _ _ = undefined"
  | "BV_binary_operate BV_Shift_Left _ _ = undefined"
  | "BV_binary_operate BV_Shift_Right _ _ = undefined"
  | "BV_binary_operate BV_Signed_Div _ _ = undefined"
  | "BV_binary_operate BV_Signed_Mod _ _ = undefined"
  | "BV_binary_operate BV_Sign_Shift_Right _ _ = undefined"
  | "BV_binary_operate BV_Xor bv1 bv2 = (let (w1,s1) = bv1;(w2,s2) = bv2 in(((XOR) w1 w2), max s1 s2))" 
  | "BV_binary_operate BV_Cmpf  _ _ = undefined"
  | "BV_binary_operate BV_Cmpd _ _ = undefined"
  | "BV_binary_operate BV_Add_Double bv1 bv2 = bv1 fplus\<^sup>b\<^sup>v bv2"
  | "BV_binary_operate BV_Add_Single _ _ = undefined"
  | "BV_binary_operate BV_Sub_Double bv1 bv2 = bv1 fsub\<^sup>b\<^sup>v bv2"
  | "BV_binary_operate BV_Sub_Single _ _ = undefined"
  | "BV_binary_operate BV_Div_Double bv1 bv2 = bv1 fdiv\<^sup>b\<^sup>v bv2"
  | "BV_binary_operate BV_Div_Single _ _ = undefined"
  | "BV_binary_operate BV_Maxcmp_Double _ _ = undefined"
  | "BV_binary_operate BV_Maxcmp_Single _ _ = undefined"
  | "BV_binary_operate BV_Mincmp_Double _ _ = undefined"
  | "BV_binary_operate BV_Mincmp_Single _ _ = undefined"
  | "BV_binary_operate BV_Mul_Double bv1 bv2 = bv1 fmult\<^sup>b\<^sup>v bv2"
  | "BV_binary_operate BV_Mul_Single _ _ = undefined"
  | "BV_binary_operate BV_Idiv_Quotient_Int8 _ _ = undefined"
  | "BV_binary_operate BV_Idiv_Remainder_Int8 _ _ = undefined"
  | "BV_binary_operate BV_Idiv_Quotient_Int16 _ _ = undefined"
  | "BV_binary_operate BV_Idiv_Remainder_Int16 _ _ = undefined"
  | "BV_binary_operate BV_Idiv_Quotient_Int32 _ _ = undefined"
  | "BV_binary_operate BV_Idiv_Remainder_Int32 _ _ = undefined"
  | "BV_binary_operate BV_Idiv_Quotient_Int64 _ _ = undefined"
  | "BV_binary_operate BV_Idiv_Remainder_Int64 _ _ = undefined"
  | "BV_binary_operate BV_Div_Quotient_Int8 _ _ = undefined"
  | "BV_binary_operate BV_Div_Remainder_Int8 _ _ = undefined"
  | "BV_binary_operate BV_Div_Quotient_Int16 _ _ = undefined"
  | "BV_binary_operate BV_Div_Remainder_Int16 _ _ = undefined"
  | "BV_binary_operate BV_Div_Quotient_Int32 _ _ = undefined"
  | "BV_binary_operate BV_Div_Remainder_Int32 _ _ = undefined"
  | "BV_binary_operate BV_Div_Quotient_Int64 _ _ = undefined"
  | "BV_binary_operate BV_Div_Remainder_Int64  _ _ = undefined"


primrec BV_unary_operate :: "BV_unary_operators \<Rightarrow> bv \<Rightarrow> bv"
  where "BV_unary_operate BV_SExtend16 bv = (let (w,s) = bv in sextend w s 16, 16)"
  | "BV_unary_operate BV_SExtend32 bv = (let (w,s) = bv in sextend w s 32, 32)"
  | "BV_unary_operate BV_SExtend64 bv = (let (w,s) = bv in sextend w s 64, 64)"
  | "BV_unary_operate BV_SExtend128 bv = (let (w,s) = bv in sextend w s 128, 128)"
  | "BV_unary_operate BV_SExtend256 bv = (let (w,s) = bv in sextend w s 256, 256)"
  | "BV_unary_operate BV_Not bv = bv_NOT bv"
  | "BV_unary_operate BV_Neg bv = (let (w,s) = bv in (-w,s))"
  | "BV_unary_operate  BV_Cvt_Int32_To_Double  _ =             undefined" (* 32 \<rightarrow> 64 bit*)
  | "BV_unary_operate BV_Cvt_Single_To_Double  _ =             undefined" (* 32 \<rightarrow> 64 bit*)
  | "BV_unary_operate BV_Cvt_Double_To_Int64  _ =              undefined" (*64 \<rightarrow> 64 bit *) 
  | "BV_unary_operate BV_Cvt_Single_To_Int64  _ =              undefined" (* 32 \<rightarrow> 64 bit*)
  | "BV_unary_operate BV_Cvt_Double_To_Int64_Truncate   _ =    undefined" (*64 \<rightarrow> 64 bit *) 
  | "BV_unary_operate BV_Cvt_Single_To_Int64_Truncate  _ =     undefined" (* 32 \<rightarrow> 64 bit*)
  | "BV_unary_operate BV_Cvt_Int32_To_Single  _ =              undefined" (* 32 \<rightarrow> 32 bit*)
  | "BV_unary_operate BV_Cvt_Double_To_Int32   _ =             undefined" (*64 \<rightarrow> 32 bit*)
  | "BV_unary_operate BV_Cvt_Double_To_Single  _ =             undefined" (*64 \<rightarrow> 32 bit*)
  | "BV_unary_operate BV_Cvt_Single_To_Int32  _ =              undefined" (* 32 \<rightarrow> 32 bit*)
  | "BV_unary_operate BV_Cvt_Int64_To_Double  _ =              undefined" (*64 \<rightarrow> 64 bit *)
  | "BV_unary_operate BV_Cvt_Int64_To_Single   _ =             undefined" (*64 \<rightarrow> 32 bit*)
  | "BV_unary_operate BV_Cvt_Double_To_Int32_Truncate  bv =    (ucast (cvttsd2si(\<langle>63,0\<rangle>fst bv)), 32)" (*64 \<rightarrow> 32 bit*)
  | "BV_unary_operate BV_Cvt_Single_To_Int32_Truncate  _ =     undefined" (* 32 \<rightarrow> 32 bit*)
  | "BV_unary_operate  BV_Approx_Reciprocal_Single  _ =        undefined"  (* 32 \<rightarrow> 32 bit*)
  | "BV_unary_operate  BV_Approx_Reciprocal_Sqrt_Single  _ =   undefined"  (* 32 \<rightarrow> 32 bit*)
  | "BV_unary_operate  BV_Sqrt_Single  _ =                     undefined"  (* 32 \<rightarrow> 32 bit*)
  | "BV_unary_operate  BV_Sqrt_Double  _ =                     undefined"   (*64 \<rightarrow> 64 bit *)



primrec B_binary_operate :: "B_binary_operators \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv"
  where 
    "B_binary_operate B_And bv1 bv2 = bool_to_bv (bv_to_bool bv1 \<and> bv_to_bool bv2)"
  | "B_binary_operate B_Or bv1 bv2 = bool_to_bv (bv_to_bool bv1 \<or> bv_to_bool bv2)"
  | "B_binary_operate B_Xor bv1 bv2 = (let x = bv_to_bool bv1 ; y = bv_to_bool bv2 in 
          bool_to_bv ((x \<and> \<not>y) \<or> (\<not>x \<and> y)))"
  | "B_binary_operate B_Iff bv1 bv2 =  bool_to_bv (bv_to_bool bv1 \<longleftrightarrow> bv_to_bool bv2)"
  | "B_binary_operate B_Implies bv1 bv2 = bool_to_bv (bv_to_bool bv1 \<longrightarrow> bv_to_bool bv2)"
  | "B_binary_operate B_Eq bv1 bv2 = bool_to_bv (bv1 = bv2)"

fun positive_offset_address :: "address \<Rightarrow> int \<Rightarrow> address "
  where "positive_offset_address a i = (A_Plus (A_Constant i) a)"

(* Upgrade a general register to its 64-bit parent or a Vector Register to it's 256-bit parent *)
fun operand_get_parent :: "operand_src \<Rightarrow> operand_src"
  where
     "operand_get_parent (Storage (Reg (General _ r)))  =  (Storage (Reg (General SixtyFour r)))" (* Upgrade to full 64-bit register *)
  |  "operand_get_parent (Storage (Reg (SIMD OneHundredTwentyEight w3 w2 w1 w0))) =  (Storage (Reg (SIMD TwoHundredFiftySix w3 w2 w1 w0)))" (* Upgrade to 256-bit register*)
  |  "operand_get_parent operand  =  operand"

(* resolve a parametric or direct variable for reading (and if downgraded to operand_dest with assocated caveat, writing). 
 Gives you an operand source vice dest as it's more general. Upgrades where needed to
the operand src from a dest, as well as to parent registers as we operate only on whole registers.
*)
fun resolve_BV_Var :: "instr \<Rightarrow> BV_var \<Rightarrow> operand_src"
  where 
    "resolve_BV_Var (Unary _ i) BV_Operand1 = operand_get_parent i"
  | "resolve_BV_Var (Binary _ i _) BV_Operand1 = operand_get_parent (Storage (i))"
  | "resolve_BV_Var (Ternary _ i _ _) BV_Operand1 =operand_get_parent (Storage (i))"
  | "resolve_BV_Var (Binary _ _ i) BV_Operand2 = operand_get_parent i"
  | "resolve_BV_Var (Ternary _ _ i _) BV_Operand2 =operand_get_parent i"
  | "resolve_BV_Var (Ternary _ _ _ i) BV_Operand3 =operand_get_parent i"
  | "resolve_BV_Var _ (BV_Var_Direct r) = (Storage (Reg (General SixtyFour r)))"
  | "resolve_BV_Var _ _ = undefined" (* Nullary's don't have operands. Also for example a Unary doesn't have an operand 2 *)

(* This is needed for BV_Assignment which should never resolve down to writing to an immediate *)
primrec operand_src_to_operand_dest  :: " operand_src \<Rightarrow> operand_dest"
  where 
   "operand_src_to_operand_dest (Storage s) = s"
|  "operand_src_to_operand_dest (Immediate _ _) = undefined"

fun bv_read_memory :: "assembly \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> address \<Rightarrow> bv"
  where
    "bv_read_memory \<alpha> \<sigma> s (A_FromReg reg) =
      (let' a = fst (read_reg \<sigma> reg) in
        (\<sigma> \<turnstile> *[a,(s div 8)],s))"
  | "bv_read_memory \<alpha> \<sigma> s (A_Label x) =
      (let a = the (label_to_address \<alpha> x) in
        (\<sigma> \<turnstile> *[a,(s div 8)],s))"
  | "bv_read_memory \<alpha> \<sigma> s (A_Minus a0 a1) =
      (let' x0 = resolve_address \<alpha> \<sigma> a0;
            x1 = resolve_address \<alpha> \<sigma> a1 in
        (\<sigma> \<turnstile> *[x0 - x1,(s div 8)],s))"
  | "bv_read_memory \<alpha> \<sigma> s (A_Plus a0 (A_Label x)) = 
      (if (a0  = (A_FromReg (General SixtyFour rip))) then 
        (\<sigma> \<turnstile> *[the (label_to_address \<alpha> x),(s div 8)],s)
      else let' x0 = resolve_address \<alpha> \<sigma> a0;
                x1 = resolve_address \<alpha> \<sigma> (A_Label x) in
        (\<sigma> \<turnstile> *[x0 + x1,(s div 8)], s))"
  | "bv_read_memory \<alpha> \<sigma> s (A_Plus a0 a1) =
      (let' x0 = resolve_address \<alpha> \<sigma> a0;
            x1 = resolve_address \<alpha> \<sigma> a1 in
        (\<sigma> \<turnstile> *[x0 + x1,(s div 8)], s))"
  | "bv_read_memory \<alpha> \<sigma> s (A_Constant a) =
      (\<sigma> \<turnstile> *[word_of_int a,(s div 8)],s)"
  | "bv_read_memory \<alpha> \<sigma> s (A_WordConstant a) =
      (\<sigma> \<turnstile> *[a,(s div 8)],s)"
  | "bv_read_memory _ _ _ _ = Code.abort (STR ''bv_read_memory error'') undefined"


(* This could be folded into data_from_src, if it were generalized to (longword x bits) and fixed the manual_exec that would be affected *)
fun exec_chum_bv_get :: "assembly \<Rightarrow> state \<Rightarrow> instr \<Rightarrow> operand_src \<Rightarrow> bv"
  where 
(* We should never really read a 128-bit register as it'a a partial to the AVX register and gets upgraded when resolved. Regardless it's here. *)
    "exec_chum_bv_get \<alpha> \<sigma> i (Storage (Reg (SIMD OneHundredTwentyEight _ _ high low ))) = ( let 
                                                                (w1,s1) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour high))); 
                                                                (w0,s0) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour low)));
                                                                bv1 = (\<langle>63,0\<rangle> w1,s1);
                                                                bv0 = (\<langle>63,0\<rangle> w0,s0)
                                                                      in bv_cat bv1 bv0)" 

  |    "exec_chum_bv_get \<alpha> \<sigma> i (Storage (Reg (SIMD TwoHundredFiftySix word3 word2 word1 word0 ))) = ( let 
                                                                (w3,s3) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour word3)));
                                                                (w2,s2) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour word2)));
                                                                (w1,s1) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour word1)));
                                                                (w0,s0) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour word0)));
                                                                bv3 = (\<langle>63,0\<rangle> w3,s3);
                                                                bv2 = (\<langle>63,0\<rangle> w2,s2);
                                                                bv1 = (\<langle>63,0\<rangle> w1,s1);
                                                                bv0 = (\<langle>63,0\<rangle> w0,s0)
                                                                      in (bv_cat (bv_cat bv3 bv2) (bv_cat bv1 bv0)) )"
  |    "exec_chum_bv_get \<alpha> \<sigma> i (Storage (Memory TwoHundredFiftySix a))  = bv_read_memory \<alpha> \<sigma> 256 a" 
  |    "exec_chum_bv_get \<alpha> \<sigma> i (Storage (Memory OneHundredTwentyEight a))  = bv_read_memory \<alpha> \<sigma> 128 a" 
  |    "exec_chum_bv_get \<alpha> \<sigma> i (Immediate b (ImmVal iv)) = (\<langle>63,0\<rangle>((word_of_int iv)::64 word),mask_to_size b)"
  |    "exec_chum_bv_get \<alpha> \<sigma> i (Immediate b (ImmLabel iv)) = (\<langle>63,0\<rangle> (resolve_address \<alpha> \<sigma> (A_Label iv)) ,64)"
  |    "exec_chum_bv_get \<alpha> \<sigma> i (Storage (Memory b a))  = (\<langle>63,0\<rangle> fst (read_memory \<alpha> \<sigma> (mask_to_size b) a), (mask_to_size b)) " 
  |    "exec_chum_bv_get \<alpha> \<sigma> i (Storage (Reg (General b a))) =  (\<langle>63,0\<rangle> fst (read_reg \<sigma> (General b a)) ,(mask_to_size b)) " 

section \<open>The semantics of chum\<close>


primrec exec_chum_bvf :: "assembly \<Rightarrow> bitvector_formula \<Rightarrow> instr \<Rightarrow> state \<Rightarrow> bv"
where
   "exec_chum_bvf \<alpha> (BV_Immediate val bits) i \<sigma> = ((word_of_int val),bits)"
|  "exec_chum_bvf \<alpha> (BV_Get v) insr \<sigma> = (let' vv = resolve_BV_Var insr v; ret = exec_chum_bv_get \<alpha> \<sigma> insr vv in ret)"
|  "exec_chum_bvf \<alpha> (BV_Slice \<psi> hi lo) i \<sigma> = (let' bv = exec_chum_bvf \<alpha> \<psi> i \<sigma> in
                                                  bv_slice hi lo bv)"
| "exec_chum_bvf \<alpha> (BV_Unop ui \<psi>) i \<sigma> =
      (let' bv0 = exec_chum_bvf \<alpha> \<psi> i \<sigma> in
        BV_unary_operate ui bv0)"
| "exec_chum_bvf \<alpha> (BV_Binop bi \<psi>0 \<psi>1) i \<sigma> =
      (let' bv0 = exec_chum_bvf \<alpha> \<psi>0 i \<sigma>;
            bv1 = exec_chum_bvf \<alpha> \<psi>1 i \<sigma> in
        BV_binary_operate bi bv0 bv1)"
| "exec_chum_bvf \<alpha> (BV_Ternop ti \<psi>0 \<psi>1 \<psi>2) i \<sigma> = BV_ternary_operate ti (exec_chum_bvf \<alpha> \<psi>0 i \<sigma>) (exec_chum_bvf \<alpha> \<psi>1 i \<sigma>) (exec_chum_bvf \<alpha> \<psi>2 i \<sigma>)"(* TODO: let' *)
| "exec_chum_bvf \<alpha> (BV_ITE bf \<psi>0 \<psi>1) i \<sigma> = (let' b = bv_to_bool (exec_chum_bvf \<alpha> bf i \<sigma>) in 
                                                 if b then exec_chum_bvf \<alpha> \<psi>0 i \<sigma> else exec_chum_bvf \<alpha> \<psi>1 i \<sigma>)"
| "exec_chum_bvf \<alpha> (BV_Assignment a b) i \<sigma> = undefined" (* We should never have a sub-assignment *)
| "exec_chum_bvf \<alpha> (BV_Flag_Assignment a b) i \<sigma> = undefined" (* We should never have a sub-assignment *)
| "exec_chum_bvf \<alpha> (B_Binop bi \<psi>0 \<psi>1) i \<sigma> = B_binary_operate bi (exec_chum_bvf \<alpha> \<psi>0 i \<sigma>) (exec_chum_bvf \<alpha> \<psi>1 i \<sigma>)"
| "exec_chum_bvf \<alpha> (B_Get f) i \<sigma> = (let' f = read_flg \<sigma> f in bool_to_bv f)"  
| "exec_chum_bvf \<alpha> (B_True) i \<sigma> = (1,1)"  
| "exec_chum_bvf \<alpha> (B_False) i \<sigma> = (0,1)"  
| "exec_chum_bvf \<alpha> (BV_Undefined) i \<sigma> = undefined "  


type_synonym flag_annotation = "64 word \<Rightarrow> flag set"


fun get_op1_bvf_sub :: "bitvector_formula list \<Rightarrow> bitvector_formula option"
  where "get_op1_bvf_sub [] = None"
  | "get_op1_bvf_sub ((BV_Assignment BV_Operand1 bvf)#bfs) = Some bvf"
  | "get_op1_bvf_sub (_#bfs) = get_op1_bvf_sub bfs"

fun is_rh :: "register \<Rightarrow> bool"
  where "is_rh (General SixtyFour _)  = False" 
  | "is_rh (General ThirtyTwo _)  = False"
  | "is_rh (General Sixteen _)  = False"
  | "is_rh (General EightHigh _)  = True"
  | "is_rh (General Eight _)  = False"
  | "is_rh (SIMD _ _ _ _ _)  = False"

fun operand_dst_is_rh :: "operand_dest \<Rightarrow> bool"
  where "operand_dst_is_rh (Reg r)  = is_rh r"
  | "operand_dst_is_rh (Memory i r)  = False"

fun get_op1_bvf :: "instr \<Rightarrow> bitvector_formula list \<Rightarrow> (bitvector_formula option \<times> bool)"
  where "get_op1_bvf (Binary (IS_8088 _) od _) bfs = (get_op1_bvf_sub bfs, operand_dst_is_rh od)"
  | "get_op1_bvf (Binary (IS_80386 _) od _) bfs= (get_op1_bvf_sub bfs, operand_dst_is_rh od)"
  | "get_op1_bvf (Binary (IS_80486 Cmpxchg) _ _) bfs = (None,False)"
  | "get_op1_bvf (Binary (IS_80486 _) od _) bfs = (get_op1_bvf_sub bfs, operand_dst_is_rh od)"
  | "get_op1_bvf (Binary (IS_PentiumPro _) od _) bfs = (get_op1_bvf_sub bfs, operand_dst_is_rh od)"
  | "get_op1_bvf (Unary (IS_8088 _) (Storage od) ) bfs = (get_op1_bvf_sub bfs, operand_dst_is_rh od)"
  | "get_op1_bvf (Unary (IS_80386 _) (Storage od) ) bfs= (get_op1_bvf_sub bfs, operand_dst_is_rh od)"
  | "get_op1_bvf (Unary (IS_80486 _) (Storage od) ) bfs = (get_op1_bvf_sub bfs, operand_dst_is_rh od)"
  | "get_op1_bvf (Unary (IS_PentiumPro _) (Storage od) ) bfs = (get_op1_bvf_sub bfs, operand_dst_is_rh od)"
  | "get_op1_bvf _ _ = (None,False)"


fun exec_learned_instr :: "assembly \<Rightarrow> bitvector_formula list \<Rightarrow> (bitvector_formula option  \<times> bool) \<Rightarrow> instr \<Rightarrow> state \<Rightarrow> state"
  where 
  "exec_learned_instr \<alpha> [] op1_bvf i \<sigma> = \<sigma>"
| "exec_learned_instr \<alpha> ((BV_Assignment v bvf)#bfs) op1_bvf i \<sigma> =
    (let' bv = ((exec_chum_bvf \<alpha> bvf i \<sigma>));
          od = operand_src_to_operand_dest (resolve_BV_Var i v);
          \<sigma>' = exec_learned_instr \<alpha> bfs op1_bvf i \<sigma> in
      bv_put \<alpha> od bv \<sigma>')"
| "exec_learned_instr \<alpha> ((BV_Flag_Assignment flag_pf bvf)#bfs) (None,op1_o) i \<sigma> =
    (let' \<sigma>' = exec_learned_instr \<alpha> bfs (None,op1_o) i \<sigma>;
          \<sigma>'' = write_flg flag_pf undefined \<sigma>' in
        \<sigma>'')"
| "exec_learned_instr \<alpha> ((BV_Flag_Assignment flag_pf bvf)#bfs) (Some op1_bvf,False) i \<sigma> =
    (let' (bv,s) = exec_chum_bvf \<alpha> op1_bvf i \<sigma>;
           pf = parity bv ;
          \<sigma>' = exec_learned_instr \<alpha> bfs (Some op1_bvf,False) i \<sigma>;
          \<sigma>'' = write_flg flag_pf pf \<sigma>' in
        \<sigma>'')"
| "exec_learned_instr \<alpha> ((BV_Flag_Assignment flag_pf bvf)#bfs) (Some op1_bvf,True) i \<sigma> =
    (let' (bv,s) = exec_chum_bvf \<alpha> op1_bvf i \<sigma>;
           pf = parity_offset bv;
          \<sigma>' = exec_learned_instr \<alpha> bfs (Some op1_bvf,True) i \<sigma>;
          \<sigma>'' = write_flg flag_pf pf \<sigma>' in
        \<sigma>'')"
| "exec_learned_instr \<alpha> ((BV_Flag_Assignment flg bvf)#bfs) op1_bvf i \<sigma> =
    (let' \<sigma>' = exec_learned_instr \<alpha> bfs op1_bvf i \<sigma>;
           e  = exec_chum_bvf \<alpha> bvf i \<sigma>;
           f  = bv_to_bool e;
           \<sigma>'' = write_flg flg f \<sigma>' in
        \<sigma>'')"
| "exec_learned_instr \<alpha> _ op1_bvf i \<sigma> = undefined"



definition  init_state :: "assembly \<Rightarrow> state \<Rightarrow> state"
  where "init_state \<alpha> \<sigma> \<equiv> let m = write_blocks (data_sections_to_blocks \<alpha>) (mem \<sigma>) in write_reg (General SixtyFour rip) (binary_offset \<alpha>) (\<sigma>\<lparr>mem:=m\<rparr>)"

fun remove_flags :: "flag list \<Rightarrow> (state \<Rightarrow> state) \<Rightarrow> state \<Rightarrow> state"
  where "remove_flags [] t = t"
  | "remove_flags (flag_pf#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_pf := undefined)\<rparr>))"
  | "remove_flags (flag_cf#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_cf := undefined)\<rparr>))"
  | "remove_flags (flag_zf#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_zf := undefined)\<rparr>))"
  | "remove_flags (flag_of#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_of := undefined)\<rparr>))"
  | "remove_flags (flag_sf#flgs) t = remove_flags flgs (\<lambda> \<sigma> . let \<sigma>' = t \<sigma> in (\<sigma>'\<lparr>flags := (flags \<sigma>')(flag_sf := undefined)\<rparr>))"

primrec filter_flag_annotation :: "flag_annotation \<Rightarrow> 64 word \<Rightarrow> flag list \<Rightarrow> flag list"
  where "filter_flag_annotation \<phi> loc [] = []"
  | "filter_flag_annotation \<phi> loc (flg#flgs) = (if flg \<notin> \<phi> loc then [flg] else [])@(filter_flag_annotation \<phi> loc flgs)"


definition get_semantics :: "assembly \<Rightarrow> semantics \<Rightarrow> instr \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where
    "get_semantics \<alpha> \<Psi> insr si \<equiv>
      let' (fam,n,o_sig) = Get_Instr_Sig insr;
           family_list = instr_semantics \<Psi> fam;
           family_list_not_found = (family_list = None);
           variant_list = (if family_list_not_found then None else the family_list n);
           variant_list_not_found = (variant_list = None);
           bv_formula = (if variant_list_not_found then None else the variant_list o_sig);
           manual = (bv_formula = None);
           op1_bvf = get_op1_bvf insr (the bv_formula) ;
           exec = (if manual then manual_exec_instr \<alpha> insr si else exec_learned_instr \<alpha> (the bv_formula) op1_bvf insr) 
            in
      exec"

definition is_manual :: "assembly \<Rightarrow> semantics \<Rightarrow> instr \<Rightarrow> bool"
  where
    "is_manual \<alpha> \<Psi> insr \<equiv>
      let' (fam,n,o_sig) = Get_Instr_Sig insr;
           family_list = instr_semantics \<Psi> fam;
           family_list_not_found = (family_list = None);
           variant_list = (if family_list_not_found then None else the family_list n);
           variant_list_not_found = (variant_list = None);
           bv_formula = (if variant_list_not_found then None else the variant_list o_sig);
           manual = (bv_formula = None) in
        manual"


definition exec_instr :: "assembly \<Rightarrow> semantics \<Rightarrow> flag_annotation \<Rightarrow> instr \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where                 
    "exec_instr \<alpha> \<Psi> \<phi> i si \<sigma> \<equiv>
      let' t = get_semantics \<alpha> \<Psi> i si;
           manual = is_manual \<alpha> \<Psi> i in
        (if manual then t \<sigma> else
          let flgs = filter_flag_annotation \<phi> (regs \<sigma> rip) [flag_pf,flag_cf,flag_zf,flag_sf,flag_of];
              t = remove_flags flgs t in
            incr_rip si (t \<sigma>))"

definition "entry_size :: nat \<equiv> 100"
definition instr_index :: "(nat \<rightharpoonup> (nat \<rightharpoonup> nat)) \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> nat option"
  where "instr_index lookup_table boffset a \<equiv>
      case lookup_table (unat (a - boffset) div entry_size * entry_size) of
            None \<Rightarrow> None
          | Some table \<Rightarrow> table (unat (a - boffset))"

fun exec_assembly :: "assembly \<Rightarrow> (nat \<rightharpoonup> (nat \<rightharpoonup> nat)) \<Rightarrow> flag_annotation \<Rightarrow> semantics \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where "exec_assembly _ _ _ _ 0 \<sigma> = \<sigma>"
  | "exec_assembly \<alpha> lookup_table \<phi> \<Psi> (Suc n) \<sigma> = (
    let  pc = get_rip \<sigma>;
         boffset = binary_offset \<alpha>;
         index = the (instr_index lookup_table boffset pc);
         (_,i,s) = (text_sections \<alpha>)!index;
         \<sigma> = exec_instr \<alpha> \<Psi> \<phi> i s \<sigma>;
         \<sigma> = exec_assembly \<alpha> lookup_table \<phi> \<Psi> n \<sigma> in
      \<sigma>
    )"

lemma exec_assembly_def:
  shows "exec_assembly \<alpha> lookup_table \<phi> \<Psi> n \<sigma> = (if n = 0 then \<sigma> else
    let' pc = get_rip \<sigma>;
         boffset = binary_offset \<alpha>;
         index = the (instr_index lookup_table boffset pc);
         (_,i,s) = (text_sections \<alpha>)!index;
         \<sigma> = exec_instr \<alpha> \<Psi> \<phi> i s \<sigma>;
         \<sigma> = exec_assembly \<alpha> lookup_table \<phi> \<Psi> (n-1) \<sigma> in \<sigma>)"
  by (cases n,auto simp add: Let'_def Let_def)
lemmas exec_assembly.simps(2-) [simp del]


end
end
