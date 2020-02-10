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

theory Manual_Execution              
imports "../InstructionSemantics_parser/Chum_Parser"
begin

fun nat_to_bit_mask :: "nat \<Rightarrow> bit_mask"
  where "nat_to_bit_mask i = 
  (if (i = 8) then ( Eight )
       else( if (i = 16) then ( Sixteen )
       else( if (i = 32) then ( ThirtyTwo )           
       else( if (i = 64) then ( SixtyFour )           
       else( if (i = 128) then ( OneHundredTwentyEight )           
       else( if (i = 256) then ( TwoHundredFiftySix )                       
       else undefined ))))))"


definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "\<otimes>" 36)
  where "a \<otimes> b \<equiv> (a \<and> \<not>b) \<or> (\<not>a \<and> b)"

definition parity :: "'a::len0 word \<Rightarrow> bool"
  where "parity a \<equiv> fold (\<otimes>) (drop (LENGTH('a) - 8) (to_bl a)) True"

definition parity_offset :: "'a::len0 word \<Rightarrow> bool"
  where "parity_offset bvf  \<equiv> fold (\<otimes>) (take 8 (drop (LENGTH('a) - 16) (to_bl bvf))) True"


locale execution_context = abstract_float +
  fixes funcs :: "string \<Rightarrow> (state \<Rightarrow> state) option"
begin

abbreviation get_rip :: "state \<Rightarrow> 64 word"
  where "get_rip \<sigma> \<equiv> regs \<sigma> rip"

definition incr_rip :: "nat \<Rightarrow> state \<Rightarrow> state"
  where "incr_rip n \<sigma> \<equiv> \<sigma>\<lparr>regs := (regs \<sigma>)(rip := (get_rip \<sigma> + of_nat n))\<rparr>"
 
fun get_size_of_reg :: "register \<Rightarrow> nat"
  where "get_size_of_reg (General SixtyFour _)  = 64" 
  | "get_size_of_reg (General ThirtyTwo _)  = 32"
  | "get_size_of_reg (General Sixteen _)  = 16"
  | "get_size_of_reg (General EightHigh _)  = 8"
  | "get_size_of_reg (General EightLow _)  = 8"
  | "get_size_of_reg (SIMD OneHundredTwentyEight _ _ _ _)  = 128"
  | "get_size_of_reg (SIMD TwoHundredFiftySix _ _ _ _)  = 256"



fun bv_put:: "assembly \<Rightarrow> operand_dest \<Rightarrow> bv \<Rightarrow> state \<Rightarrow> state"
  where
  "bv_put \<alpha> (Reg (General SixtyFour reg)) bv \<sigma> = write_reg (General SixtyFour reg) ((\<langle>63,0\<rangle>fst bv)::64 word) \<sigma>"
| "bv_put \<alpha> (Reg (General ThirtyTwo reg)) bv \<sigma> = write_reg (General SixtyFour reg) (cat_bytes ((replicate 4 0) @ (\<lbrace>3,0\<rbrace> ((\<langle>63,0\<rangle>fst bv)::64 word) )  )  ) \<sigma>"
| "bv_put \<alpha> (Reg (General Sixteen reg))   bv \<sigma> = write_reg (General SixtyFour reg) (cat_bytes ( \<lbrace>7,2\<rbrace>(get (regs \<sigma>) reg) @ (\<lbrace>1,0\<rbrace> ( ((\<langle>63,0\<rangle>fst bv)::64 word))))  ) \<sigma>"
| "bv_put \<alpha> (Reg (General EightHigh reg)) bv \<sigma> = write_reg (General SixtyFour reg) (cat_bytes ( \<lbrace>7,2\<rbrace>(get (regs \<sigma>) reg) @ (\<lbrace>1,1\<rbrace> ( ((\<langle>63,0\<rangle>fst bv)::64 word))) @ \<lbrace>0,0\<rbrace>(get (regs \<sigma>) reg))  ) \<sigma>"
| "bv_put \<alpha> (Reg (General EightLow reg))  bv \<sigma> = write_reg (General SixtyFour reg) (cat_bytes ( \<lbrace>7,1\<rbrace>(get (regs \<sigma>) reg) @ (\<lbrace>0,0\<rbrace> ( ((\<langle>63,0\<rangle>fst bv)::64 word))))  ) \<sigma>"
| "bv_put \<alpha> (Reg (SIMD OneHundredTwentyEight w4 w3 w2 w1)) bv \<sigma>  = write_reg (General SixtyFour w2) (\<langle>127,64\<rangle>fst bv) (write_reg (General SixtyFour w1) ((\<langle>63,0\<rangle>fst bv)::64 word) \<sigma>)"
| "bv_put \<alpha> (Reg (SIMD TwoHundredFiftySix w4 w3 w2 w1)) bv \<sigma>  = 
        write_reg (General SixtyFour w4) ((\<langle>255,192\<rangle>fst bv)::64 word) (
          write_reg (General SixtyFour w3) ((\<langle>191,128\<rangle>fst bv)::64 word) ( 
            write_reg (General SixtyFour w2) ((\<langle>127,64\<rangle>fst bv)::64 word) (
              write_reg (General SixtyFour w1) ((\<langle>63,0\<rangle>fst bv)::64 word) \<sigma>)))"
| "bv_put \<alpha> (Memory TwoHundredFiftySix a) bv \<sigma> = 
              (let  
                bs = \<lbrace>31,0\<rbrace> ((\<langle>255,0\<rangle>fst bv)::256 word)
              in
                let' address0 = resolve_address \<alpha> \<sigma> a;
                     m = write_block (address0 \<rhd> rev bs) (mem \<sigma>)
                in \<sigma>\<lparr>mem := m\<rparr>)"
| "bv_put \<alpha> (Memory OneHundredTwentyEight a) bv \<sigma> = 
             (let  
                bs = \<lbrace>15,0\<rbrace> ((\<langle>127,0\<rangle>fst bv)::128 word)
              in
                let' address0 = resolve_address \<alpha> \<sigma> a;
                     m = write_block (address0 \<rhd> rev bs) (mem \<sigma>)
                in \<sigma>\<lparr>mem := m\<rparr>)"
| "bv_put \<alpha> (Memory s a) bv \<sigma> = 
             ( 
             let  
                bs = \<lbrace>((mask_to_size s) div 8)-1,0\<rbrace> ((\<langle>63,0\<rangle>fst bv)::64 word)
             in
                let' address = resolve_address \<alpha> \<sigma> a;
                  m = write_block (address \<rhd> rev (drop (length bs - ((mask_to_size s) div 8)) bs)) (mem \<sigma>)
                in \<sigma>\<lparr>mem := m\<rparr>            
            )"

fun put :: "assembly \<Rightarrow> operand_dest \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> state"
  where "put \<alpha> od d \<sigma> = bv_put \<alpha> od (\<langle>63,0\<rangle>d,64::nat) \<sigma>"


(* Assumes that the operands are the same size. The size is determined by the destination.  *) 
definition apply_binop :: "assembly \<Rightarrow> (64 word \<Rightarrow> 64 word \<Rightarrow> 64 word) \<Rightarrow> (64 word \<Rightarrow> 64 word \<Rightarrow> bool) option \<Rightarrow> operand_dest \<Rightarrow> operand_src \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where "apply_binop \<alpha> f cf dst src s \<sigma> \<equiv>
    let' (d0,s0) = data_from_src \<alpha> \<sigma> src;
         (d1,s1) = data_from_storage \<alpha>  \<sigma> dst;
         r  = f d1 d0;
         \<sigma>  = put \<alpha> dst r \<sigma>;
         \<sigma>  = write_flg flag_zf (r = 0) \<sigma> ;
         \<sigma>  = case cf of None \<Rightarrow> write_flg flag_cf undefined \<sigma> | Some cf \<Rightarrow> write_flg flag_cf (cf d1 d0) \<sigma>
      in
         incr_rip s \<sigma>"

definition jmp :: "assembly \<Rightarrow> bool \<Rightarrow> char list \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where "jmp \<alpha> flg x s \<sigma> \<equiv>
      if flg then
        let' lookup = label_to_address \<alpha> x in                                                            
          case lookup of
            None \<Rightarrow> Code.abort (STR ''exec_instr: unknown label'') (\<lambda> _ . \<sigma>)
          | Some a \<Rightarrow> write_reg (General SixtyFour rip) a \<sigma>
      else
        incr_rip s \<sigma>"




fun manual_exec_nullary_instr  :: "assembly \<Rightarrow> instr_mnemonic \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where
    "manual_exec_nullary_instr \<alpha> i s \<sigma> = (
        case i of (IS_80188 Leave) \<Rightarrow>
        (let' (* first, move rbp to rsp *)
             (d,_) = read_reg \<sigma> (General SixtyFour rbp);
             \<sigma> = put \<alpha> (Reg (General SixtyFour rsp)) d \<sigma> ;
             (* then pop rbp *)
             (d,_) = read_memory \<alpha> \<sigma> 64 (A_FromReg (General SixtyFour rsp));
             \<sigma> = put \<alpha> (Reg (General SixtyFour rbp)) d \<sigma>;
             (d,_) = read_reg \<sigma> (General SixtyFour rsp);
             \<sigma> = put \<alpha> (Reg (General SixtyFour rsp)) (d+8) \<sigma> in
            incr_rip s \<sigma>)
        | IS_8088 Ret \<Rightarrow> let'
          \<comment> \<open>first, get the return address\<close>
          (ret, _) = read_memory \<alpha> \<sigma> 64 (A_FromReg (General SixtyFour rsp));
          \<comment> \<open>then increment the stack pointer\<close>
          (d, _) = read_reg \<sigma> (General SixtyFour rsp);
          \<sigma> = put \<alpha> (Reg (General SixtyFour rsp)) (d+8) \<sigma>
          \<comment> \<open>then jump to the return address, which is assumed to point to a valid label\<close>
        in
          write_reg (General SixtyFour rip) ret \<sigma>)"
     
primrec (nonexhaustive) manual_exec_unary_instr_IS_8088  :: "assembly \<Rightarrow> instr_mnemonic_8088 \<Rightarrow> operand_src \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where
    "manual_exec_unary_instr_IS_8088 \<alpha> Push st s \<sigma> = 
               (case st of (Storage ((Reg reg))) \<Rightarrow>
                (let' (* first, decrement the stack pointer *)                                 
                  (d,_) = read_reg \<sigma> (General SixtyFour rsp);
                  \<sigma> = put \<alpha> (Reg (General SixtyFour rsp)) (d - (of_nat (get_size_of_reg reg div 8))) \<sigma> ;
                  (* then, move the value from the reg to that address *)
                  (d,s0) = read_reg \<sigma> reg;
                  \<sigma> = put \<alpha> (Memory (nat_to_bit_mask s0) (A_FromReg (General SixtyFour rsp))) d \<sigma>
                in
                incr_rip s \<sigma>))"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Pop st s \<sigma> = 
                (case st of (Storage ((Reg reg))) \<Rightarrow>
                  (let' (* first, move the value from the address to the reg *)
                    (d,_) = read_memory \<alpha> \<sigma> (get_size_of_reg reg)  (A_FromReg (General SixtyFour rsp));
                    \<sigma> = put \<alpha> (Reg (reg)) d \<sigma>;
                    (* then, increment the stack pointer *)
                    (d,_) = read_reg \<sigma> (General SixtyFour rsp) ;
                    \<sigma> = put \<alpha> (Reg (General SixtyFour rsp)) (d + (of_nat (get_size_of_reg reg div 8))) \<sigma>
                  in incr_rip s \<sigma>))"      
  |  "manual_exec_unary_instr_IS_8088 \<alpha> Div src s \<sigma> =
  (case src of (Storage (Reg (General SixtyFour reg64))) \<Rightarrow>
    let' (d0,s0) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour rax)));
         (d1,s1) = data_from_storage \<alpha> \<sigma> (Reg (General SixtyFour reg64));
         \<sigma>  = put \<alpha> (Reg (General SixtyFour rax)) (d0 div d1) \<sigma>;
         \<sigma>  = put \<alpha> (Reg (General SixtyFour rdx)) (d0 mod d1) \<sigma>;
         \<sigma>  = incr_rip s \<sigma> 
      in
         \<sigma>
    | _ \<Rightarrow> undefined)"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Call a s \<sigma> =
      (case a of Immediate _ (ImmLabel func) \<Rightarrow> let'
        funopt = funcs func;
        \<sigma> = case funopt of None \<Rightarrow> let'
          \<comment> \<open>first, get the return address\<close>
          addr = get_rip \<sigma> + of_nat s;
          \<comment> \<open>then decrement the stack pointer\<close>
          (d, _) = read_reg \<sigma> (General SixtyFour rsp);
          \<sigma> = put \<alpha> (Reg (General SixtyFour rsp)) (d - 8) \<sigma>;
          \<comment> \<open>then move the return address to that address\<close>
          \<sigma> = put \<alpha> (Memory SixtyFour (A_FromReg (General SixtyFour rsp))) addr \<sigma>
        in
          write_reg (General SixtyFour rip) (the (label_to_address \<alpha> func)) \<sigma>
        | Some fun \<Rightarrow> let \<sigma>' = fun \<sigma> in incr_rip s (\<sigma>'\<lparr>regs := (regs \<sigma>')(rip := get_rip \<sigma>)\<rparr>)
      in \<sigma>)"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Ja st s \<sigma> = 
               (case st of (Immediate _ (ImmLabel x)) \<Rightarrow>
                (let' cf  = read_flg \<sigma> flag_cf;
                      zf  = read_flg \<sigma> flag_zf;
                      flg = \<not>cf \<and> \<not>zf
                in
                jmp \<alpha> flg x s \<sigma>))"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Jae st s \<sigma> = 
               (case st of (Immediate _ (ImmLabel x)) \<Rightarrow>
                (let' cf  = read_flg \<sigma> flag_cf;
                      flg = \<not>cf
                in
                jmp \<alpha> flg x s \<sigma>))"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Jb st s \<sigma> = 
               (case st of (Immediate _ (ImmLabel x)) \<Rightarrow>
                (let' flg = read_flg \<sigma> flag_cf
                in
                jmp \<alpha> flg x s \<sigma>))"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Jbe st s \<sigma> = 
               (case st of (Immediate _ (ImmLabel x)) \<Rightarrow>
                (let' cf  = read_flg \<sigma> flag_cf;
                      zf  = read_flg \<sigma> flag_zf;
                      flg = cf \<or> zf
                in
                jmp \<alpha> flg x s \<sigma>))"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Je st s \<sigma> = 
               (case st of (Immediate _ (ImmLabel x)) \<Rightarrow>
                (let'
                       flg = read_flg \<sigma> flag_zf
                in
                jmp \<alpha> flg x s \<sigma>))"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Jg st s \<sigma> =
      (case st of (Immediate _ (ImmLabel x)) \<Rightarrow>
        let' flag_zf = read_flg \<sigma> flag_zf;
             flag_sf = read_flg \<sigma> flag_sf;
             flag_of = read_flg \<sigma> flag_of;
             f = \<not>flag_zf \<and> (flag_sf = flag_of)
         in
        jmp \<alpha> f x s \<sigma>)"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Jle st s \<sigma> =
      (case st of (Immediate _ (ImmLabel x)) \<Rightarrow>
        let' flag_zf = read_flg \<sigma> flag_zf;
             flag_sf = read_flg \<sigma> flag_sf;
             flag_of = read_flg \<sigma> flag_of;
             f = flag_zf \<or> (flag_sf \<noteq> flag_of)
         in
        jmp \<alpha> f x s \<sigma>)"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Jne st s \<sigma> = 
               (case st of (Immediate _ (ImmLabel x)) \<Rightarrow>
                (let'
                    flg = read_flg \<sigma> flag_zf
                in
                jmp \<alpha> (\<not>flg) x s \<sigma>))"
  | "manual_exec_unary_instr_IS_8088 \<alpha> Jmp st \<sigma> = 
               (case st of (Immediate _ (ImmLabel x)) \<Rightarrow>
                jmp \<alpha> True x \<sigma>)"

primrec (nonexhaustive) manual_exec_unary_instr  :: "assembly \<Rightarrow> instr_mnemonic \<Rightarrow> operand_src \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where
    "manual_exec_unary_instr \<alpha> (IS_8088 i) st s \<sigma> = manual_exec_unary_instr_IS_8088 \<alpha> i st s \<sigma>" 


text \<open>
  For the compare instruction, we set the flags as follows:
\<close>
definition sub_overflow_flag
  where "sub_overflow_flag a b \<equiv> a \<noteq> b \<and> (a <s 0 \<and> \<not>b <s 0 \<and> \<not>(a - b <s 0)) \<or>
                                     (b <s 0 \<and> \<not>a <s 0 \<and> (a - b) <s 0)"
definition sub_sign_flag
  where "sub_sign_flag a b \<equiv> if sub_overflow_flag a b then \<not>(a <s 0) else a <s b"

fun get_bit_mode :: "operand_dest \<Rightarrow> nat"
  where 
    "get_bit_mode (Reg (General ThirtyTwo _)) = 32"
  | "get_bit_mode (Reg (General SixtyFour _)) = 64"
  | "get_bit_mode (Reg (General Sixteen _)) = 64"
  | "get_bit_mode (Reg (General EightHigh _)) = 8"
  | "get_bit_mode (Reg (General Eight _)) = 8"
  | "get_bit_mode (Memory s _) = (mask_to_size s)"
  | "get_bit_mode _ = undefined"


primrec (nonexhaustive) manual_exec_binary_instr_IS_8088 :: "assembly \<Rightarrow> instr_mnemonic_8088 \<Rightarrow> operand_dest \<Rightarrow> operand_src  \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where
    "manual_exec_binary_instr_IS_8088 \<alpha> Xor dst src s \<sigma> = apply_binop \<alpha>   (XOR) None dst src s \<sigma>"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> And dst src s \<sigma> = apply_binop \<alpha>  (AND) None dst src s \<sigma>"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> Or dst src s \<sigma> = apply_binop \<alpha>   (OR) None dst src s \<sigma>"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> Add dst src s \<sigma> = apply_binop \<alpha>  (+) None dst src s \<sigma>"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> Sub dst src s \<sigma> = apply_binop \<alpha>  (-) None dst src s \<sigma>"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> Shl dst src s \<sigma> = apply_binop \<alpha>  (\<lambda> x y . x << unat y) None dst src s \<sigma>"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> Shr dst src s \<sigma> = apply_binop \<alpha>  (\<lambda> x y . x >> unat y) None dst src s \<sigma>"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> Imul dst src s \<sigma> = apply_binop \<alpha> ( *) None dst src s \<sigma>"
  | "manual_exec_binary_instr_IS_8088 \<alpha> Sar dst src s \<sigma> =
  (case (dst,src) of (Reg (General ThirtyTwo _), (Storage (Reg (General EightLow _)))) \<Rightarrow>
              (let' (d1,_) = data_from_src \<alpha> \<sigma> src;
                    arg1 = unat (\<langle>7,0\<rangle>d1::8 word) ;
                    (d0,_) = data_from_storage \<alpha> \<sigma> dst;
                    arg0 = (\<langle>31,0\<rangle>d0::32 word);
                    d = arg0 >>> arg1;
                    \<sigma> = put \<alpha> dst (ucast d) \<sigma>; 
                    \<sigma> = write_flg flag_zf (d = (0::32 word)) \<sigma>;
                    \<sigma> = write_flg flag_pf undefined \<sigma>;
                    \<sigma> = write_flg flag_cf undefined \<sigma>;
                    \<sigma> = write_flg flag_of undefined \<sigma>; 
                    \<sigma> = write_flg flag_sf undefined \<sigma>
                in
               incr_rip s \<sigma>))"

  |  "manual_exec_binary_instr_IS_8088 \<alpha> Lea dst src s \<sigma> =
      (case src of (Storage (Memory _ adres))  \<Rightarrow> 
          (let' 
            a = resolve_address \<alpha> \<sigma> adres; 
            \<sigma> = put \<alpha> dst a \<sigma> in incr_rip s \<sigma>))"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> Test dst src s \<sigma> = 
                (let'
                    zz = read_flg (apply_binop \<alpha> (AND) None dst src s \<sigma>) flag_zf;
                    \<sigma>  = write_flg flag_zf zz \<sigma> 
                 in incr_rip s \<sigma>)"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> Cmp dst src s \<sigma> =
      (if get_bit_mode dst = 8 then
                (let'
                    (a::8 word) = \<langle>7,0\<rangle>(fst (data_from_storage \<alpha> \<sigma> dst));
                    (b::8 word) = \<langle>7,0\<rangle>(fst (data_from_src \<alpha> \<sigma> src));
                    \<sigma>  = write_flg flag_zf (a = b) \<sigma>;
                    \<sigma>  = write_flg flag_cf (a < b) \<sigma>;
                    \<sigma>  = write_flg flag_sf (sub_sign_flag a b) \<sigma>;
                    \<sigma>  = write_flg flag_of (sub_overflow_flag a b) \<sigma> 
                 in incr_rip s \<sigma>)
        else if get_bit_mode dst = 32 then
                (let'
                    (a::32 word) = \<langle>31,0\<rangle>(fst (data_from_storage \<alpha> \<sigma> dst));
                    (b::32 word) = \<langle>31,0\<rangle>(fst (data_from_src \<alpha> \<sigma> src));
                    \<sigma>  = write_flg flag_zf (a = b) \<sigma>;
                    \<sigma>  = write_flg flag_cf (a < b) \<sigma>;
                    \<sigma>  = write_flg flag_sf (sub_sign_flag a b) \<sigma>;
                    \<sigma>  = write_flg flag_of (sub_overflow_flag a b) \<sigma> 
                 in incr_rip s \<sigma>)
        else if get_bit_mode dst = 64 then
                (let'
                    (a::64 word) = \<langle>63,0\<rangle>(fst (data_from_storage \<alpha> \<sigma> dst));
                    (b::64 word) = \<langle>63,0\<rangle>(fst (data_from_src \<alpha> \<sigma> src));
                    \<sigma>  = write_flg flag_zf (a = b) \<sigma>;
                    \<sigma>  = write_flg flag_cf (a < b) \<sigma>;
                    \<sigma>  = write_flg flag_sf (sub_sign_flag a b) \<sigma>;
                    \<sigma>  = write_flg flag_of (sub_overflow_flag a b) \<sigma> 
                 in incr_rip s \<sigma>)
         else undefined)"
  |  "manual_exec_binary_instr_IS_8088 \<alpha> Mov dst src s \<sigma> = 
              (let' (d,_) = data_from_src \<alpha> \<sigma> src;
                  \<sigma> = put \<alpha> dst d \<sigma> in
          incr_rip s \<sigma>)"    


definition bsr :: "'a::len0 word \<Rightarrow> nat" (* bit scan reverse *)
  where "bsr a \<equiv> (GREATEST i . i < LENGTH('a) \<and> a !! i)"

primrec (nonexhaustive) manual_exec_binary_instr_IS_80386 :: "assembly \<Rightarrow> instr_mnemonic_80386 \<Rightarrow> operand_dest \<Rightarrow> operand_src \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where  "manual_exec_binary_instr_IS_80386 \<alpha> Movzx dst src s \<sigma> =
  (case dst of (Reg (General rs dstreg)) \<Rightarrow>
              (let' (d,_) = data_from_src \<alpha> \<sigma> src;
                    \<sigma> = put \<alpha> (Reg (General rs dstreg)) d \<sigma> 
                in
               incr_rip s \<sigma>))"
       | "manual_exec_binary_instr_IS_80386 \<alpha> Bsr dst src s \<sigma> =
  (case dst of (Reg (General ThirtyTwo dstreg)) \<Rightarrow>
              (let' (d,_) = data_from_src \<alpha> \<sigma> src;
                    d' = ucast (of_nat (bsr (\<langle>31,0\<rangle>d::32 word)) :: 32 word) ;
                    \<sigma> = put \<alpha> (Reg (General ThirtyTwo dstreg)) d' \<sigma>; 
                    \<sigma> = write_flg flag_zf (\<langle>31,0\<rangle>d = (0::32 word)) \<sigma>;
                    \<sigma> = write_flg flag_pf undefined \<sigma>;
                    \<sigma> = write_flg flag_cf undefined \<sigma>;
                    \<sigma> = write_flg flag_of undefined \<sigma>; 
                    \<sigma> = write_flg flag_sf undefined \<sigma>
                in
               incr_rip s \<sigma>)
            | (Reg (General SixtyFour dstreg)) \<Rightarrow>
              (let' (d,_) = data_from_src \<alpha> \<sigma> src;
                    d' = of_nat (bsr (\<langle>63,0\<rangle>d::64 word)) ;
                    \<sigma> = put \<alpha> (Reg (General SixtyFour dstreg)) d' \<sigma>; 
                    \<sigma> = write_flg flag_zf (\<langle>63,0\<rangle>d = (0::64 word)) \<sigma>;
                    \<sigma> = write_flg flag_pf undefined \<sigma>;
                    \<sigma> = write_flg flag_cf undefined \<sigma>;
                    \<sigma> = write_flg flag_of undefined \<sigma>; 
                    \<sigma> = write_flg flag_sf undefined \<sigma>
                in
               incr_rip s \<sigma>)
            | (Reg (General Sixteen dstreg)) \<Rightarrow>
              (let' (d,_) = data_from_src \<alpha> \<sigma> src;
                    d' = ucast (of_nat (bsr (\<langle>15,0\<rangle>d::16 word)) :: 16 word) ;
                    \<sigma> = put \<alpha> (Reg (General Sixteen dstreg)) d' \<sigma>; 
                    \<sigma> = write_flg flag_zf (\<langle>15,0\<rangle>d = (0::16 word)) \<sigma>;
                    \<sigma> = write_flg flag_pf undefined \<sigma>;
                    \<sigma> = write_flg flag_cf undefined \<sigma>;
                    \<sigma> = write_flg flag_of undefined \<sigma>; 
                    \<sigma> = write_flg flag_sf undefined \<sigma>
                in
               incr_rip s \<sigma>))"



primrec (nonexhaustive) manual_exec_binary_instr_IS_PentiumMMX_MMX :: "assembly \<Rightarrow> instr_mnemonic_pentiummmx_mmx \<Rightarrow> operand_dest \<Rightarrow> operand_src \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where  "manual_exec_binary_instr_IS_PentiumMMX_MMX \<alpha> Movq dst src s \<sigma> =
  (case dst of (Reg (General SixtyFour dst)) \<Rightarrow> case src of (Storage (Reg (SIMD OneHundredTwentyEight _ _ srch srcl))) \<Rightarrow>
           (let'
              (d,_) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour srcl))); 
              \<sigma> = put \<alpha> (Reg (General SixtyFour dst)) d \<sigma>
            in incr_rip s \<sigma>))"

primrec (nonexhaustive) manual_exec_binary_instr_IS_SSE2_SIMD :: "assembly \<Rightarrow> instr_mnemonic_sse2_simd \<Rightarrow> operand_dest \<Rightarrow> operand_src \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where  
        "manual_exec_binary_instr_IS_SSE2_SIMD \<alpha> Movapd dst src s \<sigma> =
          (case dst of (Reg (SIMD OneHundredTwentyEight _ _ dsth dstl)) \<Rightarrow> case src of (Storage (Reg (SIMD OneHundredTwentyEight _ _ srch srcl))) \<Rightarrow>
            ( let' 
              (d,_) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour srcl))); 
                  \<sigma> = put \<alpha> (Reg (General SixtyFour dstl)) d \<sigma>;
              (d,_) = data_from_src \<alpha> \<sigma> (Storage (Reg  (General SixtyFour srch))); 
                  \<sigma> = put \<alpha> (Reg (General SixtyFour dsth)) d \<sigma>
              in incr_rip s \<sigma>))"
      |  "manual_exec_binary_instr_IS_SSE2_SIMD \<alpha> Mulsd dst src s \<sigma> =
          (case dst of (Reg (SIMD OneHundredTwentyEight _ _ dsth dstl)) \<Rightarrow> case src of (Storage (Reg (SIMD OneHundredTwentyEight _ _ srch srcl))) \<Rightarrow>
                    (apply_binop \<alpha> ( *\<^sup>f) None (Reg (General SixtyFour dstl)) (Storage (Reg (General SixtyFour srcl))) s \<sigma>))"
      |  "manual_exec_binary_instr_IS_SSE2_SIMD \<alpha> Divsd dst src s \<sigma> =
          (case dst of (Reg (SIMD OneHundredTwentyEight _ _ dsth dstl)) \<Rightarrow> case src of (Storage (Reg (SIMD OneHundredTwentyEight _ _ srch srcl))) \<Rightarrow>
                    (apply_binop \<alpha> (div\<^sup>f) None (Reg (General SixtyFour dstl)) (Storage (Reg (General SixtyFour srcl))) s \<sigma>))"
      |  "manual_exec_binary_instr_IS_SSE2_SIMD \<alpha> Movsd dst src s \<sigma> =
            (case (dst,src) of (Reg (SIMD OneHundredTwentyEight _ _ dsth dstl),Storage (Memory i src)) \<Rightarrow>
           let'
            (d,_) = data_from_src \<alpha> \<sigma> (Storage (Memory i src)); 
            \<sigma> = put \<alpha> (Reg (General SixtyFour dstl)) d \<sigma>;
            \<sigma> = put \<alpha> (Reg (General SixtyFour dsth)) 0 \<sigma>
           in incr_rip s \<sigma>
          | (Reg (SIMD OneHundredTwentyEight _ _ dsth dstl), Storage (Reg (SIMD OneHundredTwentyEight _ _ srch srcl))) \<Rightarrow>
           let' 
            (d,_) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour srcl))); 
            \<sigma> = put \<alpha> (Reg (General SixtyFour dstl)) d \<sigma>
           in incr_rip s \<sigma>
          | (Memory i dst, Storage (Reg (SIMD OneHundredTwentyEight _ _ srch srcl))) \<Rightarrow>
           let' 
            (d,_) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour srcl))); 
            \<sigma> = put \<alpha> (Memory i dst) d \<sigma> 
           in incr_rip s \<sigma>)" 
      |  "manual_exec_binary_instr_IS_SSE2_SIMD \<alpha> Ucomisd dst src s \<sigma> =
          (case (dst,src) of (Reg (SIMD OneHundredTwentyEight _ _ _ dstl),Storage (Reg (SIMD OneHundredTwentyEight _ _ _ srcl))) \<Rightarrow>
           let' (d0,_) = data_from_src \<alpha> \<sigma> (Storage (Reg (General SixtyFour srcl)));
                (d1,_) = data_from_storage \<alpha> \<sigma> (Reg (General SixtyFour dstl));
                cmp = float_ucmp d0 d1;
                \<sigma>  = write_flg flag_zf (cmp \<in> {Unordered, EQ}) \<sigma>;
                \<sigma>  = write_flg flag_pf (cmp = Unordered) \<sigma>;
                \<sigma>  = write_flg flag_cf (cmp \<in> {Unordered, LT}) \<sigma>;
                \<sigma>  = write_flg flag_of False \<sigma>; 
                \<sigma>  = write_flg flag_sf False \<sigma>
                 in incr_rip s \<sigma>
          | (Reg (SIMD OneHundredTwentyEight _ _ _ dstl),Storage (Memory i src)) \<Rightarrow>
           let' (d0,_) = data_from_src \<alpha> \<sigma> (Storage (Memory i src));
                (d1,_) = data_from_storage \<alpha> \<sigma> (Reg (General SixtyFour dstl));
                cmp = float_ucmp d0 d1;
                \<sigma>  = write_flg flag_zf (cmp \<in> {Unordered, EQ}) \<sigma>;
                \<sigma>  = write_flg flag_pf (cmp = Unordered) \<sigma>;
                \<sigma>  = write_flg flag_cf (cmp \<in> {Unordered, LT}) \<sigma>;
                \<sigma>  = write_flg flag_of False \<sigma>; 
                \<sigma>  = write_flg flag_sf False \<sigma>
                 in incr_rip s \<sigma>)"


primrec (nonexhaustive) manual_exec_binary_instr :: "assembly \<Rightarrow> instr_mnemonic \<Rightarrow> operand_dest \<Rightarrow> operand_src \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where
    "manual_exec_binary_instr \<alpha> (IS_8088 i) dst src s \<sigma> = manual_exec_binary_instr_IS_8088 \<alpha> i dst src s \<sigma>" 
  | "manual_exec_binary_instr \<alpha> (IS_80386 i) dst src s \<sigma> = manual_exec_binary_instr_IS_80386 \<alpha> i dst src s \<sigma>" 
  | "manual_exec_binary_instr \<alpha> (IS_PentiumMMX_MMX i) dst src s \<sigma> = manual_exec_binary_instr_IS_PentiumMMX_MMX \<alpha> i dst src s \<sigma>" 
  | "manual_exec_binary_instr \<alpha> (IS_SSE2_SIMD i) dst src s \<sigma> = manual_exec_binary_instr_IS_SSE2_SIMD \<alpha> i dst src s \<sigma>" 

fun manual_exec_ternary_instr  :: "assembly \<Rightarrow> instr_mnemonic \<Rightarrow> operand_dest \<Rightarrow> operand_src  \<Rightarrow> operand_src \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where
    "manual_exec_ternary_instr \<alpha> i dst src1 src2 s \<sigma> = undefined"


primrec (nonexhaustive) manual_exec_instr  :: "assembly \<Rightarrow> instr \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state"
  where
    "manual_exec_instr \<alpha> (Nullary mnemonic) s \<sigma> = manual_exec_nullary_instr \<alpha> mnemonic s \<sigma>"
  | "manual_exec_instr \<alpha> (Unary mnemonic src) s \<sigma> = manual_exec_unary_instr \<alpha> mnemonic src s \<sigma>"
  | "manual_exec_instr \<alpha> (Binary mnemonic dst src) s \<sigma> = manual_exec_binary_instr \<alpha> mnemonic dst src s \<sigma>"
  | "manual_exec_instr \<alpha> (Ternary mnemonic dst src1 src2 ) s \<sigma> = manual_exec_ternary_instr \<alpha> mnemonic dst src1 src2 s \<sigma>"

end
end 
