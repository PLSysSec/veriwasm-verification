theory Instr_Class
  imports reassembly_datatypes.MachineDatatypes reassembly_manual_execution.BitVectors
begin

type_synonym flags_t = "flag \<Rightarrow> bool"

datatype instr_class = 
  Mem_Read register bv flags_t
  | Mem_Write register bv flags_t
  | Bounds_Check register flags_t
  | Branch "address list" flags_t
  | Reg_Write register bv flags_t
  | Stack_Expand int flags_t
  | Stack_Contract int flags_t
  | Stack_Read register int flags_t
  | Stack_Write int bv flags_t
  | Ret flags_t
  | Call flags_t

(* fun write_reg :: "register \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> state" *)

fun update_flags :: "flags_t \<Rightarrow> state \<Rightarrow> state"
  where "update_flags f \<sigma> = \<sigma>\<lparr>flags := f\<rparr>"

fun run_instr :: "instr_class \<Rightarrow> state \<Rightarrow> state"
  where
    "run_instr (Mem_Read reg bv f) \<sigma> =
    (let data = (cat_bytes (read_bytes (mem \<sigma>) ((\<langle>63,0\<rangle>fst bv), 64))) in
       update_flags f (write_reg reg data \<sigma>))"
  | "run_instr (Mem_Write reg bv f) \<sigma> =
    (let loc = fst (read_reg \<sigma> reg);
         data = (bytes_of 0 64 (fst bv)) in
       update_flags f (\<sigma>\<lparr>mem := write_bytes (loc, data) (mem \<sigma>)\<rparr>))" 
  | "run_instr (Bounds_Check reg f) \<sigma> =
    (let data =  (fst (read_reg \<sigma> reg) AND mask 32) in
       update_flags f (write_reg reg data \<sigma>))" 
  | "run_instr (Branch addrs f) \<sigma> = update_flags f \<sigma>" 
  | "run_instr (Reg_Write reg bv f) \<sigma> = update_flags f (write_reg reg (\<langle>63,0\<rangle>fst bv) \<sigma>)" 
  | "run_instr (Stack_Expand i f) \<sigma> =
    (let rsp_reg = General SixtyFour rsp;
         loc = (fst (read_reg \<sigma> rsp_reg)) + (word_of_int i) in
       update_flags f (write_reg rsp_reg loc \<sigma>))" 
  | "run_instr (Stack_Contract i f) \<sigma> =
    (let rsp_reg = General SixtyFour rsp;
         loc = (fst (read_reg \<sigma> rsp_reg)) - (word_of_int i) in
       update_flags f (write_reg rsp_reg loc \<sigma>))" 
  | "run_instr (Stack_Read reg i f) \<sigma> =
    (let rbp_reg = General SixtyFour rbp;
         loc = (fst (read_reg \<sigma> rbp_reg)) + (word_of_int i);
         data = (cat_bytes (read_bytes (mem \<sigma>) (loc, 64))) in
       update_flags f (write_reg reg data \<sigma>))" 
  | "run_instr (Stack_Write i bv f) \<sigma> = 
    (let rbp_reg = General SixtyFour rbp;
         loc = (fst (read_reg \<sigma> rbp_reg)) + (word_of_int i);
         data = (word_to_bytes (fst bv) 64) in
       update_flags f (\<sigma>\<lparr>mem := (write_bytes (loc, data) (mem \<sigma>))\<rparr>))" 
  | "run_instr (Ret f) \<sigma> = update_flags f \<sigma>"
  | "run_instr (Call f) \<sigma> = update_flags f \<sigma>" 

end