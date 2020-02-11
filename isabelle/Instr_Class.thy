theory Instr_Class
  imports reassembly_datatypes.MachineDatatypes reassembly_manual_execution.BitVectors
begin
  
datatype instr_class = 
  Mem_Read register bv
  | Mem_Write register bv
  | Bounds_Check register
  | Branch "address list"
  | Reg_Write register bv
  | Stack_Expand int
  | Stack_Contract int
  | Stack_Read register int
  | Stack_Write int bv
  | Ret

(* fun write_reg :: "register \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> state" *)

fun run_instr :: "instr_class \<Rightarrow> state \<Rightarrow> state"
  where
    "run_instr (Mem_Read reg bv) \<sigma> = write_reg reg (cat_bytes (read_bytes (mem \<sigma>) ((\<langle>63,0\<rangle>fst bv), 64)))   \<sigma>"
  | "run_instr (Mem_Write reg bv) \<sigma> = \<sigma>\<lparr>mem := write_bytes (fst (read_reg \<sigma> reg), (bytes_of 0 64 (\<langle>63,0\<rangle>fst bv))) (mem \<sigma>)\<rparr>"
  | "run_instr (Bounds_Check reg) \<sigma> = write_reg reg (fst (read_reg \<sigma> reg) AND mask 32) \<sigma>"
  | "run_instr (Branch addrs) \<sigma> = \<sigma>"
  | "run_instr (Reg_Write reg bv) \<sigma> = write_reg reg (\<langle>63,0\<rangle>fst bv) \<sigma>"
  | "run_instr (Stack_Expand i) \<sigma> = write_reg rsp (add (read_reg \<sigma> rsp) (word_of_int i)) \<sigma>"
(*  | "run_instr (Mem_Write reg (v * l)) \<sigma> =
      let addr = fst (read_reg \<sigma> reg); val = read_bytes \<sigma> 
        \<sigma>\<lparr>mem := write_bytes (addr * val) (mem \<sigma>)\<rparr>" *)
 (* | "run_instr (Reg_Write (General bm r) bv) \<sigma> = write_reg (General bm r) ((<63,0>fst bv)::64 word) \<sigma>"*)

end