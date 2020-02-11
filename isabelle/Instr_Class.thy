theory Instr_Class
  imports reassembly_datatypes.MachineDatatypes reassembly_manual_execution.BitVectors
begin
  
datatype instr_class = 
  Mem_Read register bv
  | Mem_Write register bv
  | Bound_Checks bv
  | Branch "address list"
  | Reg_Write register bv
  | Stack_Expand int
  | Stack_Contract int
  | Stack_Read int
  | Stack_Write int bv
  | Ret

(* fun write_reg :: "register \<Rightarrow> 64 word \<Rightarrow> state \<Rightarrow> state" *)

fun run_instr :: "instr_class \<Rightarrow> state \<Rightarrow> state"
  where
    "run_instr (Mem_Read reg b) \<sigma> = write_reg reg (read_bytes (mem \<sigma>) (from_bv (bv_slice 0 64 (fst b)) * 64)) \<sigma>"
(*  | "run_instr (Mem_Write reg (v * l)) \<sigma> = 
      let addr = fst (read_reg \<sigma> reg); val = read_bytes \<sigma> 
        \<sigma>\<lparr>mem := write_bytes (addr * val) (mem \<sigma>)\<rparr>" *)
 (* | "run_instr (Reg_Write (General bm r) bv) \<sigma> = write_reg (General bm r) ((<63,0>fst bv)::64 word) \<sigma>"*)

end