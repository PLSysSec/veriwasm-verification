theory Instr_Class
  imports reassembly_datatypes.MachineDatatypes BitVectors Machine
begin
  
datatype instr_class = 
  Mem_Read register
  | Mem_Write register bv
  | Bound_Checks bv
  | Branch "address list"
  | Reg_Write register bv
  | Stack_Expand int
  | Stack_Contract int
  | Stack_Read int
  | Stack_Write int bv
  | Ret

fun run_instr :: "instr_class \<Rightarrow> state \<Rightarrow> state"
  where
    "run_instr (Mem_Read (General bm r)) \<sigma> = Memory bit_mask address"
  | "run_instr (Reg_Write (General bm r) bv) \<sigma> = write_reg (General bm r) ((<63,0>fst bv)::64 word) \<sigma>"

end