theory Instr_Class
  imports reassembly_datatypes.MachineDatatypes
begin
  
datatype instr_class = 
  Mem_Read register
  | Mem_Write register address
  | Bound_Checks register
  | Branch "address list"
  | Reg_Write register address
  | Stack_Expand int
  | Stack_Contract int
  | Stack_Read int
  | Stack_Write int address
  | Ret


end