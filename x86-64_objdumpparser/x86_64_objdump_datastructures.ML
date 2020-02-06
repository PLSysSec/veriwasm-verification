fun mk_objdump_assembly { instruction_list = is, data_sections = ds, labels_to_addresses = lta, current_offset = _ } =
  @{term "assembly.make"}
    $ mk_list @{typ "nat \<times> instr \<times> nat"} (map mk_instruction_list is)
    $ mk_list @{typ "nat \<times> (data_value list)"} (map mk_data_list ds)
    $ mk_list @{typ "string \<times> nat"} (map mk_label lta)
