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

(*
This file contains the machinery for obtaining flag_info for assembly code.
Flag info concerns which instructions read which flags.
See, for example, flag_info_RIP_adjusting below, where some information has been added hard-coded and manually.

Based on the learned semantics, this initial flag_info is augmented.
The resulting flag_info is written to a file using function write_flag_info_to_file.
That file can be read using function read_flag_info.


Function create_flag_info_for_assembly will create flag_info specifically for the loaded assembly code.
It produces a mapping from locations (ts,pc) to flag lists.
For example, if this mapping assigns {CF,SF} to (2,5), then instruction 5 in text section 2 will set
the carry- and sign flags.
This means that instruction 6 in that text section reads those flags.
*)




(* BEGIN OBTAINING FLAG_INFO FROM LEARNED SEMANTICS *)
fun instr_mnemonic_from_instr_sig (Nullary_sig (instr_mnemonic)) = instr_mnemonic 
|   instr_mnemonic_from_instr_sig (Unary_sig   (instr_mnemonic,_)) = instr_mnemonic
|   instr_mnemonic_from_instr_sig (Binary_sig  (instr_mnemonic,_,_)) = instr_mnemonic
|   instr_mnemonic_from_instr_sig (Ternary_sig  (instr_mnemonic,_,_,_)) = instr_mnemonic

fun flags_from_bvf (BV_Assignment (_,bv)) = flags_from_bvf bv
| flags_from_bvf (BV_Immediate (_,_)) = []
| flags_from_bvf (BV_Get _) = [] 
| flags_from_bvf (BV_Slice (bv,_,_)) = flags_from_bvf bv
| flags_from_bvf (BV_Unop (_,bv1)) = flags_from_bvf bv1 
| flags_from_bvf (BV_Binop (_,bv1,bv2)) = flags_from_bvf bv1 @ flags_from_bvf bv2
| flags_from_bvf (BV_Ternop (_,bv1,bv2,bv3)) = flags_from_bvf bv1 @ flags_from_bvf bv2 @ flags_from_bvf bv3
| flags_from_bvf (BV_ITE (bf,bv0,bv1)) = flags_from_bf bf @ flags_from_bvf bv0 @ flags_from_bvf bv1
and
  flags_from_bf (B_Eq (bv0,bv1)) = flags_from_bvf bv0 @ flags_from_bvf bv1
| flags_from_bf (B_Flg f) = [f]

fun add_flag_info_from_semantic (ins_sig, bv) x = 
  let val mnemonic = instr_mnemonic_from_instr_sig ins_sig;
      val flags = flags_from_bvf bv 
      fun update [] = [(mnemonic,flags)]
        | update ((mnemonic',flags')::x) =
            (if mnemonic' = mnemonic then
                  ((mnemonic',rem_dups (flags@flags'))::x)
             else (mnemonic',flags') :: update x)
  in
    update x
end    

(*See: http://unixwiz.net/techtips/x86-jumps.html*)
val flag_info_RIP_adjusting = [
  (IS_8088 Jo,[flag_of]),
  (IS_8088 Jno,[flag_of]),
  (IS_8088 Js,[flag_sf]),
  (IS_8088 Jns,[flag_sf]),
  (IS_8088 Je,[flag_zf]),
  (IS_8088 Jz,[flag_zf]),
  (IS_8088 Jne,[flag_zf]),
  (IS_8088 Jnz,[flag_zf]),
  (IS_8088 Jb,[flag_cf]),
  (IS_8088 Jnae,[flag_cf]),
  (IS_8088 Jc,[flag_cf]),
  (IS_8088 Jnb,[flag_cf]),
  (IS_8088 Jae,[flag_cf]),
  (IS_8088 Jnc,[flag_cf]),
  (IS_8088 Jnb,[flag_cf]),
  (IS_8088 Jbe,[flag_cf,flag_zf]),
  (IS_8088 Jna,[flag_cf,flag_zf]),
  (IS_8088 Jae,[flag_cf,flag_zf]),
  (IS_8088 Jnbe,[flag_cf,flag_zf]),
  (IS_8088 Jl,[flag_sf,flag_of]),
  (IS_8088 Jnge,[flag_sf,flag_of]),
  (IS_8088 Jge,[flag_sf,flag_of]),
  (IS_8088 Jnl,[flag_sf,flag_of]),
  (IS_8088 Jle,[flag_zf,flag_sf,flag_of]),
  (IS_8088 Jng,[flag_zf,flag_sf,flag_of]),
  (IS_8088 Jg,[flag_zf,flag_sf,flag_of]),
  (IS_8088 Jnle,[flag_zf,flag_sf,flag_of]),
  (IS_8088 Jp,[flag_pf]),
  (IS_8088 Jpe,[flag_pf]),
  (IS_8088 Jnp,[flag_pf]),
  (IS_8088 Jpo,[flag_pf]),
  (IS_8088 Call, []),
  (IS_8088 Ret, [])
  ]

fun write_flag_info_to_file file_name is =
  let val flag_info = fold add_flag_info_from_semantic is flag_info_RIP_adjusting;
      fun toString_flag_info (mnemonic,flags) = (toLowerString o toString_instr_nmenonic) mnemonic
        ^ " {"
        ^ intercalate "," (map (toLowerString o toString_flag) flags)
        ^ "}";
      val _ = writeFile file_name (intercalate "\n" (map toString_flag_info flag_info))
  in 
    ()
  end



fun scanWord rdr stream =
  case StringCvt.splitl Char.isAlpha rdr stream of
      ("",_) => NONE
    | (w,stream') => SOME(w,stream')

fun scanList_of_Words getc stream =
  let fun scan_remainder getc stream =
    case scanWord getc stream
      of NONE => SOME ([], stream)
       | SOME (x, stream1) =>
    let val stream2 = StringCvt.skipWS getc stream1 in
    case getc stream2
      of NONE => NONE
       | SOME (c1, stream3) =>
    if c1 = #"}" then SOME ([x], stream3) else
    if c1 <> #"," then NONE else
    let val stream4 = StringCvt.skipWS getc stream3 in
    case scan_remainder getc stream4
      of NONE => NONE
       | SOME (xs, stream5) => SOME (x::xs, stream5)
    end
    end in

  case getc stream
    of NONE => NONE
     | SOME (c1, stream1) =>
  let val stream2 = StringCvt.skipWS getc stream1 in
  if c1 <> #"{" then NONE else scan_remainder getc stream2
  end
  end

fun scan_flag_info_line getc stream =
  let val stream = StringCvt.skipWS getc stream in
    case scanWord getc stream
      of NONE => NONE
       | SOME (mnemonic, stream1) =>
    let val stream2 = StringCvt.skipWS getc stream1 in
    case scanList_of_Words getc stream2
      of NONE => NONE
       | SOME (flags, stream3) => 
    SOME ((mnemonic, flags), stream3)
  end
  end

exception Read_Flag_Info

fun read_flag_info filename =
  let val flag_info = readlist filename;
      val parsed_flag_info = map (StringCvt.scanString scan_flag_info_line) flag_info
      fun check NONE = raise Read_Flag_Info
        | check (SOME (mnemonic, flags)) = [(mnemonic, flags)]
  in
    List.concat (map check parsed_flag_info)
  end

(* END OBTAINING FLAG_INFO FROM LEARNED SEMANTICS *)






(* BEGIN ANNOTATING AN ASSEMBLY WITH FLAG_INFO *)

fun lookup_flag_info _ [] = NONE
  | lookup_flag_info m ((mnemonic,flags)::flag_info) =
    if toLowerString m = toLowerString mnemonic then SOME flags else lookup_flag_info m flag_info

val serialize_flag_info =
  map (fn (mnemonic,flags) => ((toLowerString o toString_instr_nmenonic) mnemonic,map (toLowerString o toString_flag) flags))

fun instr_mnemonic_from_instr (Nullary (instr_mnemonic)) = instr_mnemonic 
|   instr_mnemonic_from_instr (Unary   (instr_mnemonic,_)) = instr_mnemonic
|   instr_mnemonic_from_instr (Binary  (instr_mnemonic,_,_)) = instr_mnemonic
|   instr_mnemonic_from_instr (Ternary (instr_mnemonic,_,_,_)) = instr_mnemonic


fun create_flag_info_for_text_section _ _ _ [] = []
  | create_flag_info_for_text_section _ ts pc [_] =
  (* The last instruction of the code does not need to set flags. TODO: discuss. *)
      [(ts,pc,[])]
  | create_flag_info_for_text_section flag_info ts pc (i::i'::is) =
  (* Consider two consecutive instructions i; i'.*)
  let val mnemonic = (toLowerString o toString_instr_nmenonic) (instr_mnemonic_from_instr i)
      val mnemonic' = (toLowerString o toString_instr_nmenonic) (instr_mnemonic_from_instr i')
      val flag_info_of_i =
      case lookup_flag_info mnemonic (serialize_flag_info flag_info_RIP_adjusting) of
          NONE => (* Instruction i is not a jump or call/ret *)
          (case lookup_flag_info mnemonic' flag_info of
              NONE => (* Instruction i' is unknown, we now assume that it does not read flags. *)
                      (ts,pc,[])
            | SOME flags => (* Instruction i' is known, so return the set of flags read by it. *) 
                      (ts,pc,flags)
          )
        | SOME _ => (* Instruction i is a jump or call/ret. Assume it doesn't set flags itself. *)
                    (ts,pc,[])
  in
      flag_info_of_i::(create_flag_info_for_text_section flag_info ts (pc+1) (i'::is))
  end

fun create_flag_info_for_text_sections _ [] _ = []
  | create_flag_info_for_text_sections flag_info ({ts_name = _, instructions = is}::tss) i =
    (create_flag_info_for_text_section flag_info i 0 is)::(create_flag_info_for_text_sections flag_info tss (i+1))

fun create_flag_info_for_assembly flag_info_file_name {text_sections = tss, data_sections = _, labels_to_addresses = _, labels_to_indices = _ } =
  let val flag_info = read_flag_info flag_info_file_name
  in
    create_flag_info_for_text_sections flag_info tss 0
  end

(* For debugging *)
fun toString_flag_info_of_assembly flag_info =
  let fun toString_flags flags = "{" ^ (intercalate "," flags) ^ "}" 
      fun toString_flag_info_of_line (ts,pc,flags) = "(" ^ toString ts ^ "," ^ toString pc ^ "," ^ toString_flags flags ^ ")"
      fun toString_flag_info_of_lines ls = intercalate "\n" (map toString_flag_info_of_line ls)
  in
    intercalate "\n\n" (map toString_flag_info_of_lines flag_info)
  end

(* END ANNOTATING AN ASSEMBLY WITH FLAG_INFO *)

