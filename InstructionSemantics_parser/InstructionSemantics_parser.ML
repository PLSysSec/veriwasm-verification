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



signature MyInstructionSemanticsParser =
sig
  val instruction_semantics_parser : string -> theory -> theory
end

(*
  The following is boiler plate code for mllex and mlyacc
*)
structure InstructionSemanticsLrVals = InstructionSemanticsLrValsFun(structure Token = LrParser.Token)

structure InstructionSemanticsLex = InstructionSemanticsLexFun(structure Tokens = InstructionSemanticsLrVals.Tokens);

structure InstructionSemanticsParser =
    Join(structure LrParser = LrParser
         structure ParserData = InstructionSemanticsLrVals.ParserData
         structure Lex = InstructionSemanticsLex)

fun invoke lexstream =
  let fun print_error (s,i:int,_) = print ("Error, line " ^ (Int.toString i) ^ ", " ^ s ^ "\n")
    in InstructionSemanticsParser.parse(0,lexstream,print_error,())
  end


(*
  Takes as input a stream and parses it as InstructionSemantics.
  This produces an vcode object.
*)
fun parse strm =
  let val input_line = fn strm => case TextIO.inputLine strm of NONE => "" | SOME s => s
      val lexer = InstructionSemanticsParser.makeLexer (fn _ => input_line strm)
      val dummyEOF = InstructionSemanticsLrVals.Tokens.EOF(0,0)
      fun loop lexer =
        let val (result,lexer) = invoke lexer
            val (nextToken,lexer) = InstructionSemanticsParser.Stream.get lexer
        in if InstructionSemanticsParser.sameToken(nextToken,dummyEOF) then result
           else loop lexer
        end
  in
    loop lexer
  end


(*
  Make a definition in HOL with name "name" and as body "value".
  Value can be any HOL term, e.g.,:
      HOLogic.mk_number @{typ nat} 42
  Note that HOL terms can be produced using antiquotations, e.g.,
      @{term "42::nat"}
  does the same as the above code.
*)
fun mk_definition name value lthy = let
  val binding = Binding.name name
  val (_, lthy) = Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), value)) lthy
  val _ = tracing ("Added definition: " ^ (Local_Theory.full_name lthy binding))
  in
    lthy
  end
                                            
fun embed_semantics semantics lthy = let
  val lthy = mk_definition "semantics" (mk_semantics semantics) lthy
  in
    lthy
end


fun main file_name thy = let
  val dir = case OS.Process.getEnv "LEVIATHAN" of SOME d => d | NONE => OS.FileSys.getDir()
  val _ = tracing ("Reading file: " ^ (dir ^ "/" ^ file_name) ^ ".")
  val {base = localename,...} = OS.Path.splitBaseExt (OS.Path.file (dir ^ "/" ^ file_name))
  val _ = not (Long_Name.is_qualified localename) orelse raise Fail ("Base of filename looks like qualified Isabelle ID: " ^ localename)
  val _ = localename <> "" orelse raise Fail ("Filename (>'" ^ file_name ^ "'<) gives \"\" as locale name, which is illegal")
  val strm = TextIO.openIn (dir ^ "/" ^ file_name)  

  (* Build a locale. This produces a local theory to which we can add definitions. *)
  val loc_b = Binding.name localename
  val (_, lthy) = Expression.add_locale loc_b loc_b ([], []) [] thy
  val _ = tracing ("Added locale: " ^ localename)  
  (* Parse the given stream *)
  val semantics = parse strm
  val _ = TextIO.closeIn strm
  val _ = tracing ("parsing result = \n" ^ toString_semantics semantics)

  (* Embed the binary *)
  val lthy = embed_semantics semantics lthy 

(*
  (* Write the flag info to a file *)
  val flag_info_file_name = dir ^ "/../InstructionSemantics/strata_rules_flag_info"
  val _ = write_flag_info_to_file flag_info_file_name semantics
  val _ = tracing ("Written flag info to file = " ^ flag_info_file_name)
*)
  (* Exit the local theory and return to the global theory *)
  val thy = Local_Theory.exit_global lthy
  in
    thy
  end


structure MyInstructionSemanticsParser : MyInstructionSemanticsParser =
struct
(*
  Add the command "install_model" to the Isabelle syntax.
  Its argument is parsed by Parse.text (for now), which (for now) simply returns
  the text. The parsed text is given to the "main" function. 
*)

fun instruction_semantics_parser args thy =
    thy |> main args (* (TextIO.openString args)*)

val file_inclusion =
   Parse.text >> (Toplevel.theory o instruction_semantics_parser) (* of Toplevel.theory NONE NONE *)


val _ =
    Outer_Syntax.command
      @{command_keyword "instruction_semantics_parser"}
      "import a file containing learned bitvector functions (Instruction Semantics)"
      file_inclusion

end
