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


signature Myx86_64Parser =
sig
  val x86_64_objdump_parser : string -> theory -> theory
end

(*
  The following is boiler plate code for mllex and mlyacc
*)
structure x86_64LrVals = x86_64LrValsFun(structure Token = LrParser.Token)

structure x86_64Lex = x86_64LexFun(structure Tokens = x86_64LrVals.Tokens);

structure x86_64Parser =
    Join(structure LrParser = LrParser
         structure ParserData = x86_64LrVals.ParserData
         structure Lex = x86_64Lex)

fun invoke lexstream =
  let fun print_error (s,i:int,_) = print ("Error, line " ^ (Int.toString i) ^ ", " ^ s ^ "\n")
    in x86_64Parser.parse(0,lexstream,print_error,())
  end


(*
  Takes as input a stream and parses it as x86_64.
  This produces an vcode object.
*)
fun parse strm =
  let val input_line = fn strm => case TextIO.inputLine strm of NONE => "" | SOME s => s
      val lexer = x86_64Parser.makeLexer (fn _ => input_line strm)
      val dummyEOF = x86_64LrVals.Tokens.EOF(0,0)
      fun loop lexer =
        let val (result,lexer) = invoke lexer
            val (nextToken,lexer) = x86_64Parser.Stream.get lexer
        in if x86_64Parser.sameToken(nextToken,dummyEOF) then result
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

(*
  The main function of the Isar command "x86_64_objdump_parser"
*)

fun embed_assembly assembly lthy = let
(*  val lthy = mk_definition "boffset" @{term "undefined :: 64 word"} lthy (* TODO: this should be in the generated locale instead of a definition *)
	val lthy = mk_definition "lookup_table" (mk_lookup_table assembly) lthy
*)  val lthy = mk_definition "assembly" (mk_objdump_assembly assembly) lthy
  in
    lthy
end

fun main file_name thy = let
  val dir = case OS.Process.getEnv "LEVIATHAN" of SOME d => d | NONE => OS.FileSys.getDir()
  val dir = "C:/Users/ian/Documents/Leviathan/reassembly_verification/x86-64_objdumpparser/Examples"
  val _ = tracing ("Reading file: " ^ (dir ^ "/" ^ file_name) ^ ".")
  val {base = localename,...} = OS.Path.splitBaseExt (OS.Path.file (dir ^ "/" ^ file_name))
  val _ = not (Long_Name.is_qualified localename) orelse raise Fail ("Base of filename looks like qualified Isabelle ID: " ^ localename)
  val _ = localename <> "" orelse raise Fail ("Filename (>'" ^ file_name ^ "'<) gives \"\" as locale name, which is illegal")
  val strm = TextIO.openIn (dir ^ "/" ^ file_name)

  (* Build a locale. This produces a local theory to which we can add definitions. *)
  val loc_b = Binding.name localename
(*  val fixes_boffset = Element.Fixes [( Binding.name "boffset" , SOME (mk_word_typ 64), NoSyn)] *)

  val (_, lthy) = Expression.add_locale loc_b loc_b ([], []) [(*fixes_boffset*)] thy
  val _ = tracing ("Added locale: " ^ localename)
  (* Parse the given stream *)
  val assembly = parse strm
  val _ = TextIO.closeIn strm
  val _ = tracing ("parsing result = \n" ^ toString_assembly assembly ^ "\n")
  (* Embed the module into Isabelle/HOL *)
  val lthy = embed_assembly assembly lthy  
  (* Exit the local theory and return to the global theory *)
  val thy = Local_Theory.exit_global lthy
  in
    thy
  end


structure Myx86_64Parser : Myx86_64Parser =
struct
(*
  Add the command "install_model" to the Isabelle syntax.
  Its argument is parsed by Parse.text (for now), which (for now) simply returns
  the text. The parsed text is given to the "main" function. 
*)
fun x86_64_objdump_parser args thy =
    thy |> main args

val file_inclusion =
   Parse.text >> (Toplevel.theory o x86_64_objdump_parser)

val _ =
    Outer_Syntax.command
      @{command_keyword "x86_64_objdump_parser"}
      "import a x86_64 file"
      file_inclusion
end;





