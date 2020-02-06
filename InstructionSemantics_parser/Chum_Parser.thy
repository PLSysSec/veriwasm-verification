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

theory Chum_Parser
imports "../isabelle/BitVectors"
 keywords
  "instruction_semantics_parser" :: thy_decl
begin




text {*
  Open mlyacc
*}
ML_file "mlyacc_base.ML"
ML_file "mlyacc/mlyacclib/MLY_base-sig.ML"
ML_file "mlyacc/mlyacclib/MLY_join.ML"
ML_file "mlyacc/mlyacclib/MLY_lrtable.ML"
ML_file "mlyacc/mlyacclib/MLY_stream.ML"
ML_file "mlyacc/mlyacclib/MLY_parser2.ML" 
  
  
text {* 
  Open the data structures concerning x86-64 assembly.  
*}  
ML_file "../isabelle/Base.ML" 
ML_file "../x86-64_parser/x86_64_datastructures.ML" 
ML_file "InstructionSemantics_Datastructures.ML"

text {*  
  Open the CHUM parser.   
*}
ML_file "InstructionSemantics.grm.sig" 
ML_file "InstructionSemantics.grm.sml"
ML_file "InstructionSemantics.lex.sml" 


text {*        
  Open the embedding of CHUM into Isabelle/HOL.
*}                 
ML_file "InstructionSemantics_parser.ML"

end