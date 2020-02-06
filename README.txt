// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

1) We used Isabelle 2017 to run our theories. 

2) The Examples used within the paper can be found here:
 Figure 5 		= isabelle/SimplifiedSemantics.thy
 Figure 7 to 9 	= isabelle/Examples.thy
 Figure 10 		= examples/vel/Vel.thy
 Figure 11 		= examples/memcpyMemcpy.thy
 Figure 12 		= isabelle/CaseStudy_IEEE_Div.thy
 
3) The serialized Strata semantics can be found here:
	InstructionSemantics/StrataRules
	
4) The Test Lemmas can be found here:
	InstructionSemantics/TestLemmas
	
5) The Pintool developed to generate concolic test data can be found here:
	InstructionSemantics/TestLemmas/pintool
	
6) The modified Ramblr reassembler with formal verification annotations:
	ramblr
	
7) Tools developed for Generating Test Lemmas and Chum Serialization:
	InstructionSemantics/stoke
	
	
	