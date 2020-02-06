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

theory TestLemmas_GenSet0
  imports 
Main
 "IS_80386/IS_80386_GenSet0"  "IS_80486/IS_80486_GenSet0"  "IS_8088/IS_8088_GenSet0" 
 "IS_BM1_BM2/IS_BM1_BM2_GenSet0"  "IS_PentiumPro/IS_PentiumPro_GenSet0"  "IS_SSE4_2/IS_SSE4_2_GenSet0" 
 "IS_X86_64/IS_X86_64_GenSet0" 

begin

definition TestLemmas_IsTested where "TestLemmas_IsTested \<equiv> True"

end