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

theory IS_8088_GenSet0
  imports 
Main
 "Adc/Adc_GenSet0"  "Add/Add_GenSet0"  "And/And_GenSet0"  "Cmp/Cmp_GenSet0"  "Dec/Dec_GenSet0" 
 "Inc/Inc_GenSet0"  "Mov/Mov_GenSet0"  "Neg/Neg_GenSet0"  "Nop/Nop_GenSet0"  "Not/Not_GenSet0" 
 "Or/Or_GenSet0"  "Sbb/Sbb_GenSet0"  "Sub/Sub_GenSet0"  "Test/Test_GenSet0"  "Xchg/Xchg_GenSet0" 
 "Xor/Xor_GenSet0" 

begin

definition IS_8088_IsTested where "IS_8088_IsTested \<equiv> True"

end