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

theory Mov_GenSet0
  imports 
Main
Mov_rh_rh_GenSet0 Mov_rh_r8_GenSet0 Mov_r8_rh_GenSet0 Mov_r8_r8_GenSet0 Mov_r64_r64_GenSet0 
Mov_r16_r16_GenSet0 Mov_r32_r32_GenSet0 

begin

definition Mov_IsTested where "Mov_IsTested \<equiv> True"

end