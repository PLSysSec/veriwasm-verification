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

theory IS_80486_GenSet0
  imports 
Main
 "Bswap/Bswap_GenSet0"  "Cmpxchg/Cmpxchg_GenSet0"  "Xadd/Xadd_GenSet0" 

begin

definition IS_80486_IsTested where "IS_80486_IsTested \<equiv> True"

end