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

theory IS_80386_GenSet0
  imports 
Main
 "Movsx/Movsx_GenSet0"  "Movzx/Movzx_GenSet0"  "Seta/Seta_GenSet0"  "Setae/Setae_GenSet0"  "Setb/Setb_GenSet0" 
 "Setbe/Setbe_GenSet0"  "Setc/Setc_GenSet0"  "Sete/Sete_GenSet0"  "Setg/Setg_GenSet0"  "Setge/Setge_GenSet0" 
 "Setl/Setl_GenSet0"  "Setle/Setle_GenSet0"  "Setna/Setna_GenSet0"  "Setnae/Setnae_GenSet0"  "Setnb/Setnb_GenSet0" 
 "Setnbe/Setnbe_GenSet0"  "Setnc/Setnc_GenSet0"  "Setne/Setne_GenSet0"  "Setng/Setng_GenSet0"  "Setnge/Setnge_GenSet0" 
 "Setnl/Setnl_GenSet0"  "Setnle/Setnle_GenSet0"  "Setno/Setno_GenSet0"  "Setnp/Setnp_GenSet0"  "Setns/Setns_GenSet0" 
 "Setnz/Setnz_GenSet0"  "Seto/Seto_GenSet0"  "Setp/Setp_GenSet0"  "Setpe/Setpe_GenSet0"  "Setpo/Setpo_GenSet0" 
 "Sets/Sets_GenSet0"  "Setz/Setz_GenSet0" 

begin

definition IS_80386_IsTested where "IS_80386_IsTested \<equiv> True"

end