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

theory State_Rewriting
  imports Main   
     "reassembly_setup.Leviathan_Setup" 
begin

(* Rules to reorder functions with size(domain)=2 , 2!-1 = {ab, ba}- {ab} *)
lemma fun_reorder2_ba[simp]: (* b *)
  assumes "src\<noteq>dst"
  shows "         (f \<sigma>)(dst := b, src := a) = 
                  (f \<sigma>)(src := a, dst := b)"
proof-
  show ?thesis
  apply (insert assms(1))
  by (auto)
qed

(* Rules to reorder functions with size(domain)=3 , 3! - the target and anything prefixed with a (by recursion)
 = {abc, bac, acb, cab, bca, cba }- {abc} *)
lemma fun_reorder3_bac[simp]: (* bac *)
  assumes "r1\<noteq>r2" and "r2 \<noteq>r3" and "r1 \<noteq>r3"
   shows "          (f \<sigma>)(r2 := b, r1 := a, r3 := c) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c)"
  apply (insert assms(1-3))  by (auto)
(* lemma fun_reorder3_acb[simp]: (* acb *)
  assumes "r1\<noteq>r2" and "r2 \<noteq>r3" and "r1 \<noteq>r3"
   shows "          (f \<sigma>)(r1 := a, r3 := c, r2 := b) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c)"
  apply (insert assms(1-3))  by (auto)
*)
lemma fun_reorder3_cab[simp]: (* cab *)
  assumes "r1\<noteq>r2" and "r2 \<noteq>r3" and "r1 \<noteq>r3"
   shows "          (f \<sigma>)(r3 := c, r1 := a, r2 := b) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c)"
  apply (insert assms(1-3))  by (auto)
lemma fun_reorder3_bca[simp]: (* bca *)
  assumes "r1\<noteq>r2" and "r2 \<noteq>r3" and "r1 \<noteq>r3"
   shows "          (f \<sigma>)(r2 := b, r3 := c, r1 := a) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c)"
  apply (insert assms(1-3))  by (auto)
lemma fun_reorder3_cba[simp]: (* cba *)
  assumes "r1\<noteq>r2" and "r2 \<noteq>r3" and "r1 \<noteq>r3"
   shows "          (f \<sigma>)(r3 := c, r2 := b, r1 := a) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c)"
  apply (insert assms(1-3))  by (auto)

(* Rules to reorder functions with size(domain)=4 , 4!-1 = {dabc, dbac, dacb, dcab, dbca, dcba  
                                                            badc, bdac, bacd, bcad, bdca, bcda
                                                            cadb, cdab, cabd, cbad, cdba, cbda
                                                            acdb, adcb, acbd, abcd, adbc, abdc} - {abcd}
*)
lemma fun_reorder3_dabc[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r4 := d, r1 := a, r2 := b, r3 :=c) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_dbac[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r4 := d, r2 := b, r1 := a, r3 :=c) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_dacb[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r4 := d, r1 := a, r3 := c, r2 :=b) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_dcab[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r4 := d, r3 := c, r1 := a, r2 :=b) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_dbca[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r4 := d, r2 := b, r3 := c, r1 :=a) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_dcba[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r4 := d, r3 := c, r2 := b, r1 :=a) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
(*badc, bdac, bacd, bcad, bdca, bcda*)
lemma fun_reorder3_badc[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r2 := b, r1 := a, r4 := d, r3 :=c) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_bdac[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r2 := b, r4 := d, r1 := a, r3 :=c) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_bacd[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r2 := b, r1 := a, r3 := c, r4 :=d) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_bcad[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r2 := b, r3 := c, r1 := a, r4 :=d) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_bdca[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r2 := b, r4 := d, r3 := c, r1 :=a) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_bcda[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r2 := b, r3 := c, r4 := d, r1 :=a) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
(*cadb, cdab, cabd, cbad, cdba, cbda*)
lemma fun_reorder3_cadb[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r3 := c, r1 := a, r4 := d, r2 :=b) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_cdab[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r3 := c, r4 := d, r1 := a, r2 :=b) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_cabd[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r3 := c, r1 := a, r2 := b, r4 :=d) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_cbad[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r3 := c, r2 := b, r1 := a, r4 :=d) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_cdba[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r3 := c, r4 := d, r2 := b, r1 :=a) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_cbda[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r3 := c, r2 := b, r4 := d, r1 :=a) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
(*acdb, adcb, acbd, abcd, adbc, abdc} - {abcd} *)
lemma fun_reorder3_acdb[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r1 := a, r3 := c, r4 := d, r2 :=b) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_adcb[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r1 := a, r4 := d, r3 := c, r2 :=b) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_acbd[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r1 := a, r3 := c, r2 := b, r4 :=d) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_adbc[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r1 := a, r4 := d, r2 := b, r3 :=c) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)
lemma fun_reorder3_abdc[simp]: 
  assumes "r1\<noteq>r2" and "r1 \<noteq>r3" and "r1 \<noteq>r4" and "r2 \<noteq>r3" and "r2 \<noteq>r4" and "r3 \<noteq>r4" 
   shows "          (f \<sigma>)(r1 := a, r2 := b, r4 := d, r3 :=c) = 
                    (f \<sigma>)(r1 := a, r2 := b, r3 := c, r4 :=d)"
  apply (insert assms(1-6))  by (auto)


(* total ordering of record states with 2 fields set *)
lemma state_reorder2_rm[simp]:
  shows "         \<sigma>\<lparr>mem := b, regs := a\<rparr> = 
                  \<sigma>\<lparr>regs := a, mem := b\<rparr>"
  by auto

lemma state_reorder2_rf[simp]:
  shows "         \<sigma>\<lparr>flags := b, regs := a\<rparr> = 
                  \<sigma>\<lparr>regs := a, flags := b\<rparr>"
  by auto

(* Rules to reorder functions with size(domain)=3 for regs,mem,flags *)
lemma state_reorder3_bac[simp]: (* bac *)
   shows "          \<sigma>\<lparr>mem := b, regs := a, flags := c\<rparr> = 
                    \<sigma>\<lparr>regs := a, mem := b, flags := c\<rparr>"
  by auto
 lemma state_reorder3_acb[simp]: (* acb *)
   shows "          \<sigma>\<lparr>regs := a, flags := c, mem := b\<rparr> = 
                    \<sigma>\<lparr>regs := a, mem := b, flags := c\<rparr>"
  by auto

lemma state_reorder3_cab[simp]: (* cab *)
   shows "          \<sigma>\<lparr>flags := c, regs := a, mem := b\<rparr> = 
                    \<sigma>\<lparr>regs := a, mem := b, flags := c\<rparr>"
  by auto
lemma state_reorder3_bca[simp]: (* bca *)
   shows "          \<sigma>\<lparr>mem := b, flags := c, regs := a\<rparr> = 
                    \<sigma>\<lparr>regs := a, mem := b, flags := c\<rparr>"
  by auto
lemma state_reorder3_cba[simp]: (* cba *)
   shows "          \<sigma>\<lparr>flags := c, mem := b, regs := a\<rparr> = 
                    \<sigma>\<lparr>regs := a, mem := b, flags := c\<rparr>"
  by auto


end