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

theory pow2_autocorres
  imports "$HOME/Packages/autocorres-1.4/autocorres/AutoCorres"
begin

install_C_file "pow2-autocorres.c"
autocorres [ts_rules = nondet] "pow2-autocorres.c"

context "pow2-autocorres" begin
thm pow2_body_def
thm pow2'_def

lemma \<open>\<lbrace>\<lambda>s. True\<rbrace>pow2' e\<lbrace>\<lambda>r s. r = 2 ^ unat e\<rbrace>!\<close>
  unfolding pow2'_def
  apply (subst whileLoop_add_inv[where
        I=\<open>\<lambda>(result, i) s. i \<le> e \<and> result = 2 ^ unat i\<close> and
        M=\<open>\<lambda>((result, i), s). e - i\<close>])
  apply wp
    apply (auto simp: algebra_simps)
    apply unat_arith
   apply (metis add.commute add_diff_cancel_left' diff_0
      less_irrefl power.simps(2) unatSuc word_minus_one_le)
  apply unat_arith
  done

end

end
