theory Read_Array
  imports "reassembly_setup.Leviathan_Setup"

begin
context execution_context
begin

fun read_array :: "state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::len0 word list"
  where "read_array s a ts 0 = []"
  | "read_array s a ts (Suc si) = (s \<turnstile> *[a,ts])#(read_array s (a+of_nat ts) ts si)"

definition read_array_8 :: "state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 8 word list"
  where "read_array_8 s a n = read_array s a 1 n"

definition read_array_32 :: "state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 32 word list"
  where "read_array_32 s a n = read_array s a 4 n"


lemma read_array_8_0[simp]:
  shows "read_array_8 s a 0 = []"
  unfolding read_array_8_def
  by (auto)

lemma read_array_32_0[simp]:
  shows "read_array_32 s a 0 = []"
  unfolding read_array_32_def
  by (auto)

lemma nth_read_array:
assumes "n < si"
  shows "read_array s a ts si ! n = s \<turnstile> *[a + of_nat ts * of_nat n,ts]"
  using assms
proof(induct s a ts si arbitrary: n rule: read_array.induct)
  case (1 s a ts si)
  thus ?case
    by auto
next
  case (2 s a ts si n)
  thus ?case
    by (cases n,auto simp add: field_simps)
qed

lemma nth_read_array_8:
assumes "n < si"
shows "read_array_8 s a si ! n = (s \<turnstile> *[a + of_nat n,1] :: 8 word)"
  using assms
  unfolding read_array_8_def
  apply (subst nth_read_array)
  by auto

lemma nth_read_array_32:
assumes "n < si"
shows "read_array_32 s a si ! n = (s \<turnstile> *[a + 4 * of_nat n,4] :: 32 word)"
  using assms
  unfolding read_array_32_def
  apply (subst nth_read_array)
  by auto

lemma length_read_array:
  shows "length (read_array s a ts n) = n"
  by(induct s a ts n rule: read_array.induct,auto)

lemma length_read_array_8:
  shows "length (read_array_8 s a n) = n"
  by (auto simp add: read_array_8_def length_read_array)

lemma length_read_array_32:
  shows "length (read_array_32 s a n) = n"
  by (auto simp add: read_array_32_def length_read_array)

lemma master_for_array_update:
  assumes "seps blocks"
      and "(I, a, ts * si) \<in> blocks"
      and "n < si"
      and "ts > 0"
  shows "master blocks (a + of_nat ts * of_nat n, ts) I"
proof-
  have master: "master blocks (a, of_nat si * of_nat ts) I"
    apply (rule master_if_in_blocks)
    using assms(1,2)
    by (auto simp add: field_simps)
  have 1: "no_block_overflow (a, of_nat si * of_nat ts)"
    apply (rule no_block_overflow_smaller_block[of _ "of_nat si * of_nat ts"])
    apply (rule master_block_implies_no_block_overflow[of blocks _ I])
    using master
    by auto
  have ts_si: "si * ts < 2^64"
    using 1
    by (auto simp add: no_block_overflow.simps)
  have si: "si < 2^64"
    apply (rule le_less_trans[OF _ ts_si])
    using assms(4)
    by (auto)
  have n: "n < 2^64"
    apply (rule le_less_trans[OF _ si])
    using assms(3)
    by auto
  have ts_n: "ts * n < 2^64"
    apply (rule le_less_trans[OF _ ts_si])
    using assms(3)
    by (auto)
  have ts: "ts < 2^64"
    apply (rule le_less_trans[OF _ ts_si])
    using assms(3)
    by (auto)
  have 3: "ts * n + ts \<le> si * ts"
    using assms(3,4)
    using mult_le_mono1[of "n+1" si ts]
    by (auto simp add: field_simps)
  show ?thesis
    apply (rule master_of_enclosed[where b="(a, ts * si)"])
    using assms(1) apply simp
    apply (rule no_block_overflow_smaller_block_positive_offset_r)
    apply (rule 1)
    using assms(3) apply unat_arith
    using n si ts_n ts 3
    apply (auto simp add: unat_word_ariths unat_of_nat unat_ucast is_up)[1]
    using assms(2) apply simp
    apply (subst enclosed_plus_r)
    using 1 assms(3)
    apply (auto simp add: unat_of_nat 3 no_block_overflow.simps)
    apply unat_arith
    using n si ts_n ts 3 ts_si 3
    apply (auto simp add: unat_of_nat unat_word_ariths unat_ucast is_up)[1]
    apply (simp add: field_simps)
    apply unat_arith
    using n si ts_n ts 3 ts_si 3
    apply (auto simp add: unat_of_nat unat_word_ariths unat_ucast is_up)[1]
    using n si ts_n ts 3 ts_si 3
    by (auto simp add: unat_of_nat unat_word_ariths unat_ucast is_up field_simps)[1]
qed


lemma take_read_array:
  assumes "seps blocks"
      and "n < si"
      and "0 < ts"
      and "(I, a, ts * si) \<in> blocks"
      and "\<And> i. i < n \<Longrightarrow> master blocks (of_nat i * of_nat ts + a, ts) I \<Longrightarrow> (s' \<turnstile> *[a + of_nat i * of_nat ts,ts]::'a word) = s \<turnstile> *[a + of_nat i * of_nat ts,ts]"
  shows "(take n (read_array s' a ts si) :: 'a ::len0 word list) = read_array s a ts n"
proof-
  {
    fix i
    assume "i < n"
    hence "(take n (read_array s' a ts si) :: 'a ::len0 word list) ! i = read_array s a ts n ! i"
      using assms(1-4)
      apply (auto simp add: nth_read_array field_simps)
      apply (subst assms(5))
      using master_for_array_update[of blocks I a ts si i]
      by (auto simp add: field_simps)
  }
  thus ?thesis
    using assms
    apply (intro nth_equalityI)
    by (auto simp add: length_read_array min_def)
qed

lemma take_read_array_8:
  assumes "seps blocks"
      and "n < si"
      and "(I, a, si) \<in> blocks"
      and "\<And> i. i < n \<Longrightarrow> master blocks (of_nat i + a, 1) I \<Longrightarrow> (s' \<turnstile> *[a + of_nat i,1]::8 word) = s \<turnstile> *[a + of_nat i,1]"
    shows "take n (read_array_8 s' a si) = read_array_8 s a n"
  unfolding read_array_8_def
  using take_read_array[OF assms(1,2),where 'a=8 and ts=1] assms(3-)
  by auto

lemma take_read_array_32:
  assumes "seps blocks"
      and "n < si"
      and "(I, a, 4 * si) \<in> blocks"
      and "\<And> i. i < n \<Longrightarrow> master blocks (of_nat i * 4 + a, 4) I \<Longrightarrow> (s' \<turnstile> *[a + of_nat i * 4,4]::32 word) = s \<turnstile> *[a + of_nat i * 4,4]"
  shows "(take n (read_array_32 s' a si) :: 32 word list) = read_array_32 s a n"
  unfolding read_array_32_def
  using take_read_array[OF assms(1,2),where 'a=32 and ts=4] assms(3-)
  by auto


definition array_update :: "state \<Rightarrow> state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a ::len0 word \<Rightarrow> bool"
  where "array_update s s' a ts si n v \<equiv> \<forall> i < si . s' \<turnstile> *[a + of_nat ts * of_nat i,ts] = (if i = n then v else s \<turnstile> *[a + of_nat ts * of_nat i,ts] :: 'a word)"


lemma read_array_update_nth:
  assumes "array_update s s' a ts n\<^sub>0 n v"
      and "n < n\<^sub>0"
  shows "read_array s' a ts n\<^sub>0 = (read_array s a ts n\<^sub>0)[n := v]"
proof-
  {
    fix i
    assume i: "i < n\<^sub>0"
    hence "read_array s' a ts n\<^sub>0 ! i = (read_array s a ts n\<^sub>0)[n := v] ! i"
      using assms(2) assms(1)[unfolded array_update_def,THEN spec,of i]
      by (auto simp add: nth_read_array length_read_array nth_list_update)
  }
  thus ?thesis
    apply (intro nth_equalityI)
    by (auto simp add: length_read_array)
qed

lemma read_array_8_update_nth:
  assumes "array_update s s' a 1 n\<^sub>0 n v"
      and "n < n\<^sub>0"
  shows "read_array_8 s' a n\<^sub>0 = (read_array_8 s a n\<^sub>0)[n := v]"
  apply (simp only: read_array_8_def)
  by (rule read_array_update_nth[OF assms])

lemma read_array_32_update_nth:
  assumes "array_update s s' a 4 n\<^sub>0 n v"
      and "n < n\<^sub>0"
  shows "read_array_32 s' a n\<^sub>0 = (read_array_32 s a n\<^sub>0)[n := v]"
  apply (simp only: read_array_32_def)
  by (rule read_array_update_nth[OF assms])

lemma read_bytes_nth:
assumes "n < snd b"
shows "read_bytes m b ! n = m (fst b + of_nat n)"
  using assms
proof(induct m b arbitrary: n rule: read_bytes.induct)
  case (1 m b)
  thus ?case
    by auto
next
  case (2 m b n')
  show ?case
    using 2(2)
    apply (auto simp add: read_bytes.simps(2) Let'_def Let_def)
    using 2(1)[of "n-1"]
    by (cases n,auto simp add: field_simps)
qed


lemma read_byte_from_larger_region:
assumes "a \<ge> a\<^sub>0"
    and "unat (a - a\<^sub>0) < si"
    and "no_block_overflow (a, Suc 0)"
    and "no_block_overflow (a\<^sub>0, si)"
    and "unat (a - a\<^sub>0 + 1) * 8 - Suc 0 < LENGTH('a)"
  shows "s \<turnstile> *[a,Suc 0] = (\<langle>unat (a - a\<^sub>0 + 1) * 8 - Suc 0,unat (a - a\<^sub>0 + 1) * 8 - 8\<rangle> (s \<turnstile> *[a\<^sub>0,si] :: 'a::len0 word) :: 8 word)"
proof-
  have 2: "0 < unat (a - a\<^sub>0 + 1)"
    using assms(3)[unfolded no_block_overflow.simps] assms(1)
    apply unat_arith
    by auto
  have 3: "unat (1 + a - a\<^sub>0) - Suc 0 = unat a - unat a\<^sub>0"
    using assms(3)[unfolded no_block_overflow.simps] assms(1)
    apply unat_arith
    by (auto)
  have 4: "a\<^sub>0 + of_nat (unat (1 + a - a\<^sub>0) - Suc 0) = a"
    using assms(1)
    apply (simp add: 3)
    apply unat_arith
    by (auto simp add: unat_of_nat)
  have 5: "unat (1 + a - a\<^sub>0) \<le> si"
    using assms(2)
    by unat_arith
  show ?thesis
    using assms
    apply (auto simp add: read_region_def simp_rules Let'_def nth_word_to_bytes sublist_def min_def read_bytes.simps(2) simp del: field_simps)
    apply (subst take_eight_bits_of_cat_bytes)
    using 2 4 5
    by (auto simp add: field_simps length_read_bytes rev_nth read_bytes_nth)
qed

lemma minus_1_le:
  fixes a b :: nat
  shows "a - Suc 0 < b \<longleftrightarrow> (if a = 0 then b > 0 else a \<le> b)"
  by auto

lemma no_block_overflow_block_in_memory:
  assumes "ts > 0"
    and "no_block_overflow (a\<^sub>0, si)"
    and "no_block_overflow (a, ts * n)"
    and i: "i < n"
  shows "no_block_overflow (a + of_nat i * of_nat ts, of_nat ts)"
proof-
    have ts_n: "ts * n < 2^64"
      using assms[unfolded no_block_overflow.simps] i
      by unat_arith
    have ts_i: "ts * i < 2^64"
      apply (rule le_less_trans[OF _ ts_n])
      using assms(4)[unfolded no_block_overflow.simps] i
      by unat_arith
    have ts: "ts < 2^64"
      apply (rule le_less_trans[OF _ ts_n])
      using i
      by auto
    have n: "n < 2^64"
      apply (rule le_less_trans[OF _ ts_n])
      using assms(1)
      by auto
    have i_le_264: "i < 2^64"
      apply (rule le_less_trans[OF _ ts_n])
      apply (cases "ts=0",auto)
      using assms(1) i apply auto
      by (smt assms(1) dual_order.strict_implies_order i le_square mult_le_mono nat_mult_le_cancel1 semiring_normalization_rules(7) simp_rules(41))
    hence i': "unat (of_nat ts * of_nat i :: 64 word) < of_nat ts * n"
      apply unat_arith
      using i_le_264 ts ts_i assms(1) i
      by (auto simp add: unat_word_ariths unat_of_nat)

    have 0: "unat a + i * of_nat ts < 2^64"
      using i' assms[unfolded no_block_overflow.simps] i 
      apply unat_arith
      using ts i_le_264 ts_i
      apply (auto simp add: unat_word_ariths unat_sub_if_size unat_of_nat)
      apply (auto simp add: field_simps)
      proof -
        assume "unat a + n * ts < 18446744073709551616"
        then have "i * ts + (unat a + n * ts) < n * ts + 18446744073709551616"
          by (simp add: add_less_mono assms(1) i)
        then show "unat a + i * ts < 18446744073709551616"
          by linarith
      qed
    have a_n_ts: "unat a + n * ts < 2^64"
      using i' assms[unfolded no_block_overflow.simps] i 
      apply unat_arith
      using ts i_le_264 ts_i
      apply (auto simp add: unat_word_ariths unat_sub_if_size unat_of_nat)
      by (auto simp add: field_simps)
    have 00: "unat a + i * ts + ts < 2^64"
      apply (rule le_less_trans[of _ "unat a + n * ts"])
      using i a_n_ts
      apply auto
      using i mult_le_mono1[of "i+1" n ts]
      by unat_arith
    show ?thesis
      using assms(2) i i' ts i_le_264 ts_i a_n_ts n 0
      apply (auto simp add: no_block_overflow.simps)
      apply unat_arith
      using 00
      by (auto simp add: unat_of_nat unat_word_ariths)
  qed

lemma block_in_memory_eq:
  assumes "ts > 0"
    and "s' \<turnstile> *[a\<^sub>0,si] = (s \<turnstile> *[a\<^sub>0,si] :: 'a::len word)"
    and "a \<ge> a\<^sub>0"
    and "unat (a - a\<^sub>0) + ts * n \<le> si"
    and "no_block_overflow (a\<^sub>0, si)"
    and "no_block_overflow (a, ts * n)"
    and "unat (a + of_nat n * of_nat ts - a\<^sub>0) * 8 \<le> LENGTH('a)"
    and i: "i < n"
  shows "s' \<turnstile> *[a + of_nat i * of_nat ts,ts] = (s \<turnstile> *[a + of_nat i * of_nat ts,ts] :: 'b::len word)"
proof-
    have ts_n: "ts * n < 2^64"
      using assms(6)[unfolded no_block_overflow.simps] i
      by unat_arith
    have ts_i: "ts * i < 2^64"
      apply (rule le_less_trans[OF _ ts_n])
      using assms(6)[unfolded no_block_overflow.simps] i
      by unat_arith
    have ts: "ts < 2^64"
      apply (rule le_less_trans[OF _ ts_n])
      using i
      by auto
    have n: "n < 2^64"
      apply (rule le_less_trans[OF _ ts_n])
      using assms(1)
      by auto
    have i_le_264: "i < 2^64"
      apply (rule le_less_trans[OF _ ts_n])
      apply (cases "ts=0",auto)
      using assms(1) i apply auto
      by (smt assms(1) dual_order.strict_implies_order i le_square mult_le_mono nat_mult_le_cancel1 semiring_normalization_rules(7) simp_rules(41))
    hence i': "unat (of_nat ts * of_nat i :: 64 word) < of_nat ts * n"
      apply unat_arith
      using i_le_264 ts ts_i assms(1) i
      by (auto simp add: unat_word_ariths unat_of_nat)
    have 1: "a\<^sub>0 \<le> a + of_nat ts * of_nat i"
      using assms(3,4) i assms(5,6)[unfolded no_block_overflow.simps]
      apply unat_arith
      using i'
      by (auto simp add: unat_of_nat)
    have 00: "unat a + i * ts + ts - unat a\<^sub>0 \<le> unat a + n * ts - unat a\<^sub>0"
      apply (rule diff_le_mono)
      using i mult_le_mono1[of "i+1" n ts]
      by auto
    have 0: "unat a + i * of_nat ts < 2^64"
      using i' assms(6)[unfolded no_block_overflow.simps] i 
      apply unat_arith
      using ts i_le_264 ts_i
      apply (auto simp add: unat_word_ariths unat_sub_if_size unat_of_nat)
      apply (auto simp add: field_simps)
      proof -
        assume "unat a + n * ts < 18446744073709551616"
        then have "i * ts + (unat a + n * ts) < n * ts + 18446744073709551616"
          by (simp add: add_less_mono assms(1) i)
        then show "unat a + i * ts < 18446744073709551616"
          by linarith
      qed
    hence 22: "unat (a + of_nat i * of_nat ts - a\<^sub>0) + of_nat ts \<le> si"
      using assms(3,4) i ts i_le_264 ts_i 00
      apply (auto simp add: unat_sub_if_size word_size unat_of_nat split: if_split_asm)
      apply (auto simp add: unat_word_ariths unat_sub_if_size word_size unat_of_nat)
      apply (rule order_trans)
      apply (auto simp add: field_simps) 
      by unat_arith
    have 43: "unat a\<^sub>0 \<le> unat a + i * of_nat ts"
      using assms(3,6) i
      apply (auto simp add: no_block_overflow.simps)
      by unat_arith
    have a_n_ts: "unat a + n * ts < 2^64"
      using i' assms(6)[unfolded no_block_overflow.simps] i 
      apply unat_arith
      using ts i_le_264 ts_i
      apply (auto simp add: unat_word_ariths unat_sub_if_size unat_of_nat)
      by (auto simp add: field_simps)
    have 4: "unat (a + of_nat i * of_nat ts - a\<^sub>0) * 8 \<le> LENGTH('a)"
      using 0 assms(7) assms(6)[unfolded no_block_overflow.simps] 43 i ts i_le_264 ts_i a_n_ts n 00
      by (auto simp add: unat_word_ariths unat_sub_if_size word_size unat_of_nat split: if_split_asm)[1]
    hence 4: "unat (a + of_nat i * of_nat ts - a\<^sub>0) * 8 - Suc 0 < LENGTH('a)"
      apply (subst minus_1_le)
      by auto
    have 00: "unat a + i * ts + ts < 2^64"
      apply (rule le_less_trans[of _ "unat a + n * ts"])
      using i a_n_ts
      apply auto
      using i mult_le_mono1[of "i+1" n ts]
      by unat_arith
    have 3: "no_block_overflow (a + of_nat i * of_nat ts, of_nat ts)"
      using assms(6) i i' ts i_le_264 ts_i a_n_ts n 0
      apply (auto simp add: no_block_overflow.simps)
      apply unat_arith
      using 00
      by (auto simp add: unat_of_nat unat_word_ariths)
    {
      fix j :: nat
      assume "j < LENGTH('b)"
      {
        fix a'
        assume 1: "fst (a + of_nat i * of_nat ts, ts) \<le> a'"
           and 2: "a' < fst (a + of_nat i * of_nat ts, ts) + of_nat ts"
        have "a + (of_nat i * of_nat ts + of_nat ts) \<le> a + of_nat n * of_nat ts"
          apply (rule word_plus_mono_right)
          apply unat_arith
          using i ts ts_i assms(1) n 0 ts_n 00
          apply (auto simp add: unat_word_ariths unat_of_nat)[1]
          apply (auto simp add: field_simps)[1]
          using i mult_le_mono1[of "i+1" n ts]
          apply auto[1]
          apply unat_arith
          using i ts ts_i assms(1) n 0 ts_n 00 a_n_ts
          by (auto simp add: unat_word_ariths unat_of_nat)[1]
        hence 3: "no_block_overflow (a', Suc 0)"
          using 2 a_n_ts
          apply (auto simp add: no_block_overflow.simps field_simps)
          apply unat_arith
          apply (auto simp add: unat_of_nat)[1]
          apply (auto simp add: unat_of_nat)[1]
          done
        have 4: " a \<le> a'"
          using assms(3,6) i 1 0 ts ts_i assms(1) n
          apply (auto simp add: no_block_overflow.simps) 
          apply unat_arith
          by (auto simp add: unat_word_ariths unat_of_nat)
        hence 5: " a\<^sub>0 \<le> a'"
          using assms(3)
          by auto
        have 60 :"unat a + unat (of_nat i * of_nat ts :: 64word) < 2^64"
          using i' assms(6)[unfolded no_block_overflow.simps] i ts ts_i assms(1) n 0
          apply unat_arith
          by (auto simp add: unat_word_ariths unat_sub_if_size unat_of_nat word_size split: if_split_asm)
        have 43: "n*of_nat ts < 2^64"
          apply (rule le_less_trans[OF _ ts_n])
          using assms(1) ts_n
          by (auto)
        have 61: "i * of_nat ts < 2^64"
          using ts_i
          apply unat_arith
          by (auto simp add: field_simps)
        have 62: "a' < a + of_nat i * of_nat ts + of_nat ts \<Longrightarrow> unat a' < unat a + i * of_nat ts + of_nat ts"
          apply (subst (asm) word_less_nat_alt)
          using i ts ts_i assms(1) n 0
          by (auto simp add: unat_word_ariths unat_of_nat)
        have 6: "unat (a' - a\<^sub>0) < si"
          apply (auto simp add: unat_word_ariths unat_sub_if_size unat_of_nat word_size split: if_split_asm)
          using 22 2 60 i 61 ts ts_i assms(1) n 0
          apply (auto simp add: unat_word_ariths unat_of_nat split: if_split_asm)[1]
          apply (simp add: unat_sub_if_size)
          apply (auto simp add: unat_of_nat split: if_split_asm)[1]
          using 60 i 5 62 
          apply (auto simp add: unat_word_ariths unat_of_nat word_size split: if_split_asm)
          by unat_arith
        have 41: "Suc (unat a' - unat a\<^sub>0) < 2^64"
          using 6 assms(5)[unfolded no_block_overflow.simps]
          by (auto simp add: unat_word_ariths unat_sub_if_size unat_of_nat word_size split: if_split_asm)
        have 42: "unat a + unat (of_nat n * of_nat ts :: 64 word) < 2^64"
          using assms(5)[unfolded no_block_overflow.simps] ts ts ts_i assms(1) n 0 ts_n a_n_ts
          apply unat_arith
          by (auto simp add: unat_word_ariths unat_of_nat word_size split: if_split_asm)
        have 45: "unat a + i * ts + ts \<le> unat a + n * ts"
          apply unat_arith
          using i mult_le_mono1[of "i+1" n ts]
          by auto
        have 44: "unat a' < unat a + n * of_nat ts"
          using 2 i
          apply auto
          apply unat_arith
          using ts ts_i assms(1) n 0 ts_n a_n_ts 45
          by (auto simp add: unat_word_ariths unat_of_nat split: if_split_asm)
        have 4: "unat (a' - a\<^sub>0 + 1) * 8  - 1 < unat (a + of_nat n * of_nat ts - a\<^sub>0) * 8"
          using 2 i 5 41 42 43 
                ts ts_i assms(1) n 0 ts_n a_n_ts
          apply (auto simp add: unat_word_ariths unat_of_nat split: if_split_asm)[1]
          apply (simp add: unat_sub_if_size)
          using 42 44
          apply (auto simp add: unat_of_nat unat_word_ariths word_size split: if_split_asm)[1]
          apply unat_arith
          by unat_arith
        hence 4: "unat (a' - a\<^sub>0 + 1) * 8 - Suc 0 < LENGTH('a)"
          using assms(7)
          by unat_arith
        have "mem s' a' = (s' \<turnstile> *[a',Suc 0] :: 8word)"
         and "mem s a' = (s \<turnstile> *[a',Suc 0] :: 8word)"
          unfolding read_region_def
          using 3
          by (auto simp add: Abs_region_inverse_unconditional Let'_def read_bytes.simps(2))
        hence "mem s' a' = mem s a'"
          apply auto
          apply (subst read_byte_from_larger_region[of a\<^sub>0 _ si, where 'a='a])
          using 1 2 3 4 5 6 assms(5) apply auto
          apply (subst read_byte_from_larger_region[of a\<^sub>0 _ si, where 'a='a])
          using 1 2 3 4 assms by auto
      }
      hence "read_bytes (mem s') (a + of_nat i * of_nat ts, ts) = read_bytes (mem s) (a + of_nat i * of_nat ts, ts)"
        using 3
        apply (auto simp add: read_region_def)
        apply (rule read_bytes_focus)
        by auto
      hence "(cat_bytes (rev (read_bytes (mem s') (a + of_nat i * of_nat ts, ts))) ::'b word) !! j = (cat_bytes (rev (read_bytes (mem s) (a + of_nat i * of_nat ts, ts)))::'b word) !! j"
        by (auto simp add: test_bit_of_cat_bytes length_read_bytes)
    }
    hence "(cat_bytes (rev (read_bytes (mem s') (a + of_nat i * of_nat ts, ts))) ::'b word) = (cat_bytes (rev (read_bytes (mem s) (a + of_nat i * of_nat ts, ts)))::'b word)"
      apply (intro word_eqI)
      by (auto simp add: word_size)
    thus ?thesis
      using i 3
      by (auto simp add: nth_read_array read_region_def Abs_region_inverse_unconditional Let'_def field_simps)
qed


lemma read_array_eqI_generic:
  assumes "ts > 0"
    and "s' \<turnstile> *[a\<^sub>0,si] = (s \<turnstile> *[a\<^sub>0,si] :: 'a::len word)"
    and "a \<ge> a\<^sub>0"
    and "unat (a - a\<^sub>0) + ts * n \<le> si"
    and "no_block_overflow (a\<^sub>0, si)"
    and "no_block_overflow (a, ts * n)"
    and "unat (a + of_nat n * of_nat ts - a\<^sub>0) * 8 \<le> LENGTH('a)"
  shows "read_array s' a ts n = (read_array s a ts n ::'b::len word list)"
proof-
  {
    fix i
    assume i: "i < n"
    have 3: "no_block_overflow (a + of_nat i * of_nat ts, of_nat ts)"
      apply (rule no_block_overflow_block_in_memory)
      using assms i
      by auto
    have "(read_array s' a ts n :: 'b word list)! i = (read_array s a ts n :: 'b word list) ! i"
      using block_in_memory_eq[OF assms i,where 'b='b]
            i 3
      by (auto simp add: nth_read_array read_region_def Abs_region_inverse_unconditional Let'_def field_simps split: if_split_asm)
  }
  thus ?thesis
    apply (intro nth_equalityI)
    by (auto simp add: length_read_array)
qed

lemma read_array_8_eqI:
assumes "s' \<turnstile> *[a\<^sub>0,n] = (s \<turnstile> *[a\<^sub>0,n] :: 'a::len word)"
    and "no_block_overflow (a\<^sub>0, n)"
    and "n * 8 \<le> LENGTH('a)"
  shows "read_array_8 s' a\<^sub>0 n = read_array_8 s a\<^sub>0 n"
proof-
  have 43: "n < 2^64"
    using assms(2)[unfolded no_block_overflow.simps]
    by unat_arith
  show ?thesis
    apply (simp only: read_array_8_def)
    apply (rule read_array_eqI_generic[OF _ assms(1)])
    using 43 assms
    by (auto simp add: unat_of_nat)
qed

lemma read_array_32_eqI:
assumes "s' \<turnstile> *[a\<^sub>0,n*4] = (s \<turnstile> *[a\<^sub>0,n*4] :: 'a::len word)"
    and "no_block_overflow (a\<^sub>0, n*4)"
    and "n * 4 * 8 \<le> LENGTH('a)"
  shows "read_array_32 s' a\<^sub>0 n = read_array_32 s a\<^sub>0 n"
proof-
  have 43: "n*4 < 2^64"
    using assms(2)[unfolded no_block_overflow.simps]
    by unat_arith
  show ?thesis
    apply (simp only: read_array_32_def)
    apply (rule read_array_eqI_generic[OF _ assms(1)])
    using 43 assms
    apply (auto simp add: unat_of_nat field_simps )
    by (simp add: unat_word_ariths unat_of_nat)
qed


lemma rewrite_byte_of_to_take_bits': (* TODO replaces  old version*)
  fixes w :: "'a::len0 word"
  assumes "l < LENGTH('a) div 8"
  shows "\<lbrace>l\<rbrace>w = ((\<langle>(l+1)*8-1,l*8\<rangle> w)::8 word)"
proof-
  {
    fix n :: nat
    assume "n < 8"
    hence "(\<lbrace>l\<rbrace>w) !! n = ((\<langle>(l+1)*8-1,l*8\<rangle> w)::8 word) !! n"
      using assms
      by (auto simp add: test_bit_of_byte_of test_bit_of_take_bits)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma read_array_8_from_mem:
  assumes "LENGTH('a) div 8 > si - Suc 0"
      and "no_block_overflow (a, si)"
  shows "read_array_8 s a si = (if si = 0 then [] else rev (\<lbrace>si-1,0\<rbrace> (s \<turnstile> *[a,si]::'a::len word)))"
proof-
  {
    fix i
    assume i: "i < si"
    moreover
    have "si < 2^64"
      using i assms(2)
      by (auto simp add: no_block_overflow.simps)
    moreover
    have "a \<le> a + of_nat i"
      using i assms(2)
      apply (auto simp add: no_block_overflow.simps)
      apply unat_arith
      by (auto simp add: unat_of_nat)
    moreover
    have "no_block_overflow (a + of_nat i, Suc 0)"
      using i assms(2)
      apply (auto simp add: no_block_overflow.simps)
      apply unat_arith
      by (auto simp add: unat_of_nat)
    ultimately
    have "read_array_8 s a si ! i = (if si = 0 then [] else rev (\<lbrace>si-1,0\<rbrace> (s \<turnstile> *[a,si]::'a::len word))) ! i"
      apply (subst nth_read_array_8)
      using assms
      apply (auto simp add: rev_nth)
      apply (subst nth_bytes_of)
      apply (auto simp add: rewrite_byte_of_to_take_bits')
      apply (subst read_byte_from_larger_region[of a _ si,where 'a='a])
      by (auto simp add: unat_of_nat unat_word_ariths)
  }
  thus ?thesis
    apply (intro nth_equalityI)
    using assms
    by (auto simp add: length_read_array_8)
qed

lemma read_array_append:
  assumes "ts > 0"
      and "s' \<turnstile> *[a,ts*si] = (s \<turnstile> *[a,ts*si] :: 'a::len word)"
      and "x = read_array s a ts si"
      and "y = read_array s' (a + of_nat (ts * si)) ts si'"
      and "si''  = si' + si"
      and "no_block_overflow (a, ts * si)"
      and "8 * si * ts \<le> LENGTH('a)"
      and "si < 2^64"
      and "ts < 2^64"
  shows "(read_array s' a ts si'' ::'b::len word list) = x @ y"
proof-
  show ?thesis
    apply (rule nth_equalityI)
    using assms
    apply (auto simp add: nth_read_array length_read_array nth_list_update nth_append of_nat_diff field_simps)
    apply (subst block_in_memory_eq[OF assms(1-2),where n=si])
    apply (auto simp add: field_simps)
    apply unat_arith
    by (auto simp add: unat_word_ariths unat_of_nat)
qed

lemma read_array_32_append:
  assumes "s' \<turnstile> *[a,4*si] = (s \<turnstile> *[a,4*si] :: 'a::len word)"
      and "x = read_array_32 s a si"
      and "y = read_array_32 s' (a + 4 * of_nat si) si'"
      and "si''  = si' + si"
      and "no_block_overflow (a, 4 * si)"
      and "32 * si \<le> LENGTH('a)"
      and "si < 2^64"
  shows "(read_array_32 s' a si'') = x @ y"
  using assms
  unfolding read_array_32_def
  apply (subst read_array_append)
  by auto

lemma read_array_8_append:
  assumes "s' \<turnstile> *[a,si] = (s \<turnstile> *[a,si] :: 'a::len word)"
      and "x = read_array_8 s a si"
      and "y = read_array_8 s' (a + of_nat si) si'"
      and "si''  = si' + si"
      and "no_block_overflow (a, si)"
      and "8 * si \<le> LENGTH('a)"
      and "si < 2^64"
  shows "(read_array_8 s' a si'') = x @ y"
  using assms
  unfolding read_array_8_def
  apply (subst read_array_append)
  by auto


lemma x_le_max_word_minus: "\<And> x y :: 64 word . unat x + unat y < 2^64 \<Longrightarrow> x \<le> max_word - y"
  apply unat_arith
  by (auto simp add: max_word_eq)



lemma array_update:
  fixes v :: "'a::len0 word"
  assumes "seps blocks"
      and "(I, a, ts * si) \<in> blocks"
      and "n < si"
      and "ts > 0"
      and "master blocks (of_nat n * of_nat ts + a, ts) I \<Longrightarrow> s' \<turnstile> *[of_nat n * of_nat ts + a,ts] = v"
      and "\<And> i. i < si \<Longrightarrow> i \<noteq> n \<Longrightarrow> master blocks (of_nat i * of_nat ts + a, ts) I \<Longrightarrow> (of_nat i * of_nat ts + a, ts) \<bowtie> (of_nat n * of_nat ts + a, ts) \<Longrightarrow> (s' \<turnstile> *[of_nat i * of_nat ts + a,ts]::'a word) = s \<turnstile> *[of_nat ts * of_nat i + a,ts]"
  shows "array_update s s' a ts si n v"
proof-
  have master: "master blocks (a, of_nat si * of_nat ts) I"
    apply (rule master_if_in_blocks)
    using assms(1,2)
    by (auto simp add: field_simps)
  have 1: "no_block_overflow (a, of_nat si * of_nat ts)"
    apply (rule no_block_overflow_smaller_block[of _ "of_nat si * of_nat ts"])
    apply (rule master_block_implies_no_block_overflow[of blocks _ I])
    using master
    by auto
  have si: "si * of_nat ts < 2^64"
    using 1[unfolded no_block_overflow.simps]
    by unat_arith

  note masters_i = master_for_array_update[OF assms(1-2)]

  {
    fix i
    assume i: "i < si"
    have 0: "no_block_overflow (a + (of_nat i * of_nat ts), ts)"
      apply (rule master_block_implies_no_block_overflow[of blocks _ I])
      using masters_i[of i] i assms(4)
      by (auto simp add: field_simps)

    have ts_si: "si * ts < 2^64"
      using 1
      by (auto simp add: no_block_overflow.simps)
    have ts: "ts < 2^64"
      apply (rule le_less_trans[OF _ ts_si])
      using assms(3)
      by (auto)
    have si: "si < 2^64"
      apply (rule le_less_trans[OF _ ts_si])
      using assms(4)
      by (auto)    
    have n: "n < 2^64"
      apply (rule le_less_trans[OF _ si])
      using assms(3)
      by (auto)    
    have i_le: "i < 2^64"
      apply (rule le_less_trans[OF _ si])
      using i
      by (auto)    
    have ts_i: "i * ts < 2^64"
      apply (rule le_less_trans[OF _ ts_si])
      using i
      by (auto)    
    have ts_n: "n * ts < 2^64"
      apply (rule le_less_trans[OF _ ts_si])
      using assms(3)
      by (auto)    
    have "unat (of_nat i * of_nat ts :: 64 word) < si * of_nat ts"
      using i ts ts_i i i_le assms(4)
      apply unat_arith
      by (auto simp add: unat_ucast unat_of_nat is_up unat_word_ariths)
    hence 44: "unat a + unat (of_nat i * of_nat ts :: 64 word) < 2^64"
      using 1[unfolded no_block_overflow.simps]
      by unat_arith        
    have 00: "no_block_overflow (a + (of_nat n * of_nat ts), of_nat ts)"
      apply (rule master_block_implies_no_block_overflow[of blocks _ I])
      using masters_i[of n] assms(3,4)
      by (auto simp add: field_simps)
    have 45: "unat a + ts * n \<le> unat a + ts * si"
      using assms(3)
      by unat_arith
    hence 4: "unat a + of_nat ts * n < 2^64"
      using 1[unfolded no_block_overflow.simps] assms(3)
      apply (auto simp add: unat_word_ariths unat_ucast is_up unat_of_nat )
      apply (rule le_less_trans[OF 45])
      by (auto simp add: field_simps)
    have 5: "ts + i * ts < 2^64"
      apply (rule le_less_trans[of _ "si*ts"])
      using i mult_le_mono1[of "i+1" si ts]
      using i ts_si
      by auto
    have sep: "i \<noteq> n \<Longrightarrow> (of_nat i * of_nat ts + a, ts) \<bowtie> (a + of_nat ts * of_nat n, ts)"
    proof(cases "i < n")
      case True
      have 3: "unat (of_nat ts + of_nat i * of_nat ts :: 64 word) = of_nat ts + unat (of_nat i * of_nat ts :: 64 word)"
        using i si
        apply unat_arith
        using ts i ts_i i_le 5
        by (auto simp add: unat_word_ariths unat_of_nat)
      have "a \<le> a + (of_nat ts + (of_nat i * of_nat ts))"
        apply (rule x_less_x_plus_y)
        apply (rule x_le_max_word_minus)
        using 0[unfolded no_block_overflow.simps]
        apply (auto simp add: 3)   
        apply unat_arith
        using 44
        by (auto)
      moreover
      have "a \<le> a + of_nat ts * of_nat n"
        apply (rule x_less_x_plus_y)
        apply (rule x_le_max_word_minus)
        using 00[unfolded no_block_overflow.simps]
        apply (auto)   
        apply unat_arith
        apply (auto simp add: unat_word_ariths unat_ucast is_up)
        apply (auto simp add: field_simps)[1]
        using 4 ts n
        by (auto simp add: unat_of_nat)[1]
      moreover
      have "(of_nat ts::64 word) + of_nat i * of_nat ts \<le> of_nat ts * of_nat n"
        using True assms(3) si
        apply unat_arith
        using i_le ts n 5  ts_n
        apply (auto simp add: unat_word_ariths unat_of_nat unat_ucast is_up )
        apply (auto simp add: field_simps)
        using i mult_le_mono1[of "i+1" n ts] 
        by auto
      ultimately
      show ?thesis
        by (auto simp add: sep.simps field_simps)
    next
      case False
      have 5: "ts + ts * n < 2^64"
        apply (rule le_less_trans[of _ "si*ts"])
        using assms(3) mult_le_mono1[of "n+1" si ts] ts_si
        by (auto simp add: field_simps)
      have 6: "unat a + n < 2^64"
        apply (rule le_less_trans[OF _ 4])
        using assms(4)
        by auto
      assume "i \<noteq> n"
      hence "a + (of_nat ts + of_nat ts * of_nat n) \<le> a + of_nat i * of_nat ts"
        apply (subst plus_less_left_cancel_nowrap)
        apply (rule x_less_x_plus_y)
        apply (rule x_le_max_word_minus)
        using 00[unfolded no_block_overflow.simps] 1 4 ts 5 6 ts_n
        apply (auto simp add: unat_word_ariths unat_ucast is_up unat_of_nat)[1]
        apply (auto simp add: field_simps)[1]
        apply (rule x_less_x_plus_y)
        apply (rule x_le_max_word_minus)
        apply (rule 44)
        using False 
        apply unat_arith
        using ts_n i False assms(3) si ts 5 ts_i
        apply (auto simp add: unat_word_ariths unat_ucast is_up unat_of_nat)
        using i mult_le_mono1[of "n+1" i ts] 
        by (auto simp add: field_simps)
      thus ?thesis
        by (auto simp add: sep.simps field_simps)
    qed
  }
  note sep = this
  show ?thesis
    unfolding array_update_def
    using assms sep masters_i
    by (auto simp add: field_simps)
qed



lemma drop_read_array:
  assumes "m \<le> si"
      and "0 < ts"
      and "0 < si"
      and "si' = si - m"
      and "a' = a + of_nat m * of_nat ts"
      and "s' \<turnstile> *[a,si * ts] = (s \<turnstile> *[a,si * ts] :: 'x::len word)"
      and "si * ts * 8 \<le> LENGTH('x)"
      and "no_block_overflow (a, si * ts)"
  shows "(read_array s' a' ts si'::'y::len word list) = drop m (read_array s a ts si)"
proof-
  {
    fix i
    assume 1: "i < si - m"
    hence 3: "i + m < si"
      by auto
    have 2: "unat (of_nat si * of_nat ts :: 64 word) = si * ts"
      using assms(2,3,8)
      apply (auto simp add: unat_word_ariths unat_of_nat no_block_overflow.simps)
      apply (subst mod_less)
      apply (rule le_less_trans[of _ "unat a + si * ts"])
      apply auto
      apply (rule le_trans[of _ "si * ts"])
      apply auto
      apply (subst mod_less)
      apply (rule le_less_trans[of _ "unat a + si * ts"])
      apply auto
      apply (rule le_trans[of _ "si * ts"])
      apply auto
      done
    hence "(read_array s' a' ts si'::'y::len word list) ! i = (drop m (read_array s a ts si::'y::len word list)) ! i"
      using 1 3 assms
      apply (auto simp add: nth_read_array field_simps length_read_array)
      using block_in_memory_eq[of ts s' a "ts*si" s a si "i+m",where 'a='x and 'b='y]
      by (auto simp add: field_simps)
  }
  thus ?thesis
    using assms
    apply (intro nth_equalityI)
    by (auto simp add: length_read_array min_def)
qed

lemma drop_read_array_8:
  assumes "m \<le> si"
      and "0 < si"
      and "si' = si - m"
      and "a' = a + of_nat m"
      and "s' \<turnstile> *[a,si] = (s \<turnstile> *[a,si] :: 'x::len word)"
      and "si * 8 \<le> LENGTH('x)"
      and "no_block_overflow (a, si)"
  shows "read_array_8 s' a' si' = drop m (read_array_8 s a si)"
  using assms
  apply (auto simp add: read_array_8_def)
  apply (subst drop_read_array)
  by auto




lemma read_array_write_reg:
  shows "read_array (s\<lparr>regs := x\<rparr>) a ts n = read_array s a ts n"
  by(induct s a ts n rule: read_array.induct,auto)

lemma read_array_8_write_reg:
  shows "read_array_8 (s\<lparr>regs := x\<rparr>) a n = read_array_8 s a n"
  unfolding read_array_8_def
  by (rule read_array_write_reg)

lemma read_array_32_write_reg:
  shows "read_array_32 (s\<lparr>regs := x\<rparr>) a n = read_array_32 s a n"
  unfolding read_array_32_def
  by (rule read_array_write_reg)

lemma read_array_write_flag:
  shows "read_array (s\<lparr>flags := x\<rparr>) a ts n = read_array s a ts n"
  by(induct s a ts n rule: read_array.induct,auto)

lemma read_array_8_write_flag:
  shows "read_array_8 (s\<lparr>flags := x\<rparr>) a n = read_array_8 s a n"
  unfolding read_array_8_def
  by (rule read_array_write_flag)

lemma read_array_32_write_flag:
  shows "read_array_32 (s\<lparr>flags := x\<rparr>) a n = read_array_32 s a n"
  unfolding read_array_32_def
  by (rule read_array_write_flag)

end
end