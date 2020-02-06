theory Presimplified_Semantics
  imports "Presimplified_Semantics_Manual"
begin

named_theorems get_semantics_rewriting

context presimplified_semantics
begin

abbreviation "write_mem \<alpha>  \<sigma> a v s \<equiv> bv_put \<alpha>  (Memory s a) (ucast v,0) \<sigma>"

abbreviation "read_mem64 \<alpha> \<sigma> s a \<equiv> fst (read_memory \<alpha> \<sigma> s a)"

abbreviation "write_mem32 \<alpha>  \<sigma> a (v::32 word) \<equiv>
                \<sigma>\<lparr>mem := write_block ((resolve_address \<alpha> \<sigma> a) \<rhd> rev (\<lbrace>3,0\<rbrace> v)) (mem \<sigma>)\<rparr>"

abbreviation "write_mem64 \<alpha>  \<sigma> a (v::64 word) \<equiv>
                \<sigma>\<lparr>mem := write_block ((resolve_address \<alpha> \<sigma> a) \<rhd> rev (\<lbrace>7,0\<rbrace> v)) (mem \<sigma>)\<rparr>"

lemma state_eqI:
  fixes \<sigma> \<sigma>' :: state
  assumes "regs \<sigma> = regs \<sigma>'"
      and "mem \<sigma> = mem \<sigma>'"
      and "flags \<sigma> = flags \<sigma>'"
    shows "\<sigma> = \<sigma>'"
  using assms
  by (cases \<sigma>,cases \<sigma>',auto)

lemma flags_eqI:
  assumes "f flag_zf = f' flag_zf"
      and "f flag_cf = f' flag_cf"
      and "f flag_pf = f' flag_pf"
      and "f flag_sf = f' flag_sf"
      and "f flag_of = f' flag_of"
    shows "f = f'"
  apply (rule ext)
  subgoal for flg
    using assms
    by (cases flg,auto)
  done


lemma parity_ucast[get_semantics_rewriting]:
  fixes a :: "'b::len0 word"
  assumes "LENGTH('a) > LENGTH('b)"
      and "LENGTH('b) \<ge> 8"
  shows "parity (ucast a :: 'a::len0 word) = parity a"
  using assms
  unfolding parity_def
  by (auto simp add: to_bl_ucast)  

lemma test_bit_of_argument_of_take_bits[get_semantics_rewriting]:
 fixes a :: "'a::len0 word"
   and x :: "'b::len0 word"
 assumes "\<langle>h,0\<rangle>a = x"
     and "n \<le> h"
     and "h < LENGTH('a)"
     and "n < LENGTH('b)"
   shows "a !! n = x !! n"
proof-
 have "a !! n = (\<langle>h,0\<rangle>a :: 'b::len0 word) !! n"
   apply (subst test_bit_of_take_bits)
   using assms
   by (auto)
 also have "... = x !! n"
   apply (subst assms(1))
   by simp
 finally
 show ?thesis
   by simp
qed






(*---------------------------------------------------proofs on nop ---------------------------------------*)

lemma is_manual_nop[is_manual]:
  shows "is_manual assembly semantics (Nullary (IS_8088 Nop)) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_nop[presimplify]:
  shows "get_semantics \<alpha> semantics (Nullary (IS_8088 Nop)) si = id"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (rewrite_one_let')+
  apply simp
  done

lemma unat_take_bits_remove_32bits[get_semantics_rewriting]:
  fixes a :: "32 word"
  assumes "LENGTH('a) \<ge> 32"
  shows "unat (\<langle>31,0\<rangle>a :: 'a::len0 word) = unat a"
proof-
  have 1: "(\<langle>31,0\<rangle>a :: 'a::len0 word) = (ucast a :: 'a::len0 word)"
    by (auto simp add:take_bits_remove)
  show ?thesis
  using assms
  by (auto simp add:1 is_up unat_ucast)
qed


lemma test_bit_of_take_bits_for_diff_size[get_semantics_rewriting]:
  fixes a b:: "64 word"
  assumes "LENGTH('a) > 64"
  shows "((\<langle>63,0\<rangle>a + \<langle>63,0\<rangle>b) ::'a::len0 word ) !! 63 = (a + b) !! 63"
proof-
  {
    let ?x = "((\<langle>63,0\<rangle>a + \<langle>63,0\<rangle>b) ::'a::len0 word )"
    have 1:"(\<langle>63,0\<rangle>?x :: 64 word) = a + b"
      using assms
      apply (subst take_bits_plus_64bit(1))
      by auto
    show ?thesis
      apply (subst test_bit_of_argument_of_take_bits[where ?h=63 and ?x="a+b"])
      using assms
      by auto
  }
qed

lemma stupid[get_semantics_rewriting]:
 fixes a :: "'a::len0 word"
 assumes "LENGTH('a) = x"
 shows "a = a"
 by auto


lemma unat_take_bits_32word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "unat (\<langle>31,0\<rangle>a :: 33 word) = unat (\<langle>31,0\<rangle>a :: 32 word)"
proof -
    have 1:"(\<langle>31,0\<rangle>a :: 33 word) = (ucast (\<langle>31,0\<rangle>a :: 32 word))"
      by (auto simp add:simp_rules)
    show ?thesis
      apply (subst 1)
      apply (subst unat_ucast)
      by (auto simp add: is_up)
  qed

lemma test_bit_of_different_word_size_32[get_semantics_rewriting]:
  fixes a b:: "64 word"
  assumes "LENGTH('a) = 33"
  shows "((\<langle>31,0\<rangle>a + \<langle>31,0\<rangle>b) ::'a::len0 word ) !! 31 = ((\<langle>31,0\<rangle>a + \<langle>31,0\<rangle>b) :: 32 word ) !! 31"
proof-
  {
    let ?x = "((\<langle>31,0\<rangle>a + \<langle>31,0\<rangle>b) ::'a::len0 word )"
    have 1:"(\<langle>31,0\<rangle>?x :: 32 word) = ((\<langle>31,0\<rangle>a + \<langle>31,0\<rangle>b) :: 32 word)"
      using assms
      apply (subst take_bits_plus)
      by auto
    show ?thesis
      using assms
      apply (subst test_bit_of_argument_of_take_bits[where ?h=31 and ?x="(\<langle>31,0\<rangle>a + \<langle>31,0\<rangle>b) :: 32 word"])
      by (auto simp add:ucast_id)
  }
qed

lemma test_bit_2p_minus_1[get_semantics_rewriting]:
  shows "((2 ^ LENGTH('a) - 1) :: 'a::len word) !! n = (n < LENGTH('a))"
proof-
  show ?thesis
    apply (subst max_word_eq[symmetric])
    by (auto simp add:word_size)
qed

lemma or_mask_all_0[get_semantics_rewriting]:
  fixes a :: "'a :: len word"
  shows "a OR NOT mask LENGTH('a) = a"
proof-
  have 1:"NOT (2 ^ LENGTH('a) - 1) = (0 :: 'a::len word)"
  proof-
    {
      fix i
      assume "i < LENGTH('a)" 
      have "(NOT ((2 ^ LENGTH('a) - 1) :: 'a::len word)) !! i = (0 :: 'a::len word) !! i"
        apply (subst max_word_eq[symmetric])
        by (auto simp add:test_bit_of_take_bits test_bit_2p_minus_1)
    }
    thus ?thesis
    apply (intro word_eqI)
      by (auto simp add: word_size)
  qed
  show ?thesis
    by (auto simp add:mask_def 1)
qed

lemma useless_and[get_semantics_rewriting]:
  fixes a::"'a::len word"
  shows "a AND ((2^LENGTH('a) - 1) :: 'a:: len word) = (a)"
proof-
  show ?thesis
    using max_word_eq
    apply (subst max_word_eq[symmetric])
    by auto
qed

lemma p2_ge_one:
  shows " Suc 0 \<le> nat (2 ^ x)"
  by(induct x,auto)

lemma nat_remove_2pxminusOne[get_semantics_rewriting]:
  shows "nat (2 ^ x - 1) = 2 ^ x - Suc 0"
proof(induct x)
  case 0
  thus ?case 
    by auto
next
  case (Suc x)
  have 1: "2 * nat (2 ^ x) - Suc 0 = nat (2 ^ x) - Suc 0 + nat (2^x)"
    by (auto simp add: field_simps)
  show ?case
    using Suc 
    apply (auto simp add: nat_diff_distrib' nat_mult_distrib)
    apply (subst 1)
    apply auto
    apply (subst diff_add_assoc)
    by (auto simp add: p2_ge_one)
qed

lemma unat_max_word[get_semantics_rewriting]:
  shows "unat (max_word :: 'a::len word) = 2^LENGTH('a) - 1"
  apply (subst max_word_def)
  apply auto
  apply (subst unat_def)
  apply (subst int_word_uint)
  apply (auto simp add: m1mod2k)
  apply (subst nat_remove_2pxminusOne)
  by simp

lemma unat_2px[get_semantics_rewriting]:
  assumes "x < LENGTH('a)"
  shows "unat (2 ^ x :: 'a::len word) = 2 ^ x"
  using assms
proof (induct x)
  case 0
  thus ?case
    by auto
next
  case (Suc x)
  have 1: "2 * 2 ^ x = (2 ^ x + 2 ^ x :: 'a word)"
    by (auto simp add: field_simps)
  show ?case
    using Suc
    apply (auto simp add: )
    apply (subst 1)
    apply (subst unat_word_ariths)
    apply (auto simp add: field_simps)
    apply (subst mod_less)
    using power_strict_increasing_iff[of 2 "x+1" "LENGTH('a)"]
    by (auto simp add: field_simps mult_2)
qed


lemma test_bit_2p_of_diff_length[get_semantics_rewriting]:
  assumes "h < LENGTH('a)"
      and "LENGTH('h::len) = h"
    shows "((2 ^ h - 1) :: 'a::len word) = ucast (max_word :: 'h word)"
    using assms
    apply (auto)
    apply unat_arith
    by (auto simp add: unat_ucast is_up unat_max_word unat_2px)


lemma useless_sextend_hardocded_65_word:
  fixes a :: "64 word"
  shows "\<langle>63,0\<rangle>((sextend (\<langle>63,0\<rangle>a :: 1000 word) 64 64) :: 1000 word) = (\<langle>63,0\<rangle>a ::65 word)"
proof-
  show ?thesis
      unfolding sextend.simps
      apply (auto simp add: simp_rules mask_def)
      apply (subst take_bits_bitOR)
       apply (auto simp add:take_bits_remove ucast_id)
      apply (subst useless_and[where ?a="a :: 64 word", simplified])
      by auto
  qed

lemma useless_sextend_hardocded_64_64_word:
  fixes a :: "64 word"
  shows "\<langle>63,0\<rangle>((sextend (\<langle>63,0\<rangle>a :: 1000 word) 64 64) :: 1000 word) = (\<langle>63,0\<rangle>a ::65 word)"
proof-
  show ?thesis
      unfolding sextend.simps
      apply (auto simp add: simp_rules mask_def)
      apply (subst take_bits_bitOR)
       apply (auto simp add:take_bits_remove ucast_id)
      apply (subst useless_and[where ?a="a :: 64 word", simplified])
      by auto
  qed

lemma useless_sextend_hardocded[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "\<langle>63,0\<rangle>((sextend (\<langle>63,0\<rangle>a :: 1000 word) 64 64) :: 1000 word) = (a ::64 word)"
proof-
  show ?thesis
      unfolding sextend.simps
      apply (auto simp add: simp_rules mask_def)
      apply (subst Word.word_bool_alg.conj_disj_distrib2)
       apply (auto)
       apply (subst take_bits_remove[where ?w="a" and ?h="63", simplified])
       apply (subst take_bits_bitAND)
       apply auto
      apply (auto simp add:ucast_id)
      apply (subst useless_and[where ?a="a :: 64 word", simplified])
      by auto
  qed


lemma and_2p_minus_1_extend[get_semantics_rewriting]:
  fixes a:: "64 word"
  shows "(\<langle>63,0\<rangle>a :: 1000 word) AND 2^(LENGTH(64)) - 1 = (\<langle>63,0\<rangle>a :: 1000 word)"
proof-
  {
    fix i n :: nat
    assume a:"n < 1000"
    have 1: "(( 2^(LENGTH(64)) - 1) :: 1000 word) = \<langle>63,0\<rangle>(( 2^(LENGTH(64)) - 1) :: 64 word)"
      by auto
    hence "((\<langle>63,0\<rangle>a :: 1000 word) AND (2^(LENGTH(64)) - 1 :: 1000 word)) !! n = (\<langle>63,0\<rangle>a :: 1000 word)  !! n"
      apply (subst 1)
      apply (subst max_word_eq[symmetric])
      apply (subst take_bits_bitAND[symmetric]) 
      by (auto simp add:take_bits_remove)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed


lemma useless_sextend_hardocded_ucast[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "((sextend (\<langle>63,0\<rangle>a :: 1000 word) 64 64) :: 1000 word) = (ucast a ::1000 word)"
proof-
  show ?thesis
      unfolding sextend.simps
      apply (auto simp add: simp_rules mask_def)
      apply (subst Word.word_bool_alg.conj_disj_distrib2)
       apply (auto)
      subgoal
        apply (subst and_2p_minus_1_extend[simplified])
        apply (subst take_bits_remove[where ?w="a" and ?h="63", simplified])
        by auto
      subgoal
        apply (subst take_bits_remove[where ?w="a" and ?h="63", simplified])
        by auto
      done
 qed

lemma take_bits_lt_bit64[get_semantics_rewriting]:
  fixes a b :: "'b::len0 word"
  assumes "64 \<le> LENGTH('a)"
      and "64 \<le> LENGTH('b)"
  shows "(((\<langle>63,0\<rangle>a)::'a::len0 word) < ((\<langle>63,0\<rangle>b)::'a::len0 word)) = (((\<langle>63,0\<rangle>a)::64 word) < ((\<langle>63,0\<rangle>b)::64 word))"
proof-
  have 1: "\<forall>i\<ge>64. i < length (rev (to_bl ((\<langle>63,0\<rangle>a)::'a::len0 word))) \<longrightarrow> \<not>rev (to_bl ((\<langle>63,0\<rangle>a)::'a::len0 word)) ! i"
    using assms
    by (auto simp add: rev_nth test_bit_of_take_bits to_bl_nth word_size)
  have 2: "\<forall>i\<ge>64. i < length (rev (to_bl ((\<langle>63,0\<rangle>b)::'a::len0 word))) \<longrightarrow> \<not>rev (to_bl ((\<langle>63,0\<rangle>b)::'a::len0 word)) ! i"
    using assms
    by (auto simp add: rev_nth test_bit_of_take_bits to_bl_nth word_size)
  have 3: "\<And> a ::'b::len0 word . take 64 (rev (to_bl ((\<langle>63,0\<rangle>a)::'a::len0 word))) = rev (to_bl ((\<langle>63,0\<rangle>a)::64 word))"
  proof-
    fix a :: "'b::len0 word"
    {
      fix i :: nat
      assume "i < 64"
      hence "take 64 (rev (to_bl ((\<langle>63,0\<rangle>a)::'a::len0 word))) ! i = rev (to_bl ((\<langle>63,0\<rangle>a)::64 word)) ! i"
        using assms
        by (auto simp add: rev_nth to_bl_nth word_size test_bit_of_take_bits)
    }
    thus "?thesis a"
      using assms
      apply (intro nth_equalityI)
      by (auto)
  qed

  show ?thesis
    apply (auto simp add: word_less_rbl)
    apply (subst (asm) rev_bl_order_take[of 64])
    using 1 2 3
    apply auto
    apply (subst rev_bl_order_take[of 64])
    using 1 2 3
    by auto
qed

lemma take_bits_le_bit64[get_semantics_rewriting]:
  fixes a b :: "'b::len0 word"
  assumes "64 \<le> LENGTH('a)"
      and "64 \<le> LENGTH('b)"
  shows "(((\<langle>63,0\<rangle>a)::'a::len0 word) \<le> ((\<langle>63,0\<rangle>b)::'a::len0 word)) = (((\<langle>63,0\<rangle>a)::64 word) \<le> ((\<langle>63,0\<rangle>b)::64 word))"
proof-
  have "(((\<langle>63,0\<rangle>a)::'a::len0 word) = ((\<langle>63,0\<rangle>b)::'a::len0 word)) = (((\<langle>63,0\<rangle>a)::64 word) = ((\<langle>63,0\<rangle>b)::64 word))"
  proof-
    { fix i :: nat
      assume "(((\<langle>63,0\<rangle>a)::'a::len0 word) = ((\<langle>63,0\<rangle>b)::'a::len0 word))"
      hence "\<forall> i < 64 . (((\<langle>63,0\<rangle>a)::'a::len0 word) !! i = (((\<langle>63,0\<rangle>b)::'a::len0 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
   
      hence "\<forall> i < 64 . (((\<langle>63,0\<rangle>a)::64 word) !! i = (((\<langle>63,0\<rangle>b)::64 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
      hence "(((\<langle>63,0\<rangle>a)::64 word) = ((\<langle>63,0\<rangle>b)::64 word))"
        apply (intro word_eqI)
        by (auto simp add: word_size)
    }
    moreover
    {
      assume "(((\<langle>63,0\<rangle>a)::64 word) = ((\<langle>63,0\<rangle>b)::64 word))"
      hence "\<forall> i < 64 . (((\<langle>63,0\<rangle>a)::64 word) !! i = (((\<langle>63,0\<rangle>b)::64 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
      hence "\<forall> i < LENGTH('a) . (((\<langle>63,0\<rangle>a)::'a::len0 word) !! i = (((\<langle>63,0\<rangle>b)::'a::len0 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
      hence "(((\<langle>63,0\<rangle>a)::'a::len0 word) = ((\<langle>63,0\<rangle>b)::'a::len0 word))"
        using assms
        apply (intro word_eqI)
        by (auto simp add: word_size)
    }
    ultimately
    show ?thesis
      by auto
  qed
  thus ?thesis
    using assms
    apply (cases "(((\<langle>63,0\<rangle>a)::'a::len0 word) = ((\<langle>63,0\<rangle>b)::'a::len0 word))"; cases "(((\<langle>63,0\<rangle>a)::64 word) = ((\<langle>63,0\<rangle>b)::64 word))";auto)
    by (meson less_imp_le_nat linorder_not_le take_bits_lt_bit64)+
qed



lemma overflow_sub_bit64[get_semantics_rewriting]:
  fixes a b:: "'a :: len0 word"
  assumes "64 \<le> LENGTH('a)"
  shows "((1::65 word) + (((\<langle>63,0\<rangle>a)::65 word) + ucast (NOT ((\<langle>63,0\<rangle>b):: 64 word)))) !! 64 = (((\<langle>63,0\<rangle>a)::64 word) \<ge> \<langle>63,0\<rangle>b)"
proof-
  have 3: "(((\<langle>63,0\<rangle>a)::65 word) \<ge> \<langle>63,0\<rangle>b) = (((\<langle>63,0\<rangle>a)::64 word) \<ge> \<langle>63,0\<rangle>b)"
    using assms
    by (subst take_bits_le_bit64,simp,simp,simp)
  have 1: "\<not> ((\<langle>63,0\<rangle>a)::65 word) !! 64"
   and 2: "\<not> ((\<langle>63,0\<rangle>b)::65 word) !! 64"
    using assms
    by (auto simp add: test_bit_of_take_bits)
  have "uint ((\<langle>63,0\<rangle>a)::65 word) < 18446744073709551616"
   and "uint ((\<langle>63,0\<rangle>b)::65 word) < 18446744073709551616"
    using msb_is_gt_2p[unfolded msb_nth,where 'a=65,simplified] 1
    apply (uint_arith)
    using msb_is_gt_2p[unfolded msb_nth,where 'a=65,simplified] 2
    by (uint_arith)
  hence "((1::65 word) + (((\<langle>63,0\<rangle>a)::65 word) + ucast (NOT ((\<langle>63,0\<rangle>b):: 64 word)))) !! 64 = (((\<langle>63,0\<rangle>a)::65 word) \<ge> \<langle>63,0\<rangle>b)"
    apply (subst ucast_bitNOT)
    apply simp
    apply (subst twos_complement_subtraction)
    apply simp
    apply (subst msb_is_gt_2p[unfolded msb_nth,where 'a=65,simplified])
    apply auto
    apply uint_arith
    using assms
    apply (auto simp add: is_up)
    apply uint_arith
    using assms
    by (auto simp add: is_up)
  thus ?thesis
    using 3
    by auto
qed



lemma sign_sub_bit64[get_semantics_rewriting]:
  fixes a b:: "'a :: len0 word"
  assumes "63 < LENGTH('a)"
  shows "((1::65 word) + (((\<langle>63,0\<rangle>a)::65 word) + ucast (NOT ((\<langle>63,0\<rangle>b):: 64 word)))) !! 63 \<longleftrightarrow> sint (((\<langle>63,0\<rangle>a):: 64 word) - \<langle>63,0\<rangle>b) < 0"
proof-
  have 1: "\<And> a :: 65 word . a !! 63 = ((\<langle>63,0\<rangle>a):: 64 word) !! 63"
    using assms
    by (auto simp add: test_bit_of_take_bits nth_ucast)
  have 2: "\<langle>63,0\<rangle>((1::65 word) + (((\<langle>63,0\<rangle>a)::65 word) + ucast (NOT ((\<langle>63,0\<rangle>b):: 64 word)))) = (((\<langle>63,0\<rangle>a)::64 word) - \<langle>63,0\<rangle>b)"
    using assms
    apply (subst ucast_bitNOT)
    apply simp
    apply (subst twos_complement_subtraction)
    apply (subst take_bits_minus)
    apply (simp)
    apply (simp)
    by (simp)
  have 3: "... !! 63 \<longleftrightarrow> sint (((\<langle>63,0\<rangle>a):: 64 word) - \<langle>63,0\<rangle>b) < 0"
    using msb_nth[symmetric, where 'a=64]
    by (simp add: word_msb_sint)
  show ?thesis
    apply (subst 1)
    apply (subst 2)
    apply (subst 3)
    by simp
qed

lemma sub_overflow_flag64_bit[get_semantics_rewriting]:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('a) \<ge> 64"
  shows "((\<not> b !! 63) = a !! 63 \<and> b !! 63 = (sint (\<langle>63,0\<rangle>a - \<langle>63,0\<rangle>b::64 word) < 0)) \<longleftrightarrow>
            ((9223372036854775808::64 word) > \<langle>63,0\<rangle>b \<and> sint (\<langle>63,0\<rangle>a - \<langle>63,0\<rangle>b::64 word) \<ge> 0 \<and> (9223372036854775808::64 word) \<le> \<langle>63,0\<rangle>a)
             \<or>
             ((9223372036854775808::64 word) \<le> \<langle>63,0\<rangle>b \<and> sint (\<langle>63,0\<rangle>a - \<langle>63,0\<rangle>b::64 word) < 0 \<and> (9223372036854775808::64 word) > \<langle>63,0\<rangle>a)"
proof-
  have 1: "a !! 63 = msb (\<langle>63,0\<rangle> a :: 64 word)"
   and 2: "b !! 63 = msb (\<langle>63,0\<rangle> b :: 64 word)"
    using assms
    by (auto simp add: msb_nth test_bit_of_take_bits)
  show ?thesis
    using assms
    apply (subst 1)
    apply (subst 2)+
    apply (subst msb_is_gt_2p)+
    apply simp
    by (auto)
qed

find_theorems "(ucast ?x) !! ?v = ?m"


lemma test_32b_of_32AND64_word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "(\<langle>63,0\<rangle>a :: 1000 word) !! 31 = (\<langle>31,0\<rangle>a :: 32 word) !! 31"
  by (simp add: test_bit_of_take_bits)


(*---------------------------------------------------proofs on add ---------------------------------------*)

lemma unat_take_bits_64word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "unat (\<langle>63,0\<rangle>a :: 65 word) = unat (a)"
proof -
    have 1:"(\<langle>63,0\<rangle>a :: 65 word) = (ucast (a))"
      by (auto simp add:simp_rules take_bits_remove)
    show ?thesis
      apply (subst 1)
      apply (subst unat_ucast)
      by (auto simp add: is_up)
  qed



lemma is_manual_add_r64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Add) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_add_r64_r64[presimplify]:
  shows "get_semantics assembly semantics (Binary (IS_8088 Add) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = regs \<sigma> r64_2 :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 := (op1 + op2)),
               flags := (flags \<sigma>)
        (flag_zf := ucast(op1 + op2) = (0 :: 64 word),
         flag_cf := (unat(op1 :: 64 word) + unat(op2 :: 64 word) \<ge> 2^64),
         flag_of := (sint(op1) \<ge> 0  \<and> sint(op2) \<ge> 0 \<and> (sint(op1 + op2) <0))
                    \<or>
                    (sint(op1) < 0 \<and> sint(op2)<0 \<and> (sint(op1 + op2) \<ge>0)),

         flag_sf := sint(op1 + op2) < 0,
         flag_pf := parity(op1 + op2))  \<rparr>)"
proof-
 show ?thesis
   apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
   apply (rewrite_one_let' add: semantics_def)
   apply (rewrite_one_let')+
   apply (simp add: simp_rules )
   apply (intro state_eqI,simp_all)
   subgoal for \<sigma>
     apply (intro flags_eqI,simp_all)
   subgoal
       unfolding bv_slice.simps[simplified]
       apply (auto simp add:simp_rules)
   done
   subgoal 
     apply (subst msb_is_gt_2p[where ?a ="(\<langle>63,0\<rangle>regs \<sigma> r64_1 + \<langle>63,0\<rangle>regs \<sigma> r64_2) :: 65 word", unfolded msb_nth, simplified])
     apply unat_arith
     apply (auto simp add:simp_rules)
     using unat_take_bits_64word[where ?a="regs \<sigma> r64_1"]
     using unat_take_bits_64word[where ?a="regs \<sigma> r64_2"]
     apply auto
     done
   subgoal 
    unfolding bv_slice.simps[simplified]
    apply (auto simp add:parity_ucast)
    done
   subgoal 
     apply (subst word_msb_sint[where ?w="regs \<sigma> r64_1 + regs \<sigma> r64_2 :: 64 word", unfolded msb_nth, symmetric])
     apply (auto simp add:test_bit_of_take_bits simp_rules get_semantics_rewriting)
     done
   subgoal 
     apply (subst test_bit_of_take_bits_for_diff_size)
     using word_msb_sint[where ?w="regs \<sigma> r64_1", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="regs \<sigma> r64_2", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="regs \<sigma> r64_1 + regs \<sigma> r64_2",  unfolded msb_nth, simplified]
     by (auto simp add: simp_rules msb_nth test_bit_of_take_bits )
   done
  done
 qed



lemma test_64b_of_AND1000_word[get_semantics_rewriting]:
  fixes w :: "64 word"
  shows "w !! 63 = (\<langle>63,0\<rangle>w :: 1000 word) !! 63"
  by (simp add: test_bit_of_take_bits)

lemma is_manual_add_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Add) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_add_r32_r32[presimplify]:
  shows "get_semantics assembly semantics (Binary (IS_8088 Add) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32_1 := ucast(op1 + op2)),
               flags := (flags \<sigma>)
        (flag_zf := ucast(op1 + op2) = (0 :: 32 word),
         flag_cf := (unat(op1 :: 32 word) + unat(op2 :: 32 word) \<ge> 2^32),
         flag_of := (sint(op1) \<ge> 0  \<and> sint(op2) \<ge> 0 \<and> (sint(op1 + op2) <0))
                    \<or>
                    (sint(op1) < 0 \<and> sint(op2)<0 \<and> (sint(op1 + op2) \<ge>0)),

         flag_sf := sint(op1 + op2) < 0,
         flag_pf := parity(op1 + op2))  \<rparr>)"
proof-
 show ?thesis
   apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
   apply (rewrite_one_let' add: semantics_def)
   apply (rewrite_one_let')+
   apply (simp add: simp_rules)
   apply (intro state_eqI,simp_all)
   subgoal for \<sigma>
   apply (intro flags_eqI,simp_all)
   subgoal 
     apply (subst msb_is_gt_2p[where ?a ="(\<langle>31,0\<rangle>regs \<sigma> r32_1 + \<langle>31,0\<rangle>regs \<sigma> r32_2) :: 33 word", unfolded msb_nth, simplified])
     apply unat_arith
     apply auto
     using unat_take_bits_32word[where ?a="regs \<sigma> r32_1"]
     using unat_take_bits_32word[where ?a="regs \<sigma> r32_2"]
     apply auto
     done
   subgoal 
     apply (auto simp add:parity_ucast)
     done
   subgoal 
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1 + \<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word", unfolded msb_nth]
     apply (auto simp add:simp_rules msb_nth test_bit_of_take_bits test_bit_of_different_word_size_32)
     done
   subgoal 
     apply (subst test_bit_of_different_word_size_32)
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1 + \<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word",  unfolded msb_nth, simplified]
     by (auto simp add: simp_rules msb_nth test_bit_of_take_bits )
   done
  done
 qed

lemma sextend_useless_64_64:
  fixes a :: "64 word"
  shows "sextend a 64 64 = a"
  unfolding sextend.simps
  apply (auto simp add: simp_rules mask_def)
  apply (subst useless_and[where ?a="a OR - 18446744073709551616 :: 64 word", simplified])
  using or_mask_all_0[of a]
  by auto

lemma is_manual_add_r64_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Add) (Reg (General SixtyFour r64)) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_add_r64_Imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Add) (Reg (General SixtyFour r64)) (Immediate SixtyFour (ImmVal ImmValue))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64 :: 64 word;
                   op2 = (word_of_int ImmValue) :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64 := (op1 + op2)),
               flags := (flags \<sigma>)
        (flag_zf := (op1 + op2) = (0 :: 64 word),
         flag_cf := (unat(op1) + unat(op2) \<ge> 2^64),
         flag_of := (sint(op1) \<ge> 0  \<and> sint(op2) \<ge> 0 \<and> (sint(op1 + op2) <0))
                    \<or>
                    (sint(op1) < 0 \<and> sint(op2)<0 \<and> (sint(op1 + op2) \<ge>0)),

         flag_sf := sint(op1 + op2) < 0,
         flag_pf := parity(op1 + op2))  \<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
   apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules sextend_useless_64_64 useless_sextend_hardocded_ucast useless_sextend_hardocded useless_sextend_hardocded_65_word )
      done
   apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      unfolding bv_slice.simps[simplified]
      apply (auto simp add:take_bits_remove ucast_id)
      done
    subgoal for \<sigma>
      apply (subst msb_is_gt_2p[where ?a="( \<langle>63,0\<rangle>word_of_int ImmValue + \<langle>63,0\<rangle>regs \<sigma> r64 ) :: 65 word", unfolded msb_nth, simplified])
      apply unat_arith
      apply (auto simp add:take_bits_remove)
      apply (auto simp add:unat_ucast is_up)
      done
    subgoal for \<sigma>
      unfolding bv_slice.simps[simplified]
      apply (auto simp add:parity_ucast)
      done
    subgoal for \<sigma>
      using word_msb_sint[where ?w="word_of_int ImmValue + regs \<sigma> r64 :: 64 word", unfolded msb_nth]
      apply (auto simp add:simp_rules msb_nth test_bit_of_take_bits test_bit_of_take_bits_for_diff_size)
      done
    subgoal for \<sigma>
      using word_msb_sint[where ?w="word_of_int ImmValue + regs \<sigma> r64 :: 64 word", unfolded msb_nth]
      using word_msb_sint[where ?w="regs \<sigma> r64 :: 64 word", unfolded msb_nth]
      using word_msb_sint[where ?w="word_of_int ImmValue :: 64 word", unfolded msb_nth]
      by (auto simp add:simp_rules msb_nth test_bit_of_take_bits test_bit_of_take_bits_for_diff_size)
    done
qed

lemma is_manual_add_r32_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Add) (Reg (General ThirtyTwo r32)) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)     

lemma get_semantics_add_r32_Imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Add) (Reg (General ThirtyTwo r32)) (Immediate SixtyFour (ImmVal ImmValue))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word;
                   op2 = \<langle>31,0\<rangle> (word_of_int ImmValue :: 64 word) :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32 := ucast(op1 + op2)),
               flags := (flags \<sigma>)
        (flag_zf := (op1 + op2) = (0 :: 32 word),
         flag_cf := (unat(op1) + unat(op2) \<ge> 2^32),
         flag_of := (sint(op1) \<ge> 0  \<and> sint(op2) \<ge> 0 \<and> (sint(op1 + op2) <0))
                    \<or>
                    (sint(op1) < 0 \<and> sint(op2)<0 \<and> (sint(op1 + op2) \<ge>0)),

         flag_sf := sint(op1 + op2) < 0,
         flag_pf := parity(op1 + op2))  \<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
   apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules)
      done
   apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
     apply (subst msb_is_gt_2p[where ?a ="(\<langle>31,0\<rangle>word_of_int ImmValue + \<langle>31,0\<rangle>regs \<sigma> r32) :: 33 word", unfolded msb_nth, simplified])
     apply unat_arith
     apply auto
     using unat_take_bits_32word[where ?a="word_of_int ImmValue"]
     using unat_take_bits_32word[where ?a="regs \<sigma> r32"]
     apply auto
     done
    subgoal for \<sigma>
      apply (auto simp add:parity_ucast )
      done
    subgoal for \<sigma>
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>word_of_int ImmValue + \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word", unfolded msb_nth]
     apply (auto simp add:simp_rules msb_nth test_bit_of_take_bits test_bit_of_different_word_size_32)
     done
    subgoal for \<sigma>
     apply (subst test_bit_of_different_word_size_32)
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>word_of_int ImmValue :: 32 word", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>word_of_int ImmValue + \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word",  unfolded msb_nth, simplified]
     by (auto simp add: simp_rules msb_nth test_bit_of_take_bits )
    done
qed

lemma read_reg_after_update_flag[get_semantics_rewriting]: "read_reg (\<sigma>\<lparr>flags := x\<rparr>) r = read_reg \<sigma> r"
  by (induct \<sigma> r rule: read_reg.induct,auto)

lemma resolve_address_after_update_flag[get_semantics_rewriting]: "resolve_address \<alpha> (\<sigma>\<lparr>flags := x\<rparr>) Mem = resolve_address \<alpha> \<sigma> Mem"
 by (induct \<alpha> \<sigma> Mem rule: resolve_address.induct, auto simp add:read_reg_after_update_flag)


lemma is_manual_add_m64_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Add) (Memory SixtyFour Mem) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_add_m64_Imm32[presimplify]:
 shows "get_semantics \<alpha> semantics (Binary (IS_8088 Add) (Memory SixtyFour Mem) (Immediate SixtyFour (ImmVal ImmValue))) si =
         (\<lambda> \<sigma> . let a = resolve_address \<alpha> \<sigma> Mem;
                    op1 = read_mem64 \<alpha> \<sigma> 64 Mem;
                    op2 = (word_of_int ImmValue) :: 64 word in
      \<sigma>\<lparr>mem := write_blocks [a \<rhd> rev (\<lbrace>7,0\<rbrace> (op1 + op2))] (mem \<sigma>),
      flags := (flags \<sigma>)
      (flag_zf := (op1 + op2) = (0 :: 64 word),
       flag_cf := (unat(op1) + unat(op2) \<ge> 2^64),
       flag_of := (sint(op1) \<ge> 0 \<and> sint(op2) \<ge> 0 \<and> sint(op1 + op2) < 0)
                  \<or>
                  (sint(op1) < 0 \<and> sint(op2) < 0 \<and> sint(op1 + op2) \<ge> 0),
       flag_sf := sint(op1 + op2) < 0,
       flag_pf := parity(op1 + op2))  \<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')
    apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules sextend_useless_64_64 useless_sextend_hardocded_ucast useless_sextend_hardocded useless_sextend_hardocded_65_word resolve_address_after_update_flag)
      done
   apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:take_bits_remove ucast_id )
      unfolding bv_slice.simps
       apply (auto simp add: sextend_useless_64_64 ucast_id)
      done
    subgoal for \<sigma>
      apply (subst useless_sextend_hardocded_65_word[simplified])
      apply (subst msb_is_gt_2p[where ?a="( \<langle>63,0\<rangle>word_of_int ImmValue + \<langle>63,0\<rangle>read_mem64 \<alpha> \<sigma> 64 Mem) :: 65 word", unfolded msb_nth, simplified])
      apply unat_arith
      apply (auto simp add:take_bits_remove)
      apply (auto simp add:unat_ucast is_up)
      done
    subgoal for \<sigma>
      unfolding bv_slice.simps
      apply (subst useless_sextend_hardocded_65_word[simplified])
      apply (auto simp add:parity_ucast)
      done
    subgoal for \<sigma>
      apply (subst useless_sextend_hardocded_65_word[simplified])
      using word_msb_sint[where ?w="word_of_int ImmValue + read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word", unfolded msb_nth]
      apply (auto simp add:simp_rules msb_nth test_bit_of_take_bits test_bit_of_take_bits_for_diff_size)
      done
    subgoal for \<sigma>
      apply (subst  useless_sextend_hardocded_ucast[where ?a="word_of_int ImmValue"])
      apply (subst useless_sextend_hardocded_65_word[simplified])
      apply (subst  useless_sextend_hardocded_ucast[where ?a="word_of_int ImmValue"])
      using word_msb_sint[where ?w="word_of_int ImmValue +read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word", unfolded msb_nth]
      using word_msb_sint[where ?w="read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word", unfolded msb_nth]
      using word_msb_sint[where ?w="word_of_int ImmValue :: 64 word", unfolded msb_nth]
      by (auto simp add:simp_rules msb_nth test_bit_of_take_bits test_bit_of_take_bits_for_diff_size)
    done
qed

lemma is_manual_add_m32_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Add) (Memory ThirtyTwo Mem) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_add_m32_imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Add) (Memory ThirtyTwo Mem) (Immediate SixtyFour (ImmVal ImmValue))) si =
        (\<lambda> \<sigma> . let a = resolve_address \<alpha> \<sigma> Mem;
                   op1 = \<langle>31,0\<rangle>read_mem64 \<alpha> \<sigma> 32 Mem;
                   op2 = \<langle>31,0\<rangle>(word_of_int ImmValue :: 64 word) :: 32 word
               in
        \<sigma>\<lparr>mem :=  write_blocks [a \<rhd> rev (\<lbrace>3,0\<rbrace> (op1 + op2))] (mem \<sigma>),
               flags := (flags \<sigma>)
        (flag_zf := ucast(op1 + op2) = (0 :: 32 word),
         flag_cf := (unat(op1 :: 32 word) + unat(op2 :: 32 word) \<ge> 2^32),
         flag_of := (sint(op1) \<ge> 0  \<and> sint(op2) \<ge> 0 \<and> (sint(op1 + op2) <0))
                    \<or>
                    (sint(op1) < 0 \<and> sint(op2)<0 \<and> (sint(op1 + op2) \<ge>0)),

         flag_sf := sint(op1 + op2) < 0,
         flag_pf := parity(op1 + op2))  \<rparr>)"
proof-
 show ?thesis
   apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
   apply (rewrite_one_let' add: semantics_def)
   apply (rewrite_one_let')+
   apply (simp add: simp_rules resolve_address_after_update_flag)
   apply (intro state_eqI,simp_all)
   subgoal for \<sigma>
   apply (intro flags_eqI,simp_all)
   subgoal 
     apply (subst msb_is_gt_2p[where ?a ="(\<langle>31,0\<rangle>word_of_int ImmValue + \<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 Mem)) :: 33 word", unfolded msb_nth, simplified])
     apply unat_arith
     apply auto
     using unat_take_bits_32word[where ?a="word_of_int ImmValue"]
     using unat_take_bits_32word[where ?a="fst (read_memory \<alpha> \<sigma> 32 Mem)"]
     apply auto
     done
   subgoal 
     apply (auto simp add:parity_ucast)
     done
   subgoal 
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>word_of_int ImmValue + \<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 Mem) :: 32 word", unfolded msb_nth]
     apply (auto simp add:simp_rules msb_nth test_bit_of_take_bits test_bit_of_different_word_size_32)
     done
   subgoal 
     apply (subst test_bit_of_different_word_size_32)
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>word_of_int ImmValue :: 32 word", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 Mem) :: 32 word", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="\<langle>31,0\<rangle>word_of_int ImmValue + \<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 Mem) :: 32 word",  unfolded msb_nth, simplified]
     by (auto simp add: simp_rules msb_nth test_bit_of_take_bits )
   done
  done
 qed


lemma is_manual_add_m64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Add) (Memory SixtyFour Mem) (Storage (Reg (General SixtyFour reg)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_add_m64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Add) (Memory SixtyFour Mem) (Storage (Reg (General SixtyFour reg)))) si =
        (\<lambda> \<sigma> . let a = resolve_address \<alpha> \<sigma> Mem;
                   op1 = read_mem64 \<alpha> \<sigma> 64 Mem;
                   op2 = regs \<sigma> reg
               in
        \<sigma>\<lparr>mem :=  write_blocks [a \<rhd> rev (\<lbrace>7,0\<rbrace> (op1 + op2))] (mem \<sigma>),
               flags := (flags \<sigma>)
        (flag_zf := ucast(op1 + op2) = (0 :: 64 word),
         flag_cf := (unat(op1 :: 64 word) + unat(op2 :: 64 word) \<ge> 2^64),
         flag_of := (sint(op1) \<ge> 0  \<and> sint(op2) \<ge> 0 \<and> (sint(op1 + op2) <0))
                    \<or>
                    (sint(op1) < 0 \<and> sint(op2)<0 \<and> (sint(op1 + op2) \<ge>0)),

         flag_sf := sint(op1 + op2) < 0,
         flag_pf := parity(op1 + op2))  \<rparr>)"
proof-
 show ?thesis
   apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
   apply (rewrite_one_let' add: semantics_def)
   apply (rewrite_one_let')+
   apply (simp add: simp_rules resolve_address_after_update_flag)
   apply (intro state_eqI,simp_all)
   subgoal for \<sigma>
     apply (intro flags_eqI,simp_all)
   subgoal
       unfolding bv_slice.simps[simplified]
       apply (auto simp add:simp_rules)
   done
   subgoal 
     apply (subst msb_is_gt_2p[where ?a ="(\<langle>63,0\<rangle>regs \<sigma> reg + \<langle>63,0\<rangle>fst (read_memory \<alpha> \<sigma> 64 Mem)) :: 65 word", unfolded msb_nth, simplified])
     apply unat_arith
     apply (auto simp add:simp_rules)
     using unat_take_bits_64word[where ?a="regs \<sigma> reg"]
     using unat_take_bits_64word[where ?a="fst (read_memory \<alpha> \<sigma> 64 Mem)"]
     apply auto
     done
   subgoal 
    unfolding bv_slice.simps[simplified]
    apply (auto simp add:parity_ucast)
    done
   subgoal 
     apply (subst word_msb_sint[where ?w="regs \<sigma> reg + fst (read_memory \<alpha> \<sigma> 64 Mem) :: 64 word", unfolded msb_nth, symmetric])
     apply (auto simp add:test_bit_of_take_bits simp_rules test_bit_of_take_bits_for_diff_size)
     done
   subgoal 
     apply (subst test_bit_of_take_bits_for_diff_size)
     using word_msb_sint[where ?w="regs \<sigma> reg", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="fst (read_memory \<alpha> \<sigma> 64 Mem)", unfolded msb_nth, simplified]
     using word_msb_sint[where ?w="regs \<sigma> reg + fst (read_memory \<alpha> \<sigma> 64 Mem)",  unfolded msb_nth, simplified]
     by (auto simp add: simp_rules msb_nth test_bit_of_take_bits )
   done
  done
 qed




lemma sub_overflow_flag[get_semantics_rewriting]:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('a) \<ge> 32"
  shows "((\<not> b !! 31) = a !! 31 \<and> b !! 31 = (sint (\<langle>31,0\<rangle>a - \<langle>31,0\<rangle>b::32 word) < 0)) \<longleftrightarrow>
            ((2147483648::32 word) > \<langle>31,0\<rangle>b \<and> sint (\<langle>31,0\<rangle>a - \<langle>31,0\<rangle>b::32 word) \<ge> 0 \<and> (2147483648::32 word) \<le> \<langle>31,0\<rangle>a)
             \<or>
             ((2147483648::32 word) \<le> \<langle>31,0\<rangle>b \<and> sint (\<langle>31,0\<rangle>a - \<langle>31,0\<rangle>b::32 word) < 0 \<and> (2147483648::32 word) > \<langle>31,0\<rangle>a)"
proof-
  have 1: "a !! 31 = msb (\<langle>31,0\<rangle> a :: 32 word)"
   and 2: "b !! 31 = msb (\<langle>31,0\<rangle> b :: 32 word)"
    using assms
    by (auto simp add: msb_nth test_bit_of_take_bits)
  show ?thesis
    using assms
    apply (subst 1)
    apply (subst 2)+
    apply (subst msb_is_gt_2p)+
    apply simp
    by (auto)
qed



(*---------------------------------------------------proofs on seta ---------------------------------------*)

lemma is_manual_seta_r8[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_80386 Seta) (Storage (Reg (General Eight r1)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_seta_r8[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_80386 Seta) (Storage (Reg (General Eight r1)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r1 :: 64 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1 := \<langle>63,0\<rangle>((\<langle>63,8\<rangle>regs \<sigma> r1 << 8 :: 64 word) OR (if flags \<sigma> flag_zf \<or> flags \<sigma> flag_cf then 0 else 1))) \<rparr>)"
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
   apply (auto simp add:simp_rules Let'_def)
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto)
   apply (rule word_eqI)
   apply (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl)
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto)
   apply (rule word_eqI)
   apply (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl)
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto)
   apply (rule word_eqI)
   apply (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl)
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto)
   apply (rule word_eqI)
   apply (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl)
    apply(auto simp add:semantics_def simp_rules Let'_def)[1]
    apply(auto simp add:semantics_def simp_rules Let'_def)[1]
    apply(auto simp add:semantics_def simp_rules Let'_def)[1]
    apply(auto simp add:semantics_def simp_rules Let'_def)[1]
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto)
   apply (rule word_eqI)
  apply (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto)
   apply (rule word_eqI)
  by (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl bv_to_bool_def word_lsb_alt)

lemma is_manual_seta_m8[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_80386 Seta) (Storage (Memory Eight Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_seta_m8[presimplify]:
  shows "get_semantics \<alpha> semantics (Unary (IS_80386 Seta) (Storage (Memory Eight Mem))) si =
        (\<lambda> \<sigma> . let a = resolve_address \<alpha> \<sigma> Mem;
                   op1 = (read_mem64 \<alpha> \<sigma> 8 Mem) :: 64 word
            in
             \<sigma>\<lparr>mem := write_blocks [a \<rhd> (if flags \<sigma> flag_zf \<or> flags \<sigma> flag_cf then [0] else [1])] (mem \<sigma>)\<rparr>)"
proof-
  {
    fix x :: "64 word"
    have "rev (\<lbrace>0,0\<rbrace>(\<langle>63,0\<rangle>(\<langle>63,8\<rangle>x << 8 :: 1000 word) :: 64 word)) = [0]"
      apply auto
      apply (intro nth_equalityI)
      apply (auto simp add: nth_bytes_of)
      apply (intro word_eqI)
      by (auto simp add: word_size nth_shiftl test_bit_of_take_bits)
  }
  note 1 = this
  {
    fix x :: "64 word"
    have "rev (\<lbrace>0,0\<rbrace>(\<langle>63,0\<rangle>((\<langle>63,8\<rangle>x << 8 :: 1000 word) OR 1)::64 word)) = [1]"
      apply auto
      apply (intro nth_equalityI)
      apply (auto simp add: nth_bytes_of)
      apply (intro word_eqI)
      by (auto simp add: word_size nth_shiftl test_bit_of_take_bits word_ao_nth)
  }
  note 2 = this
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
      apply (auto simp add:simp_rules Let'_def)
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto simp add: 1)
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto simp add: 1 2)
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto simp add: 1 2)
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
    apply (auto simp add: 1 2)
    apply(auto simp add:semantics_def simp_rules Let'_def)[1]
    apply(auto simp add:semantics_def simp_rules Let'_def)[1]
    apply(auto simp add:semantics_def simp_rules Let'_def)[1]
    apply(auto simp add:semantics_def simp_rules Let'_def)[1]
   apply (intro state_eqI)
  apply (rule ext)
    apply (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl bv_to_bool_def word_lsb_alt)
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps 2)
    done
qed


(*---------------------------------------------------proofs on setne ---------------------------------------*)

lemma is_manual_setne_r8[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_80386 Setne) (Storage (Reg (General Eight r1)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_setne_r8[presimplify]:
  shows "get_semantics assembly semantics (Unary (IS_80386 Setne) (Storage (Reg (General Eight r1)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r1 :: 64 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1 := \<langle>63,0\<rangle>((\<langle>63,8\<rangle>regs \<sigma> r1 << 8 :: 64 word) OR (if flags \<sigma> flag_zf then 0 else 1))) \<rparr>)"
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
   apply (auto simp add:simp_rules )
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto)
   apply (rule word_eqI)
   apply (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
  apply(rewrite_one_let')+
   apply (auto simp add:simp_rules )
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto)
   apply (rule word_eqI)
  apply (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl)
  apply(rewrite_one_let')+
   apply (auto simp add:simp_rules )
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto)
   apply (rule word_eqI)
  by (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl bv_to_bool_def word_lsb_alt)

lemma is_manual_setne_m8[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_80386 Setne) (Storage (Memory Eight Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_setne_m8[presimplify]:
  shows "get_semantics \<alpha> semantics (Unary (IS_80386 Setne) (Storage (Memory Eight Mem))) si =
        (\<lambda> \<sigma> . let a = resolve_address \<alpha> \<sigma> Mem;
                   op1 = (read_mem64 \<alpha> \<sigma> 8 Mem) :: 64 word
            in
             \<sigma>\<lparr>mem := write_blocks [a \<rhd> (if flags \<sigma> flag_zf then [0] else [1])] (mem \<sigma>)\<rparr>)"
proof-
  {
    fix x :: "64 word"
    have "rev (\<lbrace>0,0\<rbrace>(\<langle>63,0\<rangle>(\<langle>63,8\<rangle>x << 8 :: 1000 word) :: 64 word)) = [0]"
      apply auto
      apply (intro nth_equalityI)
      apply (auto simp add: nth_bytes_of)
      apply (intro word_eqI)
      by (auto simp add: word_size nth_shiftl test_bit_of_take_bits)
  }
  note 1 = this
  {
    fix x :: "64 word"
    have "rev (\<lbrace>0,0\<rbrace>(\<langle>63,0\<rangle>((\<langle>63,8\<rangle>x << 8 :: 1000 word) OR 1)::64 word)) = [1]"
      apply auto
      apply (intro nth_equalityI)
      apply (auto simp add: nth_bytes_of)
      apply (intro word_eqI)
      by (auto simp add: word_size nth_shiftl test_bit_of_take_bits word_ao_nth)
  }
  note 2 = this
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
   apply (auto simp add:simp_rules )
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto simp add: 1)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
  apply(rewrite_one_let')+
   apply (auto simp add:simp_rules )
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto simp add: 2)
  apply(rewrite_one_let')+
   apply (auto simp add:simp_rules )
  apply (subst bv_cat'_def)
   apply (auto simp add:  bv_cat.simps)
   apply (intro state_eqI)
  apply (rule ext)
       apply (auto simp add: )
    by (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl bv_to_bool_def word_lsb_alt)
qed

(*---------------------------------------------------proofs on sete ---------------------------------------*)
lemma is_manual_sete_r8[is_manual]:
  shows \<open>is_manual assembly semantics (Unary (IS_80386 Sete) (Storage (Reg (General Eight r)))) = False\<close>
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_sete_r8[presimplify]:
  \<open>get_semantics assembly semantics (Unary (IS_80386 Sete) (Storage (Reg (General Eight r)))) si =
    (\<lambda>\<sigma>. let op1 = regs \<sigma> r in
      \<sigma>\<lparr>regs := (regs \<sigma>)(r := \<langle>63,0\<rangle>((\<langle>63,8\<rangle>regs \<sigma> r << 8::64 word) OR (if flags \<sigma> flag_zf then 1 else 0)))\<rparr>)\<close>
  apply (rule ext)
  apply (subst get_semantics_def)
  apply rewrite_one_let'
   apply rewrite_one_let'
   apply rewrite_one_let'
   apply (rewrite_one_let' add: semantics_def)
   apply rewrite_one_let'+
   apply (auto simp add: simp_rules)
   apply (subst bv_cat'_def)
   apply (auto simp add: bv_cat.simps)
   apply (intro state_eqI)
     apply (rule ext)
     apply auto
   apply (rule word_eqI)
   apply (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl)
  apply rewrite_one_let'
  apply rewrite_one_let'
  apply rewrite_one_let'
  apply (rewrite_one_let' add: semantics_def)
  apply rewrite_one_let'+
  apply (auto simp add: simp_rules)
  apply (subst bv_cat'_def)
  apply (auto simp add: bv_cat.simps)
  apply (intro state_eqI)
    apply (rule ext)
    apply auto
  apply (rule word_eqI)
  by (auto simp add: word_size word_ao_nth test_bit_of_take_bits nth_shiftl)

(*---------------------------------------------------proofs on cmp ---------------------------------------*)
lemma is_manual_cmp_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmp_r32_r32[presimplify]:
  shows "get_semantics assembly semantics (Binary (IS_8088 Cmp) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) si = 
         (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
          (flag_pf := undefined,
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
    apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>regs \<sigma> r32_1 - \<langle>31,0\<rangle>regs \<sigma> r32_2) :: 32 word"]
    by (auto simp add: simp_rules test_bit_of_take_bits )
  done
qed

lemma is_manual_cmp_r32_m32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Reg (General ThirtyTwo r32)) (Storage (Memory ThirtyTwo a))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmp_r32_m32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Cmp) (Reg (General ThirtyTwo r32)) (Storage (Memory ThirtyTwo a))) si = 
             (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word;
                   op2 = \<langle>31,0\<rangle>(read_mem64 \<alpha> \<sigma> 32 a) :: 32 word
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
          (flag_pf := undefined,
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of :=(sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
    apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 a)) :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>regs \<sigma> r32 - \<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 a)) :: 32 word"]
    by (auto simp add: simp_rules test_bit_of_take_bits )
  done
qed


lemma is_manual_cmp_r32_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Reg (General ThirtyTwo r1)) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmp_r32_Imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Cmp) (Reg (General ThirtyTwo r1)) (Immediate SixtyFour (ImmVal ImmValue))) si = 
         (\<lambda> \<sigma> . let op1 = (\<langle>31,0\<rangle>regs \<sigma> r1 :: 32 word);
                   op2 = \<langle>31,0\<rangle>(word_of_int ImmValue :: 64 word)
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
          (flag_pf := undefined,
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r1 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>(word_of_int ImmValue :: 64 word) :: 32 word)"]
    by (auto simp add: simp_rules test_bit_of_take_bits )
  done



lemma is_manual_cmp_m32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Memory ThirtyTwo a) (Storage (Reg (General ThirtyTwo r32)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmp_m32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Cmp) (Memory ThirtyTwo a) (Storage (Reg (General ThirtyTwo r32))))  si = 
             (\<lambda> \<sigma> . let op2 = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word;
                   op1 = \<langle>31,0\<rangle>(read_mem64 \<alpha> \<sigma> 32 a) :: 32 word
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
          (flag_pf := undefined,
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of :=(sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
    apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (subst add.commute[of "ucast (NOT \<langle>31,0\<rangle>regs \<sigma> r32)"])
      by auto
    subgoal for \<sigma>
      apply (subst add.commute[of "ucast (NOT \<langle>31,0\<rangle>regs \<sigma> r32)"])
      apply (subst sign_sub_bit32)
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 a)) :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 a)) - \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word"]
    by (auto simp add: simp_rules test_bit_of_take_bits)
  done
qed


lemma is_manual_cmp_r64_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Reg (General SixtyFour r64_1)) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmp_r64_Imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Cmp) (Reg (General SixtyFour r64_1)) (Immediate SixtyFour (ImmVal ImmValue))) si = 
         (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = (word_of_int ImmValue :: 64 word)
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
          (flag_pf := undefined,
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    apply (subst sextend_useless_64_64)
    unfolding bv_slice.simps
    apply (auto simp add:ucast_bitNOT ucast_id)
    done
  subgoal for \<sigma>
    apply (subst sextend_useless_64_64)
    using overflow_sub_bit64[where ?a="regs \<sigma> r64_1" and ?b="word_of_int ImmValue"]
    apply (auto simp add:simp_rules )
    done
  subgoal for \<sigma>
    apply (subst sextend_useless_64_64)
    using sign_sub_bit64[where ?a="regs \<sigma> r64_1" and ?b="word_of_int ImmValue", simplified]
    apply (auto simp add:simp_rules)
    done
  subgoal for \<sigma>
    apply (subst useless_sextend_hardocded_ucast)
    apply (subst useless_sextend_hardocded_ucast)
    apply (subst sextend_useless_64_64)
    apply(subst test_64b_of_AND1000_word[symmetric, where ?w="regs \<sigma> r64_1"])
    using sign_sub_bit64[where ?a="regs \<sigma> r64_1" and ?b="word_of_int ImmValue", simplified]
    apply (auto simp add:simp_rules)
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="word_of_int ImmValue :: 64 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="regs \<sigma> r64_1 :: 64 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(regs \<sigma> r64_1 - word_of_int ImmValue) :: 64 word"]
    using sub_overflow_flag64_bit[where ?b="word_of_int ImmValue :: 64 word" and ?a="regs \<sigma> r64_1"]
    apply (auto simp add: word_msb_sint msb_nth test_bit_of_take_bits)
    done
  done

lemma is_manual_cmp_m64_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Memory SixtyFour Mem) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmp_m64_Imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Cmp) (Memory SixtyFour Mem) (Immediate SixtyFour (ImmVal ImmValue))) si = 
         (\<lambda> \<sigma> .let  op1 = read_mem64 \<alpha> \<sigma> 64 Mem;
                   op2 = (word_of_int ImmValue :: 64 word)
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
          (flag_pf := undefined,
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    apply (subst sextend_useless_64_64)
    unfolding bv_slice.simps
    apply (auto simp add:ucast_bitNOT ucast_id)
    done
  subgoal for \<sigma>
    apply (subst sextend_useless_64_64)

    using overflow_sub_bit64[where ?a="fst (read_memory \<alpha> \<sigma> 64 Mem)" and ?b="word_of_int ImmValue"]
    apply (auto simp add:simp_rules )
    done
  subgoal for \<sigma>
    apply (subst sextend_useless_64_64)
    using sign_sub_bit64[where ?a="fst (read_memory \<alpha> \<sigma> 64 Mem)" and ?b="word_of_int ImmValue", simplified]
    apply (auto simp add:simp_rules)
    done
  subgoal for \<sigma>
    apply (subst useless_sextend_hardocded_ucast)
    apply (subst useless_sextend_hardocded_ucast)
    apply (subst sextend_useless_64_64)
    apply(subst test_64b_of_AND1000_word[symmetric, where ?w="fst (read_memory \<alpha> \<sigma> 64 Mem)"])
    using sign_sub_bit64[where ?a="fst (read_memory \<alpha> \<sigma> 64 Mem)" and ?b="word_of_int ImmValue", simplified]
    apply (auto simp add:simp_rules)
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="word_of_int ImmValue :: 64 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="fst (read_memory \<alpha> \<sigma> 64 Mem) :: 64 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(fst (read_memory \<alpha> \<sigma> 64 Mem) - word_of_int ImmValue) :: 64 word"]
    using sub_overflow_flag64_bit[where ?b="word_of_int ImmValue :: 64 word" and ?a="fst (read_memory \<alpha> \<sigma> 64 Mem)"]
    apply (auto simp add: word_msb_sint msb_nth test_bit_of_take_bits)
    done
  done

lemma is_manual_cmp_m8_Imm8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Memory Eight Mem) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma take_bits_remove_NOT:
  fixes a :: "64 word"
  shows "\<langle>7,0\<rangle>(NOT (\<langle>7,0\<rangle>a :: 1000 word)) = ((NOT \<langle>7,0\<rangle>a) :: 8 word)"
  apply (intro word_eqI)
  by (auto simp add:simp_rules test_bit_of_take_bits word_size bitNOT_nth)

lemma take_bits_lt_bit8[get_semantics_rewriting]:
  fixes a b :: "'b::len0 word"
  assumes "8 \<le> LENGTH('a)"
      and "8 \<le> LENGTH('b)"
  shows "(((\<langle>7,0\<rangle>a)::'a::len0 word) < ((\<langle>7,0\<rangle>b)::'a::len0 word)) = (((\<langle>7,0\<rangle>a)::8 word) < ((\<langle>7,0\<rangle>b)::8 word))"
proof-
  have 1: "\<forall>i\<ge>8. i < length (rev (to_bl ((\<langle>7,0\<rangle>a)::'a::len0 word))) \<longrightarrow> \<not>rev (to_bl ((\<langle>7,0\<rangle>a)::'a::len0 word)) ! i"
    using assms
    by (auto simp add: rev_nth test_bit_of_take_bits to_bl_nth word_size)
  have 2: "\<forall>i\<ge>8. i < length (rev (to_bl ((\<langle>7,0\<rangle>b)::'a::len0 word))) \<longrightarrow> \<not>rev (to_bl ((\<langle>7,0\<rangle>b)::'a::len0 word)) ! i"
    using assms
    by (auto simp add: rev_nth test_bit_of_take_bits to_bl_nth word_size)
  have 3: "\<And> a ::'b::len0 word . take 8 (rev (to_bl ((\<langle>7,0\<rangle>a)::'a::len0 word))) = rev (to_bl ((\<langle>7,0\<rangle>a)::8 word))"
  proof-
    fix a :: "'b::len0 word"
    {
      fix i :: nat
      assume "i < 8"
      hence "take 8 (rev (to_bl ((\<langle>7,0\<rangle>a)::'a::len0 word))) ! i = rev (to_bl ((\<langle>7,0\<rangle>a)::8 word)) ! i"
        using assms
        by (auto simp add: rev_nth to_bl_nth word_size test_bit_of_take_bits)
    }
    thus "?thesis a"
      using assms
      apply (intro nth_equalityI)
      by (auto)
  qed

  show ?thesis
    apply (auto simp add: word_less_rbl)
    apply (subst (asm) rev_bl_order_take[of 8])
    using 1 2 3
    apply auto
    apply (subst rev_bl_order_take[of 8])
    using 1 2 3
    by auto
qed

lemma take_bits_le_bit8[get_semantics_rewriting]:
  fixes a b :: "'b::len0 word"
  assumes "8 \<le> LENGTH('a)"
      and "8 \<le> LENGTH('b)"
  shows "(((\<langle>7,0\<rangle>a)::'a::len0 word) \<le> ((\<langle>7,0\<rangle>b)::'a::len0 word)) = (((\<langle>7,0\<rangle>a)::8 word) \<le> ((\<langle>7,0\<rangle>b)::8 word))"
proof-
  have "(((\<langle>7,0\<rangle>a)::'a::len0 word) = ((\<langle>7,0\<rangle>b)::'a::len0 word)) = (((\<langle>7,0\<rangle>a)::8 word) = ((\<langle>7,0\<rangle>b)::8 word))"
  proof-
    { fix i :: nat
      assume "(((\<langle>7,0\<rangle>a)::'a::len0 word) = ((\<langle>7,0\<rangle>b)::'a::len0 word))"
      hence "\<forall> i <8 . (((\<langle>7,0\<rangle>a)::'a::len0 word) !! i = (((\<langle>7,0\<rangle>b)::'a::len0 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
   
      hence "\<forall> i < 8 . (((\<langle>7,0\<rangle>a)::8 word) !! i = (((\<langle>7,0\<rangle>b):: 8 word)) !! i)"
        using assms
        by (simp add: simp_rules test_bit_of_take_bits)
      hence "(((\<langle>7,0\<rangle>a)::8 word) = ((\<langle>7,0\<rangle>b)::8 word))"
        apply (intro word_eqI)
        by (auto simp add: word_size)
    }
    moreover
    {
      assume "(((\<langle>7,0\<rangle>a)::8 word) = ((\<langle>7,0\<rangle>b)::8 word))"
      hence "\<forall> i < 8 . (((\<langle>7,0\<rangle>a)::8 word) !! i = (((\<langle>7,0\<rangle>b)::8 word)) !! i)"
        using assms
        by (auto simp add: test_bit_of_take_bits)
      hence "\<forall> i < LENGTH('a) . (((\<langle>7,0\<rangle>a)::'a::len0 word) !! i = (((\<langle>7,0\<rangle>b)::'a::len0 word)) !! i)"
        using assms
        by (auto simp add: simp_rules test_bit_of_take_bits)
      hence "(((\<langle>7,0\<rangle>a)::'a::len0 word) = ((\<langle>7,0\<rangle>b)::'a::len0 word))"
        using assms
        apply (intro word_eqI)
        by (auto simp add: word_size)
    }
    ultimately
    show ?thesis
      by auto
  qed
  thus ?thesis
    using assms
    apply (cases "(((\<langle>7,0\<rangle>a)::'a::len0 word) = ((\<langle>7,0\<rangle>b)::'a::len0 word))"; cases "(((\<langle>7,0\<rangle>a)::8 word) = ((\<langle>7,0\<rangle>b)::8 word))";auto)
    by (meson less_imp_le_nat linorder_not_le take_bits_lt_bit8)+
qed

value "2 ^ 8 :: 65 word"


lemma overflow_sub_bit8[get_semantics_rewriting]:
  fixes a b:: "'a :: len0 word"
  assumes "64\<le> LENGTH('a)"
  shows "((1::9 word) + (((\<langle>7,0\<rangle>a)::9 word) + ucast (NOT ((\<langle>7,0\<rangle>b):: 8 word)))) !! 8 = (((\<langle>7,0\<rangle>a)::8 word) \<ge> \<langle>7,0\<rangle>b)"
proof-
  have 3: "(((\<langle>7,0\<rangle>a)::9 word) \<ge> \<langle>7,0\<rangle>b) = (((\<langle>7,0\<rangle>a)::8 word) \<ge> \<langle>7,0\<rangle>b)"
    using assms
    by (subst take_bits_le_bit8,simp,simp,simp)
  have 1: "\<not> ((\<langle>7,0\<rangle>a)::9 word) !! 8"
   and 2: "\<not> ((\<langle>7,0\<rangle>b)::9 word) !! 8"
    using assms
    by (auto simp add: test_bit_of_take_bits)
  have "uint ((\<langle>7,0\<rangle>a)::9 word) < 256"
   and "uint ((\<langle>7,0\<rangle>b)::9 word) < 256"
    using msb_is_gt_2p[unfolded msb_nth,where 'a=9,simplified] 1
    apply (uint_arith)
    using msb_is_gt_2p[unfolded msb_nth,where 'a=9,simplified] 2
    by (uint_arith)
  hence "((1::9 word) + (((\<langle>7,0\<rangle>a)::9 word) + ucast (NOT ((\<langle>7,0\<rangle>b):: 8 word)))) !! 8 = (((\<langle>7,0\<rangle>a)::9 word) \<ge> \<langle>7,0\<rangle>b)"
    apply (subst ucast_bitNOT)
    apply simp
    apply (subst twos_complement_subtraction)
    apply simp
    apply (subst msb_is_gt_2p[unfolded msb_nth,where 'a=9,simplified])
    apply auto
    apply uint_arith
    using assms
    apply (auto simp add: is_up)
    apply uint_arith
    using assms
    by (auto simp add: is_up)
  thus ?thesis
    using 3
    by auto
qed


lemma sign_sub_bit8[get_semantics_rewriting]:
  fixes a b:: "'a :: len0 word"
  assumes "63 < LENGTH('a)"
  shows "((1::9 word) + (((\<langle>7,0\<rangle>a)::9 word) + ucast (NOT ((\<langle>7,0\<rangle>b):: 8 word)))) !! 7 \<longleftrightarrow> sint (((\<langle>7,0\<rangle>a):: 8 word) - \<langle>7,0\<rangle>b) < 0"
proof-
  have 1: "\<And> a :: 9 word . a !! 7 = ((\<langle>7,0\<rangle>a):: 8 word) !! 7"
    using assms
    by (auto simp add: test_bit_of_take_bits nth_ucast)
  have 2: "\<langle>7,0\<rangle>((1::9 word) + (((\<langle>7,0\<rangle>a)::9 word) + ucast (NOT ((\<langle>7,0\<rangle>b):: 8 word)))) = (((\<langle>7,0\<rangle>a)::8 word) - \<langle>7,0\<rangle>b)"
    using assms
    apply (subst ucast_bitNOT)
    apply simp
    apply (subst twos_complement_subtraction)
    apply (subst take_bits_minus)
    apply (simp)
    apply (simp)
    by (simp)
  have 3: "... !! 7 \<longleftrightarrow> sint (((\<langle>7,0\<rangle>a):: 8 word) - \<langle>7,0\<rangle>b) < 0"
    using msb_nth[symmetric, where 'a=8]
    by (simp add: word_msb_sint)
  show ?thesis
    apply (subst 1)
    apply (subst 2)
    apply (subst 3)
    by simp
qed


lemma test_8b_of_8AND1000_word[get_semantics_rewriting]:
  fixes a :: "1000 word"
  shows "a !! 8 = (\<langle>8,0\<rangle>a :: 9 word) !! 8"
  by (auto simp add:simp_rules test_bit_of_take_bits)

lemma take_bits_remove_NOT_1000word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "\<langle>7,0\<rangle>(NOT (\<langle>7,0\<rangle>a :: 1000 word)) = (\<langle>7,0\<rangle>(NOT a) :: 1000 word)"
  apply (intro word_eqI)
  by (auto simp add:simp_rules test_bit_of_take_bits word_size bitNOT_nth)

lemma take_bits_remove_NOT_9word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "\<langle>7,0\<rangle>(NOT (\<langle>7,0\<rangle>a :: 9 word)) = (\<langle>7,0\<rangle>(NOT a) :: 9 word)"
  apply (intro word_eqI)
  by (auto simp add:simp_rules test_bit_of_take_bits word_size bitNOT_nth)


lemma take_bits_remove_UCAST_NOT_9word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "(\<langle>7,0\<rangle>(NOT a) :: 9 word) = (ucast (NOT (\<langle>7,0\<rangle>a :: 8 word)) :: 9 word)"
  apply (intro word_eqI)
  by (auto simp add:simp_rules test_bit_of_take_bits word_size bitNOT_nth)

lemma take_bits_remove_UCAST_NOT_1000word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "\<langle>7,0\<rangle>(NOT (\<langle>7,0\<rangle>a :: 1000 word)) = (ucast (NOT (\<langle>7,0\<rangle>a :: 8 word)) :: 9 word)"
  apply (intro word_eqI)
  by (auto simp add:simp_rules test_bit_of_take_bits word_size bitNOT_nth)

lemma take_bits_remove_UCAST_NOT_9word_2[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "\<langle>7,0\<rangle>(NOT (\<langle>7,0\<rangle>a :: 9 word)) = (ucast (NOT (\<langle>7,0\<rangle>a :: 8 word)) :: 9 word)"
  apply (intro word_eqI)
  by (auto simp add:simp_rules test_bit_of_take_bits word_size bitNOT_nth)

lemma test_bit7_of_64_and_1000word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "(\<langle>63,0\<rangle>a :: 1000 word) !! 7 = (\<langle>7,0\<rangle>a :: 8 word) !! 7"
  by (auto simp add:test_bit_of_take_bits)


lemma sub_overflow_flag8_bit[get_semantics_rewriting]:
  fixes a b :: "'a::len0 word"
  assumes "LENGTH('a) \<ge> 64"
  shows "((\<not> b !! 7) = a !! 7 \<and> b !! 7 = (sint (\<langle>7,0\<rangle>a - \<langle>7,0\<rangle>b::8 word) < 0)) \<longleftrightarrow>
            ((128::8 word) > \<langle>7,0\<rangle>b \<and> sint (\<langle>7,0\<rangle>a - \<langle>7,0\<rangle>b::8 word) \<ge> 0 \<and> (128::8 word) \<le> \<langle>7,0\<rangle>a)
             \<or>
             ((128::8 word) \<le> \<langle>7,0\<rangle>b \<and> sint (\<langle>7,0\<rangle>a - \<langle>7,0\<rangle>b::8 word) < 0 \<and> (128::8 word) > \<langle>7,0\<rangle>a)"
proof-
  have 1: "a !! 7 = msb (\<langle>7,0\<rangle> a :: 8 word)"
   and 2: "b !! 7 = msb (\<langle>7,0\<rangle> b :: 8 word)"
    using assms
    by (auto simp add: msb_nth test_bit_of_take_bits)
  show ?thesis
    using assms
    apply (subst 1)
    apply (subst 2)+
    apply (subst msb_is_gt_2p)+
    apply simp
    by (auto)
qed



lemma BV_Add_bit9:
 fixes a b :: longword
   shows "(a,9) +\<^sup>b\<^sup>v (b,9) = (ucast (((\<langle>8,0\<rangle>a)::9 word) + \<langle>8,0\<rangle>b), 9)"
proof-
 have "(a,9) +\<^sup>b\<^sup>v (b,9) = (\<langle>8,0\<rangle>(a + b), 9)"
   by (cases a;cases b;auto simp add: exec_BV_Plus_def case_prod_unfold)
 also have "... = (ucast ((\<langle>8,0\<rangle>(a + b))::9 word), 9)"
   by (subst ucast_take_bits,simp,simp,simp)
 also have "... = (ucast (((\<langle>8,0\<rangle>a)::9 word) + \<langle>8,0\<rangle>b), 9)"
   by (subst take_bits_plus,simp,simp,simp)
 finally
 show ?thesis
   by auto
qed


lemma get_semantics_cmp_m8_Imm8[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Cmp) (Memory Eight Mem) (Immediate SixtyFour (ImmVal ImmValue))) si = 
         (\<lambda> \<sigma> .let  op1 = \<langle>7,0\<rangle>read_mem64 \<alpha> \<sigma> 8 Mem :: 8 word;
                   op2 = \<langle>7,0\<rangle>(word_of_int ImmValue :: 64 word) :: 8 word
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
          (flag_pf := undefined,
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of :=  (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add:BV_Add_bit9)+
  apply (intro state_eqI,simp_all)
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    unfolding bv_slice.simps
    apply (auto simp add:simp_rules exec_BV_Plus_def take_bits_remove_NOT)
    done
  subgoal for \<sigma>
    apply (subst take_bits_remove_UCAST_NOT_1000word)
    using overflow_sub_bit8[where ?a="fst (read_memory \<alpha> \<sigma> 8 Mem)" and ?b="word_of_int ImmValue", simplified]
    apply (auto simp add:simp_rules take_bits_remove_UCAST_NOT_9word)
    done
  subgoal for \<sigma>
    apply (subst take_bits_remove_UCAST_NOT_1000word)
    using sign_sub_bit8[where ?a="fst (read_memory \<alpha> \<sigma> 8 Mem)" and ?b="word_of_int ImmValue"]
    apply (auto simp add:simp_rules )
    done
  subgoal for \<sigma>
    apply(subst test_bit7_of_64_and_1000word[where ?a="fst (read_memory \<alpha> \<sigma> 8 Mem)"])
    apply(subst test_bit7_of_64_and_1000word[where ?a="word_of_int ImmValue"])
    apply(subst test_bit7_of_64_and_1000word[where ?a="word_of_int ImmValue"])
    apply (subst take_bits_remove_UCAST_NOT_1000word)
    using sign_sub_bit8[where ?a="fst (read_memory \<alpha> \<sigma> 8 Mem)" and ?b="word_of_int ImmValue", simplified]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>7,0\<rangle>word_of_int ImmValue :: 8 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>7,0\<rangle>fst (read_memory \<alpha> \<sigma> 8 Mem) :: 8 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>7,0\<rangle>fst (read_memory \<alpha> \<sigma> 8 Mem) - \<langle>7,0\<rangle>word_of_int ImmValue) :: 8 word"]
    apply (auto simp add:simp_rules test_bit_of_take_bits)
    done
  done


lemma is_manual_cmp_r8_m8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Reg (General Eight r1)) (Storage (Memory Eight a))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmp_r8_m8[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Cmp) (Reg (General Eight r1)) (Storage (Memory Eight a))) si = 
             (\<lambda> \<sigma> . let op1 = \<langle>7,0\<rangle>regs \<sigma> r1 :: 8 word;
                   op2 = \<langle>7,0\<rangle>(read_mem64 \<alpha> \<sigma> 8 a) :: 8 word
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
          (flag_pf := undefined,
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add:BV_Add_bit9)+
  apply (intro state_eqI,simp_all)
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    unfolding bv_slice.simps
    apply (auto simp add:simp_rules exec_BV_Plus_def take_bits_remove_NOT)
    done
  subgoal for \<sigma>
    apply (subst take_bits_remove_UCAST_NOT_1000word)
    using overflow_sub_bit8[where ?a="regs \<sigma> r1" and ?b="fst (read_memory \<alpha> \<sigma> 8 a)", simplified]
    apply (auto simp add:simp_rules take_bits_remove_UCAST_NOT_9word)
    done
  subgoal for \<sigma>
    apply (subst take_bits_remove_UCAST_NOT_1000word)
    using sign_sub_bit8[where ?a="regs \<sigma> r1" and ?b="fst (read_memory \<alpha> \<sigma> 8 a)"]
    apply (auto simp add:simp_rules )
    done
  subgoal for \<sigma>
    apply(subst test_bit7_of_64_and_1000word[where ?a="regs \<sigma> r1"])
    apply(subst test_bit7_of_64_and_1000word[where ?a="fst (read_memory \<alpha> \<sigma> 8 a)"])
    apply(subst test_bit7_of_64_and_1000word[where ?a="fst (read_memory \<alpha> \<sigma> 8 a)"])
    apply (subst take_bits_remove_UCAST_NOT_1000word)
    using sign_sub_bit8[where ?a="regs \<sigma> r1" and ?b="fst (read_memory \<alpha> \<sigma> 8 a)", simplified]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>7,0\<rangle>regs \<sigma> r1 :: 8 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>7,0\<rangle>fst (read_memory \<alpha> \<sigma> 8 a) :: 8 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>7,0\<rangle>regs \<sigma> r1 - \<langle>7,0\<rangle>fst (read_memory \<alpha> \<sigma> 8 a)) :: 8 word"]
    apply (auto simp add:simp_rules)
    done
  done



lemma is_manual_cmp_m32_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Cmp) (Memory ThirtyTwo Mem) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmp_m32_Imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Cmp) (Memory ThirtyTwo Mem) (Immediate SixtyFour (ImmVal ImmValue))) si = 
         (\<lambda> \<sigma> . let a = resolve_address \<alpha> \<sigma> Mem;
                  op1 = \<langle>31,0\<rangle>(read_mem64 \<alpha> \<sigma> 32 Mem :: 64 word) :: 32 word;
                   op2 = \<langle>31,0\<rangle>(word_of_int ImmValue :: 64 word) :: 32 word
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
          (flag_pf := undefined,
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    using sign_sub_bit32[where ?a="fst (read_memory \<alpha> \<sigma> 32 Mem)" and ?b="word_of_int ImmValue"]
    apply (auto simp add: simp_rules)
    done
  subgoal for \<sigma>
    apply (subst test_32b_of_32AND64_word[where ?a="fst (read_memory \<alpha> \<sigma> 32 Mem)"])
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>word_of_int ImmValue :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 Mem) :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 Mem) - \<langle>31,0\<rangle>word_of_int ImmValue) :: 32 word"]
 
    using sign_sub_bit32[where ?a="fst (read_memory \<alpha> \<sigma> 32 Mem)" and ?b="word_of_int ImmValue"]
    apply (auto simp add: simp_rules test_bit_of_take_bits)
    done
  done


(*---------------------------------------------------proofs on test ---------------------------------------*)

lemma take_bits_AND_zero_64_word[get_semantics_rewriting]:
  fixes a b :: "64 word"
  shows "(\<langle>63,0\<rangle>a AND \<langle>63,0\<rangle>b = (0::1000 word)) \<longleftrightarrow> (a AND b = (0 :: 64 word))"
proof-
  {
    assume 1: "(\<langle>63,0\<rangle>a AND \<langle>63,0\<rangle>b = (0::1000 word))"
    hence 2: "\<forall> i < 1000 . (\<langle>63,0\<rangle>a AND \<langle>63,0\<rangle>b :: 1000 word) !! i = False"
      apply (subst 1)
      by auto
    have "(a AND b = (0 :: 64 word))"
    proof-
      {
        fix i :: nat
        assume "i < 64"
        hence "(a AND b :: 64 word) !! i = (0 :: 64 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  moreover
  {
    assume 1: "(a AND b = (0::64 word))"
    hence 2: "\<forall> i < 64 . (a AND b :: 64 word) !! i = False"
      apply (subst 1)
      by auto
    have "(\<langle>63,0\<rangle>a AND \<langle>63,0\<rangle>b = (0 :: 1000 word))"
    proof-
      {
        fix i :: nat
        assume "i < 1000"
        hence "(\<langle>63,0\<rangle>a AND \<langle>63,0\<rangle>b :: 1000 word) !! i = (0 :: 1000 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  ultimately
  show ?thesis
    by auto
qed



lemma take_bits_AND_zero_32_word[get_semantics_rewriting]:
  fixes a b :: "64 word"
  shows "(\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b = (0::1000 word)) \<longleftrightarrow> (\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b = (0 :: 32 word))"
proof-
  {
    assume 1: "(\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b = (0::1000 word))"
    hence 2: "\<forall> i < 1000 . (\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b :: 1000 word) !! i = False"
      apply (subst 1)
      by auto
    have "(\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b = (0 :: 32 word))"
    proof-
      {
        fix i :: nat
        assume "i < 32"
        hence "(\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b :: 32 word) !! i = (0 :: 32 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  moreover
  {
    assume 1: "(\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b = (0::32 word))"
    hence 2: "\<forall> i < 32 . (\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b :: 32 word) !! i = False"
      apply (subst 1)
      by auto
    have "(\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b = (0 :: 1000 word))"
    proof-
      {
        fix i :: nat
        assume "i < 1000"
        hence "(\<langle>31,0\<rangle>a AND \<langle>31,0\<rangle>b :: 1000 word) !! i = (0 :: 1000 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  ultimately
  show ?thesis
    by auto
qed


lemma take_bits_AND_zero_16_word[get_semantics_rewriting]:
  fixes a b :: "64 word"
  shows "(\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b = (0::1000 word)) \<longleftrightarrow> (\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b = (0 :: 16 word))"
proof-
  {
    assume 1: "(\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b = (0::1000 word))"
    hence 2: "\<forall> i < 1000 . (\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b :: 1000 word) !! i = False"
      apply (subst 1)
      by auto
    have "(\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b = (0 :: 16 word))"
    proof-
      {
        fix i :: nat
        assume "i < 16"
        hence "(\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b :: 16 word) !! i = (0 :: 16 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  moreover
  {
    assume 1: "(\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b = (0::16 word))"
    hence 2: "\<forall> i < 16 . (\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b :: 16 word) !! i = False"
      apply (subst 1)
      by auto
    have "(\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b = (0 :: 1000 word))"
    proof-
      {
        fix i :: nat
        assume "i < 1000"
        hence "(\<langle>15,0\<rangle>a AND \<langle>15,0\<rangle>b :: 1000 word) !! i = (0 :: 1000 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        apply (intro word_eqI)
        by (auto simp add: word_size)
    qed
  }
  ultimately
  show ?thesis
    by auto
qed



lemma bool_to_bv_eq_fst[get_semantics_rewriting]:
 shows "fst (bool_to_bv b) = x \<longleftrightarrow> (x \<in> {0,1} \<and> ((x = 1) \<longleftrightarrow> b))"
  by (cases b,auto)

lemma fst_bool_to_bv_AND_def[get_semantics_rewriting]:
 shows "(fst (bool_to_bv a) AND fst (bool_to_bv b)) = (if a \<and> b then 1 else 0)"
 by (auto simp add:bool_to_bv_eq_fst )

lemma is_manual_test_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Test) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_test_r32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Test) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
        (flag_zf := (op1 AND op2) = (0 :: 32 word),
         flag_cf := False,
         flag_of := False,
         flag_sf := (sint op1 < 0) \<and> (sint op2 < 0),
         flag_pf := undefined)  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
    apply (rewrite_one_let')+
    subgoal for \<sigma> 
      apply(subst word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word", symmetric, unfolded msb_nth])
      apply(subst word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word", symmetric, unfolded msb_nth])
      by (auto simp add:simp_rules take_bits_AND_zero_32_word msb_nth flags_eqI test_bit_of_take_bits fst_bool_to_bv_AND_def)
    done
  qed


lemma is_manual_test_r64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Test) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_test_r64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Test) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = regs \<sigma> r64_2 :: 64 word
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
        (flag_zf := (op1 AND op2) = (0 :: 64 word),
         flag_cf := False,
         flag_of := False,
         flag_sf := (sint op1 < 0) \<and> (sint op2 < 0),
         flag_pf := undefined)  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
    apply (rewrite_one_let')+
    subgoal for \<sigma> 
      apply(subst word_msb_sint[where ?w="regs \<sigma> r64_1", symmetric, unfolded msb_nth])
      apply(subst word_msb_sint[where ?w="regs \<sigma> r64_2", symmetric, unfolded msb_nth])
      find_theorems "\<langle>?h,?l\<rangle>?a AND \<langle>?h,?l\<rangle>?b = 0"
      by (auto simp add:simp_rules take_bits_AND_zero_64_word msb_nth flags_eqI test_bit_of_take_bits fst_bool_to_bv_AND_def)
    done
  qed


lemma is_manual_test_r16_r16[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Test) (Reg (General Sixteen r16_1)) (Storage (Reg (General Sixteen r16_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_test_r16_r16[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Test) (Reg (General Sixteen r16_1)) (Storage (Reg (General Sixteen r16_2)))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>15,0\<rangle>regs \<sigma> r16_1 :: 16 word;
                   op2 = \<langle>15,0\<rangle>regs \<sigma> r16_2 :: 16 word
               in
        \<sigma>\<lparr>flags := (flags \<sigma>)
        (flag_zf := (op1 AND op2) = (0 :: 16 word),
         flag_cf := False,
         flag_of := False,
         flag_sf := (sint op1 < 0) \<and> (sint op2 < 0),
         flag_pf := undefined)  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
  subgoal for \<sigma> 
    apply(subst word_msb_sint[where ?w="\<langle>15,0\<rangle>regs \<sigma> r16_1 :: 16 word", symmetric, unfolded msb_nth])
    apply(subst word_msb_sint[where ?w="\<langle>15,0\<rangle>regs \<sigma> r16_2 :: 16 word", symmetric, unfolded msb_nth])
    by (auto simp add:simp_rules take_bits_AND_zero_16_word msb_nth flags_eqI test_bit_of_take_bits fst_bool_to_bv_AND_def)
    done
qed 


(*---------------------------------------------------proofs on xor ---------------------------------------*)

lemma take_bits_bitXOR[get_semantics_rewriting]:
  fixes a b :: "64 word"
  shows "((\<langle>63,0\<rangle>(a XOR b)) :: 1000 word) = ((\<langle>63,0\<rangle>a) :: 1000 word) XOR ((\<langle>63,0\<rangle>b))"
proof-
  {
fix n :: nat
    assume 1: "n < 64"
    hence "((\<langle>63,0\<rangle>(a XOR b)) :: 1000 word) !! n = (((\<langle>63,0\<rangle>a) :: 1000 word) XOR \<langle>63,0\<rangle>b) !! n  "
      using 1
        apply (subst test_bit_of_take_bits)
      by (auto simp add: simp_rules test_bit_of_take_bits word_ao_nth bitXOR_nth)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add:simp_rules test_bit_of_take_bits word_size word_ao_nth bitXOR_nth)
qed

lemma take_bits_bitXOR2:
  fixes a b :: "64 word"
    shows " ((\<langle>63,0\<rangle>a) :: 1000 word) XOR ((\<langle>63,0\<rangle>b)) = ((\<langle>63,0\<rangle>(a XOR b)) :: 1000 word)"
proof-
  {
fix n :: nat
    assume 1: "n < 64"
    hence "(((\<langle>63,0\<rangle>a) :: 1000 word) XOR \<langle>63,0\<rangle>b) !! n = ((\<langle>63,0\<rangle>(a XOR b)) :: 1000 word) !! n "
      using 1
        apply (subst test_bit_of_take_bits)
      by (auto simp add: simp_rules test_bit_of_take_bits word_ao_nth bitXOR_nth)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add:simp_rules test_bit_of_take_bits word_size word_ao_nth bitXOR_nth)
qed



lemma take_bits_XOR_eq_zero_64word[get_semantics_rewriting]:
  fixes a b :: "64 word"
  shows "((\<langle>63,0\<rangle>a XOR \<langle>63,0\<rangle>b) = (0::1000 word)) \<longleftrightarrow>  ((a XOR  b) = (0::64 word))"
proof-
  {
    assume 1: "((\<langle>63,0\<rangle>a XOR \<langle>63,0\<rangle>b) = (0::1000 word))"
    hence 2: "\<forall> i<1000. (((\<langle>63,0\<rangle>a XOR \<langle>63,0\<rangle>b) :: 1000 word) !! i = False)"
      apply (subst 1)+
      by auto
    have "((a XOR b) = (0::64 word))"
    proof-
      {
        fix i :: nat
        assume "i < 64"
        hence "((a XOR b) !! i = (0 :: 64 word) !! i)"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits bitXOR_nth)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI )
    qed
  }
 moreover
  {
    assume 1: "((a XOR b) = (0::64 word))"
    hence 2: "\<forall> i < 64 . ((a XOR b) !! i = False)"
      apply (subst 1)
      by auto
    have "((\<langle>63,0\<rangle>a XOR \<langle>63,0\<rangle>b) = (0::1000 word))"
    proof-
      {
        fix i :: nat
        assume "i < 1000"
        hence " (((\<langle>63,0\<rangle>a XOR \<langle>63,0\<rangle>b):: 1000 word) !! i = (0 :: 1000 word) !! i)"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits bitXOR_nth)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI)
    qed
  }
  ultimately
  show ?thesis
    by auto
qed

lemma take_bits_XOR_eq_zero_32word[get_semantics_rewriting]:
  fixes a b :: "64 word"
  shows "((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b) = (0::1000 word)) \<longleftrightarrow>  ((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b) = (0::32 word))"
proof-
  {
    assume 1: "((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b) = (0::1000 word))"
    hence 2: "\<forall> i<1000. (((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b) :: 1000 word) !! i = False)"
      apply (subst 1)+
      by auto
    have "(((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b) :: 32 word) = (0::32 word))"
    proof-
      {
        fix i :: nat
        assume "i < 32"
        hence "(((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b) :: 32 word) !! i = (0 :: 32 word) !! i)"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits bitXOR_nth)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI )
    qed
  }
 moreover
  {
    assume 1: "(((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b) :: 32 word) = (0::32 word))"
    hence 2: "\<forall> i < 32 . (((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b) :: 32 word) !! i = False)"
      apply (subst 1)
      by auto
    have "(((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b) :: 1000 word) = (0::1000 word))"
    proof-
      {
        fix i :: nat
        assume "i < 1000"
        hence " (((\<langle>31,0\<rangle>a XOR \<langle>31,0\<rangle>b):: 1000 word) !! i = (0 :: 1000 word) !! i)"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits bitXOR_nth)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI)
    qed
  }
  ultimately
  show ?thesis
    by auto
qed

lemma parity_bit64[simp]:
 fixes a :: "'b::len0 word"
 assumes "LENGTH('a) > 64"
     and "LENGTH('b) \<ge> 64"
 shows "parity (\<langle>63,0\<rangle> a :: 'a::len0 word) = parity (\<langle>63,0\<rangle> a :: 64 word)"
proof-
 {
   fix i
   assume "i < LENGTH('a)"
   hence "(\<langle>63,0\<rangle> a :: 'a::len0 word) !! i = (ucast (\<langle>63,0\<rangle> a :: 64 word) :: 'a::len0 word) !! i"
     using assms
     by (auto simp add: test_bit_of_take_bits nth_ucast)
 }
 hence 1: "(\<langle>63,0\<rangle> a :: 'a::len0 word) = (ucast (\<langle>63,0\<rangle> a :: 64 word) :: 'a::len0 word)"
   apply (intro word_eqI)
   by (auto simp add: word_size)
 show ?thesis
   apply (subst 1)
   apply (subst parity_ucast)
   using assms 1
   by auto
qed


lemma fst_bool_to_bv_XOR_def[get_semantics_rewriting]:
 shows "(fst (bool_to_bv a) XOR fst (bool_to_bv b)) = (if (a\<noteq>b) then 1 else 0)"
  by (auto simp add:bool_to_bv_eq_fst )

(* Proofs on Xor  *)
lemma is_manual_test_xor_r64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Xor) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_xor_r64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Xor) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = regs \<sigma> r64_2 :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 := op1 XOR op2),
               flags := (flags \<sigma>)
        (flag_zf := (op1 XOR op2) = (0 :: 64 word),
         flag_cf := False,
         flag_of := False,

         flag_sf := (sint(op1 XOR op2) < 0 ),
         flag_pf := parity(op1 XOR op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_bitXOR2)
      done
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_XOR_eq_zero_64word)
      done
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_bitXOR2 )
      done
    subgoal for \<sigma>
      using word_msb_sint[where ?w="regs \<sigma> r64_1 XOR regs \<sigma> r64_2"]
      by (auto simp add:msb_nth fst_bool_to_bv_XOR_def bitXOR_nth test_bit_of_take_bits)
      done
qed

lemma is_manual_test_xor_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Xor) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_xor_r32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Xor) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32_1 := ucast(op1 XOR op2)),
               flags := (flags \<sigma>)
        (flag_zf := (op1 XOR op2) = (0 :: 32 word),
         flag_cf := False,
         flag_of := False,
         flag_sf := (sint (op1 XOR op2) < 0),
         flag_pf := parity(op1 XOR op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
    apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_bitXOR2)
      done
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_XOR_eq_zero_32word)
      done
    subgoal for \<sigma>
      apply (auto simp add:simp_rules parity_ucast)
      done
    subgoal for \<sigma>
      using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1 XOR \<langle>31,0\<rangle>regs \<sigma> r32_2"]
      by (auto simp add:msb_nth fst_bool_to_bv_XOR_def bitXOR_nth test_bit_of_take_bits)
      done
qed

lemma is_manual_test_xor_r64_m64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Xor) (Reg (General SixtyFour r64_1)) (Storage (Memory SixtyFour Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)



lemma get_semantics_xor_r64_m64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Xor) (Reg (General SixtyFour r64_1)) (Storage (Memory SixtyFour Mem))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 := op1 XOR op2),
               flags := (flags \<sigma>)
        (flag_zf := (op1 XOR op2) = (0 :: 64 word),
         flag_cf := False,
         flag_of := False,

         flag_sf := (sint(op1 XOR op2) < 0 ),
         flag_pf := parity(op1 XOR op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_bitXOR2)
      done
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_XOR_eq_zero_64word)
      done
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_bitXOR2 )
      done
    subgoal for \<sigma>
      using word_msb_sint[where ?w="regs \<sigma> r64_1 XOR read_mem64 \<alpha> \<sigma> 64 Mem"]
      by (auto simp add:msb_nth fst_bool_to_bv_XOR_def bitXOR_nth test_bit_of_take_bits)
      done
qed

lemma is_manual_test_xor_m32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Xor) (Memory ThirtyTwo Mem) (Storage (Reg (General ThirtyTwo r32_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_xor_m32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Xor) (Memory ThirtyTwo Mem) (Storage (Reg (General ThirtyTwo r32_2)))) si =
        (\<lambda> \<sigma> . let a = resolve_address \<alpha> \<sigma> Mem;
                   op1 = \<langle>31,0\<rangle>read_mem64 \<alpha> \<sigma> 32 Mem;

                   op2 = \<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word
               in
       \<sigma>\<lparr>mem := write_blocks [a \<rhd> rev (\<lbrace>3,0\<rbrace> (op1 XOR op2))] (mem \<sigma>),
               flags := (flags \<sigma>)
        (flag_zf := (op1 XOR op2) = (0 :: 32 word),
         flag_cf := False,
         flag_of := False,
         flag_sf := (sint (op1 XOR op2) < 0),
         flag_pf := parity(op1 XOR op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
    apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_bitXOR2 resolve_address_after_update_flag)
      done
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules take_bits_XOR_eq_zero_32word)
      done
    subgoal for \<sigma>
      apply (auto simp add:simp_rules parity_ucast)
      done
    subgoal for \<sigma>
      using word_msb_sint[where ?w="\<langle>31,0\<rangle>read_mem64 \<alpha> \<sigma> 32 Mem XOR \<langle>31,0\<rangle>regs \<sigma> r32_2"]
      by (auto simp add:msb_nth fst_bool_to_bv_XOR_def bitXOR_nth test_bit_of_take_bits)
      done
qed


(*---------------------------------------------------proofs on or ---------------------------------------*)


lemma test_bit_of_extended_word_64[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "(\<langle>63,0\<rangle>a :: 1000 word) !! 63 = a !! 63"
  using test_bit_of_take_bits[of 63 63 0 "\<langle>63,0\<rangle>a::1000 word",where  ?'a=64]
  by auto



(* Proofs on or  *)


lemma extended_AND_iff_orig_AND[get_semantics_rewriting]:
  fixes a b :: "64 word"
  shows "(\<langle>63,0\<rangle>a = (0::1000 word) \<and> \<langle>63,0\<rangle>b = (0::1000 word)) \<longleftrightarrow>  (a = (0::64 word) \<and> b = (0::64 word))"
proof-
  {
    assume 1: "(\<langle>63,0\<rangle>a = (0::1000 word) \<and> \<langle>63,0\<rangle>b = (0::1000 word))"
    hence 2: "\<forall> i<1000. ((\<langle>63,0\<rangle>a :: 1000 word) !! i = False) \<and> ((\<langle>63,0\<rangle>b :: 1000 word) !! i = False)"
      apply (subst 1)+
      by auto
    have "(a = (0::64 word) \<and> b = (0::64 word))"
    proof-
      {
        fix i :: nat
        assume "i < 64"
        hence "((a !! i = (0 :: 64 word) !! i) \<and> (b !! i = (0 :: 64 word) !! i))"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI)
    qed
  }
 moreover
  {
    assume 1: "(a = (0::64 word) \<and> b = (0::64 word))"
    hence 2: "\<forall> i < 64 . ((a !! i = False) \<and> (b !! i = False))"
      apply (subst 1)
      by auto
    have "(\<langle>63,0\<rangle>a = (0::1000 word) \<and> \<langle>63,0\<rangle>b = (0::1000 word))"
    proof-
      {
        fix i :: nat
        assume "i < 1000"
        hence "( ((\<langle>63,0\<rangle>a :: 1000 word) !! i = (0 :: 1000 word) !! i) \<and> ((\<langle>63,0\<rangle>b :: 1000 word) !! i = (0 :: 1000 word) !! i))"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI)
    qed
  }
  ultimately
  show ?thesis
    by auto
qed

lemma extended_AND_iff_orig_AND_32[get_semantics_rewriting]:
  fixes a b :: "64 word"
  shows "(\<langle>31,0\<rangle>a = (0::1000 word) \<and> \<langle>31,0\<rangle>b = (0::1000 word)) \<longleftrightarrow>  (\<langle>31,0\<rangle>a = (0::32 word) \<and> \<langle>31,0\<rangle>b = (0::32 word))"
proof-
  {
    assume 1: "(\<langle>31,0\<rangle>a = (0::1000 word) \<and> \<langle>31,0\<rangle>b = (0::1000 word))"
    hence 2: "\<forall> i<1000. ((\<langle>31,0\<rangle>a :: 1000 word) !! i = False) \<and> ((\<langle>31,0\<rangle>b :: 1000 word) !! i = False)"
      apply (subst 1)+
      by auto
    have "(\<langle>31,0\<rangle>a = (0::32 word) \<and> \<langle>31,0\<rangle>b = (0::32 word))"
    proof-
      {
        fix i :: nat
        assume "i < 32"
        hence "(((\<langle>31,0\<rangle>a::32 word) !! i = (0 :: 32 word) !! i) \<and> ((\<langle>31,0\<rangle>b::32 word) !! i = (0 :: 32 word) !! i))"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI)
    qed
  }
 moreover
  {
    assume 1: "((\<langle>31,0\<rangle>a :: 32 word) = (0::32 word) \<and> (\<langle>31,0\<rangle>b :: 32 word) = (0::32 word))"
    hence 2: "\<forall> i < 32 . (((\<langle>31,0\<rangle>a ::32 word) !! i = False) \<and> ((\<langle>31,0\<rangle>b :: 32 word) !! i = False))"
      apply (subst 1)
      by auto
    have "((\<langle>31,0\<rangle>a :: 1000 word) = (0::1000 word) \<and> (\<langle>31,0\<rangle>b :: 1000 word) = (0::1000 word))"
    proof-
      {
        fix i :: nat
        assume "i < 1000"
        hence "( ((\<langle>31,0\<rangle>a :: 1000 word) !! i = (0 :: 1000 word) !! i) \<and> ((\<langle>31,0\<rangle>b :: 1000 word) !! i = (0 :: 1000 word) !! i))"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI)
    qed
  }
  ultimately
  show ?thesis
    by blast
qed

lemma take_bits_bitOR_64[get_semantics_rewriting]:
  fixes a b::"64 word"
  shows "((\<langle>63,0\<rangle>a OR \<langle>63,0\<rangle>b) :: 1000 word) = (\<langle>63,0\<rangle>(a OR b) :: 1000 word) "
  apply (subst take_bits_bitOR[symmetric, where ?h=63 and ?l=0 and ?a=a and ?b=b])
  apply simp
  by simp


lemma fst_bool_to_bv_OR_def[get_semantics_rewriting]:
 shows "(fst (bool_to_bv a) OR fst (bool_to_bv b)) = (if a then 1 else if b then 1 else 0)"
  by (auto simp add:bool_to_bv_eq_fst )

lemma is_manual_or_r64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Or) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_or_r64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Or) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = regs \<sigma> r64_2 :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 := op1 OR op2),
               flags := (flags \<sigma>)
        (flag_zf := (op1 OR op2) = (0 :: 64 word),
         flag_cf := False,
         flag_of := False,

         flag_sf := ((sint(op1)<0) \<or> (sint(op2)<0)),
         flag_pf := parity(op1 OR op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add: simp_rules take_bits_bitOR)
      done
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:extended_AND_iff_orig_AND)
      done
    subgoal for \<sigma>
      apply (auto simp add:take_bits_bitOR_64)
      done
    subgoal for \<sigma>
      using fst_bool_to_bv_OR_def
      using word_msb_sint[where ?w="regs \<sigma> r64_1"]
      using word_msb_sint[where ?w="regs \<sigma> r64_2"]
      by (auto simp add: msb_nth test_bit_of_take_bits simp_rules)
      done
  qed


lemma is_manual_or_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Or) (Reg (General ThirtyTwo r64_1)) (Storage (Reg (General ThirtyTwo r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_or_r32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Or) (Reg (General ThirtyTwo r64_1)) (Storage (Reg (General ThirtyTwo r64_2)))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r64_1 :: 32 word;
                   op2 = \<langle>31,0\<rangle> regs \<sigma> r64_2 :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 :=  \<langle>31,0\<rangle>(op1 OR op2)),
               flags := (flags \<sigma>)
        (flag_zf := (op1 OR op2) = (0 :: 32 word),
         flag_cf := False,
         flag_of := False,

         flag_sf := (((op1 !! 31) \<or> (op2 !! 31)) = True),
         flag_pf := parity(op1 OR op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add: simp_rules take_bits_bitOR)
      done
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:extended_AND_iff_orig_AND_32)
      done
    subgoal for \<sigma>
      apply (simp add: simp_rules parity_ucast take_bits_bitOR)
      done
    subgoal for \<sigma>
      using fst_bool_to_bv_OR_def
      by (auto simp add:test_bit_of_take_bits simp_rules)
      done
  qed


lemma is_manual_or_r32_m32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Or) (Reg (General ThirtyTwo r64_1)) (Storage (Memory ThirtyTwo Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_or_r32_m32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Or) (Reg (General ThirtyTwo r64_1)) (Storage (Memory ThirtyTwo Mem))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r64_1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>(read_mem64 \<alpha> \<sigma> 32 Mem) :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 :=  ucast(op1 OR op2)),
               flags := (flags \<sigma>)
        (flag_zf := (op1 OR op2) = (0 :: 32 word),
         flag_cf := False,
         flag_of := False,

         flag_sf := (((op1 !! 31) \<or> (op2 !! 31)) = True),
         flag_pf := parity(op1 OR op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (simp add: simp_rules)
      done
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:extended_AND_iff_orig_AND_32)
      done
    subgoal for \<sigma>
      apply (simp add: simp_rules parity_ucast take_bits_bitOR)
      done
    subgoal for \<sigma>
      using fst_bool_to_bv_OR_def
      by (auto simp add:test_bit_of_take_bits simp_rules)
      done
  qed


lemma useless_take_bits_ucast[get_semantics_rewriting]:
  shows "(\<langle>31,0\<rangle>(a :: 1000 word) :: 1000 word) = ucast (\<langle>31,0\<rangle>a :: 32 word) "
  by auto


lemma useless_and_generic[get_semantics_rewriting]:
  fixes a::"'a::len word"
  assumes "LENGTH('b :: len) < LENGTH('a)" 
    and   "h = LENGTH('b) - 1"
  shows "\<langle>h,0\<rangle>a AND ((2^LENGTH('b) - 1) :: 'b:: len word) = (\<langle>h,0\<rangle>a  :: 'b:: len word)"
proof-
  show ?thesis
    using max_word_eq
    apply (subst max_word_eq[symmetric])
    by auto
qed

lemma useless_sextend_hardocded_32_word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "\<langle>31,0\<rangle>((sextend (\<langle>63,0\<rangle>a :: 1000 word) 64 32) :: 1000 word) = (\<langle>31,0\<rangle>a ::32 word)"
proof-
  show ?thesis
      unfolding sextend.simps
      apply (auto simp add: simp_rules mask_def)
      apply (subst Word.word_bool_alg.conj_disj_distrib2)
       apply (auto)
       apply (subst take_bits_remove[where ?w="a" and ?h="63", simplified])
       apply (subst take_bits_bitAND)
       apply auto
      apply (subst useless_and_generic[where ?a=a and ?h=31 and ?'b=32, simplified])
      by auto
  qed

lemma is_manual_or_r32_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Or) (Reg (General ThirtyTwo r32_1)) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_or_r32_Imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Or) (Reg (General ThirtyTwo r32_1)) (Immediate SixtyFour (ImmVal ImmValue))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word;
                    op2 = (word_of_int ImmValue) :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32_1 :=  ucast(op1 OR \<langle>31,0\<rangle>op2)),
               flags := (flags \<sigma>)
        (flag_zf := (op1 OR \<langle>31,0\<rangle>op2) = (0 :: 32 word),
         flag_cf := False,
         flag_of := False,

       flag_sf := sint(op1 OR \<langle>31,0\<rangle>op2) < 0,
         flag_pf := parity(op1 OR \<langle>31,0\<rangle>op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (simp add: simp_rules useless_sextend_hardocded_32_word)
      done
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:useless_sextend_hardocded_32_word extended_AND_iff_orig_AND_32)
      done
    subgoal for \<sigma>
      apply (simp add: simp_rules parity_ucast take_bits_bitOR)
      done
    subgoal for \<sigma>
      apply (subst word_msb_sint[where ?w="(\<langle>31,0\<rangle>regs \<sigma> r32_1 OR \<langle>31,0\<rangle>word_of_int ImmValue) :: 32 word", unfolded msb_nth, symmetric])
      apply (subst word_ao_nth[where ?x="(\<langle>31,0\<rangle>regs \<sigma> r32_1) :: 32 word" and ?y="(\<langle>31,0\<rangle>word_of_int ImmValue) :: 32 word" and ?n="(LENGTH(32) - 1)"])
      using fst_bool_to_bv_OR_def
      by (auto simp add:test_bit_of_take_bits simp_rules)
      done
  qed


lemma is_manual_or_r64_m64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Or) (Reg (General SixtyFour r64_1)) (Storage (Memory SixtyFour Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_or_r64_m64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Or) (Reg (General SixtyFour r64_1)) (Storage (Memory SixtyFour Mem))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 := op1 OR op2),
               flags := (flags \<sigma>)
        (flag_zf := (op1 OR op2) = (0 :: 64 word),
         flag_cf := False,
         flag_of := False,

         flag_sf := ((sint(op1)<0) \<or> (sint(op2)<0)),
         flag_pf := parity(op1 OR op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add: simp_rules take_bits_bitOR)
      done
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:extended_AND_iff_orig_AND)
      done
    subgoal for \<sigma>
      apply (auto simp add:take_bits_bitOR_64)
      done
    subgoal for \<sigma>
      apply (subst  test_bit_of_extended_word_64[where ?a="regs \<sigma> r64_1"])
      apply (subst  test_bit_of_extended_word_64[where ?a="read_mem64 \<alpha> \<sigma> 64 Mem"])
      apply (subst word_msb_sint[where ?w="regs \<sigma> r64_1", symmetric, unfolded msb_nth, simplified])
      apply (subst word_msb_sint[where ?w="read_mem64 \<alpha> \<sigma> 64 Mem", symmetric, unfolded msb_nth, simplified])
      using fst_bool_to_bv_OR_def
      by (auto simp add: msb_nth test_bit_of_take_bits simp_rules)
      done
  qed


(*---------------------------------------------------proofs on and ---------------------------------------*)
lemma is_manual_and_r64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 And) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_and_r64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 And) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = regs \<sigma> r64_2 :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 := op1 AND op2),
               flags := (flags \<sigma>)
        (flag_zf := (op1 AND op2) = (0 :: 64 word),
         flag_cf := False,
         flag_of := False,

         flag_sf := (((op1 !! 63) \<and> (op2 !! 63)) = True),
         flag_pf := parity(op1 AND op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
     apply (simp add:simp_rules take_bits_bitAND)
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      using take_bits_bitAND[where ?h=63 and ?l=0 and ?a="regs \<sigma> r64_1" and ?b="regs \<sigma> r64_2"  ]
      apply auto
      done
    subgoal for \<sigma>
      apply (subst take_bits_bitAND[symmetric, where ?h=63 and ?l=0 and ?a="regs \<sigma> r64_1" and ?b="regs \<sigma> r64_2", simplified])
      apply (simp add:parity_ucast)
      done
    subgoal for \<sigma>
      by (auto simp add:test_bit_of_take_bits fst_bool_to_bv_AND_def)
    done
qed

lemma is_manual_and_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 And) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_and_r32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 And) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32_1 := ucast(op1 AND op2)),
               flags := (flags \<sigma>)
        (flag_zf := (op1 AND op2) = (0 :: 32 word),
         flag_cf := False,
         flag_of := False,
         flag_sf := (sint op1 < 0) \<and> (sint op2 < 0),
         flag_pf := parity(op1 AND op2))  
\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
      apply (simp add:simp_rules take_bits_bitAND)
    apply (intro flags_eqI,simp_all)
      apply (simp add:take_bits_AND_zero_32_word)
     apply (simp add: parity_ucast)
    apply (auto simp add: fst_bool_to_bv_AND_def test_bit_of_take_bits)
    subgoal for \<sigma>
      using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1"]
      apply (auto)
      done
    subgoal for \<sigma>
      using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_2"]
      apply (auto)
      done
    subgoal for \<sigma>
      using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1"]
      apply (auto)
      done
    subgoal for \<sigma>
      using word_msb_sint[where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_2"]
      by (auto)
      done
  qed

lemma and_2p_minus_1_32_extended[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "\<langle>63,0\<rangle>a AND (2^(LENGTH(32)) - 1 :: 1000 word) = (\<langle>31,0\<rangle>a :: 1000 word)"
proof-
  {
    fix n :: nat
    assume 1:"n < 1000"
    have a: "(2^(LENGTH(32)) - 1 :: 1000 word) = ucast (2^(LENGTH(32)) - 1 :: 32 word)"
      apply (subst max_word_eq[symmetric])
      by (auto simp add:simp_rules max_word_eq)
    have b: "(mask 32 :: 1000 word) = ucast (mask 32 :: 32 word)"
      by simp
    have c: " (mask 32 :: 32 word) = (2^(LENGTH(32)) - 1 :: 32 word)"
      apply (subst max_word_eq[symmetric])
      by (simp add: max_word_def)
    have d: "ucast (2^(LENGTH(32)) - 1 :: 32 word) = (mask 32 :: 1000 word)"
      apply (subst c[symmetric])
      apply (subst b[symmetric])
      by simp
    have e :"(mask 32 :: 1000 word) !! n = (n < 32)"
      apply (subst b)
      apply (subst c)
      apply(subst max_word_eq[symmetric])
      by (auto simp add:simp_rules)
    hence "(\<langle>63,0\<rangle>a AND (2^(LENGTH(32)) - 1 :: 1000 word)) !! n = (\<langle>31,0\<rangle>a :: 1000 word) !! n"
      using 1
      apply (subst a)
      apply (subst d)
      by (auto simp add: mask_def word_ao_nth test_bit_of_take_bits e)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed

lemma test_nth_32_bit[get_semantics_rewriting]:
  fixes a:: "64 word"
  assumes "i<32"
  shows "(\<langle>63,0\<rangle>a :: 1000 word) !! i = (\<langle>31,0\<rangle>a :: 32 word) !! i"
proof-
  show ?thesis
    using assms
    by(auto simp add:simp_rules test_bit_of_take_bits)
qed

lemma test_bit_msb_sextend[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "(sextend (\<langle>63,0\<rangle>a :: 1000 word) 64 32 :: 1000 word) !! 31 = (\<langle>31,0\<rangle>sextend (\<langle>63,0\<rangle>a :: 1000 word) 64 32 :: 32 word) !! 31"
proof-
  show ?thesis
    by (auto simp add:test_bit_of_take_bits)
qed

lemma is_manual_and_m32_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 And) (Memory ThirtyTwo Mem) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_and_m32_Imm32[presimplify]:
 shows "get_semantics \<alpha> semantics (Binary (IS_8088 And) (Memory ThirtyTwo Mem) (Immediate SixtyFour (ImmVal ImmValue))) si =
         (\<lambda> \<sigma> . let a = resolve_address \<alpha> \<sigma> Mem;
                    op1 = read_mem64 \<alpha> \<sigma> 32 Mem;
                    op2 = (word_of_int ImmValue) :: 64 word in
      \<sigma>\<lparr>mem := write_blocks [a \<rhd> rev (\<lbrace>3,0\<rbrace> (\<langle>31,0\<rangle>(op1 AND op2) :: 32 word))] (mem \<sigma>),
      flags := (flags \<sigma>)
      (flag_zf :=  (\<langle>31,0\<rangle>(op1 AND op2)) = (0 :: 32 word),
       flag_cf := False,
       flag_of := False,
       flag_sf := sint((\<langle>31,0\<rangle>op1 :: 32 word) AND (\<langle>31,0\<rangle>op2)) < 0,
       flag_pf := parity(\<langle>31,0\<rangle>(op1 AND op2) :: 32 word))  \<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
  subgoal for \<sigma>
    apply (auto simp add:resolve_address_after_update_flag useless_sextend_hardocded_32_word)
    apply (subst take_bits_bitAND[symmetric, where ?h=31 and ?l=0 and ?a="fst (read_memory \<alpha> \<sigma> 32 Mem)" and ?b="word_of_int ImmValue"])
    apply auto
    done
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    apply (auto simp add:take_bits_remove take_bits_bitAND take_bits_AND_zero_32_word)
    done
  subgoal for \<sigma>
    apply (auto simp add: parity_ucast take_bits_bitAND)
    done
  subgoal for \<sigma>
    apply (subst word_msb_sint[where ?w="(\<langle>31,0\<rangle>read_mem64 \<alpha> \<sigma> 32 Mem AND \<langle>31,0\<rangle>word_of_int ImmValue) :: 32 word", unfolded msb_nth, symmetric])
    apply (subst word_ao_nth[where ?x="(\<langle>31,0\<rangle>read_mem64 \<alpha> \<sigma> 32 Mem) :: 32 word" and ?y="(\<langle>31,0\<rangle>word_of_int ImmValue) :: 32 word" and ?n="(LENGTH(32) - 1)"])
    apply (subst test_nth_32_bit[where ?a="read_mem64 \<alpha> \<sigma> 32 Mem" and i=31])
    by (auto simp add:simp_rules  test_bit_of_take_bits fst_bool_to_bv_AND_def)
  done
qed


lemma is_manual_and_r32_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 And) (Reg (General ThirtyTwo r32_1)) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_and_r32_Imm32[presimplify]:
 shows "get_semantics \<alpha> semantics (Binary (IS_8088 And) (Reg (General ThirtyTwo r32_1)) (Immediate SixtyFour (ImmVal ImmValue))) si =
         (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word;
                    op2 = (word_of_int ImmValue) :: 64 word
                 in
       \<sigma>\<lparr>regs := (regs \<sigma>)(r32_1 := (ucast(op1 AND \<langle>31,0\<rangle>op2) :: 64 word)),
      flags := (flags \<sigma>)
      (flag_zf :=  ((op1 AND \<langle>31,0\<rangle>op2)) = (0 :: 32 word),
       flag_cf := False,
       flag_of := False,
       flag_sf := sint(op1 AND (\<langle>31,0\<rangle>op2)) < 0,
       flag_pf := parity(op1 AND \<langle>31,0\<rangle>op2))  \<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
  subgoal for \<sigma>
    apply (auto simp add: simp_rules)
    done
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    apply (auto simp add:take_bits_remove take_bits_bitAND take_bits_AND_zero_32_word)
    done
  subgoal for \<sigma>
    apply (auto simp add: parity_ucast take_bits_bitAND)
    done
  subgoal for \<sigma>
    apply (subst word_msb_sint[where ?w="(\<langle>31,0\<rangle>regs \<sigma> r32_1 AND \<langle>31,0\<rangle>word_of_int ImmValue) :: 32 word", unfolded msb_nth, symmetric])
    apply (subst word_ao_nth[where ?x="(\<langle>31,0\<rangle>regs \<sigma> r32_1) :: 32 word" and ?y="(\<langle>31,0\<rangle>word_of_int ImmValue) :: 32 word" and ?n="(LENGTH(32) - 1)"])
    by (auto simp add:simp_rules  test_bit_of_take_bits fst_bool_to_bv_AND_def)
  done
qed


(*---------------------------------------------------proofs on not ---------------------------------------*)
lemma is_manual_not_r64_r64[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Not) (Storage (Reg (General SixtyFour r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_not_r64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Unary (IS_8088 Not) (Storage (Reg (General SixtyFour r64_2)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_2 :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_2 := NOT op1)\<rparr>)"
proof -
 show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
     by (simp add:simp_rules)
 qed

lemma is_manual_not_r32[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Not) (Storage (Reg (General ThirtyTwo r32)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_not_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Unary (IS_8088 Not) (Storage (Reg (General ThirtyTwo r32)))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32 := \<langle>31,0\<rangle>(NOT op1))\<rparr>)"
proof -
 show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')+
   by (simp add:simp_rules)
 qed


(*---------------------------------------------------proofs on neg ---------------------------------------*)

lemma zero_le_2p[get_semantics_rewriting]:
  assumes "n < LENGTH('a)"
  shows "(0::'a::len word) < 2 ^ n"
  using assms
proof (induct n)
  case 0
  thus ?case
    by auto
next
  case (Suc n)
  thus ?case
    using shiftl_1[symmetric,of "n+1",where 'a='a]
    using is_zero_shiftl[of "1::'a word" "n+1"]
    apply (auto simp del: shiftl_1)
    by fastforce
qed


lemma take_bits_neg[get_semantics_rewriting]:
  fixes w :: "1000 word"
  shows "\<langle>63,0\<rangle> (- w) = (ucast (NOT w) + 1 :: 64 word)"
  apply (subst twos_complement)
  apply (subst word_succ_p1)
  apply (subst take_bits_plus[of 63 "NOT w" 1])
  apply simp
  apply simp
  apply simp
  apply (intro word_eqI)
  by (auto simp add: word_size nth_ucast word_ao_nth bitNOT_nth test_bit_of_take_bits)

lemma take_bits_drop_minus_64bit[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "\<langle>63,0\<rangle> (- (\<langle>63,0\<rangle>a :: 1000 word)) = -a"
  using take_bits_minus_64bit(1)[where ?'a=1000,of 0 "\<langle>63,0\<rangle>a"]
  by auto

lemma test_bit_of_take_bits_extended_64_neg_word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "(- (\<langle>63,0\<rangle>a :: 1000 word)) !! 63 = (-a) !! 63"
  using take_bits_drop_minus_64bit[of a]
  using test_bit_of_take_bits[of 63 63 0 "- (\<langle>63,0\<rangle>a::1000 word)",where  ?'a=64]
  by auto

lemma test_bit_of_take_bits_extended_64_word[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "((\<langle>63,0\<rangle>a :: 1000 word)) !! 63 = (a) !! 63"
  using take_bits_drop_minus_64bit[of a]
  using test_bit_of_take_bits[of 63 63 0 "(\<langle>63,0\<rangle>a::1000 word)",where  ?'a=64]
  by auto


lemma diff_len_word_eq_0_64[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "((\<langle>63,0\<rangle>a :: 1000 word) = 0) = (a = 0)"
proof-
  {
    assume 1: "\<langle>63,0\<rangle>a = (0::1000 word)"
    hence 2: "\<forall> i<1000. (\<langle>63,0\<rangle>a :: 1000 word) !! i = False"
      apply (subst 1)+
      by auto
    have "(a = (0::64 word))"
    proof-
      {
        fix i :: nat
        assume "i < 64"
        hence "a !! i = (0 :: 64 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits bitXOR_nth)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI )
    qed
  }
 moreover
  {
    assume 1: "a = (0::64 word)"
    hence 2: "\<forall> i < 64 . a !! i = False"
      apply (subst 1)
      by auto
    have "\<langle>63,0\<rangle>a = (0::1000 word)"
    proof-
      {
        fix i :: nat
        assume "i < 1000"
        hence " (\<langle>63,0\<rangle>a:: 1000 word) !! i = (0 :: 1000 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits bitXOR_nth)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI)
    qed
  }
  ultimately
  show ?thesis
    by auto
qed


lemma parity_equality[get_semantics_rewriting]:
  fixes a :: "1000 word"
    and b :: "64 word"
  assumes "\<langle>63,0\<rangle>a = b"
  shows "parity a = parity b"
proof-
  have a:"parity(a) = parity(\<langle>63,0\<rangle>a :: 64 word)"
    unfolding parity_def
    unfolding take_bits_def
    by (auto simp add:simp_rules word_rep_drop)
  thus ?thesis
    apply (subst assms(1)[symmetric]) 
    by (auto simp add:simp_rules)
qed


lemma is_manual_neg_r64_r64[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Neg) (Storage (Reg (General SixtyFour r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_neg_r64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Unary (IS_8088 Neg) (Storage (Reg (General SixtyFour r64_2)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_2 :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_2 := (0:: 64 word) - op1),
        flags := (flags \<sigma>)
        (flag_zf := op1 = (0 :: 64 word),
         flag_cf := op1 \<noteq> (0 :: 64 word),
         flag_sf := (2^63 \<le> - op1),
         flag_of := (op1 \<ge> 2^63 \<and> 2^63 \<le> - op1),
         flag_pf := parity((0:: 64 word) - op1)  )
                
  \<rparr>)"
proof-

  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply rewrite_one_let'
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
     apply (auto simp add: simp_rules take_bits_drop_minus_64bit)
      done
  apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:diff_len_word_eq_0_64)
      done
    subgoal for \<sigma>
      apply (auto simp add:diff_len_word_eq_0_64)
      done
    subgoal for \<sigma>
      using parity_equality[where ?a="- (\<langle>63,0\<rangle>regs \<sigma> r64_2)" and ?b="- regs \<sigma> r64_2"]
      apply (auto simp add:take_bits_drop_minus_64bit)
      done
    subgoal for \<sigma>
      using msb_is_gt_2p[of "- regs \<sigma> r64_2", unfolded msb_nth]
      using msb_is_gt_2p[of "regs \<sigma> r64_2", unfolded msb_nth]
      apply (simp add: test_bit_of_take_bits_extended_64_neg_word test_bit_of_take_bits)
    done
  subgoal for \<sigma>
    apply (subst test_bit_of_take_bits_extended_64_neg_word[where ?a="regs \<sigma> r64_2"])
    apply (subst test_bit_of_take_bits_extended_64_word[where ?a="regs \<sigma> r64_2"])
    apply( subst msb_is_gt_2p[of "- regs \<sigma> r64_2", unfolded msb_nth, simplified])
    apply( subst msb_is_gt_2p[of "regs \<sigma> r64_2", unfolded msb_nth, simplified])
    by simp
  done
qed

lemma diff_len_word_eq_0_32[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "((\<langle>31,0\<rangle>a :: 1000 word) = 0) \<longleftrightarrow> ((\<langle>31,0\<rangle>a :: 32 word) = (0 :: 32 word))"
proof-
  {
    assume 1: "\<langle>31,0\<rangle>a = (0::1000 word)"
    hence 2: "\<forall> i<1000. (\<langle>31,0\<rangle>a :: 1000 word) !! i = False"
      apply (subst 1)+
      by auto
    have "((\<langle>31,0\<rangle>a :: 32 word) = (0::32 word))"
    proof-
      {
        fix i :: nat
        assume "i < 32"
        hence "(\<langle>31,0\<rangle>a :: 32 word) !! i = (0 :: 32 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits)
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI )
    qed
  }
 moreover
  {
    assume 1: "\<langle>31,0\<rangle>a = (0::32 word)"
    hence 2: "\<forall> i < 32 . (\<langle>31,0\<rangle>a :: 32 word) !! i = False"
      apply (subst 1)
      by auto
    have "\<langle>31,0\<rangle>a = (0::1000 word)"
    proof-
      {
        fix i :: nat
        assume "i < 1000"
        hence " (\<langle>31,0\<rangle>a:: 1000 word) !! i = (0 :: 1000 word) !! i"
          using 2[THEN spec, of i]
          by (auto simp add: word_ao_nth test_bit_of_take_bits )
      }
      thus ?thesis
        by (auto simp add: word_size word_eqI)
    qed
  }
  ultimately
  show ?thesis
    by auto
qed


lemma take_bits_minus_extend_32_to_64bits[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "(\<langle>31,0\<rangle>(- (\<langle>31,0\<rangle>a :: 1000 word)) :: 64 word) = (ucast (-(\<langle>31,0\<rangle>a :: 32 word)) :: 64 word)"
  apply (subst take_bits_minus_bit32_generic[where ?a="0 :: 1000 word" and ?b="(\<langle>31,0\<rangle>a :: 1000 word)" and ?'b=64, simplified])
  by (auto simp add:simp_rules)

lemma take_bits_minus_extend_32_to_32bits[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "(\<langle>31,0\<rangle>(- (\<langle>31,0\<rangle>a :: 1000 word)) :: 32 word) = ((-(\<langle>31,0\<rangle>a :: 32 word)))"
  apply (subst take_bits_minus_bit32_generic[where ?a="0 :: 1000 word" and ?b="(\<langle>31,0\<rangle>a :: 1000 word)" and ?'b=32, simplified])
  by (auto simp add:simp_rules)

lemma parity_equality_32[get_semantics_rewriting]:
  fixes a :: "1000 word"
    and b :: "32 word"
  assumes "\<langle>31,0\<rangle>a = b"
  shows "parity a = parity b"
proof-
  have a:"parity(a) = parity(\<langle>31,0\<rangle>a :: 32 word)"
    unfolding parity_def
    unfolding take_bits_def
    by (auto simp add:simp_rules word_rep_drop)
  thus ?thesis
    apply (subst assms(1)[symmetric]) 
    by (auto simp add:simp_rules)
qed

lemma test_32b_neg_wordextended[get_semantics_rewriting]:
  fixes a :: "64 word"
  shows "(- (\<langle>31,0\<rangle>a :: 1000 word)) !! 31 = (-(\<langle>31,0\<rangle>a :: 32 word)) !! 31"
  using take_bits_minus_extend_32_to_32bits[of a]
  using test_bit_of_take_bits[of 31 31 0 "- (\<langle>31,0\<rangle>a::1000 word)",where  ?'a=32]
  by auto

lemma is_manual_neg_r32[is_manual]:
  shows "is_manual assembly semantics (Unary (IS_8088 Neg) (Storage (Reg (General ThirtyTwo r32)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_neg_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Unary (IS_8088 Neg) (Storage (Reg (General ThirtyTwo r32)))) si =
        (\<lambda> \<sigma> . let opx = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32 := ucast ((0:: 32 word) - opx) ),
        flags := (flags \<sigma>)
        (flag_zf := opx = (0 :: 32 word),
         flag_cf := opx \<noteq> (0 :: 32 word),
         flag_sf := sint(0 - opx) < 0,
         flag_of := (opx \<ge> 2^31 \<and> 2^31 \<le> - opx),
         flag_pf := parity((0:: 32 word) - opx)  )
                
  \<rparr>)"
proof-

  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply rewrite_one_let'
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
    subgoal for \<sigma>
     apply (auto simp add: simp_rules take_bits_minus_extend_32_to_64bits)
      done
  apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:diff_len_word_eq_0_32)
      done
    subgoal for \<sigma>
      apply (auto simp add:diff_len_word_eq_0_32)
      done
    subgoal for \<sigma>
      apply (subst stupid[where a="(\<langle>31,0\<rangle>- (\<langle>31,0\<rangle>regs \<sigma> r32))"])
      using parity_equality_32[where ?a="- (\<langle>31,0\<rangle>regs \<sigma> r32)" and ?b="- (\<langle>31,0\<rangle>regs \<sigma> r32)"]
      apply (auto simp add:take_bits_minus_extend_32_to_32bits parity_equality_32 ucast_id)
      done
    subgoal for \<sigma>
      apply (subst word_msb_sint[where ?w="(- (\<langle>31,0\<rangle>regs \<sigma> r32)) :: 32 word", symmetric, unfolded msb_nth, simplified])
      apply (simp add: test_32b_neg_wordextended test_bit_of_take_bits)
    done
  subgoal for \<sigma>
    apply (subst test_32b_of_32AND64_word[where ?a="regs \<sigma> r32"])
    apply (subst test_32b_neg_wordextended[where a="regs \<sigma> r32"]) 
    apply( subst msb_is_gt_2p[of "(- (\<langle>31,0\<rangle>regs \<sigma> r32)) :: 32 word", unfolded msb_nth, simplified])
    apply( subst msb_is_gt_2p[of "\<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word", unfolded msb_nth, simplified])
    by simp
  done
qed


(*---------------------------------------------------proofs on mov ---------------------------------------*)
abbreviation "write_mem16 \<alpha>  \<sigma> a (v::64 word) \<equiv>
                \<sigma>\<lparr>mem := write_block ((resolve_address \<alpha> \<sigma> a) \<rhd> rev (\<lbrace>1,0\<rbrace> v)) (mem \<sigma>)\<rparr>"

abbreviation "write_mem8 \<alpha>  \<sigma> a (v::64 word) \<equiv>
                \<sigma>\<lparr>mem := write_block ((resolve_address \<alpha> \<sigma> a) \<rhd> rev (\<lbrace>0,0\<rbrace> v)) (mem \<sigma>)\<rparr>"


lemma is_manual_mov_r64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_r64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) si =
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = regs \<sigma> r64_2 :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 := op2)\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  by (simp add: simp_rules)
qed

lemma is_manual_mov_m64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Memory SixtyFour Mem) (Storage (Reg (General SixtyFour r64)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_m64_r64[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Memory SixtyFour Mem) (Storage (Reg (General SixtyFour r64)))) si =
        (\<lambda> \<sigma>.  let op2 = regs \<sigma> r64 :: 64 word
          in 
          write_mem64 \<alpha> \<sigma> Mem op2)"
    apply (rule ext)
    apply(subst get_semantics_def)
    by(rewrite_one_let' add: semantics_def)+

lemma is_manual_mov_m32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Memory ThirtyTwo Mem) (Storage (Reg (General ThirtyTwo r32)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_m32_r32[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Memory ThirtyTwo Mem) (Storage (Reg (General ThirtyTwo r32))) ) si =
        (\<lambda> \<sigma>.  let op2 = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word
          in 
          write_mem32 \<alpha> \<sigma> Mem op2)"
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    by(rewrite_one_let')+



lemma is_manual_mov_m16_r16[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Memory Sixteen Mem) (Storage (Reg (General Sixteen r16)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_m16_r16[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Memory Sixteen Mem) (Storage (Reg (General Sixteen r16))) ) si =
        (\<lambda> \<sigma>.  let op2 = \<langle>15,0\<rangle>regs \<sigma> r16 :: 64 word;
                op1 = \<langle>63,16\<rangle>read_mem64 \<alpha> \<sigma> 16 Mem :: 64 word;
                op3 = \<langle>15,0\<rangle>regs \<sigma> r16 (* fst (bv_cat (op1, 48) (op2, 16)) :: 64 word *)

          in 
          write_mem16 \<alpha> \<sigma> Mem op3)"
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    by(rewrite_one_let')+
    
lemma is_manual_mov_m8_r8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Memory Eight Mem) (Storage (Reg (General Eight r8_1)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_m8_r8[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Memory Eight Mem) (Storage (Reg (General Eight r8_1))) ) si =
        (\<lambda> \<sigma>.  let op2 = \<langle>7,0\<rangle>regs \<sigma> r8_1 :: 64 word;
                op1 = \<langle>63,8\<rangle>read_mem64 \<alpha> \<sigma> 8 Mem :: 64 word;
                op3 = \<langle>7,0\<rangle>regs \<sigma> r8_1

          in 
          write_mem8 \<alpha> \<sigma> Mem op3)"
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    by(rewrite_one_let')+
    
lemma is_manual_mov_m16_imm16[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Memory Sixteen Mem) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_mov_m16_imm16[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Memory Sixteen Mem) (Immediate SixtyFour (ImmVal ImmValue)) ) si =
        (\<lambda> \<sigma>.  let op2 = word_of_int ImmValue :: 64 word;
                op1 = \<langle>63,16\<rangle>read_mem64 \<alpha> \<sigma> 16 Mem :: 64 word;
                op3 =  fst (bv_cat (op1, 48) (op2, 16)) :: 64 word

          in 
          write_mem16 \<alpha> \<sigma> Mem op3)"
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    apply(rewrite_one_let')+
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitOR[where ?h=63 and ?l=0 and ?a="(\<langle>63,16\<rangle>fst (read_memory \<alpha> \<sigma> 16 Mem) << 16) :: 1000 word" and ?b="\<langle>15,0\<rangle>word_of_int ImmValue "])
    by (auto simp add:simp_rules take_bits_def word_rep_drop shiftl_of_bl)

lemma is_manual_mov_m8_imm8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Memory Eight Mem) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_mov_m8_imm8[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Memory Eight Mem) (Immediate SixtyFour (ImmVal ImmValue)) ) si =
        (\<lambda> \<sigma>.  let op2 = word_of_int ImmValue :: 64 word;
                op1 = \<langle>63,8\<rangle>read_mem64 \<alpha> \<sigma> 8 Mem :: 64 word;
                op3 = fst (bv_cat (op1, 56) (op2, 8)) :: 64 word

          in 
          write_mem8 \<alpha> \<sigma> Mem op3)"
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    apply(rewrite_one_let')+
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitOR[where ?h=63 and ?l=0 and ?a="(\<langle>63,8\<rangle>fst (read_memory \<alpha> \<sigma> 8 Mem) << 8) :: 1000 word" and ?b="\<langle>7,0\<rangle>word_of_int ImmValue "])
    by (auto simp add:simp_rules take_bits_def word_rep_drop shiftl_of_bl)



lemma is_manual_mov_r16_imm16[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General Sixteen r16))  (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_mov_r16_imm16[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General Sixteen r16)) (Immediate SixtyFour (ImmVal ImmValue)) ) si =
        (\<lambda> \<sigma>.  let op2 = word_of_int ImmValue :: 64 word;
                op1 = \<langle>63,16\<rangle>regs \<sigma> r16 :: 64 word;
                op3 = fst (bv_cat (op1, 48) (op2, 16)) :: 64 word
          in 
        \<sigma>\<lparr>regs := (regs \<sigma>)(r16 := op3)\<rparr>)" 
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    apply(rewrite_one_let')+
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitOR[where ?h=63 and ?l=0 and ?a="(\<langle>63,16\<rangle>regs \<sigma> r16 << 16) :: 1000 word" and ?b="\<langle>15,0\<rangle>word_of_int ImmValue"])
    by (auto simp add:simp_rules take_bits_def word_rep_drop shiftl_of_bl)


lemma is_manual_mov_r8_imm8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General Eight r16))  (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_mov_r8_imm8[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General Eight r8_1)) (Immediate SixtyFour (ImmVal ImmValue)) ) si =
        (\<lambda> \<sigma>.  let op2 = word_of_int ImmValue :: 64 word;
                op1 = \<langle>63,8\<rangle>regs \<sigma> r8_1 :: 64 word;
                op3 = fst (bv_cat (op1, 56) (op2, 8)) :: 64 word
          in 
        \<sigma>\<lparr>regs := (regs \<sigma>)(r8_1 := op3)\<rparr>)" 
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    apply(rewrite_one_let')+
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitOR[where ?h=63 and ?l=0 and ?a="(\<langle>63,8\<rangle>regs \<sigma> r8_1 << 8) :: 1000 word" and ?b="\<langle>7,0\<rangle>word_of_int ImmValue"])
    by (auto simp add:simp_rules take_bits_def word_rep_drop shiftl_of_bl)



lemma is_manual_mov_r16_r16[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General Sixteen r16_1))  (Storage (Reg (General Sixteen r16_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_r16_r16[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov)  (Reg (General Sixteen r16_1))  (Storage (Reg (General Sixteen r16_2))) ) si =
        (\<lambda> \<sigma>.  let op2 =regs \<sigma> r16_2 :: 64 word;
                op1 = \<langle>63,16\<rangle>regs \<sigma> r16_1 :: 64 word;
                op3 = fst (bv_cat (op1, 48) (op2, 16)) :: 64 word
          in 
        \<sigma>\<lparr>regs := (regs \<sigma>)(r16_1 := op3)\<rparr>)" 
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    apply(rewrite_one_let')+
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitOR[where ?h=63 and ?l=0 and ?a="(\<langle>63,16\<rangle>regs \<sigma> r16_1 << 16) :: 1000 word" and ?b="\<langle>15,0\<rangle>regs \<sigma> r16_2"])
    by (auto simp add:simp_rules take_bits_def word_rep_drop shiftl_of_bl)

lemma is_manual_mov_r8_r8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General Eight r8_1))  (Storage (Reg (General Eight r8_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_r8_r8[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov)  (Reg (General Eight r8_1))  (Storage (Reg (General Eight r8_2))) ) si =
        (\<lambda> \<sigma>.  let op2 =regs \<sigma> r8_2 :: 64 word;
                op1 = \<langle>63,8\<rangle>regs \<sigma> r8_1 :: 64 word;
                op3 = fst (bv_cat (op1, 56) (op2, 8)) :: 64 word
          in 
        \<sigma>\<lparr>regs := (regs \<sigma>)(r8_1 := op3)\<rparr>)" 
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    apply(rewrite_one_let')+
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitOR[where ?h=63 and ?l=0 and ?a="(\<langle>63,8\<rangle>regs \<sigma> r8_1 << 8) :: 1000 word" and ?b="\<langle>7,0\<rangle>regs \<sigma> r8_2"])
    by (auto simp add:simp_rules take_bits_def word_rep_drop shiftl_of_bl)

lemma is_manual_mov_r16_m16[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General Sixteen r16_1))  (Storage (Memory Sixteen Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_r16_m16[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov)  (Reg (General Sixteen r16_1))  (Storage (Memory Sixteen Mem)) ) si =
        (\<lambda> \<sigma>.  let op2 =read_mem64 \<alpha> \<sigma> 16 Mem  :: 64 word;
                op1 = \<langle>63,16\<rangle>regs \<sigma> r16_1 :: 64 word;
                op3 = fst (bv_cat (op1, 48) (op2, 16)) :: 64 word
          in 
        \<sigma>\<lparr>regs := (regs \<sigma>)(r16_1 := op3)\<rparr>)" 
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    apply(rewrite_one_let')+
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitOR[where ?h=63 and ?l=0 and ?a="(\<langle>63,16\<rangle>regs \<sigma> r16_1 << 16) :: 1000 word" and ?b="\<langle>15,0\<rangle>fst (read_memory \<alpha> \<sigma> 16 Mem)"])
    by (auto simp add:simp_rules take_bits_def word_rep_drop shiftl_of_bl)

lemma is_manual_mov_r8_m8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General Eight r8_1))  (Storage (Memory Eight Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_r8_m8[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General Eight r8_1))  (Storage (Memory Eight Mem))) si =
        (\<lambda> \<sigma>.  let op2 =read_mem64 \<alpha> \<sigma> 8 Mem  :: 64 word;
                op1 = \<langle>63,8\<rangle>regs \<sigma> r8_1 :: 64 word;
                op3 = fst (bv_cat (op1, 56) (op2, 8)) :: 64 word
          in 
        \<sigma>\<lparr>regs := (regs \<sigma>)(r8_1 := op3)\<rparr>)" 
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    apply(rewrite_one_let')+
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitOR[where ?h=63 and ?l=0 and ?a="(\<langle>63,8\<rangle>regs \<sigma> r8_1 << 8) :: 1000 word" and ?b="\<langle>7,0\<rangle>fst (read_memory \<alpha> \<sigma> 8 Mem)"])
    by (auto simp add:simp_rules take_bits_def word_rep_drop shiftl_of_bl)


lemma is_manual_mov_r64_m64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General SixtyFour r64)) (Storage (Memory SixtyFour Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_r64_m64[presimplify]:
  shows  "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General SixtyFour r64)) (Storage (Memory SixtyFour Mem))) si =
        (\<lambda> \<sigma>.   let op1 = regs \<sigma> r64 :: 64 word;
                op2 = read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word
          in 
          \<sigma>\<lparr>regs := (regs \<sigma>)(r64 := op2)\<rparr>)"

proof-
  show ?thesis
    apply (rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add: semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    by (simp add: simp_rules)
qed      

lemma is_manual_mov_r32_m32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General ThirtyTwo r32)) (Storage (Memory ThirtyTwo Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_r32_m32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General ThirtyTwo r32)) (Storage (Memory ThirtyTwo Mem))) si = 
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word;
                   op2 = \<langle>31,0\<rangle>(read_mem64 \<alpha> \<sigma> 32 Mem) :: 32 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r32 := \<langle>31,0\<rangle>op2)\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    by(simp add:simp_rules)
qed

lemma is_manual_mov_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General ThirtyTwo r1_32)) (Storage (Reg (General ThirtyTwo r2_32)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_r32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General ThirtyTwo r1_32)) (Storage (Reg (General ThirtyTwo r2_32)))) si = 
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r1_32 :: 32 word;
                   op2 = \<langle>31,0\<rangle>regs \<sigma> r2_32 :: 32 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1_32 := \<langle>31,0\<rangle>op2)\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    by(simp add:simp_rules)
qed


lemma truncating_word_of_int_32_bits[get_semantics_rewriting]:
  shows "(\<lbrace>3,0\<rbrace> (word_of_int imm :: 64 word)) = (\<lbrace>3,0\<rbrace> (word_of_int imm :: 32 word))"
proof-
  let ?xs = "\<lbrace>3,0\<rbrace> (word_of_int imm :: 64 word)"
  let ?ys = "\<lbrace>3,0\<rbrace> (word_of_int imm :: 32 word)"
  {
    fix i :: nat
    assume i: "i < length ?xs"
    {
      fix j :: nat
      have i: "i \<in> {0,1,2,3}"
        using i
        by auto
      assume "j < 8"
      hence "?xs ! i !! j = ?ys ! i !! j"
        using i
        by (auto simp add: nth_bytes_of test_bit_of_take_bits test_bit_of_byte_of)
    }
    hence "?xs ! i = ?ys ! i"
      apply (intro word_eqI)
      by (auto simp add: word_size)
  }
  thus ?thesis
    apply (intro nth_equalityI)
    by auto
qed

lemma is_manual_mov_m32_imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Memory ThirtyTwo Mem) (Immediate ImmSize (ImmVal imm))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


(* Using Old IMM Resolution *)
lemma get_semantics_mov_m32_imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Memory ThirtyTwo Mem) (Immediate SixtyFour (ImmVal imm))) si = 
        (\<lambda> \<sigma> . let op2 = imm  
            in
             write_mem32 \<alpha> \<sigma> Mem (word_of_int imm))"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (simp add: truncating_word_of_int_32_bits )
qed


lemma is_manual_mov_r32_imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General ThirtyTwo r1_32)) (Immediate ImmSize (ImmVal imm))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_mov_r32_imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General ThirtyTwo r1_32)) (Immediate SixtyFour (ImmVal Imm))) si = 
        (\<lambda> \<sigma> . let op2 = word_of_int Imm :: 64 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1_32 := (\<langle>31,0\<rangle>op2) :: 64 word)\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
qed


lemma is_manual_mov_r64_imm64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Reg (General SixtyFour r64)) (Immediate ImmSize (ImmVal imm))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mov_r64_imm64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Reg (General SixtyFour r64)) (Immediate SixtyFour (ImmVal Imm))) si = 
        (\<lambda> \<sigma> . let op2 = word_of_int Imm :: 64 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r64 := op2)\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
qed

lemma is_manual_mov_m64_imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Mov) (Memory SixtyFour Mem) (Immediate ImmSize (ImmVal imm))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_mov_m64_imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Mov) (Memory SixtyFour Mem) (Immediate SixtyFour (ImmVal Imm))) si = 
        (\<lambda> \<sigma> . let op2 = imm  
            in
             write_mem64 \<alpha> \<sigma> Mem (word_of_int Imm::64 word))"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules sextend_useless_64_64)
qed

(*---------------------------------------------------proofs on cmovae ---------------------------------------*)

lemma is_manual_cmovae_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_PentiumPro Cmovae) (Reg (General ThirtyTwo r1)) (Storage (Reg (General ThirtyTwo r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmovae_r32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_PentiumPro Cmovae) (Reg (General ThirtyTwo r1)) (Storage (Reg (General ThirtyTwo r2)))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>regs \<sigma> r2 :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r1 := if flags \<sigma> flag_cf then ucast op1 else ucast op2)\<rparr>)"
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    apply (auto simp add:simp_rules semantics_def)
    apply(rewrite_one_let')+
  by (auto simp add:simp_rules bv_to_bool_def word_lsb_alt test_bit_of_take_bits)

(*---------------------------------------------------proofs on cmova ---------------------------------------*)

lemma is_manual_cmova_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_PentiumPro Cmova) (Reg (General ThirtyTwo r1)) (Storage (Reg (General ThirtyTwo r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cmova_r32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_PentiumPro Cmova) (Reg (General ThirtyTwo r1)) (Storage (Reg (General ThirtyTwo r2)))) si =
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>regs \<sigma> r2 :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r1 := if flags \<sigma> flag_cf \<or> flags \<sigma> flag_zf then ucast op1 else ucast op2)\<rparr>)"
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    apply (auto simp add:simp_rules semantics_def)
    apply(rewrite_one_let')+
  by (auto simp add:simp_rules bv_to_bool_def word_lsb_alt test_bit_of_take_bits)

(*---------------------------------------------------proofs on movsx ---------------------------------------*)
lemma is_manual_movsx_r32_r8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_80386 Movsx) (Reg (General ThirtyTwo r1_32)) (Storage (Reg (General Eight r2_8)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movsx_r32_r8[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_80386 Movsx) (Reg (General ThirtyTwo r1_32)) (Storage (Reg (General Eight r2_8)))) si = 
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r1_32 :: 32 word;
                   op2 = sextend (\<langle>7,0\<rangle>regs \<sigma> r2_8 :: 32 word) 8 32
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1_32 := ucast op2 )\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
qed

(*---------------------------------------------------proofs on movsxd ---------------------------------------*)

lemma is_manual_movsxd_r64_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_X86_64 Movsxd) (Reg (General SixtyFour r1)) (Storage (Reg (General ThirtyTwo r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movsxd_r64_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_X86_64 Movsxd) (Reg (General SixtyFour r1)) (Storage (Reg (General ThirtyTwo r2)))) si =
        (\<lambda> \<sigma> . let op2 = \<langle>31,0\<rangle>regs \<sigma> r2 :: 32 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1 := sextend (ucast op2) 32 64)\<rparr>)"
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)


lemma is_manual_movsxd_r64_m32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_X86_64 Movsxd) (Reg (General SixtyFour r1)) (Storage (Memory ThirtyTwo Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movsxd_r64_m32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_X86_64 Movsxd) (Reg (General SixtyFour r1)) (Storage (Memory ThirtyTwo Mem))) si =
        (\<lambda> \<sigma> . let op2 = \<langle>31,0\<rangle>(read_mem64 \<alpha> \<sigma> 32 Mem) :: 32 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1 := sextend (ucast op2) 32 64)\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (subst unfold_semantics)
  apply (auto simp add: Let'_def simp_rules )
  done




(*---------------------------------------------------proofs on movzx ---------------------------------------*)

lemma is_manual_movzx_r32_m8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_80386 Movzx) (Reg (General ThirtyTwo r1_32)) (Storage (Memory Eight Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movzx_r32_m8[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_80386 Movzx) (Reg (General ThirtyTwo r1_32)) (Storage (Memory Eight Mem))) si = 
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r1_32 :: 32 word;
                   op2 = \<langle>7,0\<rangle>(read_mem64 \<alpha> \<sigma> 8 Mem) :: 8 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1_32 := ucast op2 )\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
qed


lemma is_manual_movzx_r32_r8[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_80386 Movzx) (Reg (General ThirtyTwo r1_32)) (Storage (Reg (General Eight r2_8)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movzx_r32_r8[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_80386 Movzx) (Reg (General ThirtyTwo r1_32)) (Storage (Reg (General Eight r2_8)))) si = 
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r1_32 :: 32 word;
                   op2 = \<langle>7,0\<rangle>(regs \<sigma> r2_8) :: 8 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1_32 := ucast op2 )\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
qed


lemma is_manual_movzx_r32_m16[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_80386 Movzx) (Reg (General ThirtyTwo r1_32)) (Storage (Memory Sixteen Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movzx_r32_m16[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_80386 Movzx) (Reg (General ThirtyTwo r1_32)) (Storage (Memory Sixteen Mem))) si = 
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r1_32 :: 32 word;
                   op2 = \<langle>15,0\<rangle>(read_mem64 \<alpha> \<sigma> 16 Mem) :: 16 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1_32 := ucast op2 )\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
qed


lemma is_manual_movzx_r32_r16[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_80386 Movzx) (Reg (General ThirtyTwo r1_32)) (Storage (Reg (General Sixteen r16)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movzx_r32_r16[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_80386 Movzx) (Reg (General ThirtyTwo r1_32)) (Storage (Reg (General Sixteen r16)))) si = 
        (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r1_32 :: 32 word;
                   op2 = \<langle>15,0\<rangle>(regs \<sigma> r16) :: 16 word
            in
             \<sigma>\<lparr>regs := (regs \<sigma>)(r1_32 := ucast op2 )\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
qed



(*---------------------------------------------------proofs on movapd ---------------------------------------*)
lemma is_manual_movapd_xmm_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Movapd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movapd_xmm_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Movapd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r1 :: 64 word;
                   op2 = regs \<sigma> r2 :: 64 word
            in
            if r1 \<noteq> r4 \<and> r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
              \<sigma>\<lparr>regs := (regs \<sigma>)(r3 := op1, r4 := op2)\<rparr>
            else (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Movapd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Reg_sig (SIMD_sig OneHundredTwentyEight))));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; op1_bvf = get_op1_bvf (Binary (IS_SSE2_SIMD Movapd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Movapd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
                       si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Movapd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
          in exec)
          \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    apply (simp_all add: Let'_def simp_rules )
    done
qed

(*---------------------------------------------------proofs on movq ---------------------------------------*)
lemma is_manual_movq_xmm_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_PentiumMMX_MMX Movq) (Reg (General SixtyFour r64)) (Storage (Reg (SIMD OneHundredTwentyEight r3 r4 r1 r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movq_xmm_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_PentiumMMX_MMX Movq) (Reg (General SixtyFour r64)) (Storage (Reg (SIMD OneHundredTwentyEight r3 r4 r1 r2)))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r2 :: 64 word
            in
            \<sigma>\<lparr>regs := (regs \<sigma>)(r64 := op1)\<rparr>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (simp_all add: Let'_def simp_rules )
qed

(*---------------------------------------------------proofs on movsd ---------------------------------------*)
lemma is_manual_movsd_xmm_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Movsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_movsd_xmm_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Movsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r2 :: 64 word
            in
          if r1 \<noteq> r4 \<and> r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
             \<sigma>\<lparr>regs := (regs \<sigma>)(r4 := op1)\<rparr>
          else  (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Movsd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Reg_sig (SIMD_sig OneHundredTwentyEight))));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; op1_bvf = get_op1_bvf  (Binary (IS_SSE2_SIMD Movsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Movsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
                       si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Movsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
qed

(*---------------------------------------------------proofs on pxor ---------------------------------------*)

lemma take_bits_bitXOR_generic[get_semantics_rewriting]:
  fixes a b :: "'a::len0 word"
  assumes "h < LENGTH('a)"
      and "k < h" 
    shows "((\<langle>h,k\<rangle>(a XOR b)) :: 'b::len0 word) = ((\<langle>h,k\<rangle>a) :: 'b::len0 word) XOR \<langle>h,k\<rangle>b"
proof-
  {
    fix n :: nat
    assume "n < LENGTH('b)"
    hence "((\<langle>h,k\<rangle>(a XOR b)) :: 'b::len0 word) !! n = (((\<langle>h,k\<rangle>a) :: 'b::len0 word) XOR \<langle>h,k\<rangle>b) !! n"
      using assms
      apply (subst test_bit_of_take_bits)
      by (auto simp add: test_bit_of_take_bits bitXOR_nth)
  }
  thus ?thesis
    apply (intro word_eqI)
    by (auto simp add: word_size)
qed



lemma xor_shift_and_take_upper[get_semantics_rewriting]:
  fixes a b c d :: "64 word"
  shows "\<langle>127,64\<rangle>(((\<langle>63,0\<rangle>a << 64) OR (\<langle>63,0\<rangle>b :: 1000 word)) XOR (\<langle>63,0\<rangle>c << 64) OR (\<langle>63,0\<rangle>d :: 1000 word)) = (a XOR c)"
proof-
  show ?thesis
    apply (subst take_bits_bitXOR_generic)
    apply (auto)
    apply (subst take_bits_bitOR)
    apply simp
    apply (subst take_bits_bitOR)
     apply simp
    apply (subst take_bits_def)+
    apply (auto)
    by (auto simp add: word_rep_drop shiftl_of_bl)
qed

lemma xor_shift_and_take_lower[get_semantics_rewriting]:
  fixes a b c d :: "64 word"
  shows "\<langle>63,0\<rangle>(((\<langle>63,0\<rangle>a << 64) OR (\<langle>63,0\<rangle>b :: 1000 word)) XOR (\<langle>63,0\<rangle>c << 64) OR (\<langle>63,0\<rangle>d :: 1000 word)) = (b XOR d)"
proof-
  show ?thesis
    apply (subst take_bits_bitXOR_generic)
    apply (auto)
    apply (subst take_bits_bitOR)
    apply simp
    apply (subst take_bits_bitOR)
     apply simp
    apply (subst take_bits_def)+
    apply (auto)
    by (auto simp add: word_rep_drop shiftl_of_bl)
qed

lemma is_manual_pxor_xmm_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)
                                
lemma get_semantics_pxor_xmm_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r3 :: 64 word;
                   op2= regs \<sigma> r4 :: 64 word;
                   op3 = regs \<sigma> r1 :: 64 word;
                   op4 = regs \<sigma> r2 :: 64 word
            in
          if r1 \<noteq> r4 \<and> r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
             \<sigma>\<lparr>regs := (regs \<sigma>)(r3 := op1 XOR op3, r4 := op2 XOR op4 )\<rparr>
          else (let' p = (IMF_PentiumMMX_MMX, IS_PentiumMMX_MMX Pxor,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Reg_sig (SIMD_sig OneHundredTwentyEight))));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; op1_bvf = get_op1_bvf  (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4))
                         (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4))
                         (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
                       si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4))
                         (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
          in exec) 
        \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    apply (auto simp add:simp_rules)
    unfolding bv_cat.simps
    by (auto simp add:simp_rules xor_shift_and_take_upper xor_shift_and_take_lower)
  qed

abbreviation "read_mem_128 \<alpha> \<sigma> s a \<equiv> fst (bv_slice s 0 (bv_read_memory \<alpha> \<sigma> s a))"

lemma is_manual_pxor_xmm_m128[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory OneHundredTwentyEight Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_pxor_xmm_m128[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory OneHundredTwentyEight Mem))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r3 :: 64 word;
                   op2= regs \<sigma> r4 :: 64 word;
                   op3 = \<langle>127,64\<rangle>read_mem_128 \<alpha> \<sigma> 128 Mem :: 64 word;
                   op4 = \<langle>63,0\<rangle>read_mem_128 \<alpha> \<sigma> 128 Mem :: 64 word

            in
          if r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
             \<sigma>\<lparr>regs := (regs \<sigma>)(r3 := (op1 XOR op3),  r4 := (op2 XOR op4))\<rparr>
          else  (let' p = (IMF_PentiumMMX_MMX, IS_PentiumMMX_MMX Pxor,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Memory_sig OneHundredTwentyEight)));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; op1_bvf = get_op1_bvf  (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory OneHundredTwentyEight Mem))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory OneHundredTwentyEight Mem))) si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_PentiumMMX_MMX Pxor) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory OneHundredTwentyEight Mem)))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    apply (auto simp add:simp_rules)
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitXOR_generic)
    apply (auto)
    apply (subst take_bits_bitXOR_generic)
      apply (auto)
    apply (subst take_bits_bitOR)
    apply simp
    apply (subst take_bits_bitOR)
     apply simp
    apply (subst take_bits_def)+
    apply (auto)
    by (auto simp add: word_rep_drop shiftl_of_bl)
  qed

(*---------------------------------------------------proofs on andpd ---------------------------------------*)
lemma is_manual_andpd_xmm_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Andpd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_andpd_xmm_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Andpd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r3 :: 64 word;
                   op2= regs \<sigma> r4 :: 64 word;
                   op3 = regs \<sigma> r1 :: 64 word;
                   op4 = regs \<sigma> r2 :: 64 word
            in
          if r1 \<noteq> r4 \<and> r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
             \<sigma>\<lparr>regs := (regs \<sigma>)(r3 := op1 AND op3, r4 := op2 AND op4 )\<rparr>
          else (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Andpd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Reg_sig (SIMD_sig OneHundredTwentyEight))));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; 
               op1_bvf = get_op1_bvf  (Binary (IS_SSE2_SIMD Andpd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Andpd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
                       si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Andpd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitAND)
    apply simp
    apply (subst take_bits_bitAND)
    apply simp
    unfolding bv_cat.simps
    apply (auto simp add:simp_rules)
    apply (subst take_bits_bitOR)
     apply simp
    apply (subst take_bits_bitOR)
     apply simp
    apply (subst take_bits_bitOR)
     apply simp
    apply (subst take_bits_bitOR)
    apply simp
    apply (subst take_bits_def)+
    apply (auto)
    by (auto simp add: word_rep_drop shiftl_of_bl)
  qed

(*---------------------------------------------------proofs on subsd ---------------------------------------*)
lemma is_manual_subsd_xmm_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_subsd_xmm_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r3 :: 64 word;
                   op2= regs \<sigma> r4 :: 64 word;
                   op3 = regs \<sigma> r1 :: 64 word;
                   op4 = regs \<sigma> r2 :: 64 word
            in
          if r1 \<noteq> r4 \<and> r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
             \<sigma>\<lparr>regs := (regs \<sigma>)( r4 := op2 -\<^sup>f op4 )\<rparr>
          else   (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Subsd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Reg_sig (SIMD_sig OneHundredTwentyEight))));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; 
               op1_bvf = get_op1_bvf (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
                       si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
  qed

lemma is_manual_subsd_xmm_m64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_subsd_xmm_m64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r4 :: 64 word;
                   op2 = read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word

            in
          if r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
           \<sigma>\<lparr>regs := (regs \<sigma>)( r4 := op1 -\<^sup>f op2 )\<rparr>

         else (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Subsd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Memory_sig SixtyFour)));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None;
               op1_bvf = get_op1_bvf (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Subsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem)))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
     apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
  qed

(*---------------------------------------------------proofs on addsd ---------------------------------------*)
lemma is_manual_addsd_xmm_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_addsd_xmm_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r3 :: 64 word;
                   op2= regs \<sigma> r4 :: 64 word;
                   op3 = regs \<sigma> r1 :: 64 word;
                   op4 = regs \<sigma> r2 :: 64 word
            in
          if r1 \<noteq> r4 \<and> r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
             \<sigma>\<lparr>regs := (regs \<sigma>)( r4 := op2 +\<^sup>f op4 )\<rparr>
          else (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Addsd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Reg_sig (SIMD_sig OneHundredTwentyEight))));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; 
               op1_bvf = get_op1_bvf (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
                       si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
    apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
qed

lemma is_manual_addsd_xmm_m64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_addsd_xmm_m64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r4 :: 64 word;
                   op2 = read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word

            in
          if r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
           \<sigma>\<lparr>regs := (regs \<sigma>)( r4 := op1 +\<^sup>f op2 )\<rparr>

         else (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Addsd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Memory_sig SixtyFour)));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; 
               op1_bvf = get_op1_bvf (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Addsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem)))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
     apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
  qed


(*---------------------------------------------------proofs on mulsd ---------------------------------------*)
lemma is_manual_mulsd_xmm_xmm[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mulsd_xmm_xmm[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r3 :: 64 word;
                   op2= regs \<sigma> r4 :: 64 word;
                   op3 = regs \<sigma> r1 :: 64 word;
                   op4 = regs \<sigma> r2 :: 64 word
            in
          if r1 \<noteq> r4 \<and> r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
             \<sigma>\<lparr>regs := (regs \<sigma>)( r4 := op2 *\<^sup>f op4 )\<rparr>
          else 
        (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Mulsd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Reg_sig (SIMD_sig OneHundredTwentyEight))));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; op1_bvf = get_op1_bvf (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2)))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
                       si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Reg (SIMD OneHundredTwentyEight r7 r17 r1 r2))))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)        
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
     apply(rewrite_one_let')+
    by (auto simp add: set_def)
  qed

lemma is_manual_mulsd_xmm_m64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_mulsd_xmm_m64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r4 :: 64 word;
                   op2 = read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word

            in
          if r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
           \<sigma>\<lparr>regs := (regs \<sigma>)( r4 := op1 *\<^sup>f op2 )\<rparr>

         else (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Mulsd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Memory_sig SixtyFour)));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; 
               op1_bvf = get_op1_bvf (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Mulsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem)))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
     apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
  qed

(*---------------------------------------------------proofs on divsd ---------------------------------------*)
lemma is_manual_divsd_xmm_m64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_SSE2_SIMD Divsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_divsd_xmm_m64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_SSE2_SIMD Divsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) si = 
        (\<lambda> \<sigma> . let op1 = regs \<sigma> r4 :: 64 word;
                   op2 = read_mem64 \<alpha> \<sigma> 64 Mem :: 64 word

            in
          if r3 \<noteq> r4 \<and> r5 \<noteq> r3 \<and> r5 \<noteq> r4 \<and> r6 \<noteq> r4 \<and> r6 \<noteq> r3 then
           \<sigma>\<lparr>regs := (regs \<sigma>)( r4 := op1 div\<^sup>f op2 )\<rparr>

         else (let' p = (IMF_SSE2_SIMD, IS_SSE2_SIMD Divsd,
                    Binary_sig (Reg_sig (SIMD_sig OneHundredTwentyEight)) (Storage_sig (Memory_sig SixtyFour)));
               family_list = instr_semantics semantics (fst p); family_list_not_found = family_list = None;
               variant_list = if family_list_not_found then None else the family_list (fst (snd p));
               variant_list_not_found = variant_list = None;
               bv_formula = if variant_list_not_found then None else the variant_list (snd (snd p));
               manual = bv_formula = None; 
               op1_bvf = get_op1_bvf (Binary (IS_SSE2_SIMD Divsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) (the bv_formula);
               exec =
                 if manual
                 then manual_exec_instr \<alpha>
                       (Binary (IS_SSE2_SIMD Divsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem))) si
                 else exec_learned_instr \<alpha> (the bv_formula) op1_bvf
                       (Binary (IS_SSE2_SIMD Divsd) (Reg (SIMD OneHundredTwentyEight r5 r6 r3 r4)) (Storage (Memory SixtyFour Mem)))
          in exec) \<sigma>)"
proof-
  show ?thesis
    apply(rule ext)
    apply(subst get_semantics_def)
    apply(rewrite_one_let')
    defer
    apply simp
    apply(rewrite_one_let')
    apply(rewrite_one_let')
    apply(rewrite_one_let' add:semantics_def)
     apply(rewrite_one_let')+
    by (auto simp add:simp_rules)
  qed

(*---------------------------------------------------proofs on sub ---------------------------------------*)
abbreviation "read_mem \<alpha> \<sigma> s a \<equiv> fst (read_memory \<alpha> \<sigma> s a)"

lemma is_manual_sub_r32_m32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Sub) (Reg (General ThirtyTwo r32)) (Storage (Memory ThirtyTwo a))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_sub_r32_m32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Sub) (Reg (General ThirtyTwo r32)) (Storage (Memory ThirtyTwo a))) si = 
             (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word;
                   op2 = \<langle>31,0\<rangle>(read_mem \<alpha> \<sigma> 32 a) :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32 := ucast (op1 - op2)),
          flags := (flags \<sigma>)
          (flag_pf := parity (op1 - op2),
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
    apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    apply (auto simp add:simp_rules)
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules parity_ucast)
      done
    subgoal for \<sigma>
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 a)) :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>regs \<sigma> r32 - \<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 a)) :: 32 word"]
    by (auto simp add: simp_rules test_bit_of_take_bits )
  done
qed

lemma is_manual_sub_m32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Sub) (Memory ThirtyTwo a) (Storage (Reg (General ThirtyTwo r32)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_sub_m32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Sub) (Memory ThirtyTwo Mem) (Storage (Reg (General ThirtyTwo r32)))) si = 
             (\<lambda> \<sigma> . let a = resolve_address \<alpha> \<sigma> Mem;
                        op1 = \<langle>31,0\<rangle>(read_mem \<alpha> \<sigma> 32 Mem) :: 32 word;
                        op2 = \<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word
               in
        \<sigma>\<lparr>mem := write_blocks [a \<rhd> rev (\<lbrace>3,0\<rbrace> (op1 - op2))] (mem \<sigma>),
          flags := (flags \<sigma>)
          (flag_pf := parity (op1 - op2),
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
proof-
  show ?thesis
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
    apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    apply (auto simp add:simp_rules resolve_address_after_update_flag)
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules parity_ucast)
      done
    subgoal for \<sigma>
      apply (subst add.commute[of "ucast (NOT \<langle>31,0\<rangle>regs \<sigma> r32)"])
      apply (subst sign_sub_bit32)
      by auto
    subgoal for \<sigma>
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r32 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 Mem)) :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>fst (read_memory \<alpha> \<sigma> 32 Mem) - (\<langle>31,0\<rangle>regs \<sigma> r32) :: 32 word"]
    using sign_sub_bit32[where b="regs \<sigma> r32" and a="fst (read_memory \<alpha> \<sigma> 32 Mem)"]
    by (auto simp add: simp_rules test_bit_of_take_bits)
  done
qed

lemma is_manual_sub_r32_r32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Sub) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_sub_r32_r32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Sub) (Reg (General ThirtyTwo r32_1)) (Storage (Reg (General ThirtyTwo r32_2)))) si = 
         (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32_1 := ucast (op1 - op2) :: 64 word),
          flags := (flags \<sigma>)
          (flag_pf := parity (op1 - op2),
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
    apply (intro state_eqI,simp_all)
    apply (auto simp add:simp_rules)
    apply (intro flags_eqI,simp_all)
    subgoal for \<sigma>
      apply (auto simp add:simp_rules parity_ucast)
      done
    subgoal for \<sigma>
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_2 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>regs \<sigma> r32_1 - \<langle>31,0\<rangle>regs \<sigma> r32_2) :: 32 word"]
    by (auto simp add: simp_rules test_bit_of_take_bits )
  done

lemma test_32b_of_32AND1000_word[get_semantics_rewriting]:
  fixes a :: "1000 word"
  shows "(a :: 1000 word) !! 31 = (\<langle>31,0\<rangle>(a :: 1000 word) :: 32 word) !! 31"
  by (simp add: test_bit_of_take_bits)

lemma is_manual_sub_r32_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Sub) (Reg (General ThirtyTwo r32_1)) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)


lemma get_semantics_sub_r32_Imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Sub) (Reg (General ThirtyTwo r32_1)) (Immediate SixtyFour (ImmVal ImmValue))) si = 
         (\<lambda> \<sigma> . let op1 = \<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word;
                   op2 = \<langle>31,0\<rangle>(word_of_int ImmValue :: 64 word) :: 32 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r32_1 := (ucast (op1 - op2 :: 32 word)) :: 64 word),
          flags := (flags \<sigma>)
          (flag_pf := parity (op1 - op2),
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
  subgoal for \<sigma>
    apply (auto simp add:simp_rules)
    done
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    apply (auto simp add: simp_rules parity_ucast)
    done
  subgoal for \<sigma>
    apply (subst test_32b_of_32AND64_word[where ?a="regs \<sigma> r32_1"])
     using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>word_of_int ImmValue :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="\<langle>31,0\<rangle>regs \<sigma> r32_1 :: 32 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(\<langle>31,0\<rangle>regs \<sigma> r32_1 - \<langle>31,0\<rangle>word_of_int ImmValue) :: 32 word"]
    by (auto simp add: simp_rules test_bit_of_take_bits )
  done


lemma test_64b_of_1000AND_take_64_word[get_semantics_rewriting]:
  fixes a :: "1000 word"
  shows "(a :: 1000 word) !! 63 = (\<langle>63,0\<rangle>(a :: 1000 word) :: 64 word) !! 63"
  by (simp add: test_bit_of_take_bits)

lemma is_manual_sub_r64_Imm32[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Sub) (Reg (General SixtyFour r64_1)) (Immediate ImmSize (ImmVal ImmValue))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

 
lemma get_semantics_sub_r64_Imm32[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Sub) (Reg (General SixtyFour r64_1)) (Immediate SixtyFour (ImmVal ImmValue))) si = 
         (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = (word_of_int ImmValue :: 64 word)
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 := (op1 - op2 ) :: 64 word),
          flags := (flags \<sigma>)
          (flag_pf := parity (op1 - op2),
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)

  subgoal for \<sigma>
    apply (auto simp add:simp_rules useless_sextend_hardocded)
    done
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    unfolding bv_slice.simps
    apply (auto simp add:ucast_bitNOT ucast_id)
    done
  subgoal for \<sigma>
    using overflow_sub_bit64[where ?a="regs \<sigma> r64_1" and ?b="word_of_int ImmValue"]
    apply (auto simp add:simp_rules )
    done
  subgoal for \<sigma>
    unfolding bv_slice.simps
    apply (auto simp add: simp_rules parity_ucast)
    done
  subgoal for \<sigma> 
    using sign_sub_bit64[where ?a="regs \<sigma> r64_1" and ?b="word_of_int ImmValue", simplified]
    apply (auto simp add:simp_rules)
    done
  subgoal for \<sigma>
    apply(subst test_64b_of_AND1000_word[symmetric, where ?w="regs \<sigma> r64_1"])
    using sign_sub_bit64[where ?a="regs \<sigma> r64_1" and ?b="word_of_int ImmValue", simplified]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="word_of_int ImmValue :: 64 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="regs \<sigma> r64_1 :: 64 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(regs \<sigma> r64_1 - word_of_int ImmValue) :: 64 word"]
    apply (auto simp add:simp_rules)
    using sub_overflow_flag64_bit[where ?b="word_of_int ImmValue :: 64 word" and ?a="regs \<sigma> r64_1"]
    by (auto simp add: word_msb_sint msb_nth test_bit_of_take_bits)
    done


lemma is_manual_sub_r64_r64[is_manual]:
  shows "is_manual assembly semantics (Binary (IS_8088 Sub) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_sub_r64_r64[presimplify]:
  shows "get_semantics \<alpha> semantics (Binary (IS_8088 Sub) (Reg (General SixtyFour r64_1)) (Storage (Reg (General SixtyFour r64_2)))) si = 
         (\<lambda> \<sigma> . let op1 = regs \<sigma> r64_1 :: 64 word;
                   op2 = regs \<sigma> r64_2 :: 64 word
               in
        \<sigma>\<lparr>regs := (regs \<sigma>)(r64_1 := (op1 - op2 ) :: 64 word),
          flags := (flags \<sigma>)
          (flag_pf := parity (op1 - op2),
           flag_cf := op2 > op1,
           flag_zf := op1 = op2,
           flag_sf := sint (op1 - op2) < 0,
           flag_of := (sint(op2) \<ge> 0 \<and> 0 \<le> sint (op1 - op2) \<and> sint(op1) < 0)
                      \<or>
                      (sint(op2) < 0 \<and> sint (op1  - op2) < 0 \<and> sint(op1) \<ge> 0))\<rparr>)"
  apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let' add: semantics_def)
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')
  apply (rewrite_one_let')+
  apply (intro state_eqI,simp_all)
  subgoal for \<sigma>
    apply (auto simp add:simp_rules )
    done
  apply (intro flags_eqI,simp_all)
  subgoal for \<sigma>
    unfolding bv_slice.simps
    apply (auto simp add:ucast_bitNOT ucast_id)
    done
  subgoal for \<sigma>
    using overflow_sub_bit64[where ?a="regs \<sigma> r64_1" and ?b="regs \<sigma> r64_2"]
    apply (auto simp add:simp_rules )
    done
  subgoal for \<sigma>
    unfolding bv_slice.simps
    apply (auto simp add: simp_rules parity_ucast)
    done
  subgoal for \<sigma> 
    using sign_sub_bit64[where ?a="regs \<sigma> r64_1" and ?b="regs \<sigma> r64_2", simplified]
    apply (auto simp add:simp_rules)
    done
  subgoal for \<sigma>
    apply(subst test_64b_of_AND1000_word[symmetric, where ?w="regs \<sigma> r64_1"])
    using sign_sub_bit64[where ?a="regs \<sigma> r64_1" and ?b="regs \<sigma> r64_2", simplified]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="regs \<sigma> r64_2 :: 64 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="regs \<sigma> r64_1 :: 64 word"]
    using word_msb_sint[symmetric, unfolded msb_nth, where ?w="(regs \<sigma> r64_1 - regs \<sigma> r64_2) :: 64 word"]
    apply (auto simp add:simp_rules)
    using sub_overflow_flag64_bit[where ?b="regs \<sigma> r64_2 :: 64 word" and ?a="regs \<sigma> r64_1"]
    by (auto simp add: word_msb_sint msb_nth test_bit_of_take_bits)
    done




(*---------------------------------------------------proofs on cdq  ---------------------------------------*)
lemma is_manual_cdq[is_manual]:
  shows "is_manual assembly semantics (Nullary (IS_80386 Cdq)) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cdq[presimplify]:
  shows "get_semantics \<alpha> semantics (Nullary (IS_80386 Cdq)) si = 
             (\<lambda> \<sigma> . let op1 = EAX \<sigma>
               in
                \<sigma>\<lparr>regs := (regs \<sigma>)(rdx := ucast (if sint op1 \<ge> 0 then 0 else -1 :: 32 word)) \<rparr> )"
   apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
   apply (rewrite_one_let' add: semantics_def)
   apply (rewrite_one_let')+
   apply (intro state_eqI,simp_all)
  subgoal premises prems for \<sigma>
  proof(cases "(\<langle>31,0\<rangle>regs \<sigma> rax :: 1000 word) !! 31")
    case True
    hence "EAX \<sigma> !! 31"
      by (auto simp add: test_bit_of_take_bits)      
    hence False
      using word_msb_sint[of "EAX \<sigma>"] prems
      by (auto simp add: msb_nth)
    thus ?thesis
      by simp
  next
    case False
    have "\<langle>31,32\<rangle>regs \<sigma> rax = (0::64 word)"
      apply (intro word_eqI)
      by (auto simp add: word_size test_bit_of_take_bits)
    thus ?thesis
      using False
      by (auto simp add: simp_rules bv_slice.simps sextend.simps bv_cat'_def)[1]
  qed
  apply (rewrite_one_let') 
   apply (rewrite_one_let' add: semantics_def)
   apply (rewrite_one_let')+
   apply (intro state_eqI,simp_all)
  subgoal premises prems for \<sigma>
  proof(cases "(\<langle>31,0\<rangle>regs \<sigma> rax :: 1000 word) !! 31")
    case True
    have 1: "\<And> a b . a = b \<Longrightarrow> (regs \<sigma>)(rdx := a) = (regs \<sigma>)(rdx := b)"
      by auto
    thus ?thesis
      using True
      apply (auto simp add: simp_rules bv_slice.simps sextend.simps bv_cat'_def)[1]
      apply (rule 1)
      apply (intro word_eqI)
      subgoal for n
      apply (cases"n=0", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)
      apply (cases"n=1", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=2", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=3", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=4", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=5", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=6", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=7", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=8", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=9", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=10", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=11", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=12", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=13", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=14", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=15", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=16", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=17", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=18", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=19", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=20", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=21", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=21", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=21", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=22", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=23", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=24", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=25", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=26", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=27", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=28", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=29", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=30", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=31", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
        apply unat_arith
      apply (cases"n=0", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)
      apply (cases"n=1", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=2", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=3", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=4", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=5", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=6", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=7", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=8", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=9", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=10", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=11", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=12", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=13", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=14", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=15", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=16", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=17", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=18", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=19", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=20", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=21", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=21", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=21", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=22", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=23", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=24", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=25", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=26", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=27", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=28", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=29", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=30", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
      apply (cases"n=31", auto simp add: word_size test_bit_of_take_bits word_ao_nth nth_ucast)  
        apply unat_arith
        done
      done
  next
    case False
    hence "\<not>EAX \<sigma> !! 31"
      by (auto simp add: test_bit_of_take_bits)      
    hence False
      using word_msb_sint[of "EAX \<sigma>"] prems
      by (auto simp add: msb_nth)
    thus ?thesis
      by simp
  qed
  done

(*---------------------------------------------------proofs on cdqe  ---------------------------------------*)
lemma is_manual_cdqe[is_manual]:
  shows "is_manual assembly semantics (Nullary (IS_X86_64 Cdqe)) = False"
  by (auto simp add: is_manual_def Let'_def simp_rules unfold_semantics)

lemma get_semantics_cdqe[presimplify]:
  shows "get_semantics \<alpha> semantics (Nullary (IS_X86_64 Cdqe)) si = 
             (\<lambda> \<sigma> . let op1 = EAX \<sigma>
               in
                \<sigma>\<lparr>regs := (regs \<sigma>)(rax := sextend (ucast op1) 32 64) \<rparr> )"
   apply (rule ext)
  apply (subst get_semantics_def)
  apply (rewrite_one_let') 
   apply (rewrite_one_let' add: semantics_def)
   apply (rewrite_one_let')+
   apply (intro state_eqI,simp_all add: set_def)
      apply (auto simp add: simp_rules sextend.simps)[1]
  done



thm is_manual
thm presimplify

end
end
