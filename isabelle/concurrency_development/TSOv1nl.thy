theory TSOv1nl

  imports Main "HOL-Word.WordBitwise" TNIv1nl

begin

typedecl reg
typedecl flag

(* These are local write buffers for each concurrent thread *)

(* A word of large enough length to store the largest possible memory write by a given instruction (512-bit) via AVX-512 *)
(* The nat is the size of the memory item *)
type_synonym memory = "(512 word \<times> nat)"  
type_synonym addr = "64 word"
type_synonym memory_region = "(64 word \<times> nat)" 
type_synonym addressable_mem = "addr \<Rightarrow> 8 word"

datatype ('t) action =  Local_Instr 't 

record memory_update = 
  address :: "64 word" (* The address in memory to update *)
  mem :: "memory" 

fun region_of_update :: " memory_update \<Rightarrow> memory_region"
  where "region_of_update \<lparr> address=a , mem = m \<rparr> = (a,snd m)"

type_synonym store = "memory_update list"
definition emptyStore :: "store" where "emptyStore \<equiv> []"

(* Returns true if the most recent memory update matches the memory region specified *)
fun lastitemcheckStore :: "memory_region \<Rightarrow> store \<Rightarrow> bool" 
  where "lastitemcheckStore _ [] = False" |
        "lastitemcheckStore (a1,s1) ((\<lparr>address=a2, mem=(w2,s2)\<rparr>)#[]) = (a1=a2\<and>s1=s2) " |
        "lastitemcheckStore mu (_#aa) = lastitemcheckStore mu aa" 

(* Local thread *)
record ('loc) thread_state =
  regs  :: "reg \<Rightarrow> 64 word"
  flags :: "flag \<Rightarrow> bool"
  loc   :: 'loc (* Like the program counter *)
  write_buffer  :: "store"  

record ('t, 'loc) global_state =
  tstate :: "'t \<Rightarrow> 'loc thread_state"
  mem :: "addressable_mem"
  lock :: "'t option"
 
(*
  'T = thread
  'I = instruction
  loc = location
*)

locale x86TSO = fixes
    exec_instr :: "'I \<Rightarrow> 'loc thread_state \<Rightarrow> 'loc thread_state"
and fetch :: "'loc thread_state \<Rightarrow> 'I"
begin

fun update_thread_state :: "'t \<Rightarrow> 'loc thread_state \<Rightarrow> ('t, 'loc) global_state \<Rightarrow> ('t, 'loc) global_state"
  where "update_thread_state t newthreadstate \<lparr> tstate = ts, mem = m, lock = l \<rparr> =  \<lparr> tstate = ts(t := newthreadstate), mem = m, lock = l \<rparr>"

fun x86_tso_thread :: "('t) action \<Rightarrow> 't"
  where 
        "x86_tso_thread (Local_Instr t) = t" 

fun x86_tso_view :: "('t, 'loc) global_state \<Rightarrow> 't \<Rightarrow> 'loc thread_state"
  where "x86_tso_view gs t = ((tstate gs) t)"

fun gstep_deterministic :: "('t, 'loc) global_state  \<Rightarrow> ('t) action \<Rightarrow> ('t, 'loc) global_state"
  where
        "gstep_deterministic gs (Local_Instr t) = (let 
                                        p = ((tstate gs) t) ;                             
                                        i = fetch p ;                                      
                                        t2 = exec_instr i p                                
                                      in (update_thread_state t t2 gs))" 
     

 lemma update_thread_non_interferering:
   assumes "t \<noteq> u"
   shows   "tstate (update_thread_state t new_t gs) u = tstate gs u "
 proof (cases gs)
   case (fields tstate mem lock)
   thus ?thesis
     using assms
     by auto
 qed

lemma step_consistency_local_instr_internal_2:
  shows "(tstate (update_thread_state x x_new s) x) = x_new"
proof (cases "s")
  case (fields tstate mem lock)
  then show ?thesis by auto
qed

lemma step_consistency_local_instr_internal:
    assumes "sc = x"
    assumes "a = Local_Instr x"
    assumes "s \<noteq> t"
    assumes "tstate s x = tstate t x"
    shows "tstate (update_thread_state x (exec_instr (fetch (tstate t x)) (tstate t x)) s) x =
           tstate (update_thread_state x (exec_instr (fetch (tstate t x)) (tstate t x)) t) x"
  using assms
  by (simp add:step_consistency_local_instr_internal_2)

lemma step_consistency_local_instr:
    assumes "a = Local_Instr x"
    assumes "s \<noteq> t"
    assumes "tstate s sc = tstate t sc"
    shows "    tstate (update_thread_state x (exec_instr (fetch (tstate s x)) (tstate s x)) s) sc =
    tstate (update_thread_state x (exec_instr (fetch (tstate t x)) (tstate t x)) t) sc"
 proof (cases "sc=x")
   case True
   then show ?thesis 
     using assms
     by (auto simp add: Let_def update_thread_non_interferering step_consistency_local_instr_internal) 
 next
   case False
   then show ?thesis 
    using assms
    by (auto simp add: Let_def update_thread_non_interferering) 
 qed

interpretation tso : thread_noninteference gstep_deterministic x86_tso_view x86_tso_thread
proof(unfold_locales)
  show "\<And>a u s. x86_tso_thread a \<noteq> u \<longrightarrow> x86_tso_view s u = x86_tso_view (gstep_deterministic s a) u"
  proof-
    fix a u s    
    show "x86_tso_thread a \<noteq> u \<longrightarrow> x86_tso_view s u = x86_tso_view (gstep_deterministic s a) u"
    proof(cases a)
      case (Local_Instr x)
      thus ?thesis  
        by (auto simp add: Let_def update_thread_non_interferering) 
    qed
  qed
  show "\<And>s sc t a. x86_tso_view s sc = x86_tso_view t sc \<longrightarrow> x86_tso_view (gstep_deterministic s a) sc = x86_tso_view (gstep_deterministic t a) sc"
  proof-
    fix s sc t a
    show "x86_tso_view s sc = x86_tso_view t sc \<longrightarrow> x86_tso_view (gstep_deterministic s a) sc = x86_tso_view (gstep_deterministic t a) sc"
    proof(cases "s=t")
      case True
      then show ?thesis by auto
    next
      case False
      then show ?thesis 
          proof(cases a)
            case (Local_Instr x)
            then show ?thesis
              using False
              apply (auto simp add: Let_def)
              by (simp only:step_consistency_local_instr)
        qed
    qed
  qed
qed


end

end