theory x86TSO_view_partitioned_deterministic1

  imports Main "HOL-Word.WordBitwise"

begin


locale view_partitioning = fixes
    step :: " 'S \<Rightarrow> 'A \<Rightarrow> 'S"
and view :: " 'S \<Rightarrow> 'T \<Rightarrow> 'V"
and dom :: "'A \<Rightarrow> 'T" (* For a given action, which thread does it below too?*)

assumes locally_respects: "(dom a) \<noteq> u  \<longrightarrow> (view s u) = (view (step s a) u)" (* Locally Respects *)
assumes step_consistency:"((view s sc) = (view t sc))  \<longrightarrow> ((view (step s a) sc) = (view (step t a) sc))" (* Step Consistency *)

begin
    
fun purge :: " 'A list \<Rightarrow> 'T \<Rightarrow>  'A list"
  where "purge [] d = []" |
        "purge (a#aa) d = (case (dom a = d) of 
                              True \<Rightarrow> (a # purge aa d) | 
                              False \<Rightarrow> (purge aa d))" 

fun run :: "'S \<Rightarrow> 'A list \<Rightarrow> 'S"
  where "run s [] = s" |
        "run s (a#aa) = run (step s a) aa"

lemma view_partitioned:
  assumes " view s sc = view t sc"
  shows "((view (run s \<alpha>) sc) = (view (run t (purge \<alpha> sc)) sc))"
using assms
proof (induct \<alpha> arbitrary: s t)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a \<alpha>)
  then show 
?case 
    proof (cases "dom a = sc")
      case True
      then show ?thesis 
        using assms Cons step_consistency[where s=s and t=t and a=a and sc=sc]
        by (simp)
      next
      case False
      then show ?thesis 
        using Cons locally_respects[where s=s and a=a and u=sc]
        by (simp) 
    qed
  qed                    
end

typedecl reg
typedecl flag

(* These are local write buffers for each concurrent thread *)

(* A word of large enough length to store the largest possible memory write by a given instruction (512-bit) via AVX-512 *)
(* The nat is the size of the memory item *)
type_synonym memory = "(512 word \<times> nat)"  
type_synonym addr = "64 word"
type_synonym memory_region = "(64 word \<times> nat)" 
type_synonym addressable_mem = "addr \<Rightarrow> 8 word"

datatype ('t) action = Write_Instr 't | Read_Instr 't | Local_Instr 't | Commit 't

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
(* and get_store :: "'I \<Rightarrow> store list" *)
and global_write_mem :: "memory_update \<Rightarrow> ('t, 'loc) global_state \<Rightarrow> ('t, 'loc) global_state"
and local_write_mem :: "memory_update \<Rightarrow>'loc thread_state \<Rightarrow> 'loc thread_state"
and local_read_mem :: "memory_region \<Rightarrow> store \<Rightarrow> addressable_mem \<Rightarrow> memory" (*Reads local write buffer first (only last item) then global memory to support condition #2*)
and region_in_buffer :: " memory_region \<Rightarrow> store \<Rightarrow> bool " (* Should be undefined if the region is None. *)
and write_region :: "'I \<Rightarrow> memory_region option"
and read_region :: "'I \<Rightarrow> memory_region option"
begin

definition does_read :: "'I \<Rightarrow> bool"
  where "does_read i \<equiv> \<not>((read_region i)= None)"
definition does_write :: "'I \<Rightarrow> bool"
  where "does_write i \<equiv> \<not>((write_region i)= None)"

fun pop_thread_write_buffer :: "'loc thread_state \<Rightarrow> ( 'loc thread_state \<times> memory_update)  "
  where "pop_thread_write_buffer \<lparr> regs = rs, flags = fs, loc = l, write_buffer = mu#stores\<rparr> = (\<lparr> regs = rs, flags = fs, loc = l, write_buffer = stores\<rparr>, mu )" |
        "pop_thread_write_buffer \<lparr> regs = rs, flags = fs, loc = l, write_buffer = []\<rparr> = undefined"

fun pop_buffer :: "'t \<Rightarrow> ('t, 'loc) global_state \<Rightarrow> ('t, 'loc) global_state"
  where "pop_buffer t \<lparr> tstate = ts, mem = m, lock = l \<rparr> =  \<lparr> tstate = ts(t := fst (pop_thread_write_buffer (ts t))), mem = m, lock = l \<rparr>"

fun update_thread_state :: "'t \<Rightarrow> 'loc thread_state \<Rightarrow> ('t, 'loc) global_state \<Rightarrow> ('t, 'loc) global_state"
  where "update_thread_state t newthreadstate \<lparr> tstate = ts, mem = m, lock = l \<rparr> =  \<lparr> tstate = ts(t := newthreadstate), mem = m, lock = l \<rparr>"

fun blocked :: "'t \<Rightarrow> ('t, 'loc) global_state \<Rightarrow> bool"
  where "blocked t \<lparr> tstate = ts, mem = m, lock = l \<rparr> = (\<exists> t' . l = Some t' \<and> t \<noteq> t')"

fun x86_tso_dom :: "('t) action \<Rightarrow> 't"
  where "x86_tso_dom (Write_Instr t) = t" | 
        "x86_tso_dom (Read_Instr t) = t" | 
        "x86_tso_dom (Local_Instr t) = t" | 
        "x86_tso_dom (Commit t) = t"  

fun x86_tso_view :: "('t, 'loc) global_state \<Rightarrow> 't \<Rightarrow> 'loc thread_state"
  where "x86_tso_view gs t = ((tstate gs) t)"

fun gstep_deterministic :: "('t, 'loc) global_state  \<Rightarrow> ('t) action \<Rightarrow> ('t, 'loc) global_state"
  where "gstep_deterministic gs (Write_Instr t) =  (let 
                                        p = ((tstate gs) t) ;                               \<comment> \<open>Thread state for an unquantified thread t\<close>  
                                        i = fetch p ;                                       \<comment> \<open>Next Instruction i\<close>
                                        t2 = exec_instr i p                                     \<comment> \<open> Execute instruction on local thread state\<close>
                                      in (update_thread_state t t2 gs))" |
        "gstep_deterministic gs (Read_Instr t) = 
              (let block = blocked t gs;
                   p = ((tstate gs) t) ;                               \<comment> \<open>Thread state for an unquantified thread t\<close>  
                   i = fetch p;                                  \<comment> \<open>Next Instruction i\<close>
                   r = (read_region i)                             \<comment> \<open>The memory region that the next instruction reads. By definition not None as it's a read instr.\<close>
               in (case (block,r) of (False, Some (r)) \<Rightarrow> 
                    (let rib = region_in_buffer r (write_buffer p);
                         lics = lastitemcheckStore r (write_buffer p)
                     in (case (rib,lics) of (False,_)   \<Rightarrow> (update_thread_state t (exec_instr i p) gs) |
                                            (True,True) \<Rightarrow> (update_thread_state t (exec_instr i p) gs) 
                        ) 
                    )
                  )
              )" |
        "gstep_deterministic gs (Local_Instr t) = (let 
                                        p = ((tstate gs) t) ;                               \<comment> \<open>Thread state for an unquantified thread t\<close>  
                                        i = fetch p ;                                       \<comment> \<open>Next Instruction i\<close>
                                        t2 = exec_instr i p                                 \<comment> \<open> Execute instruction on local thread state\<close>
                                      in (update_thread_state t t2 gs))" |
        "gstep_deterministic gs (Commit t) = 
              (let block = blocked t gs;
                   p = ((tstate gs) t) ;                         \<comment> \<open>Thread state for an unquantified thread t\<close>  
                   (t2,mu) = pop_thread_write_buffer p
               in (case block of (False) \<Rightarrow> 
                   (update_thread_state t t2 (global_write_mem mu gs)) 
                  )
              )"

fun tso_valid_action :: "('t, 'loc) global_state \<Rightarrow> ('t) action \<Rightarrow> bool"
  where "tso_valid_action gs a = ((gstep_deterministic gs a)\<noteq>undefined)"

fun possible_actions_thread :: " 't \<Rightarrow> ('t) action set"
  where "possible_actions_thread t = {(Write_Instr t),(Read_Instr t),(Local_Instr t),(Commit t)}"

definition possible_actions :: " ('t) action set"
  where "possible_actions \<equiv> {a . \<exists> t . a \<in> {(Write_Instr t),(Read_Instr t),(Local_Instr t),(Commit t)}}"

fun tso_valid_actions :: "('t, 'loc) global_state \<Rightarrow> ('t) action set"
  where "tso_valid_actions gs =  Set.filter (\<lambda> a. tso_valid_action gs a) possible_actions"

inductive gstep_nondeterministic :: "('t,'loc) global_state  \<Rightarrow> ('t,'loc) global_state \<Rightarrow> bool"
  where
    " a \<in> (tso_valid_actions gs) \<Longrightarrow> gs' = (gstep_deterministic gs a) \<Longrightarrow> gstep_nondeterministic gs gs"

(*
interpretation int : view_partitioning gstep_deterministic x86_tso_view x86_tso_dom
proof 
 
*)

(* OLD VERSION *)

(*

inductive gstep :: "('t,'loc) global_state \<Rightarrow> ('t,'loc) global_state \<Rightarrow> bool"
  where
(*\<forall> r \<in> R . \<not>(region_in_buffer r (write_buffer p)) \<Longrightarrow> \<comment> \<open>For all memory locations read, they aren't in the write buffer\<close>*)
(* Condition 1: Reading from Memory *)

    " p = ((tstate gs) t) \<Longrightarrow>                               \<comment> \<open>Thread state for an unquantified thread t\<close>  
      i = fetch p \<Longrightarrow>                                       \<comment> \<open>Next Instruction i\<close>
      Some r = (read_region i) \<Longrightarrow>                            \<comment> \<open>The memory region that the next instruction reads\<close>
      does_read i \<Longrightarrow> \<not>(does_write i) \<Longrightarrow> \<not>blocked t gs \<Longrightarrow> \<comment> \<open>Reads, Doesn't write, and isn't blocked\<close>
      \<not>(region_in_buffer r (write_buffer p)) \<Longrightarrow>            \<comment> \<open>Region isn't in the write buffer\<close>
      t2 = step i p \<Longrightarrow>                                     \<comment> \<open> Execute instruction on local thread state\<close>
      gs' = (update_thread_state t t2 gs) \<Longrightarrow>               \<comment> \<open>Update global state with new thread state\<close>
      gstep gs gs'"                                         \<comment> \<open>Induction Step over global state\<close>
  |
(* Condition 2: Reading from Memory #2 --Peek last write *)
    " p = ((tstate gs) t) \<Longrightarrow>                               \<comment> \<open>Thread state for an unquantified thread t\<close>  
      i = fetch p \<Longrightarrow>                                       \<comment> \<open>Next Instruction i\<close>
      Some r = (read_region i) \<Longrightarrow>                            \<comment> \<open>The memory region that the next instruction reads\<close>
      does_read i \<Longrightarrow> \<not>(does_write i) \<Longrightarrow> \<not>blocked t gs \<Longrightarrow> \<comment> \<open>Reads, Doesn't write, and isn't blocked\<close>
      lastitemcheckStore r (write_buffer p) \<Longrightarrow>             \<comment> \<open>This last item in the write buffer is the read of the current instruction \<close>
      t2 = step i p \<Longrightarrow>                                     \<comment> \<open> Execute instruction on local thread state\<close>
      gs' = (update_thread_state t t2 gs) \<Longrightarrow>               \<comment> \<open>Update global state with new thread state\<close>
      gstep gs gs'"                                         \<comment> \<open>Induction Step over global state\<close>
  |
(* Condition 3: Writing to Memory *)
    " p = ((tstate gs) t) \<Longrightarrow>                               \<comment> \<open>Thread state for an unquantified thread t\<close>  
      i = fetch p \<Longrightarrow>                                       \<comment> \<open>Next Instruction i\<close>
      \<not>(does_read i) \<Longrightarrow> does_write i \<Longrightarrow>                   \<comment> \<open>Writes, Doesn't read\<close>
      t2 = step i p \<Longrightarrow>                                     \<comment> \<open> Execute instruction on local thread state\<close>
      gs' = (update_thread_state t t2 gs) \<Longrightarrow>               \<comment> \<open>Update global state with new thread state\<close>
      gstep gs gs'"                                         \<comment> \<open>Induction Step over global state\<close>
  |
(* Condition 4: Silent global commit, in the presence on not being blocked *)
    " p = ((tstate gs) t) \<Longrightarrow>                               \<comment> \<open>Thread state for an unquantified thread t\<close>  
      write_buffer p = (mu # stores) \<Longrightarrow>                    \<comment> \<open>There is at least 1 item on the write buffer, mu\<close>
      \<not>blocked t gs \<Longrightarrow>                                     \<comment> \<open>Thread isn't blocked\<close>
      gs' = global_write_mem mu gs \<Longrightarrow>                      \<comment> \<open>Update global state with committed write\<close>
      gs'' = (pop_buffer t gs') \<Longrightarrow>                         \<comment> \<open>Update global state with popped write buffer\<close>
      gstep gs gs''" 
  |
(* Implicit Condition 1: Local threads can free-wheel if not using memory *)
    "i = fetch (tstate gs t) \<Longrightarrow> \<not>(does_write i) \<Longrightarrow> \<not>(does_read i) \<Longrightarrow> t2 = step i (tstate gs t) \<Longrightarrow> gstep gs (update_thread_state t t2 gs)"
*)


end

end