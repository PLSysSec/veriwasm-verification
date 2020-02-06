theory Calls
  imports "../x86-64_parser/Leviathan_Setup"
          "Det_Step"
begin

context execution_context
begin
text "To call a concrete function on a concrete state."
definition call\<^sub>c :: "(state \<Rightarrow> state) \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  where "call\<^sub>c f s s' \<equiv> s' = (let s'' = f s in s''\<lparr>regs := (regs s'')(rip := get_rip s + 5)\<rparr>)"

text "To call an abstract function on an abstract state"
definition abstract\<^sub>0 :: "(state \<Rightarrow> '\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> _ \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> bool"
  where "abstract\<^sub>0 S f \<sigma> \<sigma>' \<equiv> \<exists> s s' . call\<^sub>c f s s' \<and> ((), \<L> S s') = \<sigma>' \<and> ((), \<L> S s) = \<sigma>"

lemma abstract_call\<^sub>0:
  shows "call\<^sub>c f s s' \<Longrightarrow> abstract\<^sub>0 S f ((), \<L> S s) ((), \<L> S s')"
  by (auto simp add: call\<^sub>c_def Let_def abstract\<^sub>0_def)

definition abstract\<^sub>1\<^sub>_\<^sub>3\<^sub>2 :: "(state \<Rightarrow> '\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> _ \<Rightarrow> 32 word \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> bool"
  where "abstract\<^sub>1\<^sub>_\<^sub>3\<^sub>2 S f p\<^sub>0 \<sigma> \<sigma>' \<equiv> \<exists> s s' . EDI s = p\<^sub>0 \<and> call\<^sub>c f s s' \<and> ((), \<L> S s') = \<sigma>' \<and> ((), \<L> S s) = \<sigma>"

lemma abstract_call\<^sub>1\<^sub>_\<^sub>3\<^sub>2:
  shows "EDI s = p\<^sub>0 \<Longrightarrow> call\<^sub>c f s s' \<Longrightarrow> abstract\<^sub>1\<^sub>_\<^sub>3\<^sub>2 S f p\<^sub>0 ((), \<L> S s) ((), \<L> S s')"
  by (auto simp add: call\<^sub>c_def Let_def abstract\<^sub>1\<^sub>_\<^sub>3\<^sub>2_def)

definition abstract\<^sub>1\<^sub>_\<^sub>6\<^sub>4 :: "(state \<Rightarrow> '\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> _ \<Rightarrow> 64 word \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> bool"
  where "abstract\<^sub>1\<^sub>_\<^sub>6\<^sub>4 S f p\<^sub>0 \<sigma> \<sigma>' \<equiv> \<exists> s s' . RDI s = p\<^sub>0 \<and> call\<^sub>c f s s' \<and> ((), \<L> S s') = \<sigma>' \<and> ((), \<L> S s) = \<sigma>"

lemma abstract_call\<^sub>1\<^sub>_\<^sub>6\<^sub>4:
  shows "RDI s = p\<^sub>0 \<Longrightarrow> call\<^sub>c f s s' \<Longrightarrow> abstract\<^sub>1\<^sub>_\<^sub>6\<^sub>4 S f p\<^sub>0 ((), \<L> S s) ((), \<L> S s')"
  by (auto simp add: call\<^sub>c_def Let_def abstract\<^sub>1\<^sub>_\<^sub>6\<^sub>4_def)

definition abstract\<^sub>2\<^sub>_\<^sub>6\<^sub>4\<^sub>_\<^sub>3\<^sub>2 :: "(state \<Rightarrow> '\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> bool"
  where "abstract\<^sub>2\<^sub>_\<^sub>6\<^sub>4\<^sub>_\<^sub>3\<^sub>2 S f p\<^sub>0 p\<^sub>1 \<sigma> \<sigma>' \<equiv> \<exists> s s' . RDI s = p\<^sub>0 \<and> ESI s = p\<^sub>1 \<and> call\<^sub>c f s s' \<and> ((), \<L> S s') = \<sigma>' \<and> ((), \<L> S s) = \<sigma>"

lemma abstract_call\<^sub>2\<^sub>_\<^sub>6\<^sub>4\<^sub>_\<^sub>3\<^sub>2:
  shows "RDI s = p\<^sub>0 \<Longrightarrow> ESI s = p\<^sub>1 \<Longrightarrow> call\<^sub>c f s s' \<Longrightarrow> abstract\<^sub>2\<^sub>_\<^sub>6\<^sub>4\<^sub>_\<^sub>3\<^sub>2 S f p\<^sub>0 p\<^sub>1 ((), \<L> S s) ((), \<L> S s')"
  by (auto simp add: call\<^sub>c_def Let_def abstract\<^sub>2\<^sub>_\<^sub>6\<^sub>4\<^sub>_\<^sub>3\<^sub>2_def)

definition abstract\<^sub>2\<^sub>_\<^sub>3\<^sub>2_\<^sub>3\<^sub>2 :: "(state \<Rightarrow> '\<sigma>\<^sub>C \<times> '\<sigma>\<^sub>C\<^sub>C) \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> unit \<times> '\<sigma>\<^sub>C \<Rightarrow> bool"
  where "abstract\<^sub>2\<^sub>_\<^sub>3\<^sub>2_\<^sub>3\<^sub>2 S f p\<^sub>0 p\<^sub>1 \<sigma> \<sigma>' \<equiv> \<exists> s s' . EDI s = p\<^sub>0 \<and> ESI s = p\<^sub>1 \<and> call\<^sub>c f s s' \<and> ((), \<L> S s') = \<sigma>' \<and> ((), \<L> S s) = \<sigma>"

lemma abstract_call\<^sub>2\<^sub>_\<^sub>3\<^sub>2\<^sub>_\<^sub>3\<^sub>2:
  shows "EDI s = p\<^sub>0 \<Longrightarrow> ESI s = p\<^sub>1 \<Longrightarrow> call\<^sub>c f s s' \<Longrightarrow> abstract\<^sub>2\<^sub>_\<^sub>3\<^sub>2_\<^sub>3\<^sub>2 S f p\<^sub>0 p\<^sub>1 ((), \<L> S s) ((), \<L> S s')"
  by (auto simp add: call\<^sub>c_def Let_def abstract\<^sub>2\<^sub>_\<^sub>3\<^sub>2_\<^sub>3\<^sub>2_def)

end
end