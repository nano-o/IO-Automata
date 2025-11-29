theory IOA_Automation
imports IOA "HOL-Eisbach.Eisbach_Tools"
begin

named_theorems invs
  \<comment> \<open>named theorem for use by the tactics below\<close>
named_theorems inv_proofs_defs
  \<comment> \<open>definitions to unfold\<close>

lemma reach_and_inv_imp_p:"\<lbrakk>reachable ioa s; invariant ioa i\<rbrakk> \<Longrightarrow> i s"
by (auto simp add:invariant_def)

method rm_reachable = (match premises in R[thin]:"reachable ?ioa ?s" \<Rightarrow> succeed)+

method instantiate_invs declares invs =
  insert invs,
  ((match premises in I[thin]:"invariant ?ioa ?inv" and R[thin]:"reachable ?ioa ?s" \<Rightarrow> \<open>insert reach_and_inv_imp_p[OF R I]\<close>)+)?

\<comment> \<open>Case split on the action type, producing one subgoal per action constructor.
   Tries to solve each subgoal with simp, leaving unsolved ones for interactive proof.\<close>
method prove_inductive_case declares inv_proofs_defs = (
  (* Match the action variable and do case analysis *)
  match premises in T:"(?s, a, ?t) \<in> ?trans" for a \<Rightarrow> \<open>cases a\<close>;
  (* Try to solve each case *)
  (simp add: inv_proofs_defs split: if_splits)?)

thm ioa.simps

method prove_invariant declares inv_proofs_defs = (
    rule invariantI; (
      \<comment> \<open>Base case: goal has start state premise\<close>
        (match premises in prem:"?s \<in> ioa.start ?ioa" \<Rightarrow>
          \<open>insert prem, auto simp add:inv_proofs_defs ioa.defs\<close>)
      | (match premises in prem:"?s \<midarrow>a\<midarrow>?A\<longrightarrow> ?t" for a \<Rightarrow>
          \<open>cases a; simp add:inv_proofs_defs split: if_splits\<close>)))

\<comment> \<open>Try multiple provers on each subgoal. Order: fast methods first.\<close>
method auto_finish = 
  (blast | meson | fastforce | force | auto | metis)+

end 
