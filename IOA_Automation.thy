theory IOA_Automation
imports IOA  "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

context IOA begin

named_theorems invs
  -- "named theorem for use by the tactics below"
named_theorems inv_proofs_defs
  -- "definitions to unfold"

lemma reach_and_inv_imp_p:"\<lbrakk>reachable ioa s; invariant ioa i\<rbrakk> \<Longrightarrow> i s"
by (auto simp add:invariant_def)

method rm_reachable = (match premises in R[thin]:"reachable ?ioa ?s" \<Rightarrow> \<open>-\<close>)

method instantiate_invs declares invs =
  (match premises in I[thin]:"invariant ?ioa ?inv" and R:"reachable ?ioa ?s" \<Rightarrow> \<open>
    print_fact I, insert reach_and_inv_imp_p[OF R I]\<close>)+

method instantiate_invs_2 declares invs = (
  (* Deduce that all invariants hold in s *)
  ( insert invs,
    instantiate_invs )?,
  (* Deduce that all invariants hold in t (first deduce that t is reachable) *)
  match premises in R[thin]:"reachable ?ioa ?s" and T:"?s \<midarrow>?a\<midarrow>?ioa\<longrightarrow> ?t" \<Rightarrow> 
    \<open>insert reachable_n[OF R T]\<close>,
  ( insert invs,
    instantiate_invs )?,
  (* Get rid of the reachability assumption *)
  rm_reachable )

method try_solve_ind_case uses case_thm declares invs inv_proofs_defs  = (
  instantiate_invs_2,
  (* Now do case analysis on the transition *)
  ( (match premises in T:"?s \<midarrow>?a\<midarrow>?ioa\<longrightarrow> ?t"  \<Rightarrow> 
    \<open>simp add:inv_proofs_defs, induct rule:case_thm\<close>) 
    | (print_term "''case analysis failed''", fail) );
  (* Finally try simp *)
  (simp add:inv_proofs_defs ; fail) )

method try_solve_ind_case_2 = (
  instantiate_invs_2,
  (* Now do case analysis on the transition *)
  ( (match premises in T:"?s \<midarrow>a\<midarrow>?ioa\<longrightarrow> ?t" for a \<Rightarrow> \<open>case_tac a\<close>) | (print_term "''case analysis failed''", fail) );
  (* Finally try simp *)
  (simp add:inv_proofs_defs ; fail) )

method try_solve_inv2 uses case_thm declares invs inv_proofs_defs = (
  rule invariantI,
  ( ( force simp add:inv_proofs_defs, 
      (try_solve_ind_case case_thm:case_thm| (instantiate_invs_2, print_term "''inductive case failed''")))
    | ( print_term "''base case failed''", (auto simp add:inv_proofs_defs)[1]) ) )

end 

end