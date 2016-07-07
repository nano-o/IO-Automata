section {* History Variables *}

theory History
imports Simulations IOA_Automation
begin

text {*
The concept of unfolding of an IOA is taken from Lynch and Vaandrager's paper: "Forward
  and Backward Simulations Part 1: Untimed Systems".
*}
         
context IOA begin

context begin

private
definition ioa_unfolding :: "('s,'a)ioa \<Rightarrow> (('s,'a)execution,'a)ioa" where
  "ioa_unfolding a \<equiv> let
      start = {(s,[]) | s . s \<in> start a};
      trans = {(e,act,e') . (last_state e) \<midarrow>act\<midarrow>a\<longrightarrow> (last_state e') 
        \<and> e' = cons_exec e (act, last_state e')}
    in
      \<lparr>ioa.asig = ioa.asig a, ioa.start = start, ioa.trans = trans\<rparr>"

private 
lemma l1:"is_ref_map last_state (ioa_unfolding a) a"
proof -
  { fix e e' act
    assume "reachable (ioa_unfolding a) e" and tr:"e \<midarrow>act\<midarrow>(ioa_unfolding a) \<longrightarrow>e'"
    have "last_state e \<midarrow>act\<midarrow>a \<longrightarrow> last_state e'" using tr 
      by (simp add:ioa_unfolding_def is_trans_def)
    hence "refines (last_state e, [(act, last_state e')]) e act e' a last_state"
      by (simp add:refines_def Let_def is_trans_def trace_def schedule_def filter_act_def trace_match_def) }
  thus ?thesis by (auto simp add:is_ref_map_def, simp add:ioa_unfolding_def, blast)
qed

private
definition hist_fwd_sim :: "('s,'a)ioa \<Rightarrow> 's \<Rightarrow> (('s,'a)execution set)" where    
  "hist_fwd_sim a s \<equiv> {e . is_exec_of a e \<and> last_state e = s}"

private                              
lemma l2:"is_forward_sim (hist_fwd_sim a) a (ioa_unfolding a)"
proof -
  text {* The base case *}
  { fix s assume "s \<in> start a"
    hence "hist_fwd_sim a s \<inter> start (ioa_unfolding a) \<noteq> {}"
    by (auto simp add: hist_fwd_sim_def ioa_unfolding_def is_exec_of_def Int_def) }
  moreover
  { fix s s' t act
    assume "s' \<in> hist_fwd_sim a s" and "s \<midarrow>act\<midarrow>a\<longrightarrow> t" and "reachable a s"
    def t' \<equiv> "cons_exec s' (act,t)"
    def e \<equiv> "(s',[(act,t')])"
    have tr:"s' \<midarrow>act\<midarrow>(ioa_unfolding a)\<longrightarrow> t'" and next_in_image:"t' \<in> hist_fwd_sim a t"
    proof -
      show "s' \<midarrow>act\<midarrow>(ioa_unfolding a)\<longrightarrow> t'" using \<open>s \<midarrow>act\<midarrow>a\<longrightarrow> t\<close> t'_def \<open>s' \<in> hist_fwd_sim a s\<close>
        by (simp add:is_trans_def ioa_unfolding_def cons_exec_def hist_fwd_sim_def) 
      show "t' \<in> hist_fwd_sim a t" using \<open>s' \<in> hist_fwd_sim a s\<close> t'_def \<open>s \<midarrow>act\<midarrow>a\<longrightarrow> t\<close>
        by (simp add:hist_fwd_sim_def) (metis IOA.cons_exec_def IOA.is_exec_of_def IOA.last_state.simps(2) IOA.trans_from_last_state fst_conv snd_conv)
    qed
    have is_exec:"is_exec_frag_of (ioa_unfolding a) e" using tr
      by (metis IOA.is_exec_frag_of.simps(2) fst_conv snd_conv e_def) 
    have fst:"fst e = s'" and last:"last_state e = t'" by (auto simp add:e_def)
    have trace_match:"trace_match (ioa_unfolding a) act e" 
      by (auto simp add:trace_match_def Let_def ioa_unfolding_def traces_simps e_def) 
    note next_in_image is_exec fst last trace_match}
  ultimately show ?thesis by (smt IOA.is_forward_sim_def)
qed

private
lemma traces_ioa_unfolding:"traces (ioa_unfolding a) = traces a" using l1 l2 ref_map_soundness forward_sim_soundness
by (metis (no_types, lifting) ioa.select_convs(1) ioa_unfolding_def set_eq_subset)

definition add_history :: "('s,'a)ioa \<Rightarrow> ('s \<Rightarrow> 'h \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 'h) \<Rightarrow> ('s \<Rightarrow> 'h) \<Rightarrow> ('s\<times>'h,'a)ioa"
  -- {* @{term add_history} can be used to add hitory state to an IOA, and the theorem below 
    stipulates that no new traces are introduced by the operation. *}
  where "add_history a f f\<^sub>0 \<equiv> let
      start = {(s,h) . s \<in> start a \<and> h = f\<^sub>0 s};
      trans = {((s,h),act,(s',h')) .  s \<midarrow>act\<midarrow>a\<longrightarrow> s' \<and> h' = f s h act s'}
    in
      \<lparr>ioa.asig = ioa.asig a, ioa.start = start, ioa.trans = trans\<rparr>"

private
definition hist_ref_map :: "('s \<Rightarrow> 'h \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 'h) \<Rightarrow> ('s \<Rightarrow> 'h) \<Rightarrow> ('s,'a)execution \<Rightarrow> 's\<times>'h" where 
  "hist_ref_map f f\<^sub>0 e \<equiv> foldr (\<lambda> (a, s') (s, h) . (s', f s h a s'))
    (snd e) (fst e, f\<^sub>0 (fst e))"

private 
lemma l5:"fst (hist_ref_map f f\<^sub>0 e) = last_state e"
proof (induct e rule:last_state.induct)
  case 1 thus ?case by (auto simp add:hist_ref_map_def)
next 
  case (2 s p ps)
  thus ?case apply (auto simp add:hist_ref_map_def) by (metis (no_types, lifting) fstI prod.case_eq_if)
qed

private
lemma l6:
  assumes "e' = cons_exec e (a,s)"
  shows "let hs = \<lambda> e . hist_ref_map f f\<^sub>0 e in hs e' = (s, f (last_state e) (snd (hs e)) a s)" 
nitpick[verbose,  card 'a = 2, card 'b = 2, card 'c = 2, card "('b \<times> 'a) list" = 30, card "'a \<times> 'c" = 4, expect=none]
using assms
proof (induct "snd e")
  case Nil thus ?case by (simp add:hist_ref_map_def cons_exec_def, cases e, cases e', auto)
next
  case (Cons x xs) thus ?case by (simp add:hist_ref_map_def cons_exec_def, cases e, cases e', auto)
    (metis (no_types, lifting) case_prod_beta fstI)
qed

private
lemma l4:"is_ref_map (hist_ref_map f f\<^sub>0) (ioa_unfolding a) (add_history a f f\<^sub>0)"
apply (auto simp only:is_ref_map_def)
    apply(simp add: ioa_unfolding_def hist_ref_map_def add_history_def)
    (* base case discharged *)
  subgoal premises prems for fst_e snd_e fst_e' snd_e' act
  proof -
    let ?e = "(hist_ref_map f f\<^sub>0 (fst_e, snd_e), [(act, hist_ref_map f f\<^sub>0 (fst_e', snd_e'))])"
    show ?thesis using prems
    apply (intro exI[where ?x="?e"])
    apply (auto simp add:refines_def)
        defer
        apply (simp add:hist_ref_map_def is_trans_def trace_match_def ioa_unfolding_def add_history_def Let_def traces_simps)
      apply (rm_reachable)
      subgoal premises prems
      proof -
        from prems have 1:"(fst_e', snd_e') = cons_exec (fst_e, snd_e) (act, last_state (fst_e', snd_e'))" 
        and 2:"last_state (fst_e, snd_e) \<midarrow>act\<midarrow>a\<longrightarrow> last_state (fst_e', snd_e')"
          by (simp_all add:ioa_unfolding_def is_trans_def)
        from 1 have 3:"fst_e = fst_e'" by (simp add:cons_exec_def)
        from 1 2 3 l6[of "(fst_e', snd_e')" "(fst_e, snd_e)" act "last_state (fst_e', snd_e')" f f\<^sub>0] show ?thesis 
        apply (simp add:add_history_def is_trans_def Let_def, cases "hist_ref_map f f\<^sub>0 (fst_e', snd_e)", auto)
            apply (metis fst_conv l5)
          apply (metis fst_conv l5) 
        done
      qed
    done
  qed
done

private
lemma l3:"traces (ioa_unfolding a) \<subseteq> IOA.traces (add_history a f f\<^sub>0)" 
using l4 ref_map_soundness
by (metis (no_types, lifting) add_history_def ioa.select_convs(1) ioa_unfolding_def) 

theorem hist_soundness:"IOA.traces a \<subseteq> IOA.traces (add_history a f f\<^sub>0)"
using traces_ioa_unfolding l3 by fast

end

end

end