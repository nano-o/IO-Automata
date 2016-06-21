theory History
imports Simulations
begin
         
context IOA begin

definition ioa_unfolding :: "('s,'a)ioa \<Rightarrow> (('s,'a)execution,'a)ioa" where
  "ioa_unfolding a \<equiv> let
      start = {(s,[]) | s . s \<in> start a};
      trans = {(e,act,e') . (last_state e) \<midarrow>act\<midarrow>a\<longrightarrow> (last_state e') \<and> (fst o hd o snd) e' = act}
    in
      \<lparr>ioa.asig = ioa.asig a, ioa.start = start, ioa.trans = trans\<rparr>"

lemma "is_ref_map last_state (ioa_unfolding a) a"
proof -
  { fix e e' act
    assume "reachable (ioa_unfolding a) e" and tr:"e \<midarrow>act\<midarrow>(ioa_unfolding a) \<longrightarrow>e'"
    have "last_state e \<midarrow>act\<midarrow>a \<longrightarrow> last_state e'" using tr 
      by (simp add:ioa_unfolding_def is_trans_def)
    hence "refines (last_state e, [(act, last_state e')]) e act e' a last_state"
      by (simp add:refines_def Let_def is_trans_def trace_def schedule_def filter_act_def trace_match_def) }
  thus ?thesis by (auto simp add:is_ref_map_def, simp add:ioa_unfolding_def, blast)
qed

definition hist_fwd_sim :: "('s,'a)ioa \<Rightarrow> 's \<Rightarrow> (('s,'a)execution set)" where    
  "hist_fwd_sim a s \<equiv> {e . is_exec_of a e \<and> last_state e = s}"
                                
lemma "is_forward_sim (hist_fwd_sim a) a (ioa_unfolding a)"
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

definition add_history :: "('s,'a)ioa \<Rightarrow> ('s \<Rightarrow> 'h \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 'h) \<Rightarrow> ('s \<Rightarrow> 'h) \<Rightarrow> ('s\<times>'h,'a)ioa"
  where "add_history a f f\<^sub>0 \<equiv> let
      start = {(s,h) . s \<in> start a \<and> h = f\<^sub>0 s};
      trans = {((s,h),act,(s',h')) . (s,act,s') \<in> trans a \<and> h' = f s h act s'}
    in
      \<lparr>ioa.asig = ioa.asig a, ioa.start = start, ioa.trans = trans\<rparr>"

theorem "IOA.traces (add_history a f f\<^sub>0) = IOA.traces a"
oops

end

end