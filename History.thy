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

lemma "is_ref_map last_state (ioa_unfolding a) a" oops

definition hist_fwd_sim where    
  "hist_fwd_sim a s \<equiv> {e . is_exec_of a e \<and> last_state e = s}"
                                
lemma "is_fwd_sim hist_fwd_sim a (ioa_unfolding a)" oops


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