theory Executions
imports "/home/nano/Documents/IO-Automata/IOA" "~~/src/HOL/Library/Sublist"
begin

(* Author: Giuliano Losa. This theory is an adaptation of the one by Olaf Mueller found in 
  Isabelle/HOLCF *)

context IOA begin

declare Let_def[simp]

definition cons_exec where
  "cons_exec p e \<equiv> (fst e, (snd e)#p)"

definition append_exec where
  "append_exec e e' \<equiv> (fst e, (snd e)@(snd e'))"

fun last_state where
  "last_state (s,[]) = s"
| "last_state (s,ps#p) = snd p"

definition proj_exec  ("_ \<downharpoonright> _ _") where
  "proj_exec e i sig \<equiv> 
    (fst e i, map (\<lambda> p . (fst p, snd p i)) (filter (\<lambda> p . fst p \<in> actions sig) (snd e)))"

lemma last_state_reachable:
  fixes A e
  assumes "is_exec_of A e"
  shows "reachable A (last_state e)" using assms
proof -
  have "is_exec_of A e \<Longrightarrow> reachable A (last_state e)"
  proof (induction "snd e" arbitrary: e)
    case Nil
    from Nil.prems have 1:"fst e \<in> start A" by (simp add:is_exec_of_def)
    from Nil.hyps have 2:"last_state e = fst e" by (metis last_state.simps(1) surjective_pairing)
    from 1 and 2 and Nil.hyps show ?case by (metis reachable_0)
  next
    case (Cons p ps e)
    let ?e' = "(fst e, ps)"
    have ih:"reachable A (last_state ?e')"
    proof -
      from Cons.prems and Cons.hyps(2) have "is_exec_of A ?e'"
        by (simp add:is_exec_of_def) (metis is_exec_frag_of.simps(1,3) list.exhaust prod.collapse)
      with Cons.hyps(1) show ?thesis by auto
    qed
    from Cons.prems and Cons.hyps(2) have "(last_state ?e')\<midarrow>(fst p)\<midarrow>A\<longrightarrow>(snd p)"
      by (simp add:is_exec_of_def) (cases "(A,fst e,ps#p)" rule:is_exec_frag_of.cases, auto)
    with ih and Cons.hyps(2) show ?case
      by (metis Executions.IOA.last_state.simps(2) IOA.reachable_n prod.collapse) 
  qed
  thus ?thesis using assms by fastforce
qed 

lemma trans_from_last_state:
  assumes "is_exec_frag_of A e" and "(last_state e)\<midarrow>a\<midarrow>A\<longrightarrow>s'"
  shows "is_exec_frag_of A (cons_exec (a,s') e)"
    using assms by (cases "(A, fst e, snd e)" rule:is_exec_frag_of.cases, auto simp add:cons_exec_def)

lemma exec_frag_prefix:
  fixes A p ps
  assumes "is_exec_frag_of A (cons_exec p e)"
  shows "is_exec_frag_of A e"
    using assms by (cases "(A, fst e, snd e)" rule:is_exec_frag_of.cases, auto simp add:cons_exec_def)

lemma trace_same_ext:
  fixes A B e
  assumes "ext A = ext B"
  shows "trace (ioa.asig A) e = trace (ioa.asig B) e" 
  using assms by (auto simp add:trace_def)

lemma trace_append_is_append_trace:
  fixes e e' sig
  shows "trace sig (append_exec e' e) = trace sig e' @ trace sig e"
  by (simp add:append_exec_def trace_def schedule_def filter_act_def)

lemma append_exec_frags_is_exec_frag:
  fixes e e' A as
  assumes "is_exec_frag_of A e" and "last_state e = fst e'" 
  and "is_exec_frag_of A e'"
  shows "is_exec_frag_of A (append_exec e e')"
proof -
  from assms show ?thesis 
  proof (induct "(fst e',snd e')" arbitrary:e' rule:is_exec_frag_of.induct)
    case (3 A) print_cases
    from "3.hyps" and "3.prems"(1,2)
    show ?case by (simp add:append_exec_def)
  next
    case (2 A p)
    have "last_state e \<midarrow>(fst p)\<midarrow>A\<longrightarrow> snd p" using "2.prems"(2,3) and "2.hyps" 
      by (metis is_exec_frag_of.simps(2) prod.collapse)
    hence "is_exec_frag_of A (fst e, (snd e)#p)" using "2.prems"(1) 
      by (metis cons_exec_def prod.collapse trans_from_last_state)
    moreover 
    have "append_exec e e' = (fst e, (snd e)#p)" using "2.hyps" 
      by (metis append_Cons append_Nil append_exec_def)
    ultimately 
    show ?case by auto
  next
    case (1 A ps p' p e')
    have "is_exec_frag_of A (fst e, (snd e)@(ps#p'#p))"
    proof -
      have "is_exec_frag_of A (fst e, (snd e)@(ps#p'))"
        by (metis "1.hyps"(1,2) "1.prems"(1-3) Executions.IOA.append_exec_def IOA.is_exec_frag_of.simps(1) fst_conv prod.collapse swap_simp) 
      moreover
      have "snd p' \<midarrow>(fst p)\<midarrow>A\<longrightarrow> snd p" using "1.prems"(3) "1.hyps"(2) 
        by (metis is_exec_frag_of.simps(1) prod.collapse)
      ultimately show ?thesis by simp
    qed
    moreover have "append_exec e e' = (fst e, (snd e)@(ps#p'#p))" 
      by (metis "1.hyps"(2) append_exec_def)
    ultimately show ?case by simp
  qed
qed

lemma last_state_of_append:
  fixes e e'
  assumes "fst e' = last_state e"
  shows "last_state (append_exec e e') = last_state e'"
  using assms by (cases e' rule:last_state.cases, auto simp add:append_exec_def)

section {* Composition is monotonic with respect to the implementation relation *}

(*  Should also hold with the stuttering version of projection, would even be simpler *)
lemma last_state_proj:
  fixes fam i e
  assumes "i \<in> ids fam" and "is_exec_frag_of (par fam) e"
  shows "(last_state e) i = last_state (e \<downharpoonright> i (ioa.asig (memb fam i)))"
proof -
  have "is_exec_frag_of (par fam) e 
        \<Longrightarrow> (last_state e) i = last_state (e \<downharpoonright> i (ioa.asig (memb fam i)))"
  proof (induction "snd e" arbitrary: e) 
    case Nil show ?case 
      by (simp add:proj_exec_def)
      (metis Executions.IOA.last_state.simps(1) Nil.hyps filter.simps(1) list.simps(8) prod.collapse) 
  next 
    case (Cons p ps e) print_cases
    from "Cons.prems" have 1:"is_exec_frag_of (par fam) (fst e, ps)"
      by (metis Cons.hyps(2) is_exec_frag_of.simps(1) is_exec_frag_of.simps(3) list.exhaust surjective_pairing)
    from 1 and "Cons.hyps"
      have 2:"(last_state (fst e, ps)) i = last_state ((fst e, ps) \<downharpoonright> i (ioa.asig (memb fam i)))" 
        by simp
    show ?case
    proof (cases "fst p \<in> act (memb fam i)")
      case True
      hence "last_state (fst e, ps#p) i = last_state ((fst e, ps#p) \<downharpoonright> i (ioa.asig (memb fam i)))"
        by (simp add:proj_exec_def)
      with Cons.hyps(2) show ?thesis by simp
    next
      case False
      from False have 3: "((fst e, ps#p) \<downharpoonright> i (ioa.asig (memb fam i))) 
                          = ((fst e, ps) \<downharpoonright> i (ioa.asig (memb fam i)))"
          by (simp add:proj_exec_def)
      from False and `i \<in> ids fam` and Cons.prems and Cons.hyps(2) 
        have 4:"last_state (fst e, ps#p) i = last_state (fst e, ps) i" 
          by  (cases "(par fam, fst e, snd e)" rule:is_exec_frag_of.cases)
              (auto simp add:is_trans_def par_def)
      from 2 3 4 Cons.hyps(2) show ?thesis by simp
    qed
  qed
  with assms(2) show ?thesis by simp
qed

lemma proj_execs:
  fixes fam i e
  assumes "is_exec_frag_of (par fam) e"
  and "i \<in> ids fam"
  defines sig_def:"sig \<equiv> ioa.asig (memb fam i)"
  and A_i_def:"A_i \<equiv> memb fam i"
  shows "is_exec_frag_of A_i (e \<downharpoonright> i sig)" (* Here we would have a problem with the stuttering version of projections *)
proof -
  have "is_exec_frag_of (par fam) e 
        \<Longrightarrow> is_exec_frag_of A_i (e \<downharpoonright> i sig)"
  proof (induction "snd e" arbitrary:e)
    case Nil
    thus ?case by (simp add:proj_exec_def)
  next
    case (Cons p ps e)
    let ?e = "(fst e, ps#p)"
    let ?e' = "(fst e, ps)"
    thm Cons.hyps
    from Cons.prems and Cons.hyps(2) have prems:"is_exec_frag_of (par fam) ?e" by simp
    from Cons.hyps have ih:"is_exec_frag_of (par fam) ?e' 
                          \<Longrightarrow> is_exec_frag_of A_i (?e' \<downharpoonright> i sig)" by simp
    from prems have 0:"is_exec_frag_of (par fam) ?e'" by (metis is_exec_frag_of.simps(1,3) list.exhaust)
    from 0 and ih have 1:"is_exec_frag_of A_i (?e' \<downharpoonright> i sig)" by auto
    have "is_exec_frag_of A_i (?e \<downharpoonright> i sig)"
    proof (cases "fst p \<in> act A_i")
      case False
      hence "(?e \<downharpoonright> i sig) = (?e' \<downharpoonright> i sig)" by (simp add:proj_exec_def sig_def A_i_def)
      with 1 show ?thesis by simp
    next
      case True
      from True and prems and `i \<in> ids fam` 
        have 2:"(last_state ?e' i)\<midarrow>(fst p)\<midarrow>A_i\<longrightarrow>(snd p i)"
          by  (cases "(par fam, ?e')" rule:is_exec_frag_of.cases)
              (auto simp add:A_i_def is_trans_def par_def split add:split_if_asm)
      from True have 3:"(?e \<downharpoonright> i sig) = cons_exec (fst p, snd p i) (?e' \<downharpoonright> i sig)" 
        by (simp add:proj_exec_def A_i_def sig_def cons_exec_def)
      from `i \<in> ids fam` and last_state_proj and 0 
        have 4:"last_state ?e' i = last_state (?e' \<downharpoonright>i sig)" by (metis sig_def)
      from 1 2 3 4 and trans_from_last_state show ?thesis by fastforce
    qed
    thus ?case using Cons.hyps(2) by simp
  qed
  with assms(1) show ?thesis by simp
qed

(*  This one is trickier. In the HOLCF theory, projection on a component does not remove steps but
    instead results in suttering sequences. Stuttering sequences can be pasted easily.
lemma paste_execs:
  fixes fam::"('id, ('a,'s)ioa)family" and es::"'id \<Rightarrow> ('s,'a)execution" and t::"'a trace" 
  assumes "\<forall> i \<in> ids fam . is_exec_of (memb fam i) (es i)"
    and "\<forall> i \<in> ids fam . let sig_i = ioa.asig (memb fam i) in (t \<bar> sig_i) = trace sig_i (es i)"
  obtains e where "is_exec_of (par fam) e" and "trace (ioa.asig (par fam)) e = t" 
    and "\<forall> i \<in> ids fam . (e \<downharpoonright> i (ioa.asig (memb fam i))) = es i" *)

end