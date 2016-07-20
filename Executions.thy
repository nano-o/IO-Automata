theory Executions
imports "IOA" "~~/src/HOL/Library/Sublist"
begin

(* Author: Giuliano Losa. This theory is an adaptation of the one by Olaf Mueller found in 
  Isabelle/HOLCF *)

context IOA begin

declare Let_def[simp]

definition proj_exec  ("_ \<downharpoonright> _ _") where
  "proj_exec e i sig \<equiv> 
    (fst e i, map (\<lambda> p . (fst p, snd p i)) (filter (\<lambda> p . fst p \<in> actions sig) (snd e)))"

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
      (metis last_state.simps(1) Nil.hyps filter.simps(1) list.simps(8) prod.collapse) 
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
      hence "last_state (fst e, p#ps) i = last_state ((fst e, p#ps) \<downharpoonright> i (ioa.asig (memb fam i)))"
        by (simp add:proj_exec_def)
      with Cons.hyps(2) show ?thesis by simp
    next
      case False
      from False have 3: "((fst e, p#ps) \<downharpoonright> i (ioa.asig (memb fam i))) 
                          = ((fst e, ps) \<downharpoonright> i (ioa.asig (memb fam i)))"
          by (simp add:proj_exec_def)
      from False and `i \<in> ids fam` and Cons.prems and Cons.hyps(2) 
        have 4:"last_state (fst e, p#ps) i = last_state (fst e, ps) i" 
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
    let ?e = "(fst e, p#ps)"
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
      from True have 3:"(?e \<downharpoonright> i sig) = cons_exec  (?e' \<downharpoonright> i sig) (fst p, snd p i)" 
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
    instead results in suttering sequences. Stuttering sequences can be pasted easily. *)
lemma paste_execs:
  fixes fam and es and t::"'a trace" 
  assumes "\<forall> i \<in> ids fam . is_exec_of (memb fam i) (es i)"
    and "\<forall> i \<in> ids fam . let sig_i = ioa.asig (memb fam i) in (t \<bar> sig_i) = trace sig_i (es i)"
  obtains e where "is_exec_of (par fam) e" and "trace (ioa.asig (par fam)) e = t" 
    and "\<forall> i \<in> ids fam . (e \<downharpoonright> i (ioa.asig (memb fam i))) = es i" oops 

end