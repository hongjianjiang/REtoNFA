
theory LTS
imports Main "HOL.Option"
begin


text \<open> Given a set of states $\mathcal{Q}$ and an alphabet $\Sigma$,
a labeled transition system is a subset of $\mathcal{Q} \times \Sigma
\times \mathcal{Q}$.  Given such a relation $\Delta \subseteq
\mathcal{Q} \times \Sigma \times \mathcal{Q}$, a triple $(q, \sigma,
q')$ is an element of $\Delta$ iff starting in state $q$ the state
$q'$ can be reached reading the label $\sigma$. \<close>

  
type_synonym ('q,'a) LTS = "('q * 'a set * 'q) set"


subsubsection  \<open>Reachability\<close>

text \<open>Often it is enough to consider just the first and last state of
a path. This leads to the following definition of reachability. Notice, 
that @{term "LTS_is_reachable \<Delta>"} is the reflexive, transitive closure of @{term \<Delta>}.\<close>

inductive LTS_is_reachable :: "('q, 'a) LTS  \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool"  where 
   LTS_Empty:"LTS_is_reachable \<Delta> q [] q"|
   LTS_Step:"(\<exists>q'' \<sigma>. a \<in> \<sigma> \<and> (q, \<sigma>, q'') \<in> \<Delta> \<and> LTS_is_reachable \<Delta> q'' w q') \<Longrightarrow> LTS_is_reachable \<Delta> q (a # w) q'"|
   LTS_Epi:"(\<exists>q''. (q,{},q'') \<in> \<Delta> \<and>  LTS_is_reachable \<Delta> q'' l q') \<Longrightarrow> LTS_is_reachable \<Delta> q l q'"  

declare LTS_is_reachable.intros[intro]

inductive_cases LTS_Step_cases[elim!]:"LTS_is_reachable \<Delta> q (a # w) q'"
inductive_cases LTS_Epi_cases[elim!]:"LTS_is_reachable \<Delta> q l q'"
inductive_cases LTS_Empty_cases[elim!]:"LTS_is_reachable \<Delta> q [] q"

thm LTS_is_reachable.simps


lemma DeltLTSlemma1:"LTS_is_reachable \<Delta> q l q'\<Longrightarrow> LTS_is_reachable {(f u, v, f w)| u v w. (u,v,w)\<in> \<Delta>} (f q) l (f q')"
  apply(induct l)
  subgoal
    apply(rule LTS_is_reachable.cases)
       apply simp
      apply (simp add: LTS_Empty)
     apply force
    sorry
  sorry


lemma subLTSlemma[simp]:"LTS_is_reachable l1 q x y \<Longrightarrow> LTS_is_reachable (l1 \<union> l2) q x y"
  apply (rule LTS_is_reachable.cases)
     apply simp
    apply (simp add: LTS_Empty)
  sledgehammer


primrec LTS_is_reachable_set :: "('q, 'a) LTS ⇒ 'q ⇒ 'a list ⇒ 'q set" where    
  "LTS_is_reachable_set Δ q [] = {q}"|
  "LTS_is_reachable_set Δ q (a # w) = ⋃ ((λ(q', σ, q''). if a ∈ σ ∧ q' = q then LTS_is_reachable_set Δ q'' w else {}) ` Δ)"


lemma "LTS_is_reachable Δ q1 w q2 ⟹ q2 ∈ LTS_is_reachable_set Δ q1 w"
proof (induction w arbitrary: q1)
  case Nil
  then show ?case
    by simp
next
  case (Cons a w)
  from `LTS_is_reachable Δ q1 (a # w) q2`
  obtain q'' and σ
  where "a ∈ σ" and "(q1, σ, q'') ∈ Δ" and "LTS_is_reachable Δ q'' w q2"
    by auto
  moreover from `LTS_is_reachable Δ q'' w q2` and Cons.IH
  have "q2 ∈ LTS_is_reachable_set Δ q'' w"
    by simp
  ultimately show ?case
    by fastforce
qed*)
end