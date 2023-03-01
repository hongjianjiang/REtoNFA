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

primrec LTS_is_reachable :: "('q, 'a) LTS \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" where
   "LTS_is_reachable \<Delta> q [] q' = (q = q' ∨ (q, {}, q') ∈ Δ)"|
   "LTS_is_reachable \<Delta> q (a # w) q' =
      (\<exists>q'' \<sigma>. a \<in> \<sigma> \<and> (q, \<sigma>, q'') \<in> \<Delta> \<and> LTS_is_reachable \<Delta> q'' w q')"


lemma LChr_lemma :"LTS_is_reachable {(a,{x},b)} a l b ⟹ a≠ b ⟹ l = [x]"
  by (smt (verit, del_insts) LTS_is_reachable.simps(1) LTS_is_reachable.simps(2) empty_iff old.prod.inject remdups_adj.cases singleton_iff)

end