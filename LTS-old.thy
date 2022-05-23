
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
   "LTS_is_reachable \<Delta> q [] q' = (q = q')"|
   "LTS_is_reachable \<Delta> q (a # w) q' =
      (\<exists>q'' \<sigma>. a \<in> \<sigma> \<and> (q, \<sigma>, q'') \<in> \<Delta> \<and> LTS_is_reachable \<Delta> q'' w q')"


lemma DeltLTSlemma:"LTS_is_reachable Δ q x y \<Longrightarrow>LTS_is_reachable {(f a, b, f c)| a b c. (a,b,c)\<in> Δ } (f q) x (f y)"
  apply(induct x arbitrary:q)
   apply auto
  done

(*primrec LTS_is_reachable_set :: "('q, 'a) LTS ⇒ 'q ⇒ 'a list ⇒ 'q set" where
"LTS_is_reachable_set Δ q [] = {q}"| 
"LTS_is_reachable_set Δ q (a # w) =     (⋃((λ(q, σ, q''). LTS_is_reachable_set Δ q'' w)  Δ))"
*)

lemma subLTSlemma[simp]:"LTS_is_reachable l1 q x y \<Longrightarrow> LTS_is_reachable (l1 \<union> l2) q x y"
  apply (induct x  arbitrary:q)
  apply auto
  done



lemma [simp]:"LTS_is_reachable {([], {x}, [x])} [] w [x] \<Longrightarrow> w = [x]"
  apply (cases w; cases ‹tl w›)
  apply auto
  done



lemma [simp]:"LTS_is_reachable {([], {}, [])} [] x xa ⟹ x = []" 
  apply (induct x)
  apply auto
  done


lemma [simp]:"{w. LTS_is_reachable {([], {x}, [x])} [] w [x]} = {[x]}"
  apply auto
  done


end