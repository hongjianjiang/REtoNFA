(*  Title:       Nondeterministic Finite Automata 
    Authors:     Shuanglong Kan <shuanglong@uni-kl.de>
                 Thomas Tuerk <tuerk@in.tum.de>             
                 Petra Dietrich <petra@ecs.vuw.ac.nz>
*)

(* Nondeterministic Finite Automata *)

theory NFA
imports Main LTS 
begin




record ('q,'a) NFA_rec =
  \<Q> :: "'q set"           (* "The set of states" *)
  \<Sigma> :: "'a set"           (* alphabet *)
  \<Delta> :: "(('q,'a) LTS * 'q * 'q) list set"      (* "The transition relation" *)
  \<I> :: "'q set"            (* "The set of initial states *)
  \<F> :: "'q set"           (* "The set of final states *)

text \<open>Using notions for labelled transition systems, 
it is easy to define the languages accepted by automata.\<close>

primrec single_LTS_reachable_by_path :: "'a list ⇒ (('q,'a) LTS * 'q * 'q) list  ⇒ bool " where
"single_LTS_reachable_by_path w []= (w = [])"|
"single_LTS_reachable_by_path w (x# xs) = (∃p q. (w = p @ q ∧ LTS_is_reachable (fst x) (fst (snd x)) p (snd (snd x)) ∧ single_LTS_reachable_by_path q xs))"

lemma concat_lemma:"single_LTS_reachable_by_path qa x ⟹ single_LTS_reachable_by_path q xa ⟹ single_LTS_reachable_by_path (qa @ q) (x @ xa)"
  apply(induct x arbitrary:qa) apply auto apply(induct xa arbitrary:q) apply auto 
  by metis 


lemma inverse_concat_lemma: "single_LTS_reachable_by_path q (xa @ y) ⟹ ∃p qa. q = qa @ p ∧ single_LTS_reachable_by_path qa xa ∧ single_LTS_reachable_by_path p y"
  apply(induct xa arbitrary:q) apply auto 
  by (metis append.assoc)

fun judge ::"bool set \<Rightarrow> bool" where
"judge bs = (True \<in> bs)"

lemma ""

definition NFA_accept :: "('a, 'b) NFA_rec \<Rightarrow> 'b list \<Rightarrow> bool" where
  "NFA_accept \<A> w = judge ((single_LTS_reachable_by_path w) `  (Δ 𝒜))"

definition \<L> where "\<L> \<A> = {w. NFA_accept \<A> w}"

end