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
  \<Delta> :: "(('q,'a) LTS * ('q * 'q) set) set"      (* "The transition relation" *)
  \<I> :: "'q set"            (* "The set of initial states *)
  \<F> :: "'q set"           (* "The set of final states *)

text \<open>Using notions for labelled transition systems, 
it is easy to define the languages accepted by automata.\<close>

definition reachable_from_node1_to_node2 ::"'q \<Rightarrow> 'q \<Rightarrow>  'a list \<Rightarrow> ('q,'a) LTS * ('q * 'q) set \<Rightarrow>  bool" where
"reachable_from_node1_to_node2 I F w trans1= LTS_is_reachable (fst trans1) (snd trans1) I w F"


definition get_reachable_from_LTS_list :: "('q, 'a) NFA_rec \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> 'q \<Rightarrow> bool set" where
  "get_reachable_from_LTS_list \<A> w q q' = (reachable_from_node1_to_node2 q q' w) ` (\<Delta> \<A>)"

fun judge ::"bool set \<Rightarrow> bool" where
"judge bs = (True \<in> bs)"


 
definition NFA_accept :: "('q, 'a) NFA_rec \<Rightarrow> 'a list \<Rightarrow> bool" where
"NFA_accept \<A> w = (\<exists> q\<in>(\<I> \<A>) . \<exists> q' \<in> (\<F> \<A>). judge (get_reachable_from_LTS_list \<A> w q q'))"

(*definition NFA_accept_Q :: "('q, 'a) NFA_rec \<Rightarrow> 'q  \<Rightarrow> 'a list \<Rightarrow> bool" where
  "NFA_accept_Q \<A> q w = (\<exists> q' \<in> (\<F> \<A>).
                  LTS_is_reachable (\<Delta> \<A>) (\<Delta>' \<A>) q w q') "*)

definition \<L> where "\<L> \<A> = {w. NFA_accept  \<A> w}"

end