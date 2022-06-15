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
  \<Delta> :: "('q,'a) LTS"      (* "The transition relation" *)
  \<Delta>' :: "('q * 'q) set"      (* "The transition relation" *)
  \<I> :: "'q set"            (* "The set of initial states *)
  \<F> :: "'q set"           (* "The set of final states *)

text \<open>Using notions for labelled transition systems, 
it is easy to define the languages accepted by automata.\<close>

definition NFA_accept :: "('q, 'a) NFA_rec \<Rightarrow> 'a list \<Rightarrow> bool" where
  "NFA_accept \<A> w = (\<exists> q \<in> (\<I> \<A>). \<exists> q' \<in> (\<F> \<A>).
                  LTS_is_reachable (\<Delta> \<A>) (\<Delta>' \<A>) q w q') "

definition \<L> where "\<L> \<A> = {w. NFA_accept \<A> w}"

end
