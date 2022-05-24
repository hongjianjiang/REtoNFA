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
  \<I> :: "'q set"            (* "The set of initial states *)
  \<F> :: "'q set"           (* "The set of final states *)

text \<open>Using notions for labelled transition systems, 
it is easy to define the languages accepted by automata.\<close>

definition NFA_accept :: "('a, 'b) NFA_rec \<Rightarrow> 'b list \<Rightarrow> bool" where
  "NFA_accept \<A> w = (\<exists> q \<in> (\<I> \<A>). \<exists> q' \<in> (\<F> \<A>).
                  LTS_is_reachable (\<Delta> \<A>) q w q') "

definition \<L> where "\<L> \<A> = {w. NFA_accept \<A> w}"

(*lemma "u \<in> v \<Longrightarrow> NFA_accept ⦇𝒬 = (λu. [u]) ` v, Σ = v, Δ = (λx. ([], v, x)) ` (λu. [u]) ` v, ℐ = {[]}, ℱ = (λu. [u]) ` v⦈ [u]"
  apply (unfold NFA_accept_def)
  apply auto
  done

lemma [simp]:"u \<in> v \<Longrightarrow> NFA_accept ⦇𝒬 = (λu. [u]) ` v, Σ = v, Δ = (λx. ([], v, x)) ` (λu. [u]) ` v, ℐ = {[]}, ℱ = (λu. [u]) ` v⦈ [u]"
  apply (unfold NFA_accept_def)
  apply auto
  done
*)

end
