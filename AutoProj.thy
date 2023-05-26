(*  Author:     Tobias Nipkow
    Copyright   1998 TUM

Is there an optimal order of arguments for `next'?
Currently we can have laws like `delta A (a#w) = delta A w o delta A a'
Otherwise we could have `acceps A == fin A o delta A (start A)'
and use foldl instead of foldl2.
*)

section "Projection functions for automata"

theory AutoProj
imports Main
begin

definition start :: "'a * 'b * 'c * 'd \<Rightarrow> 'a" where "start A = fst A"
definition alp :: "'a * 'b * 'c * 'd \<Rightarrow> 'b" where "alp A = fst(snd(A))"
definition "next" :: "'a * 'b * 'c * 'd \<Rightarrow> 'c" where "next A = fst(snd(snd(A)))"
definition fin :: "'a * 'b * 'c * 'd \<Rightarrow> 'd" where "fin A = snd(snd(snd(A)))"


lemma [simp]: "start(q,vs,d,f) = q"
by(simp add:start_def)

lemma [simp]: "next(q,vs,d,f) = d"
by(simp add:next_def)

lemma [simp]: "fin(q,vs,d,f) = f"
by(simp add:fin_def)

lemma [simp]: "alp(q,vs,d,f) = vs"
by(simp add:alp_def)

end
