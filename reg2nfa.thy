theory reg2nfa 
  imports AReg NFA
begin



datatype 'v state =  Node "'v regexp" | \<epsilon> | Pair "'v state" "'v state" 

primrec L :: "'v state \<Rightarrow> 'v set \<Rightarrow> 'v list set"  where 
  "L (Node r) v = sem_reg r v"|
  "L (Pair n1 n2) v = L n1 v \<union> L  n2 v"|
  "L \<epsilon> v = {[]}"

fun getEpsilon :: "('v state * 'v set * 'v state) set \<Rightarrow> ('v state * 'v set * 'v state) set" where (*get the triple set which the third state is \<epsilon>*)
    "getEpsilon ss = {x. snd (snd x) = \<epsilon> \<and> x \<in> ss}"

fun renameState :: "('v state * 'v set * 'v state) set \<Rightarrow> 'v state \<Rightarrow>('v state *'v set *'v state) set" where  (*change the whole state in the triple set into new state*)
    "renameState ss newstate = {(Pair (fst x) (newstate), fst (snd x), Pair (snd (snd x)) newstate)| x. x\<in> ss}"

fun renameState1 :: "('v state * 'v set * 'v state)  \<Rightarrow> 'v state \<Rightarrow>('v state *'v set *'v state) " where  (*change the state in the triple into new state*)
    "renameState1 s newstate = (Pair (fst s) (newstate), fst (snd s), Pair (snd (snd s)) newstate)"

fun pairState :: "'v state \<Rightarrow> 'v state \<Rightarrow> 'v state" where
    "pairState ss newstate = Pair ss newstate"

inductive_set star_state :: " ('v state * 'v set * 'v state) set \<Rightarrow> 'v regexp \<Rightarrow> ('v state * 'v set * 'v state) set" 
  for tr :: "('v state * 'v set * 'v state) set" and r::"'v regexp" 
  where (* For star r, tr is the transition of regexp r, r is the regexp*)
  Star2Node:"(Node (Star r), {},Node r) \<in> (star_state tr r)" | (* a* \<rightarrow> a*)
  Epi2Star:"(\<epsilon>,{},Node (Star r)) \<in> star_state tr r" |  (* \<epsilon> \<rightarrow> a**)
  Node2Star:"x \<in> tr \<Longrightarrow> x \<in> (star_state tr r)" |(* a \<rightarrow> \<epsilon>*)
  StepStar:"x \<in> star_state tr r \<Longrightarrow> (renameState1 x (Node (Star r)) \<in> star_state tr r)" (* repeat like a.a* \<rightarrow> \<epsilon>.a* *)

primrec trans2Del1 :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> ('v state × 'v set × 'v state) set" where (*regexp to LTS*)
    "trans2Del1 (LChr v) alp_set= {(Node (LChr v),{v},\<epsilon>)}"|
    "trans2Del1 (ESet) alp_set= {(Node ESet,{},\<epsilon>)}"|
    (*"trans2Del1 (EString) alp_set = {}"|*)
    "trans2Del1 (Dot) alp_set = {(Node Dot ,alp_set, \<epsilon>)}"|
    "trans2Del1 (Concat r1 r2) alp_set = {(Node (Concat r1 r2), {}, Pair (Node r1) (Node r2))} \<union> (let r1StateSet = trans2Del1 r1 alp_set in
                                   renameState (r1StateSet) (Node r2)) \<union> trans2Del1 r2 alp_set \<union> {(Pair \<epsilon> (Node r2),{},Node r2)}"|
    "trans2Del1 (Alter r1 r2) alp_set = trans2Del1 r1 alp_set \<union> trans2Del1 r2 alp_set \<union> {(Node (Alter r1 r2), {}, Node r1), (Node (Alter r1 r2),{}, Node r2)}"|
    "trans2Del1 (Star r) alp_set = star_state (trans2Del1 r alp_set) r "|
    "trans2Del1 (Plus r) alp_set = {(Node (Plus r),{},Node (Concat r (Star r))),(Node (Concat r (Star r)), {}, Pair (Node r) (Node (Star r)))} \<union> (let rStateSet = trans2Del1 r alp_set in
                                   renameState (rStateSet) (Node (Star r))) \<union> star_state (trans2Del1 r alp_set) r \<union> {(Pair \<epsilon> (Node (Star r)),{},Node (Star r))}"|
    "trans2Del1 (Ques r) alp_set = trans2Del1 r alp_set \<union> {(Node (Ques r), {} , \<epsilon>),(Node (Ques r),{},Node r)}"


(*primrec trans2Del2 :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> ('v state × 'v state) set" where (*regexp to epsilon*)
    "trans2Del2 (LChr v) alp_set= {}"|
    "trans2Del2 (ESet) alp_set= {}"|
    "trans2Del2 (Dot) alp_set ={}"|
    "trans2Del2 (Concat r1 r2) alp_set ={}"|
    "trans2Del2 (Alter r1 r2) alp_set = {(Node (Alter r1 r2),  Node r1)} \<union> {(Node (Alter r1 r2),Node r2)}"|
    "trans2Del2 (Star r) alp_set ={(Node (Star r), Node r),(Node (Star r),\<epsilon>)}"|
    "trans2Del2 (Plus r) alp_set ={(Node (Star r), Node r),(Node (Star r),\<epsilon>)}"|
    "trans2Del2 (Ques r) alp_set ={(Node (Ques r), Node r)}"*)


primrec reg2lts :: "'v regexp \<Rightarrow> 'v set\<Rightarrow>  ('v state, 'v) LTS" where
    "reg2lts Dot a = trans2Del1 Dot a"|
    "reg2lts (LChr p) a = trans2Del1 (LChr p) a"|
    "reg2lts (r1||r2) a = trans2Del1 (r1||r2) a"|
    "reg2lts (Star r) a = trans2Del1 (Star r) a" |
    "reg2lts (r+) a = trans2Del1 (r+) a" | 
    "reg2lts (r?) a = trans2Del1 (r?) a" |
    (*"reg2lts EString a = trans2Del1 EString a"|*)
    "reg2lts ESet a = trans2Del1 ESet a"|
    "reg2lts (Concat r1 r2) a = trans2Del1 (Concat r1 r2) a"

primrec reg2q :: "'v regexp \<Rightarrow> 'v set\<Rightarrow>  ('v state) set" where
    "reg2q Dot a = {Node Dot, \<epsilon>}"|
    "reg2q (LChr p) a =  {Node (LChr p), \<epsilon>}"|
    "reg2q (r1||r2) a = {Node (r1||r2),\<epsilon>} \<union> reg2q r1 a \<union> reg2q r2 a"|
    "reg2q (Star r) a = {Node (Star r), \<epsilon>} \<union> reg2q r a" |
    "reg2q (r+) a = {Node (Plus r), \<epsilon>} \<union> reg2q r a" |
    "reg2q (r?) a = {Node (Ques r), \<epsilon>} \<union> reg2q r a" |
    (*"reg2q EString a = {Node EString, \<epsilon>}"|*)
    "reg2q ESet a = {Node ESet, \<epsilon>}"|
    "reg2q (Concat r1 r2) a = {pairState \<epsilon> (Node r2)}\<union> {pairState x (Node r2)| x. x\<in> (reg2q r1 a)}  \<union> reg2q r2 a"


value "reg2q (Concat Dot Dot) {v}"

primrec reg2nfa :: "'v regexp \<Rightarrow> 'v set\<Rightarrow> ('v state,'v) NFA_rec" where 
    "reg2nfa (Concat r1 r2) a= \<lparr> 
                  \<Q> = reg2q (Concat r1 r2) a,
                  \<Sigma> = alp_reg  (Concat r1 r2) a,
                  \<Delta> = reg2lts  (Concat r1 r2) a,
                  \<I> ={Node (Concat r1 r2)}, 
                  \<F> ={\<epsilon>}\<rparr> " |
   (* "reg2nfa (EString) a= \<lparr>
                  \<Q> = reg2q EString a,
                  \<Sigma> = alp_reg (EString) a,
                  \<Delta> = reg2lts (EString) a,
                  \<Delta>' = trans2Del2 (EString) a,
                  \<I> = {Node EString}, 
                  \<F> = {\<epsilon>}\<rparr> " |*)
    "reg2nfa (ESet) a= \<lparr>
                  \<Q> = reg2q ESet a,
                  \<Sigma> = alp_reg (ESet) a,
                  \<Delta> = reg2lts (ESet) a,
                  \<I> = {Node ESet}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (Dot) a= \<lparr> 
                  \<Q> = reg2q (Dot) a,
                  \<Sigma> = alp_reg (Dot) a,
                  \<Delta> = reg2lts (Dot) a,
                  \<I> = {Node Dot}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (LChr v) a=  \<lparr> 
                  \<Q> = reg2q (LChr v) a,
                  \<Sigma> = alp_reg (LChr v) a,
                  \<Delta> = reg2lts (LChr v) a,
                  \<I> = {Node (LChr v)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (r1||r2) a =  \<lparr> 
                  \<Q> = reg2q (r1||r2) a,
                  \<Sigma> = alp_reg (r1||r2) a,
                  \<Delta> = reg2lts (r1||r2) a,
                  \<I> = {Node (Alter r1 r2)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (Star r) a = \<lparr> 
                  \<Q> = reg2q  (Star r) a,
                  \<Sigma> = alp_reg (Star r) a,
                  \<Delta> = reg2lts (Star r) a,
                  \<I> = {Node (Star r)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (r+) a= \<lparr> 
                  \<Q> = reg2q  (r+) a,
                  \<Sigma> = alp_reg (r+) a,
                  \<Delta> = reg2lts  (r+) a,
                  \<I> = {Node (Plus r)}, 
                  \<F> = {\<epsilon>}\<rparr> " |
    "reg2nfa (r?) a = \<lparr> 
                  \<Q> = reg2q  (r?) a,
                  \<Sigma> = alp_reg (r?) a,
                  \<Delta> = reg2lts  (r?) a,
                  \<I> = {Node (Ques r)}, 
                  \<F> = {\<epsilon>}\<rparr> " 


lemma transEqDel : "trans2Del1 r1 v = Δ (reg2nfa r1 v)"
  apply (induct r1)
  apply auto
  done


lemma InitState:"q ∈ ℐ (reg2nfa r1 v) \<Longrightarrow> q = (Node r1)"
  apply (induct r1)
  by auto

lemma FinalState:"xa ∈ ℱ (reg2nfa r1 v) \<Longrightarrow> xa = \<epsilon>"
  apply (induct r1)
  by auto


lemma trans2Del :"trans2Del1 r v =(Δ (reg2nfa r v))"
  by (simp add: transEqDel)



theorem tranl_eq :
  fixes r v  
  shows l1: "sem_reg r v = \<L> (reg2nfa r v)"
proof(induct r)
case ESet
  then show ?case 
    apply (unfold \<L>_def NFA_accept_def)
    apply auto
     apply (meson LTS_Empty LTS_Epi singletonI)
    subgoal for x
    proof-
      assume a1:"LTS_is_reachable {(Node ESet, {}, ε)} (Node ESet) x ε"
      have c1:"LTS_is_reachable {(Node ESet, {}, ε)} (Node ESet) [] ε" 
        by (meson LTS_Empty LTS_Epi insertI1)
      from a1 c1 show ?thesis 
        by (smt (verit, del_insts) LTS_Step_cases empty_iff list.exhaust prod.sel(1) prod.sel(2) singletonD state.distinct(2))
    qed
    done
next
    case (LChr x)
    then show ?case     
      apply( unfold \<L>_def NFA_accept_def)
      apply auto
      apply (simp add: LTS_Empty LTS_Step)
      apply (rule LTS_is_reachable.cases)
      apply auto
      using LTS_Epi1_cases by fastforce
next
  case Dot
  then show ?case 
    apply (unfold \<L>_def  NFA_accept_def)
    apply auto
     apply (simp add: LTS_Empty LTS_Step)
    sorry
next
  case (Alter r1 r2)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    sorry
next
  case (Concat r1 r2)
  then show ?case 
    apply(unfold \<L>_def NFA_accept_def)
    apply auto
    subgoal for a b q xa qa xb 
    proof -
    assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}"
    assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x}"
    assume a3:"q ∈ ℐ (reg2nfa r1 v)"
    assume a4:"xa ∈ ℱ (reg2nfa r1 v)"
    assume a5:"LTS_is_reachable (Δ (reg2nfa r1 v)) q a xa "
    assume a6:"qa ∈ ℐ (reg2nfa r2 v)"
    assume a7:"xb ∈ ℱ (reg2nfa r2 v)"
    assume a8:"LTS_is_reachable (Δ (reg2nfa r2 v)) qa b xb"
    from a3 have c1:"q = Node r1" 
      using InitState by blast
    from a4 have c2:"xa = \<epsilon>" 
      using FinalState by blast
    from c1 c2 a5 have c3:"LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) a \<epsilon>" 
      by blast
    from a6 have c4: "qa = Node r2" 
      using InitState by blast
    from a7 have c5: "xb = \<epsilon>"
      using FinalState by blast 
    from c4 c5 a8 have c6: "LTS_is_reachable (Δ (reg2nfa r2 v)) (Node r2) b \<epsilon>" 
      by blast
    from c3 c6 have c7:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (Node (Concat r1 r2)) (a @ b) ε" apply auto
    proof -
      assume b1:"LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) a ε"
      assume b2:"LTS_is_reachable (Δ (reg2nfa r2 v)) (Node r2) b ε"
      have e1:"LTS_is_reachable (trans2Del1 r1 v) (Node r1) a ε" 
        by (simp add: c3 transEqDel)
      have e2:"LTS_is_reachable (trans2Del1 r2 v) (Node r2) b ε"
        by (simp add: b2 transEqDel)
      from e1 e2 have e3:"LTS_is_reachable (insert (pairState ε (Node r2), {}, Node r2) ({(pairState a (Node r2), aa, pairState b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)) (pairState (Node r1) (Node r2)) (a) (pairState ε (Node r2))"
         proof (induction rule: LTS_is_reachable.induct)
           case (LTS_Empty Δ q)
           then show ?case apply auto
             by (simp add: LTS_is_reachable.LTS_Empty)
         next
           case (LTS_Step a q Δ w q')
           then show ?case apply auto 
             by (smt (verit, del_insts) LTS_is_reachable.LTS_Step UnCI Un_insert_right mem_Collect_eq)
         next
           case (LTS_Epi q Δ q')
           then show ?case apply auto 
             by (smt (verit, del_insts) LTS_Epi1 UnCI Un_insert_right mem_Collect_eq)
         next
           case (LTS_Epi1 q Δ l q')
           then show ?case apply auto 
             by (smt (verit, ccfv_threshold) LTS_is_reachable.LTS_Epi1 UnCI Un_insert_right mem_Collect_eq)
         qed
         have ee:"LTS_is_reachable  (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v))) (pairState (Node r1) (Node r2)) (a) (pairState ε (Node r2))"
           by (smt (verit, best) Collect_cong Un_insert_left e3 insert_is_Un pairState.simps subLTSlemma sup_commute)
      have e4:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (pairState (Node r1) (Node r2)) (a) (pairState ε (Node r2))"
         using ee by auto
      have e5:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (Node r2) b ε"
        by (metis e2 subLTSlemma sup_commute trans2Del1.simps(4) transEqDel)
      have e6:"Δ (reg2nfa (Concat r1 r2) v) = (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))"
        by auto
      have ee1:"LTS_is_reachable (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v))) (Node (Concat r1 r2)) [] (state.Pair (Node r1) (Node r2))"
        by (meson LTS_Empty LTS_Epi insertCI)
      have e7:"LTS_is_reachable ({(pairState ε (Node r2), {}, Node r2)} \<union> ({(pairState a (Node r2), aa, pairState b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v}))
        (pairState ε (Node r2)) [] (Node r2)"
        by (meson LTS_Empty LTS_Epi UnCI singletonI)
      have e8:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (pairState (Node r1) (Node r2)) (a@b) ε" 
        by (metis (no_types, lifting) LTS_Epi1 e4 e5 e6 insertI1 joinLTSlemma pairState.simps)      
      have e9:"LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (Node (Concat r1 r2)) (a@b) ε"
        using e8 ee1 joinLTSlemma by fastforce
      have e10:"LTS_is_reachable
     (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))
     (Node (Concat r1 r2)) (a @ b) ε " 
        using e6 e9 by presburger
      from b1 b2 show "LTS_is_reachable
     (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))
     (Node (Concat r1 r2)) (a @ b) ε" 
        using e10 by blast
    qed
    from c7 have "LTS_is_reachable
     (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))
     (Node (Concat r1 r2)) (a @ b) ε" by auto
    then show ?thesis by auto
  qed
  subgoal for x
  proof -
    assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}"
    assume a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x}"
    assume a3:"LTS_is_reachable
     (insert (state.Pair ε (Node r2), {}, Node r2)
       (insert (Node (Concat r1 r2), {}, state.Pair (Node r1) (Node r2))
         ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v)))
     (Node (Concat r1 r2)) x ε"
    show "x ∈ (λx. fst x @ snd x) `
         ({w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x} ×
          {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x})" sorry
  qed
done
next
  case (Star r)
  then show ?case sorry
next
  case (Plus r)
  then show ?case sorry
next
  case (Ques r)
  then show ?case sorry
qed

(*
lemma [simp]:"a \<in> (transition r1 v) \<Longrightarrow> a \<in> (transition r1 v ∪ transition r2 v)"
  apply auto
  done

lemma [simp]:"a \<in> (transition r2 v) \<Longrightarrow> a \<in> (transition r1 v ∪ transition r2 v)"
  apply auto
  done

lemma lts2del: " \<Delta> (reg2nfa r v) = reg2lts r v"
  apply (induct r)
  apply (unfold reg2nfa_def)
  apply auto
  done

lemma lts2transition: "reg2lts r1 v = transition r1 v"
  apply (induct r1)
  sorry  

lemma ltsrewrite: "LTS_is_reachable (Δ (reg2nfa r1 v)) q x xa = LTS_is_reachable (transition r1 v) q x xa"
  by (simp add: lts2del lts2transition)

lemma nfa2trans: "Δ (reg2nfa r1 v) = transition r1 v"
  by (simp add: lts2del lts2transition)
 
lemma lts2trans: "LTS_is_reachable (Δ (reg2nfa r1 v)) q x xa = LTS_is_reachable (transition r1 v) q x xa"
  by (simp add: nfa2trans)

lemma [simp]:"LTS_is_reachable ((λx. ([], v, x)) ` (λu. [u]) ` v) [] x [xa] ⟹ x ∈ (λu. [u]) ` v"
  apply (cases x; cases ‹tl x›)
     apply auto
  done

lemma initqlem[simp]:"q ∈ ℐ (reg2nfa r v) \<Longrightarrow> q = []"
  apply (induct r)
  apply auto
 done



lemma inistate:"ℐ (reg2nfa r2 v) = {[]}"
  apply (induct r2)
  apply auto
  done

lemma l2:"u ∈ v ⟹ ∃x∈v. ∃σ. u ∈ σ ∧ ([], σ, [x]) ∈ (λx. ([], v, x)) ` (λu. [u]) ` v" 
  apply auto
  done

lemma "r1 = LChr a \<Longrightarrow> v = {a} \<Longrightarrow> xa ∈ ℱ (reg2nfa r1 v) \<Longrightarrow> LTS_is_reachable (Δ (reg2nfa r1 v)) [] xa xa "
  apply auto
  done

lemma "r1 = Dot \<Longrightarrow> v = {a} \<Longrightarrow> xa ∈ ℱ (reg2nfa r1 v) \<Longrightarrow> LTS_is_reachable (Δ (reg2nfa r1 v)) [] xa xa "
  apply auto
  done

lemma "r1 = EString \<Longrightarrow> v = {a} \<Longrightarrow> xa ∈ ℱ (reg2nfa r1 v) \<Longrightarrow> LTS_is_reachable (Δ (reg2nfa r1 v)) [] xa xa "
  apply auto
  done

lemma "r1 = ESet \<Longrightarrow> v = {a} \<Longrightarrow> xa ∈ ℱ (reg2nfa r1 v) \<Longrightarrow> LTS_is_reachable (Δ (reg2nfa r1 v)) [] xa xa "
  apply auto
  done

lemma "r1 = LChr a ||  LChr b \<Longrightarrow> v = {c} \<Longrightarrow> xa ∈ ℱ (reg2nfa r1 v) \<Longrightarrow> LTS_is_reachable (Δ (reg2nfa r1 v)) [] xa xa "
  apply auto
  done

lemma "LTS_is_reachable (star_lts {[a]} {a}) [] [a] [a]"
  apply auto
  apply(rule star_lts.induct)
  apply auto
done

lemma "r1 = Dot* \<Longrightarrow> v = {a} \<Longrightarrow> xa ∈ ℱ (reg2nfa r1 v) \<Longrightarrow> LTS_is_reachable (Δ (reg2nfa r1 v)) [] xa xa "
  apply auto
  apply(induct xa)
  apply auto
  


lemma "       xa ∈ ℱ (reg2nfa r1 v) ⟹ LTS_is_reachable (Δ (reg2nfa r1 v)) [] xa xa"
  apply (cases xa, cases \<open>tl xa\<close>)
    apply simp     apply simp 

lemma [simp]:"LTS_is_reachable (Δ (reg2nfa (LChr a⇩1) {a⇩1})) []  [a⇩1]  []  ⟹
        []  ∈ ℱ (reg2nfa (LChr a⇩1) {a⇩1}) ⟹
       LTS_is_reachable (Δ (reg2nfa (LChr a⇩1) {a⇩1})) []  []   [a⇩1]"
  apply auto
  done


lemma "LTS_is_reachable (Δ (reg2nfa (LChr a1) {a1})) [] [a1] [] == False"
  by auto

lemma "[] \<in> ℱ (reg2nfa (LChr a1) {a1}) == False"
  by auto

lemma "LTS_is_reachable (Δ (reg2nfa (LChr a⇩1) {a⇩1})) []  []   [a⇩1] == False"
  by auto
*)

(*
definition allStates :: "'v regexp  \<Rightarrow> 'v set \<Rightarrow>'v list list " where 
"allStates r a == set_to_list (sem_reg r a)"

definition initState :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> 'v list set" where 
"initState r a = {}"

definition finalState :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> 'v list set" where 
"finalState r a= sem_reg r a"

definition allAlpha :: "'v regexp \<Rightarrow> 'v set \<Rightarrow>  'v set" where 
"allAlpha r a == alp_reg r a"

definition "maxlen vset ≡ Max (length ` vset)"

definition finalstate1 ::"'a list set \<Rightarrow> 'a list set" where 
    "finalstate1 vset = {x. x∈vset ∧ length x = maxlen vset}"

definition "minlen vset ≡ Min (length ` vset)"

definition initialstate ::"'a list set \<Rightarrow> 'a list set" where 
    "initialstate vset = {x. x∈vset ∧ length x = minlen vset}"
*)

end