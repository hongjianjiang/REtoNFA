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
    "trans2Del1 (Dot) alp_set =(\<lambda>x.(Node Dot ,{x}, \<epsilon>)) ` alp_set"|
    "trans2Del1 (Concat r1 r2) alp_set = (let r1StateSet = trans2Del1 r1 alp_set in
                                   renameState (r1StateSet) (Node r2)) \<union> trans2Del1 r2 alp_set \<union> {(Pair \<epsilon> (Node r2),{},Node r2)}"|
    "trans2Del1 (Alter r1 r2) alp_set = trans2Del1 r1 alp_set \<union> trans2Del1 r2 alp_set"|
    "trans2Del1 (Star r) alp_set = star_state (trans2Del1 r alp_set) r "|
    "trans2Del1 (Plus r) alp_set = (let rStateSet = trans2Del1 r alp_set in rStateSet \<union> star_state rStateSet r) "|
    "trans2Del1 (Ques r) alp_set = trans2Del1 r alp_set \<union> {(Node (Ques r), {} , \<epsilon>)}"


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


(*lemma set_set_to_list[simp]:
   "finite s ⟹ set (set_to_list s) = s"
  unfolding set_to_list_def by (metis (mono_tags) finite_list some_eq_ex)*)




lemma InitState:"q ∈ ℐ (reg2nfa r1 v) \<Longrightarrow> q = (Node r1)"
  apply (induct r1)
  by auto

lemma FinalState:"xa ∈ ℱ (reg2nfa r1 v) \<Longrightarrow> xa = \<epsilon>"
  apply (induct r1)
  by auto


lemma l11:"⋀x q xa.
       sem_reg r2 v =
       {w. (Δ' (reg2nfa r2 v) = {} ∨ ℐ (reg2nfa r2 v) ≠ {} ∧ (∃q'∈ℱ (reg2nfa r2 v). ∃x∈Δ' (reg2nfa r2 v). case x of (q, q'') ⇒ LTS_is_reachable (Δ (reg2nfa r2 v)) q'' w q')) ∧
           (Δ' (reg2nfa r2 v) = {} ⟶ (∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x))} ⟹
       sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x} ⟹
       ¬ LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r1) x \<epsilon> ⟹
       ¬ LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r2) x \<epsilon> ⟹
       Δ' (reg2nfa r1 v) = {} ⟹ q ∈ ℐ (reg2nfa r1 v) ⟹ xa ∈ ℱ (reg2nfa r1 v) ⟹ LTS_is_reachable (Δ (reg2nfa r1 v)) q x xa ⟹ False"
  subgoal premises for x q xa 
  proof - 
    have "q ∈ ℐ (reg2nfa r1 v)" by fact 
    moreover have "sem_reg r2 v =
       {w. (Δ' (reg2nfa r2 v) = {} ∨ ℐ (reg2nfa r2 v) ≠ {} ∧ (∃q'∈ℱ (reg2nfa r2 v). ∃x∈Δ' (reg2nfa r2 v). case x of (q, q'') ⇒ LTS_is_reachable (Δ (reg2nfa r2 v)) q'' w q')) ∧
           (Δ' (reg2nfa r2 v) = {} ⟶ (∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x))}" by fact 
    moreover have c1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}" by fact 
    moreover have c2:"¬ LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r1) x \<epsilon>" by fact
    moreover have c3:"¬ LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r2) x \<epsilon>" by fact
    moreover have c4:"Δ' (reg2nfa r1 v) = {}" by fact 
    moreover have c5:"q ∈ ℐ (reg2nfa r1 v)" by fact
    moreover have c6:"xa ∈ ℱ (reg2nfa r1 v)" by fact 
    moreover have c7:"LTS_is_reachable (Δ (reg2nfa r1 v)) q x xa" by fact
    from c5 have c8:"q = Node r1" 
      using InitState by blast
    from c6 have c9:"xa = \<epsilon>" 
      using FinalState by blast 
    from c7 c8 c9 have c10:" LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) x \<epsilon>" 
      by simp
    from c3 have c11:"¬ LTS_is_reachable (Δ (reg2nfa r1 v) ∪ Δ (reg2nfa r2 v)) (Node r1) x \<epsilon>"  by (metis c2 transEqDel)
    from c11 have c12:"¬ LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) x \<epsilon>" by (meson subLTSlemma)
    from c12 c10 show "False" by auto
  qed
 done



theorem tranl_eq :
  fixes r v  
  shows l1: "sem_reg r v = \<L> (reg2nfa r v)"
proof(induct r)
case ESet
  then show ?case 
    apply (unfold \<L>_def NFA_accept_def)
    by (smt Collect_cong FinalState InitState LTS_Epi_cases LTS_Step_cases empty_def empty_iff prod.inject reg2lts.simps(7) reg2nfa.simps(2) select_convs(3) sem_reg.simps(1) singletonD state.distinct(1) trans2Del1.simps(2))
next
  case (LChr x)
  then show ?case     
    apply( unfold \<L>_def NFA_accept_def)
    apply auto
     apply (simp add: LTS_Empty LTS_Step)
    by (smt LTS_Epi_cases insert_not_empty prod.sel(1) singleton_iff snd_conv state.distinct(1))
next
  case Dot
  then show ?case 
    apply (unfold \<L>_def  NFA_accept_def)
    apply auto
     apply (meson LTS_Empty LTS_Step image_eqI singletonI)
    by (smt LTS_Epi_cases image_iff insert_not_empty prod.sel(1) singletonD snd_conv state.distinct(1))
next    
  case (Alter r1 r2)
  then show ?case     
    apply(unfold \<L>_def NFA_accept_def)
    sorry
  (*subgoal for x q xa 
    proof -
      assume "sem_reg r2 v =
        {w. (Δ' (reg2nfa r2 v) = {} ∨ ℐ (reg2nfa r2 v) ≠ {} ∧ (∃q'∈ℱ (reg2nfa r2 v). ∃x∈Δ' (reg2nfa r2 v). case x of (q, q'') ⇒ LTS_is_reachable (Δ (reg2nfa r2 v)) q'' w q')) ∧
            (Δ' (reg2nfa r2 v) = {} ⟶ (∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x))}" and
        "sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}" and a3:"¬ LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r1) x \<epsilon>" and 
        "¬ LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r2) x \<epsilon>" and 
        "Δ' (reg2nfa r1 v) = {}" and "q ∈ ℐ (reg2nfa r1 v)" and a1:"xa ∈ ℱ (reg2nfa r1 v)" and a2:"LTS_is_reachable (Δ (reg2nfa r1 v)) q x xa" 
      then have c1:"q = Node r1" by auto
      from a1 have c2:"xa = \<epsilon>" by auto 
      from a2 c1 c2 have c3:"LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) x \<epsilon>" by auto
      from a3 have c4:"¬ LTS_is_reachable (Δ (reg2nfa r1 v) ∪ Δ (reg2nfa r2 v)) (Node r1) x \<epsilon>" by (auto simp:transEqDel)
      from c4 have c5:"¬ LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) x \<epsilon>" by (auto simp:UnionE)
      from c3 c5 show "False" by auto
    qed
    prefer 2
    subgoal premises for x q' a b q qa xa proof -
      have a1:"q' ∈ ℱ (reg2nfa r1 v)" by fact
      have c1:"q' = \<epsilon>" using a1 by auto
      have a2:"q ∈ ℐ (reg2nfa r1 v)" by fact
      have c2:"q = Node r1" using a2 by auto
      have a3:"qa ∈ ℐ (reg2nfa r1 v)" by fact 
      have c3:"qa = Node r1" using a3 by auto
      have a4:"xa ∈ ℱ (reg2nfa r1 v)" by fact 
      have c4:"xa = \<epsilon>" using a4 by auto
      have a5:"LTS_is_reachable (Δ (reg2nfa r1 v)) qa x xa" by fact 
      have c5:"LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) x \<epsilon>" using a5 c3 c4 by auto
      have a6:"LTS_is_reachable (Δ (reg2nfa r1 v)) b x q'" by fact
      have c6:"LTS_is_reachable (Δ (reg2nfa r1 v)) b x \<epsilon>" using c1 a6 by auto
      have a7:"(a, b) ∈ Δ' (reg2nfa r1 v)" by fact
      have c7:"LTS_is_reachable (Δ (reg2nfa r1 v)) a x \<epsilon>" using c6 a7 
        by (metis ‹¬ LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r1) x ε› c5 reg2nfa.subLTSlemma transEqDel)
      have "a = Node r1" using c5 c7 
        by (metis ‹¬ LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r1) x ε› reg2nfa.subLTSlemma transEqDel)
      have a8:"¬ LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r1) x ε" by fact
      have c8:"False" using a8 c5 
        by (simp add: transEqDel)
      then show " LTS_is_reachable (trans2Del1 r1 v ∪ trans2Del1 r2 v) (Node r2) x ε" 
        by fastforce
    qed
    sorry   *)
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
    

    

  (*proof -
    fix a b q xa qa xb 
    assume a1:"sem_reg r1 v = {w. ∃q∈ℐ (reg2nfa r1 v). ∃x∈ℱ (reg2nfa r1 v). LTS_is_reachable (Δ (reg2nfa r1 v)) q w x}" and
       a2:"sem_reg r2 v = {w. ∃q∈ℐ (reg2nfa r2 v). ∃x∈ℱ (reg2nfa r2 v). LTS_is_reachable (Δ (reg2nfa r2 v)) q w x}" and
       a3:"¬ LTS_is_reachable ({(state.Pair a (Node r2), aa, state.Pair b (Node r2)) |a aa b. (a, aa, b) ∈ trans2Del1 r1 v} ∪ trans2Del1 r2 v) (Node r2) (a @ b) ε" and
       a4:"Δ' (reg2nfa r1 v) = {}" and
       a5:"q ∈ ℐ (reg2nfa r1 v)" and
       a6:"xa ∈ ℱ (reg2nfa r1 v)" and
       a7:"LTS_is_reachable (Δ (reg2nfa r1 v)) q a xa" and
       a8:"Δ' (reg2nfa r2 v) = {}" and 
       a9:"qa ∈ ℐ (reg2nfa r2 v)" and 
       a10:"xb ∈ ℱ (reg2nfa r2 v)" and 
       a11:"LTS_is_reachable (Δ (reg2nfa r2 v)) qa b xb"
    from this show "False" proof -
      have c1:"q = Node r1" 
        using a5 by auto
      have c2:"xa = \<epsilon>" 
        using a6 by auto
      have c3:"qa = Node r2" 
        using a9 by auto
      have c4:"xb = \<epsilon>"
        using a10 by auto
      have c5:"LTS_is_reachable (Δ (reg2nfa r1 v)) (Node r1) a \<epsilon>"
        using a7 c1 c2 by blast
      have c6:"LTS_is_reachable (Δ (reg2nfa r2 v)) (Node r2) b \<epsilon>"
        using a11 c3 c4 by blast
      have c7:"¬ LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (Node r2) (a @ b) ε " using a3 by auto
      have c8:"Δ' (reg2nfa (Concat r1 r2) v) = {(Pair \<epsilon> (Node r2),Node r2)}"
        by simp
      have "LTS_is_reachable (Δ (reg2nfa (Concat r1 r2) v)) (Node (Concat r1 r2)) (a @ b) ε" using c5 c6
      *)
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