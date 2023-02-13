theory AReg imports Main  begin

section "Regexp definition and semantics"

datatype ('v)regexp = ESet | LChr 'v| Concat "'v regexp" "'v regexp"|
                      Alter "('v) regexp" "('v) regexp"| Dot|
                      Star "'v regexp" |(* Plus "('v) regexp" |*) Ques "('v) regexp" | \<epsilon>    

datatype t_regexp = t_ESet | t_LChr | t_Concat | t_Alter | t_Dot | t_Star |(* t_Plus |*) t_Ques | t_\<epsilon>

inductive_set star :: "'v list set \<Rightarrow> 'v list set" 
  for r :: "'v list set" where
zero[intro!]:"[] \<in> star r"|
step[intro!]:"x \<in> r \<and> y \<in> star r \<Longrightarrow> x@y \<in> star r"

primrec sem_reg :: "('v) regexp => 'v set\<Rightarrow> 'v list set" where 
"sem_reg ESet v = {[]}"| (*Empty Set*)
"sem_reg (Dot) vset = (\<lambda>x .[x]) ` vset" | 
"sem_reg (Concat r1 r2) v ={q@p| q p. q \<in> sem_reg r1 v \<and> p \<in> sem_reg r2 v}"|
"sem_reg (LChr a) v = {[a]}"|
"sem_reg (Alter v1 v2) a = (sem_reg v1 a) \<union> (sem_reg v2 a)"|
"sem_reg (Star a) v = star (sem_reg a v)"|
(*"sem_reg (Plus a) v = {q@p| q p. q \<in> (sem_reg a v) \<and> p \<in> star (sem_reg a v)}"|*)
"sem_reg (Ques v) a = {[]} \<union> (sem_reg v a)"|
"sem_reg \<epsilon> v = {[]}"



primrec  alp_reg :: "'v regexp \<Rightarrow> 'v set \<Rightarrow> 'v set" where
"alp_reg (LChr n) vs=  {n}"|
"alp_reg (ESet) vs = {}"|
"alp_reg (Concat r1 r2) vs =  (alp_reg r1 vs \<union> alp_reg r2 vs)"|
"alp_reg (Alter v1 v2) vs = alp_reg v1 vs \<union> alp_reg v2 vs"|
"alp_reg (Dot) vs = vs"|
"alp_reg (Star v) vs = alp_reg v vs"| 
(*"alp_reg (Plus v) vs = alp_reg v vs"|*)
"alp_reg (Ques v) vs = alp_reg v vs"|
"alp_reg \<epsilon> vs = {}"

end
