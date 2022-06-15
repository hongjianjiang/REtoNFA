theory Regrexp
  imports Main Com begin


value "Match s1 r n"
value "Replace r s s1"



inductive
  regrexp :: "'a com * 'a option  \<Rightarrow> 'a option \<Rightarrow>  bool"  (infix "\<Rightarrow>" 55) where
Skip: "(Skip,s) \<Rightarrow> s" | 
Match: "(Match s r n, s1)   \<Rightarrow>  s1"|
Search: "(Replace r s s1, s2) \<Rightarrow> s2"|
Split: "(Split r s ls,s1) \<Rightarrow> s1"|
Extarct : "(Extract s n, s1) \<Rightarrow> s1"


end