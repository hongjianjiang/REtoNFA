(*  Author: Tobias Nipkow *)

section "Regular expressions"

theory Regular_Exp
imports Regular_Set
begin

datatype (atoms: 'a) rexp =
  is_Zero: Zero |
  is_One: One |
  Atom 'a |
  Alter "('a rexp)" "('a rexp)" |
  Times "('a rexp)" "('a rexp)" |
  Star "('a rexp)" |
  Dot |
  Ques "('a rexp)"|
  Plus "('a rexp)"|
 (* Range "('a rexp)" "nat" "nat"|
  Neg "('a rexp)" |*)
  Inter "('a rexp)" "('a rexp)"|
Multi "('a rexp)" nat




primrec lang :: "'a rexp \<Rightarrow> 'a set \<Rightarrow> 'a lang" where
"lang (Zero) vset= {}" |
"lang (One) vset= {[]}" |
"lang (Atom a) vset= (if a : vset then {[a]} else {})" |
"lang (Alter r s) vset= (lang r vset) Un (lang s vset)" |
"lang (Times r s) vset= conc (lang r vset) (lang s vset)" |
"lang (Star r) vset= star(lang r vset)"|
"lang (Dot) vset = (\<lambda>x. [x]) ` vset" |
"lang (Ques r) vset = (lang r vset) \<union> {[]}"|
"lang (Plus r) vset = (conc (lang r vset) (star(lang r vset)))"|
"lang (Inter r s) vset = (lang r vset) \<inter> (lang s vset)"|
(*"lang (Range r m n) vset = (range (lang r vset) m n)"|
"lang (Neg r) vset = star((\<lambda>x. [x]) ` vset) - (lang r vset)"|*)
"lang (Multi r m) vset = (lang r vset) ^^ m"

  
abbreviation (input) regular_lang where "regular_lang A \<equiv> (\<exists>r vset. lang r vset = A)"
end
